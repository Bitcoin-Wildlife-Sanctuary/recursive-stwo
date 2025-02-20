use circle_plonk_dsl_constraint_system::dvar::DVar;
use circle_plonk_dsl_data_structures::PlonkWithAcceleratorLookupElementsVar;
use circle_plonk_dsl_fields::QM31Var;
use stwo_prover::constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_prover::constraint_framework::{
    INTERACTION_TRACE_IDX, ORIGINAL_TRACE_IDX, PREPROCESSED_TRACE_IDX,
};
use stwo_prover::core::fields::m31::BaseField;
use stwo_prover::core::fields::secure_column::SECURE_EXTENSION_DEGREE;
use stwo_prover::core::pcs::TreeVec;
use stwo_prover::core::ColumnVec;

pub struct PointEvaluationAccumulatorVar {
    pub random_coeff: QM31Var,
    pub accumulation: QM31Var,
}

impl PointEvaluationAccumulatorVar {
    pub fn new(random_coeff: QM31Var) -> Self {
        Self {
            random_coeff: random_coeff.clone(),
            accumulation: QM31Var::zero(&random_coeff.cs()),
        }
    }

    pub fn accumulate(&mut self, evaluation: QM31Var) {
        self.accumulation = &(&self.accumulation * &self.random_coeff) + &evaluation;
    }

    pub fn finalize(self) -> QM31Var {
        self.accumulation
    }
}

pub struct RelationEntryVar<'a> {
    pub relation: &'a PlonkWithAcceleratorLookupElementsVar,
    pub multiplicity: QM31Var,
    pub values: &'a [QM31Var],
}

impl<'a> RelationEntryVar<'a> {
    pub fn new(
        relation: &'a PlonkWithAcceleratorLookupElementsVar,
        multiplicity: QM31Var,
        values: &'a [QM31Var],
    ) -> Self {
        Self {
            relation,
            multiplicity,
            values,
        }
    }
}

pub struct LogupAtRowVar {
    pub interaction: usize,
    pub cumsum_shift: QM31Var,
    pub fracs: Vec<(QM31Var, QM31Var)>,
    pub is_finalized: bool,
    pub log_size: u32,
}

impl LogupAtRowVar {
    pub fn new(interaction: usize, total_sum: QM31Var, log_size: u32) -> Self {
        LogupAtRowVar {
            interaction,
            cumsum_shift: total_sum
                .mul_constant_m31(BaseField::from_u32_unchecked(1 << log_size).inverse()),
            fracs: vec![],
            is_finalized: true,
            log_size,
        }
    }
}

impl Drop for LogupAtRowVar {
    fn drop(&mut self) {
        assert!(self.is_finalized);
    }
}

pub struct EvalAtRowVar<'a> {
    pub col_index: [usize; 4],
    pub mask: TreeVec<ColumnVec<&'a Vec<QM31Var>>>,
    pub logup: LogupAtRowVar,
    pub denom_inverse: QM31Var,
    pub evaluation_accumulator: &'a mut PointEvaluationAccumulatorVar,
}

impl<'a> EvalAtRowVar<'a> {
    pub fn new(
        sampled_values: TreeVec<ColumnVec<&'a Vec<QM31Var>>>,
        total_sum: QM31Var,
        denom_inverse: QM31Var,
        log_size: u32,
        evaluation_accumulator: &'a mut PointEvaluationAccumulatorVar,
    ) -> Self {
        Self {
            col_index: [0usize; 4],
            mask: sampled_values,
            logup: LogupAtRowVar::new(INTERACTION_TRACE_IDX, total_sum, log_size),
            denom_inverse,
            evaluation_accumulator,
        }
    }

    pub fn next_trace_mask(&mut self) -> QM31Var {
        let [mask_item] = self.next_interaction_mask(ORIGINAL_TRACE_IDX, [0]);
        mask_item
    }

    pub fn get_preprocessed_column(&mut self, _column: PreProcessedColumnId) -> QM31Var {
        let [mask_item] = self.next_interaction_mask(PREPROCESSED_TRACE_IDX, [0]);
        mask_item
    }

    pub fn next_interaction_mask<const N: usize>(
        &mut self,
        interaction: usize,
        _offsets: [isize; N],
    ) -> [QM31Var; N] {
        let col_index = self.col_index[interaction];
        self.col_index[interaction] += 1;

        let mask = self.mask[interaction][col_index].clone();
        assert_eq!(mask.len(), N);
        mask.try_into().unwrap()
    }

    pub fn next_extension_interaction_mask<const N: usize>(
        &mut self,
        interaction: usize,
        offsets: [isize; N],
    ) -> [QM31Var; N] {
        let mut res_col_major =
            std::array::from_fn(|_| self.next_interaction_mask(interaction, offsets).into_iter());
        std::array::from_fn(|_| {
            Self::combine_ef(res_col_major.each_mut().map(|iter| iter.next().unwrap()))
        })
    }

    pub fn combine_ef(values: [QM31Var; SECURE_EXTENSION_DEGREE]) -> QM31Var {
        &(&(&values[0] + &values[1].shift_by_i()) + &values[2].shift_by_j())
            + &values[3].shift_by_ij()
    }

    pub fn add_to_relation(&mut self, entry: RelationEntryVar) {
        let mut denom = &entry.relation.alpha_powers[0] * &entry.values[0];
        for (alpha_power, entry_value) in entry
            .relation
            .alpha_powers
            .iter()
            .zip(entry.values.iter())
            .skip(1)
        {
            denom = &denom + &(alpha_power * entry_value);
        }
        denom = &denom - &entry.relation.z;

        if self.logup.fracs.is_empty() {
            self.logup.is_finalized = false;
        }
        self.logup.fracs.push((entry.multiplicity, denom));
    }

    pub fn add_constraint(&mut self, value: QM31Var) {
        self.evaluation_accumulator
            .accumulate(&value * &self.denom_inverse);
    }

    pub fn finalize_logup_in_pairs(&mut self) {
        let num_batches = self.logup.fracs.len().div_ceil(2);

        let mut batched_fracs = vec![];
        for chunk in self.logup.fracs.chunks(2) {
            let (num, denom) = if chunk.len() == 1 {
                chunk[0].clone()
            } else {
                let (p1, q1) = &chunk[0];
                let (p2, q2) = &chunk[1];

                (&(p1 * q2) + &(p2 * q1), q1 * q2)
            };
            batched_fracs.push((num, denom));
        }

        let mut prev_col_cumsum = QM31Var::zero(&self.logup.cumsum_shift.cs());
        for (num, denom) in batched_fracs.iter().take(num_batches - 1) {
            let [cur_cumsum] = self.next_extension_interaction_mask(self.logup.interaction, [0]);
            let diff = &cur_cumsum - &prev_col_cumsum;
            prev_col_cumsum = cur_cumsum;

            self.add_constraint(&(&diff * denom) - num);
        }

        for (num, denom) in batched_fracs.iter().skip(num_batches - 1) {
            let [prev_row_cumsum, cur_cumsum] =
                self.next_extension_interaction_mask(self.logup.interaction, [-1, 0]);

            let diff = &(&cur_cumsum - &prev_row_cumsum) - &prev_col_cumsum;
            let fixed_diff = &diff + &self.logup.cumsum_shift;

            self.add_constraint(&(&fixed_diff * denom) - num);
            self.logup.is_finalized = true;
        }
    }
}
