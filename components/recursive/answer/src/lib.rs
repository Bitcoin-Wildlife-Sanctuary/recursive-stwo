use crate::data_structures::{
    accumulate_row_quotients_var, quotient_constants_var, ColumnSampleBatchVar, PointSampleVar,
    ShiftIndex,
};
use circle_plonk_dsl_circle::{CirclePointM31Var, CirclePointQM31Var};
use circle_plonk_dsl_constraint_system::dvar::DVar;
use circle_plonk_dsl_constraint_system::ConstraintSystemRef;
use circle_plonk_dsl_data_structures::{DecommitmentVar, PlonkWithPoseidonProofVar};
use circle_plonk_dsl_fiat_shamir::FiatShamirResults;
use circle_plonk_dsl_fields::{M31Var, QM31Var};
use circle_plonk_dsl_hints::{AnswerHints, DecommitHints, FiatShamirHints};
use circle_plonk_dsl_query::{PointCarryingQuery, QueryPositionsPerLogSize};
use itertools::{izip, multiunzip, Itertools};
use std::cmp::Reverse;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::iter::zip;
use std::ops::Add;
use stwo_prover::constraint_framework::PREPROCESSED_TRACE_IDX;
use stwo_prover::core::pcs::{PcsConfig, TreeVec};
use stwo_prover::core::poly::circle::CanonicCoset;
use stwo_prover::core::ColumnVec;

pub mod data_structures;

pub struct AnswerResults {
    pub cs: ConstraintSystemRef,
    pub query_positions_per_log_size: QueryPositionsPerLogSize,
    pub fri_answers: ColumnVec<Vec<QM31Var>>,
    pub domain_points: ColumnVec<Vec<CirclePointM31Var>>,
}

impl AnswerResults {
    pub fn compute(
        oods_point: &CirclePointQM31Var,
        fiat_shamir_hints: &FiatShamirHints,
        fiat_shamir_results: &FiatShamirResults,
        fri_answer_hints: &AnswerHints,
        decommit_hints: &DecommitHints,
        proof: &PlonkWithPoseidonProofVar,
        pcs_config: PcsConfig,
    ) -> AnswerResults {
        let cs = oods_point.cs();

        let mut all_shifts_plonk = HashSet::new();
        let mut all_shifts_poseidon = HashSet::new();
        for round in fiat_shamir_hints.mask_plonk.iter() {
            for column in round.iter() {
                for &shift in column.iter() {
                    all_shifts_plonk.insert(shift);
                }
            }
        }
        for round in fiat_shamir_hints.mask_poseidon.iter() {
            for column in round.iter() {
                for &shift in column.iter() {
                    all_shifts_poseidon.insert(shift);
                }
            }
        }

        let trace_step_plonk = CanonicCoset::new(fiat_shamir_hints.log_size_plonk).step();
        let trace_step_poseidon = CanonicCoset::new(fiat_shamir_hints.log_size_poseidon).step();

        let mut shifted_points_plonk = HashMap::<isize, CirclePointQM31Var>::new();
        let mut shifted_points_poseidon = HashMap::<isize, CirclePointQM31Var>::new();
        for &i in all_shifts_plonk.iter() {
            shifted_points_plonk.insert(i, oods_point.add(&trace_step_plonk.mul_signed(i)));
        }
        for &i in all_shifts_poseidon.iter() {
            shifted_points_poseidon.insert(i, oods_point.add(&trace_step_poseidon.mul_signed(i)));
        }

        let mut mask_points_plonk: TreeVec<ColumnVec<Vec<(ShiftIndex, CirclePointQM31Var)>>> =
            fiat_shamir_hints.mask_plonk.as_ref().map_cols(|column| {
                column
                    .iter()
                    .map(|shift| {
                        (
                            ShiftIndex::from_shift(*shift, fiat_shamir_hints.log_size_plonk),
                            shifted_points_plonk.get(shift).unwrap().clone(),
                        )
                    })
                    .collect_vec()
            });
        mask_points_plonk[PREPROCESSED_TRACE_IDX] =
            vec![vec![(ShiftIndex::Zero, oods_point.clone())]; 10];
        let mut mask_points_poseidon: TreeVec<ColumnVec<Vec<(ShiftIndex, CirclePointQM31Var)>>> =
            fiat_shamir_hints.mask_poseidon.as_ref().map_cols(|column| {
                column
                    .iter()
                    .map(|shift| {
                        (
                            ShiftIndex::from_shift(*shift, fiat_shamir_hints.log_size_poseidon),
                            shifted_points_poseidon.get(shift).unwrap().clone(),
                        )
                    })
                    .collect_vec()
            });
        mask_points_poseidon[PREPROCESSED_TRACE_IDX] =
            vec![vec![(ShiftIndex::Zero, oods_point.clone())]; 40];

        assert_eq!(
            mask_points_plonk.len(),
            fiat_shamir_hints.sample_points.len() - 1
        );
        for (round_idx, (round_plonk, round_poseidon)) in mask_points_plonk
            .iter()
            .zip(mask_points_poseidon.iter())
            .enumerate()
            .take(3)
        {
            assert_eq!(
                round_plonk.len() + round_poseidon.len(),
                fiat_shamir_hints.sample_points[round_idx].len(),
                "round_idx = {}",
                round_idx
            );
            for (column_idx, column) in round_plonk.iter().enumerate() {
                assert_eq!(
                    column.len(),
                    fiat_shamir_hints.sample_points[round_idx][column_idx].len()
                );
                for (shift_idx, (_, shifted_point)) in column.iter().enumerate() {
                    assert_eq!(
                        shifted_point.x.value(),
                        fiat_shamir_hints.sample_points[round_idx][column_idx][shift_idx].x
                    );
                    assert_eq!(
                        shifted_point.y.value(),
                        fiat_shamir_hints.sample_points[round_idx][column_idx][shift_idx].y
                    );
                }
            }

            for (column_idx, column) in round_poseidon.iter().enumerate() {
                assert_eq!(
                    column.len(),
                    fiat_shamir_hints.sample_points[round_idx][round_plonk.len() + column_idx]
                        .len()
                );
                for (shift_idx, (_, shifted_point)) in column.iter().enumerate() {
                    assert_eq!(
                        shifted_point.x.value(),
                        fiat_shamir_hints.sample_points[round_idx][round_plonk.len() + column_idx]
                            [shift_idx]
                            .x
                    );
                    assert_eq!(
                        shifted_point.y.value(),
                        fiat_shamir_hints.sample_points[round_idx][round_plonk.len() + column_idx]
                            [shift_idx]
                            .y
                    );
                }
            }
        }

        let mut sampled_points =
            TreeVec::concat_cols([mask_points_plonk, mask_points_poseidon].into_iter());
        sampled_points.push(vec![vec![(ShiftIndex::Zero, oods_point.clone())]; 4]);

        let samples = sampled_points
            .zip_cols(proof.stark_proof.sampled_values.clone())
            .map_cols(|(sampled_points, sampled_values)| {
                zip(sampled_points, sampled_values)
                    .map(|((shift, point), value)| PointSampleVar {
                        shift,
                        point,
                        value,
                    })
                    .collect_vec()
            });

        let query_positions_per_log_size = QueryPositionsPerLogSize::new(
            pcs_config.fri_config.log_blowup_factor + 1
                ..=fiat_shamir_hints.max_first_layer_column_log_size,
            &fiat_shamir_results.raw_queries,
        );

        for &column_log_size in fiat_shamir_hints.all_log_sizes.iter() {
            let mut sorted_queries = vec![];
            for query in query_positions_per_log_size[column_log_size].iter() {
                sorted_queries.push(query.bits.get_value().0 as usize);
            }
            sorted_queries.sort_unstable();
            sorted_queries.dedup();

            if column_log_size == fiat_shamir_hints.max_first_layer_column_log_size {
                assert_eq!(sorted_queries.len(), pcs_config.fri_config.n_queries,
                    "The implementation does not support the situation when the first {} attempts in sampling queries end up duplicated queries",
                           pcs_config.fri_config.n_queries
                );
            }

            assert_eq!(
                sorted_queries,
                fiat_shamir_hints.query_positions_per_log_size[&column_log_size]
            );
        }
        for &column_log_size in fiat_shamir_hints.all_log_sizes.iter() {
            let mut unsorted_queries = vec![];
            for query in query_positions_per_log_size[column_log_size].iter() {
                unsorted_queries.push(query.bits.get_value().0 as usize);
            }

            assert_eq!(
                unsorted_queries,
                fiat_shamir_hints.raw_query_positions_per_log_size[&column_log_size]
            );
        }

        let mut decommitment_var = DecommitmentVar::new(&cs, &decommit_hints);
        for (i, query) in query_positions_per_log_size[*fiat_shamir_hints.trees_log_sizes[0]
            .iter()
            .max()
            .unwrap()
            + fiat_shamir_hints.log_blowup_factor]
            .iter()
            .enumerate()
        {
            decommitment_var.precomputed_proofs[i]
                .verify(&fiat_shamir_results.preprocessed_commitment, &query.bits);
        }

        for (i, query) in query_positions_per_log_size[*fiat_shamir_hints.trees_log_sizes[1]
            .iter()
            .max()
            .unwrap()
            + fiat_shamir_hints.log_blowup_factor]
            .iter()
            .enumerate()
        {
            decommitment_var.trace_proofs[i]
                .verify(&fiat_shamir_results.trace_commitment, &query.bits);
        }
        for (i, query) in query_positions_per_log_size[*fiat_shamir_hints.trees_log_sizes[2]
            .iter()
            .max()
            .unwrap()
            + fiat_shamir_hints.log_blowup_factor]
            .iter()
            .enumerate()
        {
            decommitment_var.interaction_proofs[i].verify(
                &fiat_shamir_results.interaction_trace_commitment,
                &query.bits,
            );
        }
        for (i, query) in query_positions_per_log_size
            [fiat_shamir_hints.max_first_layer_column_log_size]
            .iter()
            .enumerate()
        {
            decommitment_var.composition_proofs[i]
                .verify(&fiat_shamir_results.composition_commitment, &query.bits);
        }

        let mut queried_values = BTreeMap::new();
        for &log_size in fiat_shamir_hints.all_log_sizes.iter() {
            let mut queried_values_this_log_size = Vec::new();
            for (i, _) in query_positions_per_log_size[log_size].iter().enumerate() {
                let mut v = vec![];
                v.extend_from_slice(
                    &decommitment_var.precomputed_proofs[i]
                        .columns
                        .get(&(log_size as usize))
                        .unwrap_or(&vec![]),
                );
                v.extend_from_slice(
                    &decommitment_var.trace_proofs[i]
                        .columns
                        .get(&(log_size as usize))
                        .unwrap_or(&vec![]),
                );
                v.extend_from_slice(
                    &decommitment_var.interaction_proofs[i]
                        .columns
                        .get(&(log_size as usize))
                        .unwrap_or(&vec![]),
                );
                v.extend_from_slice(
                    &decommitment_var.composition_proofs[i]
                        .columns
                        .get(&(log_size as usize))
                        .unwrap_or(&vec![]),
                );
                queried_values_this_log_size.push(v);
            }
            queried_values.insert(log_size, queried_values_this_log_size);
        }

        let mut fri_answers = ColumnVec::<Vec<QM31Var>>::new();
        let mut domain_points = ColumnVec::<Vec<CirclePointM31Var>>::new();

        izip!(
            fiat_shamir_hints.column_log_sizes.clone().flatten(),
            samples.flatten().iter()
        )
        .sorted_by_key(|(log_size, ..)| Reverse(*log_size))
        .chunk_by(|(log_size, ..)| *log_size)
        .into_iter()
        .for_each(|(log_size, tuples)| {
            let (_, samples): (Vec<_>, Vec<_>) = multiunzip(tuples);
            let (domain_points_per_log_size, fri_answers_per_log_size) =
                Self::fri_answers_for_log_size(
                    &samples,
                    &fiat_shamir_results.after_sampled_values_random_coeff,
                    &query_positions_per_log_size[log_size],
                    &queried_values[&log_size],
                );
            domain_points.push(domain_points_per_log_size);
            fri_answers.push(fri_answers_per_log_size);
        });

        let mut log_sizes = fiat_shamir_hints
            .all_log_sizes
            .iter()
            .copied()
            .collect_vec();
        log_sizes.sort_by_key(|log_size| Reverse(*log_size));

        for ((log_size, fri_answers), sorted_fri_answers) in log_sizes
            .iter()
            .zip(fri_answers.iter())
            .zip(fri_answer_hints.fri_answers.iter())
        {
            let mut map = BTreeMap::new();
            for (k, v) in fiat_shamir_hints.query_positions_per_log_size[log_size]
                .iter()
                .zip(sorted_fri_answers.iter())
            {
                map.insert(*k, *v);
            }

            for (k, v) in query_positions_per_log_size[*log_size]
                .iter()
                .zip(fri_answers.iter())
            {
                assert_eq!(
                    *map.get(&(k.bits.get_value().0 as usize)).unwrap(),
                    v.value()
                );
            }
        }

        Self {
            cs,
            query_positions_per_log_size,
            fri_answers,
            domain_points,
        }
    }

    pub fn fri_answers_for_log_size(
        samples: &[&Vec<PointSampleVar>],
        random_coeff: &QM31Var,
        query_positions: &[PointCarryingQuery],
        queried_values: &[Vec<M31Var>],
    ) -> (Vec<CirclePointM31Var>, Vec<QM31Var>) {
        let sample_batches = ColumnSampleBatchVar::new_vec(samples);
        // TODO(ilya): Is it ok to use the same `random_coeff` for all log sizes.
        let quotient_constants = quotient_constants_var(&sample_batches, random_coeff);

        let mut domain_points_at_queries = Vec::new();
        let mut quotient_evals_at_queries = Vec::new();
        for (query_position, queried_values_at_row) in
            query_positions.iter().zip(queried_values.iter())
        {
            let domain_point = query_position.get_point();
            quotient_evals_at_queries.push(accumulate_row_quotients_var(
                &sample_batches,
                &queried_values_at_row,
                &quotient_constants,
                &domain_point,
            ));
            domain_points_at_queries.push(domain_point);
        }

        (domain_points_at_queries, quotient_evals_at_queries)
    }
}

#[cfg(test)]
mod test {
    use crate::AnswerResults;
    use circle_plonk_dsl_circle::CirclePointQM31Var;
    use circle_plonk_dsl_constraint_system::dvar::AllocVar;
    use circle_plonk_dsl_constraint_system::ConstraintSystemRef;
    use circle_plonk_dsl_data_structures::PlonkWithPoseidonProofVar;
    use circle_plonk_dsl_fiat_shamir::FiatShamirResults;
    use circle_plonk_dsl_fields::QM31Var;
    use circle_plonk_dsl_hints::{AnswerHints, DecommitHints, FiatShamirHints};
    use num_traits::One;
    use stwo_prover::core::fields::qm31::QM31;
    use stwo_prover::core::fri::FriConfig;
    use stwo_prover::core::pcs::PcsConfig;
    use stwo_prover::core::vcs::poseidon31_merkle::{
        Poseidon31MerkleChannel, Poseidon31MerkleHasher,
    };
    use stwo_prover::examples::plonk_with_poseidon::air::{
        prove_plonk_with_poseidon, verify_plonk_with_poseidon, PlonkWithPoseidonProof,
    };

    #[test]
    fn test_answer() {
        let proof: PlonkWithPoseidonProof<Poseidon31MerkleHasher> =
            bincode::deserialize(include_bytes!("../../../test_data/small_proof.bin")).unwrap();
        let config = PcsConfig {
            pow_bits: 20,
            fri_config: FriConfig::new(0, 5, 16),
        };

        let fiat_shamir_hints = FiatShamirHints::new(&proof, config, &[(1, QM31::one())]);

        let cs = ConstraintSystemRef::new_qm31_ref();
        let mut proof_var = PlonkWithPoseidonProofVar::new_witness(&cs, &proof);

        let fiat_shamir_results = FiatShamirResults::compute(
            &fiat_shamir_hints,
            &mut proof_var,
            config,
            &[(1, QM31Var::one(&cs))],
        );
        let fri_answer_hints = AnswerHints::compute(&fiat_shamir_hints, &proof);
        let decommitment_hints = DecommitHints::compute(&fiat_shamir_hints, &proof);

        AnswerResults::compute(
            &CirclePointQM31Var::new_witness(&cs, &fiat_shamir_hints.oods_point),
            &fiat_shamir_hints,
            &fiat_shamir_results,
            &fri_answer_hints,
            &decommitment_hints,
            &proof_var,
            config,
        );

        cs.pad();
        cs.check_arithmetics();
        cs.populate_logup_arguments();
        cs.check_poseidon_invocations();

        let (plonk, mut poseidon) = cs.generate_qm31_circuit();
        let proof =
            prove_plonk_with_poseidon::<Poseidon31MerkleChannel>(config, &plonk, &mut poseidon);
        verify_plonk_with_poseidon::<Poseidon31MerkleChannel>(
            proof,
            config,
            &[
                (1, QM31::one()),
                (2, QM31::from_u32_unchecked(0, 1, 0, 0)),
                (3, QM31::from_u32_unchecked(0, 0, 1, 0)),
            ],
        )
        .unwrap();
    }
}
