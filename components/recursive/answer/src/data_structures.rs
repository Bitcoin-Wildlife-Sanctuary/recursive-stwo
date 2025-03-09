use circle_plonk_dsl_circle::{CirclePointM31Var, CirclePointQM31Var};
use circle_plonk_dsl_constraint_system::dvar::{AllocVar, DVar};
use circle_plonk_dsl_fields::{CM31Var, M31Var, QM31Var};
use indexmap::IndexMap;
use itertools::{izip, zip_eq};
use num_traits::Zero;
use std::ops::Neg;
use stwo_prover::core::circle::CirclePoint;
use stwo_prover::core::fields::m31::M31;
use stwo_prover::core::fields::qm31::QM31;
use stwo_prover::core::fields::ComplexConjugate;

#[derive(Debug, Clone, Copy, Hash, Eq, PartialEq)]
pub enum ShiftIndex {
    Shift(isize, u32),
    Zero,
}

impl ShiftIndex {
    pub fn from_shift(shift: isize, log_size: u32) -> Self {
        if shift == 0 {
            Self::Zero
        } else {
            Self::Shift(shift, log_size)
        }
    }
}

#[derive(Debug, Clone)]
pub struct PointSampleVar {
    pub shift: ShiftIndex,
    pub point: CirclePointQM31Var,
    pub value: QM31Var,
}

#[derive(Debug, Clone)]
pub struct ColumnSampleBatchVar {
    pub point: CirclePointQM31Var,
    pub columns_and_values: Vec<(usize, QM31Var)>,
}

impl ColumnSampleBatchVar {
    pub fn new_vec(samples: &[&Vec<PointSampleVar>]) -> Vec<Self> {
        let mut grouped_samples = IndexMap::new();
        for (column_index, samples) in samples.iter().enumerate() {
            for sample in samples.iter() {
                grouped_samples
                    .entry(sample.shift)
                    .or_insert_with(Vec::new)
                    .push((sample.point.clone(), column_index, sample.value.clone()));
            }
        }
        grouped_samples
            .into_iter()
            .map(|(_, columns_and_values)| ColumnSampleBatchVar {
                point: columns_and_values[0].0.clone(),
                columns_and_values: columns_and_values
                    .iter()
                    .map(|v| (v.1, v.2.clone()))
                    .collect(),
            })
            .collect()
    }
}

pub struct QuotientConstantsVar {
    pub line_coeffs: Vec<Vec<(QM31Var, QM31Var, QM31Var)>>,
    pub batch_random_coeffs: Vec<QM31Var>,
}

pub fn accumulate_row_quotients_var(
    sample_batches: &[ColumnSampleBatchVar],
    queried_values_at_row: &[M31Var],
    quotient_constants: &QuotientConstantsVar,
    domain_point: &CirclePointM31Var,
) -> QM31Var {
    let cs = domain_point.cs();
    let denominator_inverses = denominator_inverses_var(sample_batches, domain_point);
    let mut row_accumulator = QM31Var::zero(&cs);
    for (sample_batch, line_coeffs, batch_coeff, denominator_inverse) in izip!(
        sample_batches,
        &quotient_constants.line_coeffs,
        &quotient_constants.batch_random_coeffs,
        denominator_inverses
    ) {
        let mut numerator = QM31Var::zero(&cs);
        for ((column_index, _), (a, b, c)) in zip_eq(&sample_batch.columns_and_values, line_coeffs)
        {
            let value = &queried_values_at_row[*column_index] * c;
            // The numerator is a line equation passing through
            //   (sample_point.y, sample_value), (conj(sample_point), conj(sample_value))
            // evaluated at (domain_point.y, value).
            // When substituting a polynomial in this line equation, we get a polynomial with a root
            // at sample_point and conj(sample_point) if the original polynomial had the values
            // sample_value and conj(sample_value) at these points.
            let linear_term = &(a * &domain_point.y) + b;
            numerator = &numerator + &(&value - &linear_term);
        }

        row_accumulator = &(&row_accumulator * batch_coeff) + &(&numerator * &denominator_inverse);
    }
    row_accumulator
}

pub fn denominator_inverses_var(
    sample_batches: &[ColumnSampleBatchVar],
    domain_point: &CirclePointM31Var,
) -> Vec<CM31Var> {
    let mut denominator_inverses = Vec::new();

    // We want a P to be on a line that passes through a point Pr + uPi in QM31^2, and its conjugate
    // Pr - uPi. Thus, Pr - P is parallel to Pi. Or, (Pr - P).x * Pi.y - (Pr - P).y * Pi.x = 0.
    for sample_batch in sample_batches {
        // Extract Pr, Pi.
        let [prx, pix] = sample_batch.point.x.decompose_cm31();
        let [pry, piy] = sample_batch.point.y.decompose_cm31();

        let mut a = &prx - &domain_point.x;
        a = &a * &piy;

        let mut b = &pry - &domain_point.y;
        b = &b * &pix;

        denominator_inverses.push((&a - &b).inv());
    }

    denominator_inverses
}

pub fn quotient_constants_var(
    sample_batches: &[ColumnSampleBatchVar],
    random_coeff: &QM31Var,
) -> QuotientConstantsVar {
    QuotientConstantsVar {
        line_coeffs: column_line_coeffs_var(sample_batches, random_coeff),
        batch_random_coeffs: batch_random_coeffs_var(sample_batches, random_coeff),
    }
}

pub fn complex_conjugate_line_coeffs_var(
    point: &CirclePointQM31Var,
    value: &QM31Var,
    alpha: &QM31Var,
) -> (QM31Var, QM31Var, QM31Var) {
    assert_ne!(
        point.y.value(),
        point.y.value().complex_conjugate(),
        "Cannot evaluate a line with a single point ({:?}).",
        CirclePoint {
            x: point.x.value(),
            y: point.y.value()
        }
    );

    let [value0, value1] = value.decompose_cm31();
    let [y0, y1] = point.y.decompose_cm31();

    let a = value1.clone();
    let c = y1.clone();
    let b = &(&value0 * &y1) - &(&value1 * &y0);

    (alpha * &a, alpha * &b, alpha * &c)
}

pub fn column_line_coeffs_var(
    sample_batches: &[ColumnSampleBatchVar],
    random_coeff: &QM31Var,
) -> Vec<Vec<(QM31Var, QM31Var, QM31Var)>> {
    let cs = random_coeff.cs();
    sample_batches
        .iter()
        .map(|sample_batch| {
            let mut alpha = QM31Var::new_constant(
                &cs,
                &QM31::from_m31(M31::zero(), M31::zero(), M31::from(2).neg(), M31::zero()),
            );
            sample_batch
                .columns_and_values
                .iter()
                .map(|(_, sampled_value)| {
                    alpha = &alpha * random_coeff;
                    complex_conjugate_line_coeffs_var(&sample_batch.point, sampled_value, &alpha)
                })
                .collect()
        })
        .collect()
}

pub fn batch_random_coeffs_var(
    sample_batches: &[ColumnSampleBatchVar],
    random_coeff: &QM31Var,
) -> Vec<QM31Var> {
    sample_batches
        .iter()
        .map(|sb| random_coeff.pow(sb.columns_and_values.len() as u128))
        .collect()
}
