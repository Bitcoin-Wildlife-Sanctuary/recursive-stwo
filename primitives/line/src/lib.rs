use circle_plonk_dsl_constraint_system::var::{AllocVar, AllocationMode, Var};
use circle_plonk_dsl_constraint_system::ConstraintSystemRef;
use circle_plonk_dsl_fields::{M31Var, QM31Var};
use itertools::Itertools;
use num_traits::One;
use std::ops::Neg;
use stwo::core::fields::m31::M31;
use stwo::core::poly::line::LinePoly;

#[derive(Clone, Debug)]
pub struct LinePolyVar {
    pub cs: ConstraintSystemRef,
    pub coeffs: Vec<QM31Var>,
}

impl Var for LinePolyVar {
    type Value = LinePoly;

    fn cs(&self) -> ConstraintSystemRef {
        self.cs.clone()
    }
}

impl AllocVar for LinePolyVar {
    fn new_variables(cs: &ConstraintSystemRef, value: &Self::Value, mode: AllocationMode) -> Self {
        let coeffs = value
            .coeffs
            .iter()
            .map(|v| QM31Var::new_variables(cs, v, mode))
            .collect_vec();
        LinePolyVar {
            cs: cs.clone(),
            coeffs,
        }
    }
}

impl LinePolyVar {
    pub fn eval_at_point(&self, x: &M31Var) -> QM31Var {
        let cs = self.cs();
        let mut x = x.clone();
        let line_poly_log_size = self.coeffs.len().ilog2();

        let mut doublings = vec![];
        doublings.push(x.clone());
        for _ in 1..line_poly_log_size {
            let x_sq = &x * &x;
            x = &x_sq + &x_sq;
            x = &x + &M31Var::new_constant(&cs, &M31::one().neg());
            doublings.push(x.clone())
        }

        pub fn fold(values: &[QM31Var], folding_factors: &[M31Var]) -> QM31Var {
            let n = values.len();
            assert_eq!(n, 1 << folding_factors.len());
            if n == 1 {
                return values[0].clone();
            }
            let (lhs_values, rhs_values) = values.split_at(n / 2);
            let (folding_factor, folding_factors) = folding_factors.split_first().unwrap();
            let lhs_val = fold(lhs_values, folding_factors);
            let rhs_val = fold(rhs_values, folding_factors);
            &lhs_val + &(&rhs_val * folding_factor)
        }

        fold(&self.coeffs, &doublings)
    }
}

#[cfg(test)]
mod test {
    use crate::LinePolyVar;
    use circle_plonk_dsl_constraint_system::var::AllocVar;
    use circle_plonk_dsl_constraint_system::ConstraintSystemRef;
    use circle_plonk_dsl_fields::{M31Var, QM31Var};
    use rand::prelude::StdRng;
    use rand::{Rng, SeedableRng};
    use stwo::core::circle::M31_CIRCLE_GEN;
    use stwo::core::poly::line::LinePoly;

    #[test]
    fn test_line_poly_var() {
        let mut prng = StdRng::seed_from_u64(0);

        let mut coeffs = vec![];
        for _ in 0..16 {
            coeffs.push(prng.gen());
        }

        let point = M31_CIRCLE_GEN.mul(prng.gen::<u128>());

        let line_poly = LinePoly::new(coeffs);
        let expected = line_poly.eval_at_point(point.x.into());

        let cs = ConstraintSystemRef::new_plonk_with_poseidon_ref();
        let line_poly_var = LinePolyVar::new_witness(&cs, &line_poly);
        let res = line_poly_var.eval_at_point(&M31Var::new_witness(&cs, &point.x));

        res.equalverify(&QM31Var::new_witness(&cs, &expected));

        cs.pad();
        cs.check_arithmetics();
    }
}
