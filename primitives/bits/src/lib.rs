use circle_plonk_dsl_constraint_system::dvar::{AllocVar, AllocationMode, DVar};
use circle_plonk_dsl_constraint_system::ConstraintSystemRef;
use circle_plonk_dsl_fields::M31Var;
use num_traits::{One, Zero};
use stwo_prover::core::fields::m31::M31;

#[derive(Clone)]
pub struct BitsVar {
    pub cs: ConstraintSystemRef,
    pub value: Vec<bool>,
    pub variables: Vec<usize>,
}

impl DVar for BitsVar {
    type Value = Vec<bool>;

    fn cs(&self) -> ConstraintSystemRef {
        self.cs.clone()
    }
}

impl AllocVar for BitsVar {
    fn new_variables(cs: &ConstraintSystemRef, value: &Self::Value, mode: AllocationMode) -> Self {
        let mut variables = Vec::with_capacity(value.len());
        for &b in value.iter() {
            let n = if b { M31::one() } else { M31::zero() };
            variables.push(cs.new_variables(&[n], mode));
        }

        Self {
            cs: cs.clone(),
            value: value.clone(),
            variables,
        }
    }
}

impl BitsVar {
    pub fn from_m31(v: &M31Var, l: usize) -> BitsVar {
        let cs = v.cs();
        let mut bools = Vec::with_capacity(l);

        let mut cur = v.value.0;
        for _ in 0..l {
            bools.push(cur & 1 != 0);
            cur >>= 1;
        }

        let res = BitsVar::new_witness(&cs, &bools);

        let cast_into_m31var = |b: bool, v: usize| M31Var {
            cs: cs.clone(),
            value: if b { M31::one() } else { M31::zero() },
            variable: v,
        };

        let mut reconstructed = cast_into_m31var(res.value[0], res.variables[0]);
        for i in 1..l {
            reconstructed = &reconstructed
                + &cast_into_m31var(res.value[i], res.variables[i]).mul_constant(M31::from(1 << i));
        }
        reconstructed.equalverify(v);

        res
    }
}
