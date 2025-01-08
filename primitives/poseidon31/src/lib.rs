use crate::implementation::poseidon2_permute;
use circle_plonk_dsl_constraint_system::accelerators::ID_POSEIDON2;
use circle_plonk_dsl_constraint_system::dvar::{AllocVar, AllocationMode, DVar};
use circle_plonk_dsl_constraint_system::ConstraintSystemRef;
use circle_plonk_dsl_fields::M31Var;
use num_traits::Zero;
use stwo_prover::core::fields::m31::M31;

pub mod implementation;
mod parameters;

#[derive(Debug, Clone)]
pub struct Poseidon2State {
    pub cs: ConstraintSystemRef,
    pub value: [M31; 16],
    pub variables: usize,
}

impl Poseidon2State {
    pub fn zero(cs: &ConstraintSystemRef) -> Self {
        let r = if let Some(r) = cs.get_cache("poseidon2_zero") {
            r
        } else {
            let r = cs.new_variables(&[M31::zero(); 16], AllocationMode::Constant);
            cs.set_cache("poseidon2_zero", r.clone());
            r
        };

        Self {
            cs: cs.clone(),
            value: [M31::zero(); 16],
            variables: r,
        }
    }
}

impl DVar for Poseidon2State {
    type Value = [M31; 16];

    fn cs(&self) -> ConstraintSystemRef {
        self.cs.clone()
    }
}

impl AllocVar for Poseidon2State {
    fn new_variables(cs: &ConstraintSystemRef, value: &Self::Value, mode: AllocationMode) -> Self {
        Self {
            cs: cs.clone(),
            value: value.clone(),
            variables: cs.new_variables(value, mode),
        }
    }
}

impl Poseidon2State {
    pub fn permute(&self) -> Poseidon2State {
        let mut state = self.value.clone();
        poseidon2_permute(&mut state);
        let res = Poseidon2State::new_witness(&self.cs(), &state);
        self.cs.add_accelerator_entry(ID_POSEIDON2, res.variables);
        res
    }

    pub fn to_m31(&self) -> Vec<M31Var> {
        let mut m31 = vec![];
        for i in 0..8 {
            m31.push(M31Var {
                cs: self.cs(),
                value: self.value[i],
                variable: self.variables[i],
            });
        }
        m31
    }
}
