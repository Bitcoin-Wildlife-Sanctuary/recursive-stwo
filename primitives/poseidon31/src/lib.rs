use crate::implementation::poseidon2_permute;
use circle_plonk_dsl_constraint_system::dvar::{AllocVar, AllocationMode, DVar};
use circle_plonk_dsl_constraint_system::ConstraintSystemRef;
use circle_plonk_dsl_fields::M31Var;
use num_traits::Zero;
use stwo_prover::core::fields::m31::M31;

pub mod implementation;
mod parameters;

#[derive(Debug, Clone)]
pub struct Poseidon2HalfStateRef {
    pub cs: ConstraintSystemRef,
    pub value: [M31; 8],
    pub half_state_variable: usize,
    pub addr_variable: usize,
}

impl DVar for Poseidon2HalfStateRef {
    type Value = [M31; 8];

    fn cs(&self) -> ConstraintSystemRef {
        self.cs.clone()
    }
}

#[derive(Debug, Clone)]
pub struct Poseidon2HalfState {
    pub cs: ConstraintSystemRef,
    pub value: [M31; 8],
    pub variables: usize,
}

impl Poseidon2HalfStateRef {
    pub fn zero(cs: &ConstraintSystemRef) -> Self {
        if let Some(addr_variable) = cs.get_cache("poseidon2 zero_half addr") {
            Self {
                cs: cs.clone(),
                value: [M31::zero(); 8],
                half_state_variable: cs.get_cache("poseidon2 zero_half").unwrap(),
                addr_variable,
            }
        } else {
            let r = Self::new_constant(cs, &[M31::zero(); 8]);
            cs.set_cache("poseidon2 zero_half addr", r.addr_variable);
            cs.set_cache("poseidon2 zero_half", r.half_state_variable);
            r
        }
    }

    pub fn to_m31(&self) -> Vec<M31Var> {
        let mut m31 = vec![];
        let variable = self.half_state_variable;
        for i in 0..8 {
            m31.push(M31Var {
                cs: self.cs(),
                value: self.value[i],
                variable: variable + i,
            });
        }
        m31
    }

    pub fn permute(
        left: &Poseidon2HalfStateRef,
        right: &Poseidon2HalfStateRef,
    ) -> (Poseidon2HalfStateRef, Poseidon2HalfStateRef) {
        let cs = left.cs().and(&right.cs());

        let mut state: [M31; 16] = std::array::from_fn(|i| {
            if i < 8 {
                left.value[i]
            } else {
                right.value[i - 8]
            }
        });

        poseidon2_permute(&mut state);

        for i in 0..8 {
            state[i] = state[i] + left.value[i];
        }

        let new_left = Poseidon2HalfStateRef::new_variables(
            &cs,
            &std::array::from_fn(|i| state[i]),
            AllocationMode::Witness,
        );

        let new_right = Poseidon2HalfStateRef::new_variables(
            &cs,
            &std::array::from_fn(|i| state[8 + i]),
            AllocationMode::Witness,
        );

        cs.invoke_poseidon_accelerator(
            left.addr_variable,
            right.addr_variable,
            new_left.addr_variable,
            new_right.addr_variable,
        );

        (new_left, new_right)
    }
}

impl AllocVar for Poseidon2HalfStateRef {
    fn new_variables(cs: &ConstraintSystemRef, value: &Self::Value, mode: AllocationMode) -> Self {
        let half_state_variable = cs.new_variables(value, mode);
        Self {
            cs: cs.clone(),
            value: value.clone(),
            half_state_variable,
            addr_variable: cs
                .new_variables(&[M31::from(half_state_variable)], AllocationMode::Constant),
        }
    }
}
