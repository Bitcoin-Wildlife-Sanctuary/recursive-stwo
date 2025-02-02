use crate::implementation::poseidon2_permute;
use circle_plonk_dsl_constraint_system::dvar::{AllocVar, AllocationMode, DVar};
use circle_plonk_dsl_constraint_system::ConstraintSystemRef;
use circle_plonk_dsl_fields::{M31Var, QM31Var};
use num_traits::{One, Zero};
use std::ops::Neg;
use stwo_prover::core::fields::m31::M31;
use stwo_prover::core::fields::qm31::QM31;
use stwo_prover::examples::plonk_with_poseidon::poseidon::PoseidonEntry;

pub mod implementation;
mod parameters;

#[derive(Debug, Clone)]
pub struct Poseidon2HalfStateRef {
    pub cs: ConstraintSystemRef,
    pub value: [M31; 8],
    pub left_variable: usize,
    pub right_variable: usize,
    pub half_state_variable: usize,
    pub addr_variable: usize,
    pub disabled: bool,
}

impl Poseidon2HalfStateRef {
    pub fn is_allocated(&self) -> bool {
        self.addr_variable != 0
    }

    pub fn new_single_use_witness(cs: &ConstraintSystemRef, value: &[M31; 8]) -> Self {
        Self {
            cs: cs.clone(),
            value: *value,
            left_variable: 0,
            right_variable: 0,
            half_state_variable: 0,
            addr_variable: 0,
            disabled: false,
        }
    }

    pub fn from_m31(slice: &[M31Var]) -> Self {
        assert_eq!(slice.len(), 8);
        let left_variable = QM31Var::from_m31(&slice[0], &slice[1], &slice[2], &slice[3]);
        let right_variable = QM31Var::from_m31(&slice[4], &slice[5], &slice[6], &slice[7]);

        let cs = left_variable.cs().and(&right_variable.cs());
        let left_variable = left_variable.variable;
        let right_variable = right_variable.variable;

        let half_state_variable = cs.mul(left_variable, right_variable);
        let addr_variable = cs.new_m31(M31::from(half_state_variable), AllocationMode::Constant);

        Poseidon2HalfStateRef {
            cs,
            value: std::array::from_fn(|i| slice[i].value),
            left_variable,
            right_variable,
            half_state_variable,
            addr_variable,
            disabled: false,
        }
    }

    pub fn from_qm31(a: &QM31Var, b: &QM31Var) -> Self {
        let cs = a.cs().and(&b.cs());
        let left_variable = a.variable;
        let right_variable = b.variable;
        let half_state_variable = cs.mul(left_variable, right_variable);
        let addr_variable = cs.new_m31(M31::from(half_state_variable), AllocationMode::Constant);

        let a_arr = a.value.to_m31_array();
        let b_arr = b.value.to_m31_array();

        Self {
            cs,
            value: std::array::from_fn(|i| if i < 4 { a_arr[i] } else { b_arr[i - 4] }),
            left_variable,
            right_variable,
            half_state_variable,
            addr_variable,
            disabled: false,
        }
    }

    pub fn swap_compress(
        a0: &Poseidon2HalfStateRef,
        a1: &Poseidon2HalfStateRef,
        bit_value: bool,
        bit_variable: usize,
    ) -> Poseidon2HalfStateRef {
        if a0.addr_variable == 0 {
            assert!(!a0.disabled);
        }
        if a1.addr_variable == 0 {
            assert!(!a1.disabled);
        }

        let cs = a0.cs.and(&a1.cs);
        let mut bit_variable_neg = cs.mul_constant(bit_variable, M31::one().neg());
        bit_variable_neg = cs.add(1, bit_variable_neg);

        let t0 = cs.mul(a0.addr_variable, bit_variable_neg);
        let t1 = cs.mul(a1.addr_variable, bit_variable);
        let new_a0_addr_variable = cs.add(t0, t1);

        let t0 = cs.add(a0.addr_variable, a1.addr_variable);
        let t1 = cs.mul_constant(new_a0_addr_variable, M31::one().neg());
        let new_a1_addr_variable = cs.add(t0, t1);

        let (mut left, mut right) = if !bit_value {
            (a0.clone(), a1.clone())
        } else {
            (a1.clone(), a0.clone())
        };
        left.addr_variable = new_a0_addr_variable;
        right.addr_variable = new_a1_addr_variable;

        let (digest, _) = Self::permute(&mut left, &mut right, false, true);
        digest
    }
}

impl DVar for Poseidon2HalfStateRef {
    type Value = [M31; 8];

    fn cs(&self) -> ConstraintSystemRef {
        self.cs.clone()
    }
}

impl AllocVar for Poseidon2HalfStateRef {
    fn new_variables(cs: &ConstraintSystemRef, value: &Self::Value, mode: AllocationMode) -> Self {
        let left_variable = QM31Var::new_variables(
            cs,
            &QM31::from_m31(value[0], value[1], value[2], value[3]),
            mode,
        )
        .variable;
        let right_variable = QM31Var::new_variables(
            cs,
            &QM31::from_m31(value[4], value[5], value[6], value[7]),
            mode,
        )
        .variable;
        let half_state_variable = cs.mul(left_variable, right_variable);
        let addr_variable = cs.new_m31(M31::from(half_state_variable), AllocationMode::Constant);

        Self {
            cs: cs.clone(),
            value: *value,
            left_variable,
            right_variable,
            half_state_variable,
            addr_variable,
            disabled: false,
        }
    }
}

impl Poseidon2HalfStateRef {
    pub fn zero(cs: &ConstraintSystemRef) -> Self {
        if let Some(addr_variable) = cs.get_cache("poseidon2 zero_half addr") {
            Self {
                cs: cs.clone(),
                value: [M31::zero(); 8],
                left_variable: 0,
                right_variable: 0,
                half_state_variable: cs.get_cache("poseidon2 zero_half").unwrap(),
                addr_variable,
                disabled: false,
            }
        } else {
            let half_state_variable = cs.mul(0, 0);
            let addr_variable =
                cs.new_m31(M31::from(half_state_variable), AllocationMode::Constant);
            cs.set_cache("poseidon2 zero_half addr", addr_variable);
            cs.set_cache("poseidon2 zero_half", half_state_variable);

            Self {
                cs: cs.clone(),
                value: [M31::zero(); 8],
                left_variable: 0,
                right_variable: 0,
                half_state_variable,
                addr_variable,
                disabled: false,
            }
        }
    }

    pub fn to_qm31(&self) -> [QM31Var; 2] {
        assert_ne!(self.addr_variable, 0);
        let cs = self.cs();

        [
            QM31Var {
                cs: cs.clone(),
                value: QM31::from_m31(self.value[0], self.value[1], self.value[2], self.value[3]),
                variable: self.left_variable,
            },
            QM31Var {
                cs: cs.clone(),
                value: QM31::from_m31(self.value[4], self.value[5], self.value[6], self.value[7]),
                variable: self.right_variable,
            },
        ]
    }

    pub fn permute(
        left: &mut Poseidon2HalfStateRef,
        right: &mut Poseidon2HalfStateRef,
        ignore_left_result: bool,
        ignore_right_result: bool,
    ) -> (Poseidon2HalfStateRef, Poseidon2HalfStateRef) {
        let cs = left.cs().and(&right.cs());

        if left.addr_variable == 0 {
            assert!(!left.disabled);
            left.disabled = true;
        }

        if right.addr_variable == 0 {
            assert!(!right.disabled);
            right.disabled = true;
        }

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

        let new_left = if ignore_left_result {
            Poseidon2HalfStateRef {
                cs: cs.clone(),
                value: std::array::from_fn(|i| state[i]),
                left_variable: 0,
                right_variable: 0,
                half_state_variable: 0,
                addr_variable: 0,
                disabled: true,
            }
        } else {
            let left_variable =
                QM31Var::new_witness(&cs, &QM31::from_m31(state[0], state[1], state[2], state[3]))
                    .variable;
            let right_variable =
                QM31Var::new_witness(&cs, &QM31::from_m31(state[4], state[5], state[6], state[7]))
                    .variable;
            let half_state_variable = cs.mul(left_variable, right_variable);
            let addr_variable =
                cs.new_m31(M31::from(half_state_variable), AllocationMode::Constant);

            Poseidon2HalfStateRef {
                cs: cs.clone(),
                value: std::array::from_fn(|i| state[i]),
                left_variable,
                right_variable,
                half_state_variable,
                addr_variable,
                disabled: false,
            }
        };

        let new_right = if ignore_right_result {
            Poseidon2HalfStateRef {
                cs: cs.clone(),
                value: std::array::from_fn(|i| state[i + 8]),
                left_variable: 0,
                right_variable: 0,
                half_state_variable: 0,
                addr_variable: 0,
                disabled: true,
            }
        } else {
            let left_variable = QM31Var::new_witness(
                &cs,
                &QM31::from_m31(state[8], state[9], state[10], state[11]),
            )
            .variable;
            let right_variable = QM31Var::new_witness(
                &cs,
                &QM31::from_m31(state[12], state[13], state[14], state[15]),
            )
            .variable;
            let half_state_variable = cs.mul(left_variable, right_variable);
            let addr_variable =
                cs.new_m31(M31::from(half_state_variable), AllocationMode::Constant);

            Poseidon2HalfStateRef {
                cs: cs.clone(),
                value: std::array::from_fn(|i| state[i + 8]),
                left_variable,
                right_variable,
                half_state_variable,
                addr_variable,
                disabled: false,
            }
        };

        let entry_1 = PoseidonEntry {
            addr: left.addr_variable,
            sel: left.half_state_variable,
            hash: left.value,
        };
        let entry_2 = PoseidonEntry {
            addr: right.addr_variable,
            sel: right.half_state_variable,
            hash: right.value,
        };
        let entry_3 = PoseidonEntry {
            addr: new_left.addr_variable,
            sel: new_left.half_state_variable,
            hash: new_left.value,
        };
        let entry_4 = PoseidonEntry {
            addr: new_right.addr_variable,
            sel: new_right.half_state_variable,
            hash: new_right.value,
        };

        cs.invoke_poseidon_accelerator(entry_1, entry_2, entry_3, entry_4);

        (new_left, new_right)
    }
}
