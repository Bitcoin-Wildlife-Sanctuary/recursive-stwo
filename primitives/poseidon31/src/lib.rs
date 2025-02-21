use crate::implementation::poseidon2_permute;
use circle_plonk_dsl_constraint_system::dvar::{AllocVar, AllocationMode, DVar};
use circle_plonk_dsl_constraint_system::ConstraintSystemRef;
use circle_plonk_dsl_fields::{M31Var, QM31Var};
use num_traits::Zero;
use stwo_prover::core::fields::m31::M31;
use stwo_prover::core::fields::qm31::QM31;
use stwo_prover::examples::plonk_with_poseidon::poseidon::{PoseidonEntry, SwapOption};

pub mod implementation;
mod parameters;

#[derive(Debug, Clone)]
pub struct Poseidon2HalfStateRef {
    pub cs: ConstraintSystemRef,
    pub value: [M31; 8],
    pub left_variable: usize,
    pub right_variable: usize,
    pub sel_value: usize,
}

impl Poseidon2HalfStateRef {
    pub fn new_single_use_witness_only(cs: &ConstraintSystemRef, value: &[M31; 8]) -> Self {
        Poseidon2HalfStateRef {
            cs: cs.clone(),
            value: value.clone(),
            left_variable: 0,
            right_variable: 0,
            sel_value: 0,
        }
    }

    pub fn from_m31(slice: &[M31Var]) -> Self {
        assert_eq!(slice.len(), 8);
        let left_variable = QM31Var::from_m31(&slice[0], &slice[1], &slice[2], &slice[3]);
        let right_variable = QM31Var::from_m31(&slice[4], &slice[5], &slice[6], &slice[7]);

        let cs = left_variable.cs().and(&right_variable.cs());
        let left_variable = left_variable.variable;
        let right_variable = right_variable.variable;
        let sel_value = cs.assemble_poseidon_gate(left_variable, right_variable);

        Poseidon2HalfStateRef {
            cs,
            value: std::array::from_fn(|i| slice[i].value),
            left_variable,
            right_variable,
            sel_value,
        }
    }

    pub fn from_qm31(a: &QM31Var, b: &QM31Var) -> Self {
        let cs = a.cs().and(&b.cs());
        let left_variable = a.variable;
        let right_variable = b.variable;
        let half_state_variable = cs.assemble_poseidon_gate(left_variable, right_variable);

        let a_arr = a.value.to_m31_array();
        let b_arr = b.value.to_m31_array();

        Self {
            cs,
            value: std::array::from_fn(|i| if i < 4 { a_arr[i] } else { b_arr[i - 4] }),
            left_variable,
            right_variable,
            sel_value: half_state_variable,
        }
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
        let half_state_variable = cs.assemble_poseidon_gate(left_variable, right_variable);

        Self {
            cs: cs.clone(),
            value: *value,
            left_variable,
            right_variable,
            sel_value: half_state_variable,
        }
    }
}

impl Poseidon2HalfStateRef {
    pub fn zero(cs: &ConstraintSystemRef) -> Self {
        if let Some(half_state_variable) = cs.get_cache("poseidon2 zero_half") {
            Self {
                cs: cs.clone(),
                value: [M31::zero(); 8],
                left_variable: 0,
                right_variable: 0,
                sel_value: half_state_variable,
            }
        } else {
            let half_state_variable = cs.assemble_poseidon_gate(0, 0);
            cs.set_cache("poseidon2 zero_half", half_state_variable);

            Self {
                cs: cs.clone(),
                value: [M31::zero(); 8],
                left_variable: 0,
                right_variable: 0,
                sel_value: half_state_variable,
            }
        }
    }

    pub fn to_qm31(&self) -> [QM31Var; 2] {
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

    pub fn swap_permute_get_rate(
        left: &Poseidon2HalfStateRef,
        right: &Poseidon2HalfStateRef,
        swap_bit_addr: usize,
        swap_bit_val: bool,
    ) -> Poseidon2HalfStateRef {
        let (res, _) = Self::permute(left, right, false, true, swap_bit_addr, swap_bit_val);
        res
    }

    pub fn swap_permute_get_capacity(
        left: &Poseidon2HalfStateRef,
        right: &Poseidon2HalfStateRef,
        swap_bit_addr: usize,
        swap_bit_val: bool,
    ) -> Poseidon2HalfStateRef {
        let (_, res) = Self::permute(left, right, true, false, swap_bit_addr, swap_bit_val);
        res
    }

    pub fn permute_get_rate(
        left: &Poseidon2HalfStateRef,
        right: &Poseidon2HalfStateRef,
    ) -> Poseidon2HalfStateRef {
        let (res, _) = Self::permute(left, right, false, true, 0, false);
        res
    }

    pub fn permute_get_capacity(
        left: &Poseidon2HalfStateRef,
        right: &Poseidon2HalfStateRef,
    ) -> Poseidon2HalfStateRef {
        let (_, res) = Self::permute(left, right, true, false, 0, false);
        res
    }

    pub fn permute(
        left: &Poseidon2HalfStateRef,
        right: &Poseidon2HalfStateRef,
        ignore_left_result: bool,
        ignore_right_result: bool,
        swap_bit_addr: usize,
        swap_bit_val: bool,
    ) -> (Poseidon2HalfStateRef, Poseidon2HalfStateRef) {
        let cs = left.cs().and(&right.cs());

        let mut state: [M31; 16] = if !swap_bit_val {
            std::array::from_fn(|i| {
                if i < 8 {
                    left.value[i]
                } else {
                    right.value[i - 8]
                }
            })
        } else {
            std::array::from_fn(|i| {
                if i < 8 {
                    right.value[i]
                } else {
                    left.value[i - 8]
                }
            })
        };

        poseidon2_permute(&mut state);

        let new_left = if ignore_left_result {
            Poseidon2HalfStateRef {
                cs: cs.clone(),
                value: std::array::from_fn(|i| state[i]),
                left_variable: 0,
                right_variable: 0,
                sel_value: 0,
            }
        } else {
            let left_variable =
                QM31Var::new_witness(&cs, &QM31::from_m31(state[0], state[1], state[2], state[3]))
                    .variable;
            let right_variable =
                QM31Var::new_witness(&cs, &QM31::from_m31(state[4], state[5], state[6], state[7]))
                    .variable;
            let half_state_variable = cs.assemble_poseidon_gate(left_variable, right_variable);

            Poseidon2HalfStateRef {
                cs: cs.clone(),
                value: std::array::from_fn(|i| state[i]),
                left_variable,
                right_variable,
                sel_value: half_state_variable,
            }
        };

        let new_right = if ignore_right_result {
            Poseidon2HalfStateRef {
                cs: cs.clone(),
                value: std::array::from_fn(|i| state[i + 8]),
                left_variable: 0,
                right_variable: 0,
                sel_value: 0,
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
            let half_state_variable = cs.assemble_poseidon_gate(left_variable, right_variable);

            Poseidon2HalfStateRef {
                cs: cs.clone(),
                value: std::array::from_fn(|i| state[i + 8]),
                left_variable,
                right_variable,
                sel_value: half_state_variable,
            }
        };

        let entry_1 = PoseidonEntry {
            wire: left.sel_value,
            hash: left.value,
        };
        let entry_2 = PoseidonEntry {
            wire: right.sel_value,
            hash: right.value,
        };
        let entry_3 = PoseidonEntry {
            wire: new_left.sel_value,
            hash: new_left.value,
        };
        let entry_4 = PoseidonEntry {
            wire: new_right.sel_value,
            hash: new_right.value,
        };
        let swap_option = SwapOption {
            addr: swap_bit_addr,
            swap: swap_bit_val,
        };

        cs.invoke_poseidon_accelerator(entry_1, entry_2, entry_3, entry_4, swap_option);

        (new_left, new_right)
    }
}
