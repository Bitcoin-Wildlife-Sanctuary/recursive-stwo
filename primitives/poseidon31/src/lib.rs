use crate::emulated::poseidon_permute_emulated;
use crate::implementation::poseidon2_permute;
use circle_plonk_dsl_constraint_system::dvar::{AllocVar, AllocationMode, DVar};
use circle_plonk_dsl_constraint_system::{ConstraintSystemRef, ConstraintSystemType};
use circle_plonk_dsl_fields::{M31Var, QM31Var};
use num_traits::{One, Zero};
use stwo_prover::core::fields::m31::M31;
use stwo_prover::core::fields::qm31::QM31;
use stwo_prover::examples::plonk_with_poseidon::poseidon::{PoseidonEntry, SwapOption};

mod emulated;
pub mod implementation;
mod parameters;

#[derive(Debug, Clone)]
pub enum Poseidon2HalfVar {
    Native(Poseidon2HalfNativeVar),
    Emulated(Poseidon2HalfEmulatedVar),
}

#[derive(Debug, Clone)]
pub struct Poseidon2HalfNativeVar {
    pub cs: ConstraintSystemRef,
    pub value: [M31; 8],
    pub left_variable: usize,
    pub right_variable: usize,
    pub sel_value: usize,
}

#[derive(Debug, Clone)]
pub struct Poseidon2HalfEmulatedVar {
    pub cs: ConstraintSystemRef,
    pub elems: [QM31Var; 2],
}

pub type IsSwap = Option<(bool, usize)>;

impl Poseidon2HalfVar {
    pub fn value(&self) -> [M31; 8] {
        match self {
            Poseidon2HalfVar::Native(var) => var.value.clone(),
            Poseidon2HalfVar::Emulated(var) => {
                let first = var.elems[0].value.to_m31_array();
                let second = var.elems[1].value.to_m31_array();
                std::array::from_fn(|i| if i < 4 { first[i] } else { second[i - 4] })
            }
        }
    }

    pub fn new_single_use_witness_only(cs: &ConstraintSystemRef, value: &[M31; 8]) -> Self {
        if cs.get_type() == ConstraintSystemType::PlonkWithPoseidon {
            Poseidon2HalfVar::Native(Poseidon2HalfNativeVar {
                cs: cs.clone(),
                value: value.clone(),
                left_variable: 0,
                right_variable: 0,
                sel_value: 0,
            })
        } else {
            Poseidon2HalfVar::Emulated(Poseidon2HalfEmulatedVar {
                cs: cs.clone(),
                elems: [
                    QM31Var::new_witness(
                        &cs,
                        &QM31::from_m31(value[0], value[1], value[2], value[3]),
                    ),
                    QM31Var::new_witness(
                        &cs,
                        &QM31::from_m31(value[4], value[5], value[6], value[7]),
                    ),
                ],
            })
        }
    }

    pub fn from_m31(slice: &[M31Var]) -> Self {
        assert_eq!(slice.len(), 8);

        let mut cs = slice[0].cs.clone();
        for i in 1..8 {
            cs = cs.and(&slice[i].cs);
        }

        if cs.get_type() == ConstraintSystemType::PlonkWithPoseidon {
            let left = QM31Var::from_m31(&slice[0], &slice[1], &slice[2], &slice[3]);
            let right = QM31Var::from_m31(&slice[4], &slice[5], &slice[6], &slice[7]);

            let cs = left.cs().and(&right.cs());
            let sel_value = cs.assemble_poseidon_gate(left.variable, right.variable);

            Poseidon2HalfVar::Native(Poseidon2HalfNativeVar {
                cs,
                value: std::array::from_fn(|i| slice[i].value),
                left_variable: left.variable,
                right_variable: right.variable,
                sel_value,
            })
        } else {
            Poseidon2HalfVar::Emulated(Poseidon2HalfEmulatedVar {
                cs: cs.clone(),
                elems: [
                    QM31Var::from_m31(&slice[0], &slice[1], &slice[2], &slice[3]),
                    QM31Var::from_m31(&slice[4], &slice[5], &slice[6], &slice[7]),
                ],
            })
        }
    }

    pub fn from_qm31(a: &QM31Var, b: &QM31Var) -> Self {
        let cs = a.cs().and(&b.cs());

        if cs.get_type() == ConstraintSystemType::PlonkWithPoseidon {
            let left_variable = a.variable;
            let right_variable = b.variable;
            let half_state_variable = cs.assemble_poseidon_gate(left_variable, right_variable);

            let a_arr = a.value.to_m31_array();
            let b_arr = b.value.to_m31_array();

            Poseidon2HalfVar::Native(Poseidon2HalfNativeVar {
                cs,
                value: std::array::from_fn(|i| if i < 4 { a_arr[i] } else { b_arr[i - 4] }),
                left_variable,
                right_variable,
                sel_value: half_state_variable,
            })
        } else {
            Poseidon2HalfVar::Emulated(Poseidon2HalfEmulatedVar {
                cs,
                elems: [a.clone(), b.clone()],
            })
        }
    }
}

impl DVar for Poseidon2HalfVar {
    type Value = [M31; 8];

    fn cs(&self) -> ConstraintSystemRef {
        match self {
            Poseidon2HalfVar::Native(var) => var.cs.clone(),
            Poseidon2HalfVar::Emulated(var) => var.cs.clone(),
        }
    }
}

impl AllocVar for Poseidon2HalfVar {
    fn new_variables(cs: &ConstraintSystemRef, value: &Self::Value, mode: AllocationMode) -> Self {
        if cs.get_type() == ConstraintSystemType::PlonkWithPoseidon {
            let left = QM31Var::new_variables(
                cs,
                &QM31::from_m31(value[0], value[1], value[2], value[3]),
                mode,
            );
            let right = QM31Var::new_variables(
                cs,
                &QM31::from_m31(value[4], value[5], value[6], value[7]),
                mode,
            );

            let half_state_variable = cs.assemble_poseidon_gate(left.variable, right.variable);

            Poseidon2HalfVar::Native(Poseidon2HalfNativeVar {
                cs: cs.clone(),
                value: *value,
                left_variable: left.variable,
                right_variable: right.variable,
                sel_value: half_state_variable,
            })
        } else {
            Poseidon2HalfVar::Emulated(Poseidon2HalfEmulatedVar {
                cs: cs.clone(),
                elems: [
                    QM31Var::new_variables(
                        cs,
                        &QM31::from_m31(value[0], value[1], value[2], value[3]),
                        mode,
                    ),
                    QM31Var::new_variables(
                        cs,
                        &QM31::from_m31(value[4], value[5], value[6], value[7]),
                        mode,
                    ),
                ],
            })
        }
    }
}

impl Poseidon2HalfVar {
    pub fn zero(cs: &ConstraintSystemRef) -> Self {
        if cs.get_type() == ConstraintSystemType::PlonkWithPoseidon {
            if let Some(half_state_variable) = cs.get_cache("poseidon2 zero_half") {
                Self::Native(Poseidon2HalfNativeVar {
                    cs: cs.clone(),
                    value: [M31::zero(); 8],
                    left_variable: 0,
                    right_variable: 0,
                    sel_value: half_state_variable,
                })
            } else {
                let half_state_variable = cs.assemble_poseidon_gate(0, 0);
                cs.set_cache("poseidon2 zero_half", half_state_variable);
                Self::Native(Poseidon2HalfNativeVar {
                    cs: cs.clone(),
                    value: [M31::zero(); 8],
                    left_variable: 0,
                    right_variable: 0,
                    sel_value: half_state_variable,
                })
            }
        } else {
            Self::Emulated(Poseidon2HalfEmulatedVar {
                cs: cs.clone(),
                elems: [QM31Var::zero(&cs), QM31Var::zero(&cs)],
            })
        }
    }

    pub fn to_qm31(&self) -> [QM31Var; 2] {
        match self {
            Poseidon2HalfVar::Native(var) => {
                let cs = self.cs();
                [
                    QM31Var {
                        cs: cs.clone(),
                        value: QM31::from_m31(
                            var.value[0],
                            var.value[1],
                            var.value[2],
                            var.value[3],
                        ),
                        variable: var.left_variable,
                    },
                    QM31Var {
                        cs: cs.clone(),
                        value: QM31::from_m31(
                            var.value[4],
                            var.value[5],
                            var.value[6],
                            var.value[7],
                        ),
                        variable: var.right_variable,
                    },
                ]
            }
            Poseidon2HalfVar::Emulated(var) => var.elems.clone(),
        }
    }

    pub fn swap_permute_get_rate(
        left: &Poseidon2HalfVar,
        right: &Poseidon2HalfVar,
        is_swap: IsSwap,
    ) -> Poseidon2HalfVar {
        let (res, _) = Self::permute(left, right, false, true, is_swap);
        res
    }

    pub fn swap_permute_get_capacity(
        left: &Poseidon2HalfVar,
        right: &Poseidon2HalfVar,
        is_swap: IsSwap,
    ) -> Poseidon2HalfVar {
        let (_, res) = Self::permute(left, right, true, false, is_swap);
        res
    }

    pub fn permute_get_rate(left: &Poseidon2HalfVar, right: &Poseidon2HalfVar) -> Poseidon2HalfVar {
        let (res, _) = Self::permute(left, right, false, true, None);
        res
    }

    pub fn permute_get_capacity(
        left: &Poseidon2HalfVar,
        right: &Poseidon2HalfVar,
    ) -> Poseidon2HalfVar {
        let (_, res) = Self::permute(left, right, true, false, None);
        res
    }

    pub fn permute(
        left: &Poseidon2HalfVar,
        right: &Poseidon2HalfVar,
        ignore_left_result: bool,
        ignore_right_result: bool,
        is_swap: IsSwap,
    ) -> (Poseidon2HalfVar, Poseidon2HalfVar) {
        match (left, right) {
            (Poseidon2HalfVar::Native(left_var), Poseidon2HalfVar::Native(right_var)) => {
                let cs = left.cs().and(&right.cs());

                let mut state: [M31; 16] = if is_swap.is_none() || !is_swap.unwrap().0 {
                    std::array::from_fn(|i| {
                        if i < 8 {
                            left_var.value[i]
                        } else {
                            right_var.value[i - 8]
                        }
                    })
                } else {
                    std::array::from_fn(|i| {
                        if i < 8 {
                            right_var.value[i]
                        } else {
                            left_var.value[i - 8]
                        }
                    })
                };

                poseidon2_permute(&mut state);

                let new_left = if ignore_left_result {
                    Poseidon2HalfNativeVar {
                        cs: cs.clone(),
                        value: std::array::from_fn(|i| state[i]),
                        left_variable: 0,
                        right_variable: 0,
                        sel_value: 0,
                    }
                } else {
                    let out_left = QM31Var::new_witness(
                        &cs,
                        &QM31::from_m31(state[0], state[1], state[2], state[3]),
                    );
                    let left_variable = out_left.variable;

                    let out_right = QM31Var::new_witness(
                        &cs,
                        &QM31::from_m31(state[4], state[5], state[6], state[7]),
                    );
                    let right_variable = out_right.variable;

                    let half_state_variable =
                        cs.assemble_poseidon_gate(left_variable, right_variable);

                    Poseidon2HalfNativeVar {
                        cs: cs.clone(),
                        value: std::array::from_fn(|i| state[i]),
                        left_variable,
                        right_variable,
                        sel_value: half_state_variable,
                    }
                };

                let new_right = if ignore_right_result {
                    Poseidon2HalfNativeVar {
                        cs: cs.clone(),
                        value: std::array::from_fn(|i| state[i + 8]),
                        left_variable: 0,
                        right_variable: 0,
                        sel_value: 0,
                    }
                } else {
                    let out_left = QM31Var::new_witness(
                        &cs,
                        &QM31::from_m31(state[8], state[9], state[10], state[11]),
                    );
                    let left_variable = out_left.variable;

                    let out_right = QM31Var::new_witness(
                        &cs,
                        &QM31::from_m31(state[12], state[13], state[14], state[15]),
                    );
                    let right_variable = out_right.variable;

                    let half_state_variable =
                        cs.assemble_poseidon_gate(left_variable, right_variable);

                    Poseidon2HalfNativeVar {
                        cs: cs.clone(),
                        value: std::array::from_fn(|i| state[i + 8]),
                        left_variable,
                        right_variable,
                        sel_value: half_state_variable,
                    }
                };

                let entry_1 = PoseidonEntry {
                    wire: left_var.sel_value,
                    hash: left_var.value,
                };
                let entry_2 = PoseidonEntry {
                    wire: right_var.sel_value,
                    hash: right_var.value,
                };
                let entry_3 = PoseidonEntry {
                    wire: new_left.sel_value,
                    hash: new_left.value,
                };
                let entry_4 = PoseidonEntry {
                    wire: new_right.sel_value,
                    hash: new_right.value,
                };
                let swap_option = if let Some((swap_bit_val, swap_bit_addr)) = is_swap {
                    SwapOption {
                        addr: swap_bit_addr,
                        swap: swap_bit_val,
                    }
                } else {
                    SwapOption {
                        addr: 0,
                        swap: false,
                    }
                };

                cs.invoke_poseidon_accelerator(entry_1, entry_2, entry_3, entry_4, swap_option);

                (
                    Poseidon2HalfVar::Native(new_left),
                    Poseidon2HalfVar::Native(new_right),
                )
            }
            (Poseidon2HalfVar::Emulated(left_var), Poseidon2HalfVar::Emulated(right_var)) => {
                let (new_left, new_right) = poseidon_permute_emulated(left_var, right_var, is_swap);
                (
                    Poseidon2HalfVar::Emulated(new_left),
                    Poseidon2HalfVar::Emulated(new_right),
                )
            }
            _ => unimplemented!(),
        }
    }

    pub fn equalverify(&self, rhs: &Self) {
        let cs = self.cs().and(&rhs.cs());
        match (self, rhs) {
            (Poseidon2HalfVar::Native(lhs), Poseidon2HalfVar::Native(rhs)) => {
                cs.insert_gate(lhs.left_variable, 0, rhs.left_variable, M31::one());
                cs.insert_gate(lhs.right_variable, 0, rhs.right_variable, M31::one());
            }
            (Poseidon2HalfVar::Emulated(lhs), Poseidon2HalfVar::Emulated(rhs)) => {
                for i in 0..2 {
                    lhs.elems[i].equalverify(&rhs.elems[i]);
                }
            }
            _ => unimplemented!(),
        }
    }
}
