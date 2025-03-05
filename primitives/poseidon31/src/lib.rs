use crate::implementation::poseidon2_permute;
use circle_plonk_dsl_constraint_system::dvar::{AllocVar, AllocationMode, DVar};
use circle_plonk_dsl_constraint_system::{ConstraintSystemRef, ConstraintSystemType};
use circle_plonk_dsl_fields::{
    CM31EmulatedVar, CM31Var, M31Var, QM31EmulatedVar, QM31NativeVar, QM31Var,
};
use num_traits::Zero;
use stwo_prover::core::fields::m31::M31;
use stwo_prover::core::fields::qm31::QM31;
use stwo_prover::examples::plonk_with_poseidon::poseidon::{PoseidonEntry, SwapOption};

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
    pub elems: [M31Var; 8],
}

impl Poseidon2HalfVar {
    pub fn new_single_use_witness_only(cs: &ConstraintSystemRef, value: &[M31; 8]) -> Self {
        if cs.get_type() == ConstraintSystemType::QM31 {
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
                elems: std::array::from_fn(|i| M31Var::new_witness(cs, &value[i])),
            })
        }
    }

    pub fn from_m31(slice: &[M31Var]) -> Self {
        assert_eq!(slice.len(), 8);

        let mut cs = slice[0].cs.clone();
        for i in 1..8 {
            cs = cs.and(&slice[i].cs);
        }

        if cs.get_type() == ConstraintSystemType::QM31 {
            let left = QM31Var::from_m31(&slice[0], &slice[1], &slice[2], &slice[3]);
            let right = QM31Var::from_m31(&slice[4], &slice[5], &slice[6], &slice[7]);

            let cs = left.cs().and(&right.cs());
            let (left_variable, right_variable) = match (left, right) {
                (QM31Var::Native(left), QM31Var::Native(right)) => (left.variable, right.variable),
                _ => unimplemented!(),
            };
            let sel_value = cs.assemble_poseidon_gate(left_variable, right_variable);

            Poseidon2HalfVar::Native(Poseidon2HalfNativeVar {
                cs,
                value: std::array::from_fn(|i| slice[i].value),
                left_variable,
                right_variable,
                sel_value,
            })
        } else {
            Poseidon2HalfVar::Emulated(Poseidon2HalfEmulatedVar {
                cs: cs.clone(),
                elems: std::array::from_fn(|i| slice[i].clone()),
            })
        }
    }

    pub fn from_qm31(a: &QM31Var, b: &QM31Var) -> Self {
        match (a, b) {
            (QM31Var::Native(a_var), QM31Var::Native(b_var)) => {
                let cs = a.cs().and(&b.cs());
                let left_variable = a_var.variable;
                let right_variable = b_var.variable;
                let half_state_variable = cs.assemble_poseidon_gate(left_variable, right_variable);

                let a_arr = a_var.value.to_m31_array();
                let b_arr = b_var.value.to_m31_array();

                Poseidon2HalfVar::Native(Poseidon2HalfNativeVar {
                    cs,
                    value: std::array::from_fn(|i| if i < 4 { a_arr[i] } else { b_arr[i - 4] }),
                    left_variable,
                    right_variable,
                    sel_value: half_state_variable,
                })
            }
            (QM31Var::Emulated(a_var), QM31Var::Emulated(b_var)) => {
                let cs = a.cs().and(&b.cs());

                let a_var = match (&a_var.elems[0], &a_var.elems[1]) {
                    (CM31Var::Emulated(l), CM31Var::Emulated(r)) => [
                        l.elems[0].clone(),
                        l.elems[1].clone(),
                        r.elems[0].clone(),
                        r.elems[1].clone(),
                    ],
                    _ => unimplemented!(),
                };
                let b_var = match (&b_var.elems[0], &b_var.elems[1]) {
                    (CM31Var::Emulated(l), CM31Var::Emulated(r)) => [
                        l.elems[0].clone(),
                        l.elems[1].clone(),
                        r.elems[0].clone(),
                        r.elems[1].clone(),
                    ],
                    _ => unimplemented!(),
                };

                Poseidon2HalfVar::Emulated(Poseidon2HalfEmulatedVar {
                    cs,
                    elems: [
                        a_var[0].clone(),
                        a_var[1].clone(),
                        a_var[2].clone(),
                        a_var[3].clone(),
                        b_var[0].clone(),
                        b_var[1].clone(),
                        b_var[2].clone(),
                        b_var[3].clone(),
                    ],
                })
            }
            _ => unimplemented!(),
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
        if cs.get_type() == ConstraintSystemType::QM31 {
            let left = QM31Var::new_variables(
                cs,
                &QM31::from_m31(value[0], value[1], value[2], value[3]),
                mode,
            );
            let left_variable = match left {
                QM31Var::Native(left) => left.variable,
                _ => unimplemented!(),
            };

            let right = QM31Var::new_variables(
                cs,
                &QM31::from_m31(value[4], value[5], value[6], value[7]),
                mode,
            );
            let right_variable = match right {
                QM31Var::Native(right) => right.variable,
                _ => unimplemented!(),
            };

            let half_state_variable = cs.assemble_poseidon_gate(left_variable, right_variable);

            Poseidon2HalfVar::Native(Poseidon2HalfNativeVar {
                cs: cs.clone(),
                value: *value,
                left_variable,
                right_variable,
                sel_value: half_state_variable,
            })
        } else {
            Poseidon2HalfVar::Emulated(Poseidon2HalfEmulatedVar {
                cs: cs.clone(),
                elems: std::array::from_fn(|i| M31Var::new_variables(cs, &value[i], mode)),
            })
        }
    }
}

impl Poseidon2HalfVar {
    pub fn zero(cs: &ConstraintSystemRef) -> Self {
        if cs.get_type() == ConstraintSystemType::QM31 {
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
                elems: std::array::from_fn(|_| M31Var::zero(&cs)),
            })
        }
    }

    pub fn to_qm31(&self) -> [QM31Var; 2] {
        match self {
            Poseidon2HalfVar::Native(var) => {
                let cs = self.cs();
                [
                    QM31Var::Native(QM31NativeVar {
                        cs: cs.clone(),
                        value: QM31::from_m31(
                            var.value[0],
                            var.value[1],
                            var.value[2],
                            var.value[3],
                        ),
                        variable: var.left_variable,
                    }),
                    QM31Var::Native(QM31NativeVar {
                        cs: cs.clone(),
                        value: QM31::from_m31(
                            var.value[4],
                            var.value[5],
                            var.value[6],
                            var.value[7],
                        ),
                        variable: var.right_variable,
                    }),
                ]
            }
            Poseidon2HalfVar::Emulated(var) => {
                let cs = self.cs();
                [
                    QM31Var::Emulated(QM31EmulatedVar {
                        cs: cs.clone(),
                        elems: [
                            CM31Var::Emulated(CM31EmulatedVar {
                                cs: cs.clone(),
                                elems: [var.elems[0].clone(), var.elems[1].clone()],
                            }),
                            CM31Var::Emulated(CM31EmulatedVar {
                                cs: cs.clone(),
                                elems: [var.elems[2].clone(), var.elems[3].clone()],
                            }),
                        ],
                    }),
                    QM31Var::Emulated(QM31EmulatedVar {
                        cs: cs.clone(),
                        elems: [
                            CM31Var::Emulated(CM31EmulatedVar {
                                cs: cs.clone(),
                                elems: [var.elems[4].clone(), var.elems[5].clone()],
                            }),
                            CM31Var::Emulated(CM31EmulatedVar {
                                cs: cs.clone(),
                                elems: [var.elems[6].clone(), var.elems[7].clone()],
                            }),
                        ],
                    }),
                ]
            }
        }
    }

    pub fn swap_permute_get_rate(
        left: &Poseidon2HalfVar,
        right: &Poseidon2HalfVar,
        swap_bit_addr: usize,
        swap_bit_val: bool,
    ) -> Poseidon2HalfVar {
        let (res, _) = Self::permute(left, right, false, true, swap_bit_addr, swap_bit_val);
        res
    }

    pub fn swap_permute_get_capacity(
        left: &Poseidon2HalfVar,
        right: &Poseidon2HalfVar,
        swap_bit_addr: usize,
        swap_bit_val: bool,
    ) -> Poseidon2HalfVar {
        let (_, res) = Self::permute(left, right, true, false, swap_bit_addr, swap_bit_val);
        res
    }

    pub fn permute_get_rate(left: &Poseidon2HalfVar, right: &Poseidon2HalfVar) -> Poseidon2HalfVar {
        let (res, _) = Self::permute(left, right, false, true, 0, false);
        res
    }

    pub fn permute_get_capacity(
        left: &Poseidon2HalfVar,
        right: &Poseidon2HalfVar,
    ) -> Poseidon2HalfVar {
        let (_, res) = Self::permute(left, right, true, false, 0, false);
        res
    }

    pub fn permute(
        left: &Poseidon2HalfVar,
        right: &Poseidon2HalfVar,
        ignore_left_result: bool,
        ignore_right_result: bool,
        swap_bit_addr: usize,
        swap_bit_val: bool,
    ) -> (Poseidon2HalfVar, Poseidon2HalfVar) {
        match (left, right) {
            (Poseidon2HalfVar::Native(left_var), Poseidon2HalfVar::Native(right_var)) => {
                let cs = left.cs().and(&right.cs());

                let mut state: [M31; 16] = if !swap_bit_val {
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
                    let left_variable = match out_left {
                        QM31Var::Native(var) => var.variable,
                        _ => unimplemented!(),
                    };

                    let out_right = QM31Var::new_witness(
                        &cs,
                        &QM31::from_m31(state[4], state[5], state[6], state[7]),
                    );
                    let right_variable = match out_right {
                        QM31Var::Native(var) => var.variable,
                        _ => unimplemented!(),
                    };

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
                    let left_variable = match out_left {
                        QM31Var::Native(var) => var.variable,
                        _ => unimplemented!(),
                    };

                    let out_right = QM31Var::new_witness(
                        &cs,
                        &QM31::from_m31(state[12], state[13], state[14], state[15]),
                    );
                    let right_variable = match out_right {
                        QM31Var::Native(var) => var.variable,
                        _ => unimplemented!(),
                    };

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
                let swap_option = SwapOption {
                    addr: swap_bit_addr,
                    swap: swap_bit_val,
                };

                cs.invoke_poseidon_accelerator(entry_1, entry_2, entry_3, entry_4, swap_option);

                (
                    Poseidon2HalfVar::Native(new_left),
                    Poseidon2HalfVar::Native(new_right),
                )
            }
            (Poseidon2HalfVar::Emulated(left_var), Poseidon2HalfVar::Emulated(right_var)) => {
                todo!()
            }
            _ => unimplemented!(),
        }
    }
}
