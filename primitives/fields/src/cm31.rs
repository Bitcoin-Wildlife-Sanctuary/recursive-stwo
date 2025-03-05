use crate::M31Var;
use circle_plonk_dsl_constraint_system::dvar::{AllocVar, AllocationMode, DVar};
use circle_plonk_dsl_constraint_system::{ConstraintSystemRef, ConstraintSystemType};
use num_traits::{One, Zero};
use std::ops::{Add, Mul, Neg, Sub};
use stwo_prover::core::fields::cm31::CM31;
use stwo_prover::core::fields::m31::M31;
use stwo_prover::core::fields::FieldExpOps;

#[derive(Debug, Clone)]
pub enum CM31Var {
    Native(CM31NativeVar),
    Emulated(CM31EmulatedVar),
}

#[derive(Debug, Clone)]
pub struct CM31NativeVar {
    pub cs: ConstraintSystemRef,
    pub value: CM31,
    pub variable: usize,
}

#[derive(Debug, Clone)]
pub struct CM31EmulatedVar {
    pub cs: ConstraintSystemRef,
    pub elems: [M31Var; 2],
}

impl DVar for CM31Var {
    type Value = CM31;

    fn cs(&self) -> ConstraintSystemRef {
        match self {
            CM31Var::Native(var) => var.cs.clone(),
            CM31Var::Emulated(var) => var.cs.clone(),
        }
    }
}

impl AllocVar for CM31Var {
    fn new_variables(cs: &ConstraintSystemRef, value: &Self::Value, mode: AllocationMode) -> Self {
        if mode != AllocationMode::Constant {
            let real = M31Var::new_variables(cs, &value.0, mode);
            let imag = M31Var::new_variables(cs, &value.1, mode);

            if cs.get_type() == ConstraintSystemType::QM31 {
                let res = cs.add(real.variable, cs.mul(imag.variable, 2));

                Self::Native(CM31NativeVar {
                    cs: cs.clone(),
                    value: *value,
                    variable: res,
                })
            } else {
                Self::Emulated(CM31EmulatedVar {
                    cs: cs.clone(),
                    elems: [real, imag],
                })
            }
        } else {
            Self::new_constant(cs, value)
        }
    }

    fn new_constant(cs: &ConstraintSystemRef, value: &Self::Value) -> Self {
        if value.is_zero() {
            return Self::zero(&cs);
        }
        if value.is_one() {
            return Self::one(&cs);
        }
        if *value == CM31(M31::zero(), M31::one()) {
            return Self::i(&cs);
        }

        if cs.get_type() == ConstraintSystemType::QM31 {
            let f = format!("cm31 {},{}", value.0 .0, value.1 .0);
            let exist = cs.get_cache(f.clone());
            if let Some(variable) = exist {
                Self::Native(CM31NativeVar {
                    cs: cs.clone(),
                    value: *value,
                    variable,
                })
            } else {
                let real = M31Var::new_constant(cs, &value.0);
                let imag = M31Var::new_constant(cs, &value.1);

                let variable = cs.add(real.variable, cs.mul(imag.variable, 2));
                cs.set_cache(f, variable);
                Self::Native(CM31NativeVar {
                    cs: cs.clone(),
                    value: *value,
                    variable,
                })
            }
        } else {
            let a = M31Var::new_constant(cs, &value.0);
            let b = M31Var::new_constant(cs, &value.1);

            Self::Emulated(CM31EmulatedVar {
                cs: cs.clone(),
                elems: [a, b],
            })
        }
    }
}

impl From<&M31Var> for CM31Var {
    fn from(var: &M31Var) -> Self {
        let cs = var.cs();
        if cs.get_type() == ConstraintSystemType::QM31 {
            Self::Native(CM31NativeVar {
                cs,
                value: CM31::from(var.value),
                variable: var.variable,
            })
        } else {
            Self::Emulated(CM31EmulatedVar {
                cs: cs.clone(),
                elems: [var.clone(), M31Var::zero(&cs)],
            })
        }
    }
}

impl Add<&M31Var> for &CM31Var {
    type Output = CM31Var;

    fn add(self, rhs: &M31Var) -> CM31Var {
        let cs = self.cs().and(&rhs.cs);
        match self {
            CM31Var::Native(var) => CM31Var::Native(CM31NativeVar {
                cs: cs.clone(),
                value: var.value + rhs.value,
                variable: cs.add(var.variable, rhs.variable),
            }),
            CM31Var::Emulated(var) => CM31Var::Emulated(CM31EmulatedVar {
                cs: cs.clone(),
                elems: [&var.elems[0] + rhs, var.elems[1].clone()],
            }),
        }
    }
}

impl Add<&CM31Var> for &M31Var {
    type Output = CM31Var;

    fn add(self, rhs: &CM31Var) -> CM31Var {
        rhs + self
    }
}

impl Add<&CM31Var> for &CM31Var {
    type Output = CM31Var;

    fn add(self, rhs: &CM31Var) -> CM31Var {
        let cs = self.cs().and(&rhs.cs());
        match (self, rhs) {
            (CM31Var::Native(lhs), CM31Var::Native(rhs)) => CM31Var::Native(CM31NativeVar {
                cs: cs.clone(),
                value: lhs.value + rhs.value,
                variable: cs.add(lhs.variable, rhs.variable),
            }),
            (CM31Var::Emulated(lhs), CM31Var::Emulated(rhs)) => {
                CM31Var::Emulated(CM31EmulatedVar {
                    cs: cs.clone(),
                    elems: [&lhs.elems[0] + &rhs.elems[0], &lhs.elems[1] + &rhs.elems[1]],
                })
            }
            _ => unimplemented!(),
        }
    }
}

impl Sub<&M31Var> for &CM31Var {
    type Output = CM31Var;

    fn sub(self, rhs: &M31Var) -> CM31Var {
        self + &(-rhs)
    }
}

impl Sub<&CM31Var> for &M31Var {
    type Output = CM31Var;

    fn sub(self, rhs: &CM31Var) -> CM31Var {
        self + &(-rhs)
    }
}

impl Sub<&CM31Var> for &CM31Var {
    type Output = CM31Var;

    fn sub(self, rhs: &CM31Var) -> CM31Var {
        self + &(-rhs)
    }
}

impl Mul<&M31Var> for &CM31Var {
    type Output = CM31Var;

    fn mul(self, rhs: &M31Var) -> CM31Var {
        let cs = self.cs().and(&rhs.cs);
        match self {
            CM31Var::Native(var) => CM31Var::Native(CM31NativeVar {
                cs: cs.clone(),
                value: var.value * rhs.value,
                variable: cs.mul(var.variable, rhs.variable),
            }),
            CM31Var::Emulated(var) => CM31Var::Emulated(CM31EmulatedVar {
                cs: cs.clone(),
                elems: [&var.elems[0] * rhs, &var.elems[1] * rhs],
            }),
        }
    }
}

impl Mul<&CM31Var> for &M31Var {
    type Output = CM31Var;

    fn mul(self, rhs: &CM31Var) -> CM31Var {
        rhs * self
    }
}

impl Mul<&CM31Var> for &CM31Var {
    type Output = CM31Var;

    fn mul(self, rhs: &CM31Var) -> CM31Var {
        let cs = self.cs().and(&rhs.cs());
        match (self, rhs) {
            (CM31Var::Native(lhs), CM31Var::Native(rhs)) => CM31Var::Native(CM31NativeVar {
                cs: cs.clone(),
                value: lhs.value * rhs.value,
                variable: cs.mul(lhs.variable, rhs.variable),
            }),
            (CM31Var::Emulated(lhs), CM31Var::Emulated(rhs)) => {
                // (a + bi) * (c + di) = (ac - bd) + (ad + bc)i

                let ac = &lhs.elems[0] * &rhs.elems[0];
                let bd = &lhs.elems[1] * &rhs.elems[1];
                let ad = &lhs.elems[0] * &rhs.elems[1];
                let bc = &lhs.elems[1] * &rhs.elems[0];

                let first = &ac - &bd;
                let second = &ad + &bc;

                CM31Var::Emulated(CM31EmulatedVar {
                    cs: cs.clone(),
                    elems: [first, second],
                })
            }
            _ => unimplemented!(),
        }
    }
}

impl Neg for &CM31Var {
    type Output = CM31Var;

    fn neg(self) -> Self::Output {
        match self {
            CM31Var::Native(var) => {
                let value = -var.value;
                let variable = var.cs.mul_constant(var.variable, M31::one().neg());

                CM31Var::Native(CM31NativeVar {
                    cs: var.cs.clone(),
                    value,
                    variable,
                })
            }
            CM31Var::Emulated(var) => CM31Var::Emulated(CM31EmulatedVar {
                cs: var.cs.clone(),
                elems: [-&var.elems[0], -&var.elems[1]],
            }),
        }
    }
}

impl CM31Var {
    pub fn value(&self) -> CM31 {
        match self {
            CM31Var::Native(var) => var.value,
            CM31Var::Emulated(var) => CM31(var.elems[0].value, var.elems[1].value),
        }
    }

    pub fn from_m31(real: &M31Var, imag: &M31Var) -> Self {
        let cs = real.cs().and(&imag.cs());
        if cs.get_type() == ConstraintSystemType::QM31 {
            let value = CM31::from_m31(real.value, imag.value);
            let variable = cs.add(real.variable, cs.mul(imag.variable, 2));
            Self::Native(CM31NativeVar {
                cs,
                value,
                variable,
            })
        } else {
            Self::Emulated(CM31EmulatedVar {
                cs,
                elems: [real.clone(), imag.clone()],
            })
        }
    }

    pub fn zero(cs: &ConstraintSystemRef) -> CM31Var {
        if cs.get_type() == ConstraintSystemType::QM31 {
            CM31Var::Native(CM31NativeVar {
                cs: cs.clone(),
                value: CM31::zero(),
                variable: 0,
            })
        } else {
            CM31Var::Emulated(CM31EmulatedVar {
                cs: cs.clone(),
                elems: [M31Var::zero(&cs), M31Var::zero(&cs)],
            })
        }
    }

    pub fn one(cs: &ConstraintSystemRef) -> CM31Var {
        if cs.get_type() == ConstraintSystemType::QM31 {
            CM31Var::Native(CM31NativeVar {
                cs: cs.clone(),
                value: CM31::one(),
                variable: 1,
            })
        } else {
            CM31Var::Emulated(CM31EmulatedVar {
                cs: cs.clone(),
                elems: [M31Var::one(&cs), M31Var::zero(&cs)],
            })
        }
    }

    pub fn i(cs: &ConstraintSystemRef) -> CM31Var {
        if cs.get_type() == ConstraintSystemType::QM31 {
            CM31Var::Native(CM31NativeVar {
                cs: cs.clone(),
                value: CM31::from_u32_unchecked(0, 1),
                variable: 2,
            })
        } else {
            CM31Var::Emulated(CM31EmulatedVar {
                cs: cs.clone(),
                elems: [M31Var::zero(&cs), M31Var::one(&cs)],
            })
        }
    }

    pub fn equalverify(&self, rhs: &CM31Var) {
        match (self, rhs) {
            (CM31Var::Native(lhs), CM31Var::Native(rhs)) => {
                assert_eq!(lhs.value, rhs.value);
                let cs = lhs.cs.and(&rhs.cs);
                cs.insert_gate(lhs.variable, 0, rhs.variable, M31::one());
            }
            (CM31Var::Emulated(lhs), CM31Var::Emulated(rhs)) => {
                lhs.elems[0].equalverify(&rhs.elems[0]);
                lhs.elems[1].equalverify(&rhs.elems[1]);
            }
            _ => unimplemented!(),
        }
    }

    pub fn inv(&self) -> CM31Var {
        match self {
            CM31Var::Native(var) => {
                let cs = self.cs();
                let value = var.value.inverse();
                let res = CM31Var::new_witness(&cs, &value);
                match &res {
                    CM31Var::Native(res) => {
                        cs.insert_gate(var.variable, res.variable, 1, M31::zero());
                    }
                    _ => unimplemented!(),
                }
                res
            }
            CM31Var::Emulated(var) => {
                let cs = self.cs();
                let value = CM31::from_m31(var.elems[0].value, var.elems[1].value).inverse();
                let res = CM31Var::new_witness(&cs, &value);

                (&res * self).equalverify(&CM31Var::one(&cs));

                res
            }
        }
    }

    pub fn shift_by_i(&self) -> CM31Var {
        match self {
            CM31Var::Native(var) => {
                let cs = self.cs();
                CM31Var::Native(CM31NativeVar {
                    cs: cs.clone(),
                    value: var.value * CM31::from_u32_unchecked(0, 1),
                    variable: cs.mul(var.variable, 2),
                })
            }
            CM31Var::Emulated(var) => CM31Var::Emulated(CM31EmulatedVar {
                cs: var.cs.clone(),
                elems: [-&var.elems[1], var.elems[0].clone()],
            }),
        }
    }

    pub fn mul_constant_m31(&self, constant: M31) -> CM31Var {
        match self {
            CM31Var::Native(var) => {
                let cs = self.cs();
                let value = var.value * constant;

                CM31Var::Native(CM31NativeVar {
                    cs: cs.clone(),
                    value,
                    variable: cs.mul_constant(var.variable, constant),
                })
            }
            CM31Var::Emulated(var) => {
                let cs = self.cs();

                CM31Var::Emulated(CM31EmulatedVar {
                    cs: cs.clone(),
                    elems: [
                        var.elems[0].mul_constant(constant),
                        var.elems[1].mul_constant(constant),
                    ],
                })
            }
        }
    }

    pub fn mul_constant_cm31(&self, constant: CM31) -> CM31Var {
        match self {
            CM31Var::Native(var) => {
                let cs = self.cs();

                let a = self.mul_constant_m31(constant.0);
                let b = self.mul_constant_m31(constant.1);

                let variable = match (a, b) {
                    (CM31Var::Native(a), CM31Var::Native(b)) => {
                        cs.add(a.variable, cs.mul(b.variable, 2))
                    }
                    _ => unimplemented!(),
                };

                CM31Var::Native(CM31NativeVar {
                    cs,
                    value: var.value * constant,
                    variable,
                })
            }
            CM31Var::Emulated(var) => {
                let cs = self.cs();

                // (a + bi) * (c + di) = (ac - bd) + (ad + bc)i
                let ac = var.elems[0].mul_constant(constant.0);
                let bd = var.elems[1].mul_constant(constant.1);
                let ad = var.elems[0].mul_constant(constant.1);
                let bc = var.elems[1].mul_constant(constant.0);

                let first = &ac - &bd;
                let second = &ad + &bc;

                CM31Var::Emulated(CM31EmulatedVar {
                    cs: cs.clone(),
                    elems: [first, second],
                })
            }
        }
    }
}
