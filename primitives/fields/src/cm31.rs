use crate::M31Var;
use circle_plonk_dsl_constraint_system::dvar::{AllocVar, AllocationMode, DVar};
use circle_plonk_dsl_constraint_system::ConstraintSystemRef;
use num_traits::{One, Zero};
use std::ops::{Add, Mul, Neg, Sub};
use stwo_prover::core::fields::cm31::CM31;
use stwo_prover::core::fields::m31::M31;
use stwo_prover::core::fields::FieldExpOps;

#[derive(Debug, Clone)]
pub struct CM31Var {
    pub cs: ConstraintSystemRef,
    pub value: CM31,
    pub variable: usize,
}

impl DVar for CM31Var {
    type Value = CM31;

    fn cs(&self) -> ConstraintSystemRef {
        self.cs.clone()
    }
}

impl AllocVar for CM31Var {
    fn new_variables(cs: &ConstraintSystemRef, value: &Self::Value, mode: AllocationMode) -> Self {
        if mode != AllocationMode::Constant {
            let real = M31Var::new_variables(cs, &value.0, mode);
            let imag = M31Var::new_variables(cs, &value.1, mode);

            let res = cs.add(real.variable, cs.mul(imag.variable, 2));
            Self {
                cs: cs.clone(),
                value: *value,
                variable: res,
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

        let f = format!("cm31 {},{}", value.0 .0, value.1 .0);
        let exist = cs.get_cache(f.clone());
        if let Some(variable) = exist {
            Self {
                cs: cs.clone(),
                value: *value,
                variable,
            }
        } else {
            let real = M31Var::new_constant(cs, &value.0);
            let imag = M31Var::new_constant(cs, &value.1);

            let variable = cs.add(real.variable, cs.mul(imag.variable, 2));
            cs.set_cache(f, variable);
            Self {
                cs: cs.clone(),
                value: *value,
                variable,
            }
        }
    }
}

impl From<&M31Var> for CM31Var {
    fn from(var: &M31Var) -> Self {
        let cs = var.cs();
        Self {
            cs,
            value: CM31::from(var.value),
            variable: var.variable,
        }
    }
}

impl Add<&M31Var> for &CM31Var {
    type Output = CM31Var;

    fn add(self, rhs: &M31Var) -> CM31Var {
        let cs = self.cs().and(&rhs.cs);
        CM31Var {
            cs: cs.clone(),
            value: self.value + rhs.value,
            variable: cs.add(self.variable, rhs.variable),
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
        CM31Var {
            cs: cs.clone(),
            value: self.value + rhs.value,
            variable: cs.add(self.variable, rhs.variable),
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
        CM31Var {
            cs: cs.clone(),
            value: self.value * rhs.value,
            variable: cs.mul(self.variable, rhs.variable),
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
        CM31Var {
            cs: cs.clone(),
            value: self.value * rhs.value,
            variable: cs.mul(self.variable, rhs.variable),
        }
    }
}

impl Neg for &CM31Var {
    type Output = CM31Var;

    fn neg(self) -> Self::Output {
        let value = -self.value;
        let variable = self.cs.mul_constant(self.variable, M31::one().neg());

        CM31Var {
            cs: self.cs.clone(),
            value,
            variable,
        }
    }
}

impl CM31Var {
    pub fn value(&self) -> CM31 {
        self.value
    }

    pub fn from_m31(real: &M31Var, imag: &M31Var) -> Self {
        let cs = real.cs().and(&imag.cs());
        let value = CM31::from_m31(real.value, imag.value);
        let variable = cs.add(real.variable, cs.mul(imag.variable, 2));
        Self {
            cs,
            value,
            variable,
        }
    }

    pub fn zero(cs: &ConstraintSystemRef) -> CM31Var {
        CM31Var {
            cs: cs.clone(),
            value: CM31::zero(),
            variable: 0,
        }
    }

    pub fn one(cs: &ConstraintSystemRef) -> CM31Var {
        CM31Var {
            cs: cs.clone(),
            value: CM31::one(),
            variable: 1,
        }
    }

    pub fn i(cs: &ConstraintSystemRef) -> CM31Var {
        CM31Var {
            cs: cs.clone(),
            value: CM31::from_u32_unchecked(0, 1),
            variable: 2,
        }
    }

    pub fn equalverify(&self, rhs: &CM31Var) {
        assert_eq!(self.value, rhs.value);
        let cs = self.cs.and(&rhs.cs);
        cs.insert_gate(self.variable, 0, rhs.variable, M31::one());
    }

    pub fn inv(&self) -> CM31Var {
        let cs = self.cs();
        let value = self.value.inverse();
        let res = CM31Var::new_witness(&cs, &value);
        res
    }

    pub fn shift_by_i(&self) -> CM31Var {
        let cs = self.cs();
        CM31Var {
            cs: cs.clone(),
            value: self.value * CM31::from_u32_unchecked(0, 1),
            variable: cs.mul(self.variable, 2),
        }
    }

    pub fn mul_constant_m31(&self, constant: M31) -> CM31Var {
        let cs = self.cs();
        let value = self.value * constant;
        CM31Var {
            cs: cs.clone(),
            value,
            variable: cs.mul_constant(self.variable, constant),
        }
    }

    pub fn mul_constant_cm31(&self, constant: CM31) -> CM31Var {
        let cs = self.cs();

        let a = self.mul_constant_m31(constant.0);
        let b = self.mul_constant_m31(constant.1);

        let variable = cs.add(a.variable, cs.mul(b.variable, 2));
        CM31Var {
            cs,
            value: self.value * constant,
            variable,
        }
    }
}
