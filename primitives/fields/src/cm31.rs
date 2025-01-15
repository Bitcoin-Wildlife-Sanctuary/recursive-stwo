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
    pub value: CM31,
    pub real: M31Var,
    pub imag: M31Var,
}

impl DVar for CM31Var {
    type Value = CM31;

    fn cs(&self) -> ConstraintSystemRef {
        self.real.cs.and(&self.imag.cs)
    }
}

impl AllocVar for CM31Var {
    fn new_variables(cs: &ConstraintSystemRef, value: &Self::Value, mode: AllocationMode) -> Self {
        let real = M31Var::new_variables(cs, &value.0, mode);
        let imag = M31Var::new_variables(cs, &value.1, mode);
        Self {
            value: *value,
            real,
            imag,
        }
    }
}

impl From<&M31Var> for CM31Var {
    fn from(var: &M31Var) -> Self {
        let cs = var.cs();
        Self {
            value: CM31::from(var.value),
            real: var.clone(),
            imag: M31Var::zero(&cs),
        }
    }
}

impl Add<&M31Var> for &CM31Var {
    type Output = CM31Var;

    fn add(self, rhs: &M31Var) -> CM31Var {
        CM31Var {
            value: self.value + rhs.value,
            real: &self.real + rhs,
            imag: self.imag.clone(),
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
        CM31Var {
            value: self.value + rhs.value,
            real: &self.real + &rhs.real,
            imag: &self.imag + &rhs.imag,
        }
    }
}

impl Sub<&M31Var> for &CM31Var {
    type Output = CM31Var;

    fn sub(self, rhs: &M31Var) -> CM31Var {
        CM31Var {
            value: self.value - rhs.value,
            real: &self.real - rhs,
            imag: self.imag.clone(),
        }
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
        CM31Var {
            value: self.value - rhs.value,
            real: &self.real - &rhs.real,
            imag: &self.imag - &rhs.imag,
        }
    }
}

impl Mul<&M31Var> for &CM31Var {
    type Output = CM31Var;

    fn mul(self, rhs: &M31Var) -> CM31Var {
        CM31Var {
            value: self.value * rhs.value,
            real: &self.real * rhs,
            imag: &self.imag * rhs,
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
        let t1 = &self.real * &rhs.real;
        let t2 = &self.imag * &rhs.imag;
        let t3 = &self.real * &rhs.imag;
        let t4 = &self.imag * &rhs.real;

        CM31Var {
            value: self.value * rhs.value,
            real: &t1 - &t2,
            imag: &t3 + &t4,
        }
    }
}

impl Neg for &CM31Var {
    type Output = CM31Var;

    fn neg(self) -> Self::Output {
        CM31Var {
            value: -self.value,
            real: -&self.real,
            imag: -&self.imag,
        }
    }
}

impl CM31Var {
    pub fn from_m31(real: &M31Var, imag: &M31Var) -> Self {
        Self {
            value: CM31(real.value, imag.value),
            real: real.clone(),
            imag: imag.clone(),
        }
    }

    pub fn zero(cs: &ConstraintSystemRef) -> CM31Var {
        CM31Var {
            value: CM31::zero(),
            real: M31Var::zero(cs),
            imag: M31Var::zero(cs),
        }
    }

    pub fn one(cs: &ConstraintSystemRef) -> CM31Var {
        CM31Var {
            value: CM31::one(),
            real: M31Var::one(cs),
            imag: M31Var::zero(cs),
        }
    }

    pub fn equalverify(&self, rhs: &CM31Var) {
        assert_eq!(self.value, rhs.value);
        self.real.equalverify(&rhs.real);
        self.imag.equalverify(&rhs.imag);
    }

    pub fn inv(&self) -> CM31Var {
        let cs = self.cs();
        let value = self.value.inverse();
        let res = CM31Var::new_witness(&cs, &value);

        let expected_one = &res * self;
        expected_one.real.equalverify(&M31Var::one(&cs));
        cs.enforce_zero(expected_one.imag.variable);

        res
    }

    pub fn shift_by_i(&self) -> CM31Var {
        CM31Var {
            value: self.value * CM31::from_u32_unchecked(0, 1),
            real: -&self.imag,
            imag: self.real.clone(),
        }
    }

    pub fn mul_constant_m31(&self, constant: M31) -> CM31Var {
        let value = self.value * constant;

        CM31Var {
            value,
            real: self.real.mul_constant(constant),
            imag: self.imag.mul_constant(constant),
        }
    }

    pub fn mul_constant_cm31(&self, constant: CM31) -> CM31Var {
        let t1 = self.real.mul_constant(constant.0);
        let t2 = self.imag.mul_constant(constant.1);
        let t3 = self.real.mul_constant(constant.1);
        let t4 = self.imag.mul_constant(constant.0);

        CM31Var {
            value: self.value * constant,
            real: &t1 - &t2,
            imag: &t3 + &t4,
        }
    }
}
