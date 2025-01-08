use crate::{CM31Var, M31Var};
use circle_plonk_dsl_constraint_system::dvar::{AllocVar, AllocationMode, DVar};
use circle_plonk_dsl_constraint_system::ConstraintSystemRef;
use num_traits::{One, Zero};
use std::ops::{Add, Mul, Neg, Sub};
use stwo_prover::core::fields::cm31::CM31;
use stwo_prover::core::fields::m31::M31;
use stwo_prover::core::fields::qm31::QM31;
use stwo_prover::core::fields::FieldExpOps;

#[derive(Debug, Clone)]
pub struct QM31Var {
    pub value: QM31,
    pub first: CM31Var,
    pub second: CM31Var,
}

impl DVar for QM31Var {
    type Value = QM31;

    fn cs(&self) -> ConstraintSystemRef {
        self.first.cs().and(&self.second.cs())
    }
}

impl AllocVar for QM31Var {
    fn new_variables(cs: &ConstraintSystemRef, value: &Self::Value, mode: AllocationMode) -> Self {
        let first = CM31Var::new_variables(cs, &value.0, mode);
        let second = CM31Var::new_variables(cs, &value.1, mode);
        Self {
            value: *value,
            first,
            second,
        }
    }
}

impl Add<&M31Var> for &QM31Var {
    type Output = QM31Var;

    fn add(self, rhs: &M31Var) -> Self::Output {
        QM31Var {
            value: self.value + rhs.value,
            first: &self.first + rhs,
            second: self.second.clone(),
        }
    }
}

impl Add<&QM31Var> for &M31Var {
    type Output = QM31Var;

    fn add(self, rhs: &QM31Var) -> Self::Output {
        rhs + self
    }
}

impl Add<&CM31Var> for &QM31Var {
    type Output = QM31Var;

    fn add(self, rhs: &CM31Var) -> Self::Output {
        QM31Var {
            value: self.value + QM31(rhs.value, CM31::zero()),
            first: &self.first + rhs,
            second: self.second.clone(),
        }
    }
}

impl Add<&QM31Var> for &CM31Var {
    type Output = QM31Var;

    fn add(self, rhs: &QM31Var) -> Self::Output {
        rhs + self
    }
}

impl Add<&QM31Var> for &QM31Var {
    type Output = QM31Var;

    fn add(self, rhs: &QM31Var) -> Self::Output {
        QM31Var {
            value: self.value + rhs.value,
            first: &self.first + &rhs.first,
            second: &self.second + &rhs.second,
        }
    }
}

impl Sub<&M31Var> for &QM31Var {
    type Output = QM31Var;

    fn sub(self, rhs: &M31Var) -> Self::Output {
        QM31Var {
            value: self.value - rhs.value,
            first: &self.first - rhs,
            second: self.second.clone(),
        }
    }
}

impl Sub<&CM31Var> for &QM31Var {
    type Output = QM31Var;

    fn sub(self, rhs: &CM31Var) -> Self::Output {
        QM31Var {
            value: self.value - QM31(rhs.value, CM31::zero()),
            first: &self.first - rhs,
            second: self.second.clone(),
        }
    }
}

impl Sub<&QM31Var> for &QM31Var {
    type Output = QM31Var;

    fn sub(self, rhs: &QM31Var) -> Self::Output {
        QM31Var {
            value: self.value - rhs.value,
            first: &self.first - &rhs.first,
            second: &self.second - &rhs.second,
        }
    }
}

impl Sub<&QM31Var> for &M31Var {
    type Output = QM31Var;

    fn sub(self, rhs: &QM31Var) -> Self::Output {
        self + &(-rhs)
    }
}

impl Sub<&QM31Var> for &CM31Var {
    type Output = QM31Var;

    fn sub(self, rhs: &QM31Var) -> Self::Output {
        self + &(-rhs)
    }
}

impl Mul<&M31Var> for &QM31Var {
    type Output = QM31Var;

    fn mul(self, rhs: &M31Var) -> Self::Output {
        QM31Var {
            value: self.value * rhs.value,
            first: &self.first * rhs,
            second: &self.second * rhs,
        }
    }
}

impl Mul<&QM31Var> for &M31Var {
    type Output = QM31Var;

    fn mul(self, rhs: &QM31Var) -> Self::Output {
        rhs * self
    }
}

impl Mul<&CM31Var> for &QM31Var {
    type Output = QM31Var;

    fn mul(self, rhs: &CM31Var) -> Self::Output {
        QM31Var {
            value: self.value * QM31(rhs.value, CM31::zero()),
            first: &self.first * rhs,
            second: &self.second * rhs,
        }
    }
}

impl Mul<&QM31Var> for &CM31Var {
    type Output = QM31Var;

    fn mul(self, rhs: &QM31Var) -> Self::Output {
        rhs * self
    }
}

impl Mul<&QM31Var> for &QM31Var {
    type Output = QM31Var;

    fn mul(self, rhs: &QM31Var) -> Self::Output {
        let a0b0 = &self.first * &rhs.first;
        let a1b1 = &self.second * &rhs.second;

        let sum_a = &self.first + &self.second;
        let sum_b = &rhs.first + &rhs.second;

        let asbs = &sum_a * &sum_b;
        let a1b1_shifted = a1b1.shift_by_i();

        let mut first = &a0b0 + &a1b1;
        first = &first + &a1b1;
        first = &first + &a1b1_shifted;

        let mut second = &asbs - &a0b0;
        second = &second - &a1b1;

        QM31Var {
            value: self.value * rhs.value,
            first,
            second,
        }
    }
}

impl Neg for &QM31Var {
    type Output = QM31Var;

    fn neg(self) -> Self::Output {
        QM31Var {
            value: -self.value,
            first: -&self.first,
            second: -&self.second,
        }
    }
}

impl QM31Var {
    pub fn from_m31(a0: &M31Var, a1: &M31Var, a2: &M31Var, a3: &M31Var) -> Self {
        Self {
            value: QM31(CM31(a0.value, a1.value), CM31(a2.value, a3.value)),
            first: CM31Var::from_m31(a0, a1),
            second: CM31Var::from_m31(a2, a3),
        }
    }

    pub fn from_cm31(a0: &CM31Var, a1: &CM31Var) -> Self {
        Self {
            value: QM31(a0.value, a1.value),
            first: a0.clone(),
            second: a1.clone(),
        }
    }

    pub fn zero(cs: &ConstraintSystemRef) -> QM31Var {
        QM31Var {
            value: QM31::zero(),
            first: CM31Var::zero(cs),
            second: CM31Var::zero(cs),
        }
    }

    pub fn one(cs: &ConstraintSystemRef) -> QM31Var {
        QM31Var {
            value: QM31::one(),
            first: CM31Var::one(cs),
            second: CM31Var::zero(cs),
        }
    }

    pub fn equalverify(&self, rhs: &QM31Var) {
        assert_eq!(self.value, rhs.value);
        self.first.eq(&rhs.first);
        self.second.eq(&rhs.second);
    }

    pub fn inv(&self) -> QM31Var {
        let cs = self.cs();
        let value = self.value.inverse();
        let res = QM31Var::new_witness(&cs, &value);

        let expected_one = &res * self;
        expected_one.first.real.equalverify(&M31Var::one(&cs));
        cs.enforce_zero(expected_one.first.imag.variable);
        cs.enforce_zero(expected_one.second.real.variable);
        cs.enforce_zero(expected_one.second.imag.variable);

        res
    }

    pub fn mul_constant_m31(&self, constant: M31) -> QM31Var {
        let value = self.value * constant;

        QM31Var {
            value,
            first: self.first.mul_constant_m31(constant),
            second: self.second.mul_constant_m31(constant),
        }
    }

    pub fn mul_constant_cm31(&self, constant: CM31) -> QM31Var {
        let value = self.value * QM31(constant, CM31::zero());

        QM31Var {
            value,
            first: self.first.mul_constant_cm31(constant),
            second: self.second.mul_constant_cm31(constant),
        }
    }

    pub fn mul_constant_qm31(&self, constant: QM31) -> QM31Var {
        let a0b0 = self.first.mul_constant_cm31(constant.0);
        let a1b1 = self.second.mul_constant_cm31(constant.1);

        let sum_a = &self.first + &self.second;
        let sum_b = constant.0 + constant.1;

        let asbs = sum_a.mul_constant_cm31(sum_b);
        let a1b1_shifted = a1b1.shift_by_i();

        let mut first = &a0b0 + &a1b1;
        first = &first + &a1b1;
        first = &first + &a1b1_shifted;

        let mut second = &asbs - &a0b0;
        second = &second - &a1b1;

        QM31Var {
            value: self.value * constant,
            first,
            second,
        }
    }
}
