use crate::{CM31Var, M31Var};
use circle_plonk_dsl_constraint_system::dvar::{AllocVar, AllocationMode, DVar};
use circle_plonk_dsl_constraint_system::{ConstraintSystemRef, ConstraintSystemType};
use num_traits::{One, Zero};
use std::ops::{Add, Mul, Neg, Sub};
use stwo_prover::core::fields::cm31::CM31;
use stwo_prover::core::fields::m31::M31;
use stwo_prover::core::fields::qm31::QM31;
use stwo_prover::core::fields::FieldExpOps;

#[derive(Debug, Clone)]
pub enum QM31Var {
    Native(QM31NativeVar),
    Emulated(QM31EmulatedVar),
}

#[derive(Debug, Clone)]
pub struct QM31NativeVar {
    pub cs: ConstraintSystemRef,
    pub value: QM31,
    pub variable: usize,
}

#[derive(Debug, Clone)]
pub struct QM31EmulatedVar {
    pub cs: ConstraintSystemRef,
    pub elems: [CM31Var; 2],
}

impl DVar for QM31Var {
    type Value = QM31;

    fn cs(&self) -> ConstraintSystemRef {
        match self {
            QM31Var::Native(var) => var.cs.clone(),
            QM31Var::Emulated(var) => var.cs.clone(),
        }
    }
}

impl AllocVar for QM31Var {
    fn new_variables(cs: &ConstraintSystemRef, value: &Self::Value, mode: AllocationMode) -> Self {
        if mode != AllocationMode::Constant {
            if cs.get_type() == ConstraintSystemType::QM31 {
                QM31Var::Native(QM31NativeVar {
                    cs: cs.clone(),
                    value: *value,
                    variable: cs.new_qm31(*value, mode),
                })
            } else {
                let a = CM31Var::new_variables(cs, &value.0, mode);
                let b = CM31Var::new_variables(cs, &value.1, mode);
                QM31Var::Emulated(QM31EmulatedVar {
                    cs: cs.clone(),
                    elems: [a, b],
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
        if *value == QM31::from_u32_unchecked(0, 1, 0, 0) {
            return Self::i(&cs);
        }
        if *value == QM31::from_u32_unchecked(0, 0, 1, 0) {
            return Self::j(&cs);
        }

        if cs.get_type() == ConstraintSystemType::QM31 {
            let f = format!(
                "qm31 {},{},{},{}",
                value.0 .0 .0, value.0 .1 .0, value.1 .0 .0, value.1 .1 .0
            );
            let exist = cs.get_cache(f.clone());
            if let Some(variable) = exist {
                Self::Native(QM31NativeVar {
                    cs: cs.clone(),
                    value: *value,
                    variable,
                })
            } else {
                let variable = cs.new_qm31(*value, AllocationMode::Constant);
                cs.set_cache(f, variable);
                Self::Native(QM31NativeVar {
                    cs: cs.clone(),
                    value: *value,
                    variable,
                })
            }
        } else {
            let a = CM31Var::new_constant(cs, &value.0);
            let b = CM31Var::new_constant(cs, &value.1);

            Self::Emulated(QM31EmulatedVar {
                cs: cs.clone(),
                elems: [a, b],
            })
        }
    }
}

impl From<&M31Var> for QM31Var {
    fn from(var: &M31Var) -> Self {
        let cs = var.cs();
        if cs.get_type() == ConstraintSystemType::QM31 {
            Self::Native(QM31NativeVar {
                cs,
                value: QM31::from(var.value),
                variable: var.variable,
            })
        } else {
            Self::Emulated(QM31EmulatedVar {
                cs: cs.clone(),
                elems: [CM31Var::from(var), CM31Var::zero(&cs)],
            })
        }
    }
}

impl Add<&M31Var> for &QM31Var {
    type Output = QM31Var;

    fn add(self, rhs: &M31Var) -> Self::Output {
        let cs = self.cs();
        match self {
            QM31Var::Native(var) => QM31Var::Native(QM31NativeVar {
                cs: cs.clone(),
                value: var.value + rhs.value,
                variable: cs.add(var.variable, rhs.variable),
            }),
            QM31Var::Emulated(var) => QM31Var::Emulated(QM31EmulatedVar {
                cs: cs.clone(),
                elems: [&var.elems[0] + rhs, var.elems[1].clone()],
            }),
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
        let cs = self.cs();
        match (self, rhs) {
            (QM31Var::Native(lhs), CM31Var::Native(rhs)) => QM31Var::Native(QM31NativeVar {
                cs: cs.clone(),
                value: lhs.value + QM31(rhs.value, CM31::zero()),
                variable: cs.add(lhs.variable, rhs.variable),
            }),
            (QM31Var::Emulated(lhs), CM31Var::Emulated(_)) => QM31Var::Emulated(QM31EmulatedVar {
                cs,
                elems: [&lhs.elems[0] + rhs, lhs.elems[1].clone()],
            }),
            _ => unimplemented!(),
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
        let cs = self.cs();

        match (self, rhs) {
            (QM31Var::Native(lhs), QM31Var::Native(rhs)) => QM31Var::Native(QM31NativeVar {
                cs: cs.clone(),
                value: lhs.value + rhs.value,
                variable: cs.add(lhs.variable, rhs.variable),
            }),
            (QM31Var::Emulated(lhs), QM31Var::Emulated(rhs)) => {
                QM31Var::Emulated(QM31EmulatedVar {
                    cs: cs.clone(),
                    elems: [&lhs.elems[0] + &rhs.elems[0], &lhs.elems[1] + &rhs.elems[1]],
                })
            }
            _ => unimplemented!(),
        }
    }
}

impl Sub<&M31Var> for &QM31Var {
    type Output = QM31Var;

    fn sub(self, rhs: &M31Var) -> Self::Output {
        self + &(-rhs)
    }
}

impl Sub<&CM31Var> for &QM31Var {
    type Output = QM31Var;

    fn sub(self, rhs: &CM31Var) -> Self::Output {
        self + &(-rhs)
    }
}

impl Sub<&QM31Var> for &QM31Var {
    type Output = QM31Var;

    fn sub(self, rhs: &QM31Var) -> Self::Output {
        self + &(-rhs)
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
        match self {
            QM31Var::Native(var) => {
                let cs = self.cs();
                QM31Var::Native(QM31NativeVar {
                    cs: cs.clone(),
                    value: var.value * rhs.value,
                    variable: cs.mul(var.variable, rhs.variable),
                })
            }
            QM31Var::Emulated(var) => {
                let cs = self.cs();
                QM31Var::Emulated(QM31EmulatedVar {
                    cs: cs.clone(),
                    elems: [&var.elems[0] * rhs, &var.elems[1] * rhs],
                })
            }
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
        match (self, rhs) {
            (QM31Var::Native(lhs), CM31Var::Native(rhs)) => {
                let cs = self.cs();
                QM31Var::Native(QM31NativeVar {
                    cs: cs.clone(),
                    value: lhs.value * QM31(rhs.value, CM31::zero()),
                    variable: cs.mul(lhs.variable, rhs.variable),
                })
            }
            (QM31Var::Emulated(lhs), CM31Var::Emulated(_)) => {
                let cs = self.cs();
                QM31Var::Emulated(QM31EmulatedVar {
                    cs: cs.clone(),
                    elems: [&lhs.elems[0] * rhs, &lhs.elems[1] * rhs],
                })
            }
            _ => unimplemented!(),
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
        match (self, rhs) {
            (QM31Var::Native(lhs), QM31Var::Native(rhs)) => {
                let cs = self.cs();
                QM31Var::Native(QM31NativeVar {
                    cs: cs.clone(),
                    value: lhs.value * rhs.value,
                    variable: cs.mul(lhs.variable, rhs.variable),
                })
            }
            (QM31Var::Emulated(lhs), QM31Var::Emulated(rhs)) => {
                // (a + bj) * (c + dj) = (ac + (2 + i) * bd) + (ad + bc) j
                let cs = self.cs();

                let ac = &lhs.elems[0] * &rhs.elems[0];
                let bd = &lhs.elems[1] * &rhs.elems[1];
                let ad = &lhs.elems[0] * &rhs.elems[1];
                let bc = &lhs.elems[1] * &rhs.elems[0];

                let bd_shifted = bd.shift_by_i();
                let bd_doubled = &bd + &bd;

                let first = &(&ac + &bd_shifted) + &bd_doubled;
                let second = &ad + &bc;

                QM31Var::Emulated(QM31EmulatedVar {
                    cs: cs.clone(),
                    elems: [first, second],
                })
            }
            _ => unimplemented!(),
        }
    }
}

impl Neg for &QM31Var {
    type Output = QM31Var;

    fn neg(self) -> Self::Output {
        match self {
            QM31Var::Native(var) => {
                let value = -var.value;
                let variable = var.cs.mul_constant(var.variable, M31::one().neg());

                QM31Var::Native(QM31NativeVar {
                    cs: var.cs.clone(),
                    value,
                    variable,
                })
            }
            QM31Var::Emulated(var) => QM31Var::Emulated(QM31EmulatedVar {
                cs: var.cs.clone(),
                elems: [-&var.elems[0], -&var.elems[1]],
            }),
        }
    }
}

impl QM31Var {
    pub fn value(&self) -> QM31 {
        match self {
            QM31Var::Native(var) => var.value,
            QM31Var::Emulated(var) => QM31(var.elems[0].value(), var.elems[1].value()),
        }
    }

    pub fn from_m31(a0: &M31Var, a1: &M31Var, a2: &M31Var, a3: &M31Var) -> Self {
        let cs = a0.cs().and(&a1.cs()).and(&a2.cs()).and(&a3.cs());

        if cs.get_type() == ConstraintSystemType::QM31 {
            QM31Var::Native(QM31NativeVar {
                cs: cs.clone(),
                value: QM31(CM31(a0.value, a1.value), CM31(a2.value, a3.value)),
                variable: cs.add(
                    cs.add(a0.variable, cs.mul(a1.variable, 2)),
                    cs.mul(cs.add(a2.variable, cs.mul(a3.variable, 2)), 3),
                ),
            })
        } else {
            QM31Var::Emulated(QM31EmulatedVar {
                cs,
                elems: [CM31Var::from_m31(a0, a1), CM31Var::from_m31(a2, a3)],
            })
        }
    }

    pub fn decompose_m31(&self) -> [M31Var; 4] {
        match self {
            QM31Var::Native(var) => {
                let cs = self.cs();

                let a0 = M31Var::new_witness(&cs, &var.value.0 .0);
                let a1 = M31Var::new_witness(&cs, &var.value.0 .1);
                let a2 = M31Var::new_witness(&cs, &var.value.1 .0);
                let a3 = M31Var::new_witness(&cs, &var.value.1 .1);

                let l = cs.add(a0.variable, cs.mul(a1.variable, 2));
                let r = cs.mul(cs.add(a2.variable, cs.mul(a3.variable, 2)), 3);

                cs.insert_gate(l, r, var.variable, M31::one());

                [a0, a1, a2, a3]
            }
            QM31Var::Emulated(var) => match (&var.elems[0], &var.elems[1]) {
                (CM31Var::Emulated(a), CM31Var::Emulated(b)) => [
                    a.elems[0].clone(),
                    a.elems[1].clone(),
                    b.elems[0].clone(),
                    b.elems[1].clone(),
                ],
                _ => unimplemented!(),
            },
        }
    }

    pub fn decompose_cm31(&self) -> [CM31Var; 2] {
        match self {
            QM31Var::Native(_) => {
                let v = self.decompose_m31();

                let a0 = &CM31Var::from(&v[1]).shift_by_i() + &v[0];
                let a1 = &CM31Var::from(&v[3]).shift_by_i() + &v[2];

                [a0, a1]
            }
            QM31Var::Emulated(var) => [var.elems[0].clone(), var.elems[1].clone()],
        }
    }

    pub fn pow(&self, mut exp: u128) -> Self {
        let cs = self.cs();
        let mut bools = vec![];

        while exp > 0 {
            bools.push(exp & 1 != 0);
            exp >>= 1;
        }

        let mut cur = QM31Var::one(&cs);
        for (i, &b) in bools.iter().enumerate().rev() {
            if b {
                cur = &cur * self;
            }
            if i != 0 {
                cur = &cur * &cur;
            }
        }
        cur
    }

    pub fn from_cm31(a: &CM31Var, b: &CM31Var) -> Self {
        match (a, b) {
            (CM31Var::Native(a), CM31Var::Native(b)) => {
                let cs = a.cs.and(&b.cs);
                QM31Var::Native(QM31NativeVar {
                    cs: cs.clone(),
                    value: QM31(a.value, b.value),
                    variable: cs.add(a.variable, cs.mul(b.variable, 3)),
                })
            }
            (CM31Var::Emulated(_), CM31Var::Emulated(_)) => {
                let cs = a.cs().and(&b.cs());
                QM31Var::Emulated(QM31EmulatedVar {
                    cs: cs.clone(),
                    elems: [a.clone(), b.clone()],
                })
            }
            _ => unimplemented!(),
        }
    }

    pub fn zero(cs: &ConstraintSystemRef) -> QM31Var {
        if cs.get_type() == ConstraintSystemType::QM31 {
            QM31Var::Native(QM31NativeVar {
                cs: cs.clone(),
                value: QM31::zero(),
                variable: 0,
            })
        } else {
            QM31Var::Emulated(QM31EmulatedVar {
                cs: cs.clone(),
                elems: [CM31Var::zero(cs), CM31Var::zero(cs)],
            })
        }
    }

    pub fn one(cs: &ConstraintSystemRef) -> QM31Var {
        if cs.get_type() == ConstraintSystemType::QM31 {
            QM31Var::Native(QM31NativeVar {
                cs: cs.clone(),
                value: QM31::one(),
                variable: 1,
            })
        } else {
            QM31Var::Emulated(QM31EmulatedVar {
                cs: cs.clone(),
                elems: [CM31Var::one(cs), CM31Var::zero(cs)],
            })
        }
    }

    pub fn i(cs: &ConstraintSystemRef) -> QM31Var {
        if cs.get_type() == ConstraintSystemType::QM31 {
            QM31Var::Native(QM31NativeVar {
                cs: cs.clone(),
                value: QM31(CM31::from_u32_unchecked(0, 1), CM31::zero()),
                variable: 2,
            })
        } else {
            QM31Var::Emulated(QM31EmulatedVar {
                cs: cs.clone(),
                elems: [CM31Var::i(cs), CM31Var::zero(cs)],
            })
        }
    }

    pub fn j(cs: &ConstraintSystemRef) -> QM31Var {
        if cs.get_type() == ConstraintSystemType::QM31 {
            QM31Var::Native(QM31NativeVar {
                cs: cs.clone(),
                value: QM31(CM31::zero(), CM31::one()),
                variable: 3,
            })
        } else {
            QM31Var::Emulated(QM31EmulatedVar {
                cs: cs.clone(),
                elems: [CM31Var::zero(cs), CM31Var::one(cs)],
            })
        }
    }

    pub fn equalverify(&self, rhs: &QM31Var) {
        match (self, rhs) {
            (QM31Var::Native(a), QM31Var::Native(b)) => {
                assert_eq!(a.value, b.value);
                let cs = a.cs.and(&b.cs);
                cs.insert_gate(a.variable, 0, b.variable, M31::one());
            }
            (QM31Var::Emulated(a), QM31Var::Emulated(b)) => {
                a.elems[0].equalverify(&b.elems[0]);
                a.elems[1].equalverify(&b.elems[1]);
            }
            _ => unimplemented!(),
        }
    }

    pub fn inv(&self) -> QM31Var {
        match self {
            QM31Var::Native(a) => {
                let cs = self.cs();
                let value = a.value.inverse();
                let res = QM31Var::new_witness(&cs, &value);
                match &res {
                    QM31Var::Native(res) => {
                        cs.insert_gate(a.variable, res.variable, 1, M31::zero());
                    }
                    _ => unimplemented!(),
                }
                res
            }
            QM31Var::Emulated(a) => {
                let cs = self.cs();
                let value = match (&a.elems[0], &a.elems[1]) {
                    (CM31Var::Emulated(a), CM31Var::Emulated(b)) => QM31::from_m31(
                        a.elems[0].value,
                        a.elems[1].value,
                        b.elems[0].value,
                        b.elems[1].value,
                    ),
                    _ => unimplemented!(),
                }
                .inverse();
                let res = QM31Var::new_witness(&cs, &value);
                (&res * self).equalverify(&QM31Var::one(&cs));
                res
            }
        }
    }

    pub fn mul_constant_m31(&self, constant: M31) -> QM31Var {
        match self {
            QM31Var::Native(a) => {
                let value = a.value * constant;
                QM31Var::Native(QM31NativeVar {
                    cs: a.cs.clone(),
                    value,
                    variable: a.cs.mul_constant(a.variable, constant),
                })
            }
            QM31Var::Emulated(a) => {
                let cs = self.cs();
                QM31Var::Emulated(QM31EmulatedVar {
                    cs: cs.clone(),
                    elems: [
                        a.elems[0].mul_constant_m31(constant),
                        a.elems[1].mul_constant_m31(constant),
                    ],
                })
            }
        }
    }

    pub fn mul_constant_cm31(&self, constant: CM31) -> QM31Var {
        match self {
            QM31Var::Native(var) => {
                let cs = self.cs();

                let a = self.mul_constant_m31(constant.0);
                let b = self.mul_constant_m31(constant.1);

                let variable = match (a, b) {
                    (QM31Var::Native(a), QM31Var::Native(b)) => {
                        cs.add(a.variable, cs.mul(b.variable, 2))
                    }
                    _ => unimplemented!(),
                };

                QM31Var::Native(QM31NativeVar {
                    cs,
                    value: var.value * QM31(constant, CM31::zero()),
                    variable,
                })
            }
            QM31Var::Emulated(var) => {
                let cs = self.cs();
                QM31Var::Emulated(QM31EmulatedVar {
                    cs,
                    elems: [
                        var.elems[0].mul_constant_cm31(constant),
                        var.elems[1].mul_constant_cm31(constant),
                    ],
                })
            }
        }
    }

    pub fn mul_constant_qm31(&self, constant: QM31) -> QM31Var {
        match self {
            QM31Var::Native(var) => {
                let cs = self.cs();
                let constant_var = cs.new_qm31(constant, AllocationMode::Constant);

                QM31Var::Native(QM31NativeVar {
                    cs: cs.clone(),
                    value: var.value * constant,
                    variable: cs.mul(var.variable, constant_var),
                })
            }
            QM31Var::Emulated(var) => {
                // (a + bj) * (c + dj) = (ac + (2 + i) * bd) + (ad + bc) j
                let cs = self.cs();

                let ac = var.elems[0].mul_constant_cm31(constant.0);
                let bd_times_2_plus_i =
                    var.elems[1].mul_constant_cm31(constant.1 * CM31::from_u32_unchecked(2, 1));
                let ad = var.elems[0].mul_constant_cm31(constant.1);
                let bc = var.elems[1].mul_constant_cm31(constant.0);

                let first = &ac + &bd_times_2_plus_i;
                let second = &ad + &bc;

                QM31Var::Emulated(QM31EmulatedVar {
                    cs: cs.clone(),
                    elems: [first, second],
                })
            }
        }
    }

    pub fn shift_by_i(&self) -> QM31Var {
        match self {
            QM31Var::Native(var) => {
                let cs = self.cs();
                QM31Var::Native(QM31NativeVar {
                    cs: cs.clone(),
                    value: var.value * QM31::from_u32_unchecked(0, 1, 0, 0),
                    variable: cs.mul(var.variable, 2),
                })
            }
            QM31Var::Emulated(var) => {
                let cs = self.cs();
                QM31Var::Emulated(QM31EmulatedVar {
                    cs,
                    elems: [var.elems[0].shift_by_i(), var.elems[1].shift_by_i()],
                })
            }
        }
    }

    pub fn shift_by_j(&self) -> QM31Var {
        match self {
            QM31Var::Native(var) => {
                let cs = self.cs();
                QM31Var::Native(QM31NativeVar {
                    cs: cs.clone(),
                    value: var.value * QM31::from_u32_unchecked(0, 0, 1, 0),
                    variable: cs.mul(var.variable, 3),
                })
            }
            QM31Var::Emulated(var) => {
                let cs = self.cs();
                QM31Var::Emulated(QM31EmulatedVar {
                    cs,
                    elems: [
                        var.elems[1].mul_constant_cm31(CM31::from_u32_unchecked(2, 1)),
                        var.elems[0].clone(),
                    ],
                })
            }
        }
    }

    pub fn select(a: &Self, b: &Self, bit_value: bool, bit_variable: usize) -> Self {
        let cs = a.cs().and(&b.cs());

        match (a, b) {
            (QM31Var::Native(a_var), QM31Var::Native(b_var)) => {
                let value = if !bit_value { a_var.value } else { b_var.value };

                // the result is a + (b - a) * bit_value
                let b_minus_a = b - a;
                let mut variable = match b_minus_a {
                    QM31Var::Native(b_minus_a) => cs.mul(b_minus_a.variable, bit_variable),
                    _ => unimplemented!(),
                };
                variable = cs.add(a_var.variable, variable);

                QM31Var::Native(QM31NativeVar {
                    cs,
                    value,
                    variable,
                })
            }
            (QM31Var::Emulated(_), QM31Var::Emulated(_)) => {
                // the result is a + (b - a) * bit_value
                let b_minus_a = b - a;
                let tmp = M31Var {
                    cs,
                    value: if bit_value { M31::one() } else { M31::zero() },
                    variable: bit_variable,
                };
                &(&b_minus_a * &tmp) + a
            }
            _ => unimplemented!(),
        }
    }

    pub fn swap(a: &Self, b: &Self, bit_value: bool, bit_variable: usize) -> (Self, Self) {
        let cs = a.cs().and(&b.cs());

        match (a, b) {
            (QM31Var::Native(a_var), QM31Var::Native(b_var)) => {
                let (left_value, right_value) = if !bit_value {
                    (a_var.value, b_var.value)
                } else {
                    (b_var.value, a_var.value)
                };

                let b_minus_a = b - a;
                let mut left_variable = match b_minus_a {
                    QM31Var::Native(b_minus_a) => cs.mul(b_minus_a.variable, bit_variable),
                    _ => unimplemented!(),
                };
                left_variable = cs.add(a_var.variable, left_variable);

                let a_minus_b = a - b;
                let mut right_variable = match a_minus_b {
                    QM31Var::Native(a_minus_b) => cs.mul(a_minus_b.variable, bit_variable),
                    _ => unimplemented!(),
                };
                right_variable = cs.add(b_var.variable, right_variable);

                (
                    Self::Native(QM31NativeVar {
                        cs: cs.clone(),
                        value: left_value,
                        variable: left_variable,
                    }),
                    Self::Native(QM31NativeVar {
                        cs,
                        value: right_value,
                        variable: right_variable,
                    }),
                )
            }
            (QM31Var::Emulated(_), QM31Var::Emulated(_)) => {
                let b_minus_a = b - a;
                let a_minus_b = a - b;
                let tmp = M31Var {
                    cs,
                    value: if bit_value { M31::one() } else { M31::zero() },
                    variable: bit_variable,
                };
                let left = a + &(&b_minus_a * &tmp);
                let right = b + &(&a_minus_b * &tmp);
                (left, right)
            }
            _ => unimplemented!(),
        }
    }

    pub fn shift_by_ij(&self) -> QM31Var {
        self.shift_by_i().shift_by_j()
    }
}

#[cfg(test)]
mod test {
    use crate::QM31Var;
    use circle_plonk_dsl_constraint_system::dvar::AllocVar;
    use circle_plonk_dsl_constraint_system::ConstraintSystemRef;
    use num_traits::One;
    use rand::prelude::SmallRng;
    use rand::{Rng, SeedableRng};
    use stwo_prover::core::fields::qm31::QM31;
    use stwo_prover::core::fields::FieldExpOps;
    use stwo_prover::core::fri::FriConfig;
    use stwo_prover::core::pcs::PcsConfig;
    use stwo_prover::core::vcs::poseidon31_merkle::Poseidon31MerkleChannel;
    use stwo_prover::examples::plonk_with_poseidon::air::{
        prove_plonk_with_poseidon, verify_plonk_with_poseidon,
    };

    #[test]
    fn test_qm31_pow() {
        let config = PcsConfig {
            pow_bits: 20,
            fri_config: FriConfig::new(0, 5, 16),
        };

        let mut prng = SmallRng::seed_from_u64(0);
        let a: QM31 = prng.gen();
        let exp = 100u128;
        let b = a.pow(exp);

        let cs = ConstraintSystemRef::new_qm31_ref();

        let a_var = QM31Var::new_witness(&cs, &a);
        let b_var = QM31Var::new_witness(&cs, &b);
        a_var.pow(exp).equalverify(&b_var);

        cs.pad();
        cs.check_arithmetics();
        cs.populate_logup_arguments();
        cs.check_poseidon_invocations();

        let (plonk, mut poseidon) = cs.generate_qm31_circuit();
        let proof =
            prove_plonk_with_poseidon::<Poseidon31MerkleChannel>(config, &plonk, &mut poseidon);
        verify_plonk_with_poseidon::<Poseidon31MerkleChannel>(
            proof,
            config,
            &[
                (1, QM31::one()),
                (2, QM31::from_u32_unchecked(0, 1, 0, 0)),
                (3, QM31::from_u32_unchecked(0, 0, 1, 0)),
            ],
        )
        .unwrap();
    }
}
