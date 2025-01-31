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
    pub cs: ConstraintSystemRef,
    pub value: QM31,
    pub variable: usize,
}

impl DVar for QM31Var {
    type Value = QM31;

    fn cs(&self) -> ConstraintSystemRef {
        self.cs.clone()
    }
}

impl AllocVar for QM31Var {
    fn new_variables(cs: &ConstraintSystemRef, value: &Self::Value, mode: AllocationMode) -> Self {
        if mode != AllocationMode::Constant {
            Self {
                cs: cs.clone(),
                value: *value,
                variable: cs.new_qm31(*value, mode),
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

        let f = format!(
            "qm31 {},{},{},{}",
            value.0 .0 .0, value.0 .1 .0, value.1 .0 .0, value.1 .1 .0
        );
        let exist = cs.get_cache(f.clone());
        if let Some(variable) = exist {
            Self {
                cs: cs.clone(),
                value: *value,
                variable,
            }
        } else {
            let variable = cs.new_qm31(*value, AllocationMode::Constant);
            cs.set_cache(f, variable);
            Self {
                cs: cs.clone(),
                value: *value,
                variable,
            }
        }
    }
}

impl From<&M31Var> for QM31Var {
    fn from(var: &M31Var) -> Self {
        let cs = var.cs();
        Self {
            cs,
            value: QM31::from(var.value),
            variable: var.variable,
        }
    }
}

impl Add<&M31Var> for &QM31Var {
    type Output = QM31Var;

    fn add(self, rhs: &M31Var) -> Self::Output {
        let cs = self.cs();
        QM31Var {
            cs: cs.clone(),
            value: self.value + rhs.value,
            variable: cs.add(self.variable, rhs.variable),
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
        QM31Var {
            cs: cs.clone(),
            value: self.value + QM31(rhs.value, CM31::zero()),
            variable: cs.add(self.variable, rhs.variable),
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
        QM31Var {
            cs: cs.clone(),
            value: self.value + rhs.value,
            variable: cs.add(self.variable, rhs.variable),
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
        let cs = self.cs();
        QM31Var {
            cs: cs.clone(),
            value: self.value * rhs.value,
            variable: cs.mul(self.variable, rhs.variable),
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
        let cs = self.cs();
        QM31Var {
            cs: cs.clone(),
            value: self.value * QM31(rhs.value, CM31::zero()),
            variable: cs.mul(self.variable, rhs.variable),
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
        let cs = self.cs();
        QM31Var {
            cs: cs.clone(),
            value: self.value * rhs.value,
            variable: cs.mul(self.variable, rhs.variable),
        }
    }
}

impl Neg for &QM31Var {
    type Output = QM31Var;

    fn neg(self) -> Self::Output {
        let value = -self.value;
        let variable = self.cs.mul_constant(self.variable, M31::one().neg());

        QM31Var {
            cs: self.cs.clone(),
            value,
            variable,
        }
    }
}

impl QM31Var {
    pub fn from_m31(a0: &M31Var, a1: &M31Var, a2: &M31Var, a3: &M31Var) -> Self {
        let cs = a0.cs().and(&a1.cs()).and(&a2.cs()).and(&a3.cs());

        Self {
            cs: cs.clone(),
            value: QM31(CM31(a0.value, a1.value), CM31(a2.value, a3.value)),
            variable: cs.add(
                cs.add(a0.variable, cs.mul(a1.variable, 2)),
                cs.mul(cs.add(a2.variable, cs.mul(a3.variable, 2)), 3),
            ),
        }
    }

    pub fn decompose_m31(&self) -> [M31Var; 4] {
        let cs = self.cs();

        let a0 = M31Var::new_witness(&cs, &self.value.0 .0);
        let a1 = M31Var::new_witness(&cs, &self.value.0 .1);
        let a2 = M31Var::new_witness(&cs, &self.value.1 .0);
        let a3 = M31Var::new_witness(&cs, &self.value.1 .1);

        let l = cs.add(a0.variable, cs.mul(a1.variable, 2));
        let r = cs.mul(cs.add(a2.variable, cs.mul(a3.variable, 2)), 3);

        cs.insert_gate(l, r, self.variable, M31::one());

        [a0, a1, a2, a3]
    }

    pub fn decompose_cm31(&self) -> [CM31Var; 2] {
        let v = self.decompose_m31();

        let a0 = &CM31Var::from(&v[1]).shift_by_i() + &v[0];
        let a1 = &CM31Var::from(&v[3]).shift_by_i() + &v[2];

        [a0, a1]
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

    pub fn from_cm31(a0: &CM31Var, a1: &CM31Var) -> Self {
        let cs = a0.cs().and(&a1.cs());

        Self {
            cs: cs.clone(),
            value: QM31(a0.value, a1.value),
            variable: cs.add(a0.variable, cs.mul(a1.variable, 3)),
        }
    }

    pub fn zero(cs: &ConstraintSystemRef) -> QM31Var {
        QM31Var {
            cs: cs.clone(),
            value: QM31::zero(),
            variable: 0,
        }
    }

    pub fn one(cs: &ConstraintSystemRef) -> QM31Var {
        QM31Var {
            cs: cs.clone(),
            value: QM31::one(),
            variable: 1,
        }
    }

    pub fn i(cs: &ConstraintSystemRef) -> QM31Var {
        QM31Var {
            cs: cs.clone(),
            value: QM31(CM31::from_u32_unchecked(0, 1), CM31::zero()),
            variable: 2,
        }
    }

    pub fn j(cs: &ConstraintSystemRef) -> QM31Var {
        QM31Var {
            cs: cs.clone(),
            value: QM31(CM31::zero(), CM31::one()),
            variable: 3,
        }
    }

    pub fn equalverify(&self, rhs: &QM31Var) {
        assert_eq!(self.value, rhs.value);
        let cs = self.cs.and(&rhs.cs);
        cs.insert_gate(self.variable, 0, rhs.variable, M31::one());
    }

    pub fn inv(&self) -> QM31Var {
        let cs = self.cs();
        let value = self.value.inverse();
        let res = QM31Var::new_witness(&cs, &value);
        cs.insert_gate(self.variable, res.variable, 1, M31::zero());
        res
    }

    pub fn mul_constant_m31(&self, constant: M31) -> QM31Var {
        let value = self.value * constant;
        QM31Var {
            cs: self.cs.clone(),
            value,
            variable: self.cs.mul_constant(self.variable, constant),
        }
    }

    pub fn mul_constant_cm31(&self, constant: CM31) -> QM31Var {
        let cs = self.cs();

        let a = self.mul_constant_m31(constant.0);
        let b = self.mul_constant_m31(constant.1);

        let variable = cs.add(a.variable, cs.mul(b.variable, 2));

        QM31Var {
            cs,
            value: self.value * QM31(constant, CM31::zero()),
            variable,
        }
    }

    pub fn mul_constant_qm31(&self, constant: QM31) -> QM31Var {
        let cs = self.cs();
        let constant_var = cs.new_qm31(constant, AllocationMode::Constant);

        QM31Var {
            cs: cs.clone(),
            value: self.value * constant,
            variable: cs.mul(self.variable, constant_var),
        }
    }

    pub fn shift_by_i(&self) -> QM31Var {
        let cs = self.cs();
        QM31Var {
            cs: cs.clone(),
            value: self.value * QM31::from_u32_unchecked(0, 1, 0, 0),
            variable: cs.mul(self.variable, 2),
        }
    }

    pub fn shift_by_j(&self) -> QM31Var {
        let cs = self.cs();
        QM31Var {
            cs: cs.clone(),
            value: self.value * QM31::from_u32_unchecked(0, 0, 1, 0),
            variable: cs.mul(self.variable, 3),
        }
    }

    pub fn select(a: &Self, b: &Self, bit_value: bool, bit_variable: usize) -> Self {
        let cs = a.cs().and(&b.cs());

        let value = if !bit_value { a.value } else { b.value };

        // the result is a + (b - a) * bit_value
        let b_minus_a = b - a;
        let mut variable = cs.mul(b_minus_a.variable, bit_variable);
        variable = cs.add(a.variable, variable);

        Self {
            cs,
            value,
            variable,
        }
    }

    pub fn swap(a: &Self, b: &Self, bit_value: bool, bit_variable: usize) -> (Self, Self) {
        let cs = a.cs().and(&b.cs());

        let (left_value, right_value) = if !bit_value {
            (a.value, b.value)
        } else {
            (b.value, a.value)
        };

        let b_minus_a = b - a;
        let mut left_variable = cs.mul(b_minus_a.variable, bit_variable);
        left_variable = cs.add(a.variable, left_variable);

        let a_minus_b = a - b;
        let mut right_variable = cs.mul(a_minus_b.variable, bit_variable);
        right_variable = cs.add(b.variable, right_variable);

        (
            Self {
                cs: cs.clone(),
                value: left_value,
                variable: left_variable,
            },
            Self {
                cs,
                value: right_value,
                variable: right_variable,
            },
        )
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

        let cs = ConstraintSystemRef::new_ref();

        let a_var = QM31Var::new_witness(&cs, &a);
        let b_var = QM31Var::new_witness(&cs, &b);
        a_var.pow(exp).equalverify(&b_var);

        cs.pad();
        cs.check_arithmetics();
        cs.populate_logup_arguments();
        cs.check_poseidon_invocations();

        let (plonk, mut poseidon) = cs.generate_circuit();
        let proof = prove_plonk_with_poseidon::<Poseidon31MerkleChannel>(
            plonk.mult_a.length.ilog2(),
            poseidon.0.len().ilog2(),
            config,
            &plonk,
            &mut poseidon,
        );
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
