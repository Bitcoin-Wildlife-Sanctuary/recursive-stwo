use circle_plonk_dsl_constraint_system::var::{AllocVar, AllocationMode, Var};
use circle_plonk_dsl_constraint_system::ConstraintSystemRef;
use circle_plonk_dsl_fields::M31Var;
use num_traits::{One, Zero};
use std::ops::{Neg, Range, RangeFrom};
use stwo_prover::core::fields::m31::M31;
use stwo_prover::core::fields::qm31::QM31;

#[derive(Clone)]
pub struct BitsVar {
    pub cs: ConstraintSystemRef,
    pub value: Vec<bool>,
    pub variables: Vec<usize>,
}

impl Var for BitsVar {
    type Value = Vec<bool>;

    fn cs(&self) -> ConstraintSystemRef {
        self.cs.clone()
    }
}

impl AllocVar for BitsVar {
    fn new_variables(cs: &ConstraintSystemRef, value: &Self::Value, mode: AllocationMode) -> Self {
        let mut variables = Vec::with_capacity(value.len());
        for &b in value.iter() {
            let n = if b { QM31::one() } else { QM31::zero() };
            let bit = cs.new_qm31(n, mode);
            variables.push(bit);

            if mode == AllocationMode::Witness {
                let minus_one = M31Var::new_constant(cs, &M31::one().neg());
                let bit_minus_one = cs.add(bit, minus_one.variable);
                cs.insert_gate(bit, bit_minus_one, 0, M31::zero());
            }
        }

        Self {
            cs: cs.clone(),
            value: value.clone(),
            variables,
        }
    }
}

impl BitsVar {
    pub fn from_m31(v: &M31Var, l: usize) -> BitsVar {
        let cs = v.cs();
        let mut bools = Vec::with_capacity(l);

        let mut cur = v.value.0;
        for _ in 0..l {
            bools.push(cur & 1 != 0);
            cur >>= 1;
        }

        let res = BitsVar::new_witness(&cs, &bools);

        let cast_into_m31var = |b: bool, v: usize| M31Var {
            cs: cs.clone(),
            value: if b { M31::one() } else { M31::zero() },
            variable: v,
        };

        let mut reconstructed = cast_into_m31var(res.value[0], res.variables[0]);
        for i in 1..l {
            reconstructed = &reconstructed
                + &cast_into_m31var(res.value[i], res.variables[i]).mul_constant(M31::from(1 << i));
        }
        reconstructed.equalverify(v);

        if l == 31 {
            let mut product = cs.mul(res.variables[0], res.variables[1]);
            for i in 2..l {
                product = cs.mul(product, res.variables[i]);
            }
            cs.enforce_zero(product);
        }

        res
    }

    pub fn get_value(&self) -> M31 {
        let mut sum_value = M31::zero();

        for (shift, &i) in self.value.iter().enumerate() {
            if i {
                sum_value += M31::from(1 << shift);
            }
        }

        sum_value
    }

    pub fn compose_range(&self, range: Range<usize>) -> M31Var {
        let cs = self.cs();

        let mut sum_value = if self.value[range.start] {
            M31::one()
        } else {
            M31::zero()
        };
        let mut sum_variable = self.variables[range.start];

        for (shift, i) in (range.start + 1..range.end).enumerate() {
            if self.value[i] {
                sum_value += M31::from(1 << (shift + 1));
            }
            let shifted_variable = cs.mul_constant(self.variables[i], M31::from(1 << (shift + 1)));
            sum_variable = cs.add(sum_variable, shifted_variable);
        }

        M31Var {
            cs,
            value: sum_value,
            variable: sum_variable,
        }
    }
}

impl BitsVar {
    pub fn index_range(&self, range: Range<usize>) -> BitsVar {
        BitsVar {
            cs: self.cs.clone(),
            value: self.value[range.clone()].to_vec(),
            variables: self.variables[range].to_vec(),
        }
    }

    pub fn index_range_from(&self, range: RangeFrom<usize>) -> BitsVar {
        BitsVar {
            cs: self.cs.clone(),
            value: self.value[range.clone()].to_vec(),
            variables: self.variables[range].to_vec(),
        }
    }
}
