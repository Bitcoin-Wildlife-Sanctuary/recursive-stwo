use circle_plonk_dsl_bits::BitsVar;
use circle_plonk_dsl_channel::ChannelVar;
use circle_plonk_dsl_constraint_system::dvar::{AllocVar, AllocationMode, DVar};
use circle_plonk_dsl_constraint_system::ConstraintSystemRef;
use circle_plonk_dsl_fields::{M31Var, QM31Var};
use itertools::Itertools;
use num_traits::{One, Zero};
use std::ops::{Add, Neg};
use stwo_prover::core::circle::{CirclePoint, Coset};
use stwo_prover::core::fields::m31::{BaseField, M31};
use stwo_prover::core::fields::qm31::{SecureField, QM31};

#[derive(Clone, Debug)]
pub struct CirclePointM31Var {
    pub x: M31Var,
    pub y: M31Var,
}

impl CirclePointM31Var {
    pub fn value(&self) -> CirclePoint<M31> {
        CirclePoint::<M31> {
            x: self.x.value,
            y: self.y.value,
        }
    }
}

impl DVar for CirclePointM31Var {
    type Value = CirclePoint<BaseField>;

    fn cs(&self) -> ConstraintSystemRef {
        self.x.cs().and(&self.y.cs())
    }
}

impl AllocVar for CirclePointM31Var {
    fn new_variables(cs: &ConstraintSystemRef, value: &Self::Value, mode: AllocationMode) -> Self {
        let x = M31Var::new_variables(cs, &value.x, mode);
        let y = M31Var::new_variables(cs, &value.y, mode);
        Self { x, y }
    }
}

impl Add<&CirclePointM31Var> for &CirclePointM31Var {
    type Output = CirclePointM31Var;

    fn add(self, rhs: &CirclePointM31Var) -> Self::Output {
        let x1x2 = &self.x * &rhs.x;
        let y1y2 = &self.y * &rhs.y;
        let x1y2 = &self.x * &rhs.y;
        let y1x2 = &self.y * &rhs.x;

        let new_x = &x1x2 - &y1y2;
        let new_y = &x1y2 + &y1x2;

        CirclePointM31Var { x: new_x, y: new_y }
    }
}

impl CirclePointM31Var {
    pub fn double(&self) -> Self {
        let xx = &self.x * &self.x;
        let yy = &self.y * &self.y;
        let xy = &self.x * &self.y;

        let new_x = &xx - &yy;
        let new_y = xy.mul_constant(M31::from(2));

        CirclePointM31Var { x: new_x, y: new_y }
    }
}

impl CirclePointM31Var {
    pub fn select(
        cs: &ConstraintSystemRef,
        point: &CirclePoint<BaseField>,
        bit_value: bool,
        bit_variable: usize,
    ) -> Self {
        let value = if bit_value {
            *point
        } else {
            CirclePoint {
                x: M31::one(),
                y: M31::zero(),
            }
        };

        let mut new_x = cs.mul_constant(bit_variable, value.x - M31::one());
        new_x = cs.add(new_x, 1);

        let new_y = cs.mul_constant(bit_variable, value.y);

        Self {
            x: M31Var {
                cs: cs.clone(),
                value: value.x,
                variable: new_x,
            },
            y: M31Var {
                cs: cs.clone(),
                value: value.y,
                variable: new_y,
            },
        }
    }

    pub fn conditional_negate(&self, bit_value: bool, bit_variable: usize) -> Self {
        let cs = self.cs();

        let y_value = if bit_value {
            -self.y.value
        } else {
            self.y.value
        };

        // y_multiplier = 1 if bit = 0, or y_multiplier = -1 if bit = 1
        let mut y_multiplier = cs.mul_constant(bit_variable, M31::from(2).neg());
        y_multiplier = cs.add(y_multiplier, 1);

        let y_variable = cs.mul(y_multiplier, self.y.variable);

        Self {
            x: self.x.clone(),
            y: M31Var {
                cs,
                value: y_value,
                variable: y_variable,
            },
        }
    }
}

impl CirclePointM31Var {
    pub fn bit_reverse_at(coset: &Coset, bits_var: &BitsVar, log_size: u32) -> Self {
        assert_eq!(bits_var.value.len(), log_size as usize);
        let cs = bits_var.cs();

        let initial = coset.initial;
        let step = coset.step;

        let mut steps = Vec::with_capacity((log_size - 1) as usize);
        let mut cur = step;
        for _ in 0..log_size - 1 {
            steps.push(cur);
            cur = cur.double();
        }

        let mut steps_var = Vec::with_capacity(log_size as usize);
        for ((step, &bit_value), &bit_variable) in steps
            .iter()
            .zip_eq(bits_var.value.iter().skip(1).rev())
            .zip_eq(bits_var.variables.iter().skip(1).rev())
        {
            steps_var.push(CirclePointM31Var::select(
                &cs,
                step,
                bit_value,
                bit_variable,
            ));
        }

        let mut sum = CirclePointM31Var::new_constant(&cs, &initial);
        for step_var in steps_var.iter() {
            sum = &sum + &step_var;
        }
        sum = sum.conditional_negate(bits_var.value[0], bits_var.variables[0]);
        sum
    }
}

#[derive(Clone, Debug)]
pub struct CirclePointQM31Var {
    pub x: QM31Var,
    pub y: QM31Var,
}

impl CirclePointQM31Var {
    pub fn value(&self) -> CirclePoint<QM31> {
        CirclePoint::<QM31> {
            x: self.x.value,
            y: self.y.value,
        }
    }
}

impl DVar for CirclePointQM31Var {
    type Value = CirclePoint<SecureField>;

    fn cs(&self) -> ConstraintSystemRef {
        self.x.cs().and(&self.y.cs())
    }
}

impl AllocVar for CirclePointQM31Var {
    fn new_variables(cs: &ConstraintSystemRef, value: &Self::Value, mode: AllocationMode) -> Self {
        let x = QM31Var::new_variables(cs, &value.x, mode);
        let y = QM31Var::new_variables(cs, &value.y, mode);
        Self { x, y }
    }
}

impl CirclePointQM31Var {
    pub fn from_t(t: &QM31Var) -> Self {
        let cs = t.cs();

        let t_doubled = t + t;
        let t_squared = t * t;

        let t_squared_plus_1 = t_squared.add(&M31Var::one(&cs));
        let t_squared_plus_1_inverse = t_squared_plus_1.inv();

        let one_minus_t_squared_minus = t_squared.neg().add(&M31Var::one(&cs));

        let x = &one_minus_t_squared_minus * &t_squared_plus_1_inverse;
        let y = &t_doubled * &t_squared_plus_1_inverse;

        Self { x, y }
    }

    pub fn from_channel(channel: &mut ChannelVar) -> Self {
        let [t, _] = channel.get_felts();
        Self::from_t(&t)
    }
}

impl Add<&CirclePoint<M31>> for &CirclePointQM31Var {
    type Output = CirclePointQM31Var;

    fn add(self, rhs: &CirclePoint<M31>) -> Self::Output {
        let x1x2 = self.x.mul_constant_m31(rhs.x);
        let y1y2 = self.y.mul_constant_m31(rhs.y);
        let x1y2 = self.x.mul_constant_m31(rhs.y);
        let y1x2 = self.y.mul_constant_m31(rhs.x);

        let new_x = &x1x2 - &y1y2;
        let new_y = &x1y2 + &y1x2;

        CirclePointQM31Var { x: new_x, y: new_y }
    }
}

#[cfg(test)]
mod test {
    use crate::CirclePointM31Var;
    use circle_plonk_dsl_bits::BitsVar;
    use circle_plonk_dsl_constraint_system::dvar::AllocVar;
    use circle_plonk_dsl_constraint_system::ConstraintSystemRef;
    use circle_plonk_dsl_fields::M31Var;
    use stwo_prover::core::fields::m31::M31;
    use stwo_prover::core::poly::circle::CanonicCoset;
    use stwo_prover::core::utils::bit_reverse_index;

    #[test]
    fn test_bit_reverse_at() {
        let circle_domain = CanonicCoset::new(16).circle_domain();

        let a = circle_domain.at(bit_reverse_index(40, 16));
        let b = circle_domain.at(bit_reverse_index(41, 16));

        let cs = ConstraintSystemRef::new_ref();

        let a_index = M31Var::new_witness(&cs, &M31::from(40));
        let b_index = M31Var::new_witness(&cs, &M31::from(41));

        let a_bits = BitsVar::from_m31(&a_index, 16);
        let b_bits = BitsVar::from_m31(&b_index, 16);

        let a_point = CirclePointM31Var::bit_reverse_at(&circle_domain.half_coset, &a_bits, 16);
        let b_point = CirclePointM31Var::bit_reverse_at(&circle_domain.half_coset, &b_bits, 16);

        assert_eq!(a.x, a_point.x.value);
        assert_eq!(a.y, a_point.y.value);
        assert_eq!(b.x, b_point.x.value);
        assert_eq!(b.y, b_point.y.value);
    }
}
