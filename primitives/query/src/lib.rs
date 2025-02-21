use circle_plonk_dsl_bits::BitsVar;
use circle_plonk_dsl_circle::CirclePointM31Var;
use circle_plonk_dsl_constraint_system::dvar::{AllocVar, DVar};
use circle_plonk_dsl_fields::M31Var;
use itertools::Itertools;
use num_traits::One;
use std::collections::BTreeMap;
use std::ops::{Index, Neg, RangeInclusive};
use stwo_prover::core::circle::CirclePoint;
use stwo_prover::core::fields::m31::M31;
use stwo_prover::core::poly::circle::CanonicCoset;

pub struct QueryPositionsPerLogSize {
    pub range: RangeInclusive<u32>,
    pub points: BTreeMap<u32, Vec<PointCarryingQuery>>,
}

impl QueryPositionsPerLogSize {
    pub fn new(range: RangeInclusive<u32>, raw_queries: &[M31Var]) -> Self {
        let max_degree = *range.end();
        let min_degree = *range.start();

        let mut elems = vec![];
        for raw_query in raw_queries {
            elems.push(PointCarryingQuery::new(
                BitsVar::from_m31(&raw_query, 31).index_range(0..max_degree as usize),
            ));
        }
        let mut points = BTreeMap::new();
        points.insert(max_degree, elems.clone());

        for log_size in (min_degree..max_degree).rev() {
            elems.iter_mut().for_each(|e| e.next());
            points.insert(log_size, elems.clone());
        }

        Self { range, points }
    }
}

impl Index<u32> for QueryPositionsPerLogSize {
    type Output = Vec<PointCarryingQuery>;

    fn index(&self, index: u32) -> &Self::Output {
        self.points.get(&index).unwrap()
    }
}

#[derive(Clone)]
pub struct PointCarryingQuery {
    pub bits: BitsVar,
    pub last_step: CirclePoint<M31>,
    pub point: CirclePointM31Var,
}

impl PointCarryingQuery {
    pub fn new(bits: BitsVar) -> Self {
        let cs = bits.cs();
        let log_size = bits.value.len() as u32;
        let coset = CanonicCoset::new(log_size + 1).circle_domain().half_coset;

        let initial = coset.initial;
        let step = coset.step;

        let mut steps = Vec::with_capacity((log_size - 1) as usize);
        let mut cur = step;
        for _ in 0..log_size - 1 {
            steps.push(cur);
            cur = cur.double();
        }

        let combs = steps
            .iter()
            .zip(bits.value[1..].iter().rev())
            .zip(bits.variables[1..].iter().rev())
            .collect_vec();

        let mut cur = CirclePointM31Var::new_constant(&cs, &initial);
        for chunk in combs.chunks(2) {
            if chunk.len() == 1 {
                let point =
                    CirclePointM31Var::select(&cs, chunk[0].0 .0, *chunk[0].0 .1, *chunk[0].1);
                cur = &point + &cur;
            } else {
                let p00 = CirclePoint::<M31>::zero();
                let p01 = chunk[0].0 .0.clone();
                let p10 = chunk[1].0 .0.clone();
                let p11 = p01 + p10;

                let value = match (*chunk[0].0 .1, *chunk[1].0 .1) {
                    (false, false) => p00,
                    (true, false) => p01,
                    (false, true) => p10,
                    (true, true) => p11,
                };

                let a = *chunk[0].1;
                let b = *chunk[1].1;
                let one_minus_a = cs.add(1, cs.mul_constant(a, M31::one().neg()));
                let one_minus_b = cs.add(1, cs.mul_constant(b, M31::one().neg()));

                let b00 = cs.mul(one_minus_a, one_minus_b);
                let b01 = cs.mul(a, one_minus_b);
                let b10 = cs.mul(one_minus_a, b);
                let b11 = cs.mul(a, b);

                let mut x = cs.mul_constant(b00, p00.x);
                x = cs.add(x, cs.mul_constant(b01, p01.x));
                x = cs.add(x, cs.mul_constant(b10, p10.x));
                x = cs.add(x, cs.mul_constant(b11, p11.x));

                let mut y = cs.mul_constant(b00, p00.y);
                y = cs.add(y, cs.mul_constant(b01, p01.y));
                y = cs.add(y, cs.mul_constant(b10, p10.y));
                y = cs.add(y, cs.mul_constant(b11, p11.y));

                let point = CirclePointM31Var {
                    x: M31Var {
                        cs: cs.clone(),
                        value: value.x,
                        variable: x,
                    },
                    y: M31Var {
                        cs: cs.clone(),
                        value: value.y,
                        variable: y,
                    },
                };
                cur = &point + &cur;
            }
        }

        PointCarryingQuery {
            bits,
            last_step: steps.last().unwrap().neg(),
            point: cur,
        }
    }

    pub fn get_point(&self) -> CirclePointM31Var {
        self.point
            .double()
            .conditional_negate(self.bits.value[0], self.bits.variables[0])
    }

    pub fn next(&mut self) {
        assert!(self.bits.value.len() > 1);

        let cs = self.bits.cs();
        let target_bit_value = self.bits.value[1];
        let target_bit_variable = self.bits.variables[1];

        let t =
            CirclePointM31Var::select(&cs, &self.last_step, target_bit_value, target_bit_variable);

        self.bits = self.bits.index_range_from(1..);
        self.point = (&self.point + &t).double();
    }

    pub fn get_absolute_point(&self) -> CirclePointM31Var {
        self.point.clone()
    }
}

#[cfg(test)]
mod tests {
    use crate::PointCarryingQuery;
    use circle_plonk_dsl_bits::BitsVar;
    use circle_plonk_dsl_constraint_system::dvar::AllocVar;
    use circle_plonk_dsl_constraint_system::ConstraintSystemRef;
    use circle_plonk_dsl_fields::M31Var;
    use stwo_prover::core::fields::m31::M31;
    use stwo_prover::core::poly::circle::CanonicCoset;
    use stwo_prover::core::utils::bit_reverse_index;

    #[test]
    fn test_point_carrying_query() {
        let coset = CanonicCoset::new(16).circle_domain();

        let a = coset.at(bit_reverse_index(82, 16));
        let b = coset.at(bit_reverse_index(83, 16));

        let cs = ConstraintSystemRef::new_ref();

        let a_index = M31Var::new_witness(&cs, &M31::from(82));
        let b_index = M31Var::new_witness(&cs, &M31::from(83));

        let a_bits = BitsVar::from_m31(&a_index, 16);
        let b_bits = BitsVar::from_m31(&b_index, 16);

        let mut a_query = PointCarryingQuery::new(a_bits);
        let mut b_query = PointCarryingQuery::new(b_bits);
        let a_point = a_query.get_point();
        let b_point = b_query.get_point();
        let b_point_abs = b_query.get_absolute_point();

        assert_eq!(a.x, a_point.x.value);
        assert_eq!(a.y, a_point.y.value);
        assert_eq!(a.x, b_point_abs.x.value);
        assert_eq!(a.y, b_point_abs.y.value);
        assert_eq!(b.x, b_point.x.value);
        assert_eq!(b.y, b_point.y.value);

        let coset = CanonicCoset::new(15).circle_domain();

        let a = coset.at(bit_reverse_index(40, 15));

        a_query.next();
        b_query.next();

        let a_point = a_query.get_absolute_point();
        let b_point = b_query.get_absolute_point();
        assert_eq!(a.x, a_point.x.value);
        assert_eq!(a.y, a_point.y.value);
        assert_eq!(a.x, b_point.x.value);
        assert_eq!(a.y, b_point.y.value);
    }
}
