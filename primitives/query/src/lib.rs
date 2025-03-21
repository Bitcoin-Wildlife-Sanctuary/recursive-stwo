use circle_plonk_dsl_bits::BitsVar;
use circle_plonk_dsl_circle::CirclePointM31Var;
use circle_plonk_dsl_constraint_system::var::{AllocVar, Var};
use circle_plonk_dsl_fields::M31Var;
use itertools::Itertools;
use num_traits::One;
use std::collections::BTreeMap;
use std::ops::{Index, Neg, RangeInclusive};
use stwo_prover::core::circle::CirclePoint;
use stwo_prover::core::fields::m31::M31;
use stwo_prover::core::poly::circle::CanonicCoset;

pub struct QueryPositionsPerLogSizeVar {
    pub range: RangeInclusive<u32>,
    pub points: BTreeMap<u32, Vec<PointCarryingQueryVar>>,
}

impl QueryPositionsPerLogSizeVar {
    pub fn new(range: RangeInclusive<u32>, raw_queries: &[M31Var]) -> Self {
        let max_degree = *range.end();
        let min_degree = *range.start();

        let mut elems = vec![];
        for raw_query in raw_queries {
            elems.push(PointCarryingQueryVar::new(
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

impl Index<u32> for QueryPositionsPerLogSizeVar {
    type Output = Vec<PointCarryingQueryVar>;

    fn index(&self, index: u32) -> &Self::Output {
        self.points.get(&index).unwrap()
    }
}

#[derive(Clone)]
pub struct PointCarryingQueryVar {
    pub bits: BitsVar,
    pub last_step: CirclePoint<M31>,
    pub point: CirclePointM31Var,
}

impl PointCarryingQueryVar {
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

        PointCarryingQueryVar {
            bits,
            last_step: steps.last().unwrap().neg(),
            point: cur,
        }
    }

    pub fn get_next_point(&self) -> CirclePointM31Var {
        self.point
            .double()
            .conditional_negate(self.bits.value[0], self.bits.variables[0])
    }

    pub fn get_next_point_x(&self) -> M31Var {
        let xx = &self.point.x * &self.point.x;
        let yy = &self.point.y * &self.point.y;
        &xx - &yy
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
