use crate::parameters::{
    FIRST_FOUR_ROUND_RC, LAST_FOUR_ROUNDS_RC, MAT_DIAG16_M_1, PARTIAL_ROUNDS_RC,
};
use crate::{IsSwap, Poseidon2HalfEmulatedVar};
use circle_plonk_dsl_constraint_system::dvar::{AllocVar, DVar};
use circle_plonk_dsl_constraint_system::ConstraintSystemRef;
use circle_plonk_dsl_fields::{M31Var, QM31Var};
use num_traits::{One, Zero};
use stwo_prover::core::fields::m31::M31;
use stwo_prover::core::fields::qm31::QM31;

pub fn apply_4x4_mds_matrix(x: &QM31Var) -> QM31Var {
    let cs = x.cs();
    let constant = QM31Var::new_constant(&cs, &QM31::from_u32_unchecked(1, 1, 1, 1));
    let variable = cs.do_m4_gate(x.variable, constant.variable);
    let value = cs.get_value(variable);
    QM31Var {
        cs,
        value,
        variable,
    }
}

pub fn apply_16x16_mds_matrix(state: [QM31Var; 4]) -> [QM31Var; 4] {
    let p1 = apply_4x4_mds_matrix(&state[0]);
    let p2 = apply_4x4_mds_matrix(&state[1]);
    let p3 = apply_4x4_mds_matrix(&state[2]);
    let p4 = apply_4x4_mds_matrix(&state[3]);

    let mut t = &p1 + &p2;
    t = &t + &p3;
    t = &t + &p4;

    [&p1 + &t, &p2 + &t, &p3 + &t, &p4 + &t]
}

pub fn pow5m4(x: &QM31Var) -> QM31Var {
    let value = x.value;
    let x0 = value.0 .0;
    let x1 = value.0 .1;
    let x2 = value.1 .0;
    let x3 = value.1 .1;

    let cs = x.cs();

    let b = QM31::from_m31(
        x0 * x0 * x0 * x0,
        x1 * x1 * x1 * x1,
        x2 * x2 * x2 * x2,
        x3 * x3 * x3 * x3,
    );
    let b_var = QM31Var::new_witness(&cs, &b);

    let variable = cs.do_pow5m4_gate(x.variable, b_var.variable);
    let value = cs.get_value(variable);
    QM31Var {
        cs,
        value,
        variable,
    }
}

pub fn pow5(cs: &ConstraintSystemRef, variable: usize) -> usize {
    let value = cs.get_value(variable);
    let x0 = value.0 .0;
    let x1 = value.0 .1;
    let x2 = value.1 .0;
    let x3 = value.1 .1;

    let b = QM31::from_m31(
        x0 * x0 * x0 * x0,
        x1 * x1 * x1 * x1,
        x2 * x2 * x2 * x2,
        x3 * x3 * x3 * x3,
    );
    let b_var = QM31Var::new_witness(&cs, &b);
    cs.do_pow5_gate(variable, b_var.variable)
}

pub fn poseidon_permute_emulated(
    left: &Poseidon2HalfEmulatedVar,
    right: &Poseidon2HalfEmulatedVar,
    is_swap: IsSwap,
) -> (Poseidon2HalfEmulatedVar, Poseidon2HalfEmulatedVar) {
    let cs = left.cs.and(&right.cs);

    let (left_elems, right_elems) = if let Some((bit_value, bit_variable)) = is_swap {
        // (right - left) * bit + left
        let right_minus_left: [QM31Var; 2] =
            std::array::from_fn(|i| &right.elems[i] - &left.elems[i]);
        let bit_var = M31Var {
            cs: cs.clone(),
            value: if bit_value { M31::one() } else { M31::zero() },
            variable: bit_variable,
        };
        let right_minus_left_times_bit: [QM31Var; 2] =
            std::array::from_fn(|i| &right_minus_left[i] * &bit_var);

        let new_left: [QM31Var; 2] =
            std::array::from_fn(|i| &right_minus_left_times_bit[i] + &left.elems[i]);
        let new_right: [QM31Var; 2] =
            std::array::from_fn(|i| &right.elems[i] - &right_minus_left_times_bit[i]);
        (new_left, new_right)
    } else {
        (left.elems.clone(), right.elems.clone())
    };

    let mut state: [QM31Var; 4] = [
        left_elems[0].clone(),
        left_elems[1].clone(),
        right_elems[0].clone(),
        right_elems[1].clone(),
    ];
    state = apply_16x16_mds_matrix(state);

    for r in 0..4 {
        for i in 0..4 {
            state[i] = &state[i]
                + &QM31Var::new_constant(
                    &cs,
                    &QM31::from_m31(
                        FIRST_FOUR_ROUND_RC[r][i * 4],
                        FIRST_FOUR_ROUND_RC[r][i * 4 + 1],
                        FIRST_FOUR_ROUND_RC[r][i * 4 + 2],
                        FIRST_FOUR_ROUND_RC[r][i * 4 + 3],
                    ),
                );
        }
        for i in 0..4 {
            state[i] = pow5m4(&state[i]);
        }
        let mut t = &state[0] + &state[1];
        t = &t + &state[2];
        t = &t + &state[3];
        state = [
            &state[0] + &t,
            &state[1] + &t,
            &state[2] + &t,
            &state[3] + &t,
        ];
    }

    for r in 0..14 {
        let mut first_limb_with_first_only = cs.do_hadamard(state[0].variable, 1);

        let constant = QM31Var::new_constant(&cs, &QM31::from_u32_unchecked(0, 1, 1, 1));
        let first_limb_without_first = cs.do_hadamard(state[0].variable, constant.variable);

        let constant = M31Var::new_constant(&cs, &PARTIAL_ROUNDS_RC[r]);
        first_limb_with_first_only = cs.add(first_limb_with_first_only, constant.variable);
        first_limb_with_first_only = pow5(&cs, first_limb_with_first_only);
        let tmp = cs.add(first_limb_with_first_only, first_limb_without_first);
        state[0] = QM31Var {
            cs: cs.clone(),
            value: cs.get_value(tmp),
            variable: tmp,
        };

        let sum_1 = cs.do_grandsum_gate(state[0].variable, state[1].variable);
        let sum_2 = cs.do_grandsum_gate(state[2].variable, state[3].variable);
        let sum = cs.add(sum_1, sum_2);

        for i in 0..4 {
            let constant = QM31Var::new_constant(
                &cs,
                &QM31::from_m31_array([
                    MAT_DIAG16_M_1[i * 4],
                    MAT_DIAG16_M_1[i * 4 + 1],
                    MAT_DIAG16_M_1[i * 4 + 2],
                    MAT_DIAG16_M_1[i * 4 + 3],
                ]),
            );
            let mut v = cs.do_hadamard(state[i].variable, constant.variable);
            v = cs.add(sum, v);

            state[i] = QM31Var {
                cs: cs.clone(),
                value: cs.get_value(v),
                variable: v,
            }
        }
    }

    for r in 0..4 {
        for i in 0..4 {
            state[i] = &state[i]
                + &QM31Var::new_constant(
                    &cs,
                    &QM31::from_m31(
                        LAST_FOUR_ROUNDS_RC[r][i * 4],
                        LAST_FOUR_ROUNDS_RC[r][i * 4 + 1],
                        LAST_FOUR_ROUNDS_RC[r][i * 4 + 2],
                        LAST_FOUR_ROUNDS_RC[r][i * 4 + 3],
                    ),
                );
        }
        for i in 0..4 {
            state[i] = pow5m4(&state[i]);
        }
        let mut t = &state[0] + &state[1];
        t = &t + &state[2];
        t = &t + &state[3];
        state = [
            &state[0] + &t,
            &state[1] + &t,
            &state[2] + &t,
            &state[3] + &t,
        ];
    }

    let out_left = Poseidon2HalfEmulatedVar {
        cs: cs.clone(),
        elems: [state[0].clone(), state[1].clone()],
    };
    let out_right = Poseidon2HalfEmulatedVar {
        cs,
        elems: [state[2].clone(), state[3].clone()],
    };

    (out_left, out_right)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Poseidon2HalfVar;
    use circle_plonk_dsl_constraint_system::ConstraintSystemRef;
    use stwo_prover::core::fri::FriConfig;
    use stwo_prover::core::pcs::PcsConfig;
    use stwo_prover::core::vcs::poseidon31_merkle::Poseidon31MerkleChannel;
    use stwo_prover::examples::plonk_without_poseidon::air::{
        prove_plonk_without_poseidon, verify_plonk_without_poseidon,
    };

    #[test]
    fn test_poseidon2_emulated_permute() {
        let cs = ConstraintSystemRef::new_plonk_without_poseidon_ref();

        let left: [M31Var; 8] = std::array::from_fn(|i| M31Var::new_witness(&cs, &M31::from(i)));
        let right: [M31Var; 8] =
            std::array::from_fn(|i| M31Var::new_witness(&cs, &M31::from(i + 8)));

        let left = Poseidon2HalfVar::from_m31(&left);
        let right = Poseidon2HalfVar::from_m31(&right);

        let check_result = |result: (Poseidon2HalfVar, Poseidon2HalfVar)| {
            let result_left = result.0.value();
            let result_right = result.1.value();

            let state: [u32; 16] = std::array::from_fn(|i| {
                if i < 8 {
                    result_left[i].0
                } else {
                    result_right[i - 8].0
                }
            });

            assert_eq!(
                state,
                [
                    260776483, 1182896747, 1656699352, 746018898, 102875940, 1812541025, 515874083,
                    755063943, 1682438524, 1265420601, 238640995, 200799880, 1659717477,
                    2080202267, 1269806256, 1287849264
                ]
            );
        };

        let result = Poseidon2HalfVar::permute(&left, &right, false, false, None);
        check_result(result);

        let result = Poseidon2HalfVar::permute(&left, &right, false, false, Some((false, 0)));
        check_result(result);

        let result = Poseidon2HalfVar::permute(&right, &left, false, false, Some((true, 1)));
        check_result(result);

        cs.pad();
        cs.check_arithmetics();
        cs.populate_logup_arguments();

        let config = PcsConfig {
            pow_bits: 20,
            fri_config: FriConfig::new(0, 5, 16),
        };

        let circuit = cs.generate_plonk_without_poseidon_circuit();
        let proof = prove_plonk_without_poseidon::<Poseidon31MerkleChannel>(config, &circuit);
        verify_plonk_without_poseidon::<Poseidon31MerkleChannel>(
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
