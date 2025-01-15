use crate::parameters::{
    FIRST_FOUR_ROUND_RC, LAST_FOUR_ROUNDS_RC, MAT_DIAG16_M_1, PARTIAL_ROUNDS_RC,
};
use stwo_prover::core::fields::m31::M31;
use stwo_prover::core::fields::Field;

pub fn apply_4x4_mds_matrix(x0: M31, x1: M31, x2: M31, x3: M31) -> (M31, M31, M31, M31) {
    let t0 = x0 + x1;
    let t1 = x2 + x3;
    let t2 = x1.double() + t1;
    let t3 = x3.double() + t0;
    let t4 = t1.double().double() + t3;
    let t5 = t0.double().double() + t2;
    let t6 = t3 + t5;
    let t7 = t2 + t4;

    (t6, t5, t7, t4)
}

pub fn apply_16x16_mds_matrix(state: [M31; 16]) -> [M31; 16] {
    let p1 = apply_4x4_mds_matrix(state[0], state[1], state[2], state[3]);
    let p2 = apply_4x4_mds_matrix(state[4], state[5], state[6], state[7]);
    let p3 = apply_4x4_mds_matrix(state[8], state[9], state[10], state[11]);
    let p4 = apply_4x4_mds_matrix(state[12], state[13], state[14], state[15]);

    let t = [
        p1.0, p1.1, p1.2, p1.3, p2.0, p2.1, p2.2, p2.3, p3.0, p3.1, p3.2, p3.3, p4.0, p4.1, p4.2,
        p4.3,
    ];

    let mut state = t.clone();
    for i in 0..16 {
        state[i] = state[i].double();
    }

    for i in 0..4 {
        state[i] += t[i + 4];
        state[i] += t[i + 8];
        state[i] += t[i + 12];
    }
    for i in 4..8 {
        state[i] += t[i - 4];
        state[i] += t[i + 4];
        state[i] += t[i + 8];
    }
    for i in 8..12 {
        state[i] += t[i - 8];
        state[i] += t[i - 4];
        state[i] += t[i + 4];
    }
    for i in 12..16 {
        state[i] += t[i - 12];
        state[i] += t[i - 8];
        state[i] += t[i - 4];
    }

    state
}

pub fn from_u32_array(state: [u32; 16]) -> [M31; 16] {
    [
        M31::from(state[0]),
        M31::from(state[1]),
        M31::from(state[2]),
        M31::from(state[3]),
        M31::from(state[4]),
        M31::from(state[5]),
        M31::from(state[6]),
        M31::from(state[7]),
        M31::from(state[8]),
        M31::from(state[9]),
        M31::from(state[10]),
        M31::from(state[11]),
        M31::from(state[12]),
        M31::from(state[13]),
        M31::from(state[14]),
        M31::from(state[15]),
    ]
}

pub fn to_u32_array(state: [M31; 16]) -> [u32; 16] {
    [
        state[0].0,
        state[1].0,
        state[2].0,
        state[3].0,
        state[4].0,
        state[5].0,
        state[6].0,
        state[7].0,
        state[8].0,
        state[9].0,
        state[10].0,
        state[11].0,
        state[12].0,
        state[13].0,
        state[14].0,
        state[15].0,
    ]
}

#[inline(always)]
pub fn pow5(a: M31) -> M31 {
    let b = a * a;
    b * b * a
}

pub fn poseidon2_permute(p_state: &mut [M31; 16]) {
    let mut state = p_state.clone();
    state = apply_16x16_mds_matrix(state);

    for r in 0..4 {
        for i in 0..16 {
            state[i] += FIRST_FOUR_ROUND_RC[r][i];
        }
        for i in 0..16 {
            state[i] = pow5(state[i]);
        }

        state = apply_16x16_mds_matrix(state);
    }

    for r in 0..14 {
        state[0] += PARTIAL_ROUNDS_RC[r];
        state[0] = pow5(state[0]);

        let mut sum = state[0];
        for i in 1..16 {
            sum += state[i];
        }

        for i in 0..16 {
            state[i] = sum + state[i] * MAT_DIAG16_M_1[i];
        }
    }

    for r in 0..4 {
        for i in 0..16 {
            state[i] += LAST_FOUR_ROUNDS_RC[r][i];
        }
        for i in 0..16 {
            state[i] = pow5(state[i]);
        }

        state = apply_16x16_mds_matrix(state);
    }

    *p_state = state;
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_traits::Zero;

    #[test]
    fn test_poseidon2_permute() {
        let mut state = [M31::zero(); 16];
        for i in 0..16 {
            state[i] = M31::from(i);
        }

        poseidon2_permute(&mut state);

        assert_eq!(
            to_u32_array(state),
            [
                260776483, 1182896747, 1656699352, 746018898, 102875940, 1812541025, 515874083,
                755063943, 1682438524, 1265420601, 238640995, 200799880, 1659717477, 2080202267,
                1269806256, 1287849264
            ]
        );
    }
}
