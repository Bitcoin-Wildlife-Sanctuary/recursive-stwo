use crate::data_structures::{EvalAtRowVar, RelationEntryVar};
use circle_plonk_dsl_constraint_system::var::Var;
use circle_plonk_dsl_data_structures::LookupElementsVar;
use circle_plonk_dsl_fields::QM31Var;
use stwo::core::fields::m31::M31;
use stwo_examples::plonk_with_poseidon::poseidon::Poseidon;

const N_STATE: usize = 16;

#[inline(always)]
/// Applies the M4 MDS matrix described in <https://eprint.iacr.org/2023/323.pdf> 5.1.
fn apply_m4(x: [QM31Var; 4]) -> [QM31Var; 4] {
    let t0 = &x[0] + &x[1];
    let t02 = &t0 + &t0;
    let t1 = &x[2] + &x[3];
    let t12 = &t1 + &t1;
    let t2 = &(&x[1] + &x[1]) + &t1;
    let t3 = &(&x[3] + &x[3]) + &t0;
    let t4 = &(&t12 + &t12) + &t3;
    let t5 = &(&t02 + &t02) + &t2;
    let t6 = &t3 + &t5;
    let t7 = &t2 + &t4;
    [t6, t5, t7, t4]
}

/// Applies the external round matrix.
/// See <https://eprint.iacr.org/2023/323.pdf> 5.1 and Appendix B.
fn apply_external_round_matrix(state: &mut [QM31Var; 16]) {
    // Applies circ(2M4, M4, M4, M4).
    for i in 0..4 {
        [
            state[4 * i],
            state[4 * i + 1],
            state[4 * i + 2],
            state[4 * i + 3],
        ] = apply_m4([
            state[4 * i].clone(),
            state[4 * i + 1].clone(),
            state[4 * i + 2].clone(),
            state[4 * i + 3].clone(),
        ]);
    }
    for j in 0..4 {
        let s = &(&(&state[j] + &state[j + 4]) + &state[j + 8]) + &state[j + 12];
        for i in 0..4 {
            state[4 * i + j] = &state[4 * i + j] + &s;
        }
    }
}

// Applies the internal round matrix.
//   mu_i = 2^{i+1} + 1.
// See <https://eprint.iacr.org/2023/323.pdf> 5.2.
fn apply_internal_round_matrix(state: &mut [QM31Var; 16]) {
    let sum = state[1..]
        .iter()
        .cloned()
        .fold(state[0].clone(), |acc, s| &acc + &s);

    state[0] = &state[0] + &(&(&state[0] + &state[0]) + &sum);
    state.iter_mut().enumerate().skip(1).for_each(|(i, s)| {
        // TODO(andrew): Change to rotations.
        *s = &s.mul_constant_m31(M31::from_u32_unchecked(1 << (i + 1))) + &sum;
    });
}

fn pow5(x: QM31Var) -> QM31Var {
    let x2 = &x * &x;
    let x4 = &x2 * &x2;
    &x4 * &x
}

pub fn evaluate_poseidon<'a>(
    lookup_elements: &LookupElementsVar,
    mut eval: EvalAtRowVar<'a>,
) -> EvalAtRowVar<'a> {
    let cs = lookup_elements.cs();

    let is_first_round =
        eval.get_preprocessed_column(Poseidon::new("is_first_round".to_string()).id());
    let is_last_round =
        eval.get_preprocessed_column(Poseidon::new("is_last_round".to_string()).id());
    let is_full_round =
        eval.get_preprocessed_column(Poseidon::new("is_full_round".to_string()).id());

    let one = QM31Var::one(&cs);

    let is_not_first_round = &one - &is_first_round;
    let is_not_last_round = &one - &is_last_round;
    let is_partial_round = &is_not_first_round - &is_full_round;

    let round_id = eval.get_preprocessed_column(Poseidon::new("round_id".to_string()).id());

    let mut rc0 = vec![];
    for i in 0..16 {
        rc0.push(
            eval.get_preprocessed_column(Poseidon::new(format!("rc0 {}", i).to_string()).id()),
        );
    }
    let mut rc1 = vec![];
    for i in 0..16 {
        rc1.push(
            eval.get_preprocessed_column(Poseidon::new(format!("rc1 {}", i).to_string()).id()),
        );
    }

    let external_idx_1 =
        eval.get_preprocessed_column(Poseidon::new("external_idx_1".to_string()).id());
    let external_idx_2 =
        eval.get_preprocessed_column(Poseidon::new("external_idx_2".to_string()).id());
    let is_external_idx_1_nonzero =
        eval.get_preprocessed_column(Poseidon::new("is_external_idx_1_nonzero".to_string()).id());
    let is_external_idx_2_nonzero =
        eval.get_preprocessed_column(Poseidon::new("is_external_idx_2_nonzero".to_string()).id());

    let swap_bit_addr = rc0[0].clone();

    let in_state: [_; N_STATE] = std::array::from_fn(|_| eval.next_trace_mask());
    let intermediate_state: [_; N_STATE] = std::array::from_fn(|_| eval.next_trace_mask());
    let out_state: [_; N_STATE] = std::array::from_fn(|_| eval.next_trace_mask());
    let swap_bit_value = intermediate_state[0].clone();

    // if this is first round
    let one_minus_swap_bit_value = &one - &swap_bit_value;
    let mut permuted_state: [_; N_STATE] = std::array::from_fn(|i| {
        if i < 8 {
            &(&in_state[i] * &one_minus_swap_bit_value) + &(&in_state[i + 8] * &swap_bit_value)
        } else {
            &(&in_state[i - 8] * &swap_bit_value) + &(&in_state[i] * &one_minus_swap_bit_value)
        }
    });
    apply_external_round_matrix(&mut permuted_state);
    (0..N_STATE).for_each(|i| {
        eval.add_constraint(&is_first_round * &(&permuted_state[i] - &out_state[i]));
    });

    // if this is a full round
    let mut full_round_state = in_state.clone();
    (0..N_STATE).for_each(|i| {
        full_round_state[i] = &full_round_state[i] + &rc0[i];
    });
    full_round_state = std::array::from_fn(|i| pow5(full_round_state[i].clone()));
    (0..N_STATE).for_each(|i| {
        eval.add_constraint(&is_full_round * &(&intermediate_state[i] - &full_round_state[i]));
        full_round_state[i] = intermediate_state[i].clone();
    });
    apply_external_round_matrix(&mut full_round_state);
    (0..N_STATE).for_each(|i| {
        full_round_state[i] = &full_round_state[i] + &rc1[i];
    });
    full_round_state = std::array::from_fn(|i| pow5(full_round_state[i].clone()));
    apply_external_round_matrix(&mut full_round_state);
    (0..N_STATE).for_each(|i| {
        eval.add_constraint(&is_full_round * &(&out_state[i] - &full_round_state[i]));
    });

    // if this is a partial round
    let mut partial_round_state = in_state.clone();
    for r in 0..14 {
        partial_round_state[0] = &partial_round_state[0] + &rc0[r];
        partial_round_state[0] = pow5(partial_round_state[0].clone());
        eval.add_constraint(
            &is_partial_round * &(&intermediate_state[r] - &partial_round_state[0]),
        );
        partial_round_state[0] = intermediate_state[r].clone();
        apply_internal_round_matrix(&mut partial_round_state);
    }
    (0..N_STATE).for_each(|i| {
        eval.add_constraint(&is_partial_round * &(&out_state[i] - &partial_round_state[i]));
    });

    // in_state with id
    let in_left_id = &round_id + &round_id;
    let in_right_id = &in_left_id + &one;
    let out_left_id = &in_right_id + &one;
    let out_right_id = &out_left_id + &one;

    let sel = &is_external_idx_1_nonzero * &is_first_round;
    let id = &(&is_first_round * &external_idx_1) + &(&is_not_first_round * &in_left_id);

    let a = &(&(&in_state[0] + &in_state[1].shift_by_i()) + &in_state[2].shift_by_j())
        + &in_state[3].shift_by_ij();
    let b = &(&(&in_state[4] + &in_state[5].shift_by_i()) + &in_state[6].shift_by_j())
        + &in_state[7].shift_by_ij();

    eval.add_to_relation(RelationEntryVar::new(
        lookup_elements,
        &sel - &is_not_first_round,
        &[id, a, b],
    ));

    let sel = &is_external_idx_2_nonzero * &is_first_round;
    let id = &(&is_first_round * &external_idx_2) + &(&is_not_first_round * &in_right_id);

    let a = &(&(&in_state[8] + &in_state[9].shift_by_i()) + &in_state[10].shift_by_j())
        + &in_state[11].shift_by_ij();
    let b = &(&(&in_state[12] + &in_state[13].shift_by_i()) + &in_state[14].shift_by_j())
        + &in_state[15].shift_by_ij();

    eval.add_to_relation(RelationEntryVar::new(
        lookup_elements,
        &sel - &is_not_first_round,
        &[id, a, b],
    ));

    let sel = &is_external_idx_1_nonzero * &is_last_round;
    let id = &(&is_last_round * &external_idx_1) + &(&is_not_last_round * &out_left_id);

    let a = &(&(&out_state[0] + &out_state[1].shift_by_i()) + &out_state[2].shift_by_j())
        + &out_state[3].shift_by_ij();
    let b = &(&(&out_state[4] + &out_state[5].shift_by_i()) + &out_state[6].shift_by_j())
        + &out_state[7].shift_by_ij();

    eval.add_to_relation(RelationEntryVar::new(
        lookup_elements,
        &sel.clone() + &is_not_last_round,
        &[id.clone(), a, b],
    ));

    let sel = &is_external_idx_2_nonzero * &is_last_round;
    let id = &(&is_last_round * &external_idx_2) + &(&is_not_last_round * &out_right_id);

    let a = &(&(&out_state[8] + &out_state[9].shift_by_i()) + &out_state[10].shift_by_j())
        + &out_state[11].shift_by_ij();
    let b = &(&(&out_state[12] + &out_state[13].shift_by_i()) + &out_state[14].shift_by_j())
        + &out_state[15].shift_by_ij();

    eval.add_to_relation(RelationEntryVar::new(
        lookup_elements,
        &sel + &is_not_last_round,
        &[id.clone(), a, b],
    ));
    eval.add_to_relation(RelationEntryVar::new(
        lookup_elements,
        &is_first_round * &is_not_last_round,
        &[swap_bit_value, swap_bit_addr],
    ));

    eval.finalize_logup(3);
    eval
}
