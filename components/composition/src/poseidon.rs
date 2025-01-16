use crate::data_structures::{EvalAtRowVar, RelationEntryVar};
use circle_plonk_dsl_constraint_system::dvar::{AllocVar, DVar};
use circle_plonk_dsl_data_structures::PlonkWithAcceleratorLookupElementsVar;
use circle_plonk_dsl_fields::{M31Var, QM31Var};
use stwo_prover::constraint_framework::preprocessed_columns::PreprocessedColumn;
use stwo_prover::core::fields::m31::M31;
use stwo_prover::core::vcs::poseidon31_ref::{
    FIRST_FOUR_ROUND_RC, LAST_FOUR_ROUNDS_RC, PARTIAL_ROUNDS_RC,
};

const N_STATE: usize = 16;
const N_HALF_FULL_ROUNDS: usize = 4;
const N_PARTIAL_ROUNDS: usize = 14;

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
    lookup_elements: &PlonkWithAcceleratorLookupElementsVar,
    mut eval: EvalAtRowVar<'a>,
) -> EvalAtRowVar<'a> {
    let cs = lookup_elements.cs();

    let addr_1 = eval.get_preprocessed_column(PreprocessedColumn::Poseidon(0));
    let addr_2 = eval.get_preprocessed_column(PreprocessedColumn::Poseidon(1));
    let addr_3 = eval.get_preprocessed_column(PreprocessedColumn::Poseidon(2));
    let addr_4 = eval.get_preprocessed_column(PreprocessedColumn::Poseidon(3));

    let sel_1 = eval.next_trace_mask();
    let sel_2 = eval.next_trace_mask();
    let sel_3 = eval.next_trace_mask();
    let sel_4 = eval.next_trace_mask();

    let mut state: [_; 16] = std::array::from_fn(|_| eval.next_trace_mask());

    // Require state lookup.
    let initial_state = state.clone();

    apply_external_round_matrix(&mut state);

    // 4 full rounds.
    (0..N_HALF_FULL_ROUNDS).for_each(|round| {
        (0..N_STATE).for_each(|i| {
            state[i] = &state[i] + &M31Var::new_constant(&cs, &FIRST_FOUR_ROUND_RC[round][i]);
        });
        state = std::array::from_fn(|i| pow5(state[i].clone()));
        apply_external_round_matrix(&mut state);
        state.iter_mut().for_each(|s| {
            let m = eval.next_trace_mask();
            eval.add_constraint((s as &QM31Var) - &m);
            *s = m;
        });
    });

    // Partial rounds.
    (0..N_PARTIAL_ROUNDS).for_each(|round| {
        state[0] = &state[0] + &M31Var::new_constant(&cs, &PARTIAL_ROUNDS_RC[round]);
        state[0] = pow5(state[0].clone());

        let m = eval.next_trace_mask();
        eval.add_constraint(&state[0] - &m);
        state[0] = m;

        apply_internal_round_matrix(&mut state);
    });

    // 4 full rounds.
    (0..N_HALF_FULL_ROUNDS - 1).for_each(|round| {
        (0..N_STATE).for_each(|i| {
            state[i] = &state[i] + &M31Var::new_constant(&cs, &LAST_FOUR_ROUNDS_RC[round][i]);
        });
        state = std::array::from_fn(|i| pow5(state[i].clone()));
        apply_external_round_matrix(&mut state);
        state.iter_mut().for_each(|s| {
            let m = eval.next_trace_mask();
            eval.add_constraint((s as &QM31Var) - &m);
            *s = m;
        })
    });

    // the last full round
    {
        (0..N_STATE).for_each(|i| {
            state[i] = &state[i] + &M31Var::new_constant(&cs, &LAST_FOUR_ROUNDS_RC[3][i]);
        });
        state = std::array::from_fn(|i| pow5(state[i].clone()));
        apply_external_round_matrix(&mut state);
        state
            .iter_mut()
            .zip(initial_state.iter())
            .take(8)
            .for_each(|(s, i)| {
                let m = eval.next_trace_mask();
                eval.add_constraint(&(&m - (&s as &QM31Var)) - i);
                *s = m;
            });

        state.iter_mut().skip(8).for_each(|s| {
            let m = eval.next_trace_mask();
            eval.add_constraint((s as &QM31Var) - &m);
            *s = m;
        })
    }

    eval.add_to_relation(RelationEntryVar::new(
        lookup_elements,
        QM31Var::one(&cs),
        &[addr_1, sel_1.clone()],
    ));

    eval.add_to_relation(RelationEntryVar::new(
        lookup_elements,
        QM31Var::one(&cs),
        &[addr_2, sel_2.clone()],
    ));

    eval.add_to_relation(RelationEntryVar::new(
        lookup_elements,
        QM31Var::one(&cs),
        &[addr_3, sel_3.clone()],
    ));

    eval.add_to_relation(RelationEntryVar::new(
        lookup_elements,
        QM31Var::one(&cs),
        &[addr_4, sel_4.clone()],
    ));

    eval.add_to_relation(RelationEntryVar::new(
        lookup_elements,
        QM31Var::one(&cs),
        &[
            -&sel_1,
            initial_state[0].clone(),
            initial_state[1].clone(),
            initial_state[2].clone(),
            initial_state[3].clone(),
            initial_state[4].clone(),
            initial_state[5].clone(),
            initial_state[6].clone(),
            initial_state[7].clone(),
        ],
    ));

    eval.add_to_relation(RelationEntryVar::new(
        lookup_elements,
        QM31Var::one(&cs),
        &[
            -&sel_2,
            initial_state[8].clone(),
            initial_state[9].clone(),
            initial_state[10].clone(),
            initial_state[11].clone(),
            initial_state[12].clone(),
            initial_state[13].clone(),
            initial_state[14].clone(),
            initial_state[15].clone(),
        ],
    ));

    eval.add_to_relation(RelationEntryVar::new(
        lookup_elements,
        QM31Var::one(&cs),
        &[
            -&sel_3,
            state[0].clone(),
            state[1].clone(),
            state[2].clone(),
            state[3].clone(),
            state[4].clone(),
            state[5].clone(),
            state[6].clone(),
            state[7].clone(),
        ],
    ));

    eval.add_to_relation(RelationEntryVar::new(
        lookup_elements,
        QM31Var::one(&cs),
        &[
            -&sel_4,
            state[8].clone(),
            state[9].clone(),
            state[10].clone(),
            state[11].clone(),
            state[12].clone(),
            state[13].clone(),
            state[14].clone(),
            state[15].clone(),
        ],
    ));

    eval.finalize_logup_in_pairs();
    eval
}
