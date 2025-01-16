use crate::data_structures::{EvalAtRowVar, RelationEntryVar};
use circle_plonk_dsl_constraint_system::dvar::DVar;
use circle_plonk_dsl_data_structures::PlonkWithAcceleratorLookupElementsVar;
use circle_plonk_dsl_fields::QM31Var;
use std::ops::Neg;
use stwo_prover::constraint_framework::preprocessed_columns::PreprocessedColumn;
use stwo_prover::constraint_framework::ORIGINAL_TRACE_IDX;

pub fn evaluate_plonk<'a>(
    lookup_elements: &PlonkWithAcceleratorLookupElementsVar,
    mut eval: EvalAtRowVar<'a>,
) -> EvalAtRowVar<'a> {
    let cs = lookup_elements.cs();

    let a_wire = eval.get_preprocessed_column(PreprocessedColumn::Plonk(0));
    let b_wire = eval.get_preprocessed_column(PreprocessedColumn::Plonk(1));
    let c_wire = eval.get_preprocessed_column(PreprocessedColumn::Plonk(2));
    let op = eval.get_preprocessed_column(PreprocessedColumn::Plonk(3));
    let mult = eval.get_preprocessed_column(PreprocessedColumn::Plonk(4));
    let mult_poseidon = eval.get_preprocessed_column(PreprocessedColumn::Plonk(5));

    let a_val = eval.next_trace_mask();
    let b_val = eval.next_trace_mask();
    let c_vals = eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1, 2, 3, 4, 5, 6, 7]);

    eval.add_constraint(
        &(&c_vals[0] - &(&op * &(&a_val + &b_val)))
            - &(&(&(&QM31Var::one(&cs) - &op) * &a_val) * &b_val),
    );

    eval.add_to_relation(RelationEntryVar::new(
        lookup_elements,
        QM31Var::one(&cs),
        &[a_wire, a_val],
    ));
    eval.add_to_relation(RelationEntryVar::new(
        lookup_elements,
        QM31Var::one(&cs),
        &[b_wire, b_val],
    ));

    eval.add_to_relation(RelationEntryVar::new(
        lookup_elements,
        mult.neg(),
        &[c_wire.clone(), c_vals[0].clone()],
    ));
    eval.add_to_relation(RelationEntryVar::new(
        lookup_elements,
        mult_poseidon.neg(),
        &[
            c_wire.neg(),
            c_vals[0].clone(),
            c_vals[1].clone(),
            c_vals[2].clone(),
            c_vals[3].clone(),
            c_vals[4].clone(),
            c_vals[5].clone(),
            c_vals[6].clone(),
            c_vals[7].clone(),
        ],
    ));

    eval.finalize_logup_in_pairs();
    eval
}
