use crate::data_structures::{EvalAtRowVar, RelationEntryVar};
use circle_plonk_dsl_constraint_system::dvar::DVar;
use circle_plonk_dsl_data_structures::PlonkWithAcceleratorLookupElementsVar;
use circle_plonk_dsl_fields::QM31Var;
use std::ops::Neg;
use stwo_prover::examples::plonk::Plonk;

pub fn evaluate_plonk<'a>(
    lookup_elements: &PlonkWithAcceleratorLookupElementsVar,
    mut eval: EvalAtRowVar<'a>,
) -> EvalAtRowVar<'a> {
    let cs = lookup_elements.cs();

    let a_wire = eval.get_preprocessed_column(Plonk::new("a_wire".to_string()).id());
    let b_wire = eval.get_preprocessed_column(Plonk::new("b_wire".to_string()).id());
    let c_wire = eval.get_preprocessed_column(Plonk::new("c_wire".to_string()).id());
    let op = eval.get_preprocessed_column(Plonk::new("op".to_string()).id());
    let mult_a = eval.get_preprocessed_column(Plonk::new("mult_a".to_string()).id());
    let mult_b = eval.get_preprocessed_column(Plonk::new("mult_b".to_string()).id());
    let mult_c = eval.get_preprocessed_column(Plonk::new("mult_c".to_string()).id());
    let poseidon_wire = eval.get_preprocessed_column(Plonk::new("poseidon_wire".to_string()).id());
    let mult_poseidon = eval.get_preprocessed_column(Plonk::new("mult_poseidon".to_string()).id());
    let enforce_c_m31 = eval.get_preprocessed_column(Plonk::new("enforce_c_m31".to_string()).id());

    let a_val_0 = eval.next_trace_mask();
    let a_val_1 = eval.next_trace_mask();
    let a_val_2 = eval.next_trace_mask();
    let a_val_3 = eval.next_trace_mask();

    let b_val_0 = eval.next_trace_mask();
    let b_val_1 = eval.next_trace_mask();
    let b_val_2 = eval.next_trace_mask();
    let b_val_3 = eval.next_trace_mask();

    let c_val_0 = eval.next_trace_mask();
    let c_val_1 = eval.next_trace_mask();
    let c_val_2 = eval.next_trace_mask();
    let c_val_3 = eval.next_trace_mask();

    eval.add_constraint(&enforce_c_m31 * &c_val_1);
    eval.add_constraint(&enforce_c_m31 * &c_val_2);
    eval.add_constraint(&enforce_c_m31 * &c_val_3);

    let a_val =
        &(&(&a_val_0 + &a_val_1.shift_by_i()) + &a_val_2.shift_by_j()) + &a_val_3.shift_by_ij();

    let b_val =
        &(&(&b_val_0 + &b_val_1.shift_by_i()) + &b_val_2.shift_by_j()) + &b_val_3.shift_by_ij();

    let c_val =
        &(&(&c_val_0 + &c_val_1.shift_by_i()) + &c_val_2.shift_by_j()) + &c_val_3.shift_by_ij();

    eval.add_constraint(
        &(&c_val - &(&op * &(&a_val + &b_val)))
            - &(&(&(&QM31Var::one(&cs) - &op) * &a_val) * &b_val),
    );

    eval.add_to_relation(RelationEntryVar::new(
        lookup_elements,
        mult_a,
        &[
            a_wire,
            a_val_0.clone(),
            a_val_1.clone(),
            a_val_2.clone(),
            a_val_3.clone(),
        ],
    ));
    eval.add_to_relation(RelationEntryVar::new(
        lookup_elements,
        mult_b,
        &[
            b_wire,
            b_val_0.clone(),
            b_val_1.clone(),
            b_val_2.clone(),
            b_val_3.clone(),
        ],
    ));

    eval.add_to_relation(RelationEntryVar::new(
        lookup_elements,
        mult_c,
        &[c_wire.clone(), c_val_0, c_val_1, c_val_2, c_val_3],
    ));
    eval.add_to_relation(RelationEntryVar::new(
        lookup_elements,
        mult_poseidon.neg(),
        &[
            poseidon_wire,
            a_val_0,
            a_val_1,
            a_val_2,
            a_val_3,
            b_val_0,
            b_val_1,
            b_val_2,
            b_val_3,
        ],
    ));

    eval.finalize_logup_in_pairs();
    eval
}
