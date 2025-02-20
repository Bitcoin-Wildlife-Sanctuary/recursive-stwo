use crate::data_structures::{EvalAtRowVar, PointEvaluationAccumulatorVar};
use crate::plonk::evaluate_plonk;
use crate::poseidon::evaluate_poseidon;
use circle_plonk_dsl_circle::CirclePointQM31Var;
use circle_plonk_dsl_constraint_system::dvar::DVar;
use circle_plonk_dsl_data_structures::{
    PlonkWithAcceleratorLookupElementsVar, PlonkWithPoseidonProofVar,
};
use circle_plonk_dsl_fields::{M31Var, QM31Var};
use circle_plonk_dsl_hints::FiatShamirHints;
use itertools::Itertools;
use stwo_prover::constraint_framework::PREPROCESSED_TRACE_IDX;
use stwo_prover::core::poly::circle::CanonicCoset;

pub mod data_structures;
pub mod plonk;
pub mod poseidon;

pub fn coset_vanishing(p: &CirclePointQM31Var, coset_log_size: u32) -> QM31Var {
    let cs = p.cs();
    let coset = CanonicCoset::new(coset_log_size).coset;
    let mut x = (p + &(-coset.initial + coset.step_size.half().to_point())).x;

    // The formula for the x coordinate of the double of a point.
    for _ in 1..coset.log_size {
        let sq = &x * &x;
        x = &(&sq + &sq) - &M31Var::one(&cs);
    }
    x
}

pub struct CompositionCheck;

impl CompositionCheck {
    pub fn compute(
        fiat_shamir_hints: &FiatShamirHints,
        lookup_elements: &PlonkWithAcceleratorLookupElementsVar,
        random_coeff: QM31Var,
        oods_point: CirclePointQM31Var,
        proof: &PlonkWithPoseidonProofVar,
    ) {
        let plonk_tree_subspan = &fiat_shamir_hints.plonk_tree_subspan;
        let plonk_prepared_column_indices = &fiat_shamir_hints.plonk_prepared_column_indices;
        let poseidon_tree_subspan = &fiat_shamir_hints.poseidon_tree_subspan;
        let poseidon_prepared_column_indices = &fiat_shamir_hints.poseidon_prepared_column_indices;

        // enforce that the columns are separate, which would be the case if the Poseidon circuit is
        // much smaller than the Plonk circuit (expected), so there is_first column does not overlap.
        assert_eq!(
            *plonk_prepared_column_indices,
            vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
        );
        assert_eq!(
            *poseidon_prepared_column_indices,
            vec![
                10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30,
                31, 32, 33, 34
            ]
        );

        let mut evaluation_accumulator = PointEvaluationAccumulatorVar::new(random_coeff);

        let eval_row_plonk = {
            let preprocessed_mask: Vec<&Vec<QM31Var>> = plonk_prepared_column_indices
                .iter()
                .map(|idx| &proof.stark_proof.sampled_values[PREPROCESSED_TRACE_IDX][*idx])
                .collect_vec();

            let mut mask_points = proof
                .stark_proof
                .sampled_values
                .sub_tree(&plonk_tree_subspan);
            mask_points[PREPROCESSED_TRACE_IDX] = preprocessed_mask;

            EvalAtRowVar::new(
                mask_points,
                proof.stmt1.plonk_total_sum.clone(),
                coset_vanishing(&oods_point, proof.stmt0.log_size_plonk.value.0).inv(),
                proof.stmt0.log_size_plonk.value.0,
                &mut evaluation_accumulator,
            )
        };
        evaluate_plonk(lookup_elements, eval_row_plonk);

        let eval_row_poseidon = {
            let preprocessed_mask: Vec<&Vec<QM31Var>> = poseidon_prepared_column_indices
                .iter()
                .map(|idx| &proof.stark_proof.sampled_values[PREPROCESSED_TRACE_IDX][*idx])
                .collect_vec();

            let mut mask_points = proof
                .stark_proof
                .sampled_values
                .sub_tree(&poseidon_tree_subspan);
            mask_points[PREPROCESSED_TRACE_IDX] = preprocessed_mask;

            EvalAtRowVar::new(
                mask_points,
                proof.stmt1.poseidon_total_sum.clone(),
                coset_vanishing(&oods_point, proof.stmt0.log_size_poseidon.value.0).inv(),
                proof.stmt0.log_size_poseidon.value.0,
                &mut evaluation_accumulator,
            )
        };
        evaluate_poseidon(lookup_elements, eval_row_poseidon);

        let computed_composition = evaluation_accumulator.finalize();
        let expected_composition = &(&(&proof.stark_proof.sampled_values[3][0][0]
            + &proof.stark_proof.sampled_values[3][1][0].shift_by_i())
            + &proof.stark_proof.sampled_values[3][2][0].shift_by_j())
            + &proof.stark_proof.sampled_values[3][3][0].shift_by_ij();

        computed_composition.equalverify(&expected_composition);
    }
}

#[cfg(test)]
mod test {
    use crate::CompositionCheck;
    use circle_plonk_dsl_circle::CirclePointQM31Var;
    use circle_plonk_dsl_constraint_system::dvar::AllocVar;
    use circle_plonk_dsl_constraint_system::ConstraintSystemRef;
    use circle_plonk_dsl_data_structures::{
        PlonkWithAcceleratorLookupElementsVar, PlonkWithPoseidonProofVar,
    };
    use circle_plonk_dsl_fields::QM31Var;
    use circle_plonk_dsl_hints::FiatShamirHints;
    use num_traits::One;
    use stwo_prover::core::fields::qm31::QM31;
    use stwo_prover::core::fields::FieldExpOps;
    use stwo_prover::core::fri::FriConfig;
    use stwo_prover::core::pcs::PcsConfig;
    use stwo_prover::core::vcs::poseidon31_merkle::{
        Poseidon31MerkleChannel, Poseidon31MerkleHasher,
    };
    use stwo_prover::examples::plonk_with_poseidon::air::{
        prove_plonk_with_poseidon, verify_plonk_with_poseidon, PlonkWithPoseidonProof,
    };

    #[test]
    fn test_composition() {
        let proof: PlonkWithPoseidonProof<Poseidon31MerkleHasher> =
            bincode::deserialize(include_bytes!("../../test_data/small_proof.bin")).unwrap();
        let config = PcsConfig {
            pow_bits: 20,
            fri_config: FriConfig::new(0, 5, 16),
        };

        let fiat_shamir_hints = FiatShamirHints::new(&proof, config, &[(1, QM31::one())]);

        let cs = ConstraintSystemRef::new_ref();
        let proof_var = PlonkWithPoseidonProofVar::new_witness(&cs, &proof);

        CompositionCheck::compute(
            &fiat_shamir_hints,
            &PlonkWithAcceleratorLookupElementsVar {
                cs: cs.clone(),
                z: QM31Var::new_witness(&cs, &fiat_shamir_hints.z),
                alpha: QM31Var::new_witness(&cs, &fiat_shamir_hints.alpha),
                alpha_powers: std::array::from_fn(|i| {
                    QM31Var::new_witness(&cs, &fiat_shamir_hints.alpha.pow(i as u128))
                }),
            },
            QM31Var::new_witness(&cs, &fiat_shamir_hints.random_coeff),
            CirclePointQM31Var::new_witness(&cs, &fiat_shamir_hints.oods_point),
            &proof_var,
        );

        cs.pad();
        cs.check_arithmetics();
        cs.populate_logup_arguments();
        cs.check_poseidon_invocations();

        let (plonk, mut poseidon) = cs.generate_circuit();
        let proof =
            prove_plonk_with_poseidon::<Poseidon31MerkleChannel>(config, &plonk, &mut poseidon);
        verify_plonk_with_poseidon::<Poseidon31MerkleChannel>(
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
