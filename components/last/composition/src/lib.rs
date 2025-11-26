use circle_plonk_dsl_circle::CirclePointQM31Var;
use circle_plonk_dsl_composition::coset_vanishing;
use circle_plonk_dsl_composition::data_structures::{EvalAtRowVar, PointEvaluationAccumulatorVar};
use circle_plonk_dsl_composition::plonk::evaluate_plonk;
use circle_plonk_dsl_composition::poseidon::evaluate_poseidon;
use circle_plonk_dsl_data_structures::LookupElementsVar;
use circle_plonk_dsl_fields::QM31Var;
use circle_plonk_dsl_hints::FiatShamirHints;
use circle_plonk_dsl_last_data_structures::LastPlonkWithPoseidonProofVar;
use itertools::Itertools;
use stwo::core::vcs::sha256_poseidon31_merkle::Sha256Poseidon31MerkleChannel;
use stwo_constraint_framework::PREPROCESSED_TRACE_IDX;

pub struct LastCompositionCheck;

impl LastCompositionCheck {
    pub fn compute(
        fiat_shamir_hints: &FiatShamirHints<Sha256Poseidon31MerkleChannel>,
        lookup_elements: &LookupElementsVar,
        random_coeff: QM31Var,
        oods_point: CirclePointQM31Var,
        proof: &LastPlonkWithPoseidonProofVar,
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
                31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49,
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
        let left_value = &(&(&proof.stark_proof.sampled_values[3][0][0]
            + &proof.stark_proof.sampled_values[3][1][0].shift_by_i())
            + &proof.stark_proof.sampled_values[3][2][0].shift_by_j())
            + &proof.stark_proof.sampled_values[3][3][0].shift_by_ij();
        let right_value = &(&(&proof.stark_proof.sampled_values[3][4][0]
            + &proof.stark_proof.sampled_values[3][5][0].shift_by_i())
            + &proof.stark_proof.sampled_values[3][6][0].shift_by_j())
            + &proof.stark_proof.sampled_values[3][7][0].shift_by_ij();
        let expected_composition = &left_value
            + &(&right_value
                * &oods_point
                    .repeated_double_x_only(fiat_shamir_hints.composition_log_degree_bound - 2));

        computed_composition.equalverify(&expected_composition);
    }
}

#[cfg(test)]
mod test {
    use crate::LastCompositionCheck;
    use circle_plonk_dsl_constraint_system::var::AllocVar;
    use circle_plonk_dsl_constraint_system::ConstraintSystemRef;
    use circle_plonk_dsl_hints::FiatShamirHints;
    use circle_plonk_dsl_last_data_structures::LastPlonkWithPoseidonProofVar;
    use circle_plonk_dsl_last_fiat_shamir::{
        LastFiatShamirInput, LastFiatShamirInputVar, LastFiatShamirResults,
    };
    use num_traits::One;
    use stwo::core::fields::qm31::QM31;
    use stwo::core::fri::FriConfig;
    use stwo::core::pcs::PcsConfig;
    use stwo::core::vcs::sha256_merkle::Sha256MerkleChannel;
    use stwo::core::vcs::sha256_poseidon31_merkle::{
        Sha256Poseidon31MerkleChannel, Sha256Poseidon31MerkleHasher,
    };
    use stwo_examples::plonk_with_poseidon::air::{
        verify_plonk_with_poseidon, PlonkWithPoseidonProof,
    };
    use stwo_examples::plonk_without_poseidon::air::{
        prove_plonk_without_poseidon, verify_plonk_without_poseidon,
    };

    #[test]
    fn test_composition() {
        let proof: PlonkWithPoseidonProof<Sha256Poseidon31MerkleHasher> =
            bincode::deserialize(include_bytes!("../../../test_data/hybrid_hash.bin")).unwrap();
        let config = PcsConfig {
            pow_bits: 28,
            fri_config: FriConfig::new(7, 9, 8),
        };

        verify_plonk_with_poseidon::<Sha256Poseidon31MerkleChannel>(
            proof.clone(),
            config,
            &[
                (1, QM31::one()),
                (2, QM31::from_u32_unchecked(0, 1, 0, 0)),
                (3, QM31::from_u32_unchecked(0, 0, 1, 0)),
            ],
        )
        .unwrap();

        let cs = ConstraintSystemRef::new_plonk_without_poseidon_ref();

        let fiat_shamir_hints = FiatShamirHints::<Sha256Poseidon31MerkleChannel>::new(
            &proof,
            config,
            &[
                (1, QM31::one()),
                (2, QM31::from_u32_unchecked(0, 1, 0, 0)),
                (3, QM31::from_u32_unchecked(0, 0, 1, 0)),
            ],
        );
        let fiat_shamir_input = LastFiatShamirInput::from_proof(&proof, &fiat_shamir_hints);
        let fiat_shamir_input_var =
            LastFiatShamirInputVar::new_public_input(&cs, &fiat_shamir_input);
        let proof_var = LastPlonkWithPoseidonProofVar::new_witness(&cs, &proof);

        let fiat_shamir_results =
            LastFiatShamirResults::compute(&proof_var, &fiat_shamir_input_var);
        LastCompositionCheck::compute(
            &fiat_shamir_hints,
            &fiat_shamir_results.lookup_elements,
            fiat_shamir_results.random_coeff.clone(),
            fiat_shamir_results.oods_point.clone(),
            &proof_var,
        );

        cs.pad();
        cs.check_arithmetics();
        cs.populate_logup_arguments();

        let config = PcsConfig {
            pow_bits: 20,
            fri_config: FriConfig::new(0, 5, 16),
        };

        let pack_queries = |slice: &[usize]| {
            let mut slice = slice.to_vec();
            assert!(slice.len() <= 4);
            slice.resize(4, 0);
            QM31::from_u32_unchecked(
                slice[0] as u32,
                slice[1] as u32,
                slice[2] as u32,
                slice[3] as u32,
            )
        };

        let mut inputs = vec![];
        let add_input = |inputs: &mut Vec<(usize, QM31)>, input: QM31| {
            let idx = inputs.len() + 1;
            inputs.push((idx, input))
        };

        add_input(&mut inputs, QM31::one());
        add_input(&mut inputs, QM31::from_u32_unchecked(0, 1, 0, 0));
        add_input(&mut inputs, QM31::from_u32_unchecked(0, 0, 1, 0));
        add_input(&mut inputs, fiat_shamir_input.t);
        add_input(
            &mut inputs,
            QM31::from_m31_array(std::array::from_fn(|i| {
                fiat_shamir_input.sampled_values_hash.0[i]
            })),
        );
        add_input(
            &mut inputs,
            QM31::from_m31_array(std::array::from_fn(|i| {
                fiat_shamir_input.sampled_values_hash.0[i + 4]
            })),
        );
        add_input(&mut inputs, fiat_shamir_input.plonk_total_sum);
        add_input(&mut inputs, fiat_shamir_input.poseidon_total_sum);
        add_input(&mut inputs, fiat_shamir_hints.z);
        add_input(&mut inputs, fiat_shamir_hints.alpha);
        add_input(&mut inputs, fiat_shamir_input.random_coeff);
        add_input(
            &mut inputs,
            fiat_shamir_input.after_sampled_values_random_coeff,
        );
        add_input(
            &mut inputs,
            pack_queries(&fiat_shamir_input.queries_at_max_first_layer_column_log_size[0..4]),
        );
        add_input(
            &mut inputs,
            pack_queries(&fiat_shamir_input.queries_at_max_first_layer_column_log_size[4..8]),
        );
        for fri_alpha in fiat_shamir_input.fri_alphas.iter() {
            add_input(&mut inputs, *fri_alpha);
        }

        let circuit = cs.generate_plonk_without_poseidon_circuit();
        let proof = prove_plonk_without_poseidon::<Sha256MerkleChannel>(config, &circuit);
        verify_plonk_without_poseidon::<Sha256MerkleChannel>(proof, config, &inputs).unwrap();
    }
}
