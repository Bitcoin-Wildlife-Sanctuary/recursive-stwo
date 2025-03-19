use crate::data_structures::merkle_proofs::{
    LastFirstLayerHints, LastFirstLayerInputVar, LastInnerLayersInputVar,
};
use circle_plonk_dsl_fields::QM31Var;
use circle_plonk_dsl_hints::FiatShamirHints;
use circle_plonk_dsl_last_answer::LastAnswerResults;
use circle_plonk_dsl_last_data_structures::LastPlonkWithPoseidonProofVar;
use circle_plonk_dsl_last_fiat_shamir::LastFiatShamirResults;
use std::collections::{BTreeMap, HashMap};
use stwo_prover::core::vcs::sha256_poseidon31_merkle::Sha256Poseidon31MerkleChannel;

pub mod data_structures;

pub struct LastFoldingResults;

impl LastFoldingResults {
    pub fn compute(
        proof: &LastPlonkWithPoseidonProofVar,
        fiat_shamir_hints: &FiatShamirHints<Sha256Poseidon31MerkleChannel>,
        fiat_shamir_results: &LastFiatShamirResults,
        answer_results: &LastAnswerResults,
        first_layer_hints: &LastFirstLayerHints,
        first_layer_input_var: &LastFirstLayerInputVar,
        inner_layers_input_var: &LastInnerLayersInputVar,
    ) {
        let cs = answer_results.cs.clone();

        // check the fri answers match the self_columns
        for (&log_size, fri_answer_per_log_size) in fiat_shamir_hints
            .all_log_sizes
            .iter()
            .rev()
            .zip(answer_results.fri_answers.iter())
        {
            for (i, (_, fri_answer)) in fiat_shamir_hints
                .unsorted_query_positions_per_log_size
                .get(&log_size)
                .unwrap()
                .iter()
                .zip(fri_answer_per_log_size.iter())
                .enumerate()
            {
                let a = first_layer_input_var.merkle_proofs[i]
                    .self_columns
                    .get(&(log_size as usize))
                    .unwrap();
                let b = fri_answer;
                a.equalverify(&b);
            }
        }

        // compute the first layer folding results
        let mut folded_results = BTreeMap::new();
        for &log_size in fiat_shamir_hints.all_log_sizes.iter() {
            let mut folded_results_per_log_size = Vec::new();
            for (proof, query) in first_layer_input_var
                .merkle_proofs
                .iter()
                .zip(answer_results.query_positions_per_log_size[log_size].iter())
            {
                let self_val = proof.self_columns.get(&(log_size as usize)).unwrap();
                let sibling_val = proof.siblings_columns.get(&(log_size as usize)).unwrap();

                let point = query.get_absolute_point().double();
                let y_inv = point.y.inv();

                let (left_val, right_val) = QM31Var::swap(
                    &self_val,
                    &sibling_val,
                    query.bits.value[0],
                    query.bits.variables[0],
                );

                let new_left_val = &left_val + &right_val;
                let new_right_val = &(&left_val - &right_val) * &y_inv;

                let folded_result = &new_left_val
                    + &(&new_right_val
                        * &fiat_shamir_results.fri_alphas[(fiat_shamir_hints
                            .max_first_layer_column_log_size
                            - log_size)
                            as usize]);

                folded_results_per_log_size.push(folded_result);
            }
            folded_results.insert(log_size, folded_results_per_log_size);
        }

        for (log_size, folded_evals) in first_layer_hints.folded_evals_by_column.iter() {
            let folded_queries = fiat_shamir_hints
                .unsorted_query_positions_per_log_size
                .get(&log_size)
                .unwrap()
                .iter()
                .map(|v| v >> 1)
                .collect::<Vec<_>>();

            let mut dedup_folded_queries = folded_queries.clone();
            dedup_folded_queries.sort_unstable();
            dedup_folded_queries.dedup();

            assert_eq!(folded_evals.len(), dedup_folded_queries.len());

            let mut results_from_hints = HashMap::new();
            for (&query, &val) in dedup_folded_queries.iter().zip(folded_evals.iter()) {
                results_from_hints.insert(query, val);
            }

            for (query, val) in folded_queries
                .iter()
                .zip(folded_results.get(&log_size).unwrap().iter())
            {
                let left = results_from_hints.get(&query).unwrap();
                let right = &val.value();
                assert_eq!(left, right);
            }
        }

        // continue with the foldings
        let mut log_size = fiat_shamir_hints.max_first_layer_column_log_size;

        let mut folded = Vec::new();
        for _ in 0..fiat_shamir_hints
            .unsorted_query_positions_per_log_size
            .get(&log_size)
            .unwrap()
            .len()
        {
            folded.push(QM31Var::zero(&cs));
        }

        for i in 0..inner_layers_input_var.merkle_proofs.len() {
            if let Some(folded_into) = folded_results.get(&log_size) {
                assert_eq!(folded_into.len(), folded.len());

                let mut fri_alpha = fiat_shamir_results.fri_alphas[i].clone();
                fri_alpha = &fri_alpha * &fri_alpha;
                for (v, b) in folded.iter_mut().zip(folded_into.iter()) {
                    *v = &(&fri_alpha * (v as &QM31Var)) + b;
                }
            }

            log_size -= 1;

            let queries = answer_results.query_positions_per_log_size[log_size].clone();

            let merkle_proofs = inner_layers_input_var.merkle_proofs.get(&log_size).unwrap();

            let mut new_folded = vec![];
            for ((folded_result, query), proof) in
                folded.iter().zip(queries.iter()).zip(merkle_proofs.iter())
            {
                let self_val = proof.self_columns.get(&(log_size as usize)).unwrap();
                let sibling_val = proof.siblings_columns.get(&(log_size as usize)).unwrap();
                folded_result.equalverify(&self_val);

                let mut left_query = query.bits.clone();
                left_query.value[0] = false;
                left_query.variables[0] = 0;

                let point = query.get_absolute_point();
                let x_inv = point.x.inv();

                let (left_val, right_val) = QM31Var::swap(
                    &self_val,
                    &sibling_val,
                    query.bits.value[0],
                    query.bits.variables[0],
                );

                let new_left_val = &left_val + &right_val;
                let new_right_val = &(&left_val - &right_val) * &x_inv;

                let folded_result =
                    &new_left_val + &(&new_right_val * &fiat_shamir_results.fri_alphas[i + 1]);
                new_folded.push(folded_result);
            }
            folded = new_folded;
        }

        let queries = answer_results.query_positions_per_log_size[log_size].clone();

        for (query, v) in queries.iter().zip(folded.iter()) {
            if proof.stark_proof.last_poly.coeffs.len() == 1 {
                v.equalverify(&proof.stark_proof.last_poly.coeffs[0]);
            } else {
                let x = query.get_next_point_x();
                let eval = proof.stark_proof.last_poly.eval_at_point(&x);
                v.equalverify(&eval);
            }
        }
    }
}

#[cfg(test)]
mod test {
    use crate::data_structures::merkle_proofs::{
        LastFirstLayerHints, LastFirstLayerInputVar, LastInnerLayersHints, LastInnerLayersInputVar,
    };
    use crate::LastFoldingResults;
    use circle_plonk_dsl_constraint_system::dvar::AllocVar;
    use circle_plonk_dsl_constraint_system::ConstraintSystemRef;
    use circle_plonk_dsl_hints::{AnswerHints, FiatShamirHints};
    use circle_plonk_dsl_last_answer::data_structures::{
        LastDecommitHints, LastDecommitInput, LastDecommitInputVar,
    };
    use circle_plonk_dsl_last_answer::LastAnswerResults;
    use circle_plonk_dsl_last_data_structures::LastPlonkWithPoseidonProofVar;
    use circle_plonk_dsl_last_fiat_shamir::{
        LastFiatShamirInput, LastFiatShamirInputVar, LastFiatShamirResults,
    };
    use num_traits::One;
    use stwo_prover::core::fields::qm31::QM31;
    use stwo_prover::core::fri::FriConfig;
    use stwo_prover::core::pcs::PcsConfig;
    use stwo_prover::core::vcs::sha256_merkle::Sha256MerkleChannel;
    use stwo_prover::core::vcs::sha256_poseidon31_merkle::{
        Sha256Poseidon31MerkleChannel, Sha256Poseidon31MerkleHasher,
    };
    use stwo_prover::examples::plonk_with_poseidon::air::{
        verify_plonk_with_poseidon, PlonkWithPoseidonProof,
    };
    use stwo_prover::examples::plonk_without_poseidon::air::{
        prove_plonk_without_poseidon, verify_plonk_without_poseidon,
    };

    #[test]
    fn test_last_folding() {
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
        let decommit_hints = LastDecommitHints::from_proof(&fiat_shamir_hints, &proof);
        let fri_answer_hints = AnswerHints::compute(&fiat_shamir_hints, &proof);
        let first_layer_hints =
            LastFirstLayerHints::compute(&fiat_shamir_hints, &fri_answer_hints, &proof);
        let inner_layers_hints = LastInnerLayersHints::compute(
            &first_layer_hints.folded_evals_by_column,
            &fiat_shamir_hints,
            &proof,
        );

        let fiat_shamir_input = LastFiatShamirInput::from_proof(&proof, &fiat_shamir_hints);
        let decommit_input = LastDecommitInput::from_hints(&decommit_hints);
        let fiat_shamir_input_var =
            LastFiatShamirInputVar::new_public_input(&cs, &fiat_shamir_input);
        let decommit_input_var = LastDecommitInputVar::new_public_input(&cs, &decommit_input);
        let first_layer_input_var =
            LastFirstLayerInputVar::new_public_input(&cs, &first_layer_hints);
        let inner_layers_input_var =
            LastInnerLayersInputVar::new_public_input(&cs, &inner_layers_hints);

        let proof_var = LastPlonkWithPoseidonProofVar::new_witness(&cs, &proof);
        let fiat_shamir_results =
            LastFiatShamirResults::compute(&proof_var, &fiat_shamir_input_var);

        let last_answer_results = LastAnswerResults::compute(
            &fiat_shamir_hints,
            &decommit_hints,
            &fri_answer_hints,
            &fiat_shamir_results,
            &decommit_input_var,
            &proof_var,
            config,
        );

        LastFoldingResults::compute(
            &proof_var,
            &fiat_shamir_hints,
            &fiat_shamir_results,
            &last_answer_results,
            &first_layer_hints,
            &first_layer_input_var,
            &inner_layers_input_var,
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
        for proof in decommit_input
            .precomputed_proofs
            .iter()
            .chain(decommit_input.trace_proofs.iter())
            .chain(decommit_input.interaction_proofs.iter())
            .chain(decommit_input.composition_proofs.iter())
        {
            for (_, column) in proof.packed_columns.iter() {
                for elem in column.iter() {
                    add_input(&mut inputs, *elem);
                }
            }
        }
        for proof in first_layer_hints.merkle_proofs.iter() {
            for (_, elem) in proof.self_columns.iter() {
                add_input(&mut inputs, *elem);
            }
            for (_, elem) in proof.siblings_columns.iter() {
                add_input(&mut inputs, *elem);
            }
        }
        for (_, proofs) in inner_layers_hints.merkle_proofs.iter() {
            for proof in proofs.iter() {
                for (_, elem) in proof.self_columns.iter() {
                    add_input(&mut inputs, *elem);
                }
                for (_, elem) in proof.siblings_columns.iter() {
                    add_input(&mut inputs, *elem);
                }
            }
        }
        println!("input length: {} QM31", inputs.len());

        let circuit = cs.generate_plonk_without_poseidon_circuit();
        let proof = prove_plonk_without_poseidon::<Sha256MerkleChannel>(config, &circuit);
        verify_plonk_without_poseidon::<Sha256MerkleChannel>(proof, config, &inputs).unwrap();
    }
}
