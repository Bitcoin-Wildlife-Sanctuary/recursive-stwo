use circle_plonk_dsl_answer::AnswerResults;
use circle_plonk_dsl_data_structures::{PlonkWithPoseidonProofVar, SinglePairMerkleProofVar};
use circle_plonk_dsl_fiat_shamir::FiatShamirResults;
use circle_plonk_dsl_fields::QM31Var;
use circle_plonk_dsl_hints::{FiatShamirHints, FirstLayerHints, InnerLayersHints};
use std::collections::{BTreeMap, HashMap};
use stwo_prover::core::vcs::poseidon31_merkle::Poseidon31MerkleChannel;

pub struct FoldingResults;

impl FoldingResults {
    pub fn compute(
        proof_var: &PlonkWithPoseidonProofVar,
        fiat_shamir_hints: &FiatShamirHints<Poseidon31MerkleChannel>,
        fiat_shamir_results: &FiatShamirResults,
        answer_results: &AnswerResults,
        first_layer_hints: &FirstLayerHints,
        inner_layers_hints: &InnerLayersHints,
    ) {
        let cs = answer_results.cs.clone();

        // allocate all the first layer merkle proofs
        let mut proofs = vec![];
        for (i, proof) in first_layer_hints.merkle_proofs.iter().enumerate() {
            let mut proof = SinglePairMerkleProofVar::new(&cs, proof);
            proof.verify(
                &proof_var.stark_proof.fri_proof.first_layer_commitment,
                &answer_results.query_positions_per_log_size
                    [fiat_shamir_hints.max_first_layer_column_log_size][i]
                    .bits,
            );
            proofs.push(proof);
        }

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
                let a = proofs[i].self_columns.get(&(log_size as usize)).unwrap();
                let b = fri_answer;
                a.equalverify(&b);
            }
        }

        // compute the first layer folding results
        let mut folded_results = BTreeMap::new();
        for &log_size in fiat_shamir_hints.all_log_sizes.iter() {
            let mut folded_results_per_log_size = Vec::new();
            for (proof, query) in proofs
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

        for i in 0..inner_layers_hints.merkle_proofs.len() {
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

            let merkle_proofs = inner_layers_hints.merkle_proofs.get(&log_size).unwrap();

            let mut new_folded = vec![];
            for ((folded_result, query), proof) in
                folded.iter().zip(queries.iter()).zip(merkle_proofs.iter())
            {
                let mut merkle_proof = SinglePairMerkleProofVar::new(&cs, proof);

                let self_val = merkle_proof.self_columns.get(&(log_size as usize)).unwrap();
                let sibling_val = merkle_proof
                    .siblings_columns
                    .get(&(log_size as usize))
                    .unwrap();
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

                merkle_proof.verify(
                    &proof_var.stark_proof.fri_proof.inner_layer_commitments[i],
                    &query.bits,
                );
            }
            folded = new_folded;
        }

        let queries = answer_results.query_positions_per_log_size[log_size].clone();

        for (query, v) in queries.iter().zip(folded.iter()) {
            if proof_var.stark_proof.fri_proof.last_poly.coeffs.len() == 1 {
                v.equalverify(&proof_var.stark_proof.fri_proof.last_poly.coeffs[0]);
            } else {
                let x = query.get_next_point_x();
                let eval = proof_var.stark_proof.fri_proof.last_poly.eval_at_point(&x);
                v.equalverify(&eval);
            }
        }
    }
}

#[cfg(test)]
mod test {
    use crate::FoldingResults;
    use circle_plonk_dsl_answer::AnswerResults;
    use circle_plonk_dsl_circle::CirclePointQM31Var;
    use circle_plonk_dsl_constraint_system::dvar::AllocVar;
    use circle_plonk_dsl_constraint_system::ConstraintSystemRef;
    use circle_plonk_dsl_data_structures::PlonkWithPoseidonProofVar;
    use circle_plonk_dsl_fiat_shamir::FiatShamirResults;
    use circle_plonk_dsl_fields::QM31Var;
    use circle_plonk_dsl_hints::{
        AnswerHints, DecommitHints, FiatShamirHints, FirstLayerHints, InnerLayersHints,
    };
    use num_traits::One;
    use stwo_prover::core::fields::qm31::QM31;
    use stwo_prover::core::fri::FriConfig;
    use stwo_prover::core::pcs::PcsConfig;
    use stwo_prover::core::vcs::poseidon31_merkle::{
        Poseidon31MerkleChannel, Poseidon31MerkleHasher,
    };
    use stwo_prover::examples::plonk_with_poseidon::air::{
        prove_plonk_with_poseidon, verify_plonk_with_poseidon, PlonkWithPoseidonProof,
    };

    #[test]
    pub fn test_folding() {
        let proof: PlonkWithPoseidonProof<Poseidon31MerkleHasher> =
            bincode::deserialize(include_bytes!("../../../test_data/small_proof.bin")).unwrap();
        let config = PcsConfig {
            pow_bits: 20,
            fri_config: FriConfig::new(2, 5, 16),
        };

        verify_plonk_with_poseidon::<Poseidon31MerkleChannel>(
            proof.clone(),
            config,
            &[(1, QM31::one())],
        )
        .unwrap();

        let fiat_shamir_hints = FiatShamirHints::new(&proof, config, &[(1, QM31::one())]);
        let answer_hints = AnswerHints::compute(&fiat_shamir_hints, &proof);
        let fri_answer_hints = AnswerHints::compute(&fiat_shamir_hints, &proof);
        let decommitment_hints = DecommitHints::compute(&fiat_shamir_hints, &proof);
        let first_layer_hints = FirstLayerHints::compute(&fiat_shamir_hints, &answer_hints, &proof);
        let inner_layer_hints = InnerLayersHints::compute(
            &first_layer_hints.folded_evals_by_column,
            &fiat_shamir_hints,
            &proof,
        );

        let cs = ConstraintSystemRef::new_plonk_with_poseidon_ref();
        let mut proof_var = PlonkWithPoseidonProofVar::new_witness(&cs, &proof);

        let fiat_shamir_results = FiatShamirResults::compute(
            &fiat_shamir_hints,
            &mut proof_var,
            config,
            &[(1, QM31Var::one(&cs))],
        );

        let answer_results = AnswerResults::compute(
            &CirclePointQM31Var::new_witness(&cs, &fiat_shamir_hints.oods_point),
            &fiat_shamir_hints,
            &fiat_shamir_results,
            &fri_answer_hints,
            &decommitment_hints,
            &proof_var,
            config,
        );

        FoldingResults::compute(
            &proof_var,
            &fiat_shamir_hints,
            &fiat_shamir_results,
            &answer_results,
            &first_layer_hints,
            &inner_layer_hints,
        );

        cs.pad();
        cs.check_arithmetics();
        cs.populate_logup_arguments();
        cs.check_poseidon_invocations();

        let (plonk, mut poseidon) = cs.generate_plonk_with_poseidon_circuit();
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
