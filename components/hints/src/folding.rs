use crate::{AnswerHints, FiatShamirHints};
use itertools::{zip_eq, Itertools};
use num_traits::Zero;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use stwo_prover::core::circle::Coset;
use stwo_prover::core::fields::m31::M31;
use stwo_prover::core::fields::qm31::{SecureField, QM31};
use stwo_prover::core::fields::secure_column::SECURE_EXTENSION_DEGREE;
use stwo_prover::core::fields::FieldExpOps;
use stwo_prover::core::fri::SparseEvaluation;
use stwo_prover::core::utils::bit_reverse_index;
use stwo_prover::core::vcs::ops::MerkleHasher;
use stwo_prover::core::vcs::poseidon31_hash::Poseidon31Hash;
use stwo_prover::core::vcs::poseidon31_merkle::Poseidon31MerkleHasher;
use stwo_prover::core::vcs::poseidon31_ref::Poseidon31CRH;
use stwo_prover::core::vcs::prover::MerkleDecommitment;
use stwo_prover::core::vcs::verifier::MerkleVerifier;
use stwo_prover::examples::plonk_with_poseidon::air::PlonkWithPoseidonProof;

#[derive(Clone)]
pub struct SinglePairMerkleProof {
    pub query: usize,

    pub sibling_hashes: Vec<Poseidon31Hash>,
    pub self_columns: BTreeMap<usize, QM31>,
    pub siblings_columns: BTreeMap<usize, QM31>,

    pub root: Poseidon31Hash,
    pub depth: usize,
}

impl SinglePairMerkleProof {
    pub fn verify(&self) {
        let mut self_hash = Poseidon31MerkleHasher::hash_node(
            None,
            &self
                .self_columns
                .get(&self.depth)
                .map_or(vec![], |v| v.to_m31_array().to_vec()),
        );
        let mut sibling_hash = Poseidon31MerkleHasher::hash_node(
            None,
            &self
                .siblings_columns
                .get(&self.depth)
                .map_or(vec![], |v| v.to_m31_array().to_vec()),
        );

        for i in 0..self.depth {
            let h = self.depth - i - 1;

            if !self.self_columns.contains_key(&h) {
                self_hash = Poseidon31MerkleHasher::hash_node(
                    if (self.query >> i) & 1 == 0 {
                        Some((self_hash, sibling_hash))
                    } else {
                        Some((sibling_hash, self_hash))
                    },
                    &vec![],
                );
                if i != self.depth - 1 {
                    sibling_hash = self.sibling_hashes[i];
                }
            } else {
                self_hash = Poseidon31MerkleHasher::hash_node(
                    if (self.query >> i) & 1 == 0 {
                        Some((self_hash, sibling_hash))
                    } else {
                        Some((sibling_hash, self_hash))
                    },
                    &self
                        .self_columns
                        .get(&h)
                        .map_or(vec![], |v| v.to_m31_array().to_vec()),
                );
                sibling_hash = {
                    let column_hash = Poseidon31MerkleHasher::hash_column(
                        &self
                            .siblings_columns
                            .get(&h)
                            .map_or(vec![], |v| v.to_m31_array().to_vec()),
                    );
                    let mut state = [M31::zero(); 16];
                    state[..8].copy_from_slice(&self.sibling_hashes[i].0);
                    state[8..].copy_from_slice(&column_hash.0);
                    Poseidon31Hash(Poseidon31CRH::compress(&state))
                };
            }
        }
        assert_eq!(self_hash, self.root);
    }

    pub fn from_stwo_proof(
        log_sizes_with_data: &BTreeSet<u32>,
        root: Poseidon31Hash,
        leaf_queries: &[usize],
        values: &[M31],
        decommitment: &MerkleDecommitment<Poseidon31MerkleHasher>,
    ) -> Vec<SinglePairMerkleProof> {
        // require the column witness to be empty
        // (all the values are provided)
        assert_eq!(decommitment.column_witness.len(), 0);

        // get the max log_size
        let max_log_size = *log_sizes_with_data.iter().max().unwrap();

        let mut queries = leaf_queries.to_vec();

        // values iter
        let mut values_iter = values.iter();
        let mut hash_iter = decommitment.hash_witness.iter();

        let mut queries_values_map = BTreeMap::new();
        let mut hash_layers: Vec<HashMap<usize, Poseidon31Hash>> = vec![];

        for current_log_size in (0..=max_log_size).rev() {
            queries.sort_unstable();
            queries.dedup();

            if log_sizes_with_data.contains(&current_log_size) {
                // compute the query positions and their siblings
                let mut self_and_siblings = vec![];
                for &q in queries.iter() {
                    self_and_siblings.push(q);
                    self_and_siblings.push(q ^ 1);
                }
                self_and_siblings.sort_unstable();
                self_and_siblings.dedup();

                let mut queries_values = BTreeMap::new();
                for k in self_and_siblings.iter() {
                    let v = [
                        *values_iter.next().unwrap(),
                        *values_iter.next().unwrap(),
                        *values_iter.next().unwrap(),
                        *values_iter.next().unwrap(),
                    ];
                    queries_values.insert(*k, v);
                }

                let mut hash_layer = HashMap::new();
                for (&query, value) in queries_values.iter() {
                    if current_log_size == max_log_size {
                        hash_layer.insert(query, Poseidon31MerkleHasher::hash_node(None, value));
                    } else {
                        let left_idx = query << 1;
                        let right_idx = left_idx + 1;

                        let left_hash =
                            if let Some(hash) = hash_layers.last().unwrap().get(&left_idx) {
                                *hash
                            } else {
                                let v = *hash_iter.next().unwrap();
                                hash_layers.last_mut().unwrap().insert(left_idx, v);
                                v
                            };
                        let right_hash =
                            if let Some(hash) = hash_layers.last().unwrap().get(&right_idx) {
                                *hash
                            } else {
                                let v = *hash_iter.next().unwrap();
                                hash_layers.last_mut().unwrap().insert(right_idx, v);
                                v
                            };
                        hash_layer.insert(
                            query,
                            Poseidon31MerkleHasher::hash_node(Some((left_hash, right_hash)), value),
                        );
                    }
                }

                queries_values_map.insert(current_log_size, queries_values);
                hash_layers.push(hash_layer);
            } else {
                assert_ne!(current_log_size, max_log_size);

                let mut hash_layer = HashMap::new();
                for &query in queries.iter() {
                    let left_idx = query << 1;
                    let right_idx = left_idx + 1;

                    let left_hash = if let Some(hash) = hash_layers.last().unwrap().get(&left_idx) {
                        *hash
                    } else {
                        let v = *hash_iter.next().unwrap();
                        hash_layers.last_mut().unwrap().insert(left_idx, v);
                        v
                    };
                    let right_hash = if let Some(hash) = hash_layers.last().unwrap().get(&right_idx)
                    {
                        *hash
                    } else {
                        let v = *hash_iter.next().unwrap();
                        hash_layers.last_mut().unwrap().insert(right_idx, v);
                        v
                    };

                    let h = Poseidon31MerkleHasher::hash_node(Some((left_hash, right_hash)), &[]);
                    hash_layer.insert(query, h);
                }

                hash_layers.push(hash_layer);
            }

            queries.iter_mut().for_each(|v| *v = (*v) >> 1);
        }

        assert!(values_iter.next().is_none());
        assert!(hash_iter.next().is_none());

        assert_eq!(hash_layers.last().unwrap().len(), 1);
        assert_eq!(*hash_layers.last().unwrap().get(&0).unwrap(), root);

        let mut proofs = vec![];
        for leaf_query in leaf_queries.iter() {
            let mut sibling_hashes = vec![];
            let mut self_columns = BTreeMap::new();
            let mut siblings_columns = BTreeMap::new();

            let mut query = *leaf_query;

            for current_log_size in (1..=max_log_size).rev() {
                if log_sizes_with_data.contains(&current_log_size) {
                    let self_idx = query;
                    let sibling_idx = self_idx ^ 1;

                    let self_value = queries_values_map
                        .get(&current_log_size)
                        .unwrap()
                        .get(&self_idx)
                        .unwrap();
                    let sibling_value = queries_values_map
                        .get(&current_log_size)
                        .unwrap()
                        .get(&sibling_idx)
                        .unwrap();

                    self_columns
                        .insert(current_log_size as usize, QM31::from_m31_array(*self_value));
                    siblings_columns.insert(
                        current_log_size as usize,
                        QM31::from_m31_array(*sibling_value),
                    );

                    if current_log_size != max_log_size {
                        let sibling_left = sibling_idx << 1;
                        let sibling_right = sibling_left + 1;

                        let left_hash = *hash_layers
                            [(max_log_size - current_log_size - 1) as usize]
                            .get(&sibling_left)
                            .unwrap();
                        let right_hash = *hash_layers
                            [(max_log_size - current_log_size - 1) as usize]
                            .get(&sibling_right)
                            .unwrap();

                        sibling_hashes.push(Poseidon31MerkleHasher::hash_node(
                            Some((left_hash, right_hash)),
                            &[],
                        ));
                    }
                } else {
                    let self_idx = query;
                    let sibling_idx = self_idx ^ 1;

                    let sibling_hash = *hash_layers[(max_log_size - current_log_size) as usize]
                        .get(&sibling_idx)
                        .unwrap();
                    sibling_hashes.push(sibling_hash);
                }
                query >>= 1;
            }

            let proof = SinglePairMerkleProof {
                query: *leaf_query,
                sibling_hashes,
                self_columns,
                siblings_columns,
                root,
                depth: max_log_size as usize,
            };
            proof.verify();
            proofs.push(proof);
        }
        proofs
    }
}

#[derive(Clone)]
pub struct FirstLayerHints {
    pub merkle_proofs: Vec<SinglePairMerkleProof>,
    pub folded_evals_by_column: BTreeMap<u32, Vec<SecureField>>,
}

impl FirstLayerHints {
    pub fn compute(
        fiat_shamir_hints: &FiatShamirHints,
        answer_hints: &AnswerHints,
        proof: &PlonkWithPoseidonProof<Poseidon31MerkleHasher>,
    ) -> FirstLayerHints {
        // Columns are provided in descending order by size.
        let max_column_log_size = fiat_shamir_hints
            .fri_verifier
            .first_layer
            .column_commitment_domains[0]
            .log_size();
        assert_eq!(
            fiat_shamir_hints.max_first_layer_column_log_size,
            max_column_log_size
        );

        let mut fri_witness = proof
            .stark_proof
            .fri_proof
            .first_layer
            .fri_witness
            .iter()
            .copied();

        let mut decommitment_positions_by_log_size = BTreeMap::new();
        let mut decommitmented_values = vec![];

        let mut folded_evals_by_column = BTreeMap::new();

        for (&column_domain, column_query_evals) in zip_eq(
            &fiat_shamir_hints
                .fri_verifier
                .first_layer
                .column_commitment_domains,
            &answer_hints.fri_answers,
        ) {
            let queries =
                &fiat_shamir_hints.query_positions_per_log_size[&column_domain.log_size()];

            let (column_decommitment_positions, sparse_evaluation) =
                Self::compute_decommitment_positions_and_rebuild_evals(
                    queries,
                    column_domain.log_size(),
                    &column_query_evals,
                    &mut fri_witness,
                );

            // Columns of the same size have the same decommitment positions.
            decommitment_positions_by_log_size
                .insert(column_domain.log_size(), column_decommitment_positions);

            decommitmented_values.extend(
                sparse_evaluation
                    .subset_evals
                    .iter()
                    .flatten()
                    .flat_map(|qm31| qm31.to_m31_array()),
            );

            folded_evals_by_column.insert(
                column_domain.log_size(),
                sparse_evaluation.fold_circle(
                    fiat_shamir_hints.fri_verifier.first_layer.folding_alpha,
                    column_domain,
                ),
            );
        }

        assert!(fri_witness.next().is_none());

        let merkle_verifier = MerkleVerifier::new(
            proof.stark_proof.fri_proof.first_layer.commitment,
            fiat_shamir_hints
                .fri_verifier
                .first_layer
                .column_commitment_domains
                .iter()
                .flat_map(|column_domain| [column_domain.log_size(); SECURE_EXTENSION_DEGREE])
                .collect(),
        );

        merkle_verifier
            .verify(
                &decommitment_positions_by_log_size,
                decommitmented_values.clone(),
                proof.stark_proof.fri_proof.first_layer.decommitment.clone(),
            )
            .unwrap();

        // log_sizes with data
        let mut log_sizes_with_data = BTreeSet::new();
        for column_domain in fiat_shamir_hints
            .fri_verifier
            .first_layer
            .column_commitment_domains
            .iter()
        {
            log_sizes_with_data.insert(column_domain.log_size());
        }

        let merkle_proofs = SinglePairMerkleProof::from_stwo_proof(
            &log_sizes_with_data,
            proof.stark_proof.fri_proof.first_layer.commitment,
            &fiat_shamir_hints
                .raw_query_positions_per_log_size
                .get(&fiat_shamir_hints.max_first_layer_column_log_size)
                .unwrap(),
            &decommitmented_values,
            &proof.stark_proof.fri_proof.first_layer.decommitment,
        );

        FirstLayerHints {
            merkle_proofs,
            folded_evals_by_column,
        }
    }

    pub fn compute_decommitment_positions_and_rebuild_evals(
        queries: &[usize],
        domain_log_size: u32,
        query_evals: &[SecureField],
        mut witness_evals: impl Iterator<Item = SecureField>,
    ) -> (Vec<usize>, SparseEvaluation) {
        let mut queries = queries.to_vec();
        queries.dedup();
        queries.sort_unstable();

        let mut query_evals = query_evals.iter().copied();

        let mut decommitment_positions = Vec::new();
        let mut subset_evals = Vec::new();
        let mut subset_domain_index_initials = Vec::new();

        // Group queries by the subset they reside in.
        for subset_queries in queries.chunk_by(|a, b| a >> 1 == b >> 1) {
            let subset_start = (subset_queries[0] >> 1) << 1;
            let subset_decommitment_positions = subset_start..subset_start + (1 << 1);
            decommitment_positions.extend(subset_decommitment_positions.clone());

            let mut subset_queries_iter = subset_queries.iter().copied().peekable();

            let subset_eval = subset_decommitment_positions
                .map(|position| match subset_queries_iter.next_if_eq(&position) {
                    Some(_) => query_evals.next().unwrap(),
                    None => witness_evals.next().unwrap(),
                })
                .collect_vec();

            subset_evals.push(subset_eval.clone());
            subset_domain_index_initials.push(bit_reverse_index(subset_start, domain_log_size));
        }

        let sparse_evaluation = SparseEvaluation::new(subset_evals, subset_domain_index_initials);
        (decommitment_positions, sparse_evaluation)
    }
}

pub struct InnerLayersHints {
    pub merkle_proofs: BTreeMap<u32, Vec<SinglePairMerkleProof>>,
    pub folded_intermediate_results: BTreeMap<u32, BTreeMap<usize, SecureField>>,
}

impl InnerLayersHints {
    pub fn compute(
        folded_evals_by_column: &BTreeMap<u32, Vec<SecureField>>,
        fiat_shamir_hints: &FiatShamirHints,
        proof: &PlonkWithPoseidonProof<Poseidon31MerkleHasher>,
    ) -> InnerLayersHints {
        let mut log_size = fiat_shamir_hints.max_first_layer_column_log_size;

        let mut folded = BTreeMap::new();
        for i in fiat_shamir_hints
            .raw_query_positions_per_log_size
            .get(&log_size)
            .unwrap()
            .iter()
            .map(|v| (*v) >> 1)
        {
            folded.insert(i, QM31::zero());
        }

        let mut all_merkle_proofs = BTreeMap::new();
        let mut all_folded_intermediate_results = BTreeMap::new();

        for (i, inner_layer) in proof.stark_proof.fri_proof.inner_layers.iter().enumerate() {
            if let Some(folded_into) = folded_evals_by_column.get(&log_size) {
                assert_eq!(folded_into.len(), folded.len());
                for ((_, v), b) in folded.iter_mut().zip(folded_into.iter()) {
                    *v = fiat_shamir_hints.fri_alphas[0].square() * *v + *b;
                }
            }

            log_size -= 1;

            let domain = Coset::half_odds(log_size);

            let mut fri_witness = inner_layer.fri_witness.iter();
            let mut new_folded = BTreeMap::new();
            let mut decommitmented = BTreeMap::new();

            for (k, &v) in folded.iter() {
                let sibling_v = if let Some(&sibling_v) = folded.get(&(k ^ 1)) {
                    sibling_v
                } else {
                    *fri_witness.next().unwrap()
                };

                let (left_v, right_v) = if k & 1 == 0 {
                    (v, sibling_v)
                } else {
                    (sibling_v, v)
                };

                let folded_query = k >> 1;
                let left_idx = folded_query << 1;
                let right_idx = left_idx + 1;

                decommitmented.insert(left_idx, left_v);
                decommitmented.insert(right_idx, right_v);

                let point = domain.at(bit_reverse_index(left_idx, log_size));
                let x_inv = point.x.inverse();

                let new_left_v = left_v + right_v;
                let new_right_v = (left_v - right_v) * x_inv;
                let folded_value = new_left_v + new_right_v * fiat_shamir_hints.fri_alphas[i + 1];

                new_folded.insert(folded_query, folded_value);
            }

            let decommitment_positions = decommitmented.keys().copied().collect_vec();
            let decommitmented_values = decommitmented
                .values()
                .map(|v| v.to_m31_array())
                .flatten()
                .collect_vec();

            let merkle_verifier: MerkleVerifier<Poseidon31MerkleHasher> = MerkleVerifier::new(
                inner_layer.commitment,
                vec![log_size; SECURE_EXTENSION_DEGREE],
            );
            merkle_verifier
                .verify(
                    &BTreeMap::from_iter([(log_size, decommitment_positions)]),
                    decommitmented_values.clone(),
                    inner_layer.decommitment.clone(),
                )
                .unwrap();

            let merkle_proofs = SinglePairMerkleProof::from_stwo_proof(
                &BTreeSet::from([log_size]),
                inner_layer.commitment.clone(),
                &fiat_shamir_hints
                    .raw_query_positions_per_log_size
                    .get(&fiat_shamir_hints.max_first_layer_column_log_size)
                    .unwrap()
                    .iter()
                    .map(|v| *v >> (fiat_shamir_hints.max_first_layer_column_log_size - log_size))
                    .collect_vec(),
                &decommitmented_values,
                &inner_layer.decommitment,
            );
            for merkle_proof in merkle_proofs.iter() {
                merkle_proof.verify();
            }
            all_merkle_proofs.insert(log_size, merkle_proofs);

            assert!(fri_witness.next().is_none());
            all_folded_intermediate_results.insert(log_size, folded.clone());
            folded = new_folded;
        }

        for (_, v) in folded.iter() {
            assert_eq!(v, &fiat_shamir_hints.last_layer_evaluation);
        }

        Self {
            merkle_proofs: all_merkle_proofs,
            folded_intermediate_results: all_folded_intermediate_results,
        }
    }
}

#[cfg(test)]
mod test {
    use crate::{AnswerHints, FiatShamirHints, FirstLayerHints, InnerLayersHints};
    use num_traits::One;
    use stwo_prover::core::fields::qm31::QM31;
    use stwo_prover::core::fri::FriConfig;
    use stwo_prover::core::pcs::PcsConfig;
    use stwo_prover::core::vcs::poseidon31_merkle::Poseidon31MerkleHasher;
    use stwo_prover::examples::plonk_with_poseidon::air::PlonkWithPoseidonProof;

    #[test]
    fn test_folding() {
        let proof: PlonkWithPoseidonProof<Poseidon31MerkleHasher> =
            bincode::deserialize(include_bytes!("../../test_data/small_proof.bin")).unwrap();
        let config = PcsConfig {
            pow_bits: 20,
            fri_config: FriConfig::new(0, 5, 16),
        };

        let fiat_shamir_hints = FiatShamirHints::new(&proof, config, &[(1, QM31::one())]);
        let answer_hints = AnswerHints::compute(&fiat_shamir_hints, &proof);
        let first_layer_hints = FirstLayerHints::compute(&fiat_shamir_hints, &answer_hints, &proof);
        for proof in first_layer_hints.merkle_proofs.iter() {
            proof.verify();
        }

        InnerLayersHints::compute(
            &first_layer_hints.folded_evals_by_column,
            &fiat_shamir_hints,
            &proof,
        );
    }
}
