use crate::{AnswerHints, FiatShamirHints};
use itertools::{zip_eq, Itertools};
use num_traits::Zero;
use std::collections::BTreeMap;
use stwo_prover::core::fields::m31::M31;
use stwo_prover::core::fields::qm31::SecureField;
use stwo_prover::core::fields::secure_column::SECURE_EXTENSION_DEGREE;
use stwo_prover::core::fri::SparseEvaluation;
use stwo_prover::core::utils::bit_reverse_index;
use stwo_prover::core::vcs::ops::MerkleHasher;
use stwo_prover::core::vcs::poseidon31_hash::Poseidon31Hash;
use stwo_prover::core::vcs::poseidon31_merkle::Poseidon31MerkleHasher;
use stwo_prover::core::vcs::poseidon31_ref::Poseidon31CRH;
use stwo_prover::core::vcs::verifier::MerkleVerifier;
use stwo_prover::examples::plonk_with_poseidon::air::PlonkWithPoseidonProof;

pub struct SinglePairMerkleProofs {
    pub query: usize,

    pub sibling_hashes: Vec<Poseidon31Hash>,
    pub self_columns: BTreeMap<usize, Vec<M31>>,
    pub siblings_columns: BTreeMap<usize, Vec<M31>>,

    pub root: Poseidon31Hash,
    pub depth: usize,
}

impl SinglePairMerkleProofs {
    pub fn verify(&self) {
        let mut self_hash = Poseidon31MerkleHasher::hash_node(
            None,
            &self.self_columns.get(&self.depth).unwrap_or(&vec![]),
        );
        let mut sibling_hash = Poseidon31MerkleHasher::hash_node(
            None,
            &self.siblings_columns.get(&self.depth).unwrap_or(&vec![]),
        );

        for i in 0..self.depth {
            let h = self.depth - i - 1;

            if self.self_columns.get(&h).is_none() {
                self_hash = Poseidon31MerkleHasher::hash_node(
                    if (self.query >> i) & 1 == 0 {
                        Some((self_hash, sibling_hash))
                    } else {
                        Some((sibling_hash, self_hash))
                    },
                    &vec![],
                );
                sibling_hash = self.sibling_hashes[i];
            } else {
                self_hash = Poseidon31MerkleHasher::hash_node(
                    if (self.query >> i) & 1 == 0 {
                        Some((self_hash, sibling_hash))
                    } else {
                        Some((sibling_hash, self_hash))
                    },
                    &self.self_columns.get(&h).unwrap_or(&vec![]),
                );
                sibling_hash = {
                    let column_hash = Poseidon31MerkleHasher::hash_column(
                        self.siblings_columns.get(&h).unwrap_or(&vec![]),
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
}

#[derive(Clone)]
pub struct FirstLayerHints {
    pub siblings: BTreeMap<u32, BTreeMap<usize, SecureField>>,
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
        let mut siblings = BTreeMap::new();

        for (&column_domain, column_query_evals) in zip_eq(
            &fiat_shamir_hints
                .fri_verifier
                .first_layer
                .column_commitment_domains,
            &answer_hints.fri_answers,
        ) {
            let queries =
                &fiat_shamir_hints.query_positions_per_log_size[&column_domain.log_size()];

            let (results, column_decommitment_positions, sparse_evaluation) =
                Self::compute_decommitment_positions_and_rebuild_evals(
                    queries,
                    column_domain.log_size(),
                    &column_query_evals,
                    &mut fri_witness,
                );

            siblings.insert(column_domain.log_size(), results);

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
        println!(
            "{:?}",
            fiat_shamir_hints
                .fri_verifier
                .first_layer
                .column_commitment_domains
                .iter()
                .flat_map(|column_domain| [column_domain.log_size(); SECURE_EXTENSION_DEGREE])
                .collect_vec()
        );

        merkle_verifier
            .verify(
                &decommitment_positions_by_log_size,
                decommitmented_values,
                proof.stark_proof.fri_proof.first_layer.decommitment.clone(),
            )
            .unwrap();

        FirstLayerHints { siblings }
    }

    pub fn compute_decommitment_positions_and_rebuild_evals(
        queries: &[usize],
        domain_log_size: u32,
        query_evals: &[SecureField],
        mut witness_evals: impl Iterator<Item = SecureField>,
    ) -> (BTreeMap<usize, SecureField>, Vec<usize>, SparseEvaluation) {
        let mut queries = queries.to_vec();
        queries.dedup();
        queries.sort_unstable();

        let mut query_evals = query_evals.iter().copied();

        let mut results = BTreeMap::new();

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

            if subset_queries[0] == subset_start {
                results.insert(subset_queries[0], subset_eval[0]);
            } else {
                results.insert(subset_queries[0], subset_eval[1]);
            }

            if subset_queries.len() == 2 {
                if subset_queries[1] == subset_start {
                    results.insert(subset_queries[1], subset_eval[0]);
                } else {
                    results.insert(subset_queries[1], subset_eval[1]);
                }
            }
        }

        let sparse_evaluation = SparseEvaluation::new(subset_evals, subset_domain_index_initials);
        (results, decommitment_positions, sparse_evaluation)
    }
}

#[cfg(test)]
mod test {
    use crate::{AnswerHints, FiatShamirHints, FirstLayerHints};
    use stwo_prover::core::fri::FriConfig;
    use stwo_prover::core::pcs::PcsConfig;
    use stwo_prover::core::vcs::poseidon31_merkle::Poseidon31MerkleHasher;
    use stwo_prover::examples::plonk_with_poseidon::air::PlonkWithPoseidonProof;

    #[test]
    fn test_folding() {
        let proof: PlonkWithPoseidonProof<Poseidon31MerkleHasher> =
            bincode::deserialize(include_bytes!("../../test_data/joint_proof.bin")).unwrap();
        let config = PcsConfig {
            pow_bits: 20,
            fri_config: FriConfig::new(0, 5, 16),
        };

        let fiat_shamir_hints = FiatShamirHints::new(&proof, config);
        let answer_hints = AnswerHints::compute(&fiat_shamir_hints, &proof);
        FirstLayerHints::compute(&fiat_shamir_hints, &answer_hints, &proof);
    }
}
