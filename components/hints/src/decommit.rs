use crate::{AnswerHints, FiatShamirHints};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use stwo_prover::core::fields::m31::{BaseField, M31};
use stwo_prover::core::vcs::ops::MerkleHasher;
use stwo_prover::core::vcs::poseidon31_hash::Poseidon31Hash;
use stwo_prover::core::vcs::poseidon31_merkle::Poseidon31MerkleHasher;
use stwo_prover::core::vcs::prover::MerkleDecommitment;
use stwo_prover::examples::plonk_with_poseidon::air::PlonkWithPoseidonProof;

#[derive(Clone, Debug)]
pub struct StandaloneMerkleProof {
    pub query: usize,

    pub sibling_hashes: Vec<Poseidon31Hash>,
    pub columns: BTreeMap<usize, Vec<M31>>,

    pub root: Poseidon31Hash,
    pub depth: usize,
}

impl StandaloneMerkleProof {
    pub fn verify(&self) {
        let mut cur_hash = Poseidon31MerkleHasher::hash_node(
            None,
            &self.columns.get(&self.depth).unwrap_or(&vec![]),
        );

        for i in 0..self.depth {
            let h = self.depth - i - 1;

            cur_hash = Poseidon31MerkleHasher::hash_node(
                if (self.query >> i) & 1 == 0 {
                    Some((cur_hash, self.sibling_hashes[i]))
                } else {
                    Some((self.sibling_hashes[i], cur_hash))
                },
                self.columns.get(&h).unwrap_or(&vec![]),
            );
        }

        assert_eq!(cur_hash, self.root);
    }

    pub fn from_stwo_proof(
        max_log_size: u32,
        queries: &[usize],
        values: &[BaseField],
        root: Poseidon31Hash,
        n_columns_per_log_size: &BTreeMap<u32, usize>,
        merkle_decommitment: &MerkleDecommitment<Poseidon31MerkleHasher>,
    ) -> Vec<StandaloneMerkleProof> {
        // find out all the queried positions and sort them
        let mut queries = queries.to_vec();
        queries.sort_unstable();
        queries.dedup();

        // create the new value map
        let mut value_iterator = values.into_iter();

        let mut queries_values_map = HashMap::new();
        for &query in queries.iter() {
            let mut v = vec![];
            for _ in 0..*n_columns_per_log_size.get(&max_log_size).unwrap() {
                v.push(*value_iterator.next().unwrap());
            }
            queries_values_map.insert(query, v);
        }

        // require the column witness to be empty
        // (all the values are provided)
        assert_eq!(merkle_decommitment.column_witness.len(), 0);

        // turn hash witness into an iterator
        let mut hash_iterator = merkle_decommitment.hash_witness.iter();

        // create the merkle partial tree
        let mut hash_layers: Vec<HashMap<usize, Poseidon31Hash>> = vec![];

        // create the leaf layer
        let mut hash_layer = HashMap::new();
        for (&query, value) in queries_values_map.iter() {
            hash_layer.insert(query, Poseidon31MerkleHasher::hash_node(None, value));
        }
        hash_layers.push(hash_layer);

        let mut positions = queries.to_vec();
        positions.sort_unstable();

        // create the intermediate layers
        let mut column_layers: Vec<HashMap<usize, Vec<M31>>> = vec![];
        for i in 0..max_log_size as usize {
            let mut layer = HashMap::new();
            let mut parents = BTreeSet::new();
            let mut column_layer = HashMap::new();

            for &position in positions.iter() {
                if !layer.contains_key(&(position >> 1)) {
                    let sibling_idx = position ^ 1;

                    let columns = if let Some(&num_columns) =
                        n_columns_per_log_size.get(&(max_log_size - 1 - i as u32))
                    {
                        let mut v = vec![];
                        for _ in 0..num_columns {
                            v.push(*value_iterator.next().unwrap());
                        }
                        v
                    } else {
                        vec![]
                    };
                    column_layer.insert(position >> 1, columns.clone());

                    let hash = if let Some(sibling) = hash_layers[i].get(&sibling_idx) {
                        let (left, right) = if position & 1 == 0 {
                            (hash_layers[i].get(&position).unwrap(), sibling)
                        } else {
                            (sibling, hash_layers[i].get(&position).unwrap())
                        };
                        Poseidon31MerkleHasher::hash_node(Some((*left, *right)), &columns)
                    } else {
                        let sibling = hash_iterator.next().unwrap();
                        hash_layers[i].insert(sibling_idx, *sibling);
                        let (left, right) = if position & 1 == 0 {
                            (hash_layers[i].get(&position).unwrap(), sibling)
                        } else {
                            (sibling, hash_layers[i].get(&position).unwrap())
                        };
                        Poseidon31MerkleHasher::hash_node(Some((*left, *right)), &columns)
                    };

                    layer.insert(position >> 1, hash);
                    parents.insert(position >> 1);
                }
            }

            column_layers.push(column_layer);
            hash_layers.push(layer);
            positions = parents.iter().copied().collect::<Vec<usize>>();
        }

        assert_eq!(hash_iterator.next(), None);
        assert_eq!(value_iterator.next(), None);

        // cheery-pick the Merkle tree paths to construct the deterministic proofs
        let mut res = vec![];
        for &query in queries.iter() {
            let mut sibling_hashes = vec![];
            let mut columns = BTreeMap::new();

            let mut cur = query;
            for layer in hash_layers.iter().take(max_log_size as usize) {
                sibling_hashes.push(*layer.get(&(cur ^ 1)).unwrap());
                cur >>= 1;
            }

            columns.insert(
                max_log_size as usize,
                queries_values_map.get(&query).unwrap().clone(),
            );

            let mut cur = query >> 1;
            for (i, layer) in column_layers
                .iter()
                .take(max_log_size as usize - 1)
                .enumerate()
            {
                columns.insert(
                    max_log_size as usize - i - 1,
                    layer.get(&cur).unwrap().clone(),
                );
                cur >>= 1;
            }

            res.push(StandaloneMerkleProof {
                query,
                sibling_hashes,
                columns,
                root: root.clone(),
                depth: max_log_size as usize,
            });
        }
        res
    }
}

pub struct DecommitHints;

impl DecommitHints {
    pub fn compute(
        _fiat_shamir_hints: &FiatShamirHints,
        _answer_hints: &AnswerHints,
        _proof: &PlonkWithPoseidonProof<Poseidon31MerkleHasher>,
    ) -> Self {
        DecommitHints {}
    }
}

#[cfg(test)]
mod test {
    use crate::{FiatShamirHints, StandaloneMerkleProof};
    use stwo_prover::core::fri::FriConfig;
    use stwo_prover::core::pcs::PcsConfig;
    use stwo_prover::core::vcs::poseidon31_merkle::Poseidon31MerkleHasher;
    use stwo_prover::examples::plonk_with_poseidon::air::PlonkWithPoseidonProof;

    #[test]
    fn test_merkle_tree_proof_conversion() {
        let proof: PlonkWithPoseidonProof<Poseidon31MerkleHasher> =
            bincode::deserialize(include_bytes!("../../test_data/joint_proof.bin")).unwrap();
        let config = PcsConfig {
            pow_bits: 20,
            fri_config: FriConfig::new(0, 5, 16),
        };

        let fiat_shamir_hints = FiatShamirHints::new(&proof, config);

        let max_log_size = *fiat_shamir_hints.n_columns_per_log_size[0]
            .keys()
            .max()
            .unwrap();
        let proofs = StandaloneMerkleProof::from_stwo_proof(
            max_log_size,
            &fiat_shamir_hints
                .query_positions_per_log_size
                .get(&max_log_size)
                .unwrap(),
            &proof.stark_proof.queried_values[0],
            proof.stark_proof.commitments[0],
            &fiat_shamir_hints.n_columns_per_log_size[0],
            &proof.stark_proof.decommitments[0],
        );
        for proof in proofs.iter() {
            proof.verify();
        }
    }
}
