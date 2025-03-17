use crate::FiatShamirHints;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use stwo_prover::core::fields::m31::{BaseField, M31};
use stwo_prover::core::vcs::ops::MerkleHasher;
use stwo_prover::core::vcs::poseidon31_hash::Poseidon31Hash;
use stwo_prover::core::vcs::poseidon31_merkle::{Poseidon31MerkleChannel, Poseidon31MerkleHasher};
use stwo_prover::core::vcs::prover::MerkleDecommitment;
use stwo_prover::examples::plonk_with_poseidon::air::PlonkWithPoseidonProof;

#[derive(Clone, Debug)]
pub struct SinglePathMerkleProof {
    pub query: usize,

    pub sibling_hashes: Vec<Poseidon31Hash>,
    pub columns: BTreeMap<usize, Vec<M31>>,

    pub root: Poseidon31Hash,
    pub depth: usize,
}

impl SinglePathMerkleProof {
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
        raw_queries: &[usize],
        values: &[BaseField],
        root: Poseidon31Hash,
        n_columns_per_log_size: &BTreeMap<u32, usize>,
        merkle_decommitment: &MerkleDecommitment<Poseidon31MerkleHasher>,
    ) -> Vec<SinglePathMerkleProof> {
        // find out all the queried positions and sort them
        let mut queries = raw_queries.to_vec();
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
        for &query in raw_queries.iter() {
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
                let data = layer.get(&cur).unwrap().clone();
                if !data.is_empty() {
                    columns.insert(max_log_size as usize - i - 1, data);
                }
                cur >>= 1;
            }

            res.push(SinglePathMerkleProof {
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

#[derive(Debug, Clone)]
pub struct DecommitHints {
    pub precomputed_proofs: Vec<SinglePathMerkleProof>,
    pub trace_proofs: Vec<SinglePathMerkleProof>,
    pub interaction_proofs: Vec<SinglePathMerkleProof>,
    pub composition_proofs: Vec<SinglePathMerkleProof>,
}

impl DecommitHints {
    pub fn compute(
        fiat_shamir_hints: &FiatShamirHints<Poseidon31MerkleChannel>,
        proof: &PlonkWithPoseidonProof<Poseidon31MerkleHasher>,
    ) -> Self {
        let mut precomputed_proofs = vec![];
        let mut trace_proofs = vec![];
        let mut interaction_proofs = vec![];
        let mut composition_proofs = vec![];

        for (i, v) in [
            &mut precomputed_proofs,
            &mut trace_proofs,
            &mut interaction_proofs,
            &mut composition_proofs,
        ]
        .iter_mut()
        .enumerate()
        {
            let max_log_size = *fiat_shamir_hints.n_columns_per_log_size[i]
                .keys()
                .max()
                .unwrap();

            **v = SinglePathMerkleProof::from_stwo_proof(
                max_log_size,
                &fiat_shamir_hints
                    .unsorted_query_positions_per_log_size
                    .get(&max_log_size)
                    .unwrap(),
                &proof.stark_proof.queried_values[i],
                proof.stark_proof.commitments[i],
                &fiat_shamir_hints.n_columns_per_log_size[i],
                &proof.stark_proof.decommitments[i],
            );

            for proof in v.iter() {
                proof.verify();
            }
        }

        DecommitHints {
            precomputed_proofs,
            trace_proofs,
            interaction_proofs,
            composition_proofs,
        }
    }
}

#[cfg(test)]
mod test {
    use crate::{DecommitHints, FiatShamirHints};
    use num_traits::One;
    use stwo_prover::core::fields::qm31::QM31;
    use stwo_prover::core::fri::FriConfig;
    use stwo_prover::core::pcs::PcsConfig;
    use stwo_prover::core::vcs::poseidon31_merkle::{
        Poseidon31MerkleChannel, Poseidon31MerkleHasher,
    };
    use stwo_prover::examples::plonk_with_poseidon::air::{
        verify_plonk_with_poseidon, PlonkWithPoseidonProof,
    };

    #[test]
    fn test_decommitment() {
        let proof: PlonkWithPoseidonProof<Poseidon31MerkleHasher> =
            bincode::deserialize(include_bytes!("../../test_data/small_proof.bin")).unwrap();
        let config = PcsConfig {
            pow_bits: 20,
            fri_config: FriConfig::new(0, 5, 16),
        };
        verify_plonk_with_poseidon::<Poseidon31MerkleChannel>(
            proof.clone(),
            config,
            &[(1, QM31::one())],
        )
        .unwrap();

        let fiat_shamir_hints =
            FiatShamirHints::<Poseidon31MerkleChannel>::new(&proof, config, &[(1, QM31::one())]);
        let _ = DecommitHints::compute(&fiat_shamir_hints, &proof);
    }
}
