use crate::{AnswerHints, FiatShamirHints};
use std::collections::{BTreeMap, HashMap};
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

        for i in 0..self.depth - 1 {
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
        _root: Poseidon31Hash,
        n_columns_per_log_size: &BTreeMap<u32, usize>,
        merkle_decommitment: &MerkleDecommitment<Poseidon31MerkleHasher>,
    ) -> Vec<StandaloneMerkleProof> {
        // find out all the queried positions and sort them
        let mut queries = queries.to_vec();
        queries.sort_unstable();
        queries.dedup();

        // get the number of columns
        let column_num = values.len();
        println!("{:?}", queries);
        println!("{:?}", column_num);
        println!("{:?}", n_columns_per_log_size);

        // create the new value map
        let mut iter = values.into_iter();
        let mut queries_values_map = HashMap::new();
        for &query in queries.iter() {
            let mut v = vec![];
            for _ in 0..*n_columns_per_log_size.get(&max_log_size).unwrap() {
                v.push(*iter.next().unwrap());
            }
            queries_values_map.insert(query, v);
        }

        // require the column witness to be empty
        // (all the values are provided)
        assert_eq!(merkle_decommitment.column_witness.len(), 0);

        // turn hash witness into an iterator
        let mut hash_iterator = merkle_decommitment.hash_witness.iter();

        // create the merkle partial tree
        let mut layers: Vec<HashMap<usize, Poseidon31Hash>> = vec![];

        // create the leaf layer
        let mut layer = HashMap::new();
        for (&query, value) in queries_values_map.iter() {
            layer.insert(query, Poseidon31MerkleHasher::hash_node(None, value));
        }
        layers.push(layer);

        todo!()
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
        let _ = StandaloneMerkleProof::from_stwo_proof(
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
    }
}
