use circle_plonk_dsl_constraint_system::var::{AllocVar, AllocationMode, Var};
use circle_plonk_dsl_constraint_system::ConstraintSystemRef;
use circle_plonk_dsl_fields::{M31Var, QM31Var};
use circle_plonk_dsl_merkle::Poseidon31MerkleHasherVar;
use itertools::Itertools;
use num_traits::Zero;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use stwo_prover::core::fields::m31::{BaseField, M31};
use stwo_prover::core::fields::qm31::QM31;
use stwo_prover::core::vcs::poseidon31_merkle::Poseidon31MerkleHasher;
use stwo_prover::core::vcs::prover::MerkleDecommitment;
use stwo_prover::core::vcs::sha256_poseidon31_merkle::Sha256Poseidon31MerkleHasher;

#[derive(Clone, Debug)]
pub struct LastSinglePathMerkleProof {
    pub columns: BTreeMap<usize, Vec<M31>>,
}

impl LastSinglePathMerkleProof {
    pub fn from_stwo_proof(
        max_log_size: u32,
        raw_queries: &[usize],
        values: &[BaseField],
        n_columns_per_log_size: &BTreeMap<u32, usize>,
        merkle_decommitment: &MerkleDecommitment<Sha256Poseidon31MerkleHasher>,
    ) -> Vec<Self> {
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

        let mut positions = queries.to_vec();
        positions.sort_unstable();

        // create the intermediate layers
        let mut column_layers: Vec<HashMap<usize, Vec<M31>>> = vec![];
        for i in 0..max_log_size as usize {
            let mut layer = BTreeSet::new();
            let mut parents = BTreeSet::new();
            let mut column_layer = HashMap::new();

            for &position in positions.iter() {
                if !layer.contains(&(position >> 1)) {
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
                    layer.insert(position >> 1);
                    parents.insert(position >> 1);
                }
            }

            column_layers.push(column_layer);
            positions = parents.iter().copied().collect::<Vec<usize>>();
        }

        assert_eq!(value_iterator.next(), None);

        // cheery-pick the Merkle tree paths to construct the deterministic proofs
        let mut res = vec![];
        for &query in raw_queries.iter() {
            let mut columns = BTreeMap::new();

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

            res.push(LastSinglePathMerkleProof { columns });
        }
        res
    }
}

#[derive(Clone, Debug)]
pub struct LastSinglePathMerkleProofVar {
    pub cs: ConstraintSystemRef,
    pub columns: BTreeMap<usize, Vec<M31Var>>,
}

impl LastSinglePathMerkleProofVar {
    pub fn from_proof_and_input(
        input_var: &LastSinglePathMerkleProofInputVar,
        proof: &LastSinglePathMerkleProof,
    ) -> Self {
        let cs = input_var.cs();
        let mut columns = BTreeMap::new();

        let log_sizes = proof.columns.keys().copied().collect_vec();
        for log_size in log_sizes.iter() {
            let vars = proof.columns[log_size]
                .iter()
                .map(|x| M31Var::new_witness(&cs, x))
                .collect_vec();

            if vars.len() <= 4 {
                assert_eq!(input_var.packed_columns[log_size].len(), 1);
                let decomposed = input_var.packed_columns[log_size][0].decompose_m31();
                for (left, right) in vars.iter().zip(decomposed.iter()) {
                    left.equalverify(right);
                }
            } else if vars.len() <= 8 {
                assert_eq!(input_var.packed_columns[log_size].len(), 2);
                let decomposed = input_var.packed_columns[log_size][0].decompose_m31();
                for (left, right) in vars[0..4].iter().zip(decomposed.iter()) {
                    left.equalverify(right);
                }
                let decomposed = input_var.packed_columns[log_size][1].decompose_m31();
                for (left, right) in vars[4..8].iter().zip(decomposed.iter()) {
                    left.equalverify(right);
                }
            } else {
                assert_eq!(input_var.packed_columns[log_size].len(), 2);
                let hash = Poseidon31MerkleHasherVar::hash_m31_columns_get_rate(&vars).to_qm31();
                hash[0].equalverify(&input_var.packed_columns[log_size][0]);
                hash[1].equalverify(&input_var.packed_columns[log_size][1]);
            }

            columns.insert(*log_size, vars);
        }

        Self { cs, columns }
    }
}

#[derive(Debug, Clone)]
pub struct LastSinglePathMerkleProofInput {
    pub packed_columns: BTreeMap<usize, Vec<QM31>>,
}

impl LastSinglePathMerkleProofInput {
    pub fn from_proof(proof: &LastSinglePathMerkleProof) -> Self {
        let mut packed_columns = BTreeMap::new();

        for (&log_size, column_values) in proof.columns.iter() {
            if column_values.len() <= 4 {
                let mut v = column_values.clone();
                v.resize(4, M31::zero());
                packed_columns.insert(log_size, vec![QM31::from_m31(v[0], v[1], v[2], v[3])]);
            } else if column_values.len() <= 8 {
                let mut v = column_values.clone();
                v.resize(8, M31::zero());
                packed_columns.insert(
                    log_size,
                    vec![
                        QM31::from_m31(v[0], v[1], v[2], v[3]),
                        QM31::from_m31(v[4], v[5], v[6], v[7]),
                    ],
                );
            } else {
                let hash = Poseidon31MerkleHasher::hash_column_get_rate(column_values);
                packed_columns.insert(
                    log_size,
                    vec![
                        QM31::from_m31(hash.0[0], hash.0[1], hash.0[2], hash.0[3]),
                        QM31::from_m31(hash.0[4], hash.0[5], hash.0[6], hash.0[7]),
                    ],
                );
            }
        }

        Self { packed_columns }
    }
}

#[derive(Debug, Clone)]
pub struct LastSinglePathMerkleProofInputVar {
    pub cs: ConstraintSystemRef,
    pub packed_columns: BTreeMap<usize, Vec<QM31Var>>,
}

impl Var for LastSinglePathMerkleProofInputVar {
    type Value = LastSinglePathMerkleProofInput;

    fn cs(&self) -> ConstraintSystemRef {
        self.cs.clone()
    }
}

impl AllocVar for LastSinglePathMerkleProofInputVar {
    fn new_variables(cs: &ConstraintSystemRef, value: &Self::Value, mode: AllocationMode) -> Self {
        let mut packed_columns = BTreeMap::new();
        for (&log_size, column_values) in value.packed_columns.iter() {
            packed_columns.insert(
                log_size,
                column_values
                    .iter()
                    .map(|x| QM31Var::new_variables(cs, x, mode))
                    .collect_vec(),
            );
        }

        Self {
            cs: cs.clone(),
            packed_columns,
        }
    }
}
