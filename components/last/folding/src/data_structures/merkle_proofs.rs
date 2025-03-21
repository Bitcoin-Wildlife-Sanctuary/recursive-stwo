use circle_plonk_dsl_constraint_system::var::{AllocVar, AllocationMode, Var};
use circle_plonk_dsl_constraint_system::ConstraintSystemRef;
use circle_plonk_dsl_fields::QM31Var;
use circle_plonk_dsl_hints::{AnswerHints, FiatShamirHints, FirstLayerHints};
use itertools::{zip_eq, Itertools};
use num_traits::Zero;
use std::collections::{BTreeMap, BTreeSet};
use stwo_prover::core::circle::{CirclePoint, Coset};
use stwo_prover::core::fields::m31::M31;
use stwo_prover::core::fields::qm31::{SecureField, QM31};
use stwo_prover::core::fields::{ExtensionOf, Field, FieldExpOps};
use stwo_prover::core::utils::bit_reverse_index;
use stwo_prover::core::vcs::prover::MerkleDecommitment;
use stwo_prover::core::vcs::sha256_poseidon31_merkle::{
    Sha256Poseidon31MerkleChannel, Sha256Poseidon31MerkleHasher,
};
use stwo_prover::examples::plonk_with_poseidon::air::PlonkWithPoseidonProof;

#[derive(Clone, Debug)]
pub struct LastSinglePairMerkleProof {
    pub self_columns: BTreeMap<usize, QM31>,
    pub siblings_columns: BTreeMap<usize, QM31>,
}

impl LastSinglePairMerkleProof {
    pub fn from_stwo_proof(
        log_sizes_with_data: &BTreeSet<u32>,
        leaf_queries: &[usize],
        values: &[M31],
        decommitment: &MerkleDecommitment<Sha256Poseidon31MerkleHasher>,
    ) -> Vec<LastSinglePairMerkleProof> {
        // require the column witness to be empty
        // (all the values are provided)
        assert_eq!(decommitment.column_witness.len(), 0);

        // get the max log_size
        let max_log_size = *log_sizes_with_data.iter().max().unwrap();

        let mut queries = leaf_queries.to_vec();

        // values iter
        let mut values_iter = values.iter();
        let mut queries_values_map = BTreeMap::new();

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

                queries_values_map.insert(current_log_size, queries_values);
            } else {
                assert_ne!(current_log_size, max_log_size);
            }

            queries.iter_mut().for_each(|v| *v = (*v) >> 1);
        }

        assert!(values_iter.next().is_none());

        let mut proofs = vec![];
        for leaf_query in leaf_queries.iter() {
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
                }
                query >>= 1;
            }

            let proof = LastSinglePairMerkleProof {
                self_columns,
                siblings_columns,
            };
            proofs.push(proof);
        }
        proofs
    }
}

#[derive(Clone, Debug)]
pub struct LastSinglePairMerkleProofVar {
    pub cs: ConstraintSystemRef,
    pub self_columns: BTreeMap<usize, QM31Var>,
    pub siblings_columns: BTreeMap<usize, QM31Var>,
}

impl Var for LastSinglePairMerkleProofVar {
    type Value = LastSinglePairMerkleProof;

    fn cs(&self) -> ConstraintSystemRef {
        self.cs.clone()
    }
}

impl AllocVar for LastSinglePairMerkleProofVar {
    fn new_variables(cs: &ConstraintSystemRef, value: &Self::Value, mode: AllocationMode) -> Self {
        let mut self_columns = BTreeMap::new();
        for (log_size, column_values) in value.self_columns.iter() {
            self_columns.insert(*log_size, QM31Var::new_variables(cs, column_values, mode));
        }

        let mut siblings_columns = BTreeMap::new();
        for (log_size, column_values) in value.siblings_columns.iter() {
            siblings_columns.insert(*log_size, QM31Var::new_variables(cs, column_values, mode));
        }

        Self {
            cs: cs.clone(),
            self_columns,
            siblings_columns,
        }
    }
}

#[derive(Clone)]
pub struct LastFirstLayerHints {
    pub merkle_proofs: Vec<LastSinglePairMerkleProof>,
    pub folded_evals_by_column: BTreeMap<u32, Vec<SecureField>>,
}

impl LastFirstLayerHints {
    pub fn compute(
        fiat_shamir_hints: &FiatShamirHints<Sha256Poseidon31MerkleChannel>,
        answer_hints: &AnswerHints<Sha256Poseidon31MerkleChannel>,
        proof: &PlonkWithPoseidonProof<Sha256Poseidon31MerkleHasher>,
    ) -> LastFirstLayerHints {
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
                &fiat_shamir_hints.sorted_query_positions_per_log_size[&column_domain.log_size()];

            let (column_decommitment_positions, sparse_evaluation) =
                FirstLayerHints::compute_decommitment_positions_and_rebuild_evals(
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
                    fiat_shamir_hints.fri_alphas
                        [(max_column_log_size - column_domain.log_size()) as usize],
                    column_domain,
                ),
            );
        }

        assert!(fri_witness.next().is_none());

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

        let merkle_proofs = LastSinglePairMerkleProof::from_stwo_proof(
            &log_sizes_with_data,
            &fiat_shamir_hints
                .unsorted_query_positions_per_log_size
                .get(&fiat_shamir_hints.max_first_layer_column_log_size)
                .unwrap(),
            &decommitmented_values,
            &proof.stark_proof.fri_proof.first_layer.decommitment,
        );

        LastFirstLayerHints {
            merkle_proofs,
            folded_evals_by_column,
        }
    }
}

#[derive(Clone, Debug)]
pub struct LastFirstLayerInputVar {
    pub cs: ConstraintSystemRef,
    pub merkle_proofs: Vec<LastSinglePairMerkleProofVar>,
}

impl Var for LastFirstLayerInputVar {
    type Value = LastFirstLayerHints;

    fn cs(&self) -> ConstraintSystemRef {
        self.cs.clone()
    }
}

impl AllocVar for LastFirstLayerInputVar {
    fn new_variables(cs: &ConstraintSystemRef, value: &Self::Value, mode: AllocationMode) -> Self {
        let mut merkle_proofs = vec![];
        for proof in value.merkle_proofs.iter() {
            merkle_proofs.push(LastSinglePairMerkleProofVar::new_variables(cs, proof, mode))
        }

        Self {
            cs: cs.clone(),
            merkle_proofs,
        }
    }
}

#[derive(Clone, Debug)]
pub struct LastInnerLayersHints {
    pub merkle_proofs: BTreeMap<u32, Vec<LastSinglePairMerkleProof>>,
    pub folded_intermediate_results: BTreeMap<u32, BTreeMap<usize, SecureField>>,
}

impl LastInnerLayersHints {
    pub fn compute(
        folded_evals_by_column: &BTreeMap<u32, Vec<SecureField>>,
        fiat_shamir_hints: &FiatShamirHints<Sha256Poseidon31MerkleChannel>,
        proof: &PlonkWithPoseidonProof<Sha256Poseidon31MerkleHasher>,
    ) -> LastInnerLayersHints {
        let mut log_size = fiat_shamir_hints.max_first_layer_column_log_size;

        let mut folded = BTreeMap::new();
        for i in fiat_shamir_hints
            .unsorted_query_positions_per_log_size
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
                    *v = fiat_shamir_hints.fri_alphas[i].square() * *v + *b;
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
            let decommitmented_values = decommitmented
                .values()
                .map(|v| v.to_m31_array())
                .flatten()
                .collect_vec();

            let merkle_proofs = LastSinglePairMerkleProof::from_stwo_proof(
                &BTreeSet::from([log_size]),
                &fiat_shamir_hints
                    .unsorted_query_positions_per_log_size
                    .get(&fiat_shamir_hints.max_first_layer_column_log_size)
                    .unwrap()
                    .iter()
                    .map(|v| *v >> (fiat_shamir_hints.max_first_layer_column_log_size - log_size))
                    .collect_vec(),
                &decommitmented_values,
                &inner_layer.decommitment,
            );
            all_merkle_proofs.insert(log_size, merkle_proofs);

            assert!(fri_witness.next().is_none());
            all_folded_intermediate_results.insert(log_size, folded.clone());
            folded = new_folded;
        }

        log_size -= 1;
        let domain = Coset::half_odds(log_size);
        for (&idx, v) in folded.iter() {
            let mut x = domain.at(bit_reverse_index(idx, log_size)).x;
            let last_poly_log_size = fiat_shamir_hints.last_layer_coeffs.len().ilog2();
            let mut doublings = Vec::new();
            for _ in 0..last_poly_log_size {
                doublings.push(x);
                x = CirclePoint::<M31>::double_x(x);
            }

            pub fn fold<F: Field, E: ExtensionOf<F>>(values: &[E], folding_factors: &[F]) -> E {
                let n = values.len();
                assert_eq!(n, 1 << folding_factors.len());
                if n == 1 {
                    return values[0].into();
                }
                let (lhs_values, rhs_values) = values.split_at(n / 2);
                let (folding_factor, folding_factors) = folding_factors.split_first().unwrap();
                let lhs_val = fold(lhs_values, folding_factors);
                let rhs_val = fold(rhs_values, folding_factors);
                lhs_val + rhs_val * *folding_factor
            }

            let res = fold(&fiat_shamir_hints.last_layer_coeffs, &doublings);
            assert_eq!(*v, res);
        }

        Self {
            merkle_proofs: all_merkle_proofs,
            folded_intermediate_results: all_folded_intermediate_results,
        }
    }
}

#[derive(Debug, Clone)]
pub struct LastInnerLayersInputVar {
    pub cs: ConstraintSystemRef,
    pub merkle_proofs: BTreeMap<u32, Vec<LastSinglePairMerkleProofVar>>,
}

impl Var for LastInnerLayersInputVar {
    type Value = LastInnerLayersHints;

    fn cs(&self) -> ConstraintSystemRef {
        self.cs.clone()
    }
}

impl AllocVar for LastInnerLayersInputVar {
    fn new_variables(cs: &ConstraintSystemRef, value: &Self::Value, mode: AllocationMode) -> Self {
        let mut merkle_proofs = BTreeMap::new();
        for (log_size, proofs) in value.merkle_proofs.iter() {
            merkle_proofs.insert(
                *log_size,
                proofs
                    .iter()
                    .map(|v| LastSinglePairMerkleProofVar::new_variables(cs, v, mode))
                    .collect_vec(),
            );
        }

        Self {
            cs: cs.clone(),
            merkle_proofs,
        }
    }
}
