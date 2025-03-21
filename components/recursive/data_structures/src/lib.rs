use circle_plonk_dsl_bits::BitsVar;
use circle_plonk_dsl_channel::{ChannelVar, HashVar};
use circle_plonk_dsl_constraint_system::var::{AllocVar, AllocationMode, Var};
use circle_plonk_dsl_constraint_system::ConstraintSystemRef;
use circle_plonk_dsl_fields::{M31Var, QM31Var};
use circle_plonk_dsl_hints::{DecommitHints, SinglePairMerkleProof, SinglePathMerkleProof};
use circle_plonk_dsl_line::LinePolyVar;
use circle_plonk_dsl_merkle::Poseidon31MerkleHasherVar;
use std::collections::BTreeMap;
use stwo_prover::core::fields::m31::M31;
use stwo_prover::core::fri::FriProof;
use stwo_prover::core::pcs::TreeVec;
use stwo_prover::core::prover::StarkProof;
use stwo_prover::core::vcs::poseidon31_merkle::Poseidon31MerkleHasher;
use stwo_prover::core::ColumnVec;
use stwo_prover::examples::plonk_with_poseidon::air::{
    PlonkWithPoseidonProof, PlonkWithPoseidonStatement0, PlonkWithPoseidonStatement1,
};
use stwo_prover::examples::plonk_with_poseidon::plonk::PlonkWithAcceleratorLookupElements;

#[derive(Debug, Clone)]
pub struct PlonkWithPoseidonStatement0Var {
    pub log_size_plonk: M31Var,
    pub log_size_poseidon: M31Var,
}

impl Var for PlonkWithPoseidonStatement0Var {
    type Value = PlonkWithPoseidonStatement0;

    fn cs(&self) -> ConstraintSystemRef {
        self.log_size_plonk.cs().and(&self.log_size_poseidon.cs)
    }
}

impl AllocVar for PlonkWithPoseidonStatement0Var {
    fn new_variables(cs: &ConstraintSystemRef, value: &Self::Value, mode: AllocationMode) -> Self {
        assert!(value.log_size_plonk < (1 << 22));
        assert!(value.log_size_poseidon < (1 << 22));

        let log_size_plonk = M31Var::new_variables(cs, &M31::from(value.log_size_plonk), mode);
        let log_size_poseidon =
            M31Var::new_variables(cs, &M31::from(value.log_size_poseidon), mode);

        Self {
            log_size_plonk,
            log_size_poseidon,
        }
    }
}

impl PlonkWithPoseidonStatement0Var {
    pub fn mix_into(&self, channel: &mut ChannelVar) {
        channel.mix_one_felt(&QM31Var::from(&self.log_size_plonk));
        channel.mix_one_felt(&QM31Var::from(&self.log_size_poseidon))
    }
}

#[derive(Debug, Clone)]
pub struct PlonkWithPoseidonStatement1Var {
    pub plonk_total_sum: QM31Var,
    pub poseidon_total_sum: QM31Var,
}

impl Var for PlonkWithPoseidonStatement1Var {
    type Value = PlonkWithPoseidonStatement1;

    fn cs(&self) -> ConstraintSystemRef {
        self.plonk_total_sum.cs().and(&self.poseidon_total_sum.cs())
    }
}

impl AllocVar for PlonkWithPoseidonStatement1Var {
    fn new_variables(cs: &ConstraintSystemRef, value: &Self::Value, mode: AllocationMode) -> Self {
        let plonk_total_sum = QM31Var::new_variables(cs, &value.plonk_total_sum, mode);
        let poseidon_total_sum = QM31Var::new_variables(cs, &value.poseidon_total_sum, mode);

        Self {
            plonk_total_sum,
            poseidon_total_sum,
        }
    }
}

impl PlonkWithPoseidonStatement1Var {
    pub fn mix_into(&self, channel: &mut ChannelVar) {
        channel.mix_two_felts(&self.plonk_total_sum, &self.poseidon_total_sum);
    }
}

#[derive(Debug, Clone)]
pub struct PlonkWithPoseidonProofVar {
    pub stmt0: PlonkWithPoseidonStatement0Var,
    pub stmt1: PlonkWithPoseidonStatement1Var,
    pub stark_proof: StarkProofVar,
}

impl Var for PlonkWithPoseidonProofVar {
    type Value = PlonkWithPoseidonProof<Poseidon31MerkleHasher>;

    fn cs(&self) -> ConstraintSystemRef {
        self.stmt0
            .cs()
            .and(&self.stmt1.cs())
            .and(&self.stark_proof.cs())
    }
}

impl AllocVar for PlonkWithPoseidonProofVar {
    fn new_variables(cs: &ConstraintSystemRef, value: &Self::Value, mode: AllocationMode) -> Self {
        let stmt0 = PlonkWithPoseidonStatement0Var::new_variables(cs, &value.stmt0, mode);
        let stmt1 = PlonkWithPoseidonStatement1Var::new_variables(cs, &value.stmt1, mode);
        let stark_proof = StarkProofVar::new_variables(cs, &value.stark_proof, mode);

        Self {
            stmt0,
            stmt1,
            stark_proof,
        }
    }
}

#[derive(Debug, Clone)]
pub struct FriProofVar {
    pub cs: ConstraintSystemRef,
    pub first_layer_commitment: HashVar,
    pub inner_layer_commitments: Vec<HashVar>,
    pub last_poly: LinePolyVar,
}

impl Var for FriProofVar {
    type Value = FriProof<Poseidon31MerkleHasher>;

    fn cs(&self) -> ConstraintSystemRef {
        self.cs.clone()
    }
}

impl AllocVar for FriProofVar {
    fn new_variables(cs: &ConstraintSystemRef, value: &Self::Value, mode: AllocationMode) -> Self {
        let first_layer_commitment =
            HashVar::new_variables(cs, &value.first_layer.commitment.0, mode);
        let mut inner_layer_commitments = vec![];
        for layer in value.inner_layers.iter() {
            inner_layer_commitments.push(HashVar::new_variables(cs, &layer.commitment.0, mode));
        }
        let last_poly = LinePolyVar::new_variables(cs, &value.last_layer_poly, mode);

        Self {
            cs: cs.clone(),
            first_layer_commitment,
            inner_layer_commitments,
            last_poly,
        }
    }
}

#[derive(Debug, Clone)]
pub struct StarkProofVar {
    pub cs: ConstraintSystemRef,

    pub commitments: Vec<HashVar>,
    pub sampled_values: TreeVec<ColumnVec<Vec<QM31Var>>>,
    pub fri_proof: FriProofVar,
    pub proof_of_work: [M31Var; 3],
}

impl Var for StarkProofVar {
    type Value = StarkProof<Poseidon31MerkleHasher>;

    fn cs(&self) -> ConstraintSystemRef {
        self.cs.clone()
    }
}

impl AllocVar for StarkProofVar {
    fn new_variables(cs: &ConstraintSystemRef, value: &Self::Value, mode: AllocationMode) -> Self {
        let mut commitments = Vec::with_capacity(value.commitments.len());
        for commitment in value.commitments.iter() {
            commitments.push(HashVar::new_variables(cs, &commitment.0, mode));
        }

        let mut sampled_values = TreeVec::new(vec![]);
        for round in value.sampled_values.iter() {
            let mut round_res = ColumnVec::new();
            for column in round.iter() {
                let mut column_res = Vec::with_capacity(column.len());
                for eval in column.iter() {
                    column_res.push(QM31Var::new_variables(cs, eval, mode));
                }
                round_res.push(column_res);
            }
            sampled_values.push(round_res);
        }

        let fri_proof = FriProofVar::new_variables(cs, &value.fri_proof, mode);

        let proof_of_work = [
            M31Var::new_variables(
                cs,
                &M31::from((value.proof_of_work % ((1 << 22) - 1)) as u32),
                mode,
            ),
            M31Var::new_variables(
                cs,
                &M31::from(((value.proof_of_work >> 22) & ((1 << 21) - 1)) as u32),
                mode,
            ),
            M31Var::new_variables(
                cs,
                &M31::from(((value.proof_of_work >> 43) & ((1 << 21) - 1)) as u32),
                mode,
            ),
        ];

        Self {
            cs: cs.clone(),
            commitments,
            sampled_values,
            fri_proof,
            proof_of_work,
        }
    }
}

#[derive(Debug, Clone)]
pub struct LookupElementsVar {
    pub cs: ConstraintSystemRef,
    pub z: QM31Var,
    pub alpha: QM31Var,
    pub alpha_powers: [QM31Var; 3],
}

impl Var for LookupElementsVar {
    type Value = PlonkWithAcceleratorLookupElements;

    fn cs(&self) -> ConstraintSystemRef {
        self.cs.clone()
    }
}

impl LookupElementsVar {
    pub fn draw(channel: &mut ChannelVar) -> Self {
        let [z, alpha] = channel.draw_felts();
        Self::from_z_and_alpha(z, alpha)
    }

    pub fn from_z_and_alpha(z: QM31Var, alpha: QM31Var) -> Self {
        let cs = z.cs().and(&alpha.cs());

        let mut alpha_powers = Vec::with_capacity(3);
        alpha_powers.push(QM31Var::one(&cs));
        alpha_powers.push(alpha.clone());

        let mut cur = alpha.clone();
        for _ in 2..3 {
            cur = &cur * &alpha;
            alpha_powers.push(cur.clone());
        }

        let alpha_powers: [QM31Var; 3] = alpha_powers.try_into().unwrap();

        Self {
            cs,
            z,
            alpha,
            alpha_powers,
        }
    }
}

#[derive(Debug, Clone)]
pub struct SinglePathMerkleProofVar {
    pub cs: ConstraintSystemRef,
    pub value: SinglePathMerkleProof,
    pub sibling_hashes: Vec<HashVar>,
    pub columns: BTreeMap<usize, Vec<M31Var>>,
}

impl Var for SinglePathMerkleProofVar {
    type Value = SinglePathMerkleProof;

    fn cs(&self) -> ConstraintSystemRef {
        self.cs.clone()
    }
}

impl SinglePathMerkleProofVar {
    pub fn new(cs: &ConstraintSystemRef, value: &SinglePathMerkleProof) -> Self {
        let mut sibling_hashes = vec![];
        for sibling_hash in value.sibling_hashes.iter() {
            sibling_hashes.push(HashVar::new_single_use_witness_only(&cs, &sibling_hash.0));
        }

        let mut columns = BTreeMap::new();
        for (k, v) in value.columns.iter() {
            let mut v_var = vec![];
            for vv in v.iter() {
                v_var.push(M31Var::new_witness(&cs, vv));
            }
            columns.insert(*k, v_var);
        }

        Self {
            cs: cs.clone(),
            value: value.clone(),
            sibling_hashes,
            columns,
        }
    }

    pub fn get_values(&self) -> &BTreeMap<usize, Vec<M31Var>> {
        &self.columns
    }

    pub fn verify(&mut self, root: &HashVar, query: &BitsVar) {
        // verify that the Merkle proof is valid
        self.value.verify();
        assert_eq!(root.value(), self.value.root.0);
        assert_eq!(query.get_value().0, self.value.query as u32);

        let mut cur_hash = Poseidon31MerkleHasherVar::hash_m31_columns_get_rate(
            &self.columns.get(&self.value.depth).unwrap_or(&vec![]),
        );

        for i in 0..self.value.depth {
            let h = self.value.depth - i - 1;

            if self.columns.contains_key(&h) {
                let mut column_hash = Poseidon31MerkleHasherVar::hash_m31_columns_get_capacity(
                    &self.columns.get(&h).unwrap_or(&vec![]),
                );
                cur_hash = Poseidon31MerkleHasherVar::hash_tree_with_column_hash_with_swap(
                    &mut cur_hash,
                    &mut self.sibling_hashes[i],
                    query.value[i],
                    query.variables[i],
                    &mut column_hash,
                );
            } else {
                cur_hash = Poseidon31MerkleHasherVar::hash_tree_with_swap(
                    &mut cur_hash,
                    &mut self.sibling_hashes[i],
                    query.value[i],
                    query.variables[i],
                );
            }
        }

        assert_eq!(cur_hash.value(), root.value());

        // check that the left_variable and right_variable are the same
        // as though in self.root
        cur_hash.equalverify(&root);
    }
}

#[derive(Clone)]
pub struct SinglePairMerkleProofVar {
    pub cs: ConstraintSystemRef,
    pub value: SinglePairMerkleProof,
    pub sibling_hashes: Vec<HashVar>,
    pub self_columns: BTreeMap<usize, QM31Var>,
    pub siblings_columns: BTreeMap<usize, QM31Var>,
}

impl Var for SinglePairMerkleProofVar {
    type Value = SinglePairMerkleProof;

    fn cs(&self) -> ConstraintSystemRef {
        self.cs.clone()
    }
}

impl SinglePairMerkleProofVar {
    pub fn new(cs: &ConstraintSystemRef, value: &SinglePairMerkleProof) -> Self {
        let mut sibling_hashes = vec![];
        for sibling_hash in value.sibling_hashes.iter() {
            sibling_hashes.push(HashVar::new_single_use_witness_only(&cs, &sibling_hash.0));
        }

        let mut self_columns = BTreeMap::new();
        for (k, v) in value.self_columns.iter() {
            self_columns.insert(*k, QM31Var::new_witness(&cs, &v));
        }

        let mut siblings_columns = BTreeMap::new();
        for (k, v) in value.siblings_columns.iter() {
            siblings_columns.insert(*k, QM31Var::new_witness(&cs, &v));
        }

        Self {
            cs: cs.clone(),
            value: value.clone(),
            sibling_hashes,
            self_columns,
            siblings_columns,
        }
    }

    pub fn verify(&mut self, root: &HashVar, query: &BitsVar) {
        // verify that the Merkle proof is valid
        self.value.verify();
        assert_eq!(root.value(), self.value.root.0);
        assert_eq!(query.get_value().0, self.value.query as u32);

        let cs = self.cs().and(&root.cs()).and(&query.cs());

        let mut self_hash = Poseidon31MerkleHasherVar::hash_qm31_columns_get_rate(&[
            self.self_columns.get(&self.value.depth).unwrap().clone(),
            QM31Var::zero(&cs),
        ]);
        let mut sibling_hash = Poseidon31MerkleHasherVar::hash_qm31_columns_get_rate(&[
            self.siblings_columns
                .get(&self.value.depth)
                .unwrap()
                .clone(),
            QM31Var::zero(&cs),
        ]);

        for i in 0..self.value.depth {
            let h = self.value.depth - i - 1;

            if !self.self_columns.contains_key(&h) {
                self_hash = Poseidon31MerkleHasherVar::hash_tree_with_swap(
                    &mut self_hash,
                    &mut sibling_hash,
                    query.value[i],
                    query.variables[i],
                );
                if i != self.value.depth - 1 {
                    sibling_hash = self.sibling_hashes[i].clone();
                }
            } else {
                let mut self_column_hash =
                    Poseidon31MerkleHasherVar::hash_qm31_columns_get_capacity(&[
                        self.self_columns.get(&h).unwrap().clone(),
                        QM31Var::zero(&cs),
                    ]);
                let mut sibling_column_hash =
                    Poseidon31MerkleHasherVar::hash_qm31_columns_get_capacity(&[
                        self.siblings_columns.get(&h).unwrap().clone(),
                        QM31Var::zero(&cs),
                    ]);

                self_hash = Poseidon31MerkleHasherVar::hash_tree_with_column_hash_with_swap(
                    &mut self_hash,
                    &mut sibling_hash,
                    query.value[i],
                    query.variables[i],
                    &mut self_column_hash,
                );
                sibling_hash = Poseidon31MerkleHasherVar::combine_hash_tree_with_column(
                    &mut self.sibling_hashes[i],
                    &mut sibling_column_hash,
                );
            }
        }

        assert_eq!(self_hash.value(), root.value());

        // check that the left_variable and right_variable are the same
        // as though in self.root
        self_hash.equalverify(&root);
    }
}

#[derive(Debug, Clone)]
pub struct DecommitmentVar {
    pub cs: ConstraintSystemRef,
    pub precomputed_proofs: Vec<SinglePathMerkleProofVar>,
    pub trace_proofs: Vec<SinglePathMerkleProofVar>,
    pub interaction_proofs: Vec<SinglePathMerkleProofVar>,
    pub composition_proofs: Vec<SinglePathMerkleProofVar>,
}

impl Var for DecommitmentVar {
    type Value = DecommitHints;

    fn cs(&self) -> ConstraintSystemRef {
        self.cs.clone()
    }
}

impl DecommitmentVar {
    pub fn new(cs: &ConstraintSystemRef, value: &DecommitHints) -> Self {
        let mut precomputed_proofs = vec![];
        for proof in value.precomputed_proofs.iter() {
            precomputed_proofs.push(SinglePathMerkleProofVar::new(cs, proof));
        }

        let mut trace_proofs = vec![];
        for proof in value.trace_proofs.iter() {
            trace_proofs.push(SinglePathMerkleProofVar::new(cs, proof));
        }

        let mut interaction_proofs = vec![];
        for proof in value.interaction_proofs.iter() {
            interaction_proofs.push(SinglePathMerkleProofVar::new(cs, proof));
        }

        let mut composition_proofs = vec![];
        for proof in value.composition_proofs.iter() {
            composition_proofs.push(SinglePathMerkleProofVar::new(cs, proof));
        }

        Self {
            cs: cs.clone(),
            precomputed_proofs,
            trace_proofs,
            interaction_proofs,
            composition_proofs,
        }
    }
}

#[cfg(test)]
mod test {
    use crate::{SinglePairMerkleProofVar, SinglePathMerkleProofVar};
    use circle_plonk_dsl_bits::BitsVar;
    use circle_plonk_dsl_channel::HashVar;
    use circle_plonk_dsl_constraint_system::var::AllocVar;
    use circle_plonk_dsl_constraint_system::ConstraintSystemRef;
    use circle_plonk_dsl_fields::M31Var;
    use circle_plonk_dsl_hints::{
        AnswerHints, FiatShamirHints, FirstLayerHints, SinglePathMerkleProof,
    };
    use num_traits::One;
    use stwo_prover::core::fields::m31::M31;
    use stwo_prover::core::fields::qm31::QM31;
    use stwo_prover::core::fri::FriConfig;
    use stwo_prover::core::pcs::PcsConfig;
    use stwo_prover::core::vcs::poseidon31_merkle::{
        Poseidon31MerkleChannel, Poseidon31MerkleHasher,
    };
    use stwo_prover::examples::plonk_with_poseidon::air::PlonkWithPoseidonProof;

    #[test]
    fn test_merkle_path_proof() {
        let proof: PlonkWithPoseidonProof<Poseidon31MerkleHasher> =
            bincode::deserialize(include_bytes!("../../../test_data/small_proof.bin")).unwrap();
        let config = PcsConfig {
            pow_bits: 20,
            fri_config: FriConfig::new(2, 5, 16),
        };

        let fiat_shamir_hints =
            FiatShamirHints::<Poseidon31MerkleChannel>::new(&proof, config, &[(1, QM31::one())]);

        let max_log_size = *fiat_shamir_hints.n_columns_per_log_size[0]
            .keys()
            .max()
            .unwrap();
        let proofs = SinglePathMerkleProof::from_stwo_proof(
            max_log_size,
            &fiat_shamir_hints
                .sorted_query_positions_per_log_size
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

        let cs = ConstraintSystemRef::new_plonk_with_poseidon_ref();
        let root = HashVar::new_witness(&cs, &proof.stark_proof.commitments[0].0);
        for proof in proofs.iter() {
            let mut proof_var = SinglePathMerkleProofVar::new(&cs, proof);
            let query = M31Var::new_witness(&cs, &M31::from(proof.query));
            let query_bits = BitsVar::from_m31(&query, proof.depth);
            proof_var.verify(&root, &query_bits);
        }
    }

    #[test]
    fn test_merkle_pair_proof() {
        let proof: PlonkWithPoseidonProof<Poseidon31MerkleHasher> =
            bincode::deserialize(include_bytes!("../../../test_data/small_proof.bin")).unwrap();
        let config = PcsConfig {
            pow_bits: 20,
            fri_config: FriConfig::new(2, 5, 16),
        };

        let fiat_shamir_hints = FiatShamirHints::new(&proof, config, &[(1, QM31::one())]);
        let answer_hints = AnswerHints::compute(&fiat_shamir_hints, &proof);
        let first_layer_hints = FirstLayerHints::compute(&fiat_shamir_hints, &answer_hints, &proof);
        for proof in first_layer_hints.merkle_proofs.iter() {
            proof.verify();
        }

        let cs = ConstraintSystemRef::new_plonk_with_poseidon_ref();
        let root = HashVar::new_witness(&cs, &proof.stark_proof.fri_proof.first_layer.commitment.0);
        for proof in first_layer_hints.merkle_proofs.iter() {
            let mut proof_var = SinglePairMerkleProofVar::new(&cs, proof);
            let query = M31Var::new_witness(&cs, &M31::from(proof.query));
            let query_bits = BitsVar::from_m31(&query, proof.depth);
            proof_var.verify(&root, &query_bits);
        }
    }
}
