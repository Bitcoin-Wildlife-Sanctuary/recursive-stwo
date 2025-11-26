use circle_plonk_dsl_constraint_system::var::{AllocVar, AllocationMode, Var};
use circle_plonk_dsl_constraint_system::ConstraintSystemRef;
use circle_plonk_dsl_hints::FiatShamirHints;
use merkle_proofs::{
    LastSinglePathMerkleProof, LastSinglePathMerkleProofInput, LastSinglePathMerkleProofInputVar,
    LastSinglePathMerkleProofVar,
};
use stwo::core::vcs::sha256_poseidon31_merkle::{
    Sha256Poseidon31MerkleChannel, Sha256Poseidon31MerkleHasher,
};
use stwo_examples::plonk_with_poseidon::air::PlonkWithPoseidonProof;

pub mod merkle_proofs;

#[derive(Debug, Clone)]
pub struct LastDecommitHints {
    pub precomputed_proofs: Vec<LastSinglePathMerkleProof>,
    pub trace_proofs: Vec<LastSinglePathMerkleProof>,
    pub interaction_proofs: Vec<LastSinglePathMerkleProof>,
    pub composition_proofs: Vec<LastSinglePathMerkleProof>,
}

impl LastDecommitHints {
    pub fn from_proof(
        fiat_shamir_hints: &FiatShamirHints<Sha256Poseidon31MerkleChannel>,
        proof: &PlonkWithPoseidonProof<Sha256Poseidon31MerkleHasher>,
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

            **v = LastSinglePathMerkleProof::from_stwo_proof(
                max_log_size,
                &fiat_shamir_hints
                    .unsorted_query_positions_per_log_size
                    .get(&max_log_size)
                    .unwrap(),
                &proof.stark_proof.queried_values[i],
                &fiat_shamir_hints.n_columns_per_log_size[i],
                &proof.stark_proof.decommitments[i],
            );
        }

        Self {
            precomputed_proofs,
            trace_proofs,
            interaction_proofs,
            composition_proofs,
        }
    }
}

#[derive(Clone)]
pub struct LastDecommitInput {
    pub precomputed_proofs: Vec<LastSinglePathMerkleProofInput>,
    pub trace_proofs: Vec<LastSinglePathMerkleProofInput>,
    pub interaction_proofs: Vec<LastSinglePathMerkleProofInput>,
    pub composition_proofs: Vec<LastSinglePathMerkleProofInput>,
}

impl LastDecommitInput {
    pub fn from_hints(hints: &LastDecommitHints) -> Self {
        let mut precomputed_proofs = vec![];
        let mut trace_proofs = vec![];
        let mut interaction_proofs = vec![];
        let mut composition_proofs = vec![];

        for v in hints.precomputed_proofs.iter() {
            precomputed_proofs.push(LastSinglePathMerkleProofInput::from_proof(v));
        }

        for v in hints.trace_proofs.iter() {
            trace_proofs.push(LastSinglePathMerkleProofInput::from_proof(v));
        }

        for v in hints.interaction_proofs.iter() {
            interaction_proofs.push(LastSinglePathMerkleProofInput::from_proof(v));
        }

        for v in hints.composition_proofs.iter() {
            composition_proofs.push(LastSinglePathMerkleProofInput::from_proof(v));
        }

        Self {
            precomputed_proofs,
            trace_proofs,
            interaction_proofs,
            composition_proofs,
        }
    }
}

#[derive(Debug, Clone)]
pub struct LastDecommitInputVar {
    pub cs: ConstraintSystemRef,
    pub precomputed_proofs: Vec<LastSinglePathMerkleProofInputVar>,
    pub trace_proofs: Vec<LastSinglePathMerkleProofInputVar>,
    pub interaction_proofs: Vec<LastSinglePathMerkleProofInputVar>,
    pub composition_proofs: Vec<LastSinglePathMerkleProofInputVar>,
}

impl Var for LastDecommitInputVar {
    type Value = LastDecommitInput;

    fn cs(&self) -> ConstraintSystemRef {
        self.cs.clone()
    }
}

impl AllocVar for LastDecommitInputVar {
    fn new_variables(cs: &ConstraintSystemRef, value: &Self::Value, mode: AllocationMode) -> Self {
        let mut precomputed_proofs = vec![];
        for proof in value.precomputed_proofs.iter() {
            precomputed_proofs.push(LastSinglePathMerkleProofInputVar::new_variables(
                cs, proof, mode,
            ));
        }

        let mut trace_proofs = vec![];
        for proof in value.trace_proofs.iter() {
            trace_proofs.push(LastSinglePathMerkleProofInputVar::new_variables(
                cs, proof, mode,
            ));
        }

        let mut interaction_proofs = vec![];
        for proof in value.interaction_proofs.iter() {
            interaction_proofs.push(LastSinglePathMerkleProofInputVar::new_variables(
                cs, proof, mode,
            ));
        }

        let mut composition_proofs = vec![];
        for proof in value.composition_proofs.iter() {
            composition_proofs.push(LastSinglePathMerkleProofInputVar::new_variables(
                cs, proof, mode,
            ));
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

#[derive(Debug, Clone)]
pub struct LastDecommitVar {
    pub cs: ConstraintSystemRef,
    pub precomputed_proofs: Vec<LastSinglePathMerkleProofVar>,
    pub trace_proofs: Vec<LastSinglePathMerkleProofVar>,
    pub interaction_proofs: Vec<LastSinglePathMerkleProofVar>,
    pub composition_proofs: Vec<LastSinglePathMerkleProofVar>,
}

impl LastDecommitVar {
    pub fn compute(input_var: &LastDecommitInputVar, hints: &LastDecommitHints) -> Self {
        let cs = input_var.cs();

        let mut precomputed_proofs = vec![];
        for (var, proof) in input_var
            .precomputed_proofs
            .iter()
            .zip(hints.precomputed_proofs.iter())
        {
            precomputed_proofs.push(LastSinglePathMerkleProofVar::from_proof_and_input(
                var, proof,
            ));
        }

        let mut trace_proofs = vec![];
        for (var, proof) in input_var.trace_proofs.iter().zip(hints.trace_proofs.iter()) {
            trace_proofs.push(LastSinglePathMerkleProofVar::from_proof_and_input(
                var, proof,
            ));
        }

        let mut interaction_proofs = vec![];
        for (var, proof) in input_var
            .interaction_proofs
            .iter()
            .zip(hints.interaction_proofs.iter())
        {
            interaction_proofs.push(LastSinglePathMerkleProofVar::from_proof_and_input(
                var, proof,
            ));
        }

        let mut composition_proofs = vec![];
        for (var, proof) in input_var
            .composition_proofs
            .iter()
            .zip(hints.composition_proofs.iter())
        {
            composition_proofs.push(LastSinglePathMerkleProofVar::from_proof_and_input(
                var, proof,
            ));
        }

        Self {
            cs,
            precomputed_proofs,
            trace_proofs,
            interaction_proofs,
            composition_proofs,
        }
    }
}
