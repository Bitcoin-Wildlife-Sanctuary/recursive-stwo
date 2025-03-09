use circle_plonk_dsl_constraint_system::dvar::{AllocVar, AllocationMode, DVar};
use circle_plonk_dsl_constraint_system::ConstraintSystemRef;
use circle_plonk_dsl_fields::QM31Var;
use stwo_prover::core::pcs::TreeVec;
use stwo_prover::core::prover::StarkProof;
use stwo_prover::core::vcs::sha256_poseidon31_merkle::Sha256Poseidon31MerkleHasher;
use stwo_prover::core::ColumnVec;

#[derive(Debug, Clone)]
pub struct LastStarkProofVar {
    pub cs: ConstraintSystemRef,
    pub sampled_values: TreeVec<ColumnVec<Vec<QM31Var>>>,
}

impl DVar for LastStarkProofVar {
    type Value = StarkProof<Sha256Poseidon31MerkleHasher>;

    fn cs(&self) -> ConstraintSystemRef {
        self.cs.clone()
    }
}

impl AllocVar for LastStarkProofVar {
    fn new_variables(cs: &ConstraintSystemRef, value: &Self::Value, mode: AllocationMode) -> Self {
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

        Self {
            cs: cs.clone(),
            sampled_values,
        }
    }
}
