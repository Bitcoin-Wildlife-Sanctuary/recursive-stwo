use circle_plonk_dsl_channel::{ChannelVar, HashVar};
use circle_plonk_dsl_constraint_system::dvar::{AllocVar, AllocationMode, DVar};
use circle_plonk_dsl_constraint_system::ConstraintSystemRef;
use circle_plonk_dsl_fields::{M31Var, QM31Var};
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

impl DVar for PlonkWithPoseidonStatement0Var {
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
        channel.absorb_one_felt_and_permute(&QM31Var::from(&self.log_size_plonk));
        channel.absorb_one_felt_and_permute(&QM31Var::from(&self.log_size_poseidon))
    }
}

#[derive(Debug, Clone)]
pub struct PlonkWithPoseidonStatement1Var {
    pub plonk_total_sum: QM31Var,
    pub poseidon_total_sum: QM31Var,
}

impl DVar for PlonkWithPoseidonStatement1Var {
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
        channel.absorb_two_felts_and_permute(&self.plonk_total_sum, &self.poseidon_total_sum);
    }
}

#[derive(Debug, Clone)]
pub struct PlonkWithPoseidonProofVar {
    pub stmt0: PlonkWithPoseidonStatement0Var,
    pub stmt1: PlonkWithPoseidonStatement1Var,
    pub stark_proof: StarkProofVar,
}

impl DVar for PlonkWithPoseidonProofVar {
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
    pub last_poly: QM31Var,
}

impl DVar for FriProofVar {
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
        let last_poly = QM31Var::new_variables(cs, &value.last_layer_poly.coeffs[0], mode);

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

impl DVar for StarkProofVar {
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
pub struct PlonkWithAcceleratorLookupElementsVar {
    pub cs: ConstraintSystemRef,
    pub z: QM31Var,
    pub alpha: QM31Var,
    pub alpha_powers: [QM31Var; 9],
}

impl DVar for PlonkWithAcceleratorLookupElementsVar {
    type Value = PlonkWithAcceleratorLookupElements;

    fn cs(&self) -> ConstraintSystemRef {
        self.cs.clone()
    }
}

impl PlonkWithAcceleratorLookupElementsVar {
    pub fn draw(channel: &mut ChannelVar) -> Self {
        let cs = channel.cs();
        let [z, alpha] = channel.get_felts();

        let mut alpha_powers = Vec::with_capacity(9);
        alpha_powers.push(QM31Var::one(&cs));
        alpha_powers.push(alpha.clone());

        let mut cur = alpha.clone();
        for _ in 2..9 {
            cur = &cur * &alpha;
            alpha_powers.push(cur.clone());
        }

        let alpha_powers: [QM31Var; 9] = alpha_powers.try_into().unwrap();

        Self {
            cs,
            z,
            alpha,
            alpha_powers,
        }
    }
}
