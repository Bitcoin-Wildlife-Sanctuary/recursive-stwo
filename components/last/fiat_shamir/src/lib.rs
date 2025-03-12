use circle_plonk_dsl_channel::HashVar;
use circle_plonk_dsl_circle::CirclePointQM31Var;
use circle_plonk_dsl_constraint_system::dvar::{AllocVar, AllocationMode, DVar};
use circle_plonk_dsl_constraint_system::ConstraintSystemRef;
use circle_plonk_dsl_fields::QM31Var;
use circle_plonk_dsl_hints::FiatShamirHints;
use circle_plonk_dsl_last_data_structures::LastPlonkWithPoseidonProofVar;
use circle_plonk_dsl_merkle::Poseidon31MerkleHasherVar;
use itertools::Itertools;
use stwo_prover::core::fields::qm31::QM31;
use stwo_prover::core::vcs::poseidon31_hash::Poseidon31Hash;
use stwo_prover::core::vcs::poseidon31_merkle::Poseidon31MerkleHasher;
use stwo_prover::core::vcs::sha256_poseidon31_merkle::{
    Sha256Poseidon31MerkleChannel, Sha256Poseidon31MerkleHasher,
};
use stwo_prover::examples::plonk_with_poseidon::air::PlonkWithPoseidonProof;

#[derive(Clone, Debug)]
pub struct LastFiatShamirInput {
    pub t: QM31,
    pub sampled_values_hash: Poseidon31Hash,
    pub plonk_total_sum: QM31,
    pub poseidon_total_sum: QM31,
}

impl LastFiatShamirInput {
    pub fn from_proof(
        proof: &PlonkWithPoseidonProof<Sha256Poseidon31MerkleHasher>,
        fiat_shamir_hints: &FiatShamirHints<Sha256Poseidon31MerkleChannel>,
    ) -> Self {
        let sampled_values = proof.stark_proof.sampled_values.clone().flatten_cols();
        let elems = sampled_values
            .iter()
            .flat_map(|v| v.to_m31_array())
            .collect_vec();
        let sampled_values_hash = Poseidon31MerkleHasher::hash_column_get_rate(&elems);
        let plonk_total_sum = proof.stmt1.plonk_total_sum.clone();
        let poseidon_total_sum = proof.stmt1.poseidon_total_sum.clone();
        Self {
            t: fiat_shamir_hints.oods_t,
            sampled_values_hash,
            plonk_total_sum,
            poseidon_total_sum,
        }
    }
}

#[derive(Clone, Debug)]
pub struct LastFiatShamirInputVar {
    pub t: QM31Var,
    pub sampled_values_hash: HashVar,
    pub plonk_total_sum: QM31Var,
    pub poseidon_total_sum: QM31Var,
}

impl DVar for LastFiatShamirInputVar {
    type Value = LastFiatShamirInput;

    fn cs(&self) -> ConstraintSystemRef {
        self.t.cs().and(&self.sampled_values_hash.cs())
    }
}

impl AllocVar for LastFiatShamirInputVar {
    fn new_variables(cs: &ConstraintSystemRef, value: &Self::Value, mode: AllocationMode) -> Self {
        let t = QM31Var::new_variables(cs, &value.t, mode);
        let sampled_values_hash = HashVar::new_variables(cs, &value.sampled_values_hash.0, mode);
        let plonk_total_sum = QM31Var::new_variables(cs, &value.plonk_total_sum, mode);
        let poseidon_total_sum = QM31Var::new_variables(cs, &value.poseidon_total_sum, mode);
        Self {
            t,
            sampled_values_hash,
            plonk_total_sum,
            poseidon_total_sum,
        }
    }
}

pub struct LastFiatShamirResults {
    pub oods_point: CirclePointQM31Var,
}

impl LastFiatShamirResults {
    pub fn compute(
        proof_var: &LastPlonkWithPoseidonProofVar,
        last_fiat_shamir_input_var: &LastFiatShamirInputVar,
    ) -> LastFiatShamirResults {
        let oods_point = CirclePointQM31Var::from_t(&&last_fiat_shamir_input_var.t);
        let sampled_values_flattened = proof_var.stark_proof.sampled_values.clone().flatten_cols();
        let sampled_values_hash =
            Poseidon31MerkleHasherVar::hash_qm31_columns_get_rate(&sampled_values_flattened);
        sampled_values_hash.equalverify(&last_fiat_shamir_input_var.sampled_values_hash);

        LastFiatShamirResults { oods_point }
    }
}

#[cfg(test)]
mod test {
    use crate::{LastFiatShamirInput, LastFiatShamirInputVar, LastFiatShamirResults};
    use circle_plonk_dsl_constraint_system::dvar::AllocVar;
    use circle_plonk_dsl_constraint_system::ConstraintSystemRef;
    use circle_plonk_dsl_hints::FiatShamirHints;
    use circle_plonk_dsl_last_data_structures::LastPlonkWithPoseidonProofVar;
    use num_traits::One;
    use stwo_prover::core::fields::qm31::QM31;
    use stwo_prover::core::fri::FriConfig;
    use stwo_prover::core::pcs::PcsConfig;
    use stwo_prover::core::vcs::sha256_merkle::Sha256MerkleChannel;
    use stwo_prover::core::vcs::sha256_poseidon31_merkle::{
        Sha256Poseidon31MerkleChannel, Sha256Poseidon31MerkleHasher,
    };
    use stwo_prover::examples::plonk_with_poseidon::air::{
        verify_plonk_with_poseidon, PlonkWithPoseidonProof,
    };
    use stwo_prover::examples::plonk_without_poseidon::air::{
        prove_plonk_without_poseidon, verify_plonk_without_poseidon,
    };

    #[test]
    fn test_last_fiat_shamir() {
        let proof: PlonkWithPoseidonProof<Sha256Poseidon31MerkleHasher> =
            bincode::deserialize(include_bytes!("../../../test_data/hybrid_hash.bin")).unwrap();
        let config = PcsConfig {
            pow_bits: 28,
            fri_config: FriConfig::new(0, 9, 8),
        };

        verify_plonk_with_poseidon::<Sha256Poseidon31MerkleChannel>(
            proof.clone(),
            config,
            &[
                (1, QM31::one()),
                (2, QM31::from_u32_unchecked(0, 1, 0, 0)),
                (3, QM31::from_u32_unchecked(0, 0, 1, 0)),
            ],
        )
        .unwrap();

        let cs = ConstraintSystemRef::new_plonk_without_poseidon_ref();

        let fiat_shamir_hints = FiatShamirHints::<Sha256Poseidon31MerkleChannel>::new(
            &proof,
            config,
            &[
                (1, QM31::one()),
                (2, QM31::from_u32_unchecked(0, 1, 0, 0)),
                (3, QM31::from_u32_unchecked(0, 0, 1, 0)),
            ],
        );
        let fiat_shamir_input = LastFiatShamirInput::from_proof(&proof, &fiat_shamir_hints);
        let fiat_shamir_input_var =
            LastFiatShamirInputVar::new_public_input(&cs, &fiat_shamir_input);
        let proof_var = LastPlonkWithPoseidonProofVar::new_witness(&cs, &proof);

        let _res = LastFiatShamirResults::compute(&proof_var, &fiat_shamir_input_var);

        cs.pad();
        cs.check_arithmetics();
        cs.populate_logup_arguments();

        let config = PcsConfig {
            pow_bits: 20,
            fri_config: FriConfig::new(0, 5, 16),
        };

        let circuit = cs.generate_plonk_without_poseidon_circuit();
        let proof = prove_plonk_without_poseidon::<Sha256MerkleChannel>(config, &circuit);
        verify_plonk_without_poseidon::<Sha256MerkleChannel>(
            proof,
            config,
            &[
                (1, QM31::one()),
                (2, QM31::from_u32_unchecked(0, 1, 0, 0)),
                (3, QM31::from_u32_unchecked(0, 0, 1, 0)),
                (4, fiat_shamir_input.t),
                (
                    5,
                    QM31::from_m31_array(std::array::from_fn(|i| {
                        fiat_shamir_input.sampled_values_hash.0[i]
                    })),
                ),
                (
                    6,
                    QM31::from_m31_array(std::array::from_fn(|i| {
                        fiat_shamir_input.sampled_values_hash.0[i + 4]
                    })),
                ),
            ],
        )
        .unwrap();
    }
}
