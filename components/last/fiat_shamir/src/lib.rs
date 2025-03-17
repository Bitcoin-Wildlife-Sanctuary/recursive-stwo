use circle_plonk_dsl_channel::HashVar;
use circle_plonk_dsl_circle::CirclePointQM31Var;
use circle_plonk_dsl_constraint_system::dvar::{AllocVar, AllocationMode, DVar};
use circle_plonk_dsl_constraint_system::ConstraintSystemRef;
use circle_plonk_dsl_data_structures::LookupElementsVar;
use circle_plonk_dsl_fields::{M31Var, QM31Var};
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
    pub lookup_element_z: QM31,
    pub lookup_element_alpha: QM31,
    pub random_coeff: QM31,
    pub after_sampled_values_random_coeff: QM31,
    pub queries_at_max_first_layer_column_log_size: Vec<usize>,
    pub fri_alphas: Vec<QM31>,
}

impl LastFiatShamirInput {
    pub fn from_proof(
        proof: &PlonkWithPoseidonProof<Sha256Poseidon31MerkleHasher>,
        fiat_shamir_hints: &FiatShamirHints<Sha256Poseidon31MerkleChannel>,
    ) -> Self {
        let t = fiat_shamir_hints.oods_t;
        let sampled_values = proof.stark_proof.sampled_values.clone().flatten_cols();
        let elems = sampled_values
            .iter()
            .flat_map(|v| v.to_m31_array())
            .collect_vec();
        let sampled_values_hash = Poseidon31MerkleHasher::hash_column_get_rate(&elems);
        let plonk_total_sum = proof.stmt1.plonk_total_sum;
        let poseidon_total_sum = proof.stmt1.poseidon_total_sum;
        let lookup_element_z = fiat_shamir_hints.z;
        let lookup_element_alpha = fiat_shamir_hints.alpha;
        let random_coeff = fiat_shamir_hints.random_coeff;
        let after_sampled_values_random_coeff = fiat_shamir_hints.after_sampled_values_random_coeff;
        let queries_at_max_first_layer_column_log_size = fiat_shamir_hints
            .unsorted_query_positions_per_log_size
            [&fiat_shamir_hints.max_first_layer_column_log_size]
            .clone();
        let fri_alphas = fiat_shamir_hints.fri_alphas.clone();
        Self {
            t,
            sampled_values_hash,
            plonk_total_sum,
            poseidon_total_sum,
            lookup_element_z,
            lookup_element_alpha,
            random_coeff,
            after_sampled_values_random_coeff,
            queries_at_max_first_layer_column_log_size,
            fri_alphas,
        }
    }
}

#[derive(Clone, Debug)]
pub struct LastFiatShamirInputVar {
    pub cs: ConstraintSystemRef,
    pub t: QM31Var,
    pub sampled_values_hash: HashVar,
    pub plonk_total_sum: QM31Var,
    pub poseidon_total_sum: QM31Var,
    pub lookup_element_z: QM31Var,
    pub lookup_element_alpha: QM31Var,
    pub random_coeff: QM31Var,
    pub after_sampled_values_random_coeff: QM31Var,
    pub queries_len: usize,
    pub packed_queries_at_max_first_layer_column_log_size: Vec<QM31Var>,
    pub fri_alphas: Vec<QM31Var>,
}

impl DVar for LastFiatShamirInputVar {
    type Value = LastFiatShamirInput;

    fn cs(&self) -> ConstraintSystemRef {
        self.cs.clone()
    }
}

impl AllocVar for LastFiatShamirInputVar {
    fn new_variables(cs: &ConstraintSystemRef, value: &Self::Value, mode: AllocationMode) -> Self {
        let t = QM31Var::new_variables(cs, &value.t, mode);
        let sampled_values_hash = HashVar::new_variables(cs, &value.sampled_values_hash.0, mode);
        let plonk_total_sum = QM31Var::new_variables(cs, &value.plonk_total_sum, mode);
        let poseidon_total_sum = QM31Var::new_variables(cs, &value.poseidon_total_sum, mode);
        let lookup_element_z = QM31Var::new_variables(cs, &value.lookup_element_z, mode);
        let lookup_element_alpha = QM31Var::new_variables(cs, &value.lookup_element_alpha, mode);
        let random_coeff = QM31Var::new_variables(cs, &value.random_coeff, mode);
        let after_sampled_values_random_coeff =
            QM31Var::new_variables(cs, &value.after_sampled_values_random_coeff, mode);

        let mut packed_queries_at_max_first_layer_column_log_size = vec![];
        let queries_len = value.queries_at_max_first_layer_column_log_size.len();
        for chunk in value.queries_at_max_first_layer_column_log_size.chunks(4) {
            let mut chunk = chunk.to_vec();
            chunk.resize(4, 0);

            let elem = QM31::from_u32_unchecked(
                chunk[0] as u32,
                chunk[1] as u32,
                chunk[2] as u32,
                chunk[3] as u32,
            );

            packed_queries_at_max_first_layer_column_log_size
                .push(QM31Var::new_variables(cs, &elem, mode));
        }

        let mut fri_alphas = vec![];
        for fri_alpha in value.fri_alphas.iter() {
            fri_alphas.push(QM31Var::new_variables(cs, &fri_alpha, mode));
        }

        Self {
            cs: cs.clone(),
            t,
            sampled_values_hash,
            plonk_total_sum,
            poseidon_total_sum,
            lookup_element_z,
            lookup_element_alpha,
            random_coeff,
            after_sampled_values_random_coeff,
            queries_len,
            packed_queries_at_max_first_layer_column_log_size,
            fri_alphas,
        }
    }
}

pub struct LastFiatShamirResults {
    pub oods_point: CirclePointQM31Var,
    pub plonk_total_sum: QM31Var,
    pub poseidon_total_sum: QM31Var,
    pub lookup_elements: LookupElementsVar,
    pub random_coeff: QM31Var,
    pub after_sampled_values_random_coeff: QM31Var,
    pub queries_at_max_first_layer_column_log_size: Vec<M31Var>,
    pub fri_alphas: Vec<QM31Var>,
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
        let lookup_elements = LookupElementsVar::from_z_and_alpha(
            last_fiat_shamir_input_var.lookup_element_z.clone(),
            last_fiat_shamir_input_var.lookup_element_alpha.clone(),
        );
        let mut queries_at_max_first_layer_column_log_size = vec![];
        for packed in last_fiat_shamir_input_var
            .packed_queries_at_max_first_layer_column_log_size
            .iter()
        {
            queries_at_max_first_layer_column_log_size.extend_from_slice(&packed.decompose_m31());
        }
        queries_at_max_first_layer_column_log_size.truncate(last_fiat_shamir_input_var.queries_len);

        LastFiatShamirResults {
            oods_point,
            plonk_total_sum: last_fiat_shamir_input_var.plonk_total_sum.clone(),
            poseidon_total_sum: last_fiat_shamir_input_var.poseidon_total_sum.clone(),
            lookup_elements,
            random_coeff: last_fiat_shamir_input_var.random_coeff.clone(),
            after_sampled_values_random_coeff: last_fiat_shamir_input_var
                .after_sampled_values_random_coeff
                .clone(),
            queries_at_max_first_layer_column_log_size,
            fri_alphas: last_fiat_shamir_input_var.fri_alphas.clone(),
        }
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

        let pack_queries = |slice: &[usize]| {
            let mut slice = slice.to_vec();
            assert!(slice.len() <= 4);
            slice.resize(4, 0);
            QM31::from_u32_unchecked(
                slice[0] as u32,
                slice[1] as u32,
                slice[2] as u32,
                slice[3] as u32,
            )
        };

        let mut inputs = vec![];
        let add_input = |inputs: &mut Vec<(usize, QM31)>, input: QM31| {
            let idx = inputs.len() + 1;
            inputs.push((idx, input))
        };

        add_input(&mut inputs, QM31::one());
        add_input(&mut inputs, QM31::from_u32_unchecked(0, 1, 0, 0));
        add_input(&mut inputs, QM31::from_u32_unchecked(0, 0, 1, 0));
        add_input(&mut inputs, fiat_shamir_input.t);
        add_input(
            &mut inputs,
            QM31::from_m31_array(std::array::from_fn(|i| {
                fiat_shamir_input.sampled_values_hash.0[i]
            })),
        );
        add_input(
            &mut inputs,
            QM31::from_m31_array(std::array::from_fn(|i| {
                fiat_shamir_input.sampled_values_hash.0[i + 4]
            })),
        );
        add_input(&mut inputs, fiat_shamir_input.plonk_total_sum);
        add_input(&mut inputs, fiat_shamir_input.poseidon_total_sum);
        add_input(&mut inputs, fiat_shamir_hints.z);
        add_input(&mut inputs, fiat_shamir_hints.alpha);
        add_input(&mut inputs, fiat_shamir_input.random_coeff);
        add_input(
            &mut inputs,
            fiat_shamir_input.after_sampled_values_random_coeff,
        );
        add_input(
            &mut inputs,
            pack_queries(&fiat_shamir_input.queries_at_max_first_layer_column_log_size[0..4]),
        );
        add_input(
            &mut inputs,
            pack_queries(&fiat_shamir_input.queries_at_max_first_layer_column_log_size[4..8]),
        );
        for fri_alpha in fiat_shamir_input.fri_alphas.iter() {
            add_input(&mut inputs, *fri_alpha);
        }

        let circuit = cs.generate_plonk_without_poseidon_circuit();
        let proof = prove_plonk_without_poseidon::<Sha256MerkleChannel>(config, &circuit);
        verify_plonk_without_poseidon::<Sha256MerkleChannel>(proof, config, &inputs).unwrap();
    }
}
