use itertools::Itertools;
use num_traits::{One, Zero};
use std::collections::BTreeSet;
use stwo_prover::constraint_framework::{Relation, PREPROCESSED_TRACE_IDX};
use stwo_prover::core::air::Components;
use stwo_prover::core::channel::{Channel, Poseidon31Channel};
use stwo_prover::core::circle::CirclePoint;
use stwo_prover::core::fields::m31::M31;
use stwo_prover::core::fields::qm31::SecureField;
use stwo_prover::core::fields::secure_column::SECURE_EXTENSION_DEGREE;
use stwo_prover::core::fields::FieldExpOps;
use stwo_prover::core::fri::{CirclePolyDegreeBound, FriVerifier};
use stwo_prover::core::pcs::{CommitmentSchemeVerifier, PcsConfig};
use stwo_prover::core::vcs::poseidon31_hash::Poseidon31Hash;
use stwo_prover::core::vcs::poseidon31_merkle::{Poseidon31MerkleChannel, Poseidon31MerkleHasher};
use stwo_prover::examples::plonk_with_poseidon::air::{
    PlonkWithPoseidonComponents, PlonkWithPoseidonProof,
};
use stwo_prover::examples::plonk_with_poseidon::plonk::PlonkWithAcceleratorLookupElements;

pub struct FiatShamirHints {
    pub preprocessed_commitment: Poseidon31Hash,
    pub trace_commitment: Poseidon31Hash,
    pub log_size_plonk: u32,
    pub log_size_poseidon: u32,
    pub plonk_total_sum: SecureField,
    pub poseidon_total_sum: SecureField,
    pub alpha: SecureField,
    pub z: SecureField,
    pub random_coeff: SecureField,
    pub after_sampled_values_random_coeff: SecureField,
    pub oods_point: CirclePoint<SecureField>,
    pub first_layer_commitment: Poseidon31Hash,
    pub inner_layer_commitments: Vec<Poseidon31Hash>,
    pub last_layer_evaluation: SecureField,
    pub fri_alphas: Vec<SecureField>,
    pub queries: Vec<usize>,
}

impl FiatShamirHints {
    pub fn new(
        proof: &PlonkWithPoseidonProof<Poseidon31MerkleHasher>,
        config: PcsConfig,
    ) -> FiatShamirHints {
        let channel = &mut Poseidon31Channel::default();
        let commitment_scheme =
            &mut CommitmentSchemeVerifier::<Poseidon31MerkleChannel>::new(config);

        let log_sizes = proof.stmt0.log_sizes();

        // Preprocessed trace.
        commitment_scheme.commit(proof.stark_proof.commitments[0], &log_sizes[0], channel);

        // Trace.
        proof.stmt0.mix_into(channel);
        commitment_scheme.commit(proof.stark_proof.commitments[1], &log_sizes[1], channel);

        // Draw interaction elements.
        let lookup_elements = PlonkWithAcceleratorLookupElements::draw(channel);

        // Interaction trace.
        proof.stmt1.mix_into(channel);
        commitment_scheme.commit(proof.stark_proof.commitments[2], &log_sizes[2], channel);

        let components =
            PlonkWithPoseidonComponents::new(&proof.stmt0, &lookup_elements, &proof.stmt1);
        let one_sum: SecureField = lookup_elements.combine(&[M31::one(), M31::one()]);

        let total_sum =
            proof.stmt1.plonk_total_sum - one_sum.inverse() + proof.stmt1.poseidon_total_sum;
        assert_eq!(total_sum, SecureField::zero());

        let n_preprocessed_columns = commitment_scheme.trees[PREPROCESSED_TRACE_IDX]
            .column_log_sizes
            .len();

        let components = Components {
            components: components.components().to_vec(),
            n_preprocessed_columns,
        };
        let random_coeff = channel.draw_felt();

        // Read composition polynomial commitment.
        commitment_scheme.commit(
            *proof.stark_proof.commitments.last().unwrap(),
            &[components.composition_log_degree_bound(); SECURE_EXTENSION_DEGREE],
            channel,
        );

        // Draw OODS point.
        let oods_point = CirclePoint::<SecureField>::get_random_point(channel);

        // Get mask sample points relative to oods point.
        let mut sample_points = components.mask_points(oods_point);
        // Add the composition polynomial mask points.
        sample_points.push(vec![vec![oods_point]; SECURE_EXTENSION_DEGREE]);

        channel.mix_felts(&proof.stark_proof.sampled_values.clone().flatten_cols());
        let after_sampled_values_random_coeff = channel.draw_felt();

        let bounds = commitment_scheme
            .column_log_sizes()
            .flatten()
            .into_iter()
            .sorted()
            .rev()
            .dedup()
            .map(|log_size| {
                CirclePolyDegreeBound::new(log_size - config.fri_config.log_blowup_factor)
            })
            .collect_vec();

        // FRI commitment phase on OODS quotients.
        let mut fri_verifier = FriVerifier::<Poseidon31MerkleChannel>::commit(
            channel,
            config.fri_config,
            proof.stark_proof.fri_proof.clone(),
            bounds,
        )
        .unwrap();

        let first_layer_commitment = proof.stark_proof.fri_proof.first_layer.commitment;
        let inner_layer_commitments = proof
            .stark_proof
            .fri_proof
            .inner_layers
            .iter()
            .map(|l| l.commitment)
            .collect_vec();
        assert_eq!(proof.stark_proof.fri_proof.last_layer_poly.len(), 1);
        let last_layer_evaluation = proof.stark_proof.fri_proof.last_layer_poly.coeffs[0].clone();

        let mut fri_alphas = vec![];
        fri_alphas.push(fri_verifier.first_layer.folding_alpha);
        for layer in fri_verifier.inner_layers.iter() {
            fri_alphas.push(layer.folding_alpha);
        }
        let nonce = proof.stark_proof.proof_of_work;
        channel.mix_u64(nonce);

        assert!(channel.trailing_zeros() >= config.pow_bits);

        // Get FRI query positions.
        let query_positions_per_log_size = fri_verifier.sample_query_positions(channel);
        let max_first_layer_column_log_size = fri_verifier
            .first_layer
            .column_commitment_domains
            .iter()
            .map(|domain| domain.log_size())
            .max()
            .unwrap();
        let queries_parents =
            query_positions_per_log_size[&max_first_layer_column_log_size].clone();

        FiatShamirHints {
            preprocessed_commitment: proof.stark_proof.commitments[0],
            trace_commitment: proof.stark_proof.commitments[1],
            log_size_plonk: proof.stmt0.log_size_plonk,
            log_size_poseidon: proof.stmt0.log_size_poseidon,
            plonk_total_sum: proof.stmt1.plonk_total_sum,
            poseidon_total_sum: proof.stmt1.poseidon_total_sum,
            alpha: lookup_elements.0.alpha,
            z: lookup_elements.0.z,
            random_coeff,
            after_sampled_values_random_coeff,
            oods_point,
            first_layer_commitment,
            inner_layer_commitments,
            last_layer_evaluation,
            fri_alphas,
            queries: queries_parents,
        }
    }
}
