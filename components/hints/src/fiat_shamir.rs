use itertools::Itertools;
use num_traits::Zero;
use std::collections::{BTreeMap, BTreeSet};
use stwo_prover::constraint_framework::{Relation, PREPROCESSED_TRACE_IDX};
use stwo_prover::core::air::{Component, Components};
use stwo_prover::core::channel::{Channel, Poseidon31Channel};
use stwo_prover::core::circle::CirclePoint;
use stwo_prover::core::fields::m31::M31;
use stwo_prover::core::fields::qm31::{SecureField, QM31};
use stwo_prover::core::fields::secure_column::SECURE_EXTENSION_DEGREE;
use stwo_prover::core::fields::FieldExpOps;
use stwo_prover::core::fri::{CirclePolyDegreeBound, FriVerifier};
use stwo_prover::core::pcs::{CommitmentSchemeVerifier, PcsConfig, TreeSubspan, TreeVec};
use stwo_prover::core::vcs::poseidon31_hash::Poseidon31Hash;
use stwo_prover::core::vcs::poseidon31_merkle::{Poseidon31MerkleChannel, Poseidon31MerkleHasher};
use stwo_prover::core::ColumnVec;
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

    pub all_log_sizes: BTreeSet<u32>,
    pub max_first_layer_column_log_size: u32,
    pub query_positions_per_log_size: BTreeMap<u32, Vec<usize>>,
    pub raw_query_positions_per_log_size: BTreeMap<u32, Vec<usize>>,
    pub column_log_sizes: TreeVec<Vec<u32>>,
    pub n_columns_per_log_size: TreeVec<BTreeMap<u32, usize>>,
    pub trees_log_sizes: TreeVec<Vec<u32>>,

    pub log_blowup_factor: u32,

    pub plonk_tree_subspan: Vec<TreeSubspan>,
    pub poseidon_tree_subspan: Vec<TreeSubspan>,

    pub plonk_prepared_column_indices: Vec<usize>,
    pub poseidon_prepared_column_indices: Vec<usize>,

    pub sample_points: TreeVec<ColumnVec<Vec<CirclePoint<SecureField>>>>,
    pub mask_plonk: TreeVec<Vec<Vec<isize>>>,
    pub mask_poseidon: TreeVec<Vec<Vec<isize>>>,

    pub fri_verifier: FriVerifier<Poseidon31MerkleChannel>,
}

impl FiatShamirHints {
    pub fn new(
        proof: &PlonkWithPoseidonProof<Poseidon31MerkleHasher>,
        config: PcsConfig,
        inputs: &[(usize, QM31)],
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

        let plonk_tree_subspan = components.plonk.trace_locations().to_vec();
        let plonk_prepared_column_indices = components.plonk.preproccessed_column_indices();
        let poseidon_tree_subspan = components.poseidon.trace_locations().to_vec();
        let poseidon_prepared_column_indices = components.poseidon.preproccessed_column_indices();

        // Get the mask relations
        let mask_plonk = components.plonk.info.mask_offsets.clone();
        let mask_poseidon = components.poseidon.info.mask_offsets.clone();

        let mut input_sum = SecureField::zero();
        for (idx, val) in inputs.iter() {
            let sum: SecureField = lookup_elements.combine(&[
                M31::from(*idx as u32),
                val.0 .0,
                val.0 .1,
                val.1 .0,
                val.1 .1,
            ]);
            input_sum += sum.inverse();
        }

        let total_sum = proof.stmt1.plonk_total_sum + input_sum + proof.stmt1.poseidon_total_sum;
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

        let trees_log_sizes = proof.stmt0.log_sizes();

        let all_log_sizes = fri_verifier
            .first_layer
            .column_commitment_domains
            .iter()
            .map(|domain| domain.log_size())
            .collect::<BTreeSet<u32>>();
        let max_first_layer_column_log_size = *all_log_sizes.iter().max().unwrap();

        // Get FRI query positions.
        let raw_query_positions_per_log_size = {
            let mut channel = channel.clone();
            let mut raw_queries = vec![];

            while raw_queries.len() < config.fri_config.n_queries {
                let felts = channel.draw_felts(2);
                raw_queries.extend_from_slice(&felts[0].to_m31_array());
                raw_queries.extend_from_slice(&felts[1].to_m31_array());
            }
            raw_queries.truncate(config.fri_config.n_queries);

            let mut queries = vec![];
            for raw_query in raw_queries.iter() {
                queries.push(raw_query.0 & ((1 << max_first_layer_column_log_size) - 1));
            }

            let mut map = BTreeMap::new();
            for &log_size in all_log_sizes.iter() {
                map.insert(
                    log_size,
                    queries
                        .iter()
                        .map(|x| (x >> (max_first_layer_column_log_size - log_size)) as usize)
                        .collect_vec(),
                );
            }
            map
        };
        let query_positions_per_log_size = fri_verifier.sample_query_positions(channel);

        let column_log_sizes = commitment_scheme
            .trees
            .as_ref()
            .map(|tree| tree.column_log_sizes.clone());
        let n_columns_per_log_size = commitment_scheme
            .trees
            .as_ref()
            .map(|tree| tree.n_columns_per_log_size.clone());

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

            all_log_sizes,
            max_first_layer_column_log_size,
            raw_query_positions_per_log_size,
            query_positions_per_log_size,
            column_log_sizes,
            n_columns_per_log_size,
            trees_log_sizes,
            log_blowup_factor: config.fri_config.log_blowup_factor,

            plonk_tree_subspan,
            poseidon_tree_subspan,
            plonk_prepared_column_indices,
            poseidon_prepared_column_indices,
            sample_points,
            mask_plonk,
            mask_poseidon,
            fri_verifier,
        }
    }
}
