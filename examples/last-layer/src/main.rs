use circle_plonk_dsl_constraint_system::var::AllocVar;
use circle_plonk_dsl_constraint_system::ConstraintSystemRef;
use circle_plonk_dsl_hints::{AnswerHints, FiatShamirHints};
use circle_plonk_dsl_last_answer::data_structures::{
    LastDecommitHints, LastDecommitInput, LastDecommitInputVar,
};
use circle_plonk_dsl_last_answer::LastAnswerResults;
use circle_plonk_dsl_last_data_structures::LastPlonkWithPoseidonProofVar;
use circle_plonk_dsl_last_fiat_shamir::{
    LastFiatShamirInput, LastFiatShamirInputVar, LastFiatShamirResults,
};
use circle_plonk_dsl_last_folding::data_structures::merkle_proofs::{
    LastFirstLayerHints, LastFirstLayerInputVar, LastInnerLayersHints, LastInnerLayersInputVar,
};
use circle_plonk_dsl_last_folding::LastFoldingResults;
use num_traits::One;
use std::io::Write;
use stwo::core::fields::qm31::QM31;
use stwo::core::fri::FriConfig;
use stwo::core::pcs::PcsConfig;
use stwo::core::vcs::sha256_merkle::Sha256MerkleChannel;
use stwo::core::vcs::sha256_poseidon31_merkle::{
    Sha256Poseidon31MerkleChannel, Sha256Poseidon31MerkleHasher,
};
use stwo_examples::plonk_with_poseidon::air::PlonkWithPoseidonProof;
use stwo_examples::plonk_without_poseidon::air::{
    prove_plonk_without_poseidon, verify_plonk_without_poseidon,
};

fn main() {
    let proof: PlonkWithPoseidonProof<Sha256Poseidon31MerkleHasher> = bincode::deserialize(
        include_bytes!("../../../components/test_data/hybrid_hash.bin"),
    )
    .unwrap();

    let config = PcsConfig {
        pow_bits: 28,
        fri_config: FriConfig::new(7, 9, 8),
    };

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
    let decommit_hints = LastDecommitHints::from_proof(&fiat_shamir_hints, &proof);
    let fri_answer_hints = AnswerHints::compute(&fiat_shamir_hints, &proof);
    let first_layer_hints =
        LastFirstLayerHints::compute(&fiat_shamir_hints, &fri_answer_hints, &proof);
    let inner_layers_hints = LastInnerLayersHints::compute(
        &first_layer_hints.folded_evals_by_column,
        &fiat_shamir_hints,
        &proof,
    );

    let fiat_shamir_input = LastFiatShamirInput::from_proof(&proof, &fiat_shamir_hints);
    let decommit_input = LastDecommitInput::from_hints(&decommit_hints);
    let fiat_shamir_input_var = LastFiatShamirInputVar::new_public_input(&cs, &fiat_shamir_input);
    let decommit_input_var = LastDecommitInputVar::new_public_input(&cs, &decommit_input);
    let first_layer_input_var = LastFirstLayerInputVar::new_public_input(&cs, &first_layer_hints);
    let inner_layers_input_var =
        LastInnerLayersInputVar::new_public_input(&cs, &inner_layers_hints);

    let proof_var = LastPlonkWithPoseidonProofVar::new_witness(&cs, &proof);
    let fiat_shamir_results = LastFiatShamirResults::compute(&proof_var, &fiat_shamir_input_var);

    let last_answer_results = LastAnswerResults::compute(
        &fiat_shamir_hints,
        &decommit_hints,
        &fri_answer_hints,
        &fiat_shamir_results,
        &decommit_input_var,
        &proof_var,
        config,
    );

    LastFoldingResults::compute(
        &proof_var,
        &fiat_shamir_hints,
        &fiat_shamir_results,
        &last_answer_results,
        &first_layer_hints,
        &first_layer_input_var,
        &inner_layers_input_var,
    );

    cs.pad();
    cs.check_arithmetics();
    cs.populate_logup_arguments();

    let config = PcsConfig {
        pow_bits: 28,
        fri_config: FriConfig::new(0, 9, 8),
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
    for proof in decommit_input
        .precomputed_proofs
        .iter()
        .chain(decommit_input.trace_proofs.iter())
        .chain(decommit_input.interaction_proofs.iter())
        .chain(decommit_input.composition_proofs.iter())
    {
        for (_, column) in proof.packed_columns.iter() {
            for elem in column.iter() {
                add_input(&mut inputs, *elem);
            }
        }
    }
    for proof in first_layer_hints.merkle_proofs.iter() {
        for (_, elem) in proof.self_columns.iter() {
            add_input(&mut inputs, *elem);
        }
        for (_, elem) in proof.siblings_columns.iter() {
            add_input(&mut inputs, *elem);
        }
    }
    for (_, proofs) in inner_layers_hints.merkle_proofs.iter() {
        for proof in proofs.iter() {
            for (_, elem) in proof.self_columns.iter() {
                add_input(&mut inputs, *elem);
            }
            for (_, elem) in proof.siblings_columns.iter() {
                add_input(&mut inputs, *elem);
            }
        }
    }
    println!("input length: {} QM31", inputs.len());

    if std::fs::exists("data/bitcoin_proof.bin").unwrap() {
        return;
    }

    let timer = std::time::Instant::now();
    let circuit = cs.generate_plonk_without_poseidon_circuit();
    let proof = prove_plonk_without_poseidon::<Sha256MerkleChannel>(config, &circuit);
    println!("proof generation time: {}s", timer.elapsed().as_secs_f64());

    let encoded = bincode::serialize(&proof).unwrap();
    let mut fs = std::fs::File::create("data/bitcoin_proof.bin").unwrap();
    fs.write(&encoded).unwrap();

    verify_plonk_without_poseidon::<Sha256MerkleChannel>(proof, config, &inputs).unwrap();
}
