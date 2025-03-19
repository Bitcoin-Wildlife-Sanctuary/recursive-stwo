use circle_plonk_dsl_answer::AnswerResults;
use circle_plonk_dsl_circle::CirclePointQM31Var;
use circle_plonk_dsl_composition::CompositionCheck;
use circle_plonk_dsl_constraint_system::dvar::AllocVar;
use circle_plonk_dsl_constraint_system::ConstraintSystemRef;
use circle_plonk_dsl_data_structures::PlonkWithPoseidonProofVar;
use circle_plonk_dsl_fiat_shamir::FiatShamirResults;
use circle_plonk_dsl_fields::QM31Var;
use circle_plonk_dsl_folding::FoldingResults;
use circle_plonk_dsl_hints::{
    AnswerHints, DecommitHints, FiatShamirHints, FirstLayerHints, InnerLayersHints,
};
use num_traits::One;
use std::io::Write;
use stwo_prover::core::fields::qm31::QM31;
use stwo_prover::core::fri::FriConfig;
use stwo_prover::core::pcs::PcsConfig;
use stwo_prover::core::vcs::poseidon31_merkle::{Poseidon31MerkleChannel, Poseidon31MerkleHasher};
use stwo_prover::examples::plonk_with_poseidon::air::{
    prove_plonk_with_poseidon, verify_plonk_with_poseidon, PlonkWithPoseidonProof,
};

fn main() {
    let proof: PlonkWithPoseidonProof<Poseidon31MerkleHasher> = bincode::deserialize(
        include_bytes!("../../../components/test_data/small_proof.bin"),
    )
    .unwrap();
    let config = PcsConfig {
        pow_bits: 20,
        fri_config: FriConfig::new(2, 5, 16),
    };

    let fiat_shamir_hints = FiatShamirHints::new(&proof, config, &[(1, QM31::one())]);
    let answer_hints = AnswerHints::compute(&fiat_shamir_hints, &proof);
    let decommitment_hints = DecommitHints::compute(&fiat_shamir_hints, &proof);
    let first_layer_hints = FirstLayerHints::compute(&fiat_shamir_hints, &answer_hints, &proof);
    let inner_layer_hints = InnerLayersHints::compute(
        &first_layer_hints.folded_evals_by_column,
        &fiat_shamir_hints,
        &proof,
    );

    let cs = ConstraintSystemRef::new_plonk_with_poseidon_ref();
    let mut proof_var = PlonkWithPoseidonProofVar::new_witness(&cs, &proof);

    println!("after allocating the proof: {}", cs.num_plonk_rows());

    let fiat_shamir_results = FiatShamirResults::compute(
        &fiat_shamir_hints,
        &mut proof_var,
        config,
        &[(1, QM31Var::one(&cs))],
    );
    println!("after fiat-shamir: {}", cs.num_plonk_rows());
    CompositionCheck::compute(
        &fiat_shamir_hints,
        &fiat_shamir_results.lookup_elements,
        fiat_shamir_results.random_coeff.clone(),
        fiat_shamir_results.oods_point.clone(),
        &proof_var,
    );
    println!("after composition: {}", cs.num_plonk_rows());

    let answer_results = AnswerResults::compute(
        &CirclePointQM31Var::new_witness(&cs, &fiat_shamir_hints.oods_point),
        &fiat_shamir_hints,
        &fiat_shamir_results,
        &answer_hints,
        &decommitment_hints,
        &proof_var,
        config,
    );
    println!("after answer: {}", cs.num_plonk_rows());

    FoldingResults::compute(
        &proof_var,
        &fiat_shamir_hints,
        &fiat_shamir_results,
        &answer_results,
        &first_layer_hints,
        &inner_layer_hints,
    );
    println!("after folding: {}", cs.num_plonk_rows());

    cs.pad();
    cs.check_arithmetics();
    cs.populate_logup_arguments();
    cs.check_poseidon_invocations();

    let (plonk, mut poseidon) = cs.generate_plonk_with_poseidon_circuit();

    let dest_config = PcsConfig {
        pow_bits: 20,
        fri_config: FriConfig::new(8, 5, 16),
    };

    let proof =
        prove_plonk_with_poseidon::<Poseidon31MerkleChannel>(dest_config, &plonk, &mut poseidon);

    let path = format!(
        "../../components/test_data/recursive_proof_{}_{}.bin",
        proof.stmt0.log_size_plonk, proof.stmt0.log_size_poseidon
    );
    if !std::fs::exists(path.clone()).unwrap() {
        let encoded = bincode::serialize(&proof).unwrap();
        let mut fs = std::fs::File::create_new(path).unwrap();
        fs.write(&encoded).unwrap();
    }

    verify_plonk_with_poseidon::<Poseidon31MerkleChannel>(
        proof,
        dest_config,
        &[
            (1, QM31::one()),
            (2, QM31::from_u32_unchecked(0, 1, 0, 0)),
            (3, QM31::from_u32_unchecked(0, 0, 1, 0)),
        ],
    )
    .unwrap();
}
