use circle_plonk_dsl_composition::CompositionCheck;
use circle_plonk_dsl_constraint_system::dvar::AllocVar;
use circle_plonk_dsl_constraint_system::ConstraintSystemRef;
use circle_plonk_dsl_data_structures::PlonkWithPoseidonProofVar;
use circle_plonk_dsl_fiat_shamir::FiatShamirResults;
use circle_plonk_dsl_hints::FiatShamirHints;
use num_traits::One;
use stwo_prover::core::fields::qm31::QM31;
use stwo_prover::core::fri::FriConfig;
use stwo_prover::core::pcs::PcsConfig;
use stwo_prover::core::vcs::poseidon31_merkle::{Poseidon31MerkleChannel, Poseidon31MerkleHasher};
use stwo_prover::examples::plonk_with_poseidon::air::{
    prove_plonk_with_poseidon, verify_plonk_with_poseidon, PlonkWithPoseidonProof,
};

fn main() {
    let proof: PlonkWithPoseidonProof<Poseidon31MerkleHasher> =
        bincode::deserialize(include_bytes!("../../components/test_data/joint_proof.bin")).unwrap();
    let config = PcsConfig {
        pow_bits: 20,
        fri_config: FriConfig::new(0, 5, 16),
    };

    let fiat_shamir_hints = FiatShamirHints::new(&proof, config);

    let cs = ConstraintSystemRef::new_ref();
    let mut proof_var = PlonkWithPoseidonProofVar::new_constant(&cs, &proof);

    let results = FiatShamirResults::compute(&fiat_shamir_hints, &mut proof_var);
    CompositionCheck::compute(
        &fiat_shamir_hints,
        &results.lookup_elements,
        results.random_coeff,
        results.oods_point,
        &proof_var,
    );

    cs.pad();
    cs.check_arithmetics();
    cs.populate_logup_arguments();
    cs.check_poseidon_invocations();

    let (plonk, mut poseidon) = cs.generate_circuit();
    let proof = prove_plonk_with_poseidon::<Poseidon31MerkleChannel>(
        plonk.mult_a.length.ilog2(),
        poseidon.0.len().ilog2(),
        config,
        &plonk,
        &mut poseidon,
    );
    verify_plonk_with_poseidon::<Poseidon31MerkleChannel>(
        proof,
        config,
        &[
            (1, QM31::one()),
            (2, QM31::from_u32_unchecked(0, 1, 0, 0)),
            (3, QM31::from_u32_unchecked(0, 0, 1, 0)),
        ],
    )
    .unwrap();
}
