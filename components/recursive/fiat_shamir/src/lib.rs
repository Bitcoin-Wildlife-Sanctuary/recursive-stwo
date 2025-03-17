use circle_plonk_dsl_bits::BitsVar;
use circle_plonk_dsl_channel::{ChannelVar, HashVar};
use circle_plonk_dsl_circle::CirclePointQM31Var;
use circle_plonk_dsl_constraint_system::dvar::{AllocVar, DVar};
use circle_plonk_dsl_data_structures::{LookupElementsVar, PlonkWithPoseidonProofVar};
use circle_plonk_dsl_fields::{M31Var, QM31Var};
use circle_plonk_dsl_hints::FiatShamirHints;
use stwo_prover::core::fields::qm31::QM31;
use stwo_prover::core::fields::FieldExpOps;
use stwo_prover::core::pcs::PcsConfig;
use stwo_prover::core::vcs::poseidon31_merkle::Poseidon31MerkleChannel;

pub struct FiatShamirResults {
    pub preprocessed_commitment: HashVar,
    pub trace_commitment: HashVar,
    pub interaction_trace_commitment: HashVar,
    pub composition_commitment: HashVar,

    pub plonk_total_sum: QM31Var,
    pub poseidon_total_sum: QM31Var,
    pub lookup_elements: LookupElementsVar,
    pub random_coeff: QM31Var,
    pub after_sampled_values_random_coeff: QM31Var,
    pub oods_point: CirclePointQM31Var,
    pub raw_queries: Vec<M31Var>,

    pub fri_alphas: Vec<QM31Var>,
}

impl FiatShamirResults {
    pub fn compute(
        fiat_shamir_hints: &FiatShamirHints<Poseidon31MerkleChannel>,
        proof: &mut PlonkWithPoseidonProofVar,
        pcs_config: PcsConfig,
        inputs: &[(usize, QM31Var)],
    ) -> Self {
        let cs = proof.cs();

        let mut preprocessed_commitment = proof.stark_proof.commitments[0].clone();
        let mut trace_commitment = proof.stark_proof.commitments[1].clone();
        let mut interaction_trace_commitment = proof.stark_proof.commitments[2].clone();
        let mut composition_commitment = proof.stark_proof.commitments[3].clone();

        let mut channel = ChannelVar::default(&cs);

        // Preprocessed trace.
        channel.mix_root(&mut preprocessed_commitment);

        // Trace.
        proof.stmt0.mix_into(&mut channel);
        channel.mix_root(&mut trace_commitment);

        // Draw interaction elements.
        let lookup_elements = LookupElementsVar::draw(&mut channel);

        // Interaction trace.
        proof.stmt1.mix_into(&mut channel);
        channel.mix_root(&mut interaction_trace_commitment);

        let random_coeff = channel.get_felts()[0].clone();

        // Read composition polynomial commitment.
        channel.mix_root(&mut composition_commitment);

        // Draw OODS point.
        let oods_point = CirclePointQM31Var::from_channel(&mut channel);

        let sampled_values_flattened = proof.stark_proof.sampled_values.clone().flatten_cols();
        for chunk in sampled_values_flattened.chunks(2) {
            if chunk.len() == 1 {
                channel.absorb_one_felt_and_permute(&chunk[0]);
            } else {
                channel.absorb_two_felts_and_permute(&chunk[0], &chunk[1]);
            }
        }

        let after_sampled_values_random_coeff = channel.get_felts()[0].clone();

        // FRI layers commitments and alphas
        let mut fri_alphas = vec![];
        channel.mix_root(&mut proof.stark_proof.fri_proof.first_layer_commitment);
        fri_alphas.push(channel.get_felts()[0].clone());

        for l in proof
            .stark_proof
            .fri_proof
            .inner_layer_commitments
            .iter_mut()
        {
            channel.mix_root(l);
            fri_alphas.push(channel.get_felts()[0].clone());
        }
        channel.absorb_one_felt_and_permute(&proof.stark_proof.fri_proof.last_poly);

        let nonce_felt = QM31Var::from_m31(
            &proof.stark_proof.proof_of_work[0],
            &proof.stark_proof.proof_of_work[1],
            &proof.stark_proof.proof_of_work[2],
            &M31Var::zero(&cs),
        );

        let _ = BitsVar::from_m31(&proof.stark_proof.proof_of_work[0], 22);
        let _ = BitsVar::from_m31(&proof.stark_proof.proof_of_work[1], 21);
        let _ = BitsVar::from_m31(&proof.stark_proof.proof_of_work[2], 21);

        channel.absorb_one_felt_and_permute(&nonce_felt);

        let lower_bits = BitsVar::from_m31(&channel.digest.to_qm31()[0].decompose_m31()[0], 31)
            .compose_range(0..pcs_config.pow_bits as usize);
        lower_bits.equalverify(&M31Var::zero(&cs));

        let mut raw_queries = Vec::with_capacity(pcs_config.fri_config.n_queries);
        let mut draw_queries_felts =
            Vec::with_capacity(pcs_config.fri_config.n_queries.div_ceil(4));
        for _ in 0..pcs_config.fri_config.n_queries.div_ceil(4) {
            let [a, b] = channel.get_felts();
            draw_queries_felts.push(a);
            draw_queries_felts.push(b);
        }
        for felt in draw_queries_felts.iter() {
            raw_queries.extend_from_slice(&felt.decompose_m31());
        }
        raw_queries.truncate(pcs_config.fri_config.n_queries);

        // enforce the total sum
        let mut input_sum = QM31Var::zero(&cs);
        for (idx, v) in inputs.iter() {
            let sum = &(v + &(&QM31Var::new_constant(&cs, &QM31::from(*idx as u32))
                * &lookup_elements.alpha))
                - &lookup_elements.z;
            input_sum = &input_sum + &sum.inv();
        }
        (&(&input_sum + &proof.stmt1.poseidon_total_sum) + &proof.stmt1.plonk_total_sum)
            .equalverify(&QM31Var::zero(&cs));

        assert_eq!(lookup_elements.z.value(), fiat_shamir_hints.z);
        assert_eq!(lookup_elements.alpha.value(), fiat_shamir_hints.alpha);
        for i in 0..3 {
            assert_eq!(
                lookup_elements.alpha_powers[i].value(),
                fiat_shamir_hints.alpha.pow(i as u128)
            );
        }
        assert_eq!(random_coeff.value(), fiat_shamir_hints.random_coeff);
        assert_eq!(oods_point.x.value(), fiat_shamir_hints.oods_point.x);
        assert_eq!(oods_point.y.value(), fiat_shamir_hints.oods_point.y);
        assert_eq!(
            after_sampled_values_random_coeff.value(),
            fiat_shamir_hints.after_sampled_values_random_coeff
        );
        for (l, r) in fri_alphas.iter().zip(fiat_shamir_hints.fri_alphas.iter()) {
            assert_eq!(l.value(), *r);
        }

        Self {
            preprocessed_commitment,
            trace_commitment,
            interaction_trace_commitment,
            composition_commitment,
            plonk_total_sum: proof.stmt1.plonk_total_sum.clone(),
            poseidon_total_sum: proof.stmt1.poseidon_total_sum.clone(),
            lookup_elements,
            random_coeff,
            after_sampled_values_random_coeff,
            oods_point,
            raw_queries,
            fri_alphas,
        }
    }
}

#[cfg(test)]
mod test {
    use crate::FiatShamirResults;
    use circle_plonk_dsl_constraint_system::dvar::AllocVar;
    use circle_plonk_dsl_constraint_system::ConstraintSystemRef;
    use circle_plonk_dsl_data_structures::PlonkWithPoseidonProofVar;
    use circle_plonk_dsl_fields::QM31Var;
    use circle_plonk_dsl_hints::FiatShamirHints;
    use num_traits::One;
    use stwo_prover::core::fields::qm31::QM31;
    use stwo_prover::core::fri::FriConfig;
    use stwo_prover::core::pcs::PcsConfig;
    use stwo_prover::core::vcs::poseidon31_merkle::{
        Poseidon31MerkleChannel, Poseidon31MerkleHasher,
    };
    use stwo_prover::examples::plonk_with_poseidon::air::{
        prove_plonk_with_poseidon, verify_plonk_with_poseidon, PlonkWithPoseidonProof,
    };

    #[test]
    fn test_fiat_shamir() {
        let proof: PlonkWithPoseidonProof<Poseidon31MerkleHasher> =
            bincode::deserialize(include_bytes!("../../../test_data/small_proof.bin")).unwrap();
        let config = PcsConfig {
            pow_bits: 20,
            fri_config: FriConfig::new(0, 5, 16),
        };

        let fiat_shamir_hints = FiatShamirHints::new(&proof, config, &[(1, QM31::one())]);

        let cs = ConstraintSystemRef::new_plonk_with_poseidon_ref();
        let mut proof_var = PlonkWithPoseidonProofVar::new_witness(&cs, &proof);

        let _results = FiatShamirResults::compute(
            &fiat_shamir_hints,
            &mut proof_var,
            config,
            &[(1, QM31Var::one(&cs))],
        );

        cs.pad();
        cs.check_arithmetics();
        cs.populate_logup_arguments();
        cs.check_poseidon_invocations();

        let (plonk, mut poseidon) = cs.generate_plonk_with_poseidon_circuit();
        let proof =
            prove_plonk_with_poseidon::<Poseidon31MerkleChannel>(config, &plonk, &mut poseidon);
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
}
