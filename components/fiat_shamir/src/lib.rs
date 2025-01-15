use crate::data_structures::{PlonkWithAcceleratorLookupElementsVar, PlonkWithPoseidonProofVar};
use circle_plonk_dsl_bits::{get_lower_bits_checked, BitsVar};
use circle_plonk_dsl_channel::{ChannelVar, HashVar};
use circle_plonk_dsl_circle::CirclePointQM31Var;
use circle_plonk_dsl_constraint_system::dvar::DVar;
use circle_plonk_dsl_fields::{CM31Var, M31Var, QM31Var};
use circle_plonk_dsl_hints::FiatShamirHints;
use num_traits::Zero;
use std::cmp::max;
use stwo_prover::core::fields::cm31::CM31;
use stwo_prover::core::fields::m31::M31;
use stwo_prover::core::fields::qm31::QM31;
use stwo_prover::core::fields::FieldExpOps;

pub mod data_structures;

pub struct FiatShamirResults {
    pub preprocessed_commitment: HashVar,
    pub trace_commitment: HashVar,
    pub interaction_trace_commitment: HashVar,
    pub composition_commitment: HashVar,

    pub plonk_total_sum: QM31Var,
    pub poseidon_total_sum: QM31Var,
    pub lookup_elements: PlonkWithAcceleratorLookupElementsVar,
    pub random_coeff: QM31Var,
    pub after_sampled_values_random_coeff: QM31Var,
    pub oods_point: CirclePointQM31Var,
    pub queries: Vec<M31Var>,
}

impl FiatShamirResults {
    pub fn compute(fiat_shamir_hints: &FiatShamirHints, proof: &PlonkWithPoseidonProofVar) -> Self {
        let cs = proof.cs();

        let preprocessed_commitment = proof.stark_proof.commitments[0].clone();
        let trace_commitment = proof.stark_proof.commitments[1].clone();
        let interaction_trace_commitment = proof.stark_proof.commitments[2].clone();
        let composition_commitment = proof.stark_proof.commitments[3].clone();

        let mut channel = ChannelVar::default(&cs);

        // Preprocessed trace.
        channel.mix_root(&preprocessed_commitment);

        // Trace.
        proof.stmt0.mix_into(&mut channel);
        channel.mix_root(&trace_commitment);

        // Draw interaction elements.
        let lookup_elements = PlonkWithAcceleratorLookupElementsVar::draw(&mut channel);

        // Interaction trace.
        proof.stmt1.mix_into(&mut channel);
        channel.mix_root(&interaction_trace_commitment);

        let random_coeff = channel.get_felts()[0].clone();

        // Read composition polynomial commitment.
        channel.mix_root(&composition_commitment);

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
        channel.mix_root(&proof.stark_proof.fri_proof.first_layer_commitment);
        fri_alphas.push(channel.get_felts()[0].clone());

        for l in proof.stark_proof.fri_proof.inner_layer_commitments.iter() {
            channel.mix_root(&l);
            fri_alphas.push(channel.get_felts()[0].clone());
        }
        channel.absorb_one_felt_and_permute(&proof.stark_proof.fri_proof.last_poly);

        let nonce_felt = {
            QM31Var {
                value: QM31::from_m31(
                    proof.stark_proof.proof_of_work[0].value,
                    proof.stark_proof.proof_of_work[1].value,
                    proof.stark_proof.proof_of_work[2].value,
                    M31::zero(),
                ),
                first: CM31Var {
                    value: CM31(
                        proof.stark_proof.proof_of_work[0].value,
                        proof.stark_proof.proof_of_work[1].value,
                    ),
                    real: proof.stark_proof.proof_of_work[0].clone(),
                    imag: proof.stark_proof.proof_of_work[1].clone(),
                },
                second: CM31Var::from(&proof.stark_proof.proof_of_work[2]),
            }
        };

        let _ = BitsVar::from_m31(&proof.stark_proof.proof_of_work[0], 22);
        let _ = BitsVar::from_m31(&proof.stark_proof.proof_of_work[1], 21);
        let _ = BitsVar::from_m31(&proof.stark_proof.proof_of_work[2], 21);

        channel.absorb_one_felt_and_permute(&nonce_felt);

        let lower_bits = get_lower_bits_checked(&channel.digest.to_m31()[0], 20);
        lower_bits.equalverify(&M31Var::zero(&cs));

        let mut raw_queries = Vec::with_capacity(16);
        let mut draw_queries_felts = Vec::with_capacity(4);
        {
            let [a, b] = channel.get_felts();
            draw_queries_felts.push(a);
            draw_queries_felts.push(b);
            let [a, b] = channel.get_felts();
            draw_queries_felts.push(a);
            draw_queries_felts.push(b);
        }
        for felt in draw_queries_felts.iter() {
            raw_queries.push(felt.first.real.clone());
            raw_queries.push(felt.first.imag.clone());
            raw_queries.push(felt.second.real.clone());
            raw_queries.push(felt.second.imag.clone());
        }

        let mut queries = Vec::with_capacity(16);
        let max_column_log_size = max(
            proof.stmt0.log_size_plonk.value.0 + 1,
            proof.stmt0.log_size_poseidon.value.0 + 2,
        ) + 5;
        for raw_query in raw_queries.iter() {
            queries.push(get_lower_bits_checked(
                raw_query,
                max_column_log_size as usize,
            ));
        }

        // assumption: no duplicated queries in the first attempt
        let mut sorted_queries = vec![];
        for query in queries.iter() {
            sorted_queries.push(query.value.0 as usize);
        }
        sorted_queries.sort_unstable();
        sorted_queries.dedup();
        assert_eq!(sorted_queries.len(), 16);
        assert_eq!(sorted_queries, fiat_shamir_hints.queries);

        assert_eq!(lookup_elements.z.value, fiat_shamir_hints.z);
        assert_eq!(lookup_elements.alpha.value, fiat_shamir_hints.alpha);
        for i in 0..9 {
            assert_eq!(
                lookup_elements.alpha_powers[i].value,
                fiat_shamir_hints.alpha.pow((i + 1) as u128)
            );
        }
        assert_eq!(random_coeff.value, fiat_shamir_hints.random_coeff);
        assert_eq!(oods_point.x.value, fiat_shamir_hints.oods_point.x);
        assert_eq!(oods_point.y.value, fiat_shamir_hints.oods_point.y);
        assert_eq!(
            after_sampled_values_random_coeff.value,
            fiat_shamir_hints.after_sampled_values_random_coeff
        );
        for (l, r) in fri_alphas.iter().zip(fiat_shamir_hints.fri_alphas.iter()) {
            assert_eq!(l.value, *r);
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
            queries,
        }
    }
}

#[cfg(test)]
mod test {
    use crate::data_structures::PlonkWithPoseidonProofVar;
    use crate::FiatShamirResults;
    use circle_plonk_dsl_constraint_system::dvar::AllocVar;
    use circle_plonk_dsl_constraint_system::ConstraintSystemRef;
    use circle_plonk_dsl_hints::FiatShamirHints;
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
            bincode::deserialize(include_bytes!("../../test_data/joint_proof.bin")).unwrap();
        let config = PcsConfig {
            pow_bits: 20,
            fri_config: FriConfig::new(0, 5, 16),
        };

        let fiat_shamir_hints = FiatShamirHints::new(&proof, config);

        let cs = ConstraintSystemRef::new_ref();
        let proof_var = PlonkWithPoseidonProofVar::new_constant(&cs, &proof);

        let _results = FiatShamirResults::compute(&fiat_shamir_hints, &proof_var);

        cs.pad();
        cs.check_arithmetics();
        cs.check_logup_arguments();
        cs.check_poseidon_invocations();

        let (plonk, mut poseidon) = cs.generate_circuit();
        let proof = prove_plonk_with_poseidon::<Poseidon31MerkleChannel>(
            plonk.mult.length.ilog2(),
            poseidon.control_flow.sel_1.len().ilog2(),
            config,
            &plonk,
            &mut poseidon,
        );
        verify_plonk_with_poseidon::<Poseidon31MerkleChannel>(proof, config).unwrap();
    }
}
