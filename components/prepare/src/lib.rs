use crate::data_structures::PointSampleVar;
use circle_plonk_dsl_circle::CirclePointQM31Var;
use circle_plonk_dsl_data_structures::PlonkWithPoseidonProofVar;
use circle_plonk_dsl_hints::FiatShamirHints;
use itertools::Itertools;
use std::collections::{HashMap, HashSet};
use std::iter::zip;
use std::ops::Add;
use stwo_prover::constraint_framework::PREPROCESSED_TRACE_IDX;
use stwo_prover::core::pcs::TreeVec;
use stwo_prover::core::poly::circle::CanonicCoset;
use stwo_prover::core::ColumnVec;

pub mod data_structures;

pub struct PreparePointsAndColumnLineCoeffs;

impl PreparePointsAndColumnLineCoeffs {
    pub fn compute(
        oods_point: &CirclePointQM31Var,
        fiat_shamir_hints: &FiatShamirHints,
        proof: &PlonkWithPoseidonProofVar,
    ) {
        let mut all_shifts_plonk = HashSet::new();
        let mut all_shifts_poseidon = HashSet::new();
        for round in fiat_shamir_hints.mask_plonk.iter() {
            for column in round.iter() {
                for &shift in column.iter() {
                    all_shifts_plonk.insert(shift);
                }
            }
        }
        for round in fiat_shamir_hints.mask_poseidon.iter() {
            for column in round.iter() {
                for &shift in column.iter() {
                    all_shifts_poseidon.insert(shift);
                }
            }
        }

        let trace_step_plonk = CanonicCoset::new(fiat_shamir_hints.log_size_plonk).step();
        let trace_step_poseidon = CanonicCoset::new(fiat_shamir_hints.log_size_poseidon).step();

        let mut shifted_points_plonk = HashMap::<isize, CirclePointQM31Var>::new();
        let mut shifted_points_poseidon = HashMap::<isize, CirclePointQM31Var>::new();
        for &i in all_shifts_plonk.iter() {
            shifted_points_plonk.insert(i, oods_point.add(&trace_step_plonk.mul_signed(i)));
        }
        for &i in all_shifts_poseidon.iter() {
            shifted_points_poseidon.insert(i, oods_point.add(&trace_step_poseidon.mul_signed(i)));
        }

        let mut mask_points_plonk: TreeVec<ColumnVec<Vec<CirclePointQM31Var>>> =
            fiat_shamir_hints.mask_plonk.as_ref().map_cols(|column| {
                column
                    .iter()
                    .map(|shift| shifted_points_plonk.get(shift).unwrap().clone())
                    .collect_vec()
            });
        mask_points_plonk[PREPROCESSED_TRACE_IDX] = vec![vec![oods_point.clone()]; 10];
        let mut mask_points_poseidon: TreeVec<ColumnVec<Vec<CirclePointQM31Var>>> =
            fiat_shamir_hints.mask_poseidon.as_ref().map_cols(|column| {
                column
                    .iter()
                    .map(|shift| shifted_points_poseidon.get(shift).unwrap().clone())
                    .collect_vec()
            });
        mask_points_poseidon[PREPROCESSED_TRACE_IDX] = vec![vec![oods_point.clone()]; 5];

        assert_eq!(
            mask_points_plonk.len(),
            fiat_shamir_hints.sample_points.len() - 1
        );
        for (round_idx, (round_plonk, round_poseidon)) in mask_points_plonk
            .iter()
            .zip(mask_points_poseidon.iter())
            .enumerate()
            .take(3)
        {
            assert_eq!(
                round_plonk.len() + round_poseidon.len(),
                fiat_shamir_hints.sample_points[round_idx].len(),
                "round_idx = {}",
                round_idx
            );
            for (column_idx, column) in round_plonk.iter().enumerate() {
                assert_eq!(
                    column.len(),
                    fiat_shamir_hints.sample_points[round_idx][column_idx].len()
                );
                for (shift_idx, shifted_point) in column.iter().enumerate() {
                    assert_eq!(
                        shifted_point.x.value,
                        fiat_shamir_hints.sample_points[round_idx][column_idx][shift_idx].x
                    );
                    assert_eq!(
                        shifted_point.y.value,
                        fiat_shamir_hints.sample_points[round_idx][column_idx][shift_idx].y
                    );
                }
            }

            for (column_idx, column) in round_poseidon.iter().enumerate() {
                assert_eq!(
                    column.len(),
                    fiat_shamir_hints.sample_points[round_idx][round_plonk.len() + column_idx]
                        .len()
                );
                for (shift_idx, shifted_point) in column.iter().enumerate() {
                    assert_eq!(
                        shifted_point.x.value,
                        fiat_shamir_hints.sample_points[round_idx][round_plonk.len() + column_idx]
                            [shift_idx]
                            .x
                    );
                    assert_eq!(
                        shifted_point.y.value,
                        fiat_shamir_hints.sample_points[round_idx][round_plonk.len() + column_idx]
                            [shift_idx]
                            .y
                    );
                }
            }
        }

        let mut sampled_points =
            TreeVec::concat_cols([mask_points_plonk, mask_points_poseidon].into_iter());
        sampled_points.push(vec![vec![oods_point.clone()]; 4]);

        let _samples = sampled_points
            .zip_cols(proof.stark_proof.sampled_values.clone())
            .map_cols(|(sampled_points, sampled_values)| {
                zip(sampled_points, sampled_values)
                    .map(|(point, value)| PointSampleVar { point, value })
                    .collect_vec()
            });
    }
}

#[cfg(test)]
mod test {
    use crate::PreparePointsAndColumnLineCoeffs;
    use circle_plonk_dsl_circle::CirclePointQM31Var;
    use circle_plonk_dsl_constraint_system::dvar::AllocVar;
    use circle_plonk_dsl_constraint_system::ConstraintSystemRef;
    use circle_plonk_dsl_data_structures::PlonkWithPoseidonProofVar;
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
    fn test_prepare() {
        let proof: PlonkWithPoseidonProof<Poseidon31MerkleHasher> =
            bincode::deserialize(include_bytes!("../../test_data/joint_proof.bin")).unwrap();
        let config = PcsConfig {
            pow_bits: 20,
            fri_config: FriConfig::new(0, 5, 16),
        };

        let fiat_shamir_hints = FiatShamirHints::new(&proof, config);

        let cs = ConstraintSystemRef::new_ref();
        let proof_var = PlonkWithPoseidonProofVar::new_constant(&cs, &proof);

        PreparePointsAndColumnLineCoeffs::compute(
            &CirclePointQM31Var::new_constant(&cs, &fiat_shamir_hints.oods_point),
            &fiat_shamir_hints,
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
}
