use crate::data_structures::{LastDecommitHints, LastDecommitInputVar, LastDecommitVar};
use circle_plonk_dsl_answer::data_structures::{PointSampleVar, ShiftIndex};
use circle_plonk_dsl_answer::AnswerResults;
use circle_plonk_dsl_circle::{CirclePointM31Var, CirclePointQM31Var};
use circle_plonk_dsl_constraint_system::var::Var;
use circle_plonk_dsl_constraint_system::ConstraintSystemRef;
use circle_plonk_dsl_fields::QM31Var;
use circle_plonk_dsl_hints::{AnswerHints, FiatShamirHints};
use circle_plonk_dsl_last_data_structures::LastPlonkWithPoseidonProofVar;
use circle_plonk_dsl_last_fiat_shamir::LastFiatShamirResults;
use circle_plonk_dsl_query::QueryPositionsPerLogSizeVar;
use itertools::{izip, multiunzip, Itertools};
use std::cmp::Reverse;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::iter::zip;
use std::ops::Add;
use stwo::core::pcs::{PcsConfig, TreeVec};
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::vcs::sha256_poseidon31_merkle::Sha256Poseidon31MerkleChannel;
use stwo::core::ColumnVec;
use stwo_constraint_framework::PREPROCESSED_TRACE_IDX;

pub mod data_structures;

pub struct LastAnswerResults {
    pub cs: ConstraintSystemRef,
    pub query_positions_per_log_size: QueryPositionsPerLogSizeVar,
    pub fri_answers: ColumnVec<Vec<QM31Var>>,
    pub domain_points: ColumnVec<Vec<CirclePointM31Var>>,
}

impl LastAnswerResults {
    pub fn compute(
        fiat_shamir_hints: &FiatShamirHints<Sha256Poseidon31MerkleChannel>,
        decommit_hints: &LastDecommitHints,
        fri_answer_hints: &AnswerHints<Sha256Poseidon31MerkleChannel>,
        last_fiat_shamir_results: &LastFiatShamirResults,
        last_decommit_input_var: &LastDecommitInputVar,
        proof: &LastPlonkWithPoseidonProofVar,
        pcs_config: PcsConfig,
    ) -> Self {
        let cs = last_fiat_shamir_results.oods_point.cs();

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

        let oods_point = &last_fiat_shamir_results.oods_point;

        let mut shifted_points_plonk = HashMap::<isize, CirclePointQM31Var>::new();
        let mut shifted_points_poseidon = HashMap::<isize, CirclePointQM31Var>::new();
        for &i in all_shifts_plonk.iter() {
            shifted_points_plonk.insert(i, oods_point.add(&trace_step_plonk.mul_signed(i)));
        }
        for &i in all_shifts_poseidon.iter() {
            shifted_points_poseidon.insert(i, oods_point.add(&trace_step_poseidon.mul_signed(i)));
        }

        let mut mask_points_plonk: TreeVec<ColumnVec<Vec<(ShiftIndex, CirclePointQM31Var)>>> =
            fiat_shamir_hints.mask_plonk.as_ref().map_cols(|column| {
                column
                    .iter()
                    .map(|shift| {
                        (
                            ShiftIndex::from_shift(*shift, fiat_shamir_hints.log_size_plonk),
                            shifted_points_plonk.get(shift).unwrap().clone(),
                        )
                    })
                    .collect_vec()
            });
        mask_points_plonk[PREPROCESSED_TRACE_IDX] =
            vec![vec![(ShiftIndex::Zero, oods_point.clone())]; 10];
        let mut mask_points_poseidon: TreeVec<ColumnVec<Vec<(ShiftIndex, CirclePointQM31Var)>>> =
            fiat_shamir_hints.mask_poseidon.as_ref().map_cols(|column| {
                column
                    .iter()
                    .map(|shift| {
                        (
                            ShiftIndex::from_shift(*shift, fiat_shamir_hints.log_size_poseidon),
                            shifted_points_poseidon.get(shift).unwrap().clone(),
                        )
                    })
                    .collect_vec()
            });
        mask_points_poseidon[PREPROCESSED_TRACE_IDX] =
            vec![vec![(ShiftIndex::Zero, oods_point.clone())]; 40];

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
                for (shift_idx, (_, shifted_point)) in column.iter().enumerate() {
                    assert_eq!(
                        shifted_point.x.value(),
                        fiat_shamir_hints.sample_points[round_idx][column_idx][shift_idx].x
                    );
                    assert_eq!(
                        shifted_point.y.value(),
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
                for (shift_idx, (_, shifted_point)) in column.iter().enumerate() {
                    assert_eq!(
                        shifted_point.x.value(),
                        fiat_shamir_hints.sample_points[round_idx][round_plonk.len() + column_idx]
                            [shift_idx]
                            .x
                    );
                    assert_eq!(
                        shifted_point.y.value(),
                        fiat_shamir_hints.sample_points[round_idx][round_plonk.len() + column_idx]
                            [shift_idx]
                            .y
                    );
                }
            }
        }

        let mut sampled_points =
            TreeVec::concat_cols([mask_points_plonk, mask_points_poseidon].into_iter());
        sampled_points.push(vec![vec![(ShiftIndex::Zero, oods_point.clone())]; 8]);

        let samples = sampled_points
            .zip_cols(proof.stark_proof.sampled_values.clone())
            .map_cols(|(sampled_points, sampled_values)| {
                zip(sampled_points, sampled_values)
                    .map(|((shift, point), value)| PointSampleVar {
                        shift,
                        point,
                        value,
                    })
                    .collect_vec()
            });

        let query_positions_per_log_size = QueryPositionsPerLogSizeVar::new(
            pcs_config.fri_config.log_blowup_factor + 1
                ..=fiat_shamir_hints.max_first_layer_column_log_size,
            &last_fiat_shamir_results.queries_at_max_first_layer_column_log_size,
        );

        for &column_log_size in fiat_shamir_hints.all_log_sizes.iter() {
            let mut sorted_queries = vec![];
            for query in query_positions_per_log_size[column_log_size].iter() {
                sorted_queries.push(query.bits.get_value().0 as usize);
            }
            sorted_queries.sort_unstable();
            sorted_queries.dedup();

            if column_log_size == fiat_shamir_hints.max_first_layer_column_log_size {
                assert_eq!(sorted_queries.len(), pcs_config.fri_config.n_queries,
                           "The implementation does not support the situation when the first {} attempts in sampling queries end up duplicated queries",
                           pcs_config.fri_config.n_queries
                );
            }

            assert_eq!(
                sorted_queries,
                fiat_shamir_hints.sorted_query_positions_per_log_size[&column_log_size]
            );
        }
        for &column_log_size in fiat_shamir_hints.all_log_sizes.iter() {
            let mut unsorted_queries = vec![];
            for query in query_positions_per_log_size[column_log_size].iter() {
                unsorted_queries.push(query.bits.get_value().0 as usize);
            }

            assert_eq!(
                unsorted_queries,
                fiat_shamir_hints.unsorted_query_positions_per_log_size[&column_log_size]
            );
        }

        let last_decommit_var = LastDecommitVar::compute(&last_decommit_input_var, &decommit_hints);

        let mut queried_values = BTreeMap::new();
        for &log_size in fiat_shamir_hints.all_log_sizes.iter() {
            let mut queried_values_this_log_size = Vec::new();
            for (i, _) in query_positions_per_log_size[log_size].iter().enumerate() {
                let mut v = vec![];
                v.extend_from_slice(
                    &last_decommit_var.precomputed_proofs[i]
                        .columns
                        .get(&(log_size as usize))
                        .unwrap_or(&vec![]),
                );
                v.extend_from_slice(
                    &last_decommit_var.trace_proofs[i]
                        .columns
                        .get(&(log_size as usize))
                        .unwrap_or(&vec![]),
                );
                v.extend_from_slice(
                    &last_decommit_var.interaction_proofs[i]
                        .columns
                        .get(&(log_size as usize))
                        .unwrap_or(&vec![]),
                );
                v.extend_from_slice(
                    &last_decommit_var.composition_proofs[i]
                        .columns
                        .get(&(log_size as usize))
                        .unwrap_or(&vec![]),
                );
                queried_values_this_log_size.push(v);
            }
            queried_values.insert(log_size, queried_values_this_log_size);
        }

        let mut fri_answers = ColumnVec::<Vec<QM31Var>>::new();
        let mut domain_points = ColumnVec::<Vec<CirclePointM31Var>>::new();

        izip!(
            fiat_shamir_hints.column_log_sizes.clone().flatten(),
            samples.flatten().iter()
        )
        .sorted_by_key(|(log_size, ..)| Reverse(*log_size))
        .chunk_by(|(log_size, ..)| *log_size)
        .into_iter()
        .for_each(|(log_size, tuples)| {
            let (_, samples): (Vec<_>, Vec<_>) = multiunzip(tuples);
            let (domain_points_per_log_size, fri_answers_per_log_size) =
                AnswerResults::fri_answers_for_log_size(
                    &samples,
                    &last_fiat_shamir_results.after_sampled_values_random_coeff,
                    &query_positions_per_log_size[log_size],
                    &queried_values[&log_size],
                );
            domain_points.push(domain_points_per_log_size);
            fri_answers.push(fri_answers_per_log_size);
        });

        let mut log_sizes = fiat_shamir_hints
            .all_log_sizes
            .iter()
            .copied()
            .collect_vec();
        log_sizes.sort_by_key(|log_size| Reverse(*log_size));

        for ((log_size, fri_answers), sorted_fri_answers) in log_sizes
            .iter()
            .zip(fri_answers.iter())
            .zip(fri_answer_hints.fri_answers.iter())
        {
            let mut map = BTreeMap::new();
            for (k, v) in fiat_shamir_hints.sorted_query_positions_per_log_size[log_size]
                .iter()
                .zip(sorted_fri_answers.iter())
            {
                map.insert(*k, *v);
            }

            for (k, v) in query_positions_per_log_size[*log_size]
                .iter()
                .zip(fri_answers.iter())
            {
                assert_eq!(
                    *map.get(&(k.bits.get_value().0 as usize)).unwrap(),
                    v.value()
                );
            }
        }

        Self {
            cs,
            query_positions_per_log_size,
            fri_answers,
            domain_points,
        }
    }
}

#[cfg(test)]
mod test {
    use crate::data_structures::{LastDecommitHints, LastDecommitInput, LastDecommitInputVar};
    use crate::LastAnswerResults;
    use circle_plonk_dsl_constraint_system::var::AllocVar;
    use circle_plonk_dsl_constraint_system::ConstraintSystemRef;
    use circle_plonk_dsl_hints::{AnswerHints, FiatShamirHints};
    use circle_plonk_dsl_last_data_structures::LastPlonkWithPoseidonProofVar;
    use circle_plonk_dsl_last_fiat_shamir::{
        LastFiatShamirInput, LastFiatShamirInputVar, LastFiatShamirResults,
    };
    use num_traits::One;
    use stwo::core::fields::qm31::QM31;
    use stwo::core::fri::FriConfig;
    use stwo::core::pcs::PcsConfig;
    use stwo::core::vcs::sha256_merkle::Sha256MerkleChannel;
    use stwo::core::vcs::sha256_poseidon31_merkle::{
        Sha256Poseidon31MerkleChannel, Sha256Poseidon31MerkleHasher,
    };
    use stwo_examples::plonk_with_poseidon::air::{
        verify_plonk_with_poseidon, PlonkWithPoseidonProof,
    };
    use stwo_examples::plonk_without_poseidon::air::{
        prove_plonk_without_poseidon, verify_plonk_without_poseidon,
    };

    #[test]
    fn test_last_answer() {
        let proof: PlonkWithPoseidonProof<Sha256Poseidon31MerkleHasher> =
            bincode::deserialize(include_bytes!("../../../test_data/hybrid_hash.bin")).unwrap();
        let config = PcsConfig {
            pow_bits: 28,
            fri_config: FriConfig::new(7, 9, 8),
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
        let decommit_hints = LastDecommitHints::from_proof(&fiat_shamir_hints, &proof);

        let fiat_shamir_input = LastFiatShamirInput::from_proof(&proof, &fiat_shamir_hints);
        let decommit_input = LastDecommitInput::from_hints(&decommit_hints);
        let fiat_shamir_input_var =
            LastFiatShamirInputVar::new_public_input(&cs, &fiat_shamir_input);
        let decommit_input_var = LastDecommitInputVar::new_public_input(&cs, &decommit_input);
        let fri_answer_hints = AnswerHints::compute(&fiat_shamir_hints, &proof);

        let proof_var = LastPlonkWithPoseidonProofVar::new_witness(&cs, &proof);
        let fiat_shamir_results =
            LastFiatShamirResults::compute(&proof_var, &fiat_shamir_input_var);

        let _last_answer_results = LastAnswerResults::compute(
            &fiat_shamir_hints,
            &decommit_hints,
            &fri_answer_hints,
            &fiat_shamir_results,
            &decommit_input_var,
            &proof_var,
            config,
        );

        cs.pad();
        cs.check_arithmetics();
        cs.populate_logup_arguments();

        let config = PcsConfig {
            pow_bits: 20,
            fri_config: FriConfig::new(7, 5, 16),
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

        println!("input length: {} QM31", inputs.len());

        let circuit = cs.generate_plonk_without_poseidon_circuit();
        let proof = prove_plonk_without_poseidon::<Sha256MerkleChannel>(config, &circuit);
        verify_plonk_without_poseidon::<Sha256MerkleChannel>(proof, config, &inputs).unwrap();
    }
}
