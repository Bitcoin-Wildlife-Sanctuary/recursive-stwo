use circle_plonk_dsl_constraint_system::dvar::DVar;
use circle_plonk_dsl_fields::{M31Var, QM31Var};
use circle_plonk_dsl_poseidon31::Poseidon2HalfStateRef;
use std::cmp::min;

pub struct Poseidon31MerkleHasherVar;

impl Poseidon31MerkleHasherVar {
    pub fn hash_qm31_columns_get_rate(qm31: &[QM31Var]) -> Poseidon2HalfStateRef {
        assert_eq!(qm31.len(), 2);

        let cs = qm31[0].cs.and(&qm31[1].cs);
        let left_value = qm31[0].value.to_m31_array();
        let right_value = qm31[1].value.to_m31_array();
        let left_variable = qm31[0].variable;
        let right_variable = qm31[1].variable;
        let half_state_variable = cs.assemble_poseidon_gate(left_variable, right_variable);

        let left = Poseidon2HalfStateRef {
            cs: cs.clone(),
            value: std::array::from_fn(|i| {
                if i < 4 {
                    left_value[i]
                } else {
                    right_value[i - 4]
                }
            }),
            left_variable,
            right_variable,
            sel_value: half_state_variable,
        };

        let zero = Poseidon2HalfStateRef::zero(&cs);
        Poseidon2HalfStateRef::permute_get_rate(&left, &zero)
    }

    pub fn hash_qm31_columns_get_capacity(qm31: &[QM31Var]) -> Poseidon2HalfStateRef {
        assert_eq!(qm31.len(), 2);

        let cs = qm31[0].cs.and(&qm31[1].cs);
        let left_value = qm31[0].value.to_m31_array();
        let right_value = qm31[1].value.to_m31_array();
        let left_variable = qm31[0].variable;
        let right_variable = qm31[1].variable;
        let half_state_variable = cs.assemble_poseidon_gate(left_variable, right_variable);

        let left = Poseidon2HalfStateRef {
            cs: cs.clone(),
            value: std::array::from_fn(|i| {
                if i < 4 {
                    left_value[i]
                } else {
                    right_value[i - 4]
                }
            }),
            left_variable,
            right_variable,
            sel_value: half_state_variable,
        };

        let zero = Poseidon2HalfStateRef::zero(&cs);
        Poseidon2HalfStateRef::permute_get_capacity(&left, &zero)
    }

    pub fn hash_tree(
        left: &Poseidon2HalfStateRef,
        right: &Poseidon2HalfStateRef,
    ) -> Poseidon2HalfStateRef {
        Poseidon2HalfStateRef::permute_get_rate(left, right)
    }

    pub fn hash_tree_with_column(
        left: &Poseidon2HalfStateRef,
        right: &Poseidon2HalfStateRef,
        hash_column: &Poseidon2HalfStateRef,
    ) -> Poseidon2HalfStateRef {
        let hash_tree = Poseidon2HalfStateRef::permute_get_rate(left, right);
        Poseidon2HalfStateRef::permute_get_rate(&hash_tree, hash_column)
    }

    pub fn hash_tree_with_swap(
        left: &Poseidon2HalfStateRef,
        right: &Poseidon2HalfStateRef,
        bit_value: bool,
        bit_variable: usize,
    ) -> Poseidon2HalfStateRef {
        Poseidon2HalfStateRef::swap_permute_get_rate(&left, &right, bit_variable, bit_value)
    }

    pub fn hash_tree_with_column_hash_with_swap(
        left: &Poseidon2HalfStateRef,
        right: &Poseidon2HalfStateRef,
        bit_value: bool,
        bit_variable: usize,
        column_hash: &Poseidon2HalfStateRef,
    ) -> Poseidon2HalfStateRef {
        let hash_tree =
            Poseidon2HalfStateRef::swap_permute_get_rate(&left, &right, bit_variable, bit_value);
        Poseidon2HalfStateRef::permute_get_rate(&hash_tree, column_hash)
    }

    pub fn combine_hash_tree_with_column(
        hash_tree: &Poseidon2HalfStateRef,
        hash_column: &Poseidon2HalfStateRef,
    ) -> Poseidon2HalfStateRef {
        Poseidon2HalfStateRef::permute_get_rate(hash_tree, hash_column)
    }

    pub fn hash_m31_columns_get_rate(m31: &[M31Var]) -> Poseidon2HalfStateRef {
        let len = m31.len();
        let num_chunk = len.div_ceil(8);
        let cs = m31[0].cs();

        // compute the first hash, which consists of 8 elements, and it comes from (no more than)
        // 16 elements

        let mut input: [M31Var; 8] = std::array::from_fn(|_| M31Var::zero(&cs));
        input[0..min(len, 8)].clone_from_slice(&m31[0..min(len, 8)]);

        let zero = Poseidon2HalfStateRef::zero(&cs);
        let first_chunk = Poseidon2HalfStateRef::from_m31(&input[0..8]);

        if num_chunk == 1 {
            return Poseidon2HalfStateRef::permute_get_rate(&first_chunk, &zero);
        }

        let mut digest = Poseidon2HalfStateRef::permute_get_capacity(&first_chunk, &zero);
        for chunk in m31.chunks_exact(8).skip(1).take(num_chunk - 2) {
            let left = Poseidon2HalfStateRef::from_m31(&chunk);
            digest = Poseidon2HalfStateRef::permute_get_capacity(&left, &digest);
        }

        let remain = len % 8;
        if remain == 0 {
            let mut input: [M31Var; 8] = std::array::from_fn(|_| M31Var::zero(&cs));
            input[0..8].clone_from_slice(&m31[len - 8..]);

            let left = Poseidon2HalfStateRef::from_m31(&input);
            digest = Poseidon2HalfStateRef::permute_get_rate(&left, &digest);
        } else {
            let mut input: [M31Var; 8] = std::array::from_fn(|_| M31Var::zero(&cs));
            input[0..remain].clone_from_slice(&m31[len - remain..]);

            let left = Poseidon2HalfStateRef::from_m31(&input);
            digest = Poseidon2HalfStateRef::permute_get_rate(&left, &digest);
        }

        digest
    }

    pub fn hash_m31_columns_get_capacity(m31: &[M31Var]) -> Poseidon2HalfStateRef {
        let len = m31.len();
        let num_chunk = len.div_ceil(8);
        let cs = m31[0].cs();

        // compute the first hash, which consists of 8 elements, and it comes from (no more than)
        // 16 elements

        let mut input: [M31Var; 8] = std::array::from_fn(|_| M31Var::zero(&cs));
        input[0..min(len, 8)].clone_from_slice(&m31[0..min(len, 8)]);

        let zero = Poseidon2HalfStateRef::zero(&cs);
        let first_chunk = Poseidon2HalfStateRef::from_m31(&input[0..8]);

        if num_chunk == 1 {
            return Poseidon2HalfStateRef::permute_get_capacity(&first_chunk, &zero);
        }

        let mut digest = Poseidon2HalfStateRef::permute_get_capacity(&first_chunk, &zero);
        for chunk in m31.chunks_exact(8).skip(1).take(num_chunk - 2) {
            let left = Poseidon2HalfStateRef::from_m31(&chunk);
            digest = Poseidon2HalfStateRef::permute_get_capacity(&left, &digest);
        }

        let remain = len % 8;
        if remain == 0 {
            let mut input: [M31Var; 8] = std::array::from_fn(|_| M31Var::zero(&cs));
            input[0..8].clone_from_slice(&m31[len - 8..]);

            let left = Poseidon2HalfStateRef::from_m31(&input);
            digest = Poseidon2HalfStateRef::permute_get_capacity(&left, &digest);
        } else {
            let mut input: [M31Var; 8] = std::array::from_fn(|_| M31Var::zero(&cs));
            input[0..remain].clone_from_slice(&m31[len - remain..]);

            let left = Poseidon2HalfStateRef::from_m31(&input);
            digest = Poseidon2HalfStateRef::permute_get_capacity(&left, &digest);
        }

        digest
    }
}

#[cfg(test)]
mod test {
    use crate::Poseidon31MerkleHasherVar;
    use circle_plonk_dsl_constraint_system::dvar::AllocVar;
    use circle_plonk_dsl_constraint_system::ConstraintSystemRef;
    use circle_plonk_dsl_fields::M31Var;
    use circle_plonk_dsl_poseidon31::Poseidon2HalfStateRef;
    use num_traits::One;
    use rand::rngs::SmallRng;
    use rand::{Rng, SeedableRng};
    use stwo_prover::core::fields::m31::M31;
    use stwo_prover::core::fields::qm31::QM31;
    use stwo_prover::core::fri::FriConfig;
    use stwo_prover::core::pcs::PcsConfig;
    use stwo_prover::core::vcs::ops::MerkleHasher;
    use stwo_prover::core::vcs::poseidon31_hash::Poseidon31Hash;
    use stwo_prover::core::vcs::poseidon31_merkle::{
        Poseidon31MerkleChannel, Poseidon31MerkleHasher,
    };
    use stwo_prover::examples::plonk_with_poseidon::air::{
        prove_plonk_with_poseidon, verify_plonk_with_poseidon,
    };

    #[test]
    fn test_consistency() {
        let mut prng = SmallRng::seed_from_u64(0);
        let test: [M31; 25] = prng.gen();

        let cs = ConstraintSystemRef::new_ref();
        let mut test_var = vec![];
        for v in test.iter() {
            test_var.push(M31Var::new_constant(&cs, v));
        }

        // test 7
        let a = Poseidon31MerkleHasherVar::hash_m31_columns_get_rate(&test_var[0..7]);
        let b = Poseidon31MerkleHasher::hash_node(None, &test[0..7]);
        for i in 0..8 {
            assert_eq!(a.value[i], b.0[i]);
        }

        // test 13
        let a = Poseidon31MerkleHasherVar::hash_m31_columns_get_rate(&test_var[0..13]);
        let b = Poseidon31MerkleHasher::hash_node(None, &test[0..13]);
        for i in 0..8 {
            assert_eq!(a.value[i], b.0[i]);
        }

        // test 16
        let a = Poseidon31MerkleHasherVar::hash_m31_columns_get_rate(&test_var[0..16]);
        let b = Poseidon31MerkleHasher::hash_node(None, &test[0..16]);
        for i in 0..8 {
            assert_eq!(a.value[i], b.0[i]);
        }

        // test 17
        let a = Poseidon31MerkleHasherVar::hash_m31_columns_get_rate(&test_var[0..17]);
        let b = Poseidon31MerkleHasher::hash_node(None, &test[0..17]);
        for i in 0..8 {
            assert_eq!(a.value[i], b.0[i]);
        }

        // test 21
        let a = Poseidon31MerkleHasherVar::hash_m31_columns_get_rate(&test_var[0..21]);
        let b = Poseidon31MerkleHasher::hash_node(None, &test[0..21]);
        for i in 0..8 {
            assert_eq!(a.value[i], b.0[i]);
        }

        // test 25
        let a = Poseidon31MerkleHasherVar::hash_m31_columns_get_rate(&test_var[0..25]);
        let b = Poseidon31MerkleHasher::hash_node(None, &test[0..25]);
        for i in 0..8 {
            assert_eq!(a.value[i], b.0[i]);
        }

        let test_hash_left: [M31; 8] = prng.gen();
        let test_hash_right: [M31; 8] = prng.gen();
        let test_hash_column: [M31; 8] = prng.gen();

        let test_hash_left_var = Poseidon2HalfStateRef::new_witness(&cs, &test_hash_left);
        let test_hash_right_var = Poseidon2HalfStateRef::new_witness(&cs, &test_hash_right);
        let test_hash_column_var: [M31Var; 8] =
            std::array::from_fn(|i| M31Var::new_witness(&cs, &test_hash_column[i]));

        let a = Poseidon31MerkleHasherVar::hash_tree(&test_hash_left_var, &test_hash_right_var);
        let b = Poseidon31MerkleHasher::hash_node(
            Some((
                Poseidon31Hash(test_hash_left),
                Poseidon31Hash(test_hash_right),
            )),
            &[],
        );
        for i in 0..8 {
            assert_eq!(a.value[i], b.0[i]);
        }

        let test_hash_right_var = Poseidon2HalfStateRef::new_witness(&cs, &test_hash_right);

        let a = Poseidon31MerkleHasherVar::hash_tree_with_column(
            &test_hash_left_var,
            &test_hash_right_var,
            &Poseidon31MerkleHasherVar::hash_m31_columns_get_capacity(&test_hash_column_var),
        );
        let b = Poseidon31MerkleHasher::hash_node(
            Some((
                Poseidon31Hash(test_hash_left),
                Poseidon31Hash(test_hash_right),
            )),
            &test_hash_column,
        );
        for i in 0..8 {
            assert_eq!(a.value[i], b.0[i]);
        }

        let config = PcsConfig {
            pow_bits: 20,
            fri_config: FriConfig::new(0, 5, 16),
        };

        cs.pad();
        cs.check_arithmetics();
        cs.populate_logup_arguments();
        cs.check_poseidon_invocations();

        let (plonk, mut poseidon) = cs.generate_circuit();
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
