use circle_plonk_dsl_constraint_system::var::Var;
use circle_plonk_dsl_fields::{M31Var, QM31Var};
use circle_plonk_dsl_poseidon31::Poseidon2HalfVar;
use std::cmp::min;

pub struct Poseidon31MerkleHasherVar;

impl Poseidon31MerkleHasherVar {
    pub fn hash_tree(left: &Poseidon2HalfVar, right: &Poseidon2HalfVar) -> Poseidon2HalfVar {
        Poseidon2HalfVar::permute_get_rate(left, right)
    }

    pub fn hash_tree_with_column(
        left: &Poseidon2HalfVar,
        right: &Poseidon2HalfVar,
        hash_column: &Poseidon2HalfVar,
    ) -> Poseidon2HalfVar {
        let hash_tree = Poseidon2HalfVar::permute_get_rate(left, right);
        Poseidon2HalfVar::permute_get_rate(&hash_tree, hash_column)
    }

    pub fn hash_tree_with_swap(
        left: &Poseidon2HalfVar,
        right: &Poseidon2HalfVar,
        bit_value: bool,
        bit_variable: usize,
    ) -> Poseidon2HalfVar {
        Poseidon2HalfVar::swap_permute_get_rate(&left, &right, Some((bit_value, bit_variable)))
    }

    pub fn hash_tree_with_column_hash_with_swap(
        left: &Poseidon2HalfVar,
        right: &Poseidon2HalfVar,
        bit_value: bool,
        bit_variable: usize,
        column_hash: &Poseidon2HalfVar,
    ) -> Poseidon2HalfVar {
        let hash_tree =
            Poseidon2HalfVar::swap_permute_get_rate(&left, &right, Some((bit_value, bit_variable)));
        Poseidon2HalfVar::permute_get_rate(&hash_tree, column_hash)
    }

    pub fn combine_hash_tree_with_column(
        hash_tree: &Poseidon2HalfVar,
        hash_column: &Poseidon2HalfVar,
    ) -> Poseidon2HalfVar {
        Poseidon2HalfVar::permute_get_rate(hash_tree, hash_column)
    }

    pub fn hash_m31_columns_get_rate(m31: &[M31Var]) -> Poseidon2HalfVar {
        let len = m31.len();
        let num_chunk = len.div_ceil(8);
        let cs = m31[0].cs();

        // compute the first hash, which consists of 8 elements, and it comes from (no more than)
        // 16 elements

        let mut input: [M31Var; 8] = std::array::from_fn(|_| M31Var::zero(&cs));
        input[0..min(len, 8)].clone_from_slice(&m31[0..min(len, 8)]);

        let zero = Poseidon2HalfVar::zero(&cs);
        let first_chunk = Poseidon2HalfVar::from_m31(&input[0..8]);

        if num_chunk == 1 {
            let digest = Poseidon2HalfVar::permute_get_capacity(&first_chunk, &zero);
            return Poseidon2HalfVar::permute_get_rate(&Poseidon2HalfVar::zero(&cs), &digest);
        }

        let mut digest = Poseidon2HalfVar::permute_get_capacity(&first_chunk, &zero);
        for chunk in m31.chunks_exact(8).skip(1).take(num_chunk - 2) {
            let left = Poseidon2HalfVar::from_m31(&chunk);
            digest = Poseidon2HalfVar::permute_get_capacity(&left, &digest);
        }

        let remain = len % 8;
        if remain == 0 {
            let mut input: [M31Var; 8] = std::array::from_fn(|_| M31Var::zero(&cs));
            input[0..8].clone_from_slice(&m31[len - 8..]);

            let left = Poseidon2HalfVar::from_m31(&input);
            digest = Poseidon2HalfVar::permute_get_capacity(&left, &digest);
        } else {
            let mut input: [M31Var; 8] = std::array::from_fn(|_| M31Var::zero(&cs));
            input[0..remain].clone_from_slice(&m31[len - remain..]);

            let left = Poseidon2HalfVar::from_m31(&input);
            digest = Poseidon2HalfVar::permute_get_capacity(&left, &digest);
        }

        Poseidon2HalfVar::permute_get_rate(&Poseidon2HalfVar::zero(&cs), &digest)
    }

    pub fn hash_qm31_columns_get_rate(qm31: &[QM31Var]) -> Poseidon2HalfVar {
        let cs = qm31[0].cs();
        let digest = Self::hash_qm31_columns_get_capacity(qm31);
        Poseidon2HalfVar::permute_get_rate(&Poseidon2HalfVar::zero(&cs), &digest)
    }

    pub fn hash_qm31_columns_get_capacity(qm31: &[QM31Var]) -> Poseidon2HalfVar {
        let len = qm31.len();
        let num_chunk = len.div_ceil(2);
        let cs = qm31[0].cs();

        // compute the first hash, which consists of 8 elements, and it comes from (no more than)
        // 16 elements

        let mut input: [QM31Var; 2] = std::array::from_fn(|_| QM31Var::zero(&cs));
        input[0..min(len, 2)].clone_from_slice(&qm31[0..min(len, 2)]);

        let zero = Poseidon2HalfVar::zero(&cs);
        let first_chunk = Poseidon2HalfVar::from_qm31(&input[0], &input[1]);

        if num_chunk == 1 {
            return Poseidon2HalfVar::permute_get_capacity(&first_chunk, &zero);
        }

        let mut digest = Poseidon2HalfVar::permute_get_capacity(&first_chunk, &zero);
        for chunk in qm31.chunks_exact(2).skip(1).take(num_chunk - 2) {
            let left = Poseidon2HalfVar::from_qm31(&chunk[0], &chunk[1]);
            digest = Poseidon2HalfVar::permute_get_capacity(&left, &digest);
        }

        let remain = len % 2;
        if remain == 0 {
            let mut input: [QM31Var; 2] = std::array::from_fn(|_| QM31Var::zero(&cs));
            input[0..2].clone_from_slice(&qm31[len - 2..]);

            let left = Poseidon2HalfVar::from_qm31(&input[0], &input[1]);
            digest = Poseidon2HalfVar::permute_get_capacity(&left, &digest);
        } else {
            let mut input: [QM31Var; 2] = std::array::from_fn(|_| QM31Var::zero(&cs));
            input[0..remain].clone_from_slice(&qm31[len - remain..]);

            let left = Poseidon2HalfVar::from_qm31(&input[0], &input[1]);
            digest = Poseidon2HalfVar::permute_get_capacity(&left, &digest);
        }

        digest
    }

    pub fn hash_m31_columns_get_capacity(m31: &[M31Var]) -> Poseidon2HalfVar {
        let len = m31.len();
        let num_chunk = len.div_ceil(8);
        let cs = m31[0].cs();

        // compute the first hash, which consists of 8 elements, and it comes from (no more than)
        // 16 elements

        let mut input: [M31Var; 8] = std::array::from_fn(|_| M31Var::zero(&cs));
        input[0..min(len, 8)].clone_from_slice(&m31[0..min(len, 8)]);

        let zero = Poseidon2HalfVar::zero(&cs);
        let first_chunk = Poseidon2HalfVar::from_m31(&input[0..8]);

        if num_chunk == 1 {
            return Poseidon2HalfVar::permute_get_capacity(&first_chunk, &zero);
        }

        let mut digest = Poseidon2HalfVar::permute_get_capacity(&first_chunk, &zero);
        for chunk in m31.chunks_exact(8).skip(1).take(num_chunk - 2) {
            let left = Poseidon2HalfVar::from_m31(&chunk);
            digest = Poseidon2HalfVar::permute_get_capacity(&left, &digest);
        }

        let remain = len % 8;
        if remain == 0 {
            let mut input: [M31Var; 8] = std::array::from_fn(|_| M31Var::zero(&cs));
            input[0..8].clone_from_slice(&m31[len - 8..]);

            let left = Poseidon2HalfVar::from_m31(&input);
            digest = Poseidon2HalfVar::permute_get_capacity(&left, &digest);
        } else {
            let mut input: [M31Var; 8] = std::array::from_fn(|_| M31Var::zero(&cs));
            input[0..remain].clone_from_slice(&m31[len - remain..]);

            let left = Poseidon2HalfVar::from_m31(&input);
            digest = Poseidon2HalfVar::permute_get_capacity(&left, &digest);
        }

        digest
    }
}

#[cfg(test)]
mod test {
    use crate::Poseidon31MerkleHasherVar;
    use circle_plonk_dsl_constraint_system::var::AllocVar;
    use circle_plonk_dsl_constraint_system::ConstraintSystemRef;
    use circle_plonk_dsl_fields::M31Var;
    use circle_plonk_dsl_poseidon31::Poseidon2HalfVar;
    use num_traits::One;
    use rand::rngs::SmallRng;
    use rand::{Rng, SeedableRng};
    use stwo::core::fields::m31::M31;
    use stwo::core::fields::qm31::QM31;
    use stwo::core::fri::FriConfig;
    use stwo::core::pcs::PcsConfig;
    use stwo::core::vcs::poseidon31_hash::Poseidon31Hash;
    use stwo::core::vcs::poseidon31_merkle::{Poseidon31MerkleChannel, Poseidon31MerkleHasher};
    use stwo::core::vcs::MerkleHasher;
    use stwo_examples::plonk_with_poseidon::air::{
        prove_plonk_with_poseidon, verify_plonk_with_poseidon,
    };

    #[test]
    fn test_consistency() {
        let mut prng = SmallRng::seed_from_u64(0);
        let test: [M31; 25] = prng.gen();

        let cs = ConstraintSystemRef::new_plonk_with_poseidon_ref();
        let mut test_var = vec![];
        for v in test.iter() {
            test_var.push(M31Var::new_constant(&cs, v));
        }

        // test 7
        let a = Poseidon31MerkleHasherVar::hash_m31_columns_get_rate(&test_var[0..7]);
        let b = Poseidon31MerkleHasher::hash_node(None, &test[0..7]);
        let a_val = a.value();
        for i in 0..8 {
            assert_eq!(a_val[i], b.0[i]);
        }

        // test 13
        let a = Poseidon31MerkleHasherVar::hash_m31_columns_get_rate(&test_var[0..13]);
        let b = Poseidon31MerkleHasher::hash_node(None, &test[0..13]);
        let a_val = a.value();
        for i in 0..8 {
            assert_eq!(a_val[i], b.0[i]);
        }

        // test 16
        let a = Poseidon31MerkleHasherVar::hash_m31_columns_get_rate(&test_var[0..16]);
        let b = Poseidon31MerkleHasher::hash_node(None, &test[0..16]);
        let a_val = a.value();
        for i in 0..8 {
            assert_eq!(a_val[i], b.0[i]);
        }

        // test 17
        let a = Poseidon31MerkleHasherVar::hash_m31_columns_get_rate(&test_var[0..17]);
        let b = Poseidon31MerkleHasher::hash_node(None, &test[0..17]);
        let a_val = a.value();
        for i in 0..8 {
            assert_eq!(a_val[i], b.0[i]);
        }

        // test 21
        let a = Poseidon31MerkleHasherVar::hash_m31_columns_get_rate(&test_var[0..21]);
        let b = Poseidon31MerkleHasher::hash_node(None, &test[0..21]);
        let a_val = a.value();
        for i in 0..8 {
            assert_eq!(a_val[i], b.0[i]);
        }

        // test 25
        let a = Poseidon31MerkleHasherVar::hash_m31_columns_get_rate(&test_var[0..25]);
        let b = Poseidon31MerkleHasher::hash_node(None, &test[0..25]);
        let a_val = a.value();
        for i in 0..8 {
            assert_eq!(a_val[i], b.0[i]);
        }

        let test_hash_left: [M31; 8] = prng.gen();
        let test_hash_right: [M31; 8] = prng.gen();
        let test_hash_column: [M31; 8] = prng.gen();

        let test_hash_left_var = Poseidon2HalfVar::new_witness(&cs, &test_hash_left);
        let test_hash_right_var = Poseidon2HalfVar::new_witness(&cs, &test_hash_right);
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
        let a_val = a.value();
        for i in 0..8 {
            assert_eq!(a_val[i], b.0[i]);
        }

        let test_hash_right_var = Poseidon2HalfVar::new_witness(&cs, &test_hash_right);

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
        let a_val = a.value();
        for i in 0..8 {
            assert_eq!(a_val[i], b.0[i]);
        }

        let config = PcsConfig {
            pow_bits: 20,
            fri_config: FriConfig::new(0, 5, 16),
        };

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
