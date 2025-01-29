use circle_plonk_dsl_constraint_system::dvar::{AllocationMode, DVar};
use circle_plonk_dsl_fields::{M31Var, QM31Var};
use circle_plonk_dsl_poseidon31::Poseidon2HalfStateRef;
use std::cmp::min;
use stwo_prover::core::fields::m31::M31;

pub struct Poseidon31MerkleHasherVar;

impl Poseidon31MerkleHasherVar {
    pub fn hash_qm31_columns(qm31: &[QM31Var]) -> Poseidon2HalfStateRef {
        assert_eq!(qm31.len(), 2);

        let cs = qm31[0].cs.and(&qm31[1].cs);
        let left_value = qm31[0].value.to_m31_array();
        let right_value = qm31[1].value.to_m31_array();
        let left_variable = qm31[0].variable;
        let right_variable = qm31[1].variable;
        let half_state_variable = cs.mul(left_variable, right_variable);
        let addr_variable = cs.new_m31(M31::from(half_state_variable), AllocationMode::Constant);

        Poseidon2HalfStateRef {
            cs,
            value: std::array::from_fn(|i| {
                if i < 4 {
                    left_value[i]
                } else {
                    right_value[i - 4]
                }
            }),
            left_variable,
            right_variable,
            half_state_variable,
            addr_variable,
            disabled: false,
        }
    }

    pub fn hash_tree(
        left: &mut Poseidon2HalfStateRef,
        right: &mut Poseidon2HalfStateRef,
    ) -> Poseidon2HalfStateRef {
        // assume that a witness must be used
        assert!(left.addr_variable == 0 || right.addr_variable == 0);

        let (parent, _) = Poseidon2HalfStateRef::permute(left, right, false, true);
        parent
    }

    pub fn hash_tree_with_swap(
        left: &mut Poseidon2HalfStateRef,
        right: &mut Poseidon2HalfStateRef,
        bit_value: bool,
        bit_variable: usize,
    ) -> Poseidon2HalfStateRef {
        Poseidon2HalfStateRef::swap_compress(left, right, bit_value, bit_variable)
    }

    pub fn hash_tree_with_column_hash_with_swap(
        left: &mut Poseidon2HalfStateRef,
        right: &mut Poseidon2HalfStateRef,
        bit_value: bool,
        bit_variable: usize,
        column_hash: &mut Poseidon2HalfStateRef,
    ) -> Poseidon2HalfStateRef {
        let mut hash_tree = Poseidon2HalfStateRef::swap_compress(left, right, bit_value, bit_variable);
        Self::combine_hash_tree_with_column(&mut hash_tree, column_hash)
    }

    pub fn combine_hash_tree_with_column(
        hash_tree: &mut Poseidon2HalfStateRef,
        hash_column: &mut Poseidon2HalfStateRef,
    ) -> Poseidon2HalfStateRef {
        let (parent, _) = Poseidon2HalfStateRef::permute(hash_tree, hash_column, false, true);
        parent
    }

    pub fn hash_m31_columns(m31: &[M31Var]) -> Poseidon2HalfStateRef {
        let len = m31.len();
        let num_chunk = len.div_ceil(8);
        let cs = m31[0].cs();

        if num_chunk == 1 {
            // return the data back as the hash

            let mut digest: [M31Var; 8] = std::array::from_fn(|_| M31Var::zero(&cs));
            digest[0..len].clone_from_slice(m31);

            return Poseidon2HalfStateRef::from_m31(&digest);
        }

        // compute the first hash, which consists of 8 elements, and it comes from (no more than)
        // 16 elements

        let mut input: [M31Var; 16] = std::array::from_fn(|_| M31Var::zero(&cs));
        input[0..min(len, 16)].clone_from_slice(&m31[0..min(len, 16)]);

        let mut left = Poseidon2HalfStateRef::from_m31(&input[0..8]);
        let mut right = Poseidon2HalfStateRef::from_m31(&input[8..16]);

        let (mut digest, _) = Poseidon2HalfStateRef::permute(&mut left, &mut right, false, true);

        for chunk in m31.chunks_exact(8).skip(2) {
            let mut right = Poseidon2HalfStateRef::from_m31(&chunk);
            let (new_digest, _) =
                Poseidon2HalfStateRef::permute(&mut digest, &mut right, false, true);
            digest = new_digest;
        }

        let remain = len % 8;
        if len > 16 && remain != 0 {
            let mut input: [M31Var; 8] = std::array::from_fn(|_| M31Var::zero(&cs));
            input[0..remain].clone_from_slice(&m31[len - remain..]);

            let mut right = Poseidon2HalfStateRef::from_m31(&input);
            let (new_digest, _) =
                Poseidon2HalfStateRef::permute(&mut digest, &mut right, false, true);

            digest = new_digest;
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
    use rand::rngs::SmallRng;
    use rand::{Rng, SeedableRng};
    use stwo_prover::core::fields::m31::M31;
    use stwo_prover::core::vcs::ops::MerkleHasher;
    use stwo_prover::core::vcs::poseidon31_hash::Poseidon31Hash;
    use stwo_prover::core::vcs::poseidon31_merkle::Poseidon31MerkleHasher;

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
        let a = Poseidon31MerkleHasherVar::hash_m31_columns(&test_var[0..7]);
        let b = Poseidon31MerkleHasher::hash_node(None, &test[0..7]);
        for i in 0..8 {
            assert_eq!(a.value[i], b.0[i]);
        }

        // test 13
        let a = Poseidon31MerkleHasherVar::hash_m31_columns(&test_var[0..13]);
        let b = Poseidon31MerkleHasher::hash_node(None, &test[0..13]);
        for i in 0..8 {
            assert_eq!(a.value[i], b.0[i]);
        }

        // test 16
        let a = Poseidon31MerkleHasherVar::hash_m31_columns(&test_var[0..16]);
        let b = Poseidon31MerkleHasher::hash_node(None, &test[0..16]);
        for i in 0..8 {
            assert_eq!(a.value[i], b.0[i]);
        }

        // test 17
        let a = Poseidon31MerkleHasherVar::hash_m31_columns(&test_var[0..17]);
        let b = Poseidon31MerkleHasher::hash_node(None, &test[0..17]);
        for i in 0..8 {
            assert_eq!(a.value[i], b.0[i]);
        }

        // test 21
        let a = Poseidon31MerkleHasherVar::hash_m31_columns(&test_var[0..21]);
        let b = Poseidon31MerkleHasher::hash_node(None, &test[0..21]);
        for i in 0..8 {
            assert_eq!(a.value[i], b.0[i]);
        }

        // test 25
        let a = Poseidon31MerkleHasherVar::hash_m31_columns(&test_var[0..25]);
        let b = Poseidon31MerkleHasher::hash_node(None, &test[0..25]);
        for i in 0..8 {
            assert_eq!(a.value[i], b.0[i]);
        }

        let test_hash_left: [M31; 8] = prng.gen();
        let test_hash_right: [M31; 8] = prng.gen();
        let test_hash_column: [M31; 8] = prng.gen();

        let mut test_hash_left_var = Poseidon2HalfStateRef::new_witness(&cs, &test_hash_left);
        let mut test_hash_right_var =
            Poseidon2HalfStateRef::new_single_use_witness(&cs, &test_hash_right);
        let mut test_hash_column_var =
            Poseidon2HalfStateRef::new_single_use_witness(&cs, &test_hash_column);

        let a =
            Poseidon31MerkleHasherVar::hash_tree(&mut test_hash_left_var, &mut test_hash_right_var);
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

        let mut test_hash_right_var =
            Poseidon2HalfStateRef::new_single_use_witness(&cs, &test_hash_right);

        let a = Poseidon31MerkleHasherVar::hash_tree_with_column_hash(
            &mut test_hash_left_var,
            &mut test_hash_right_var,
            &mut test_hash_column_var,
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
    }
}
