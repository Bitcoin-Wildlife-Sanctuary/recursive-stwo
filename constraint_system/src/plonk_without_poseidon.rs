use crate::var::AllocationMode;
use crate::LOG_CONSTRAINT_SYSTEM_RESERVED_SIZE;
use num_traits::{One, Zero};
use std::collections::HashMap;
use std::ops::{Add, AddAssign, Mul, Neg, Sub};
use stwo::core::fields::m31::{BaseField, M31};
use stwo::core::fields::qm31::QM31;
use stwo::prover::backend::simd::m31::N_LANES;
use stwo::prover::backend::Column;
use stwo_examples::plonk_without_poseidon::plonk::PlonkWithoutAcceleratorCircuitTrace;

#[derive(Debug)]
pub struct PlonkWithoutPoseidonConstraintSystem {
    pub variables: Vec<QM31>,

    pub cache: HashMap<String, usize>,

    pub a_wire: Vec<usize>,
    pub b_wire: Vec<usize>,
    pub c_wire: Vec<usize>,

    pub mult_c: Vec<isize>,
    pub op1: Vec<M31>,
    pub op2: Vec<M31>,
    pub op3: Vec<M31>,
    pub op4: Vec<M31>,

    pub num_input: usize,
    pub is_program_started: bool,
}

impl PlonkWithoutPoseidonConstraintSystem {
    pub fn new() -> Self {
        let mut cs = Self {
            variables: Vec::with_capacity(1 << LOG_CONSTRAINT_SYSTEM_RESERVED_SIZE),
            cache: HashMap::new(),
            a_wire: Vec::with_capacity(1 << LOG_CONSTRAINT_SYSTEM_RESERVED_SIZE),
            b_wire: Vec::with_capacity(1 << LOG_CONSTRAINT_SYSTEM_RESERVED_SIZE),
            c_wire: Vec::with_capacity(1 << LOG_CONSTRAINT_SYSTEM_RESERVED_SIZE),
            mult_c: vec![],
            op1: Vec::with_capacity(1 << LOG_CONSTRAINT_SYSTEM_RESERVED_SIZE),
            op2: Vec::with_capacity(1 << LOG_CONSTRAINT_SYSTEM_RESERVED_SIZE),
            op3: Vec::with_capacity(1 << LOG_CONSTRAINT_SYSTEM_RESERVED_SIZE),
            op4: Vec::with_capacity(1 << LOG_CONSTRAINT_SYSTEM_RESERVED_SIZE),
            num_input: 0,
            is_program_started: false,
        };

        cs.variables.push(QM31::zero());
        cs.variables.push(QM31::one());
        cs.variables.push(QM31::from_u32_unchecked(0, 1, 0, 0));
        cs.variables.push(QM31::from_u32_unchecked(0, 0, 1, 0));

        cs.a_wire.push(0);
        cs.b_wire.push(0);
        cs.c_wire.push(0);
        cs.op1.push(M31::one());
        cs.op2.push(M31::zero());
        cs.op3.push(M31::zero());
        cs.op4.push(M31::zero());

        cs.a_wire.push(1);
        cs.b_wire.push(0);
        cs.c_wire.push(1);
        cs.op1.push(M31::one());
        cs.op2.push(M31::zero());
        cs.op3.push(M31::zero());
        cs.op4.push(M31::zero());

        cs.a_wire.push(2);
        cs.b_wire.push(0);
        cs.c_wire.push(2);
        cs.op1.push(M31::one());
        cs.op2.push(M31::zero());
        cs.op3.push(M31::zero());
        cs.op4.push(M31::zero());

        cs.a_wire.push(3);
        cs.b_wire.push(0);
        cs.c_wire.push(3);
        cs.op1.push(M31::one());
        cs.op2.push(M31::zero());
        cs.op3.push(M31::zero());
        cs.op4.push(M31::zero());

        cs.num_input = 3;

        cs
    }

    pub fn insert_gate(&mut self, a_wire: usize, b_wire: usize, c_wire: usize, op: M31) {
        self.is_program_started = true;
        let id = self.variables.len();

        self.a_wire.push(a_wire);
        self.b_wire.push(b_wire);
        self.c_wire.push(c_wire);
        self.op1.push(op);
        self.op2.push(M31::zero());
        self.op3.push(M31::zero());
        self.op4.push(M31::zero());

        assert!(a_wire < id);
        assert!(b_wire < id);
        assert!(c_wire < id);
    }

    pub fn do_m4_gate(&mut self, a_wire: usize, b_wire: usize) -> usize {
        self.is_program_started = true;

        let value = self.variables[a_wire];
        let x0 = value.0 .0;
        let x1 = value.0 .1;
        let x2 = value.1 .0;
        let x3 = value.1 .1;

        let t0 = x0 + x1;
        let t1 = x2 + x3;
        let t2 = x1 + x1 + t1;
        let t3 = x3 + x3 + t0;
        let t4 = t1 + t1 + t1 + t1 + t3;
        let t5 = t0 + t0 + t0 + t0 + t2;
        let t6 = t3 + t5;
        let t7 = t2 + t4;

        let id = self.variables.len();
        self.variables.push(QM31::from_m31(t6, t5, t7, t4));

        self.a_wire.push(a_wire);
        self.b_wire.push(b_wire);
        self.c_wire.push(id);
        self.op1.push(M31::one());
        self.op2.push(M31::zero());
        self.op3.push(M31::one());
        self.op4.push(M31::zero());

        id
    }

    pub fn do_pow5m4_gate(&mut self, a_wire: usize, b_wire: usize) -> usize {
        self.is_program_started = true;

        let a = self.variables[a_wire];
        let b = self.variables[b_wire];

        let x0 = a.0 .0 * b.0 .0;
        let x1 = a.0 .1 * b.0 .1;
        let x2 = a.1 .0 * b.1 .0;
        let x3 = a.1 .1 * b.1 .1;

        let t0 = x0 + x1;
        let t1 = x2 + x3;
        let t2 = x1 + x1 + t1;
        let t3 = x3 + x3 + t0;
        let t4 = t1 + t1 + t1 + t1 + t3;
        let t5 = t0 + t0 + t0 + t0 + t2;
        let t6 = t3 + t5;
        let t7 = t2 + t4;

        let id = self.variables.len();
        self.variables.push(QM31::from_m31(t6, t5, t7, t4));

        self.a_wire.push(a_wire);
        self.b_wire.push(b_wire);
        self.c_wire.push(id);
        self.op1.push(M31::one());
        self.op2.push(M31::one());
        self.op3.push(M31::one());
        self.op4.push(M31::zero());

        id
    }

    pub fn do_pow5_gate(&mut self, a_wire: usize, b_wire: usize) -> usize {
        self.is_program_started = true;

        let a = self.variables[a_wire];
        let b = self.variables[b_wire];

        let x0 = a.0 .0 * b.0 .0;
        let x1 = a.0 .1 * b.0 .1;
        let x2 = a.1 .0 * b.1 .0;
        let x3 = a.1 .1 * b.1 .1;

        let id = self.variables.len();
        self.variables.push(QM31::from_m31(x0, x1, x2, x3));

        self.a_wire.push(a_wire);
        self.b_wire.push(b_wire);
        self.c_wire.push(id);
        self.op1.push(M31::one());
        self.op2.push(M31::one());
        self.op3.push(M31::zero());
        self.op4.push(M31::one());

        id
    }

    pub fn do_hadamard(&mut self, a_wire: usize, b_wire: usize) -> usize {
        self.is_program_started = true;

        let a = self.variables[a_wire];
        let b = self.variables[b_wire];

        let x0 = a.0 .0 * b.0 .0;
        let x1 = a.0 .1 * b.0 .1;
        let x2 = a.1 .0 * b.1 .0;
        let x3 = a.1 .1 * b.1 .1;

        let id = self.variables.len();
        self.variables.push(QM31::from_m31(x0, x1, x2, x3));

        self.a_wire.push(a_wire);
        self.b_wire.push(b_wire);
        self.c_wire.push(id);
        self.op1.push(M31::one());
        self.op2.push(M31::zero());
        self.op3.push(M31::zero());
        self.op4.push(M31::one());

        id
    }

    pub fn do_grandsum_gate(&mut self, a_wire: usize, b_wire: usize) -> usize {
        self.is_program_started = true;

        let a = self.variables[a_wire];
        let b = self.variables[b_wire];

        let sum = a.0 .0 + a.0 .1 + a.1 .0 + a.1 .1 + b.0 .0 + b.0 .1 + b.1 .0 + b.1 .1;

        let id = self.variables.len();
        self.variables.push(QM31::from_m31(sum, sum, sum, sum));

        self.a_wire.push(a_wire);
        self.b_wire.push(b_wire);
        self.c_wire.push(id);
        self.op1.push(M31::one());
        self.op2.push(M31::zero());
        self.op3.push(M31::one());
        self.op4.push(M31::one());

        id
    }

    pub fn enforce_zero(&mut self, var: usize) {
        self.is_program_started = true;

        self.a_wire.push(var);
        self.b_wire.push(0);
        self.c_wire.push(0);
        self.op1.push(M31::one());
        self.op2.push(M31::zero());
        self.op3.push(M31::zero());
        self.op4.push(M31::zero());
    }

    pub fn add(&mut self, a_wire: usize, b_wire: usize) -> usize {
        let a_val = self.variables[a_wire];
        let b_val = self.variables[b_wire];

        let c_wire = self.variables.len();
        self.variables.push(a_val + b_val);

        self.insert_gate(a_wire, b_wire, c_wire, M31::one());
        c_wire
    }

    pub fn mul(&mut self, a_wire: usize, b_wire: usize) -> usize {
        let a_val = self.variables[a_wire];
        let b_val = self.variables[b_wire];

        let c_wire = self.variables.len();
        self.variables.push(a_val * b_val);

        self.insert_gate(a_wire, b_wire, c_wire, M31::zero());
        c_wire
    }

    pub fn mul_constant(&mut self, a_wire: usize, constant: M31) -> usize {
        let a_val = self.variables[a_wire];

        let c_wire = self.variables.len();
        self.variables.push(a_val * constant);

        self.insert_gate(a_wire, 0, c_wire, constant);
        c_wire
    }

    pub fn new_m31(&mut self, variable: M31, mode: AllocationMode) -> usize {
        let c_wire = self.variables.len();
        self.variables.push(QM31::from(variable));

        match mode {
            AllocationMode::PublicInput => {
                assert!(!self.is_program_started);

                self.a_wire.push(c_wire);
                self.b_wire.push(1);
                self.c_wire.push(c_wire);
                self.op1.push(M31::one());
                self.op2.push(M31::zero());
                self.op3.push(M31::zero());
                self.op4.push(M31::one());

                self.num_input += 1;
            }
            AllocationMode::Witness => {
                self.is_program_started = true;

                self.a_wire.push(c_wire);
                self.b_wire.push(1);
                self.c_wire.push(c_wire);
                self.op1.push(M31::one());
                self.op2.push(M31::zero());
                self.op3.push(M31::zero());
                self.op4.push(M31::one());
            }
            AllocationMode::Constant => {
                self.is_program_started = true;

                self.a_wire.push(1);
                self.b_wire.push(0);
                self.c_wire.push(c_wire);
                self.op1.push(variable);
                self.op2.push(M31::zero());
                self.op3.push(M31::zero());
                self.op4.push(M31::zero());
            }
        }

        c_wire
    }

    pub fn new_qm31(&mut self, variable: QM31, mode: AllocationMode) -> usize {
        let c_wire = self.variables.len();
        self.variables.push(variable);

        match mode {
            AllocationMode::PublicInput => {
                assert!(!self.is_program_started);

                self.a_wire.push(c_wire);
                self.b_wire.push(0);
                self.c_wire.push(c_wire);
                self.op1.push(M31::one());
                self.op2.push(M31::zero());
                self.op3.push(M31::zero());
                self.op4.push(M31::zero());

                self.num_input += 1;
            }
            AllocationMode::Witness => {
                self.is_program_started = true;

                self.a_wire.push(c_wire);
                self.b_wire.push(0);
                self.c_wire.push(c_wire);
                self.op1.push(M31::one());
                self.op2.push(M31::zero());
                self.op3.push(M31::zero());
                self.op4.push(M31::zero());
            }
            AllocationMode::Constant => {
                self.is_program_started = true;

                let first_real = self.new_m31(variable.0 .0, AllocationMode::Constant);
                let first_imag = self.new_m31(variable.0 .1, AllocationMode::Constant);
                let second_real = self.new_m31(variable.1 .0, AllocationMode::Constant);
                let second_imag = self.new_m31(variable.1 .1, AllocationMode::Constant);

                let t = self.mul(first_imag, 2);
                let a_wire = self.add(first_real, t);

                let t = self.mul(second_imag, 2);
                let t = self.add(second_real, t);
                let b_wire = self.mul(t, 3);

                self.a_wire.push(a_wire);
                self.b_wire.push(b_wire);
                self.c_wire.push(c_wire);
                self.op1.push(M31::one());
                self.op2.push(M31::zero());
                self.op3.push(M31::zero());
                self.op4.push(M31::zero());
            }
        }

        c_wire
    }

    pub fn pad(&mut self) {
        println!("Before padding: Plonk circuit size: {}", self.a_wire.len(),);
        assert!(self.mult_c.is_empty());

        let plonk_len = self.a_wire.len();
        let padded_plonk_len = plonk_len.next_power_of_two();

        for _ in plonk_len..padded_plonk_len {
            self.a_wire.push(0);
            self.b_wire.push(0);
            self.c_wire.push(0);
            self.op1.push(M31::one());
            self.op2.push(M31::zero());
            self.op3.push(M31::zero());
            self.op4.push(M31::zero());
        }
    }

    pub fn check_arithmetics(&self) {
        assert!(self.mult_c.is_empty());

        assert_eq!(self.a_wire.len(), self.b_wire.len());
        assert_eq!(self.a_wire.len(), self.c_wire.len());
        assert_eq!(self.a_wire.len(), self.op1.len());
        assert_eq!(self.a_wire.len(), self.op2.len());
        assert_eq!(self.a_wire.len(), self.op3.len());
        assert_eq!(self.a_wire.len(), self.op4.len());

        let len = self.a_wire.len();

        for i in 0..len {
            let a = self.variables[self.a_wire[i]];
            let b = self.variables[self.b_wire[i]];
            let c = self.variables[self.c_wire[i]];

            let op1 = self.op1[i];
            let op2 = self.op2[i];
            let op3 = self.op3[i];
            let op4 = self.op4[i];
            let one_minus_op3 = M31::one() - op3;
            let one_minus_op4 = M31::one() - op4;
            #[inline(always)]
            /// Applies the M4 MDS matrix described in <https://eprint.iacr.org/2023/323.pdf> 5.1.
            fn apply_m4<F>(x: [F; 4]) -> [F; 4]
            where
                F: Clone
                    + AddAssign<F>
                    + Add<F, Output = F>
                    + Sub<F, Output = F>
                    + Mul<BaseField, Output = F>,
            {
                let t0 = x[0].clone() + x[1].clone();
                let t02 = t0.clone() + t0.clone();
                let t1 = x[2].clone() + x[3].clone();
                let t12 = t1.clone() + t1.clone();
                let t2 = x[1].clone() + x[1].clone() + t1.clone();
                let t3 = x[3].clone() + x[3].clone() + t0.clone();
                let t4 = t12.clone() + t12.clone() + t3.clone();
                let t5 = t02.clone() + t02.clone() + t2.clone();
                let t6 = t3.clone() + t5.clone();
                let t7 = t2.clone() + t4.clone();
                [t6, t5, t7, t4]
            }
            let m4_result = QM31::from_m31_array(apply_m4([
                a.0 .0 * b.0 .0,
                a.0 .1 * b.0 .1,
                a.1 .0 * b.1 .0,
                a.1 .1 * b.1 .1,
            ]));
            let pow4_result = QM31::from_m31(
                a.0 .0 * a.0 .0 * a.0 .0 * a.0 .0,
                a.0 .1 * a.0 .1 * a.0 .1 * a.0 .1,
                a.1 .0 * a.1 .0 * a.1 .0 * a.1 .0,
                a.1 .1 * a.1 .1 * a.1 .1 * a.1 .1,
            );

            let grand_sum = a.0 .0 + a.0 .1 + a.1 .0 + a.1 .1 + b.0 .0 + b.0 .1 + b.1 .0 + b.1 .1;
            let hadamard_product = QM31::from_m31(
                a.0 .0 * b.0 .0,
                a.0 .1 * b.0 .1,
                a.1 .0 * b.1 .0,
                a.1 .1 * b.1 .1,
            );

            if op2 == M31::zero() && op3 == M31::zero() && op4 == M31::zero() {
                assert_eq!(
                    c,
                    op1 * (a + b) + (M31::one() - op1) * a * b,
                    "Row {} is incorrect:\n - a_val = {},  b_val = {}, c_val = {}\
                \n - a_wire = {}, b_wire = {}, c_wire = {}, op1 = {}",
                    i,
                    a,
                    b,
                    c,
                    self.a_wire[i],
                    self.b_wire[i],
                    self.c_wire[i],
                    op1
                );
            } else if op2 == M31::zero() && op3 == M31::zero() && op4 == M31::one() {
                assert_eq!(
                    op1,
                    M31::one(),
                    "Row {} is incorrect: Hadamard product gate should have op1 = 1",
                    i
                );
                assert_eq!(
                    c, hadamard_product,
                    "Row {} is incorrect: Hadamard product gate, c_val = {}, expected = {}",
                    i, c, hadamard_product
                );
            } else if op2 == M31::one() && op3 == M31::one() && op4 == M31::zero() {
                assert_eq!(
                    op1,
                    M31::one(),
                    "Row {} is incorrect: Pow5m4 gate should have op1 = 1",
                    i
                );
                assert_eq!(
                    b, pow4_result,
                    "Row {} is incorrect: Pow5m4 gate, b_val = {}, expected = {}",
                    i, b, pow4_result,
                );
                assert_eq!(
                    c, m4_result,
                    "Row {} is incorrect: Pow5m4 gate, c_val = {}, expected = {}",
                    i, c, m4_result,
                );
            } else if op2 == M31::one() && op3 == M31::zero() && op4 == M31::one() {
                assert_eq!(
                    op1,
                    M31::one(),
                    "Row {} is incorrect: Pow5 gate should have op1 = 1",
                    i
                );
                assert_eq!(
                    b, pow4_result,
                    "Row {} is incorrect: Pow5 gate, b_val = {}, expected = {}",
                    i, b, pow4_result,
                );
                assert_eq!(
                    c, hadamard_product,
                    "Row {} is incorrect: Pow5 gate, c_val = {}, expected = {}",
                    i, c, hadamard_product,
                );
            } else if op2 == M31::zero() && op3 == M31::one() && op4 == M31::zero() {
                assert_eq!(
                    op1,
                    M31::one(),
                    "Row {} is incorrect: m4 gate should have op1 = 1",
                    i
                );
                assert_eq!(
                    c, m4_result,
                    "Row {} is incorrect: m4 gate, c_val = {}, expected = {}",
                    i, c, m4_result,
                );
            } else if op2 == M31::zero() && op3 == M31::one() && op4 == M31::one() {
                assert_eq!(
                    op1,
                    M31::one(),
                    "Row {} is incorrect: GrandSum gate should have op1 = 1",
                    i
                );
                let c_expected = QM31::from_m31(grand_sum, grand_sum, grand_sum, grand_sum);
                assert_eq!(
                    c, c_expected,
                    "Row {} is incorrect: GrandSum gate, c_val = {}, expected = {}",
                    i, c, c_expected,
                );
            } else {
                unreachable!("Row {} should not use op2 or op3 other than defined", i);
            }

            let is_arith = one_minus_op3 * one_minus_op4;
            let is_pow5 = op2;
            let is_m4 = op3 * one_minus_op4;
            let is_hadamard_product = one_minus_op3 * op4;
            let is_grand_sum = op3 * op4;

            assert_eq!(
                is_pow5 * (a.0 .0 * a.0 .0 * a.0 .0 * a.0 .0 - b.0 .0),
                M31::zero()
            );
            assert_eq!(
                is_pow5 * (a.0 .1 * a.0 .1 * a.0 .1 * a.0 .1 - b.0 .1),
                M31::zero()
            );
            assert_eq!(
                is_pow5 * (a.1 .0 * a.1 .0 * a.1 .0 * a.1 .0 - b.1 .0),
                M31::zero()
            );
            assert_eq!(
                is_pow5 * (a.1 .1 * a.1 .1 * a.1 .1 * a.1 .1 - b.1 .1),
                M31::zero()
            );

            assert_eq!(
                c,
                is_arith * op1 * (a + b)
                    + (M31::one() - op1) * a * b
                    + is_m4 * m4_result
                    + is_hadamard_product * hadamard_product
                    + is_grand_sum * QM31::from_m31(grand_sum, grand_sum, grand_sum, grand_sum)
            );
        }
    }

    pub fn populate_logup_arguments(&mut self) {
        assert!(self.mult_c.is_empty());

        let n_vars = self.variables.len();
        let mut counts = Vec::new();
        counts.resize(n_vars, 0isize);

        let n_rows = self.a_wire.len();
        assert!(n_rows.is_power_of_two());

        for i in 0..n_rows {
            counts[self.a_wire[i]] += 1;
            counts[self.b_wire[i]] += 1;
            counts[self.c_wire[i]] += 1;
        }

        for i in 0..self.num_input {
            counts[i + 1] += 1;
        }

        let mut first_occurred = vec![false; n_vars];
        let mut mult_c = Vec::with_capacity(n_rows);
        for i in 0..n_rows {
            if !first_occurred[self.c_wire[i]] {
                mult_c.push(-(counts[self.c_wire[i]] - 1));
                first_occurred[self.c_wire[i]] = true;
            } else {
                mult_c.push(1);
            }
        }
        self.mult_c = mult_c;
    }

    pub fn generate_plonk_without_poseidon_circuit(&self) -> PlonkWithoutAcceleratorCircuitTrace {
        assert!(self.a_wire.len().is_power_of_two());
        assert!(self.a_wire.len() >= N_LANES);
        assert!(!self.mult_c.is_empty());

        let log_n_rows = self.a_wire.len().ilog2();
        let range = 0..(1 << log_n_rows);
        let isize_to_m31 = |v: isize| {
            if v.is_negative() {
                M31::from((-v) as u32).neg()
            } else {
                M31::from(v as u32)
            }
        };

        let circuit = PlonkWithoutAcceleratorCircuitTrace {
            mult_c: range
                .clone()
                .map(|i| isize_to_m31(self.mult_c[i]))
                .collect(),
            a_wire: range.clone().map(|i| self.a_wire[i].into()).collect(),
            b_wire: range.clone().map(|i| self.b_wire[i].into()).collect(),
            c_wire: range.clone().map(|i| self.c_wire[i].into()).collect(),
            op1: range.clone().map(|i| self.op1[i].into()).collect(),
            op2: range.clone().map(|i| self.op2[i].into()).collect(),
            op3: range.clone().map(|i| self.op3[i].into()).collect(),
            op4: range.clone().map(|i| self.op4[i].into()).collect(),
            a_val_0: range
                .clone()
                .map(|i| self.variables[self.a_wire[i]].0 .0.into())
                .collect(),
            a_val_1: range
                .clone()
                .map(|i| self.variables[self.a_wire[i]].0 .1.into())
                .collect(),
            a_val_2: range
                .clone()
                .map(|i| self.variables[self.a_wire[i]].1 .0.into())
                .collect(),
            a_val_3: range
                .clone()
                .map(|i| self.variables[self.a_wire[i]].1 .1.into())
                .collect(),
            b_val_0: range
                .clone()
                .map(|i| self.variables[self.b_wire[i]].0 .0.into())
                .collect(),
            b_val_1: range
                .clone()
                .map(|i| self.variables[self.b_wire[i]].0 .1.into())
                .collect(),
            b_val_2: range
                .clone()
                .map(|i| self.variables[self.b_wire[i]].1 .0.into())
                .collect(),
            b_val_3: range
                .clone()
                .map(|i| self.variables[self.b_wire[i]].1 .1.into())
                .collect(),
            c_val_0: range
                .clone()
                .map(|i| self.variables[self.c_wire[i]].0 .0.into())
                .collect(),
            c_val_1: range
                .clone()
                .map(|i| self.variables[self.c_wire[i]].0 .1.into())
                .collect(),
            c_val_2: range
                .clone()
                .map(|i| self.variables[self.c_wire[i]].1 .0.into())
                .collect(),
            c_val_3: range
                .clone()
                .map(|i| self.variables[self.c_wire[i]].1 .1.into())
                .collect(),
        };

        println!("Plonk circuit size: {}", circuit.mult_c.len());

        circuit
    }
}
