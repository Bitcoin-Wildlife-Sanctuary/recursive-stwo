use crate::var::AllocationMode;
use crate::LOG_CONSTRAINT_SYSTEM_RESERVED_SIZE;
use num_traits::{One, Zero};
use std::cmp::max;
use std::collections::HashMap;
use std::ops::Neg;
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::QM31;
use stwo::core::vcs::poseidon31_ref::poseidon2_permute;
use stwo::prover::backend::simd::m31::N_LANES;
use stwo::prover::backend::Column;
use stwo_examples::plonk_with_poseidon::plonk::PlonkWithAcceleratorCircuitTrace;
use stwo_examples::plonk_with_poseidon::poseidon::{
    PoseidonEntry, PoseidonFlow, SwapOption, CONSTANT_1, CONSTANT_2, CONSTANT_3,
};

#[derive(Debug)]
pub struct PlonkWithPoseidonConstraintSystem {
    pub variables: Vec<QM31>,

    pub cache: HashMap<String, usize>,

    pub poseidon_wire: Vec<usize>,

    pub a_wire: Vec<usize>,
    pub b_wire: Vec<usize>,
    pub c_wire: Vec<usize>,

    pub mult_a: Vec<isize>,
    pub mult_b: Vec<isize>,
    pub mult_c: Vec<isize>,
    pub mult_poseidon: Vec<usize>,

    pub enforce_c_m31: Vec<usize>,
    pub op: Vec<M31>,

    pub flow: PoseidonFlow,

    pub num_input: usize,
    pub is_program_started: bool,
}

impl PlonkWithPoseidonConstraintSystem {
    pub fn new() -> Self {
        let mut cs = Self {
            variables: Vec::with_capacity(1 << LOG_CONSTRAINT_SYSTEM_RESERVED_SIZE),
            cache: HashMap::new(),
            a_wire: Vec::with_capacity(1 << LOG_CONSTRAINT_SYSTEM_RESERVED_SIZE),
            b_wire: Vec::with_capacity(1 << LOG_CONSTRAINT_SYSTEM_RESERVED_SIZE),
            c_wire: Vec::with_capacity(1 << LOG_CONSTRAINT_SYSTEM_RESERVED_SIZE),
            poseidon_wire: Vec::with_capacity(1 << LOG_CONSTRAINT_SYSTEM_RESERVED_SIZE),
            mult_a: vec![],
            mult_b: vec![],
            mult_c: vec![],
            mult_poseidon: vec![],
            enforce_c_m31: Vec::with_capacity(1 << LOG_CONSTRAINT_SYSTEM_RESERVED_SIZE),
            op: Vec::with_capacity(1 << LOG_CONSTRAINT_SYSTEM_RESERVED_SIZE),
            num_input: 0,
            is_program_started: false,
            flow: PoseidonFlow::default(),
        };

        cs.variables.push(QM31::zero());
        cs.variables.push(QM31::one());
        cs.variables.push(QM31::from_u32_unchecked(0, 1, 0, 0));
        cs.variables.push(QM31::from_u32_unchecked(0, 0, 1, 0));

        cs.a_wire.push(0);
        cs.b_wire.push(0);
        cs.c_wire.push(0);
        cs.poseidon_wire.push(0);
        cs.enforce_c_m31.push(0);
        cs.op.push(M31::one());

        cs.a_wire.push(1);
        cs.b_wire.push(0);
        cs.c_wire.push(1);
        cs.poseidon_wire.push(0);
        cs.enforce_c_m31.push(0);
        cs.op.push(M31::one());

        cs.a_wire.push(2);
        cs.b_wire.push(0);
        cs.c_wire.push(2);
        cs.poseidon_wire.push(0);
        cs.enforce_c_m31.push(0);
        cs.op.push(M31::one());

        cs.a_wire.push(3);
        cs.b_wire.push(0);
        cs.c_wire.push(3);
        cs.poseidon_wire.push(0);
        cs.enforce_c_m31.push(0);
        cs.op.push(M31::one());

        cs.num_input = 3;

        cs
    }

    pub fn insert_gate(&mut self, a_wire: usize, b_wire: usize, c_wire: usize, op: M31) {
        self.is_program_started = true;
        let id = self.variables.len();

        self.a_wire.push(a_wire);
        self.b_wire.push(b_wire);
        self.c_wire.push(c_wire);
        self.poseidon_wire.push(0);
        self.enforce_c_m31.push(0);
        self.op.push(op);

        assert!(a_wire < id);
        assert!(b_wire < id);
        assert!(c_wire < id);
    }

    pub fn invoke_poseidon_accelerator(
        &mut self,
        entry_1: PoseidonEntry,
        entry_2: PoseidonEntry,
        entry_3: PoseidonEntry,
        entry_4: PoseidonEntry,
        swap_option: SwapOption,
    ) {
        self.flow
            .0
            .push((entry_1, entry_2, entry_3, entry_4, swap_option));
    }

    pub fn enforce_zero(&mut self, var: usize) {
        self.is_program_started = true;

        self.a_wire.push(var);
        self.b_wire.push(0);
        self.c_wire.push(0);
        self.poseidon_wire.push(0);
        self.enforce_c_m31.push(0);
        self.op.push(M31::one());
    }

    pub fn add(&mut self, a_wire: usize, b_wire: usize) -> usize {
        let a_val = self.variables[a_wire];
        let b_val = self.variables[b_wire];

        let c_wire = self.variables.len();
        self.variables.push(a_val + b_val);

        self.insert_gate(a_wire, b_wire, c_wire, M31::one());
        c_wire
    }

    pub fn assemble_poseidon_gate(&mut self, a_wire: usize, b_wire: usize) -> usize {
        let a_val = self.variables[a_wire];
        let b_val = self.variables[b_wire];

        let c_wire = self.variables.len();
        self.variables.push(a_val * b_val);

        self.is_program_started = true;

        let poseidon_wire = c_wire;

        self.a_wire.push(a_wire);
        self.b_wire.push(b_wire);
        self.c_wire.push(c_wire);
        self.poseidon_wire.push(poseidon_wire);
        self.enforce_c_m31.push(0);
        self.op.push(M31::zero());

        poseidon_wire
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
                self.b_wire.push(0);
                self.c_wire.push(c_wire);
                self.poseidon_wire.push(0);
                self.enforce_c_m31.push(1);
                self.op.push(M31::one());

                self.num_input += 1;
            }
            AllocationMode::Witness => {
                self.is_program_started = true;

                self.a_wire.push(c_wire);
                self.b_wire.push(0);
                self.c_wire.push(c_wire);
                self.poseidon_wire.push(0);
                self.enforce_c_m31.push(1);
                self.op.push(M31::one());
            }
            AllocationMode::Constant => {
                self.is_program_started = true;

                self.a_wire.push(1);
                self.b_wire.push(0);
                self.c_wire.push(c_wire);
                self.poseidon_wire.push(0);
                self.enforce_c_m31.push(0);
                self.op.push(variable);
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
                self.poseidon_wire.push(0);
                self.enforce_c_m31.push(1);
                self.op.push(M31::one());

                self.num_input += 1;
            }
            AllocationMode::Witness => {
                self.is_program_started = true;
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
                self.poseidon_wire.push(0);
                self.enforce_c_m31.push(0);
                self.op.push(M31::one());
            }
        }

        c_wire
    }

    pub fn pad(&mut self) {
        println!(
            "Before padding: Plonk circuit size: {}, Poseidon circuit size {}",
            self.a_wire.len(),
            self.flow.0.len()
        );

        assert!(self.mult_a.is_empty());
        assert!(self.mult_b.is_empty());
        assert!(self.mult_c.is_empty());
        assert!(self.mult_poseidon.is_empty());

        // pad the Poseidon accelerator first
        let poseidon_len = self.flow.0.len();
        let padded_poseidon_len = max(N_LANES * 2, poseidon_len.div_ceil(16) * 16);

        if padded_poseidon_len > poseidon_len {
            for _ in poseidon_len..padded_poseidon_len {
                self.invoke_poseidon_accelerator(
                    PoseidonEntry {
                        wire: 0,
                        hash: CONSTANT_1,
                    },
                    PoseidonEntry {
                        wire: 0,
                        hash: CONSTANT_1,
                    },
                    PoseidonEntry {
                        wire: 0,
                        hash: CONSTANT_2,
                    },
                    PoseidonEntry {
                        wire: 0,
                        hash: CONSTANT_3,
                    },
                    SwapOption::default(),
                );
            }
        }

        // pad the Plonk circuit
        let plonk_len = self.a_wire.len();
        let padded_plonk_len = plonk_len.next_power_of_two();

        for _ in plonk_len..padded_plonk_len {
            self.a_wire.push(0);
            self.b_wire.push(0);
            self.c_wire.push(0);
            self.poseidon_wire.push(0);
            self.enforce_c_m31.push(0);
            self.op.push(M31::one());
        }
    }

    pub fn check_arithmetics(&self) {
        assert!(self.mult_a.is_empty());
        assert!(self.mult_b.is_empty());
        assert!(self.mult_c.is_empty());
        assert!(self.mult_poseidon.is_empty());

        assert_eq!(self.a_wire.len(), self.b_wire.len());
        assert_eq!(self.a_wire.len(), self.c_wire.len());
        assert_eq!(self.a_wire.len(), self.poseidon_wire.len());
        assert_eq!(self.a_wire.len(), self.op.len());
        assert_eq!(self.a_wire.len(), self.enforce_c_m31.len());

        let len = self.a_wire.len();

        for i in 0..len {
            assert_eq!(
                self.variables[self.c_wire[i]],
                self.op[i] * (self.variables[self.a_wire[i]] + self.variables[self.b_wire[i]])
                    + (M31::one() - self.op[i])
                        * self.variables[self.a_wire[i]]
                        * self.variables[self.b_wire[i]],
                "Row {} is incorrect:\n - a_val = {},  b_val = {}, c_val = {}\
                \n - a_wire = {}, b_wire = {}, c_wire = {}, op = {}",
                i,
                self.variables[self.a_wire[i]],
                self.variables[self.b_wire[i]],
                self.variables[self.c_wire[i]],
                self.a_wire[i],
                self.b_wire[i],
                self.c_wire[i],
                self.op[i]
            );

            if !self.enforce_c_m31[i].is_zero() {
                assert_eq!(
                    QM31::from(self.variables[self.c_wire[i]].0 .0),
                    self.variables[self.c_wire[i]],
                    "Row {} requires c_val to be a M31, but c_val = {} at c_wire = {}",
                    i,
                    self.variables[self.c_wire[i]],
                    self.c_wire[i]
                );
            }
        }
    }

    pub fn populate_logup_arguments(&mut self) {
        assert!(self.mult_a.is_empty());
        assert!(self.mult_b.is_empty());
        assert!(self.mult_c.is_empty());
        assert!(self.mult_poseidon.is_empty());

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

        for (_, _, _, _, swap) in self.flow.0.iter() {
            counts[swap.addr] += 1;
        }

        let mut first_occurred = vec![false; n_vars];
        let mut mult_a = Vec::with_capacity(n_rows);
        let mut mult_b = Vec::with_capacity(n_rows);
        let mut mult_c = Vec::with_capacity(n_rows);

        for i in 0..n_rows {
            let w = self.a_wire[i];
            if first_occurred[w] {
                mult_a.push(1);
            } else {
                first_occurred[w] = true;
                mult_a.push(1 - counts[w])
            }

            let w = self.b_wire[i];
            if first_occurred[w] {
                mult_b.push(1);
            } else {
                first_occurred[w] = true;
                mult_b.push(1 - counts[w])
            }

            let w = self.c_wire[i];
            if first_occurred[w] {
                mult_c.push(1);
            } else {
                first_occurred[w] = true;
                mult_c.push(1 - counts[w])
            }
        }

        let mut mult_poseidon_vars = vec![0; n_vars];
        for (r1, r2, r3, r4, _) in self.flow.0.iter() {
            mult_poseidon_vars[r1.wire] += 1;
            mult_poseidon_vars[r2.wire] += 1;
            mult_poseidon_vars[r3.wire] += 1;
            mult_poseidon_vars[r4.wire] += 1;
        }
        mult_poseidon_vars[0] = 0;

        let mut mult_poseidon = Vec::with_capacity(n_rows);
        for i in 0..n_rows {
            let r = mult_poseidon_vars[self.poseidon_wire[i]];
            if r != 0 {
                mult_poseidon.push(r);
                assert_eq!(counts[self.poseidon_wire[i]], 1);
                mult_poseidon_vars[self.poseidon_wire[i]] = 0;
            } else {
                mult_poseidon.push(0);
            }
        }

        self.mult_a = mult_a;
        self.mult_b = mult_b;
        self.mult_c = mult_c;
        self.mult_poseidon = mult_poseidon;
    }

    pub fn check_poseidon_invocations(&self) {
        let n_rows = self.a_wire.len();
        let mut map = HashMap::new();
        for i in 0..n_rows {
            if self.mult_poseidon[i] != 0 {
                let l = self.variables[self.a_wire[i]].to_m31_array();
                let r = self.variables[self.b_wire[i]].to_m31_array();
                map.insert(
                    self.poseidon_wire[i],
                    [l[0], l[1], l[2], l[3], r[0], r[1], r[2], r[3]],
                );
            }
        }

        for (r1, r2, r3, r4, swap) in self.flow.0.iter() {
            if r1.wire != 0 {
                assert_eq!(*map.get(&r1.wire).unwrap(), r1.hash,);
            }
            if r2.wire != 0 {
                assert_eq!(*map.get(&r2.wire).unwrap(), r2.hash);
            }
            if r3.wire != 0 {
                assert_eq!(*map.get(&r3.wire).unwrap(), r3.hash);
            }
            if r4.wire != 0 {
                assert_eq!(*map.get(&r4.wire).unwrap(), r4.hash);
            }

            let mut state: [M31; 16] = if !swap.swap {
                [
                    r1.hash[0], r1.hash[1], r1.hash[2], r1.hash[3], r1.hash[4], r1.hash[5],
                    r1.hash[6], r1.hash[7], r2.hash[0], r2.hash[1], r2.hash[2], r2.hash[3],
                    r2.hash[4], r2.hash[5], r2.hash[6], r2.hash[7],
                ]
            } else {
                [
                    r2.hash[0], r2.hash[1], r2.hash[2], r2.hash[3], r2.hash[4], r2.hash[5],
                    r2.hash[6], r2.hash[7], r1.hash[0], r1.hash[1], r1.hash[2], r1.hash[3],
                    r1.hash[4], r1.hash[5], r1.hash[6], r1.hash[7],
                ]
            };
            let expected: [M31; 16] = [
                r3.hash[0], r3.hash[1], r3.hash[2], r3.hash[3], r3.hash[4], r3.hash[5], r3.hash[6],
                r3.hash[7], r4.hash[0], r4.hash[1], r4.hash[2], r4.hash[3], r4.hash[4], r4.hash[5],
                r4.hash[6], r4.hash[7],
            ];
            poseidon2_permute(&mut state);
            for i in 0..16 {
                assert_eq!(expected[i], state[i]);
            }
        }
    }

    pub fn generate_plonk_with_poseidon_circuit(
        &self,
    ) -> (PlonkWithAcceleratorCircuitTrace, PoseidonFlow) {
        assert!(self.a_wire.len().is_power_of_two());
        assert!(self.a_wire.len() >= N_LANES);
        assert!(!self.mult_a.is_empty());
        assert!(!self.mult_b.is_empty());
        assert!(!self.mult_c.is_empty());
        assert!(!self.poseidon_wire.is_empty());
        assert!(!self.mult_poseidon.is_empty());

        let log_n_rows = self.a_wire.len().ilog2();
        let range = 0..(1 << log_n_rows);
        let isize_to_m31 = |v: isize| {
            if v.is_negative() {
                M31::from((-v) as u32).neg()
            } else {
                M31::from(v as u32)
            }
        };

        let circuit = PlonkWithAcceleratorCircuitTrace {
            mult_a: range
                .clone()
                .map(|i| isize_to_m31(self.mult_a[i]))
                .collect(),
            mult_b: range
                .clone()
                .map(|i| isize_to_m31(self.mult_b[i]))
                .collect(),
            mult_c: range
                .clone()
                .map(|i| isize_to_m31(self.mult_c[i]))
                .collect(),
            poseidon_wire: range
                .clone()
                .map(|i| self.poseidon_wire[i].into())
                .collect(),
            mult_poseidon: range
                .clone()
                .map(|i| self.mult_poseidon[i].into())
                .collect(),
            enforce_c_m31: range
                .clone()
                .map(|i| self.enforce_c_m31[i].into())
                .collect(),
            a_wire: range.clone().map(|i| self.a_wire[i].into()).collect(),
            b_wire: range.clone().map(|i| self.b_wire[i].into()).collect(),
            c_wire: range.clone().map(|i| self.c_wire[i].into()).collect(),
            op: range.clone().map(|i| self.op[i].into()).collect(),
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

        println!(
            "Plonk circuit size: {}, Poseidon circuit size: {}",
            circuit.mult_poseidon.len(),
            self.flow.0.len()
        );

        (circuit, self.flow.clone())
    }
}
