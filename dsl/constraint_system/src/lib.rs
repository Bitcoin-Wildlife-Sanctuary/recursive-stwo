use crate::dvar::AllocationMode;
use num_traits::{One, Zero};
use std::cell::RefCell;
use std::cmp::max;
use std::collections::HashMap;
use std::rc::Rc;
use stwo_prover::core::backend::simd::m31::N_LANES;
use stwo_prover::core::backend::Column;
use stwo_prover::core::fields::m31::M31;
use stwo_prover::core::vcs::poseidon31_ref::poseidon2_permute;
use stwo_prover::examples::plonk_with_poseidon::plonk::PlonkWithAcceleratorCircuitTrace;
use stwo_prover::examples::plonk_with_poseidon::poseidon::{
    PoseidonControlFlow, PoseidonDataFlow, PoseidonMetadata, PoseidonPrescribedFlow, CONSTANT_1,
    CONSTANT_2, CONSTANT_3,
};

pub mod dvar;

/// A shared reference to a constraint system that can be stored in high level
/// variables.
#[derive(Clone, Debug)]
pub struct ConstraintSystemRef(pub(crate) Rc<RefCell<ConstraintSystem>>);

impl ConstraintSystemRef {
    pub fn new_ref() -> Self {
        Self(Rc::new(RefCell::new(ConstraintSystem::new())))
    }

    pub fn get_cache(&self, str: impl ToString) -> Option<usize> {
        self.0.borrow().cache.get(&str.to_string()).cloned()
    }

    pub fn set_cache(&self, str: impl ToString, range: usize) {
        self.0.borrow_mut().cache.insert(str.to_string(), range);
    }

    pub fn new_variables(&self, variables: &[M31], mode: AllocationMode) -> usize {
        self.0.borrow_mut().new_variables(variables, mode)
    }

    pub fn and(&self, other: &Self) -> Self {
        assert_eq!(self, other);
        self.clone()
    }

    pub fn insert_gate(&self, a_wire: usize, b_wire: usize, op: M31) -> usize {
        self.0.borrow_mut().insert_gate(a_wire, b_wire, op)
    }

    pub fn add(&self, a_wire: usize, b_wire: usize) -> usize {
        self.0.borrow_mut().add(a_wire, b_wire)
    }

    pub fn mul(&self, a_wire: usize, b_wire: usize) -> usize {
        self.0.borrow_mut().mul(a_wire, b_wire)
    }

    pub fn mul_constant(&self, a_wire: usize, constant: M31) -> usize {
        self.0.borrow_mut().mul_constant(a_wire, constant)
    }

    pub fn enforce_zero(&self, var: usize) {
        self.0.borrow_mut().enforce_zero(var);
    }

    pub fn check_arithmetics(&self) {
        self.0.borrow().check_arithmetics();
    }

    pub fn check_logup_arguments(&self) {
        self.0.borrow().check_logup_argument();
    }

    pub fn check_poseidon_invocations(&self) {
        self.0.borrow().check_poseidon_invocations();
    }

    pub fn copy(&self, a_wire: usize) -> usize {
        self.0.borrow_mut().copy(a_wire)
    }

    pub fn invoke_poseidon_accelerator(
        &self,
        addr_1: usize,
        addr_2: usize,
        addr_3: usize,
        addr_4: usize,
    ) {
        self.0
            .borrow_mut()
            .invoke_poseidon_accelerator(addr_1, addr_2, addr_3, addr_4);
    }

    pub fn pad(&self) {
        self.0.borrow_mut().pad();
    }

    pub fn generate_circuit(&self) -> (PlonkWithAcceleratorCircuitTrace, PoseidonMetadata) {
        self.0.borrow().generate_circuit()
    }
}

#[derive(Debug)]
pub struct ConstraintSystem {
    pub variables: Vec<M31>,

    pub cache: HashMap<String, usize>,

    pub a_wire: Vec<usize>,
    pub b_wire: Vec<usize>,

    pub mult: Vec<usize>,
    pub mult_poseidon: Vec<usize>,
    pub op: Vec<M31>,

    pub addr_1: Vec<usize>,
    pub addr_2: Vec<usize>,
    pub addr_3: Vec<usize>,
    pub addr_4: Vec<usize>,

    pub num_input: usize,
    pub is_program_started: bool,
}

impl PartialEq for ConstraintSystemRef {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}

pub const LOG_CONSTRAINT_SYSTEM_RESERVED_SIZE: usize = 16;

impl ConstraintSystem {
    pub fn new() -> Self {
        let mut cs = Self {
            variables: Vec::with_capacity(1 << LOG_CONSTRAINT_SYSTEM_RESERVED_SIZE),
            cache: HashMap::new(),
            a_wire: Vec::with_capacity(1 << LOG_CONSTRAINT_SYSTEM_RESERVED_SIZE),
            b_wire: Vec::with_capacity(1 << LOG_CONSTRAINT_SYSTEM_RESERVED_SIZE),
            mult: Vec::with_capacity(1 << LOG_CONSTRAINT_SYSTEM_RESERVED_SIZE),
            mult_poseidon: Vec::with_capacity(1 << LOG_CONSTRAINT_SYSTEM_RESERVED_SIZE),
            op: Vec::with_capacity(1 << LOG_CONSTRAINT_SYSTEM_RESERVED_SIZE),
            addr_1: vec![],
            addr_2: vec![],
            addr_3: vec![],
            addr_4: vec![],
            num_input: 0,
            is_program_started: false,
        };

        cs.variables.push(M31::zero());
        cs.a_wire.push(0);
        cs.b_wire.push(0);
        cs.mult.push(3);
        cs.mult_poseidon.push(0);
        cs.op.push(M31::one());

        cs.variables.push(M31::one());
        cs.a_wire.push(1);
        cs.b_wire.push(0);
        cs.mult.push(0);
        cs.mult_poseidon.push(0);
        cs.op.push(M31::one());

        cs.num_input = 1;

        cs
    }

    pub fn insert_gate(&mut self, a_wire: usize, b_wire: usize, op: M31) -> usize {
        self.is_program_started = true;
        let id = self.variables.len();

        self.a_wire.push(a_wire);
        self.b_wire.push(b_wire);
        self.mult.push(0);
        self.mult_poseidon.push(0);
        self.op.push(op);

        assert!(a_wire < id);
        assert!(b_wire < id);

        self.variables.push(
            op * (self.variables[a_wire] + self.variables[b_wire])
                + (M31::one() - op) * self.variables[a_wire] * self.variables[b_wire],
        );

        self.mult[a_wire] += 1;
        self.mult[b_wire] += 1;

        id
    }

    pub fn invoke_poseidon_accelerator(
        &mut self,
        addr_1: usize,
        addr_2: usize,
        addr_3: usize,
        addr_4: usize,
    ) {
        self.addr_1.push(addr_1);
        self.addr_2.push(addr_2);
        self.addr_3.push(addr_3);
        self.addr_4.push(addr_4);

        self.mult[addr_1] += 1;
        self.mult[addr_2] += 1;
        self.mult[addr_3] += 1;
        self.mult[addr_4] += 1;

        let sel_1 = self.variables[addr_1].0 as usize;
        let sel_2 = self.variables[addr_2].0 as usize;
        let sel_3 = self.variables[addr_3].0 as usize;
        let sel_4 = self.variables[addr_4].0 as usize;

        self.mult_poseidon[sel_1] += 1;
        self.mult_poseidon[sel_2] += 1;
        self.mult_poseidon[sel_3] += 1;
        self.mult_poseidon[sel_4] += 1;
    }

    pub fn enforce_zero(&mut self, var: usize) {
        self.is_program_started = true;
        // a + b = a => b = 0
        let id = self.variables.len();

        self.a_wire.push(id);
        self.b_wire.push(var);
        self.mult.push(1);
        self.mult_poseidon.push(0);
        self.op.push(M31::one());
        self.variables.push(M31::zero()); // can be any value

        self.mult[var] += 1;
    }

    pub fn add(&mut self, a_wire: usize, b_wire: usize) -> usize {
        self.insert_gate(a_wire, b_wire, M31::one())
    }

    pub fn mul(&mut self, a_wire: usize, b_wire: usize) -> usize {
        self.insert_gate(a_wire, b_wire, M31::zero())
    }

    pub fn mul_constant(&mut self, a_wire: usize, constant: M31) -> usize {
        self.insert_gate(a_wire, 0, constant)
    }

    pub fn copy(&mut self, a_wire: usize) -> usize {
        self.insert_gate(a_wire, 0, M31::one())
    }

    pub fn new_variables(&mut self, variables: &[M31], mode: AllocationMode) -> usize {
        match mode {
            AllocationMode::PublicInput => {
                assert!(!self.is_program_started);

                let mut id = self.variables.len();
                let start = id;
                for &variable in variables.iter() {
                    self.variables.push(variable);
                    self.a_wire.push(id);
                    self.b_wire.push(1);
                    self.mult.push(0); // intentionally reduces the count by 1
                    self.mult_poseidon.push(0);
                    self.op.push(M31::zero());

                    self.mult[1] += 1;
                    self.num_input += 1;
                    id += 1;
                }
                start
            }
            AllocationMode::Witness => {
                self.is_program_started = true;

                let mut id = self.variables.len();
                let start = id;
                for &variable in variables.iter() {
                    self.variables.push(variable);
                    self.a_wire.push(id);
                    self.b_wire.push(1);
                    self.mult.push(1);
                    self.mult_poseidon.push(0);
                    self.op.push(M31::zero());

                    self.mult[1] += 1;
                    id += 1;
                }
                start
            }
            AllocationMode::Constant => {
                self.is_program_started = true;

                let mut id = self.variables.len();
                let start = id;
                for &variable in variables.iter() {
                    self.variables.push(variable);
                    self.a_wire.push(1);
                    self.b_wire.push(0);
                    self.mult.push(0);
                    self.mult_poseidon.push(0);
                    self.op.push(variable);

                    self.mult[0] += 1;
                    self.mult[1] += 1;
                    id += 1;
                }
                start
            }
        }
    }

    pub fn pad(&mut self) {
        // pad the Poseidon accelerator first
        let poseidon_len = self.addr_1.len();
        let padded_poseidon_len = max(N_LANES * 2, poseidon_len.next_power_of_two());

        if padded_poseidon_len > poseidon_len {
            let constant_1 = self.new_variables(&CONSTANT_1, AllocationMode::Constant);
            let constant_2 = self.new_variables(&CONSTANT_2, AllocationMode::Constant);
            let constant_3 = self.new_variables(&CONSTANT_3, AllocationMode::Constant);

            let addr_1 = self.new_variables(&[M31::from(constant_1)], AllocationMode::Constant);
            let addr_2 = self.new_variables(&[M31::from(constant_2)], AllocationMode::Constant);
            let addr_3 = self.new_variables(&[M31::from(constant_3)], AllocationMode::Constant);

            for _ in poseidon_len..padded_poseidon_len {
                self.invoke_poseidon_accelerator(addr_1, addr_1, addr_2, addr_3);
            }
        }

        // pad the Plonk circuit
        let plonk_len = self.variables.len();
        let padded_plonk_len = plonk_len.next_power_of_two();

        for _ in plonk_len..padded_plonk_len {
            self.variables.push(M31::zero());
            self.a_wire.push(0);
            self.b_wire.push(0);
            self.mult.push(0);
            self.mult_poseidon.push(0);
            self.op.push(M31::one());

            self.mult[0] += 2;
        }
    }

    pub fn check_arithmetics(&self) {
        assert_eq!(self.variables.len(), self.a_wire.len());
        assert_eq!(self.variables.len(), self.b_wire.len());
        assert_eq!(self.variables.len(), self.op.len());
        assert_eq!(self.variables.len(), self.mult.len());

        let len = self.variables.len();

        for i in 0..len {
            assert_eq!(
                self.variables[i],
                self.op[i] * (self.variables[self.a_wire[i]] + self.variables[self.b_wire[i]])
                    + (M31::one() - self.op[i])
                        * self.variables[self.a_wire[i]]
                        * self.variables[self.b_wire[i]],
                "Row {} is incorrect:\n - a_val = {},  b_val = {}, variable = {}\
                \n - a_wire = {}, b_wire = {}, op = {}",
                i,
                self.variables[self.a_wire[i]],
                self.variables[self.b_wire[i]],
                self.variables[i],
                self.a_wire[i],
                self.b_wire[i],
                self.op[i]
            );
        }
    }

    pub fn check_logup_argument(&self) {
        let len = self.variables.len();

        let mut counts = Vec::new();
        counts.resize(len, 0isize);

        for i in 0..len {
            counts[self.a_wire[i]] -= 1;
            counts[self.b_wire[i]] -= 1;
            counts[i] += self.mult[i] as isize;
        }

        for i in 0..self.num_input {
            counts[i + 1] += 1;
        }

        for &i in self
            .addr_1
            .iter()
            .chain(self.addr_2.iter())
            .chain(self.addr_3.iter())
            .chain(self.addr_4.iter())
        {
            counts[i] -= 1;
        }

        let mut counts_poseidon = Vec::new();
        counts_poseidon.resize(len, 0isize);

        for i in 0..len {
            counts_poseidon[i] += self.mult_poseidon[i] as isize;
        }

        for &i in self
            .addr_1
            .iter()
            .chain(self.addr_2.iter())
            .chain(self.addr_3.iter())
            .chain(self.addr_4.iter())
        {
            counts_poseidon[self.variables[i].0 as usize] -= 1;
        }

        for (k, &v) in counts.iter().enumerate() {
            assert_eq!(v, 0, "LogUp argument does not match: {} {}", k, v);
        }

        for (k, &v) in counts_poseidon.iter().enumerate() {
            assert_eq!(
                v, 0,
                "LogUp argument for Poseidon does not match: {} {}",
                k, v
            );
        }
    }

    pub fn check_poseidon_invocations(&self) {
        for (((&addr_1, &addr_2), &addr_3), &addr_4) in self
            .addr_1
            .iter()
            .zip(self.addr_2.iter())
            .zip(self.addr_3.iter())
            .zip(self.addr_4.iter())
        {
            let sel_1 = self.variables[addr_1].0 as usize;
            let sel_2 = self.variables[addr_2].0 as usize;
            let sel_3 = self.variables[addr_3].0 as usize;
            let sel_4 = self.variables[addr_4].0 as usize;

            let mut state: [M31; 16] = std::array::from_fn(|i| {
                if i < 8 {
                    self.variables[sel_1 + i]
                } else {
                    self.variables[sel_2 + i - 8]
                }
            });
            let initial_state = state.clone();
            let expected: [M31; 16] = std::array::from_fn(|i| {
                if i < 8 {
                    self.variables[sel_3 + i]
                } else {
                    self.variables[sel_4 + i - 8]
                }
            });

            poseidon2_permute(&mut state);
            for i in 0..8 {
                assert_eq!(expected[i], state[i] + initial_state[i]);
            }
            for i in 8..16 {
                assert_eq!(expected[i], state[i]);
            }
        }
    }

    pub fn generate_circuit(&self) -> (PlonkWithAcceleratorCircuitTrace, PoseidonMetadata) {
        assert!(self.variables.len().is_power_of_two());
        assert!(self.variables.len() >= N_LANES);

        let log_n_rows = self.variables.len().ilog2();
        let range = 0..(1 << log_n_rows);

        let circuit = PlonkWithAcceleratorCircuitTrace {
            mult: range.clone().map(|i| self.mult[i].into()).collect(),
            mult_poseidon: range
                .clone()
                .map(|i| self.mult_poseidon[i].into())
                .collect(),
            a_wire: range.clone().map(|i| self.a_wire[i].into()).collect(),
            b_wire: range.clone().map(|i| self.b_wire[i].into()).collect(),
            c_wire: range.clone().map(|i| i.into()).collect(),
            op: range.clone().map(|i| self.op[i].into()).collect(),
            a_val: range
                .clone()
                .map(|i| self.variables[self.a_wire[i]].into())
                .collect(),
            b_val: range
                .clone()
                .map(|i| self.variables[self.b_wire[i]].into())
                .collect(),
            c_val: range.clone().map(|i| self.variables[i].into()).collect(),
        };

        let mut data_flow = PoseidonDataFlow(HashMap::new());
        for i in 0..(1 << log_n_rows) {
            if self.mult_poseidon[i] != 0 {
                data_flow
                    .0
                    .insert(i, std::array::from_fn(|offset| self.variables[i + offset]));
            }
        }
        let mut prescribed_flow = PoseidonPrescribedFlow {
            addr_1: vec![],
            addr_2: vec![],
            addr_3: vec![],
            addr_4: vec![],
        };
        let mut control_flow = PoseidonControlFlow {
            sel_1: vec![],
            sel_2: vec![],
            sel_3: vec![],
            sel_4: vec![],
        };

        for (((&addr_1, &addr_2), &addr_3), &addr_4) in self
            .addr_1
            .iter()
            .zip(self.addr_2.iter())
            .zip(self.addr_3.iter())
            .zip(self.addr_4.iter())
        {
            prescribed_flow.addr_1.push(addr_1);
            prescribed_flow.addr_2.push(addr_2);
            prescribed_flow.addr_3.push(addr_3);
            prescribed_flow.addr_4.push(addr_4);

            control_flow.sel_1.push(self.variables[addr_1].0 as usize);
            control_flow.sel_2.push(self.variables[addr_2].0 as usize);
            control_flow.sel_3.push(self.variables[addr_3].0 as usize);
            control_flow.sel_4.push(self.variables[addr_4].0 as usize);
        }

        let metadata = PoseidonMetadata {
            prescribed_flow,
            control_flow,
            data_flow,
        };

        println!(
            "Plonk circuit size: {}, Poseidon circuit size: {}",
            circuit.mult_poseidon.len(),
            metadata.control_flow.sel_1.len()
        );

        (circuit, metadata)
    }
}
