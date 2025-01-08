use crate::accelerators::AcceleratorEntry;
use crate::dvar::AllocationMode;
use num_traits::{One, Zero};
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;
use stwo_prover::core::fields::m31::M31;

pub mod accelerators;

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

    pub fn add_accelerator_entry(&self, id: usize, start_idx: usize) {
        self.0.borrow_mut().add_accelerator_entry(id, start_idx);
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

    pub fn copy(&self, a_wire: usize) -> usize {
        self.0.borrow_mut().copy(a_wire)
    }
}

#[derive(Debug)]
pub struct ConstraintSystem {
    pub variables: Vec<M31>,

    pub cache: HashMap<String, usize>,
    pub accelerator_entries: Vec<AcceleratorEntry>,

    pub a_wire: Vec<usize>,
    pub b_wire: Vec<usize>,

    pub mult: Vec<usize>,
    pub op: Vec<M31>,

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
            accelerator_entries: Vec::new(),
            a_wire: Vec::with_capacity(1 << LOG_CONSTRAINT_SYSTEM_RESERVED_SIZE),
            b_wire: Vec::with_capacity(1 << LOG_CONSTRAINT_SYSTEM_RESERVED_SIZE),
            mult: Vec::with_capacity(1 << LOG_CONSTRAINT_SYSTEM_RESERVED_SIZE),
            op: Vec::with_capacity(1 << LOG_CONSTRAINT_SYSTEM_RESERVED_SIZE),
            num_input: 0,
            is_program_started: false,
        };

        cs.variables.push(M31::zero());
        cs.a_wire.push(0);
        cs.b_wire.push(0);
        cs.mult.push(2);
        cs.op.push(M31::one());

        cs.variables.push(M31::one());
        cs.a_wire.push(1);
        cs.b_wire.push(0);
        cs.mult.push(0);
        cs.op.push(M31::one());

        cs.num_input = 1;

        cs
    }

    pub fn insert_gate(&mut self, a_wire: usize, b_wire: usize, op: M31) -> usize {
        let id = self.variables.len();

        self.a_wire.push(a_wire);
        self.b_wire.push(b_wire);
        self.mult.push(0);
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

    pub fn enforce_zero(&mut self, var: usize) {
        // a + b = a => b = 0
        let id = self.variables.len();

        self.a_wire.push(id);
        self.b_wire.push(var);
        self.mult.push(1);
        self.op.push(M31::one());
        self.variables.push(M31::zero()); // can be any value

        self.mult[1] += 1;
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
                    self.op.push(variable);

                    self.mult[0] += 1;
                    self.mult[1] += 1;
                    id += 1;
                }
                start
            }
        }
    }

    pub fn add_accelerator_entry(&mut self, id: usize, start_idx: usize) {
        self.accelerator_entries
            .push(AcceleratorEntry { id, start_idx });
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
        counts.resize(len, 0usize);

        for i in 0..len {
            counts[self.a_wire[i]] += 1;
            counts[self.b_wire[i]] += 1;
        }

        for i in 0..self.num_input {
            counts[i] -= 1;
        }

        assert_eq!(counts, self.mult);
    }
}
