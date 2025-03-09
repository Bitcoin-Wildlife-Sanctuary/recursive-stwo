use crate::dvar::AllocationMode;
use num_traits::{One, Zero};
use plonk_with_poseidon::PlonkWithPoseidonConstraintSystem;
use plonk_without_poseidon::PlonkWithoutPoseidonConstraintSystem;
use std::cell::RefCell;
use std::ops::{Deref, DerefMut, Neg};
use std::rc::Rc;
use stwo_prover::core::backend::Column;
use stwo_prover::core::fields::m31::M31;
use stwo_prover::core::fields::qm31::QM31;
use stwo_prover::examples::plonk::PlonkCircuitTrace;
use stwo_prover::examples::plonk_with_poseidon::plonk::PlonkWithAcceleratorCircuitTrace;
use stwo_prover::examples::plonk_with_poseidon::poseidon::{
    PoseidonEntry, PoseidonFlow, SwapOption,
};
use stwo_prover::examples::plonk_without_poseidon::plonk::PlonkWithoutAcceleratorCircuitTrace;

pub mod dvar;

pub mod plonk_with_poseidon;
pub mod plonk_without_poseidon;

#[derive(Debug)]
pub enum ConstraintSystemEnum {
    PlonkWithPoseidon(PlonkWithPoseidonConstraintSystem),
    PlonkWithoutPoseidon(PlonkWithoutPoseidonConstraintSystem),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConstraintSystemType {
    PlonkWithPoseidon,
    PlonkWithoutPoseidon,
}

/// A shared reference to a constraint system that can be stored in high level
/// variables.
#[derive(Clone, Debug)]
pub struct ConstraintSystemRef(pub(crate) Rc<RefCell<ConstraintSystemEnum>>);

impl ConstraintSystemRef {
    pub fn new_plonk_with_poseidon_ref() -> Self {
        Self(Rc::new(RefCell::new(
            ConstraintSystemEnum::PlonkWithPoseidon(PlonkWithPoseidonConstraintSystem::new()),
        )))
    }

    pub fn new_plonk_without_poseidon_ref() -> Self {
        Self(Rc::new(RefCell::new(
            ConstraintSystemEnum::PlonkWithoutPoseidon(PlonkWithoutPoseidonConstraintSystem::new()),
        )))
    }

    pub fn get_value(&self, idx: usize) -> QM31 {
        match self.0.borrow().deref() {
            ConstraintSystemEnum::PlonkWithPoseidon(cs) => cs.variables[idx].clone(),
            ConstraintSystemEnum::PlonkWithoutPoseidon(cs) => cs.variables[idx].clone(),
        }
    }

    pub fn get_type(&self) -> ConstraintSystemType {
        match self.0.borrow().deref() {
            ConstraintSystemEnum::PlonkWithPoseidon(_) => ConstraintSystemType::PlonkWithPoseidon,
            ConstraintSystemEnum::PlonkWithoutPoseidon(_) => {
                ConstraintSystemType::PlonkWithoutPoseidon
            }
        }
    }

    pub fn get_cache(&self, str: impl ToString) -> Option<usize> {
        match self.0.borrow().deref() {
            ConstraintSystemEnum::PlonkWithPoseidon(cs) => cs.cache.get(&str.to_string()).cloned(),
            ConstraintSystemEnum::PlonkWithoutPoseidon(cs) => {
                cs.cache.get(&str.to_string()).cloned()
            }
        }
    }

    pub fn set_cache(&self, str: impl ToString, range: usize) {
        match self.0.borrow_mut().deref_mut() {
            ConstraintSystemEnum::PlonkWithPoseidon(cs) => {
                cs.cache.insert(str.to_string(), range);
            }
            ConstraintSystemEnum::PlonkWithoutPoseidon(cs) => {
                cs.cache.insert(str.to_string(), range);
            }
        }
    }

    pub fn new_m31(&self, variables: M31, mode: AllocationMode) -> usize {
        match self.0.borrow_mut().deref_mut() {
            ConstraintSystemEnum::PlonkWithPoseidon(cs) => cs.new_m31(variables, mode),
            ConstraintSystemEnum::PlonkWithoutPoseidon(cs) => cs.new_m31(variables, mode),
        }
    }

    pub fn new_qm31(&self, variable: QM31, mode: AllocationMode) -> usize {
        match self.0.borrow_mut().deref_mut() {
            ConstraintSystemEnum::PlonkWithPoseidon(cs) => cs.new_qm31(variable, mode),
            ConstraintSystemEnum::PlonkWithoutPoseidon(cs) => cs.new_qm31(variable, mode),
        }
    }

    pub fn and(&self, other: &Self) -> Self {
        assert_eq!(self, other);
        self.clone()
    }

    pub fn insert_gate(&self, a_wire: usize, b_wire: usize, c_wire: usize, op: M31) {
        match self.0.borrow_mut().deref_mut() {
            ConstraintSystemEnum::PlonkWithPoseidon(cs) => {
                cs.insert_gate(a_wire, b_wire, c_wire, op)
            }
            ConstraintSystemEnum::PlonkWithoutPoseidon(cs) => {
                cs.insert_gate(a_wire, b_wire, c_wire, op)
            }
        }
    }

    pub fn do_m4_gate(&self, a_wire: usize, b_wire: usize) -> usize {
        match self.0.borrow_mut().deref_mut() {
            ConstraintSystemEnum::PlonkWithPoseidon(_) => unimplemented!(),
            ConstraintSystemEnum::PlonkWithoutPoseidon(cs) => cs.do_m4_gate(a_wire, b_wire),
        }
    }

    pub fn do_pow5m4_gate(&self, a_wire: usize, b_wire: usize) -> usize {
        match self.0.borrow_mut().deref_mut() {
            ConstraintSystemEnum::PlonkWithPoseidon(_) => unimplemented!(),
            ConstraintSystemEnum::PlonkWithoutPoseidon(cs) => cs.do_pow5m4_gate(a_wire, b_wire),
        }
    }

    pub fn do_pow5_gate(&self, a_wire: usize, b_wire: usize) -> usize {
        match self.0.borrow_mut().deref_mut() {
            ConstraintSystemEnum::PlonkWithPoseidon(_) => unimplemented!(),
            ConstraintSystemEnum::PlonkWithoutPoseidon(cs) => cs.do_pow5_gate(a_wire, b_wire),
        }
    }

    pub fn do_grandsum_gate(&self, a_wire: usize, b_wire: usize) -> usize {
        match self.0.borrow_mut().deref_mut() {
            ConstraintSystemEnum::PlonkWithPoseidon(_) => unimplemented!(),
            ConstraintSystemEnum::PlonkWithoutPoseidon(cs) => cs.do_grandsum_gate(a_wire, b_wire),
        }
    }

    pub fn do_hadamard(&self, a_wire: usize, b_wire: usize) -> usize {
        match self.0.borrow_mut().deref_mut() {
            ConstraintSystemEnum::PlonkWithPoseidon(_) => unimplemented!(),
            ConstraintSystemEnum::PlonkWithoutPoseidon(cs) => cs.do_hadamard(a_wire, b_wire),
        }
    }

    pub fn add(&self, a_wire: usize, b_wire: usize) -> usize {
        match self.0.borrow_mut().deref_mut() {
            ConstraintSystemEnum::PlonkWithPoseidon(cs) => cs.add(a_wire, b_wire),
            ConstraintSystemEnum::PlonkWithoutPoseidon(cs) => cs.add(a_wire, b_wire),
        }
    }

    pub fn mul(&self, a_wire: usize, b_wire: usize) -> usize {
        match self.0.borrow_mut().deref_mut() {
            ConstraintSystemEnum::PlonkWithPoseidon(cs) => cs.mul(a_wire, b_wire),
            ConstraintSystemEnum::PlonkWithoutPoseidon(cs) => cs.mul(a_wire, b_wire),
        }
    }

    pub fn mul_constant(&self, a_wire: usize, constant: M31) -> usize {
        match self.0.borrow_mut().deref_mut() {
            ConstraintSystemEnum::PlonkWithPoseidon(cs) => cs.mul_constant(a_wire, constant),
            ConstraintSystemEnum::PlonkWithoutPoseidon(cs) => cs.mul_constant(a_wire, constant),
        }
    }

    pub fn enforce_zero(&self, var: usize) {
        match self.0.borrow_mut().deref_mut() {
            ConstraintSystemEnum::PlonkWithPoseidon(cs) => {
                cs.enforce_zero(var);
            }
            ConstraintSystemEnum::PlonkWithoutPoseidon(cs) => {
                cs.enforce_zero(var);
            }
        }
    }

    pub fn check_arithmetics(&self) {
        match self.0.borrow().deref() {
            ConstraintSystemEnum::PlonkWithPoseidon(cs) => cs.check_arithmetics(),
            ConstraintSystemEnum::PlonkWithoutPoseidon(cs) => cs.check_arithmetics(),
        }
    }

    pub fn populate_logup_arguments(&self) {
        match self.0.borrow_mut().deref_mut() {
            ConstraintSystemEnum::PlonkWithPoseidon(cs) => cs.populate_logup_arguments(),
            ConstraintSystemEnum::PlonkWithoutPoseidon(cs) => cs.populate_logup_arguments(),
        }
    }

    pub fn check_poseidon_invocations(&self) {
        match self.0.borrow().deref() {
            ConstraintSystemEnum::PlonkWithPoseidon(cs) => cs.check_poseidon_invocations(),
            ConstraintSystemEnum::PlonkWithoutPoseidon(_) => {
                unimplemented!()
            }
        }
    }

    pub fn invoke_poseidon_accelerator(
        &self,
        entry_1: PoseidonEntry,
        entry_2: PoseidonEntry,
        entry_3: PoseidonEntry,
        entry_4: PoseidonEntry,
        swap_option: SwapOption,
    ) {
        match self.0.borrow_mut().deref_mut() {
            ConstraintSystemEnum::PlonkWithPoseidon(cs) => {
                cs.invoke_poseidon_accelerator(entry_1, entry_2, entry_3, entry_4, swap_option);
            }
            ConstraintSystemEnum::PlonkWithoutPoseidon(_) => {
                unimplemented!()
            }
        }
    }

    pub fn pad(&self) {
        match self.0.borrow_mut().deref_mut() {
            ConstraintSystemEnum::PlonkWithPoseidon(cs) => {
                cs.pad();
            }
            ConstraintSystemEnum::PlonkWithoutPoseidon(cs) => {
                cs.pad();
            }
        }
    }

    pub fn generate_plonk_with_poseidon_circuit(
        &self,
    ) -> (PlonkWithAcceleratorCircuitTrace, PoseidonFlow) {
        match self.0.borrow_mut().deref_mut() {
            ConstraintSystemEnum::PlonkWithPoseidon(cs) => {
                cs.generate_plonk_with_poseidon_circuit()
            }
            ConstraintSystemEnum::PlonkWithoutPoseidon(_) => {
                unimplemented!()
            }
        }
    }

    pub fn generate_plonk_without_poseidon_circuit(&self) -> PlonkWithoutAcceleratorCircuitTrace {
        match self.0.borrow_mut().deref_mut() {
            ConstraintSystemEnum::PlonkWithPoseidon(_) => {
                unimplemented!()
            }
            ConstraintSystemEnum::PlonkWithoutPoseidon(cs) => {
                cs.generate_plonk_without_poseidon_circuit()
            }
        }
    }

    pub fn num_plonk_rows(&self) -> usize {
        match self.0.borrow_mut().deref_mut() {
            ConstraintSystemEnum::PlonkWithPoseidon(cs) => cs.a_wire.len(),
            ConstraintSystemEnum::PlonkWithoutPoseidon(cs) => cs.a_wire.len(),
        }
    }

    pub fn assemble_poseidon_gate(&self, a_wire: usize, b_wire: usize) -> usize {
        match self.0.borrow_mut().deref_mut() {
            ConstraintSystemEnum::PlonkWithPoseidon(cs) => {
                cs.assemble_poseidon_gate(a_wire, b_wire)
            }
            ConstraintSystemEnum::PlonkWithoutPoseidon(_) => {
                unimplemented!()
            }
        }
    }
}

impl PartialEq for ConstraintSystemRef {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}

pub const LOG_CONSTRAINT_SYSTEM_RESERVED_SIZE: usize = 16;
