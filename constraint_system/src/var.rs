use crate::ConstraintSystemRef;

pub trait Var: Clone {
    /// The type of the "native" value that `Self` represents in the constraint
    /// system.
    type Value: Clone;

    /// Returns the underlying `ConstraintSystemRef`.
    fn cs(&self) -> ConstraintSystemRef;
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum AllocationMode {
    PublicInput,
    Witness,
    Constant,
}

pub trait AllocVar: Var {
    fn new_variables(cs: &ConstraintSystemRef, value: &Self::Value, mode: AllocationMode) -> Self;

    fn new_constant(cs: &ConstraintSystemRef, value: &Self::Value) -> Self {
        Self::new_variables(cs, value, AllocationMode::Constant)
    }

    fn new_public_input(cs: &ConstraintSystemRef, value: &Self::Value) -> Self {
        Self::new_variables(cs, value, AllocationMode::PublicInput)
    }

    fn new_witness(cs: &ConstraintSystemRef, value: &Self::Value) -> Self {
        Self::new_variables(cs, value, AllocationMode::Witness)
    }
}
