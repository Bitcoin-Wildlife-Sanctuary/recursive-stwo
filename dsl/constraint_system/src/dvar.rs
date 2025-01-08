use crate::ConstraintSystemRef;
use serde::de::DeserializeOwned;
use serde::Serialize;

pub trait DVar: Clone {
    /// The type of the "native" value that `Self` represents in the constraint
    /// system.
    type Value: core::fmt::Debug + Eq + Clone + Serialize + DeserializeOwned;

    /// Returns the underlying `ConstraintSystemRef`.
    fn cs(&self) -> ConstraintSystemRef;
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum AllocationMode {
    PublicInput,
    Witness,
    Constant,
}

pub trait AllocVar: DVar {
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
