// ShapeCS records the R1CS structure (required once during setup for a uniform IVC) and WitnessCS records the witness assignment vectors for each step.
// These two combined are enough to check the R1CS constraints for each step.

use bellpepper_core::{ConstraintSystem, Index, LinearCombination, SynthesisError, Variable};
use ff::PrimeField;

/// records only the input and aux assignment vectors - no constraints or no names.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WitnessCS<Scalar>
where
    Scalar: PrimeField,
{
    // input_assignment[0] is always the implicit constant ONE, matching bellpepper's reservation of Index::Input(0).
    input_assignment: Vec<Scalar>,
    aux_assignment: Vec<Scalar>,
}

impl<Scalar> WitnessCS<Scalar>
where
    Scalar: PrimeField,
{
    /// the public inputs, including the leading constant ONE at index 0.
    pub fn input_assignment(&self) -> &[Scalar] {
        &self.input_assignment
    }

    /// the witness (auxiliary) assignments.
    pub fn aux_assignment(&self) -> &[Scalar] {
        &self.aux_assignment
    }
}

impl<Scalar> ConstraintSystem<Scalar> for WitnessCS<Scalar>
where
    Scalar: PrimeField,
{
    type Root = Self;

    fn new() -> Self {
        Self {
            input_assignment: vec![Scalar::ONE],
            aux_assignment: vec![],
        }
    }

    fn alloc<F, A, AR>(&mut self, _: A, f: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<Scalar, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        // the value closure IS evaluated. what is skipped is
        // storing the constraint and the name.
        self.aux_assignment.push(f()?);
        Ok(Variable::new_unchecked(Index::Aux(
            self.aux_assignment.len() - 1,
        )))
    }

    fn alloc_input<F, A, AR>(&mut self, _: A, f: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<Scalar, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        self.input_assignment.push(f()?);
        Ok(Variable::new_unchecked(Index::Input(
            self.input_assignment.len() - 1,
        )))
    }

    fn enforce<A, AR, LA, LB, LC>(&mut self, _: A, _a: LA, _b: LB, _c: LC)
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
        LA: FnOnce(LinearCombination<Scalar>) -> LinearCombination<Scalar>,
        LB: FnOnce(LinearCombination<Scalar>) -> LinearCombination<Scalar>,
        LC: FnOnce(LinearCombination<Scalar>) -> LinearCombination<Scalar>,
    {
        // do nothing: we only want the assignments. the LC builders are not even called,
        // so their allocation and evaluation cost disappears entirely. this is the line
        // that makes it fast.
    }

    fn push_namespace<NR, N>(&mut self, _: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        // no names.
    }

    fn pop_namespace(&mut self) {
        // no names.
    }

    fn get_root(&mut self) -> &mut Self::Root {
        self
    }

    /// signals to gadgets that this backend only generates a witness, so they may skip constraint-only work.
    fn is_witness_generator(&self) -> bool {
        true
    }
}
