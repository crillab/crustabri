//! This module contains the main material used to define ABA frameworks and their related problems.

mod aba_framework;
pub use aba_framework::FlatABAFramework;

mod complete_constraints_encoder;
pub use complete_constraints_encoder::FlatABACompleteConstraintsEncoder;

use crate::{
    aa::Argument,
    sat::{Assignment, Literal, SatSolver},
    utils::LabelType,
};

/// The trait for encoders from Flat ABA frameworks to SAT.
pub trait FlatABAConstraintsEncoder<T>
where
    T: LabelType,
{
    /// Encodes the constraints for the underlying semantics into the SAT solver.
    fn encode_constraints(&self, af: &FlatABAFramework<T>, solver: &mut dyn SatSolver);

    /// Translates back a SAT assignment into the corresponding set of arguments.
    fn assignment_to_extension<'a>(
        &self,
        assignment: &Assignment,
        af: &'a FlatABAFramework<T>,
    ) -> Vec<&'a Argument<T>>;

    /// Translates an argument into the literal that represent it.
    fn arg_to_lit(&self, arg: &Argument<T>) -> Literal;
}
