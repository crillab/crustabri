//! This module contains the main material used to define ABA frameworks and their related problems.

mod aba_framework;
pub use aba_framework::FlatABAFramework;

mod aba_reduce;

mod aba_remove_cycles;
pub use aba_remove_cycles::FlatABACycleBreaker;

mod complete_semantics_solver;
pub use complete_semantics_solver::FlatABACompleteConstraintsSolver;

mod constraints_encoder;
pub use constraints_encoder::CompleteSemanticsEncoder;
pub use constraints_encoder::StableSemanticsEncoder;

mod preferred_semantics_solver;
pub use preferred_semantics_solver::FlatABAPreferredConstraintsSolver;

mod stable_semantics_solver;
pub use stable_semantics_solver::FlatABAStableConstraintsSolver;

use crate::{
    aa::Argument,
    sat::{Assignment, SatSolver},
    utils::LabelType,
};

/// The trait for encoders from Flat ABA frameworks to SAT.
pub trait FlatABAConstraintsEncoder<T>
where
    T: LabelType,
{
    /// Encodes the constraints for the underlying semantics into the SAT solver.
    fn new(
        af: &FlatABAFramework<T>,
        solver: Box<dyn SatSolver>,
        cycle_breaker: FlatABACycleBreaker<T>,
    ) -> Self;

    /// Translates back a SAT assignment into the corresponding set of arguments.
    fn assignment_to_extension(&self, assignment: &Assignment) -> Vec<&Argument<T>>;
}
