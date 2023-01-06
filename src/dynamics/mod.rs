//! Specs and solvers dedicated to dynamic argumentation frameworks.

mod dynamic_complete_semantics_solver;
pub(crate) use dynamic_complete_semantics_solver::DynamicCompleteConstraintsEncoder;
pub use dynamic_complete_semantics_solver::DynamicCompleteSemanticsSolver;

mod dynamic_preferred_semantics_solver;
pub use dynamic_preferred_semantics_solver::DynamicPreferredSemanticsSolver;

mod dynamic_solver;
pub use dynamic_solver::DynamicSolver;

mod dynamic_stable_semantics_solver;
pub use dynamic_stable_semantics_solver::DynamicStableSemanticsSolver;
