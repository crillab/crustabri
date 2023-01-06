//! Solvers dedicated to problems related to Abstract Argumentation frameworks.

mod complete_semantics_solver;
pub use complete_semantics_solver::CompleteSemanticsSolver;

mod grounded_semantics_solver;
pub use grounded_semantics_solver::GroundedSemanticsSolver;

mod ideal_semantics_solver;
pub use ideal_semantics_solver::IdealSemanticsSolver;

pub(crate) mod maximal_extension_computer;

mod maximal_range_semantics_solvers;
pub use maximal_range_semantics_solvers::SemiStableSemanticsSolver;
pub use maximal_range_semantics_solvers::StageSemanticsSolver;

mod preferred_semantics_solver;
pub use preferred_semantics_solver::PreferredSemanticsSolver;

mod specs;
pub use specs::CredulousAcceptanceComputer;
pub use specs::SingleExtensionComputer;
pub use specs::SkepticalAcceptanceComputer;

mod stable_semantics_solver;
pub use stable_semantics_solver::StableSemanticsSolver;
