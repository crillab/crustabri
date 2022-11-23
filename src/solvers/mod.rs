//! Solvers dedicated to problems related to Abstract Argumentation frameworks.

mod complete_semantics_solver;
pub use complete_semantics_solver::CompleteSemanticsSolver;

mod grounded_semantics_solver;
pub use grounded_semantics_solver::GroundedSemanticsSolver;

mod maximal_extension_computer;

mod preferred_semantics_solver;
pub use preferred_semantics_solver::PreferredSemanticsSolver;

mod semi_stable_semantics_solver;
pub use semi_stable_semantics_solver::SemiStableSemanticsSolver;

mod specs;
pub use specs::CredulousAcceptanceComputer;
pub use specs::SingleExtensionComputer;
pub use specs::SkepticalAcceptanceComputer;

mod stable_semantics_solver;
pub use stable_semantics_solver::StableSemanticsSolver;

mod utils;
