mod complete_semantics_solver;
pub use complete_semantics_solver::CompleteSemanticsSolver;

mod grounded_semantics_solver;
pub use grounded_semantics_solver::GroundedSemanticsSolver;

mod specs;
pub use specs::CredulousAcceptanceComputer;
pub use specs::SingleExtensionComputer;
pub use specs::SkepticalAcceptanceComputer;

mod stable_semantics_solver;
pub use stable_semantics_solver::StableSemanticsSolver;
