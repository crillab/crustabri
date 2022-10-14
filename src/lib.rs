//! Crustabri is a RUST ABstract argumentation Reasoner Implementation.

#![warn(missing_docs)]
#![warn(rustdoc::missing_doc_code_examples)]

mod aa;
pub use aa::read_problem_string;
pub use aa::AAFramework;
pub use aa::Argument;
pub use aa::ArgumentSet;
pub use aa::AspartixReader;
pub use aa::AspartixWriter;
pub use aa::Attack;
pub use aa::LabelType;
pub use aa::Query;
pub use aa::Semantics;

mod solvers;
pub use solvers::CompleteSemanticsSolver;
pub use solvers::CredulousAcceptanceComputer;
pub use solvers::GroundedSemanticsSolver;
pub use solvers::PreferredSemanticsSolver;
pub use solvers::SingleExtensionComputer;
pub use solvers::SkepticalAcceptanceComputer;
pub use solvers::StableSemanticsSolver;

mod sat;
pub use sat::default_solver;
pub use sat::CadicalSolver;
pub use sat::ExternalSatSolver;
pub use sat::SatSolver;
pub use sat::SatSolverFactoryFn;

mod utils;
pub use utils::connected_component_of;
pub use utils::grounded_extension;
pub use utils::iter_connected_components;
