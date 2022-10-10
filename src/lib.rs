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
pub use solvers::CredulousAcceptanceComputer;
pub use solvers::SingleExtensionComputer;
pub use solvers::SkepticalAcceptanceComputer;
pub use solvers::StableEncodingSolver;

mod sat;
pub(crate) use sat::default_solver;
