//! SAT solver interfaces for Abstract Argumentation solvers.

mod buffered_sat_solver;
pub use buffered_sat_solver::BufferedSatSolver;
pub use buffered_sat_solver::DimacsInstanceRead;
pub use buffered_sat_solver::SolvingFn;

mod cadical_solver;
pub use cadical_solver::CadicalSolver;

mod external_sat_solver;
pub use external_sat_solver::ExternalSatSolver;

mod ipasir_sat_solver;
pub use ipasir_sat_solver::IpasirSatSolver;

mod sat_solver;
pub(crate) use sat_solver::clause;
pub use sat_solver::default_solver;
pub use sat_solver::Assignment;
pub use sat_solver::DefaultSatSolverFactory;
pub use sat_solver::Literal;
pub use sat_solver::SatSolver;
pub use sat_solver::SatSolverFactory;
pub use sat_solver::SolvingListener;
pub use sat_solver::SolvingResult;
pub use sat_solver::Variable;
