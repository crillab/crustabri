use std::ffi::OsStr;

use super::{Assignment, Literal, SatSolver, SatSolverFactory, SolvingListener, SolvingResult};
use ipasir_loading::{IpasirSolverLoader, IpasirSolverWrapper};

/// A wrapper for solvers that implement the IPASIR interface.
pub struct IpasirSatSolver {
    solver: IpasirSolverWrapper,
    listeners: Vec<Box<dyn SolvingListener>>,
    n_vars: i32,
    n_clauses: usize,
}

impl IpasirSatSolver {
    /// Builds a new [`IpasirSatSolver`] given the underlying solver.
    pub fn new(solver: IpasirSolverWrapper) -> Self {
        Self {
            solver,
            listeners: vec![],
            n_vars: 0,
            n_clauses: 0,
        }
    }
}

impl SatSolver for IpasirSatSolver {
    fn add_clause(&mut self, cl: Vec<Literal>) {
        for l in cl {
            let i32_lit = isize::from(l) as i32;
            self.solver.ipasir_add(i32_lit).unwrap();
            self.n_vars = i32::max(self.n_vars, i32_lit.abs());
        }
        self.solver.ipasir_add(0).unwrap();
        self.n_clauses += 1;
    }

    fn solve(&mut self) -> SolvingResult {
        self.solve_under_assumptions(&[])
    }

    fn solve_under_assumptions(&mut self, assumptions: &[Literal]) -> SolvingResult {
        self.listeners
            .iter()
            .for_each(|l| l.solving_start(self.n_vars(), self.n_clauses));
        for l in assumptions {
            let i32_lit = isize::from(*l) as i32;
            self.solver.ipasir_assume(i32_lit).unwrap();
            self.n_vars = i32::max(self.n_vars, i32_lit.abs());
        }
        let solving_result = match self.solver.ipasir_solve().unwrap() {
            Some(true) => {
                let assignment_it: Box<dyn Iterator<Item = Option<bool>>> = Box::new(
                    (1..=self.n_vars()).map(|i| self.solver.ipasir_val(i as i32).unwrap()),
                );
                let assignment = Assignment::new(assignment_it.collect());
                SolvingResult::Satisfiable(assignment)
            }
            Some(false) => SolvingResult::Unsatisfiable,
            None => SolvingResult::Unknown,
        };
        self.listeners
            .iter()
            .for_each(|l| l.solving_end(&solving_result));
        solving_result
    }

    fn n_vars(&self) -> usize {
        self.n_vars as usize
    }

    fn add_listener(&mut self, listener: Box<dyn SolvingListener>) {
        self.listeners.push(listener);
    }

    fn reserve(&mut self, new_max_id: usize) {
        self.n_vars = i32::max(self.n_vars, new_max_id as i32)
    }
}

/// A [`SatSolverFactory`] for [`IpasirSatSolver`].
pub struct IpasirSatSolverFactory {
    loader: IpasirSolverLoader,
}

impl IpasirSatSolverFactory {
    /// Creates a new [`IpasirSatSolverFactory`] given a path the the underlying library.
    pub fn new<P: AsRef<OsStr>>(path: P) -> Self {
        Self {
            loader: IpasirSolverLoader::from_path(path).unwrap(),
        }
    }

    /// Returns the IPASIR signature of the underlying library.
    pub fn ipasir_signature(&self) -> String {
        self.loader.ipasir_signature().unwrap()
    }
}

impl SatSolverFactory for IpasirSatSolverFactory {
    fn new_solver(&self) -> Box<dyn SatSolver> {
        Box::new(IpasirSatSolver::new(self.loader.new_solver().unwrap()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_n_vars() {
        if let Ok(path) = std::env::var("IPASIR_LIBRARY") {
            let factory = IpasirSatSolverFactory::new(path);
            let mut solver = factory.new_solver();
            assert_eq!(0, solver.n_vars());
            solver.add_clause(vec![Literal::from(-1)]);
            assert_eq!(1, solver.n_vars());
        }
    }
}
