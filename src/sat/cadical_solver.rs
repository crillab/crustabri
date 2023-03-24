use super::{
    sat_solver::{SolvingListener, SolvingResult},
    Assignment, Literal, SatSolver,
};
use cadical::Solver as CadicalCSolver;

/// A wrapper around the CaDiCaL SAT solver.
///
/// See CaDiCaL on [crates.io](https://crates.io/crates/cadical).
#[derive(Default)]
pub struct CadicalSolver {
    solver: CadicalCSolver,
    listeners: Vec<Box<dyn SolvingListener>>,
}

impl SatSolver for CadicalSolver {
    fn add_clause(&mut self, cl: Vec<Literal>) {
        self.solver
            .add_clause(cl.into_iter().map(|l| isize::from(l) as i32))
    }

    fn solve(&mut self) -> SolvingResult {
        self.solve_under_assumptions(&[])
    }

    fn solve_under_assumptions(&mut self, assumptions: &[Literal]) -> SolvingResult {
        self.listeners
            .iter()
            .for_each(|l| l.solving_start(self.n_vars(), self.solver.num_clauses()));
        let solving_result = match self
            .solver
            .solve_with(assumptions.iter().map(|l| isize::from(*l) as i32))
        {
            Some(true) => {
                let assignment = Assignment::new(
                    (1..=self.solver.max_variable())
                        .map(|i| self.solver.value(i))
                        .collect(),
                );
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
        self.solver.max_variable() as usize
    }

    fn add_listener(&mut self, listener: Box<dyn SolvingListener>) {
        self.listeners.push(listener);
    }

    fn reserve(&mut self, new_max_id: usize) {
        self.solver.reserve(new_max_id as i32);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sat::clause;

    #[test]
    fn test_sat() {
        let mut s = CadicalSolver::default();
        s.add_clause(clause![-1, 2]);
        let assignment = s.solve().unwrap_model().unwrap();
        assert!(assignment.value_of(1) == Some(false) || assignment.value_of(2) == Some(true))
    }

    #[test]
    fn test_unsat() {
        let mut s = CadicalSolver::default();
        s.add_clause(clause![-1, 2]);
        s.add_clause(clause![-1, -2]);
        s.add_clause(clause![1]);
        assert!(s.solve().unwrap_model().is_none());
    }

    #[test]
    fn test_iterative() {
        let mut s = CadicalSolver::default();
        s.add_clause(clause![-1, 2]);
        let assignment_1 = s.solve().unwrap_model().unwrap();
        assert!(assignment_1.value_of(1) == Some(false) || assignment_1.value_of(2) == Some(true));
        s.add_clause(clause![1, 3]);
        s.add_clause(clause![-2, 3]);
        let assignment_2 = s.solve().unwrap_model().unwrap();
        assert!(assignment_2.value_of(1) == Some(false) || assignment_2.value_of(2) == Some(true));
        assert!(assignment_2.value_of(3) == Some(true));
        s.add_clause(clause![-3]);
        assert!(s.solve().unwrap_model().is_none());
    }

    #[test]
    fn test_solve_under_assumptions() {
        let mut s = CadicalSolver::default();
        s.add_clause(clause![1]);
        assert!(s
            .solve_under_assumptions(&[Literal::from(-1)])
            .unwrap_model()
            .is_none());
    }
}
