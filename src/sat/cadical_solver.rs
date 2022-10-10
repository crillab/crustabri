use super::{sat_solver::SolvingResult, Assignment, Literal, SatSolver};
use cadical::Solver as CadicalCSolver;

#[derive(Default)]
pub struct CadicalSolver {
    solver: CadicalCSolver,
}

impl SatSolver for CadicalSolver {
    fn add_clause(&mut self, cl: Vec<Literal>) {
        self.solver
            .add_clause(cl.into_iter().map(|l| isize::from(l) as i32))
    }

    fn solve(&mut self) -> SolvingResult {
        match self.solver.solve() {
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
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::clause;

    #[test]
    fn test_sat() {
        let mut s = CadicalSolver::default();
        s.add_clause(clause![-1, 2]);
        match s.solve() {
            SolvingResult::Satisfiable(assignment) => {
                assert!(
                    assignment.value_of(1) == Some(false) || assignment.value_of(2) == Some(true)
                )
            }
            _ => panic!(),
        }
    }

    #[test]
    fn test_unsat() {
        let mut s = CadicalSolver::default();
        s.add_clause(clause![-1, 2]);
        s.add_clause(clause![-1, -2]);
        s.add_clause(clause![1]);
        assert!(matches!(s.solve(), SolvingResult::Unsatisfiable));
    }

    #[test]
    fn test_iterative() {
        let mut s = CadicalSolver::default();
        s.add_clause(clause![-1, 2]);
        match s.solve() {
            SolvingResult::Satisfiable(assignment) => {
                assert!(
                    assignment.value_of(1) == Some(false) || assignment.value_of(2) == Some(true)
                )
            }
            _ => panic!(),
        }
        s.add_clause(clause![1, 3]);
        s.add_clause(clause![-2, 3]);
        match s.solve() {
            SolvingResult::Satisfiable(assignment) => {
                assert!(
                    assignment.value_of(1) == Some(false) || assignment.value_of(2) == Some(true)
                );
                assert!(assignment.value_of(3) == Some(true))
            }
            _ => panic!(),
        }
        s.add_clause(clause![-3]);
        assert!(matches!(s.solve(), SolvingResult::Unsatisfiable));
    }
}
