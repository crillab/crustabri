use super::specs::{
    CredulousAcceptanceComputer, SingleExtensionComputer, SkepticalAcceptanceComputer,
};
use crate::Argument;
use crate::{
    clause,
    sat::{Literal, SatSolver},
    AAFramework, LabelType,
};

/// A SAT-based solver for the stable semantics.
pub struct StableSemanticsSolver<'a, T>
where
    T: LabelType,
{
    solver: Box<dyn SatSolver>,
    af: &'a AAFramework<T>,
}

impl<'a, T> StableSemanticsSolver<'a, T>
where
    T: LabelType,
{
    /// Builds a new SAT based solver for the stable semantics.
    pub fn new(af: &'a AAFramework<T>) -> Self {
        let solver = crate::default_solver();
        let mut res = Self { solver, af };
        res.encode();
        res
    }

    fn encode(&mut self) {
        self.af.argument_set().iter().for_each(|arg| {
            let attacked_id = arg.id();
            let attacked_solver_var = arg_id_to_solver_var(attacked_id) as isize;
            let mut full_cl = clause![attacked_solver_var];
            self.af.iter_attacks_to_id(attacked_id).for_each(|att| {
                let attacker_id = att.attacker().id();
                if attacked_id == attacker_id {
                    self.solver.add_clause(clause![-attacked_solver_var])
                } else {
                    let attacker_solver_var = arg_id_to_solver_var(attacker_id) as isize;
                    self.solver
                        .add_clause(clause![-attacked_solver_var, -attacker_solver_var]);
                    full_cl.push(attacker_solver_var.into());
                }
            });
            self.solver.add_clause(full_cl);
        });
    }
}

impl<T> SingleExtensionComputer<T> for StableSemanticsSolver<'_, T>
where
    T: LabelType,
{
    fn compute_one_extension(&mut self) -> Option<Vec<&Argument<T>>> {
        self.solver.solve().unwrap_model().map(|assignment| {
            assignment
                .iter()
                .filter_map(|(var, val)| match val {
                    Some(true) => Some(
                        self.af
                            .argument_set()
                            .get_argument_by_id(arg_id_from_solver_var(var)),
                    ),
                    _ => None,
                })
                .collect()
        })
    }
}

impl<T> CredulousAcceptanceComputer<T> for StableSemanticsSolver<'_, T>
where
    T: LabelType,
{
    fn is_credulously_accepted(&mut self, arg: &Argument<T>) -> bool {
        self.solver
            .solve_under_assumptions(&[Literal::from(arg_id_to_solver_var(arg.id()) as isize)])
            .unwrap_model()
            .is_some()
    }
}

impl<T> SkepticalAcceptanceComputer<T> for StableSemanticsSolver<'_, T>
where
    T: LabelType,
{
    fn is_skeptically_accepted(&mut self, arg: &Argument<T>) -> bool {
        self.solver
            .solve_under_assumptions(&[
                Literal::from(arg_id_to_solver_var(arg.id()) as isize).negate()
            ])
            .unwrap_model()
            .is_none()
    }
}

fn arg_id_to_solver_var(id: usize) -> usize {
    id + 1
}

fn arg_id_from_solver_var(var: usize) -> usize {
    var - 1
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::AspartixReader;

    #[test]
    fn test_compute_one() {
        let instance = r#"
        arg(a0).
        arg(a1).
        att(a0,a1).
        "#;
        let reader = AspartixReader::default();
        let af = reader.read(&mut instance.as_bytes()).unwrap();
        let mut solver = StableSemanticsSolver::new(&af);
        assert_eq!(
            vec!["a0"],
            solver
                .compute_one_extension()
                .unwrap()
                .iter()
                .map(|arg| arg.label().to_string())
                .collect::<Vec<String>>()
        )
    }

    #[test]
    fn test_compute_one_auto_attack() {
        let instance = r#"
        arg(a0).
        arg(a1).
        att(a0,a1).
        att(a0,a0).
        "#;
        let reader = AspartixReader::default();
        let af = reader.read(&mut instance.as_bytes()).unwrap();
        let mut solver = StableSemanticsSolver::new(&af);
        assert!(solver.compute_one_extension().is_none());
    }

    #[test]
    fn test_compute_one_no_exists() {
        let instance = r#"
        arg(a0).
        arg(a1).
        arg(a2).
        att(a0,a1).
        att(a1,a2).
        att(a2,a0).
        "#;
        let reader = AspartixReader::default();
        let af = reader.read(&mut instance.as_bytes()).unwrap();
        let mut solver = StableSemanticsSolver::new(&af);
        assert!(solver.compute_one_extension().is_none());
    }

    #[test]
    fn test_acceptance_1() {
        let instance = r#"
        arg(a0).
        arg(a1).
        att(a0,a1).
        "#;
        let reader = AspartixReader::default();
        let af = reader.read(&mut instance.as_bytes()).unwrap();
        let mut solver = StableSemanticsSolver::new(&af);
        assert!(solver
            .is_credulously_accepted(af.argument_set().get_argument(&"a0".to_string()).unwrap()));
        assert!(!solver
            .is_credulously_accepted(af.argument_set().get_argument(&"a1".to_string()).unwrap()));
        assert!(solver
            .is_skeptically_accepted(af.argument_set().get_argument(&"a0".to_string()).unwrap()));
        assert!(!solver
            .is_skeptically_accepted(af.argument_set().get_argument(&"a1".to_string()).unwrap()));
    }

    #[test]
    fn test_acceptance_2() {
        let instance = r#"
        arg(a0).
        arg(a1).
        att(a0,a1).
        att(a1,a0).
        "#;
        let reader = AspartixReader::default();
        let af = reader.read(&mut instance.as_bytes()).unwrap();
        let mut solver = StableSemanticsSolver::new(&af);
        assert!(solver
            .is_credulously_accepted(af.argument_set().get_argument(&"a0".to_string()).unwrap()));
        assert!(solver
            .is_credulously_accepted(af.argument_set().get_argument(&"a1".to_string()).unwrap()));
        assert!(!solver
            .is_skeptically_accepted(af.argument_set().get_argument(&"a0".to_string()).unwrap()));
        assert!(!solver
            .is_skeptically_accepted(af.argument_set().get_argument(&"a1".to_string()).unwrap()));
    }
}
