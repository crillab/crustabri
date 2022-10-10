use super::specs::CredulousAcceptanceComputer;
use crate::Argument;
use crate::{
    clause,
    sat::{Literal, SatSolver},
    AAFramework, LabelType,
};

/// A SAT-based solver for the complete semantics.
///
/// This solver does not provides function to compute an extension or to check the skeptical acceptance
/// of an argument as they can be computed in a more efficient way by a [GroundedSemanticsSolver](super::GroundedSemanticsSolver).
pub struct CompleteSemanticsSolver<'a, T>
where
    T: LabelType,
{
    solver: Box<dyn SatSolver>,
    af: &'a AAFramework<T>,
}

impl<'a, T> CompleteSemanticsSolver<'a, T>
where
    T: LabelType,
{
    /// Builds a new SAT based solver for the complete semantics.
    pub fn new(af: &'a AAFramework<T>) -> Self {
        let solver = crate::default_solver();
        let mut res = Self { solver, af };
        res.encode_disjunction_vars();
        res.encode_complete_semantics_constraints();
        res
    }

    fn encode_disjunction_vars(&mut self) {
        self.af.argument_set().iter().for_each(|arg| {
            let attacked_id = arg.id();
            let attacked_solver_var = arg_id_to_solver_var(attacked_id) as isize;
            let attacked_disjunction_solver_var =
                arg_id_to_solver_disjunction_var(attacked_id) as isize;
            self.solver.add_clause(clause![
                -attacked_solver_var,
                -attacked_disjunction_solver_var
            ]);
            let mut full_cl = clause![-attacked_disjunction_solver_var];
            self.af.iter_attacks_to_id(attacked_id).for_each(|att| {
                let attacker_id = att.attacker().id();
                let attacker_solver_var = arg_id_to_solver_var(attacker_id) as isize;
                self.solver.add_clause(clause![
                    attacked_disjunction_solver_var,
                    -attacker_solver_var
                ]);
                full_cl.push(attacker_solver_var.into());
            });
            self.solver.add_clause(full_cl)
        });
    }

    fn encode_complete_semantics_constraints(&mut self) {
        self.af.argument_set().iter().for_each(|arg| {
            let attacked_id = arg.id();
            let attacked_solver_var = arg_id_to_solver_var(attacked_id) as isize;
            let mut full_cl = clause![attacked_solver_var];
            self.af.iter_attacks_to_id(attacked_id).for_each(|att| {
                let attacker_id = att.attacker().id();
                let attacker_disjunction_solver_var =
                    arg_id_to_solver_disjunction_var(attacker_id) as isize;
                self.solver.add_clause(clause![
                    -attacked_solver_var,
                    attacker_disjunction_solver_var
                ]);
                full_cl.push((-attacker_disjunction_solver_var).into());
            });
            self.solver.add_clause(full_cl)
        });
    }
}

impl<T> CredulousAcceptanceComputer<T> for CompleteSemanticsSolver<'_, T>
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

fn arg_id_to_solver_var(id: usize) -> usize {
    (id + 1) << 1
}

fn arg_id_to_solver_disjunction_var(id: usize) -> usize {
    ((id + 1) << 1) + 1
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::AspartixReader;

    #[test]
    fn test_acceptance_1() {
        let instance = r#"
        arg(a0).
        arg(a1).
        att(a0,a1).
        "#;
        let reader = AspartixReader::default();
        let af = reader.read(&mut instance.as_bytes()).unwrap();
        let mut solver = CompleteSemanticsSolver::new(&af);
        assert!(solver
            .is_credulously_accepted(af.argument_set().get_argument(&"a0".to_string()).unwrap()));
        assert!(!solver
            .is_credulously_accepted(af.argument_set().get_argument(&"a1".to_string()).unwrap()));
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
        let mut solver = CompleteSemanticsSolver::new(&af);
        assert!(solver
            .is_credulously_accepted(af.argument_set().get_argument(&"a0".to_string()).unwrap()));
        assert!(solver
            .is_credulously_accepted(af.argument_set().get_argument(&"a1".to_string()).unwrap()));
    }

    #[test]
    fn test_acceptance_3() {
        let instance = r#"
        arg(a0).
        arg(a1).
        arg(a2).
        att(a0,a1).
        att(a1,a0).
        att(a0,a2).
        "#;
        let reader = AspartixReader::default();
        let af = reader.read(&mut instance.as_bytes()).unwrap();
        let mut solver = CompleteSemanticsSolver::new(&af);
        assert!(solver
            .is_credulously_accepted(af.argument_set().get_argument(&"a0".to_string()).unwrap()));
        assert!(solver
            .is_credulously_accepted(af.argument_set().get_argument(&"a1".to_string()).unwrap()));
        assert!(solver
            .is_credulously_accepted(af.argument_set().get_argument(&"a2".to_string()).unwrap()));
    }
}
