use super::specs::CredulousAcceptanceComputer;
use super::utils::{cc_arg_to_init_af_arg, cc_assignment_to_init_af_extension};
use crate::{
    clause,
    sat::{Literal, SatSolver, SatSolverFactoryFn},
    AAFramework, ConnectedComponentsComputer, LabelType,
};
use crate::{grounded_extension, Argument};

/// A SAT-based solver for the complete semantics.
///
/// This solver does not provides function to compute an extension or to check the skeptical acceptance
/// of an argument as they can be computed in a more efficient way by a [GroundedSemanticsSolver](super::GroundedSemanticsSolver).
pub struct CompleteSemanticsSolver<'a, T>
where
    T: LabelType,
{
    af: &'a AAFramework<T>,
    solver_factory: Box<SatSolverFactoryFn>,
}

impl<'a, T> CompleteSemanticsSolver<'a, T>
where
    T: LabelType,
{
    /// Builds a new SAT based solver for the complete semantics.
    ///
    /// The underlying SAT solver is one returned by [default_solver](crate::default_solver).
    pub fn new(af: &'a AAFramework<T>) -> Self
    where
        T: LabelType,
    {
        Self::new_with_sat_solver_factory(af, Box::new(|| crate::default_solver()))
    }

    /// Builds a new SAT based solver for the complete semantics.
    ///
    /// The SAT solver to use in given through the solver factory.
    pub fn new_with_sat_solver_factory(
        af: &'a AAFramework<T>,
        solver_factory: Box<SatSolverFactoryFn>,
    ) -> Self
    where
        T: LabelType,
    {
        Self { af, solver_factory }
    }
}

fn encode_disjunction_vars<T>(af: &AAFramework<T>, solver: &mut dyn SatSolver)
where
    T: LabelType,
{
    af.argument_set().iter().for_each(|arg| {
        let attacked_id = arg.id();
        let attacked_solver_var = arg_id_to_solver_var(attacked_id) as isize;
        let attacked_disjunction_solver_var =
            arg_id_to_solver_disjunction_var(attacked_id) as isize;
        solver.add_clause(clause![
            -attacked_solver_var,
            -attacked_disjunction_solver_var
        ]);
        let mut full_cl = clause![-attacked_disjunction_solver_var];
        af.iter_attacks_to(arg).for_each(|att| {
            let attacker_id = att.attacker().id();
            let attacker_solver_var = arg_id_to_solver_var(attacker_id) as isize;
            solver.add_clause(clause![
                attacked_disjunction_solver_var,
                -attacker_solver_var
            ]);
            full_cl.push(attacker_solver_var.into());
        });
        solver.add_clause(full_cl)
    });
}

pub(crate) fn encode_complete_semantics_constraints<T>(
    af: &AAFramework<T>,
    solver: &mut dyn SatSolver,
) where
    T: LabelType,
{
    encode_disjunction_vars(af, solver);
    af.argument_set().iter().for_each(|arg| {
        let attacked_id = arg.id();
        let attacked_solver_var = arg_id_to_solver_var(attacked_id) as isize;
        let mut full_cl = clause![attacked_solver_var];
        af.iter_attacks_to(arg).for_each(|att| {
            let attacker_id = att.attacker().id();
            let attacker_disjunction_solver_var =
                arg_id_to_solver_disjunction_var(attacker_id) as isize;
            solver.add_clause(clause![
                -attacked_solver_var,
                attacker_disjunction_solver_var
            ]);
            full_cl.push((-attacker_disjunction_solver_var).into());
        });
        solver.add_clause(full_cl)
    });
}

impl<T> CredulousAcceptanceComputer<T> for CompleteSemanticsSolver<'_, T>
where
    T: LabelType,
{
    fn is_credulously_accepted(&mut self, arg: &Argument<T>) -> bool {
        let mut solver = (self.solver_factory)();
        let mut cc_computer = ConnectedComponentsComputer::new(self.af);
        let reduced_af = cc_computer.connected_component_of(arg);
        encode_complete_semantics_constraints(&reduced_af, solver.as_mut());
        let arg_in_reduced_af = reduced_af.argument_set().get_argument(arg.label()).unwrap();
        solver
            .solve_under_assumptions(&[Literal::from(
                arg_id_to_solver_var(arg_in_reduced_af.id()) as isize
            )])
            .unwrap_model()
            .is_some()
    }

    fn is_credulously_accepted_with_certificate(
        &mut self,
        arg: &Argument<T>,
    ) -> (bool, Option<Vec<&Argument<T>>>) {
        let mut cc_computer = ConnectedComponentsComputer::new(self.af);
        let reduced_af = cc_computer.connected_component_of(arg);
        let mut solver = (self.solver_factory)();
        encode_complete_semantics_constraints(&reduced_af, solver.as_mut());
        let arg_in_reduced_af = reduced_af.argument_set().get_argument(arg.label()).unwrap();
        match solver
            .solve_under_assumptions(&[Literal::from(
                arg_id_to_solver_var(arg_in_reduced_af.id()) as isize
            )])
            .unwrap_model()
        {
            Some(model) => {
                let mut merged = cc_assignment_to_init_af_extension(
                    model,
                    &reduced_af,
                    self.af,
                    arg_id_from_solver_var,
                );
                while let Some(other_cc_af) = cc_computer.next_connected_component() {
                    let other_cc_grounded = grounded_extension(&other_cc_af);
                    other_cc_grounded
                        .iter()
                        .map(|a| cc_arg_to_init_af_arg(a, self.af))
                        .for_each(|a| merged.push(a));
                }
                (true, Some(merged))
            }
            None => (false, None),
        }
    }
}

pub(crate) fn arg_id_to_solver_var(id: usize) -> usize {
    (id + 1) << 1
}

pub(crate) fn arg_id_from_solver_var(v: usize) -> Option<usize> {
    if v & 1 == 1 {
        None
    } else {
        Some((v >> 1) - 1)
    }
}

fn arg_id_to_solver_disjunction_var(id: usize) -> usize {
    arg_id_to_solver_var(id) - 1
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{io::InstanceReader, AspartixReader};

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

    #[test]
    fn test_id_to_var() {
        assert_eq!(0, arg_id_from_solver_var(arg_id_to_solver_var(0)).unwrap());
        assert_eq!(1, arg_id_from_solver_var(arg_id_to_solver_var(1)).unwrap());
        assert_eq!(2, arg_id_to_solver_var(arg_id_from_solver_var(2).unwrap()));
        assert_eq!(4, arg_id_to_solver_var(arg_id_from_solver_var(4).unwrap()));
    }

    #[test]
    fn test_credulous_acceptance_after_arg_removal() {
        let instance = r#"
        arg(a0).
        arg(a1).
        arg(a2).
        att(a0,a1).
        att(a1,a2).
        att(a2,a1).
        "#;
        let reader = AspartixReader::default();
        let mut af = reader.read(&mut instance.as_bytes()).unwrap();
        let mut solver_before = CompleteSemanticsSolver::new(&af);
        assert!(!solver_before
            .is_credulously_accepted(af.argument_set().get_argument(&"a1".to_string()).unwrap()));
        af.remove_argument(&"a0".to_string()).unwrap();
        let mut solver_after = CompleteSemanticsSolver::new(&af);
        assert!(solver_after
            .is_credulously_accepted(af.argument_set().get_argument(&"a1".to_string()).unwrap()));
    }

    #[test]
    fn test_certificates() {
        let instance = r#"
        arg(a0).
        arg(a1).
        att(a0,a1).
        "#;
        let reader = AspartixReader::default();
        let af = reader.read(&mut instance.as_bytes()).unwrap();
        let mut solver = CompleteSemanticsSolver::new(&af);
        assert_eq!(
            &["a0"],
            solver
                .is_credulously_accepted_with_certificate(
                    af.argument_set().get_argument(&"a0".to_string()).unwrap()
                )
                .1
                .unwrap()
                .iter()
                .map(|a| a.label())
                .cloned()
                .collect::<Vec<String>>()
                .as_slice()
        );
    }
}
