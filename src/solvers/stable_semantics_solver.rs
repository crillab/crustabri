use super::{
    specs::{CredulousAcceptanceComputer, SingleExtensionComputer, SkepticalAcceptanceComputer},
    utils::cc_assignment_to_init_af_extension,
};
use crate::{
    aa::{AAFramework, Argument, LabelType},
    sat::{self, clause, Literal, SatSolver, SatSolverFactoryFn},
    utils::ConnectedComponentsComputer,
};

/// A SAT-based solver for the stable semantics.
pub struct StableSemanticsSolver<'a, T>
where
    T: LabelType,
{
    af: &'a AAFramework<T>,
    solver_factory: Box<SatSolverFactoryFn>,
}

impl<'a, T> StableSemanticsSolver<'a, T>
where
    T: LabelType,
{
    /// Builds a new SAT based solver for the stable semantics.
    ///
    /// The underlying SAT solver is one returned by [default_solver](crate::sat::default_solver).
    pub fn new(af: &'a AAFramework<T>) -> Self {
        Self::new_with_sat_solver_factory(af, Box::new(|| sat::default_solver()))
    }

    /// Builds a new SAT based solver for the stable semantics.
    ///
    /// The SAT solver to use in given through the solver factory.
    pub fn new_with_sat_solver_factory(
        af: &'a AAFramework<T>,
        solver_factory: Box<SatSolverFactoryFn>,
    ) -> Self {
        Self { af, solver_factory }
    }

    fn acceptance_with_model(
        &mut self,
        arg: &Argument<T>,
        assumption_polarity: bool,
        status_on_unsat: bool,
    ) -> (bool, Option<Vec<&Argument<T>>>) {
        let mut merged = Vec::new();
        for cc_af in ConnectedComponentsComputer::iter_connected_components(self.af) {
            let mut solver = (self.solver_factory)();
            encode(&cc_af, solver.as_mut());
            match cc_af.argument_set().get_argument(arg.label()) {
                Ok(cc_arg) => {
                    let mut assumption_lit =
                        Literal::from(arg_id_to_solver_var(cc_arg.id()) as isize);
                    if !assumption_polarity {
                        assumption_lit = assumption_lit.negate()
                    }
                    match solver
                        .solve_under_assumptions(&[assumption_lit])
                        .unwrap_model()
                    {
                        Some(assignment) => {
                            let mut local_ext = cc_assignment_to_init_af_extension(
                                assignment,
                                &cc_af,
                                self.af,
                                |i| Some(arg_id_from_solver_var(i)),
                            );
                            merged.append(&mut local_ext)
                        }
                        None => return (status_on_unsat, None),
                    }
                }
                Err(_) => match solver.solve().unwrap_model() {
                    Some(assignment) => {
                        merged.append(&mut cc_assignment_to_init_af_extension(
                            assignment,
                            &cc_af,
                            self.af,
                            |i| Some(arg_id_from_solver_var(i)),
                        ));
                    }
                    None => return (status_on_unsat, None),
                },
            }
        }
        (!status_on_unsat, Some(merged))
    }
}

fn encode<T>(af: &AAFramework<T>, solver: &mut dyn SatSolver)
where
    T: LabelType,
{
    af.argument_set().iter().for_each(|arg| {
        let attacked_id = arg.id();
        let attacked_solver_var = arg_id_to_solver_var(attacked_id) as isize;
        let mut full_cl = clause![attacked_solver_var];
        af.iter_attacks_to(arg).for_each(|att| {
            let attacker_id = att.attacker().id();
            if attacked_id == attacker_id {
                solver.add_clause(clause![-attacked_solver_var])
            } else {
                let attacker_solver_var = arg_id_to_solver_var(attacker_id) as isize;
                solver.add_clause(clause![-attacked_solver_var, -attacker_solver_var]);
                full_cl.push(attacker_solver_var.into());
            }
        });
        solver.add_clause(full_cl);
    });
}

impl<T> SingleExtensionComputer<T> for StableSemanticsSolver<'_, T>
where
    T: LabelType,
{
    fn compute_one_extension(&mut self) -> Option<Vec<&Argument<T>>> {
        let mut merged = Vec::new();
        for cc_af in ConnectedComponentsComputer::iter_connected_components(self.af) {
            let mut solver = (self.solver_factory)();
            encode(&cc_af, solver.as_mut());
            match solver.solve().unwrap_model() {
                Some(assignment) => {
                    merged.append(&mut cc_assignment_to_init_af_extension(
                        assignment,
                        &cc_af,
                        self.af,
                        |i| Some(arg_id_from_solver_var(i)),
                    ));
                }
                None => return None,
            }
        }
        Some(merged)
    }
}

impl<T> CredulousAcceptanceComputer<T> for StableSemanticsSolver<'_, T>
where
    T: LabelType,
{
    fn is_credulously_accepted(&mut self, arg: &Argument<T>) -> bool {
        self.is_credulously_accepted_with_certificate(arg).0
    }

    fn is_credulously_accepted_with_certificate(
        &mut self,
        arg: &Argument<T>,
    ) -> (bool, Option<Vec<&Argument<T>>>) {
        self.acceptance_with_model(arg, true, false)
    }
}

impl<T> SkepticalAcceptanceComputer<T> for StableSemanticsSolver<'_, T>
where
    T: LabelType,
{
    fn is_skeptically_accepted(&mut self, arg: &Argument<T>) -> bool {
        self.is_skeptically_accepted_with_certificate(arg).0
    }

    fn is_skeptically_accepted_with_certificate(
        &mut self,
        arg: &Argument<T>,
    ) -> (bool, Option<Vec<&Argument<T>>>) {
        self.acceptance_with_model(arg, false, true)
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
    use crate::io::{AspartixReader, InstanceReader};

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
    fn test_certificates() {
        let instance = r#"
        arg(a0).
        arg(a1).
        att(a0,a1).
        "#;
        let reader = AspartixReader::default();
        let af = reader.read(&mut instance.as_bytes()).unwrap();
        let mut solver = StableSemanticsSolver::new(&af);
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
        assert_eq!(
            &["a0"],
            solver
                .is_skeptically_accepted_with_certificate(
                    af.argument_set().get_argument(&"a1".to_string()).unwrap()
                )
                .1
                .unwrap()
                .iter()
                .map(|a| a.label())
                .cloned()
                .collect::<Vec<String>>()
                .as_slice()
        )
    }

    #[test]
    fn test_certificates_connected_components() {
        let instance = r#"
        arg(a0).
        arg(a1).
        arg(a2).
        att(a0,a1).
        "#;
        let reader = AspartixReader::default();
        let af = reader.read(&mut instance.as_bytes()).unwrap();
        let mut solver = StableSemanticsSolver::new(&af);
        assert_eq!(
            &["a0", "a2"],
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
        assert_eq!(
            &["a0", "a2"],
            solver
                .is_skeptically_accepted_with_certificate(
                    af.argument_set().get_argument(&"a1".to_string()).unwrap()
                )
                .1
                .unwrap()
                .iter()
                .map(|a| a.label())
                .cloned()
                .collect::<Vec<String>>()
                .as_slice()
        )
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

    #[test]
    fn test_acceptance_connected_components_shortcut() {
        let instance = r#"
        arg(a0).
        arg(a1). 
        arg(a2).
        att(a0,a1).
        att(a1,a0).
        att(a2,a2).
        "#;
        let reader = AspartixReader::default();
        let af = reader.read(&mut instance.as_bytes()).unwrap();
        let mut solver = StableSemanticsSolver::new(&af);
        assert!(!solver
            .is_credulously_accepted(af.argument_set().get_argument(&"a0".to_string()).unwrap()));
        assert!(!solver
            .is_credulously_accepted(af.argument_set().get_argument(&"a1".to_string()).unwrap()));
        assert!(solver
            .is_skeptically_accepted(af.argument_set().get_argument(&"a0".to_string()).unwrap()));
        assert!(solver
            .is_skeptically_accepted(af.argument_set().get_argument(&"a1".to_string()).unwrap()));
    }
}
