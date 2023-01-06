use super::specs::CredulousAcceptanceComputer;
use crate::aa::{AAFramework, Argument};
use crate::encodings::{ConstraintsEncoder, DefaultCompleteConstraintsEncoder};
use crate::utils::LabelType;
use crate::{
    sat::{self, SatSolverFactoryFn},
    utils::ConnectedComponentsComputer,
};

/// A SAT-based solver for the complete semantics.
///
/// A definition of the complete extensions of an Argumentation Framework is given in the [tracks definition](https://iccma2023.github.io/tracks.html) of ICCMA'23 competition.
///
/// A special case of complete extension is the grounded extension.
/// Thus, this solver does not provides function to compute an extension or to check the skeptical acceptance
/// of an argument as they can be computed in an efficient way by a [GroundedSemanticsSolver](super::GroundedSemanticsSolver).
///
/// The implementation of the [CredulousAcceptanceComputer] problems relies on a single call to a SAT solver.
/// The certificate provided in case an argument is credulously accepted is a complete extension containing the argument.
pub struct CompleteSemanticsSolver<'a, T>
where
    T: LabelType,
{
    af: &'a AAFramework<T>,
    solver_factory: Box<SatSolverFactoryFn>,
    constraints_encoder: Box<dyn ConstraintsEncoder<T>>,
}

impl<'a, T> CompleteSemanticsSolver<'a, T>
where
    T: LabelType,
{
    /// Builds a new SAT based solver for the complete semantics.
    ///
    /// The underlying SAT solver is one returned by [default_solver](crate::sat::default_solver).
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::aa::{AAFramework, Argument, ArgumentSet};
    /// # use crustabri::utils::LabelType;
    /// # use crustabri::solvers::{CredulousAcceptanceComputer, CompleteSemanticsSolver};
    /// fn check_credulous_acceptance<T>(af: &AAFramework<T>, arg: &T) where T: LabelType {
    ///     let mut solver = CompleteSemanticsSolver::new(af);
    ///     if solver.is_credulously_accepted(arg) {
    ///         println!("there exists complete extension(s) with {}", arg)
    ///     } else {
    ///         println!("there is no complete extension with {}", arg)
    ///     }
    /// }
    /// # let arg_set = ArgumentSet::new_with_labels(&["a"]);
    /// # let af = AAFramework::new_with_argument_set(arg_set);
    /// # check_credulous_acceptance(&af, &"a");
    pub fn new(af: &'a AAFramework<T>) -> Self
    where
        T: LabelType,
    {
        Self::new_with_sat_solver_factory(af, Box::new(|| sat::default_solver()))
    }

    /// Builds a new SAT based solver for the complete semantics.
    ///
    /// The SAT solver to use in given through the solver factory.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::aa::{AAFramework, Argument, ArgumentSet};
    /// # use crustabri::utils::LabelType;
    /// # use crustabri::sat::CadicalSolver;
    /// # use crustabri::solvers::{CredulousAcceptanceComputer, CompleteSemanticsSolver};
    /// fn check_credulous_acceptance<T>(af: &AAFramework<T>, arg: &T) where T: LabelType {
    ///     let mut solver = CompleteSemanticsSolver::new_with_sat_solver_factory(
    ///         af,
    ///         Box::new(|| Box::new(CadicalSolver::default())),
    ///     );
    ///     if solver.is_credulously_accepted(arg) {
    ///         println!("there exists complete extension(s) with {}", arg)
    ///     } else {
    ///         println!("there is no complete extension with {}", arg)
    ///     }
    /// }
    /// # let arg_set = ArgumentSet::new_with_labels(&["a"]);
    /// # let af = AAFramework::new_with_argument_set(arg_set);
    /// # check_credulous_acceptance(&af, &"a");
    pub fn new_with_sat_solver_factory(
        af: &'a AAFramework<T>,
        solver_factory: Box<SatSolverFactoryFn>,
    ) -> Self
    where
        T: LabelType,
    {
        Self {
            af,
            solver_factory,
            constraints_encoder: Box::new(DefaultCompleteConstraintsEncoder::default()),
        }
    }
}

impl<T> CredulousAcceptanceComputer<T> for CompleteSemanticsSolver<'_, T>
where
    T: LabelType,
{
    fn is_credulously_accepted(&mut self, arg: &T) -> bool {
        let arg = self.af.argument_set().get_argument(arg).unwrap();
        let mut solver = (self.solver_factory)();
        let mut cc_computer = ConnectedComponentsComputer::new(self.af);
        let reduced_af = cc_computer.connected_component_of(arg);
        self.constraints_encoder
            .encode_constraints(&reduced_af, solver.as_mut());
        let arg_in_reduced_af = reduced_af.argument_set().get_argument(arg.label()).unwrap();
        solver
            .solve_under_assumptions(&[self.constraints_encoder.arg_to_lit(arg_in_reduced_af)])
            .unwrap_model()
            .is_some()
    }

    fn is_credulously_accepted_with_certificate(
        &mut self,
        arg: &T,
    ) -> (bool, Option<Vec<&Argument<T>>>) {
        let arg = self.af.argument_set().get_argument(arg).unwrap();
        let mut cc_computer = ConnectedComponentsComputer::new(self.af);
        let reduced_af = cc_computer.connected_component_of(arg);
        let mut solver = (self.solver_factory)();
        self.constraints_encoder
            .encode_constraints(&reduced_af, solver.as_mut());
        let arg_in_reduced_af = reduced_af.argument_set().get_argument(arg.label()).unwrap();
        match solver
            .solve_under_assumptions(&[self.constraints_encoder.arg_to_lit(arg_in_reduced_af)])
            .unwrap_model()
        {
            Some(model) => {
                let cc_ext = self
                    .constraints_encoder
                    .assignment_to_extension(&model, &reduced_af);
                let mut merged = cc_ext
                    .iter()
                    .map(|cc_arg| self.af.argument_set().get_argument(cc_arg.label()).unwrap())
                    .collect::<Vec<&Argument<T>>>();
                while let Some(other_cc_af) = cc_computer.next_connected_component() {
                    let other_cc_grounded = other_cc_af.grounded_extension();
                    other_cc_grounded
                        .iter()
                        .map(|a| self.af.argument_set().get_argument(a.label()).unwrap())
                        .for_each(|a| merged.push(a));
                }
                (true, Some(merged))
            }
            None => (false, None),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::io::{AspartixReader, InstanceReader};

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
        assert!(solver.is_credulously_accepted(&"a0".to_string()));
        assert!(!solver.is_credulously_accepted(&"a1".to_string()));
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
        assert!(solver.is_credulously_accepted(&"a0".to_string()));
        assert!(solver.is_credulously_accepted(&"a1".to_string()));
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
        assert!(solver.is_credulously_accepted(&"a0".to_string()));
        assert!(solver.is_credulously_accepted(&"a1".to_string()));
        assert!(solver.is_credulously_accepted(&"a2".to_string()));
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
        assert!(!solver_before.is_credulously_accepted(&"a1".to_string()));
        af.remove_argument(&"a0".to_string()).unwrap();
        let mut solver_after = CompleteSemanticsSolver::new(&af);
        assert!(solver_after.is_credulously_accepted(&"a1".to_string()));
    }

    #[test]
    fn test_certificates() {
        let instance = r#"
        arg(a0).
        arg(a1).
        arg(a2).
        att(a0,a1).
        "#;
        let reader = AspartixReader::default();
        let af = reader.read(&mut instance.as_bytes()).unwrap();
        let mut solver = CompleteSemanticsSolver::new(&af);
        assert_eq!(
            &["a0", "a2"],
            solver
                .is_credulously_accepted_with_certificate(&"a0".to_string())
                .1
                .unwrap()
                .iter()
                .map(|a| a.label())
                .cloned()
                .collect::<Vec<String>>()
                .as_slice()
        );
        assert_eq!(
            (false, None),
            solver.is_credulously_accepted_with_certificate(&"a1".to_string())
        )
    }
}
