use super::specs::CredulousAcceptanceComputer;
use crate::aa::{AAFramework, Argument};
use crate::encodings::{aux_var_constraints_encoder, ConstraintsEncoder};
use crate::sat::Literal;
use crate::utils::{Label, LabelType};
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
    constraints_encoder: Box<dyn ConstraintsEncoder<T> + 'a>,
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
            constraints_encoder: Box::new(aux_var_constraints_encoder::new_for_complete_semantics()),
        }
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
    /// # use crustabri::sat;
    /// # use crustabri::encodings;
    /// # use crustabri::solvers::{CredulousAcceptanceComputer, CompleteSemanticsSolver};
    /// fn check_credulous_acceptance<T>(af: &AAFramework<T>, arg: &T) where T: LabelType {
    ///     let mut solver = CompleteSemanticsSolver::new_with_sat_solver_factory_and_constraints_encoder(
    ///         af,
    ///         Box::new(|| sat::default_solver()),
    ///         encodings::new_default_complete_constraints_encoder(),
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
    pub fn new_with_sat_solver_factory_and_constraints_encoder(
        af: &'a AAFramework<T>,
        solver_factory: Box<SatSolverFactoryFn>,
        constraints_encoder: Box<dyn ConstraintsEncoder<T>>,
    ) -> Self
    where
        T: LabelType,
    {
        Self {
            af,
            solver_factory,
            constraints_encoder,
        }
    }
}

impl<T> CredulousAcceptanceComputer<T> for CompleteSemanticsSolver<'_, T>
where
    T: LabelType,
{
    fn are_credulously_accepted(&mut self, args: &[&T]) -> bool {
        let args = args
            .iter()
            .map(|a| self.af.argument_set().get_argument(a).unwrap())
            .collect::<Vec<&Label<T>>>();
        let mut solver = (self.solver_factory)();
        let mut cc_computer = ConnectedComponentsComputer::new(self.af);
        let reduced_af = cc_computer.merged_connected_components_of(&args);
        self.constraints_encoder
            .encode_constraints(&reduced_af, solver.as_mut());
        let selector = Literal::from(1 + solver.n_vars() as isize);
        let clause = args
            .iter()
            .map(|a| {
                self.constraints_encoder
                    .arg_to_lit(reduced_af.argument_set().get_argument(a.label()).unwrap())
            })
            .chain(std::iter::once(selector.negate()))
            .collect::<Vec<Literal>>();
        solver.add_clause(clause);
        let result = solver
            .solve_under_assumptions(&[selector])
            .unwrap_model()
            .is_some();
        solver.add_clause(vec![selector.negate()]);
        result
    }

    fn are_credulously_accepted_with_certificate(
        &mut self,
        args: &[&T],
    ) -> (bool, Option<Vec<&Argument<T>>>) {
        let args = args
            .iter()
            .map(|a| self.af.argument_set().get_argument(a).unwrap())
            .collect::<Vec<&Label<T>>>();
        let mut cc_computer = ConnectedComponentsComputer::new(self.af);
        let reduced_af = cc_computer.merged_connected_components_of(&args);
        let mut solver = (self.solver_factory)();
        self.constraints_encoder
            .encode_constraints(&reduced_af, solver.as_mut());
        let assumptions = args
            .iter()
            .map(|a| {
                self.constraints_encoder
                    .arg_to_lit(reduced_af.argument_set().get_argument(a.label()).unwrap())
            })
            .collect::<Vec<Literal>>();
        match solver.solve_under_assumptions(&assumptions).unwrap_model() {
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
    use crate::{
        encodings::{exp_constraints_encoder, HybridCompleteConstraintsEncoder},
        io::{AspartixReader, InstanceReader},
    };

    macro_rules! test_for_encoder {
        ($encoder:expr, $suffix:literal) => {
            paste::item! {
    #[test]
    fn [< test_acceptance_1_ $suffix >] () {
        let instance = r#"
        arg(a0).
        arg(a1).
        att(a0,a1).
        "#;
        let reader = AspartixReader::default();
        let af = reader.read(&mut instance.as_bytes()).unwrap();
        let mut solver =
            CompleteSemanticsSolver::new_with_sat_solver_factory_and_constraints_encoder(&af, Box::new(|| sat::default_solver()), Box::new($encoder));
        assert!(solver.is_credulously_accepted(&"a0".to_string()));
        assert!(!solver.is_credulously_accepted(&"a1".to_string()));
    }

    #[test]
    fn [< test_acceptance_2_ $suffix >] () {
        let instance = r#"
        arg(a0).
        arg(a1).
        att(a0,a1).
        att(a1,a0).
        "#;
        let reader = AspartixReader::default();
        let af = reader.read(&mut instance.as_bytes()).unwrap();
        let mut solver =
            CompleteSemanticsSolver::new_with_sat_solver_factory_and_constraints_encoder(&af, Box::new(|| sat::default_solver()), Box::new($encoder));
        assert!(solver.is_credulously_accepted(&"a0".to_string()));
        assert!(solver.is_credulously_accepted(&"a1".to_string()));
    }

    #[test]
    fn [< test_acceptance_3_ $suffix >] () {
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
        let mut solver =
            CompleteSemanticsSolver::new_with_sat_solver_factory_and_constraints_encoder(&af, Box::new(|| sat::default_solver()), Box::new($encoder));
        assert!(solver.is_credulously_accepted(&"a0".to_string()));
        assert!(solver.is_credulously_accepted(&"a1".to_string()));
        assert!(solver.is_credulously_accepted(&"a2".to_string()));
    }

    #[test]
    fn [< test_credulous_acceptance_after_arg_removal_ $suffix >] () {
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
        let mut solver_before =
            CompleteSemanticsSolver::new_with_sat_solver_factory_and_constraints_encoder(&af, Box::new(|| sat::default_solver()), Box::new($encoder));
        assert!(!solver_before.is_credulously_accepted(&"a1".to_string()));
        std::mem::drop(solver_before);
        af.remove_argument(&"a0".to_string()).unwrap();
        let mut solver_after =
            CompleteSemanticsSolver::new_with_sat_solver_factory_and_constraints_encoder(&af, Box::new(|| sat::default_solver()), Box::new($encoder));
        assert!(solver_after.is_credulously_accepted(&"a1".to_string()));
    }

    #[test]
    fn [< test_certificates_ $suffix >] () {
        let instance = r#"
        arg(a0).
        arg(a1).
        arg(a2).
        att(a0,a1).
        "#;
        let reader = AspartixReader::default();
        let af = reader.read(&mut instance.as_bytes()).unwrap();
        let mut solver =
            CompleteSemanticsSolver::new_with_sat_solver_factory_and_constraints_encoder(&af, Box::new(|| sat::default_solver()), Box::new($encoder));
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

    #[test]
    fn [< test_funnel_ $suffix >] () {
        let mut instance = String::new();
        (0..31).for_each(|i| {
            instance.push_str(&format!("arg(a{}).\n", i));
        });
        (0..5).for_each(|i| {
            (0..5).for_each(|j| {
                instance.push_str(&format!("att(a{},a{}).\n", 5*i+j, 25+i));
            });
        });
        (0..5).for_each(|i| {
            instance.push_str(&format!("att(a{},a30).\n", 25+i));
        });
        println!("{}",instance);
        let reader = AspartixReader::default();
        let af = reader.read(&mut instance.as_bytes()).unwrap();
        let mut solver =
            CompleteSemanticsSolver::new_with_sat_solver_factory_and_constraints_encoder(&af, Box::new(|| sat::default_solver()), Box::new($encoder));
        let (status, certificate) = solver.is_credulously_accepted_with_certificate(&"a30".to_string());
        assert!(status);
        let mut actual = certificate.unwrap().iter().map(|l| l.label().clone()).collect::<Vec<String>>();
        actual.sort_unstable();
        let mut expected = (0..25).map(|i| format!("a{}", i)).collect::<Vec<String>>();
        expected.push("a30".to_string());
        expected.sort_unstable();
        assert_eq!(expected, actual);
    }

    #[test]
    fn [< test_disj_credulous_acceptance_ $suffix >] () {
        let instance = r#"
        arg(a0).
        arg(a1).
        arg(a2).
        arg(a3).
        arg(a4).
        att(a0,a1).
        att(a1,a2).
        att(a1,a3).
        att(a2,a3).
        att(a2,a4).
        att(a3,a2).
        att(a3,a4).
        "#;
        let reader = AspartixReader::default();
        let af = reader.read(&mut instance.as_bytes()).unwrap();
        let mut solver =
            CompleteSemanticsSolver::new_with_sat_solver_factory_and_constraints_encoder(&af, Box::new(|| sat::default_solver()), Box::new($encoder));
        assert!(solver.are_credulously_accepted(&[&"a0".to_string(), &"a1".to_string()]));
        assert!(solver.are_credulously_accepted(&[&"a0".to_string(), &"a2".to_string()]));
        assert!(solver.are_credulously_accepted(&[&"a0".to_string(), &"a3".to_string()]));
        assert!(solver.are_credulously_accepted(&[&"a0".to_string(), &"a4".to_string()]));
        assert!(solver.are_credulously_accepted(&[&"a1".to_string(), &"a2".to_string()]));
        assert!(solver.are_credulously_accepted(&[&"a1".to_string(), &"a3".to_string()]));
        assert!(!solver.are_credulously_accepted(&[&"a1".to_string(), &"a4".to_string()]));
        assert!(solver.are_credulously_accepted(&[&"a2".to_string(), &"a3".to_string()]));
        assert!(solver.are_credulously_accepted(&[&"a2".to_string(), &"a4".to_string()]));
        assert!(solver.are_credulously_accepted(&[&"a3".to_string(), &"a4".to_string()]));
    }
    }
    };
    }

    test_for_encoder!(
        aux_var_constraints_encoder::new_for_complete_semantics(),
        "auxvar"
    );
    test_for_encoder!(exp_constraints_encoder::new_for_complete_semantics(), "exp");
    test_for_encoder!(HybridCompleteConstraintsEncoder::default(), "hybrid");
}
