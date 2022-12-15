use super::specs::{
    CredulousAcceptanceComputer, SingleExtensionComputer, SkepticalAcceptanceComputer,
};
use crate::{
    aa::{AAFramework, Argument},
    encodings::{ConstraintsEncoder, DefaultStableConstraintsEncoder},
    sat::{self, SatSolverFactoryFn},
    utils::{ConnectedComponentsComputer, LabelType},
};

/// A SAT-based solver for the stable semantics.
///
/// A definition of the stable extensions of an Argumentation Framework is given in the [tracks definition](https://iccma2023.github.io/tracks.html) of ICCMA'23 competition.
///
/// This solver implements [SingleExtensionComputer] and both [CredulousAcceptanceComputer] and [SkepticalAcceptanceComputer] interfaces.
/// In these three cases, the computation resumes to a single call to a SAT solver.
///
/// When a certificate is needed, a stable extension is given.
/// It contains the argument under consideration when considering credulous acceptance, while it does not contain it while considering skeptical acceptance.
///
pub struct StableSemanticsSolver<'a, T>
where
    T: LabelType,
{
    af: &'a AAFramework<T>,
    solver_factory: Box<SatSolverFactoryFn>,
    constraints_encoder: Box<dyn ConstraintsEncoder<T>>,
}

impl<'a, T> StableSemanticsSolver<'a, T>
where
    T: LabelType,
{
    /// Builds a new SAT based solver for the stable semantics.
    ///
    /// The underlying SAT solver is one returned by [default_solver](crate::sat::default_solver).
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::aa::{AAFramework};
    /// # use crustabri::utils::LabelType;
    /// # use crustabri::solvers::{SingleExtensionComputer, StableSemanticsSolver};
    /// fn search_one_extension<T>(af: &AAFramework<T>) where T: LabelType {
    ///     let mut solver = StableSemanticsSolver::new(af);
    ///     let opt_ext = solver.compute_one_extension();
    ///     if let Some(ext) = opt_ext {
    ///         println!("found an extension: {:?}", ext);
    ///     } else {
    ///         println!("the problem has no stable extension");
    ///     }
    /// }
    /// # search_one_extension::<usize>(&AAFramework::default());
    /// ```
    pub fn new(af: &'a AAFramework<T>) -> Self {
        Self::new_with_sat_solver_factory(af, Box::new(|| sat::default_solver()))
    }

    /// Builds a new SAT based solver for the stable semantics.
    ///
    /// The SAT solver to use in given through the solver factory.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::aa::{AAFramework};
    /// # use crustabri::utils::LabelType;
    /// # use crustabri::sat::CadicalSolver;
    /// # use crustabri::solvers::{SingleExtensionComputer, StableSemanticsSolver};
    /// fn search_one_extension<T>(af: &AAFramework<T>) where T: LabelType {
    ///     let mut solver = StableSemanticsSolver::new_with_sat_solver_factory(
    ///         af,
    ///         Box::new(|| Box::new(CadicalSolver::default())),
    ///     );
    ///     let opt_ext = solver.compute_one_extension();
    ///     if let Some(ext) = opt_ext {
    ///         println!("found an extension: {:?}", ext);
    ///     } else {
    ///         println!("the problem has no stable extension");
    ///     }
    /// }
    /// # search_one_extension::<usize>(&AAFramework::default());
    /// ```
    pub fn new_with_sat_solver_factory(
        af: &'a AAFramework<T>,
        solver_factory: Box<SatSolverFactoryFn>,
    ) -> Self {
        Self {
            af,
            solver_factory,
            constraints_encoder: Box::new(DefaultStableConstraintsEncoder::default()),
        }
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
            self.constraints_encoder
                .encode_constraints(&cc_af, solver.as_mut());
            match cc_af.argument_set().get_argument(arg.label()) {
                Ok(cc_arg) => {
                    let mut assumption_lit = self.constraints_encoder.arg_to_lit(cc_arg);
                    if !assumption_polarity {
                        assumption_lit = assumption_lit.negate()
                    }
                    match solver
                        .solve_under_assumptions(&[assumption_lit])
                        .unwrap_model()
                    {
                        Some(assignment) => {
                            let cc_ext = self
                                .constraints_encoder
                                .assignment_to_extension(&assignment, &cc_af);
                            merged.append(
                                &mut cc_ext
                                    .iter()
                                    .map(|cc_arg| {
                                        self.af.argument_set().get_argument(cc_arg.label()).unwrap()
                                    })
                                    .collect::<Vec<&Argument<T>>>(),
                            );
                        }
                        None => return (status_on_unsat, None),
                    }
                }
                Err(_) => match solver.solve().unwrap_model() {
                    Some(assignment) => {
                        let cc_ext = self
                            .constraints_encoder
                            .assignment_to_extension(&assignment, &cc_af);
                        merged.append(
                            &mut cc_ext
                                .iter()
                                .map(|cc_arg| {
                                    self.af.argument_set().get_argument(cc_arg.label()).unwrap()
                                })
                                .collect::<Vec<&Argument<T>>>(),
                        );
                    }
                    None => return (status_on_unsat, None),
                },
            }
        }
        (!status_on_unsat, Some(merged))
    }
}

impl<T> SingleExtensionComputer<T> for StableSemanticsSolver<'_, T>
where
    T: LabelType,
{
    fn compute_one_extension(&mut self) -> Option<Vec<&Argument<T>>> {
        let mut merged = Vec::new();
        for cc_af in ConnectedComponentsComputer::iter_connected_components(self.af) {
            let mut solver = (self.solver_factory)();
            self.constraints_encoder
                .encode_constraints(&cc_af, solver.as_mut());
            match solver.solve().unwrap_model() {
                Some(assignment) => {
                    let cc_ext = self
                        .constraints_encoder
                        .assignment_to_extension(&assignment, &cc_af);
                    merged.append(
                        &mut cc_ext
                            .iter()
                            .map(|cc_arg| {
                                self.af.argument_set().get_argument(cc_arg.label()).unwrap()
                            })
                            .collect::<Vec<&Argument<T>>>(),
                    );
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
