use std::{cell::RefCell, rc::Rc};

use super::{
    maximal_extension_computer::{self, MaximalExtensionComputerState},
    SingleExtensionComputer, SkepticalAcceptanceComputer,
};
use crate::{
    aa::{AAFramework, Argument},
    encodings::{ConstraintsEncoder, DefaultCompleteConstraintsEncoder},
    sat::{self, SatSolver, SatSolverFactoryFn},
    utils::{ConnectedComponentsComputer, LabelType},
};

/// A SAT-based solver for the preferred semantics.
///
/// This solver does not provides function to check the credulous acceptance
/// of an argument as it can be computed in a more efficient way by a [CompleteSemanticsSolver](super::CompleteSemanticsSolver).
///
/// Concerning the skeptical acceptance and the extension computation, this solver relies on successive calls to a SAT solver making the computation reach the second level of the polynomial hierarchy.
///
/// The certificate provided in case an argument is not skeptically accepted is a preferred extension that does not the argument.
pub struct PreferredSemanticsSolver<'a, T>
where
    T: LabelType,
{
    af: &'a AAFramework<T>,
    solver_factory: Box<SatSolverFactoryFn>,
    constraints_encoder: Box<dyn ConstraintsEncoder<T>>,
}

impl<'a, T> PreferredSemanticsSolver<'a, T>
where
    T: LabelType,
{
    /// Builds a new SAT based solver for the preferred semantics.
    ///
    /// The underlying SAT solver is one returned by [default_solver](crate::sat::default_solver).
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::aa::{AAFramework};
    /// # use crustabri::utils::LabelType;
    /// # use crustabri::solvers::{SingleExtensionComputer, PreferredSemanticsSolver};
    /// fn search_one_extension<T>(af: &AAFramework<T>) where T: LabelType {
    ///     let mut solver = PreferredSemanticsSolver::new(af);
    ///     let ext = solver.compute_one_extension().unwrap();
    ///     println!("found a preferred extension: {:?}", ext);
    /// }
    /// # search_one_extension::<usize>(&AAFramework::default());
    /// ```
    pub fn new(af: &'a AAFramework<T>) -> Self {
        Self::new_with_sat_solver_factory(af, Box::new(|| sat::default_solver()))
    }

    /// Builds a new SAT based solver for the preferred semantics.
    ///
    /// The SAT solver to use in given through the solver factory.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::aa::{AAFramework};
    /// # use crustabri::utils::LabelType;
    /// # use crustabri::sat::CadicalSolver;
    /// # use crustabri::solvers::{SingleExtensionComputer, PreferredSemanticsSolver};
    /// fn search_one_extension<T>(af: &AAFramework<T>) where T: LabelType {
    ///     let mut solver = PreferredSemanticsSolver::new_with_sat_solver_factory(
    ///         af,
    ///         Box::new(|| Box::new(CadicalSolver::default())),
    ///     );
    ///     let ext = solver.compute_one_extension().unwrap();
    ///     println!("found a preferred extension: {:?}", ext);
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
            constraints_encoder: Box::new(DefaultCompleteConstraintsEncoder::default()),
        }
    }

    fn is_skeptically_accepted_in_cc<'b>(
        &self,
        cc_af: &'b AAFramework<T>,
        arg: &'a Argument<T>,
        allow_shortcut: bool,
    ) -> (bool, Option<Vec<&'b Argument<T>>>) {
        let cc_arg = cc_af.argument_set().get_argument(arg.label()).unwrap();
        let solver = Rc::new(RefCell::new((self.solver_factory)()));
        self.constraints_encoder
            .encode_constraints(cc_af, solver.borrow_mut().as_mut());
        let mut computer = maximal_extension_computer::new_for_preferred_semantics(
            cc_af,
            solver,
            self.constraints_encoder.as_ref(),
        );
        loop {
            computer.compute_next();
            match computer.state() {
                MaximalExtensionComputerState::Maximal => {
                    if !computer.current().contains(&cc_arg) {
                        return (false, Some(computer.take_current()));
                    }
                }
                MaximalExtensionComputerState::Intermediate => {
                    let current = computer.current();
                    if current.contains(&cc_arg) {
                        computer.discard_current_search();
                    } else if allow_shortcut
                        && cc_af
                            .iter_attacks_to(cc_arg)
                            .any(|att| current.contains(&att.attacker()))
                    {
                        return (false, Some(computer.take_current()));
                    }
                }
                MaximalExtensionComputerState::None => return (true, None),
                _ => {}
            }
        }
    }

    pub(crate) fn enumerate_extensions(
        af: &AAFramework<T>,
        solver: Rc<RefCell<Box<dyn SatSolver>>>,
        constraints_encoder: &dyn ConstraintsEncoder<T>,
        callback: &mut dyn FnMut(&[&Argument<T>]) -> bool,
    ) {
        constraints_encoder.encode_constraints(af, solver.borrow_mut().as_mut());
        let mut computer = maximal_extension_computer::new_for_preferred_semantics(
            af,
            solver,
            constraints_encoder,
        );
        loop {
            computer.compute_next();
            match computer.state() {
                MaximalExtensionComputerState::Maximal => {
                    if !callback(computer.current()) {
                        break;
                    }
                }
                MaximalExtensionComputerState::None => break,
                _ => {}
            }
        }
        std::mem::drop(computer);
    }
}

impl<T> SingleExtensionComputer<T> for PreferredSemanticsSolver<'_, T>
where
    T: LabelType,
{
    fn compute_one_extension(&mut self) -> Option<Vec<&Argument<T>>> {
        let mut merged = Vec::new();
        for cc_af in ConnectedComponentsComputer::iter_connected_components(self.af) {
            let solver = Rc::new(RefCell::new((self.solver_factory)()));
            self.constraints_encoder
                .encode_constraints(&cc_af, solver.borrow_mut().as_mut());
            let computer = maximal_extension_computer::new_for_preferred_semantics(
                &cc_af,
                solver,
                self.constraints_encoder.as_ref(),
            );
            for cc_arg in computer.compute_maximal() {
                merged.push(self.af.argument_set().get_argument(cc_arg.label()).unwrap())
            }
        }
        Some(merged)
    }
}

impl<T> SkepticalAcceptanceComputer<T> for PreferredSemanticsSolver<'_, T>
where
    T: LabelType,
{
    fn is_skeptically_accepted(&mut self, arg: &T) -> bool {
        let arg = self.af.argument_set().get_argument(arg).unwrap();
        let mut cc_computer = ConnectedComponentsComputer::new(self.af);
        let cc_af = cc_computer.connected_component_of(arg);
        self.is_skeptically_accepted_in_cc(&cc_af, arg, true).0
    }

    fn is_skeptically_accepted_with_certificate(
        &mut self,
        arg: &T,
    ) -> (bool, Option<Vec<&Argument<T>>>) {
        let arg = self.af.argument_set().get_argument(arg).unwrap();
        let mut cc_computer = ConnectedComponentsComputer::new(self.af);
        let cc_af = cc_computer.connected_component_of(arg);
        let mut merged = Vec::new();
        let is_accepted_in_cc = self.is_skeptically_accepted_in_cc(&cc_af, arg, false);
        match is_accepted_in_cc {
            (true, None) => return (true, None),
            (false, Some(cc_ext)) => {
                cc_ext
                    .iter()
                    .map(|a| self.af.argument_set().get_argument(a.label()).unwrap())
                    .for_each(|a| merged.push(a));
            }
            _ => unreachable!(),
        }
        while let Some(other_cc_af) = cc_computer.next_connected_component() {
            let solver = Rc::new(RefCell::new((self.solver_factory)()));
            self.constraints_encoder
                .encode_constraints(&other_cc_af, solver.borrow_mut().as_mut());
            let computer = maximal_extension_computer::new_for_preferred_semantics(
                &other_cc_af,
                solver,
                self.constraints_encoder.as_ref(),
            );
            for cc_arg in computer.compute_maximal() {
                merged.push(self.af.argument_set().get_argument(cc_arg.label()).unwrap())
            }
        }
        (false, Some(merged))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::io::{AspartixReader, InstanceReader};

    #[test]
    fn test_compute_one_preferred_ext_is_grounded() {
        let instance = r#"
        arg(a0).
        arg(a1).
        att(a0,a1).
        "#;
        let reader = AspartixReader::default();
        let af = reader.read(&mut instance.as_bytes()).unwrap();
        let mut solver = PreferredSemanticsSolver::new(&af);
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
    fn test_compute_one_preferred_ext_is_not_grounded() {
        let instance = r#"
        arg(a0).
        arg(a1).
        arg(a2).
        arg(a3).
        arg(a4).
        arg(a5).
        att(a0,a1).
        att(a1,a2).
        att(a1,a3).
        att(a2,a3).
        att(a2,a4).
        att(a3,a2).
        att(a3,a4).
        att(a4,a5).
        "#;
        let reader = AspartixReader::default();
        let af = reader.read(&mut instance.as_bytes()).unwrap();
        let mut solver = PreferredSemanticsSolver::new(&af);
        let args = solver
            .compute_one_extension()
            .unwrap()
            .iter()
            .map(|arg| arg.label().to_string())
            .collect::<Vec<String>>();
        assert!(args.contains(&"a0".to_string()));
        assert!(!args.contains(&"a1".to_string()));
        assert!(args.contains(&"a2".to_string()) ^ args.contains(&"a3".to_string()));
        assert!(!args.contains(&"a4".to_string()));
        assert!(args.contains(&"a5".to_string()));
    }

    #[test]
    fn test_compute_one_preferred_after_arg_removal() {
        let instance = r#"
        arg(a0).
        arg(a1).
        "#;
        let reader = AspartixReader::default();
        let mut af = reader.read(&mut instance.as_bytes()).unwrap();
        af.remove_argument(&"a0".to_string()).unwrap();
        let mut solver = PreferredSemanticsSolver::new(&af);
        let ext = solver.compute_one_extension().unwrap();
        assert_eq!(1, ext.len());
        assert_eq!("a1", ext[0].label());
    }

    #[test]
    fn test_certificates() {
        let instance = r#"
        arg(a0).
        arg(a1).
        arg(a2).
        arg(a3).
        arg(a4).
        arg(a5).
        att(a0,a1).
        att(a1,a2).
        att(a1,a3).
        att(a2,a3).
        att(a2,a4).
        att(a3,a2).
        att(a3,a4).
        att(a4,a5).
        "#;
        let reader = AspartixReader::default();
        let af = reader.read(&mut instance.as_bytes()).unwrap();
        let mut solver = PreferredSemanticsSolver::new(&af);
        let mut cert = solver
            .is_skeptically_accepted_with_certificate(&"a2".to_string())
            .1
            .unwrap()
            .iter()
            .map(|a| a.label())
            .cloned()
            .collect::<Vec<String>>();
        cert.sort_unstable();
        assert!(["a0", "a2", "a5"] == cert.as_slice() || ["a0", "a3", "a5"] == cert.as_slice())
    }

    #[test]
    fn test_certificates_connected_components() {
        let instance = r#"
        arg(a0).
        arg(a2).
        arg(a3).
        arg(a4).
        arg(a5).
        att(a2,a3).
        att(a2,a4).
        att(a3,a2).
        att(a3,a4).
        att(a4,a5).
        "#;
        let reader = AspartixReader::default();
        let af = reader.read(&mut instance.as_bytes()).unwrap();
        let mut solver = PreferredSemanticsSolver::new(&af);
        let mut cert = solver
            .is_skeptically_accepted_with_certificate(&"a2".to_string())
            .1
            .unwrap()
            .iter()
            .map(|a| a.label())
            .cloned()
            .collect::<Vec<String>>();
        cert.sort_unstable();
        assert!(["a0", "a2", "a5"] == cert.as_slice() || ["a0", "a3", "a5"] == cert.as_slice());
        assert_eq!(
            (true, None),
            solver.is_skeptically_accepted_with_certificate(&"a0".to_string(),)
        );
    }

    #[test]
    fn test_skeptical_acceptance() {
        let instance = r#"
        arg(a0).
        arg(a1).
        arg(a2).
        arg(a3).
        arg(a4).
        arg(a5).
        att(a0,a1).
        att(a1,a2).
        att(a1,a3).
        att(a2,a3).
        att(a2,a4).
        att(a3,a2).
        att(a3,a4).
        att(a4,a5).
        "#;
        let reader = AspartixReader::default();
        let af = reader.read(&mut instance.as_bytes()).unwrap();
        let mut solver = PreferredSemanticsSolver::new(&af);
        assert!(solver.is_skeptically_accepted(&"a0".to_string()));
        assert!(!solver.is_skeptically_accepted(&"a1".to_string()));
        assert!(!solver.is_skeptically_accepted(&"a2".to_string()));
        assert!(!solver.is_skeptically_accepted(&"a3".to_string()));
        assert!(!solver.is_skeptically_accepted(&"a4".to_string()));
        assert!(solver.is_skeptically_accepted(&"a5".to_string()));
    }

    #[test]
    fn test_skeptical_acceptance_after_arg_removal() {
        let instance = r#"
        arg(a0).
        arg(a1).
        arg(a2).
        arg(a3).
        arg(a4).
        arg(a5).
        att(a0,a1).
        att(a1,a2).
        att(a1,a3).
        att(a2,a3).
        att(a2,a4).
        att(a3,a2).
        att(a3,a4).
        att(a4,a5).
        "#;
        let reader = AspartixReader::default();
        let mut af = reader.read(&mut instance.as_bytes()).unwrap();
        af.remove_argument(&"a2".to_string()).unwrap();
        af.remove_argument(&"a3".to_string()).unwrap();
        let mut solver = PreferredSemanticsSolver::new(&af);
        assert!(solver.is_skeptically_accepted(&"a0".to_string()));
        assert!(!solver.is_skeptically_accepted(&"a1".to_string()));
        assert!(solver.is_skeptically_accepted(&"a4".to_string()));
        assert!(!solver.is_skeptically_accepted(&"a5".to_string()));
    }

    #[test]
    fn test_skeptical_acceptance_auto_attack() {
        let instance = r#"
        arg(a0).
        att(a0,a0).
        "#;
        let reader = AspartixReader::default();
        let af = reader.read(&mut instance.as_bytes()).unwrap();
        let mut solver = PreferredSemanticsSolver::new(&af);
        assert!(!solver.is_skeptically_accepted(&"a0".to_string()));
    }

    #[test]
    fn test_enumerate_extensions() {
        let instance = r#"
        arg(a0).
        arg(a1).
        arg(a2).
        arg(a3).
        att(a0,a1).
        att(a0,a2).
        att(a1,a0).
        att(a1,a2).
        att(a2,a3).
        att(a3,a2).
        "#;
        let reader = AspartixReader::default();
        let af = reader.read(&mut instance.as_bytes()).unwrap();
        let solver = Rc::new(RefCell::new(sat::default_solver()));
        let mut n_exts = 0;
        let constraints_encoder = DefaultCompleteConstraintsEncoder::default();
        PreferredSemanticsSolver::enumerate_extensions(
            &af,
            solver,
            &constraints_encoder,
            &mut |ext| {
                n_exts += 1;
                let args = ext.iter().map(|a| a.label()).collect::<Vec<&String>>();
                assert!(args.contains(&&"a0".to_string()) ^ args.contains(&&"a1".to_string()));
                assert!(!args.contains(&&"a2".to_string()));
                assert!(args.contains(&&"a3".to_string()));
                true
            },
        );
        assert_eq!(2, n_exts)
    }

    #[test]
    fn test_allow_ds_shortcut() {
        let instance = r#"
        arg(a0).
        arg(a1).
        arg(a2).
        arg(a3).
        att(a0,a1).
        att(a1,a2).
        att(a1,a3).
        att(a2,a3).
        att(a3,a2).
        "#;
        let reader = AspartixReader::default();
        let af = reader.read(&mut instance.as_bytes()).unwrap();
        let mut solver = PreferredSemanticsSolver::new(&af);
        let arg1 = &"a1".to_string();
        let (result, certificate) = solver.is_skeptically_accepted_with_certificate(arg1);
        assert!(!result);
        assert_eq!(2, certificate.unwrap().len());
    }
}
