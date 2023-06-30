use super::{
    maximal_extension_computer::{self, MaximalExtensionComputerState},
    SingleExtensionComputer, SkepticalAcceptanceComputer,
};
use crate::{
    aa::{AAFramework, Argument},
    encodings::{aux_var_constraints_encoder, ConstraintsEncoder},
    sat::{self, SatSolver, SatSolverFactoryFn},
    utils::{ConnectedComponentsComputer, Label, LabelType},
};
use std::{cell::RefCell, rc::Rc};

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
            constraints_encoder: Box::new(aux_var_constraints_encoder::new_for_complete_semantics()),
        }
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
    /// # use crustabri::sat;
    /// # use crustabri::encodings;
    /// # use crustabri::solvers::{SingleExtensionComputer, PreferredSemanticsSolver};
    /// fn search_one_extension<T>(af: &AAFramework<T>) where T: LabelType {
    ///     let mut solver = PreferredSemanticsSolver::new_with_sat_solver_factory_and_constraints_encoder(
    ///         af,
    ///         Box::new(|| sat::default_solver()),
    ///         encodings::new_default_complete_constraints_encoder(),
    ///     );
    ///     let ext = solver.compute_one_extension().unwrap();
    ///     println!("found a preferred extension: {:?}", ext);
    /// }
    /// # search_one_extension::<usize>(&AAFramework::default());
    /// ```
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

    fn is_skeptically_accepted_in_cc<'b>(
        &self,
        cc_af: &'b AAFramework<T>,
        args: &[&'a Argument<T>],
        allow_shortcut: bool,
    ) -> (bool, Option<Vec<&'b Argument<T>>>) {
        let cc_args = args
            .iter()
            .map(|a| cc_af.argument_set().get_argument(a.label()).unwrap())
            .collect::<Vec<&Label<T>>>();
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
                    if !cc_args
                        .iter()
                        .any(|cc_arg| computer.current().contains(cc_arg))
                    {
                        return (false, Some(computer.take_current()));
                    }
                }
                MaximalExtensionComputerState::Intermediate => {
                    let current = computer.current();
                    if cc_args
                        .iter()
                        .any(|cc_arg: &&Label<T>| current.contains(cc_arg))
                    {
                        computer.discard_current_search();
                    } else if allow_shortcut
                        && cc_args.iter().all(|cc_arg| {
                            cc_af
                                .iter_attacks_to(cc_arg)
                                .any(|att| current.contains(&att.attacker()))
                        })
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
    fn are_skeptically_accepted(&mut self, args: &[&T]) -> bool {
        let args = args
            .iter()
            .map(|a| self.af.argument_set().get_argument(a).unwrap())
            .collect::<Vec<&Label<T>>>();
        let mut cc_computer = ConnectedComponentsComputer::new(self.af);
        let cc_af = cc_computer.merged_connected_components_of(&args);
        self.is_skeptically_accepted_in_cc(&cc_af, &args, true).0
    }

    fn are_skeptically_accepted_with_certificate(
        &mut self,
        args: &[&T],
    ) -> (bool, Option<Vec<&Argument<T>>>) {
        let args = args
            .iter()
            .map(|a| self.af.argument_set().get_argument(a).unwrap())
            .collect::<Vec<&Label<T>>>();
        let mut cc_computer = ConnectedComponentsComputer::new(self.af);
        let cc_af = cc_computer.merged_connected_components_of(&args);
        let mut merged = Vec::new();
        let is_accepted_in_cc = self.is_skeptically_accepted_in_cc(&cc_af, &args, false);
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
    use crate::{
        encodings::{exp_constraints_encoder, HybridCompleteConstraintsEncoder},
        io::{AspartixReader, InstanceReader},
    };

    macro_rules! test_for_encoder {
        ($encoder:expr, $suffix:literal) => {
            paste::item! {
    #[test]
    fn [< test_compute_one_preferred_ext_is_grounded_ $suffix >] () {
        let instance = r#"
        arg(a0).
        arg(a1).
        att(a0,a1).
        "#;
        let reader = AspartixReader::default();
        let af = reader.read(&mut instance.as_bytes()).unwrap();
        let mut solver = PreferredSemanticsSolver::new_with_sat_solver_factory_and_constraints_encoder(&af, Box::new(|| sat::default_solver()), Box::new($encoder));
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
    fn [< test_compute_one_preferred_ext_is_not_grounded_ $suffix >] () {
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
        let mut solver = PreferredSemanticsSolver::new_with_sat_solver_factory_and_constraints_encoder(&af, Box::new(|| sat::default_solver()), Box::new($encoder));
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
    fn [< test_compute_one_preferred_after_arg_removal_ $suffix >] () {
        let instance = r#"
        arg(a0).
        arg(a1).
        "#;
        let reader = AspartixReader::default();
        let mut af = reader.read(&mut instance.as_bytes()).unwrap();
        af.remove_argument(&"a0".to_string()).unwrap();
        let mut solver = PreferredSemanticsSolver::new_with_sat_solver_factory_and_constraints_encoder(&af, Box::new(|| sat::default_solver()), Box::new($encoder));
        let ext = solver.compute_one_extension().unwrap();
        assert_eq!(1, ext.len());
        assert_eq!("a1", ext[0].label());
    }

    #[test]
    fn [< test_certificates_ $suffix >] () {
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
        let mut solver = PreferredSemanticsSolver::new_with_sat_solver_factory_and_constraints_encoder(&af, Box::new(|| sat::default_solver()), Box::new($encoder));
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
    fn [< test_certificates_connected_components_ $suffix >] () {
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
        let mut solver = PreferredSemanticsSolver::new_with_sat_solver_factory_and_constraints_encoder(&af, Box::new(|| sat::default_solver()), Box::new($encoder));
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
    fn [< test_skeptical_acceptance_ $suffix >] () {
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
        let mut solver = PreferredSemanticsSolver::new_with_sat_solver_factory_and_constraints_encoder(&af, Box::new(|| sat::default_solver()), Box::new($encoder));
        assert!(solver.is_skeptically_accepted(&"a0".to_string()));
        assert!(!solver.is_skeptically_accepted(&"a1".to_string()));
        assert!(!solver.is_skeptically_accepted(&"a2".to_string()));
        assert!(!solver.is_skeptically_accepted(&"a3".to_string()));
        assert!(!solver.is_skeptically_accepted(&"a4".to_string()));
        assert!(solver.is_skeptically_accepted(&"a5".to_string()));
    }

    #[test]
    fn [< test_skeptical_acceptance_after_arg_removal_ $suffix >] () {
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
        let mut solver = PreferredSemanticsSolver::new_with_sat_solver_factory_and_constraints_encoder(&af, Box::new(|| sat::default_solver()), Box::new($encoder));
        assert!(solver.is_skeptically_accepted(&"a0".to_string()));
        assert!(!solver.is_skeptically_accepted(&"a1".to_string()));
        assert!(solver.is_skeptically_accepted(&"a4".to_string()));
        assert!(!solver.is_skeptically_accepted(&"a5".to_string()));
    }

    #[test]
    fn [< test_skeptical_acceptance_auto_attack_ $suffix >] () {
        let instance = r#"
        arg(a0).
        att(a0,a0).
        "#;
        let reader = AspartixReader::default();
        let af = reader.read(&mut instance.as_bytes()).unwrap();
        let mut solver = PreferredSemanticsSolver::new_with_sat_solver_factory_and_constraints_encoder(&af, Box::new(|| sat::default_solver()), Box::new($encoder));
        assert!(!solver.is_skeptically_accepted(&"a0".to_string()));
    }

    #[test]
    fn [< test_enumerate_extensions_ $suffix >] () {
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
        let constraints_encoder = $encoder;
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
    fn [< test_allow_ds_shortcut_ $suffix >] () {
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
        let mut solver = PreferredSemanticsSolver::new_with_sat_solver_factory_and_constraints_encoder(&af, Box::new(|| sat::default_solver()), Box::new($encoder));
        let arg1 = &"a1".to_string();
        let (result, certificate) = solver.is_skeptically_accepted_with_certificate(arg1);
        assert!(!result);
        assert_eq!(2, certificate.unwrap().len());
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
        let reader = AspartixReader::default();
        let af = reader.read(&mut instance.as_bytes()).unwrap();
        let mut solver =
            PreferredSemanticsSolver::new_with_sat_solver_factory_and_constraints_encoder(&af, Box::new(|| sat::default_solver()), Box::new($encoder));
        let extension = solver.compute_one_extension().unwrap();
        let mut actual = extension.iter().map(|l| l.label().clone()).collect::<Vec<String>>();
        actual.sort_unstable();
        let mut expected = (0..25).map(|i| format!("a{}", i)).collect::<Vec<String>>();
        expected.push("a30".to_string());
        expected.sort_unstable();
        assert_eq!(expected, actual);
    }

    #[test]
    fn [< test_skeptical_acceptance_with_autoattack_ $suffix >]() {
        let instance = r#"
        arg(a0).
        arg(a1).
        arg(a2).
        arg(a3).
        att(a0,a0).
        att(a0,a1).
        att(a0,a2).
        att(a1,a0).
        att(a2,a3).
        att(a3,a2).
        "#;
        let reader = AspartixReader::default();
        let af = reader.read(&mut instance.as_bytes()).unwrap();
        let mut solver = PreferredSemanticsSolver::new_with_sat_solver_factory_and_constraints_encoder(&af, Box::new(|| sat::default_solver()), Box::new($encoder));
        assert!(!solver.is_skeptically_accepted(&"a0".to_string()));
        assert!(solver.is_skeptically_accepted(&"a1".to_string()));
        assert!(!solver.is_skeptically_accepted(&"a2".to_string()));
        assert!(!solver.is_skeptically_accepted(&"a3".to_string()));
    }

    #[test]
    fn [< test_enumerate_extensions_with_autoattack_ $suffix >] () {
        let instance = r#"
        arg(a0).
        arg(a1).
        arg(a2).
        arg(a3).
        att(a0,a0).
        att(a0,a1).
        att(a0,a2).
        att(a1,a0).
        att(a2,a3).
        att(a3,a2).
        "#;
        let reader = AspartixReader::default();
        let af = reader.read(&mut instance.as_bytes()).unwrap();
        let solver = Rc::new(RefCell::new(sat::default_solver()));
        let mut n_exts = 0;
        let constraints_encoder = $encoder;
        PreferredSemanticsSolver::enumerate_extensions(
            &af,
            solver,
            &constraints_encoder,
            &mut |ext| {
                n_exts += 1;
                let args = ext.iter().map(|a| a.label()).collect::<Vec<&String>>();
                assert!(!args.contains(&&"a0".to_string()));
                assert!(args.contains(&&"a1".to_string()));
                assert!(args.contains(&&"a2".to_string()) ^ args.contains(&&"a3".to_string()));
                true
            },
        );
        assert_eq!(2, n_exts)
    }

    #[test]
    fn [< test_disj_skeptical_acceptance_ $suffix >] () {
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
        let mut solver = PreferredSemanticsSolver::new(&af);
        assert!(solver.are_skeptically_accepted(&[&"a0".to_string(), &"a1".to_string()]));
        assert!(solver.are_skeptically_accepted(&[&"a0".to_string(), &"a2".to_string()]));
        assert!(solver.are_skeptically_accepted(&[&"a0".to_string(), &"a3".to_string()]));
        assert!(solver.are_skeptically_accepted(&[&"a0".to_string(), &"a4".to_string()]));
        assert!(!solver.are_skeptically_accepted(&[&"a1".to_string(), &"a2".to_string()]));
        assert!(!solver.are_skeptically_accepted(&[&"a1".to_string(), &"a3".to_string()]));
        assert!(!solver.are_skeptically_accepted(&[&"a1".to_string(), &"a4".to_string()]));
        assert!(solver.are_skeptically_accepted(&[&"a2".to_string(), &"a3".to_string()]));
        assert!(!solver.are_skeptically_accepted(&[&"a2".to_string(), &"a4".to_string()]));
        assert!(!solver.are_skeptically_accepted(&[&"a3".to_string(), &"a4".to_string()]));
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
