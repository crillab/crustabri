use super::{
    complete_semantics_solver,
    maximal_extension_computer::{MaximalExtensionComputer, MaximalExtensionComputerState},
    utils::{self},
    SingleExtensionComputer, SkepticalAcceptanceComputer,
};
use crate::{
    aa::{AAFramework, Argument, LabelType},
    sat::{self, Literal, SatSolver, SatSolverFactoryFn},
    utils::ConnectedComponentsComputer,
};

/// A SAT-based solver for the preferred semantics.
///
/// This solver does not provides function to check the credulous acceptance
/// of an argument as it can be computed in a more efficient way by a [CompleteSemanticsSolver](super::CompleteSemanticsSolver).
///
/// Concerning the skeptical acceptance and the extension computation, this solver relies on successive calls to a SAT solver making the computation reach the second level of the polynomial hierarchy.
///
/// The certificates for the skeptical acceptance may be of two kinds:
///   * a preferred extension that does not contain the argument under consideration;
///   * or an admissible set of argument that attacks the argument under consideration.
///
/// In order to know which kind of certificate is provided, the caller must check if any of the attacks to the argument under consideration comes from an argument in the certificate.
pub struct PreferredSemanticsSolver<'a, T>
where
    T: LabelType,
{
    af: &'a AAFramework<T>,
    solver_factory: Box<SatSolverFactoryFn>,
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
    /// # use crustabri::aa::{AAFramework, LabelType};
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
    /// # use crustabri::aa::{AAFramework, LabelType};
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
        Self { af, solver_factory }
    }

    fn is_skeptically_accepted_in_cc<'b>(
        &self,
        cc_af: &'b AAFramework<T>,
        arg: &'a Argument<T>,
    ) -> (bool, Option<Vec<&'b Argument<T>>>) {
        let cc_arg = cc_af.argument_set().get_argument(arg.label()).unwrap();
        let mut solver = (self.solver_factory)();
        complete_semantics_solver::encode_complete_semantics_constraints(cc_af, solver.as_mut());
        let mut computer = new_maximal_extension_computer(cc_af, solver.as_mut());
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
                    } else if cc_af
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
        solver: &mut dyn SatSolver,
        callback: &mut dyn FnMut(&[&Argument<T>]) -> bool,
    ) {
        complete_semantics_solver::encode_complete_semantics_constraints(af, solver);
        let mut computer = new_maximal_extension_computer(af, solver);
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
    }
}

fn new_maximal_extension_computer<'a, 'b, T>(
    cc_af: &'a AAFramework<T>,
    solver: &'b mut dyn SatSolver,
) -> MaximalExtensionComputer<'a, 'b, T>
where
    T: LabelType,
{
    let mut computer = MaximalExtensionComputer::new(cc_af, solver);
    computer.set_increase_current_fn(Box::new(|fn_data| {
        let (mut in_ext, mut not_in_ext) =
            split_in_extension(fn_data.current_arg_set, fn_data.af.n_arguments());
        not_in_ext.push(fn_data.selector);
        in_ext.push(fn_data.selector.negate());
        fn_data.sat_solver.add_clause(not_in_ext);
        in_ext
    }));
    computer.set_discard_current_fn(Box::new(|fn_data| {
        let (mut in_ext, _) = split_in_extension(fn_data.current_arg_set, fn_data.af.n_arguments());
        in_ext.iter_mut().for_each(|l| *l = l.negate());
        in_ext.push(fn_data.selector);
        fn_data.sat_solver.add_clause(in_ext);
    }));
    computer.set_discard_maximal_fn(Box::new(|fn_data| {
        let (_, mut not_in_ext) =
            split_in_extension(fn_data.current_arg_set, fn_data.af.n_arguments());
        not_in_ext.push(fn_data.selector);
        fn_data.sat_solver.add_clause(not_in_ext);
    }));
    computer
}

pub(crate) fn split_in_extension<T>(
    current: &[&Argument<T>],
    n_args: usize,
) -> (Vec<Literal>, Vec<Literal>)
where
    T: LabelType,
{
    let mut in_ext_bool = vec![false; n_args];
    current.iter().for_each(|a| in_ext_bool[a.id()] = true);
    let mut not_in_ext = Vec::with_capacity(n_args);
    let mut in_ext = Vec::with_capacity(n_args);
    in_ext_bool.iter().enumerate().for_each(|(i, b)| {
        let lit = Literal::from(complete_semantics_solver::arg_id_to_solver_var(i) as isize);
        match *b {
            true => in_ext.push(lit),
            false => not_in_ext.push(lit),
        }
    });
    (in_ext, not_in_ext)
}

impl<T> SingleExtensionComputer<T> for PreferredSemanticsSolver<'_, T>
where
    T: LabelType,
{
    fn compute_one_extension(&mut self) -> Option<Vec<&Argument<T>>> {
        let mut merged = Vec::new();
        for cc_af in ConnectedComponentsComputer::iter_connected_components(self.af) {
            let mut solver = (self.solver_factory)();
            complete_semantics_solver::encode_complete_semantics_constraints(
                &cc_af,
                solver.as_mut(),
            );
            let computer = new_maximal_extension_computer(&cc_af, solver.as_mut());
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
    fn is_skeptically_accepted(&mut self, arg: &Argument<T>) -> bool {
        let mut cc_computer = ConnectedComponentsComputer::new(self.af);
        let cc_af = cc_computer.connected_component_of(arg);
        self.is_skeptically_accepted_in_cc(&cc_af, arg).0
    }

    fn is_skeptically_accepted_with_certificate(
        &mut self,
        arg: &Argument<T>,
    ) -> (bool, Option<Vec<&Argument<T>>>) {
        let mut cc_computer = ConnectedComponentsComputer::new(self.af);
        let cc_af = cc_computer.connected_component_of(arg);
        let mut merged = Vec::new();
        match self.is_skeptically_accepted_in_cc(&cc_af, arg) {
            (true, None) => return (true, None),
            (false, Some(cc_ext)) => {
                cc_ext
                    .iter()
                    .map(|a| utils::cc_arg_to_init_af_arg(a, self.af))
                    .for_each(|a| merged.push(a));
            }
            _ => unreachable!(),
        }
        while let Some(other_cc_af) = cc_computer.next_connected_component() {
            let mut solver = (self.solver_factory)();
            complete_semantics_solver::encode_complete_semantics_constraints(
                &other_cc_af,
                solver.as_mut(),
            );
            let computer = new_maximal_extension_computer(&other_cc_af, solver.as_mut());
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
            .is_skeptically_accepted_with_certificate(
                af.argument_set().get_argument(&"a2".to_string()).unwrap(),
            )
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
            .is_skeptically_accepted_with_certificate(
                af.argument_set().get_argument(&"a2".to_string()).unwrap(),
            )
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
            solver.is_skeptically_accepted_with_certificate(
                af.argument_set().get_argument(&"a0".to_string()).unwrap(),
            )
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
        assert!(solver
            .is_skeptically_accepted(af.argument_set().get_argument(&"a0".to_string()).unwrap()));
        assert!(!solver
            .is_skeptically_accepted(af.argument_set().get_argument(&"a1".to_string()).unwrap()));
        assert!(!solver
            .is_skeptically_accepted(af.argument_set().get_argument(&"a2".to_string()).unwrap()));
        assert!(!solver
            .is_skeptically_accepted(af.argument_set().get_argument(&"a3".to_string()).unwrap()));
        assert!(!solver
            .is_skeptically_accepted(af.argument_set().get_argument(&"a4".to_string()).unwrap()));
        assert!(solver
            .is_skeptically_accepted(af.argument_set().get_argument(&"a5".to_string()).unwrap()));
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
        assert!(solver
            .is_skeptically_accepted(af.argument_set().get_argument(&"a0".to_string()).unwrap()));
        assert!(!solver
            .is_skeptically_accepted(af.argument_set().get_argument(&"a1".to_string()).unwrap()));
        assert!(solver
            .is_skeptically_accepted(af.argument_set().get_argument(&"a4".to_string()).unwrap()));
        assert!(!solver
            .is_skeptically_accepted(af.argument_set().get_argument(&"a5".to_string()).unwrap()));
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
        assert!(!solver
            .is_skeptically_accepted(af.argument_set().get_argument(&"a0".to_string()).unwrap()));
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
        let mut solver = sat::default_solver();
        let mut n_exts = 0;
        PreferredSemanticsSolver::enumerate_extensions(&af, solver.as_mut(), &mut |ext| {
            n_exts += 1;
            let args = ext.iter().map(|a| a.label()).collect::<Vec<&String>>();
            assert!(args.contains(&&"a0".to_string()) ^ args.contains(&&"a1".to_string()));
            assert!(!args.contains(&&"a2".to_string()));
            assert!(args.contains(&&"a3".to_string()));
            true
        });
        assert_eq!(2, n_exts)
    }
}
