use super::{
    maximal_extension_computer::{self},
    CredulousAcceptanceComputer, PreferredSemanticsSolver, SingleExtensionComputer,
    SkepticalAcceptanceComputer,
};
use crate::{
    aa::{AAFramework, Argument},
    encodings::{aux_var_constraints_encoder, ConstraintsEncoder},
    sat,
    sat::{Literal, SatSolver, SatSolverFactoryFn},
    utils::{self, ConnectedComponentsComputer, Label, LabelType},
};
use std::{cell::RefCell, rc::Rc};

/// A SAT-based solver for the ideal semantics.
///
/// A definition of the ideal semantics is given in the [tracks definition](https://iccma2023.github.io/tracks.html) of ICCMA'23 competition.
///
/// For both acceptance queries and extension computation, this solver relies on successive calls to a SAT solver making the computation reach the second level of the polynomial hierarchy.
///
/// The certificates for the acceptance queries are extensions.
pub struct IdealSemanticsSolver<'a, T>
where
    T: LabelType,
{
    af: &'a AAFramework<T>,
    solver_factory: Box<SatSolverFactoryFn>,
    constraints_encoder: Box<dyn ConstraintsEncoder<T>>,
}

impl<'a, T> IdealSemanticsSolver<'a, T>
where
    T: LabelType,
{
    /// Builds a new SAT based solver for the ideal semantics.
    ///
    /// The underlying SAT solver is one returned by [default_solver](crate::sat::default_solver).
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::aa::{AAFramework};
    /// # use crustabri::utils::LabelType;
    /// # use crustabri::solvers::{SingleExtensionComputer, IdealSemanticsSolver};
    /// fn search_one_extension<T>(af: &AAFramework<T>) where T: LabelType {
    ///     let mut solver = IdealSemanticsSolver::new(af);
    ///     let ext = solver.compute_one_extension().unwrap();
    ///     println!("found the ideal extension: {:?}", ext);
    /// }
    /// # search_one_extension::<usize>(&AAFramework::default());
    /// ```
    pub fn new(af: &'a AAFramework<T>) -> Self {
        Self::new_with_sat_solver_factory(af, Box::new(|| sat::default_solver()))
    }

    /// Builds a new SAT based solver for the ideal semantics.
    ///
    /// The SAT solver to use in given through the solver factory.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::aa::{AAFramework};
    /// # use crustabri::utils::LabelType;
    /// # use crustabri::sat::CadicalSolver;
    /// # use crustabri::solvers::{SingleExtensionComputer, IdealSemanticsSolver};
    /// fn search_one_extension<T>(af: &AAFramework<T>) where T: LabelType {
    ///     let mut solver = IdealSemanticsSolver::new_with_sat_solver_factory(
    ///         af,
    ///         Box::new(|| Box::new(CadicalSolver::default())),
    ///     );
    ///     let ext = solver.compute_one_extension().unwrap();
    ///     println!("found the ideal extension: {:?}", ext);
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

    /// Builds a new SAT based solver for the ideal semantics.
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
    /// # use crustabri::solvers::{SingleExtensionComputer, IdealSemanticsSolver};
    /// fn search_one_extension<T>(af: &AAFramework<T>) where T: LabelType {
    ///     let mut solver = IdealSemanticsSolver::new_with_sat_solver_factory_and_constraints_encoder(
    ///         af,
    ///         Box::new(|| sat::default_solver()),
    ///         encodings::new_default_complete_constraints_encoder(),
    ///     );
    ///     let ext = solver.compute_one_extension().unwrap();
    ///     println!("found the ideal extension: {:?}", ext);
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

    fn compute_one_extension_for_cc<'b>(&self, cc_af: &'b AAFramework<T>) -> Vec<&'b Argument<T>> {
        let grounded = utils::grounded_extension(cc_af);
        let solver = Rc::new(RefCell::new((self.solver_factory)()));
        let (in_all, n_in_all, n_preferred) =
            self.compute_in_all_extensions_for_cc(cc_af, &grounded, Rc::clone(&solver));
        if n_in_all == grounded.len() {
            return grounded;
        }
        if n_preferred == 1 {
            return single_preferred(cc_af, in_all);
        }
        compute_maximal_with_allowed(cc_af, solver, in_all, self.constraints_encoder.as_ref())
    }

    // The number of preferred extensions may be incorrect if n_in_all is equal to the size of the grounded extension.
    fn compute_in_all_extensions_for_cc<'b>(
        &self,
        cc_af: &'b AAFramework<T>,
        grounded: &[&'b Label<T>],
        solver: Rc<RefCell<Box<dyn SatSolver>>>,
    ) -> (Vec<bool>, usize, usize) {
        let mut in_all = vec![true; cc_af.n_arguments()];
        let mut n_in_all = 0;
        let mut n_preferred = 0;
        PreferredSemanticsSolver::enumerate_extensions(
            cc_af,
            Rc::clone(&solver),
            self.constraints_encoder.as_ref(),
            &mut |ext| {
                n_preferred += 1;
                let mut new_in_all = vec![false; cc_af.n_arguments()];
                n_in_all = 0;
                ext.iter().for_each(|a| {
                    if in_all[a.id()] {
                        new_in_all[a.id()] = true;
                        n_in_all += 1;
                    }
                });
                in_all = new_in_all;
                n_in_all != grounded.len()
            },
        );
        (in_all, n_in_all, n_preferred)
    }

    fn check_credulous_acceptance_for_cc<'b>(
        &self,
        cc_af: &'b AAFramework<T>,
        cc_args: &[&'b Argument<T>],
    ) -> (bool, Option<Vec<&'b Argument<T>>>) {
        let grounded = utils::grounded_extension(cc_af);
        let solver = Rc::new(RefCell::new((self.solver_factory)()));
        let (in_all, n_in_all, n_preferred) =
            self.compute_in_all_extensions_for_cc(cc_af, &grounded, Rc::clone(&solver));
        if cc_args.iter().all(|a| !in_all[a.id()]) {
            return (false, None);
        }
        let result = |ext: Vec<&'b Argument<T>>| {
            if cc_args.iter().any(|a| ext.contains(a)) {
                (true, Some(ext))
            } else {
                (false, None)
            }
        };
        if n_in_all == grounded.len() {
            return result(grounded);
        }
        if n_preferred == 1 {
            let ext = single_preferred(cc_af, in_all);
            return result(ext);
        }
        let ideal_ext =
            compute_maximal_with_allowed(cc_af, solver, in_all, self.constraints_encoder.as_ref());
        result(ideal_ext)
    }
}

fn compute_maximal_with_allowed<'a, T>(
    cc_af: &'a AAFramework<T>,
    solver: Rc<RefCell<Box<dyn SatSolver>>>,
    in_all_preferred: Vec<bool>,
    constraints_encoder: &dyn ConstraintsEncoder<T>,
) -> Vec<&'a Argument<T>>
where
    T: LabelType,
{
    let assumptions = in_all_preferred
        .iter()
        .enumerate()
        .filter_map(|(i, b)| match *b {
            true => None,
            false => Some(
                constraints_encoder
                    .arg_to_lit(cc_af.argument_set().get_argument_by_id(i))
                    .negate(),
            ),
        })
        .collect::<Vec<Literal>>();
    let computer = maximal_extension_computer::new_for_ideal_semantics(
        cc_af,
        solver,
        constraints_encoder,
        assumptions,
    );
    computer.compute_maximal()
}

fn single_preferred<T>(cc_af: &AAFramework<T>, in_all_preferred: Vec<bool>) -> Vec<&Argument<T>>
where
    T: LabelType,
{
    in_all_preferred
        .iter()
        .enumerate()
        .filter_map(|(i, b)| {
            if *b {
                Some(cc_af.argument_set().get_argument_by_id(i))
            } else {
                None
            }
        })
        .collect()
}

impl<T> SingleExtensionComputer<T> for IdealSemanticsSolver<'_, T>
where
    T: LabelType,
{
    fn compute_one_extension(&mut self) -> Option<Vec<&Argument<T>>> {
        let mut merged = Vec::new();
        for cc_af in ConnectedComponentsComputer::iter_connected_components(self.af) {
            let mut solver = (self.solver_factory)();
            self.constraints_encoder
                .encode_constraints(&cc_af, solver.as_mut());
            let local_ext = self.compute_one_extension_for_cc(&cc_af);
            for cc_arg in local_ext {
                merged.push(self.af.argument_set().get_argument(cc_arg.label()).unwrap())
            }
        }
        Some(merged)
    }
}

impl<T> CredulousAcceptanceComputer<T> for IdealSemanticsSolver<'_, T>
where
    T: LabelType,
{
    fn are_credulously_accepted(&mut self, args: &[&T]) -> bool {
        let args = args
            .iter()
            .map(|a| self.af.argument_set().get_argument(a).unwrap())
            .collect::<Vec<&Label<T>>>();
        let mut cc_computer = ConnectedComponentsComputer::new(self.af);
        let cc_af = cc_computer.merged_connected_components_of(&args);
        let cc_args = args
            .iter()
            .map(|a| cc_af.argument_set().get_argument(a.label()).unwrap())
            .collect::<Vec<&Label<T>>>();
        self.check_credulous_acceptance_for_cc(&cc_af, &cc_args).0
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
        let cc_af = cc_computer.merged_connected_components_of(&args);
        let cc_args = args
            .iter()
            .map(|a| cc_af.argument_set().get_argument(a.label()).unwrap())
            .collect::<Vec<&Label<T>>>();
        let cc_ext = match self.check_credulous_acceptance_for_cc(&cc_af, &cc_args) {
            (true, Some(ext)) => ext,
            _ => return (false, None),
        };
        let mut merged = Vec::new();
        cc_ext
            .iter()
            .map(|a| self.af.argument_set().get_argument(a.label()).unwrap())
            .for_each(|a| merged.push(a));
        while let Some(other_cc_af) = cc_computer.next_connected_component() {
            for cc_arg in self.compute_one_extension_for_cc(&other_cc_af) {
                merged.push(self.af.argument_set().get_argument(cc_arg.label()).unwrap())
            }
        }
        (true, Some(merged))
    }
}

impl<T> SkepticalAcceptanceComputer<T> for IdealSemanticsSolver<'_, T>
where
    T: LabelType,
{
    fn are_skeptically_accepted(&mut self, args: &[&T]) -> bool {
        self.are_credulously_accepted(args)
    }

    fn are_skeptically_accepted_with_certificate(
        &mut self,
        args: &[&T],
    ) -> (bool, Option<Vec<&Argument<T>>>) {
        let args = args
            .iter()
            .map(|a| self.af.argument_set().get_argument(a).unwrap())
            .collect::<Vec<&Label<T>>>();
        let ext = self.compute_one_extension().unwrap();
        if args.iter().any(|a| ext.contains(a)) {
            (true, None)
        } else {
            (false, Some(ext))
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
            fn [< test_compute_ideal_ext_is_grounded_ $suffix >] () {
                let instance = r#"
        arg(a0).
        arg(a1).
        arg(a2).
        att(a0,a1).
        att(a0,a2).
        att(a1,a0).
        att(a1,a2).
        "#;
                let reader = AspartixReader::default();
                let af = reader.read(&mut instance.as_bytes()).unwrap();
                let mut solver = IdealSemanticsSolver::new_with_sat_solver_factory_and_constraints_encoder(&af, Box::new(|| sat::default_solver()), Box::new($encoder));
                assert!(solver.compute_one_extension().unwrap().is_empty())
            }

            #[test]
            fn [< test_compute_ideal_ext_is_single_preferred_ $suffix >] () {
                let instance = r#"
        arg(a0).
        arg(a1).
        att(a0,a1).
        att(a1,a0).
        att(a1,a1).
        "#;
                let reader = AspartixReader::default();
                let af = reader.read(&mut instance.as_bytes()).unwrap();
                let mut solver = IdealSemanticsSolver::new_with_sat_solver_factory_and_constraints_encoder(&af, Box::new(|| sat::default_solver()), Box::new($encoder));
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
            fn [< test_compute_ideal_ext_is_not_grounded_ $suffix >] () {
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
                let mut solver = IdealSemanticsSolver::new_with_sat_solver_factory_and_constraints_encoder(&af, Box::new(|| sat::default_solver()), Box::new($encoder));
                assert_eq!(
                    vec!["a3"],
                    solver
                        .compute_one_extension()
                        .unwrap()
                        .iter()
                        .map(|arg| arg.label().to_string())
                        .collect::<Vec<String>>()
                )
            }

            #[test]
            fn [< test_ideal_acceptance_ $suffix >] () {
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
                let mut solver = IdealSemanticsSolver::new_with_sat_solver_factory_and_constraints_encoder(&af, Box::new(|| sat::default_solver()), Box::new($encoder));
                assert!(!solver.is_credulously_accepted(&"a0".to_string()));
                assert!(!solver.is_credulously_accepted(&"a1".to_string()));
                assert!(!solver.is_credulously_accepted(&"a2".to_string()));
                assert!(solver.is_credulously_accepted(&"a3".to_string()));
                assert!(!solver.is_skeptically_accepted(&"a0".to_string()));
                assert!(!solver.is_skeptically_accepted(&"a1".to_string()));
                assert!(!solver.is_skeptically_accepted(&"a2".to_string()));
                assert!(solver.is_skeptically_accepted(&"a3".to_string()));
            }

            #[test]
            fn [< test_ideal_acceptance_in_all_preferred_but_not_in_ideal_ $suffix >] () {
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
        "#;
                let reader = AspartixReader::default();
                let af = reader.read(&mut instance.as_bytes()).unwrap();
                let mut solver = IdealSemanticsSolver::new_with_sat_solver_factory_and_constraints_encoder(&af, Box::new(|| sat::default_solver()), Box::new($encoder));
                assert!(!solver.is_credulously_accepted(&"a0".to_string()));
                assert!(!solver.is_credulously_accepted(&"a1".to_string()));
                assert!(!solver.is_credulously_accepted(&"a2".to_string()));
                assert!(!solver.is_credulously_accepted(&"a3".to_string()));
                assert!(!solver.is_skeptically_accepted(&"a0".to_string()));
                assert!(!solver.is_skeptically_accepted(&"a1".to_string()));
                assert!(!solver.is_skeptically_accepted(&"a2".to_string()));
                assert!(!solver.is_skeptically_accepted(&"a3".to_string()));
            }

            #[test]
            fn [< test_ideal_acceptance_ext_is_grounded_ $suffix >] () {
                let instance = r#"
        arg(a0).
        arg(a1).
        arg(a2).
        att(a0,a1).
        att(a0,a2).
        att(a1,a2).
        att(a2,a1).
        "#;
                let reader = AspartixReader::default();
                let af = reader.read(&mut instance.as_bytes()).unwrap();
                let mut solver = IdealSemanticsSolver::new_with_sat_solver_factory_and_constraints_encoder(&af, Box::new(|| sat::default_solver()), Box::new($encoder));
                assert!(solver.is_credulously_accepted(&"a0".to_string()));
                assert!(!solver.is_credulously_accepted(&"a1".to_string()));
                assert!(!solver.is_credulously_accepted(&"a2".to_string()));
                assert!(solver.is_skeptically_accepted(&"a0".to_string()));
                assert!(!solver.is_skeptically_accepted(&"a1".to_string()));
                assert!(!solver.is_skeptically_accepted(&"a2".to_string()));
            }

            #[test]
            fn [< test_ideal_acceptance_ext_is_single_preferred_ $suffix >] () {
                let instance = r#"
        arg(a0).
        arg(a1).
        att(a0,a1).
        att(a1,a0).
        att(a1,a1).
        "#;
                let reader = AspartixReader::default();
                let af = reader.read(&mut instance.as_bytes()).unwrap();
                let mut solver = IdealSemanticsSolver::new_with_sat_solver_factory_and_constraints_encoder(&af, Box::new(|| sat::default_solver()), Box::new($encoder));
                assert!(solver.is_credulously_accepted(&"a0".to_string()));
                assert!(!solver.is_credulously_accepted(&"a1".to_string()));
                assert!(solver.is_skeptically_accepted(&"a0".to_string()));
                assert!(!solver.is_skeptically_accepted(&"a1".to_string()));
            }

            #[test]
            fn [< test_with_certificate_ $suffix >] () {
                let instance = r#"
        arg(a0).
        arg(a1).
        arg(a2).
        arg(a3).
        arg(a4).
        att(a0,a1).
        att(a0,a2).
        att(a1,a0).
        att(a1,a2).
        att(a2,a3).
        att(a3,a2).
        "#;
                let reader = AspartixReader::default();
                let af = reader.read(&mut instance.as_bytes()).unwrap();
                let a3 = af.argument_set().get_argument(&"a3".to_string()).unwrap();
                let a4 = af.argument_set().get_argument(&"a4".to_string()).unwrap();
                let mut solver = IdealSemanticsSolver::new_with_sat_solver_factory_and_constraints_encoder(&af, Box::new(|| sat::default_solver()), Box::new($encoder));
                assert_eq!(
                    (false, None),
                    solver.is_credulously_accepted_with_certificate(&"a0".to_string())
                );
                assert_eq!(
                    (false, None),
                    solver.is_credulously_accepted_with_certificate(&"a1".to_string())
                );
                assert_eq!(
                    (false, None),
                    solver.is_credulously_accepted_with_certificate(&"a2".to_string())
                );
                assert_eq!(
                    (true, Some(vec![a3, a4])),
                    solver.is_credulously_accepted_with_certificate(&"a3".to_string())
                );
                assert_eq!(
                    (false, Some(vec![a3, a4])),
                    solver.is_skeptically_accepted_with_certificate(&"a0".to_string())
                );
                assert_eq!(
                    (false, Some(vec![a3, a4])),
                    solver.is_skeptically_accepted_with_certificate(&"a1".to_string())
                );
                assert_eq!(
                    (false, Some(vec![a3, a4])),
                    solver.is_skeptically_accepted_with_certificate(&"a2".to_string())
                );
                assert_eq!(
                    (true, None),
                    solver.is_skeptically_accepted_with_certificate(&"a3".to_string())
                );
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
                    IdealSemanticsSolver::new_with_sat_solver_factory_and_constraints_encoder(&af, Box::new(|| sat::default_solver()), Box::new($encoder));
                let extension = solver.compute_one_extension().unwrap();
                let mut actual = extension.iter().map(|l| l.label().clone()).collect::<Vec<String>>();
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
                    IdealSemanticsSolver::new_with_sat_solver_factory_and_constraints_encoder(&af, Box::new(|| sat::default_solver()), Box::new($encoder));
                assert!(solver.are_credulously_accepted(&[&"a0".to_string(), &"a1".to_string()]));
                assert!(solver.are_credulously_accepted(&[&"a0".to_string(), &"a2".to_string()]));
                assert!(solver.are_credulously_accepted(&[&"a0".to_string(), &"a3".to_string()]));
                assert!(solver.are_credulously_accepted(&[&"a0".to_string(), &"a4".to_string()]));
                assert!(!solver.are_credulously_accepted(&[&"a1".to_string(), &"a2".to_string()]));
                assert!(!solver.are_credulously_accepted(&[&"a1".to_string(), &"a3".to_string()]));
                assert!(!solver.are_credulously_accepted(&[&"a1".to_string(), &"a4".to_string()]));
                assert!(!solver.are_credulously_accepted(&[&"a2".to_string(), &"a3".to_string()]));
                assert!(!solver.are_credulously_accepted(&[&"a2".to_string(), &"a4".to_string()]));
                assert!(!solver.are_credulously_accepted(&[&"a3".to_string(), &"a4".to_string()]));
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
                let mut solver =
                    IdealSemanticsSolver::new_with_sat_solver_factory_and_constraints_encoder(&af, Box::new(|| sat::default_solver()), Box::new($encoder));
                assert!(solver.are_skeptically_accepted(&[&"a0".to_string(), &"a1".to_string()]));
                assert!(solver.are_skeptically_accepted(&[&"a0".to_string(), &"a2".to_string()]));
                assert!(solver.are_skeptically_accepted(&[&"a0".to_string(), &"a3".to_string()]));
                assert!(solver.are_skeptically_accepted(&[&"a0".to_string(), &"a4".to_string()]));
                assert!(!solver.are_skeptically_accepted(&[&"a1".to_string(), &"a2".to_string()]));
                assert!(!solver.are_skeptically_accepted(&[&"a1".to_string(), &"a3".to_string()]));
                assert!(!solver.are_skeptically_accepted(&[&"a1".to_string(), &"a4".to_string()]));
                assert!(!solver.are_skeptically_accepted(&[&"a2".to_string(), &"a3".to_string()]));
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
