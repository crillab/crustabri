use crate::{
    aa::{AAFramework, Argument, LabelType},
    sat,
    sat::{Literal, SatSolver, SatSolverFactoryFn},
    utils::{self, ConnectedComponentsComputer},
};
use super::{
    complete_semantics_solver, maximal_extension_computer::MaximalExtensionComputer,
    preferred_semantics_solver, CredulousAcceptanceComputer, PreferredSemanticsSolver,
    SingleExtensionComputer,
};

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
    /// # use crustabri::aa::{AAFramework, LabelType};
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
    /// # use crustabri::aa::{AAFramework, LabelType};
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
        Self { af, solver_factory }
    }

    fn compute_one_extension_for_cc<'b>(&self, cc_af: &'b AAFramework<T>) -> Vec<&'b Argument<T>> {
        let grounded = utils::grounded_extension(cc_af);
        let mut in_all = vec![true; cc_af.n_arguments()];
        let mut n_in_all = 0;
        let mut n_preferred = 0;
        let mut solver = (self.solver_factory)();
        PreferredSemanticsSolver::enumerate_extensions(cc_af, solver.as_mut(), &mut |ext| {
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
        });
        if n_in_all == grounded.len() {
            return grounded;
        }
        if n_preferred == 1 {
            return single_preferred(cc_af, in_all);
        }
        compute_maximal_with_allowed(cc_af, solver.as_mut(), in_all)
    }

    fn check_credulous_acceptance_for_cc<'b>(
        &self,
        cc_af: &'b AAFramework<T>,
        cc_arg: &'b Argument<T>,
    ) -> (bool, Option<Vec<&'b Argument<T>>>) {
        let grounded = utils::grounded_extension(cc_af);
        let mut in_all = vec![true; cc_af.n_arguments()];
        let mut n_in_all = 0;
        let mut n_preferred = 0;
        let mut solver = (self.solver_factory)();
        PreferredSemanticsSolver::enumerate_extensions(cc_af, solver.as_mut(), &mut |ext| {
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
            n_in_all != grounded.len() && in_all[cc_arg.id()]
        });
        if !in_all[cc_arg.id()] {
            return (false, None);
        }
        let result = |ext: Vec<&'b Argument<T>>| {
            if ext.contains(&cc_arg) {
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
        let ideal_ext = compute_maximal_with_allowed(cc_af, solver.as_mut(), in_all);
        result(ideal_ext)
    }
}

fn compute_maximal_with_allowed<'a, T>(
    cc_af: &'a AAFramework<T>,
    solver: &mut dyn SatSolver,
    in_all_preferred: Vec<bool>,
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
                Literal::from(complete_semantics_solver::arg_id_to_solver_var(i) as isize).negate(),
            ),
        })
        .collect::<Vec<Literal>>();
    let mut computer = MaximalExtensionComputer::new(cc_af, solver);
    computer.set_increase_current_fn(Box::new(move |fn_data| {
        let (mut in_ext, mut not_in_ext) = preferred_semantics_solver::split_in_extension(
            fn_data.current_arg_set,
            fn_data.af.n_arguments(),
        );
        not_in_ext.push(fn_data.selector);
        in_ext.push(fn_data.selector.negate());
        in_ext.append(&mut assumptions.clone());
        fn_data.sat_solver.add_clause(not_in_ext);
        in_ext
    }));
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
            complete_semantics_solver::encode_complete_semantics_constraints(
                &cc_af,
                solver.as_mut(),
            );
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
    fn is_credulously_accepted(&mut self, arg: &Argument<T>) -> bool {
        let mut cc_computer = ConnectedComponentsComputer::new(self.af);
        let cc_af = cc_computer.connected_component_of(arg);
        let cc_arg = cc_af.argument_set().get_argument(arg.label()).unwrap();
        self.check_credulous_acceptance_for_cc(&cc_af, cc_arg).0
    }

    fn is_credulously_accepted_with_certificate(
        &mut self,
        arg: &Argument<T>,
    ) -> (bool, Option<Vec<&Argument<T>>>) {
        let mut cc_computer = ConnectedComponentsComputer::new(self.af);
        let cc_af = cc_computer.connected_component_of(arg);
        let cc_arg = cc_af.argument_set().get_argument(arg.label()).unwrap();
        let cc_ext = match self.check_credulous_acceptance_for_cc(&cc_af, cc_arg) {
            (true, Some(ext)) => ext,
            _ => return (false, None),
        };
        let mut merged = Vec::new();
        cc_ext
            .iter()
            .map(|a| super::utils::cc_arg_to_init_af_arg(a, self.af))
            .for_each(|a| merged.push(a));
        while let Some(other_cc_af) = cc_computer.next_connected_component() {
            for cc_arg in self.compute_one_extension_for_cc(&other_cc_af) {
                merged.push(self.af.argument_set().get_argument(cc_arg.label()).unwrap())
            }
        }
        (true, Some(merged))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::io::{AspartixReader, InstanceReader};

    #[test]
    fn test_compute_ideal_ext_is_grounded() {
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
        let mut solver = IdealSemanticsSolver::new(&af);
        assert!(solver.compute_one_extension().unwrap().is_empty())
    }

    #[test]
    fn test_compute_ideal_ext_is_not_grounded() {
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
        let mut solver = IdealSemanticsSolver::new(&af);
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
    fn test_ideal_acceptance() {
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
        let mut solver = IdealSemanticsSolver::new(&af);
        assert!(!solver
            .is_credulously_accepted(af.argument_set().get_argument(&"a0".to_string()).unwrap()));
        assert!(!solver
            .is_credulously_accepted(af.argument_set().get_argument(&"a1".to_string()).unwrap()));
        assert!(!solver
            .is_credulously_accepted(af.argument_set().get_argument(&"a2".to_string()).unwrap()));
        assert!(solver
            .is_credulously_accepted(af.argument_set().get_argument(&"a3".to_string()).unwrap()));
    }
}
