use std::{cell::RefCell, rc::Rc};

use crate::{
    aa::{AAFramework, Argument, LabelType},
    sat::{self, clause, Literal, SatSolver, SatSolverFactoryFn},
    utils::ConnectedComponentsComputer,
};

use super::{
    complete_semantics_solver,
    maximal_extension_computer::{
        MaximalExtensionComputer, MaximalExtensionComputerState, MaximalExtensionComputerStateData,
    },
    utils, CredulousAcceptanceComputer, SingleExtensionComputer, SkepticalAcceptanceComputer,
};

/// A SAT-based solver for the semi-stable semantics.
///
/// A definition of the semi-stable extensions of an Argumentation Framework is given in the [tracks definition](https://iccma2023.github.io/tracks.html) of ICCMA'23 competition.
///
/// For both acceptance queries and extension computation, this solver relies on successive calls to a SAT solver making the computation reach the second level of the polynomial hierarchy.
///
/// The certificates for the acceptance queries are extensions.
pub struct SemiStableSemanticsSolver<'a, T>
where
    T: LabelType,
{
    af: &'a AAFramework<T>,
    solver_factory: Box<SatSolverFactoryFn>,
}

impl<'a, T> SemiStableSemanticsSolver<'a, T>
where
    T: LabelType,
{
    /// Builds a new SAT based solver for the semi-stable semantics.
    ///
    /// The underlying SAT solver is one returned by [default_solver](crate::sat::default_solver).
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::aa::{AAFramework, LabelType};
    /// # use crustabri::solvers::{SingleExtensionComputer, SemiStableSemanticsSolver};
    /// fn search_one_extension<T>(af: &AAFramework<T>) where T: LabelType {
    ///     let mut solver = SemiStableSemanticsSolver::new(af);
    ///     let ext = solver.compute_one_extension().unwrap();
    ///     println!("found a semi-stable extension: {:?}", ext);
    /// }
    /// # search_one_extension::<usize>(&AAFramework::default());
    pub fn new(af: &'a AAFramework<T>) -> Self
    where
        T: LabelType,
    {
        Self::new_with_sat_solver_factory(af, Box::new(|| sat::default_solver()))
    }

    /// Builds a new SAT based solver for the semi-stable semantics.
    ///
    /// The SAT solver to use in given through the solver factory.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::aa::{AAFramework, LabelType};
    /// # use crustabri::solvers::{SingleExtensionComputer, SemiStableSemanticsSolver};
    /// fn search_one_extension<T>(af: &AAFramework<T>) where T: LabelType {
    ///     let mut solver = SemiStableSemanticsSolver::new(af);
    ///     let ext = solver.compute_one_extension().unwrap();
    ///     println!("found a semi-stable extension: {:?}", ext);
    /// }
    /// # search_one_extension::<usize>(&AAFramework::default());
    pub fn new_with_sat_solver_factory(
        af: &'a AAFramework<T>,
        solver_factory: Box<SatSolverFactoryFn>,
    ) -> Self
    where
        T: LabelType,
    {
        Self { af, solver_factory }
    }

    fn check_acceptance_with_certificate(
        &mut self,
        arg: &Argument<T>,
        is_credulous_acceptance: bool,
    ) -> (bool, Option<Vec<&Argument<T>>>) {
        let mut cc_computer = ConnectedComponentsComputer::new(self.af);
        let cc_af = cc_computer.connected_component_of(arg);
        let mut merged = Vec::new();
        match self.check_acceptance_in_cc(&cc_af, arg, is_credulous_acceptance) {
            (_, None) => return (!is_credulous_acceptance, None),
            (_, Some(cc_ext)) => {
                cc_ext
                    .iter()
                    .map(|a| utils::cc_arg_to_init_af_arg(a, self.af))
                    .for_each(|a| merged.push(a));
            }
        }
        self.fulfill_extension_with_other_connected_components(cc_computer, &mut merged);
        (is_credulous_acceptance, Some(merged))
    }

    fn check_acceptance_in_cc<'b>(
        &self,
        cc_af: &'b AAFramework<T>,
        arg: &'a Argument<T>,
        is_credulous_acceptance: bool,
    ) -> (bool, Option<Vec<&'b Argument<T>>>) {
        let cc_arg = cc_af.argument_set().get_argument(arg.label()).unwrap();
        let mut solver = (self.solver_factory)();
        complete_semantics_solver::encode_complete_semantics_constraints(cc_af, solver.as_mut());
        let (mut computer, first_range_var) = new_maximal_extension_computer(cc_af, solver);
        loop {
            computer.compute_next();
            match computer.state() {
                MaximalExtensionComputerState::Maximal => {
                    let stop_enum = Rc::new(RefCell::new(false));
                    enumerate_extensions_for_range(
                        &mut computer.state_data(),
                        first_range_var,
                        &|ext| {
                            if ext.contains(&cc_arg) == is_credulous_acceptance {
                                *stop_enum.borrow_mut() = true;
                                false
                            } else {
                                true
                            }
                        },
                    );
                    if *stop_enum.borrow() {
                        return (is_credulous_acceptance, Some(computer.take_current()));
                    }
                }
                MaximalExtensionComputerState::None => return (!is_credulous_acceptance, None),
                _ => {}
            }
        }
    }

    fn fulfill_extension_with_other_connected_components(
        &self,
        mut cc_computer: ConnectedComponentsComputer<T>,
        ext: &mut Vec<&'a Argument<T>>,
    ) where
        T: LabelType,
    {
        while let Some(other_cc_af) = cc_computer.next_connected_component() {
            let mut solver = (self.solver_factory)();
            complete_semantics_solver::encode_complete_semantics_constraints(
                &other_cc_af,
                solver.as_mut(),
            );
            let (computer, _) = new_maximal_extension_computer(&other_cc_af, solver);
            for cc_arg in computer.compute_maximal() {
                ext.push(self.af.argument_set().get_argument(cc_arg.label()).unwrap())
            }
        }
    }
}

fn new_maximal_extension_computer<T>(
    cc_af: &AAFramework<T>,
    mut solver: Box<dyn SatSolver>,
) -> (MaximalExtensionComputer<T>, usize)
where
    T: LabelType,
{
    let first_range_var = encode_range_constraints(cc_af, solver.as_mut());
    let mut computer = MaximalExtensionComputer::new(cc_af, solver);
    computer.set_increase_current_fn(Box::new(move |fn_data| {
        let (mut in_range, mut not_in_range) = split_in_range(&fn_data, first_range_var);
        not_in_range.push(fn_data.selector);
        in_range.push(fn_data.selector.negate());
        fn_data.sat_solver.add_clause(not_in_range);
        in_range
    }));
    computer.set_discard_maximal_fn(Box::new(move |fn_data| {
        let (_, mut not_in_range) = split_in_range(&fn_data, first_range_var);
        not_in_range.push(fn_data.selector);
        fn_data.sat_solver.add_clause(not_in_range);
    }));
    (computer, first_range_var)
}

fn encode_range_constraints<T>(af: &AAFramework<T>, solver: &mut dyn SatSolver) -> usize
where
    T: LabelType,
{
    af.argument_set().iter().for_each(|a| {
        let range_var = 1 + solver.n_vars() as isize;
        let arg_var = complete_semantics_solver::arg_id_to_solver_var(a.id()) as isize;
        let att_disj_var =
            complete_semantics_solver::arg_id_to_solver_disjunction_var(a.id()) as isize;
        solver.add_clause(clause!(-arg_var, range_var));
        solver.add_clause(clause!(-att_disj_var, range_var));
        solver.add_clause(clause!(-range_var, arg_var, att_disj_var));
    });
    solver.n_vars() + 1 - af.n_arguments()
}

// The callback function is called for all extension matching the range.
// This function returns a Boolean indicating if the enumeration must continue.
fn enumerate_extensions_for_range<T>(
    fn_data: &mut MaximalExtensionComputerStateData<T>,
    first_range_var: usize,
    callback: &dyn Fn(&[&Argument<T>]) -> bool,
) where
    T: LabelType,
{
    let enum_selector = Literal::from(1 + fn_data.sat_solver.n_vars() as isize);
    let (mut in_range, mut not_in_range) = split_in_range(fn_data, first_range_var);
    not_in_range.iter_mut().for_each(|l| *l = l.negate());
    let mut assumptions = Vec::with_capacity(fn_data.af.n_arguments() + 1);
    assumptions.append(&mut in_range);
    assumptions.append(&mut not_in_range);
    assumptions.push(enum_selector.negate());
    #[allow(unused_assignments)]
    let mut current_extension_vec = None;
    let mut current_extension = fn_data.current_arg_set;
    loop {
        let must_continue = (callback)(current_extension);
        if !must_continue {
            break;
        }
        let mut in_current = vec![false; fn_data.af.n_arguments()];
        current_extension
            .iter()
            .for_each(|a| in_current[a.id()] = true);
        let blocking_clause = in_current
            .iter()
            .enumerate()
            .filter_map(|(i, b)| {
                if *b {
                    None
                } else {
                    Some(Literal::from(
                        complete_semantics_solver::arg_id_to_solver_var(i) as isize,
                    ))
                }
            })
            .chain(std::iter::once(enum_selector))
            .collect();
        fn_data.sat_solver.add_clause(blocking_clause);
        match fn_data
            .sat_solver
            .solve_under_assumptions(&assumptions)
            .unwrap_model()
        {
            Some(assignment) => {
                current_extension_vec = Some(utils::assignment_to_complete_extension(
                    &assignment,
                    fn_data.af,
                ));
                current_extension = current_extension_vec.as_ref().unwrap();
            }
            None => break,
        }
    }
    fn_data.sat_solver.add_clause(clause!(enum_selector));
}

fn split_in_range<T>(
    fn_data: &MaximalExtensionComputerStateData<T>,
    first_range_var: usize,
) -> (Vec<Literal>, Vec<Literal>)
where
    T: LabelType,
{
    let mut in_range = Vec::with_capacity(1 + fn_data.af.n_arguments());
    let mut not_in_range = Vec::with_capacity(1 + fn_data.af.n_arguments());
    if let Some(m) = fn_data.current_model {
        (first_range_var..first_range_var + fn_data.af.n_arguments()).for_each(|i| {
            if m.value_of(i) == Some(false) {
                not_in_range.push(Literal::from(i as isize));
            } else {
                in_range.push(Literal::from(i as isize));
            }
        });
    } else {
        let mut in_range_bool = vec![false; fn_data.af.n_arguments()];
        fn_data.current_arg_set.iter().for_each(|arg| {
            in_range_bool[arg.id()] = true;
            fn_data
                .af
                .iter_attacks_from(arg)
                .for_each(|att| in_range_bool[att.attacked().id()] = true);
        });
        in_range_bool.iter().enumerate().for_each(|(i, b)| {
            let lit = Literal::from((first_range_var + i) as isize);
            if *b {
                in_range.push(lit);
            } else {
                not_in_range.push(lit);
            }
        });
    }
    (in_range, not_in_range)
}

impl<T> SingleExtensionComputer<T> for SemiStableSemanticsSolver<'_, T>
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
            let (computer, _) = new_maximal_extension_computer(&cc_af, solver);
            for cc_arg in computer.compute_maximal() {
                merged.push(self.af.argument_set().get_argument(cc_arg.label()).unwrap())
            }
        }
        Some(merged)
    }
}

impl<T> CredulousAcceptanceComputer<T> for SemiStableSemanticsSolver<'_, T>
where
    T: LabelType,
{
    fn is_credulously_accepted(&mut self, arg: &Argument<T>) -> bool {
        let mut cc_computer = ConnectedComponentsComputer::new(self.af);
        let cc_af = cc_computer.connected_component_of(arg);
        self.check_acceptance_in_cc(&cc_af, arg, true).0
    }

    fn is_credulously_accepted_with_certificate(
        &mut self,
        arg: &Argument<T>,
    ) -> (bool, Option<Vec<&Argument<T>>>) {
        self.check_acceptance_with_certificate(arg, true)
    }
}

impl<T> SkepticalAcceptanceComputer<T> for SemiStableSemanticsSolver<'_, T>
where
    T: LabelType,
{
    fn is_skeptically_accepted(&mut self, arg: &Argument<T>) -> bool {
        let mut cc_computer = ConnectedComponentsComputer::new(self.af);
        let cc_af = cc_computer.connected_component_of(arg);
        self.check_acceptance_in_cc(&cc_af, arg, false).0
    }

    fn is_skeptically_accepted_with_certificate(
        &mut self,
        arg: &Argument<T>,
    ) -> (bool, Option<Vec<&Argument<T>>>) {
        self.check_acceptance_with_certificate(arg, false)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::io::{AspartixReader, InstanceReader};

    #[test]
    fn test_compute_one_semi_stable_ext_is_grounded() {
        let instance = r#"
        arg(a0).
        arg(a1).
        att(a0,a1).
        "#;
        let reader = AspartixReader::default();
        let af = reader.read(&mut instance.as_bytes()).unwrap();
        let mut solver = SemiStableSemanticsSolver::new(&af);
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
    fn test_compute_one_semi_stable_ext_is_not_grounded() {
        let instance = r#"
        arg(a0).
        arg(a1).
        arg(a2).
        arg(a3).
        arg(a4).
        att(a0,a1).
        att(a1,a0).
        att(a1,a2).
        att(a2,a3).
        att(a3,a4).
        att(a4,a2).
        "#;
        let reader = AspartixReader::default();
        let af = reader.read(&mut instance.as_bytes()).unwrap();
        let mut solver = SemiStableSemanticsSolver::new(&af);
        let args = solver
            .compute_one_extension()
            .unwrap()
            .iter()
            .map(|arg| arg.label().to_string())
            .collect::<Vec<String>>();
        assert!(!args.contains(&"a0".to_string()));
        assert!(args.contains(&"a1".to_string()));
        assert!(!args.contains(&"a2".to_string()));
        assert!(args.contains(&"a3".to_string()));
        assert!(!args.contains(&"a4".to_string()));
    }

    #[test]
    fn test_compute_one_semi_stable_after_arg_removal() {
        let instance = r#"
        arg(a0).
        arg(a1).
        "#;
        let reader = AspartixReader::default();
        let mut af = reader.read(&mut instance.as_bytes()).unwrap();
        af.remove_argument(&"a0".to_string()).unwrap();
        let mut solver = SemiStableSemanticsSolver::new(&af);
        let ext = solver.compute_one_extension().unwrap();
        assert_eq!(1, ext.len());
        assert_eq!("a1", ext[0].label());
    }

    #[test]
    fn test_skeptical_acceptance() {
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
        let mut solver = SemiStableSemanticsSolver::new(&af);
        assert!(solver
            .is_skeptically_accepted(af.argument_set().get_argument(&"a0".to_string()).unwrap()));
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
        let mut af = reader.read(&mut instance.as_bytes()).unwrap();
        af.remove_argument(&"a0".to_string()).unwrap();
        let mut solver = SemiStableSemanticsSolver::new(&af);
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
    fn test_skeptical_acceptance_auto_attack() {
        let instance = r#"
        arg(a0).
        att(a0,a0).
        "#;
        let reader = AspartixReader::default();
        let af = reader.read(&mut instance.as_bytes()).unwrap();
        let mut solver = SemiStableSemanticsSolver::new(&af);
        assert!(!solver
            .is_skeptically_accepted(af.argument_set().get_argument(&"a0".to_string()).unwrap()));
    }

    #[test]
    fn test_credulous_acceptance() {
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
        let mut solver = SemiStableSemanticsSolver::new(&af);
        assert!(solver
            .is_credulously_accepted(af.argument_set().get_argument(&"a0".to_string()).unwrap()));
        assert!(solver
            .is_credulously_accepted(af.argument_set().get_argument(&"a2".to_string()).unwrap()));
        assert!(solver
            .is_credulously_accepted(af.argument_set().get_argument(&"a3".to_string()).unwrap()));
        assert!(!solver
            .is_credulously_accepted(af.argument_set().get_argument(&"a4".to_string()).unwrap()));
        assert!(solver
            .is_credulously_accepted(af.argument_set().get_argument(&"a5".to_string()).unwrap()));
    }

    #[test]
    fn test_credulous_acceptance_after_arg_removal() {
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
        let mut af = reader.read(&mut instance.as_bytes()).unwrap();
        af.remove_argument(&"a0".to_string()).unwrap();
        let mut solver = SemiStableSemanticsSolver::new(&af);
        assert!(solver
            .is_credulously_accepted(af.argument_set().get_argument(&"a2".to_string()).unwrap()));
        assert!(solver
            .is_credulously_accepted(af.argument_set().get_argument(&"a3".to_string()).unwrap()));
        assert!(!solver
            .is_credulously_accepted(af.argument_set().get_argument(&"a4".to_string()).unwrap()));
        assert!(solver
            .is_credulously_accepted(af.argument_set().get_argument(&"a5".to_string()).unwrap()));
    }

    #[test]
    fn test_credulous_acceptance_auto_attack() {
        let instance = r#"
        arg(a0).
        att(a0,a0).
        "#;
        let reader = AspartixReader::default();
        let af = reader.read(&mut instance.as_bytes()).unwrap();
        let mut solver = SemiStableSemanticsSolver::new(&af);
        assert!(!solver
            .is_credulously_accepted(af.argument_set().get_argument(&"a0".to_string()).unwrap()));
    }
}
