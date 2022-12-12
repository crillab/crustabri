use super::{
    complete_semantics_solver,
    maximal_extension_computer::{
        MaximalExtensionComputer, MaximalExtensionComputerState, MaximalExtensionComputerStateData,
    },
    utils, CredulousAcceptanceComputer, SingleExtensionComputer, SkepticalAcceptanceComputer,
};
use crate::{
    aa::{AAFramework, Argument},
    sat::{self, clause, Literal, SatSolver, SatSolverFactoryFn},
    utils::{ConnectedComponentsComputer, LabelType},
};

macro_rules! maximal_range_solver {
    ($solver_ident:ident, $sem_name:literal, $constraints_encoder:expr) => {
        #[doc = concat!(" A SAT-based solver for the ", $sem_name, " semantics.")]
        ///
        /// A definition of the extensions wrt. this semantics is given in the [tracks definition](https://iccma2023.github.io/tracks.html) of ICCMA'23 competition.
        ///
        /// For both acceptance queries and extension computation, this solver relies on successive calls to a SAT solver making the computation reach the second level of the polynomial hierarchy.
        ///
        /// The certificates for the acceptance queries are extensions.
        pub struct $solver_ident<'a, T>
        where
            T: LabelType,
        {
            helper: MaximalRangeSemanticsHelper<'a, T>,
        }

        impl<'a, T> $solver_ident<'a, T>
        where
            T: LabelType,
        {
            /// Builds a new SAT based solver for this semantics.
            ///
            /// The underlying SAT solver is one returned by [default_solver](crate::sat::default_solver).
            ///
            /// # Example
            ///
            /// ```
            /// # use crustabri::aa::{AAFramework};
            /// # use crustabri::utils::LabelType;
            #[doc = concat!(" # use crustabri::solvers::{SingleExtensionComputer, ", stringify!($solver_ident), "};")]
            /// fn search_one_extension<T>(af: &AAFramework<T>) where T: LabelType {
            #[doc = concat!("     let mut solver = ", stringify!($solver_ident), "::new(af);")]
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

            /// Builds a new SAT based solver for the this semantics.
            ///
            /// The SAT solver to use in given through the solver factory.
            ///
            /// # Example
            ///
            /// ```
            /// # use crustabri::aa::{AAFramework};
            /// # use crustabri::utils::LabelType;
            /// # use crustabri::sat::CadicalSolver;
            #[doc = concat!(" # use crustabri::solvers::{SingleExtensionComputer, ", stringify!($solver_ident), "};")]
            /// fn search_one_extension<T>(af: &AAFramework<T>) where T: LabelType {
            #[doc = concat!("     let mut solver = ", stringify!($solver_ident), "::new_with_sat_solver_factory(")]
            ///         af,
            ///         Box::new(|| Box::new(CadicalSolver::default()))
            ///     );
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
                Self {
                    helper: MaximalRangeSemanticsHelper::new(
                        af,
                        solver_factory,
                        $constraints_encoder,
                    ),
                }
            }
        }

        impl<T> SingleExtensionComputer<T> for $solver_ident<'_, T>
        where
            T: LabelType,
        {
            fn compute_one_extension(&mut self) -> Option<Vec<&Argument<T>>> {
                self.helper.compute_one_extension()
            }
        }

        impl<T> CredulousAcceptanceComputer<T> for $solver_ident<'_, T>
        where
            T: LabelType,
        {
            fn is_credulously_accepted(&mut self, arg: &Argument<T>) -> bool {
                self.helper.is_credulously_accepted(arg)
            }

            fn is_credulously_accepted_with_certificate(
                &mut self,
                arg: &Argument<T>,
            ) -> (bool, Option<Vec<&Argument<T>>>) {
                self.helper.is_credulously_accepted_with_certificate(arg)
            }
        }

        impl<T> SkepticalAcceptanceComputer<T> for $solver_ident<'_, T>
        where
            T: LabelType,
        {
            fn is_skeptically_accepted(&mut self, arg: &Argument<T>) -> bool {
                self.helper.is_skeptically_accepted(arg)
            }

            fn is_skeptically_accepted_with_certificate(
                &mut self,
                arg: &Argument<T>,
            ) -> (bool, Option<Vec<&Argument<T>>>) {
                self.helper.is_skeptically_accepted_with_certificate(arg)
            }
        }
    };
}

maximal_range_solver!(
    SemiStableSemanticsSolver,
    "semi-stable",
    Box::new(|af, solver| {
        complete_semantics_solver::encode_complete_semantics_constraints(af, solver)
    })
);

maximal_range_solver!(
    StageSemanticsSolver,
    "stage",
    Box::new(|af, solver| { encode_conflict_freeness_constraints(af, solver) })
);

fn encode_conflict_freeness_constraints<T>(af: &AAFramework<T>, solver: &mut dyn SatSolver)
where
    T: LabelType,
{
    complete_semantics_solver::encode_disjunction_vars(af, solver);
    af.argument_set().iter().for_each(|arg| {
        let attacked_id = arg.id();
        let attacked_solver_var =
            complete_semantics_solver::arg_id_to_solver_var(attacked_id) as isize;
        af.iter_attacks_to(arg).for_each(|att| {
            let attacker_id = att.attacker().id();
            let attacker_solver_var =
                complete_semantics_solver::arg_id_to_solver_var(attacker_id) as isize;
            solver.add_clause(clause![-attacked_solver_var, -attacker_solver_var,]);
        });
    });
}

pub(crate) type ConstraintsEncoder<T> = dyn Fn(&AAFramework<T>, &mut dyn SatSolver);

pub(crate) struct MaximalRangeSemanticsHelper<'a, T>
where
    T: LabelType,
{
    af: &'a AAFramework<T>,
    solver_factory: Box<SatSolverFactoryFn>,
    constraints_encoder: Box<ConstraintsEncoder<T>>,
}

impl<'a, T> MaximalRangeSemanticsHelper<'a, T>
where
    T: LabelType,
{
    pub fn new(
        af: &'a AAFramework<T>,
        solver_factory: Box<SatSolverFactoryFn>,
        constraints_encoder: Box<ConstraintsEncoder<T>>,
    ) -> Self {
        MaximalRangeSemanticsHelper {
            af,
            solver_factory,
            constraints_encoder,
        }
    }

    pub fn compute_one_extension(&mut self) -> Option<Vec<&Argument<T>>> {
        let mut merged = Vec::new();
        for cc_af in ConnectedComponentsComputer::iter_connected_components(self.af) {
            let mut solver = (self.solver_factory)();
            (self.constraints_encoder)(&cc_af, solver.as_mut());
            let (computer, _) = new_maximal_extension_computer(&cc_af, solver.as_mut());
            for cc_arg in computer.compute_maximal() {
                merged.push(self.af.argument_set().get_argument(cc_arg.label()).unwrap())
            }
        }
        Some(merged)
    }

    pub fn is_credulously_accepted(&mut self, arg: &Argument<T>) -> bool {
        let mut cc_computer = ConnectedComponentsComputer::new(self.af);
        let cc_af = cc_computer.connected_component_of(arg);
        self.check_acceptance_in_cc(&cc_af, arg, true).0
    }

    pub fn is_credulously_accepted_with_certificate(
        &mut self,
        arg: &Argument<T>,
    ) -> (bool, Option<Vec<&Argument<T>>>) {
        self.check_acceptance_with_certificate(arg, true)
    }

    pub fn is_skeptically_accepted(&mut self, arg: &Argument<T>) -> bool {
        let mut cc_computer = ConnectedComponentsComputer::new(self.af);
        let cc_af = cc_computer.connected_component_of(arg);
        self.check_acceptance_in_cc(&cc_af, arg, false).0
    }

    pub fn is_skeptically_accepted_with_certificate(
        &mut self,
        arg: &Argument<T>,
    ) -> (bool, Option<Vec<&Argument<T>>>) {
        self.check_acceptance_with_certificate(arg, false)
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
        (self.constraints_encoder)(cc_af, solver.as_mut());
        let (mut computer, first_range_var) =
            new_maximal_extension_computer(cc_af, solver.as_mut());
        loop {
            computer.compute_next();
            match computer.state() {
                MaximalExtensionComputerState::Maximal => {
                    let stop_enum_reason = enumerate_extensions_for_range(
                        &mut computer.state_data(),
                        first_range_var,
                        &|ext| {
                            if ext.contains(&cc_arg) == is_credulous_acceptance {
                                Some(ext.iter().map(|a| a.id()).collect())
                            } else {
                                None
                            }
                        },
                    );
                    if let Some(reason) = stop_enum_reason {
                        return (
                            is_credulous_acceptance,
                            Some(
                                reason
                                    .iter()
                                    .map(|id| cc_af.argument_set().get_argument_by_id(*id))
                                    .collect(),
                            ),
                        );
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
            (self.constraints_encoder)(&other_cc_af, solver.as_mut());
            let (computer, _) = new_maximal_extension_computer(&other_cc_af, solver.as_mut());
            for cc_arg in computer.compute_maximal() {
                ext.push(self.af.argument_set().get_argument(cc_arg.label()).unwrap())
            }
        }
    }
}

fn new_maximal_extension_computer<'a, 'b, T>(
    af: &'a AAFramework<T>,
    solver: &'b mut dyn SatSolver,
) -> (MaximalExtensionComputer<'a, 'b, T>, usize)
where
    T: LabelType,
{
    let first_range_var = encode_range_constraints(af, solver);
    let mut computer = MaximalExtensionComputer::new(af, solver);
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
//
// This function returns `None` if the enumeration must continue.
// Otherwise, it returns a value indicating why the enumeration should stop.
// This value is computed and returned by the callback function.
fn enumerate_extensions_for_range<F, T>(
    fn_data: &mut MaximalExtensionComputerStateData<T>,
    first_range_var: usize,
    callback: &F,
) -> Option<Vec<usize>>
where
    T: LabelType,
    F: Fn(&[&Argument<T>]) -> Option<Vec<usize>>,
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
        let must_stop = (callback)(current_extension);
        if must_stop.is_some() {
            return must_stop;
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
    None
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
    fn test_semi_stable_skeptical_acceptance() {
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
    fn test_semi_stable_skeptical_acceptance_after_arg_removal() {
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
    fn test_semi_stable_skeptical_acceptance_auto_attack() {
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
    fn test_semi_stable_credulous_acceptance() {
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
    fn test_semi_stable_credulous_acceptance_after_arg_removal() {
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
    fn test_semi_stable_credulous_acceptance_auto_attack() {
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

    #[test]
    fn test_compute_one_stage_ext_is_grounded() {
        let instance = r#"
        arg(a0).
        arg(a1).
        att(a0,a1).
        "#;
        let reader = AspartixReader::default();
        let af = reader.read(&mut instance.as_bytes()).unwrap();
        let mut solver = StageSemanticsSolver::new(&af);
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
    fn test_compute_one_stage_ext_is_not_grounded() {
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
        let mut solver = StageSemanticsSolver::new(&af);
        let n_args = solver.compute_one_extension().unwrap().len();
        assert_eq!(1, n_args);
    }

    #[test]
    fn test_compute_one_stage_after_arg_removal() {
        let instance = r#"
        arg(a0).
        arg(a1).
        "#;
        let reader = AspartixReader::default();
        let mut af = reader.read(&mut instance.as_bytes()).unwrap();
        af.remove_argument(&"a0".to_string()).unwrap();
        let mut solver = StageSemanticsSolver::new(&af);
        let ext = solver.compute_one_extension().unwrap();
        assert_eq!(1, ext.len());
        assert_eq!("a1", ext[0].label());
    }

    #[test]
    fn test_stage_skeptical_acceptance() {
        let instance = r#"
        arg(a0).
        arg(a1).
        arg(a2).
        arg(a3).
        arg(a4).
        att(a0,a1).
        att(a0,a3).
        att(a1,a2).
        att(a1,a3).
        att(a2,a0).
        att(a2,a3).
        att(a3,a4).
        "#;
        let reader = AspartixReader::default();
        let af = reader.read(&mut instance.as_bytes()).unwrap();
        let mut solver = StageSemanticsSolver::new(&af);
        assert!(!solver
            .is_skeptically_accepted(af.argument_set().get_argument(&"a0".to_string()).unwrap()));
        assert!(!solver
            .is_skeptically_accepted(af.argument_set().get_argument(&"a1".to_string()).unwrap()));
        assert!(!solver
            .is_skeptically_accepted(af.argument_set().get_argument(&"a2".to_string()).unwrap()));
        assert!(!solver
            .is_skeptically_accepted(af.argument_set().get_argument(&"a3".to_string()).unwrap()));
        assert!(solver
            .is_skeptically_accepted(af.argument_set().get_argument(&"a4".to_string()).unwrap()));
    }

    #[test]
    fn test_stage_skeptical_acceptance_after_arg_removal() {
        let instance = r#"
        arg(a0).
        arg(a1).
        arg(a2).
        arg(a3).
        arg(a4).
        att(a0,a1).
        att(a0,a3).
        att(a1,a2).
        att(a1,a3).
        att(a2,a0).
        att(a2,a3).
        att(a3,a4).
        "#;
        let reader = AspartixReader::default();
        let mut af = reader.read(&mut instance.as_bytes()).unwrap();
        af.remove_argument(&"a0".to_string()).unwrap();
        let mut solver = StageSemanticsSolver::new(&af);
        assert!(solver
            .is_skeptically_accepted(af.argument_set().get_argument(&"a1".to_string()).unwrap()));
        assert!(!solver
            .is_skeptically_accepted(af.argument_set().get_argument(&"a2".to_string()).unwrap()));
        assert!(!solver
            .is_skeptically_accepted(af.argument_set().get_argument(&"a3".to_string()).unwrap()));
        assert!(solver
            .is_skeptically_accepted(af.argument_set().get_argument(&"a4".to_string()).unwrap()));
    }

    #[test]
    fn test_stage_skeptical_acceptance_auto_attack() {
        let instance = r#"
        arg(a0).
        att(a0,a0).
        "#;
        let reader = AspartixReader::default();
        let af = reader.read(&mut instance.as_bytes()).unwrap();
        let mut solver = StageSemanticsSolver::new(&af);
        assert!(!solver
            .is_skeptically_accepted(af.argument_set().get_argument(&"a0".to_string()).unwrap()));
    }

    #[test]
    fn test_stage_credulous_acceptance() {
        let instance = r#"
        arg(a0).
        arg(a1).
        arg(a2).
        arg(a3).
        arg(a4).
        att(a0,a1).
        att(a0,a3).
        att(a1,a2).
        att(a1,a3).
        att(a2,a0).
        att(a2,a3).
        att(a3,a4).
        "#;
        let reader = AspartixReader::default();
        let af = reader.read(&mut instance.as_bytes()).unwrap();
        let mut solver = StageSemanticsSolver::new(&af);
        assert!(solver
            .is_credulously_accepted(af.argument_set().get_argument(&"a0".to_string()).unwrap()));
        assert!(solver
            .is_credulously_accepted(af.argument_set().get_argument(&"a1".to_string()).unwrap()));
        assert!(solver
            .is_credulously_accepted(af.argument_set().get_argument(&"a2".to_string()).unwrap()));
        assert!(!solver
            .is_credulously_accepted(af.argument_set().get_argument(&"a3".to_string()).unwrap()));
        assert!(solver
            .is_credulously_accepted(af.argument_set().get_argument(&"a4".to_string()).unwrap()));
    }

    #[test]
    fn test_stage_credulous_acceptance_after_arg_removal() {
        let instance = r#"
        arg(a0).
        arg(a1).
        arg(a2).
        arg(a3).
        arg(a4).
        att(a0,a1).
        att(a0,a3).
        att(a1,a2).
        att(a1,a3).
        att(a2,a0).
        att(a2,a3).
        att(a3,a4).
        "#;
        let reader = AspartixReader::default();
        let mut af = reader.read(&mut instance.as_bytes()).unwrap();
        af.remove_argument(&"a0".to_string()).unwrap();
        let mut solver = StageSemanticsSolver::new(&af);
        assert!(solver
            .is_credulously_accepted(af.argument_set().get_argument(&"a1".to_string()).unwrap()));
        assert!(!solver
            .is_credulously_accepted(af.argument_set().get_argument(&"a2".to_string()).unwrap()));
        assert!(!solver
            .is_credulously_accepted(af.argument_set().get_argument(&"a3".to_string()).unwrap()));
        assert!(solver
            .is_credulously_accepted(af.argument_set().get_argument(&"a4".to_string()).unwrap()));
    }

    #[test]
    fn test_stage_credulous_acceptance_auto_attack() {
        let instance = r#"
        arg(a0).
        att(a0,a0).
        "#;
        let reader = AspartixReader::default();
        let af = reader.read(&mut instance.as_bytes()).unwrap();
        let mut solver = StageSemanticsSolver::new(&af);
        assert!(!solver
            .is_credulously_accepted(af.argument_set().get_argument(&"a0".to_string()).unwrap()));
    }

    #[test]
    fn test_semi_stable_check_certificate_involve_var() {
        let instance = r#"
        arg(a0).
        arg(a1).
        att(a0,a1).
        att(a1,a0).
        "#;
        let reader = AspartixReader::default();
        let af = reader.read(&mut instance.as_bytes()).unwrap();
        let mut solver = SemiStableSemanticsSolver::new(&af);
        let a0_label = af.argument_set().get_argument(&"a0".to_string()).unwrap();
        let (acceptance, certificate) = solver.is_credulously_accepted_with_certificate(a0_label);
        assert!(acceptance);
        assert!(certificate.unwrap().contains(&a0_label));
        let a1_label = af.argument_set().get_argument(&"a1".to_string()).unwrap();
        let (acceptance, certificate) = solver.is_credulously_accepted_with_certificate(a1_label);
        assert!(acceptance);
        assert!(certificate.unwrap().contains(&a1_label));
    }
}
