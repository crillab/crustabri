use super::complete_semantics_solver;
use crate::{
    sat::{Literal, SatSolver},
    AAFramework, LabelType, SatSolverFactoryFn,
};
use crate::{Argument, SingleExtensionComputer, SkepticalAcceptanceComputer};

/// A SAT-based solver for the preferred semantics.
///
/// This solver does not provides function to check the credulous acceptance
/// of an argument as it can be computed in a more efficient way by a [CompleteSemanticsSolver](super::CompleteSemanticsSolver).
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
    /// The underlying SAT solver is one returned by [default_solver](crate::default_solver).
    pub fn new(af: &'a AAFramework<T>) -> Self {
        Self::new_with_sat_solver_factory(af, Box::new(|| crate::default_solver()))
    }

    /// Builds a new SAT based solver for the preferred semantics.
    ///
    /// The SAT solver to use in given through the solver factory.
    pub fn new_with_sat_solver_factory(
        af: &'a AAFramework<T>,
        solver_factory: Box<SatSolverFactoryFn>,
    ) -> Self {
        Self { af, solver_factory }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum ComputerState {
    Preferred,
    Complete,
    JustDiscarded,
    None,
    Init,
}

struct PreferredExtensionComputer<'a, T>
where
    T: LabelType,
{
    af: &'a AAFramework<T>,
    solver: Box<dyn SatSolver>,
    current: Option<Vec<&'a Argument<T>>>,
    state: ComputerState,
    selector: Literal,
}

impl<'a, T> PreferredExtensionComputer<'a, T>
where
    T: LabelType,
{
    fn new(af: &'a AAFramework<T>, solver: Box<dyn SatSolver>) -> Self {
        let selector = Literal::from(1 + solver.n_vars() as isize);
        Self {
            af,
            solver,
            current: None,
            state: ComputerState::Init,
            selector,
        }
    }

    fn compute_next(&mut self) {
        match &self.state {
            ComputerState::Preferred => self.discard_preferred_and_new_search(),
            ComputerState::Complete => self.increase_current(),
            ComputerState::JustDiscarded => self.new_search(),
            ComputerState::None => panic!("no more extensions"),
            ComputerState::Init => self.compute_grounded(),
        };
    }

    fn compute_grounded(&mut self) {
        self.current = Some(crate::grounded_extension(self.af));
        self.state = ComputerState::Complete;
    }

    fn increase_current(&mut self) {
        let (mut in_ext, mut not_in_ext) = self.split_current_args();
        not_in_ext.push(self.selector);
        in_ext.push(self.selector.negate());
        self.solver.add_clause(not_in_ext);
        match self.solve(&in_ext) {
            Some(ext) => {
                self.current = Some(ext);
                self.state = ComputerState::Complete
            }
            None => self.state = ComputerState::Preferred,
        }
    }

    fn discard_current_search(&mut self) {
        let (mut in_ext, _) = self.split_current_args();
        in_ext.iter_mut().for_each(|l| *l = l.negate());
        in_ext.push(self.selector);
        self.solver.add_clause(in_ext);
        self.state = ComputerState::JustDiscarded;
    }

    fn discard_preferred_and_new_search(&mut self) {
        let (_, mut not_in_ext) = self.split_current_args();
        not_in_ext.push(self.selector);
        self.solver.add_clause(not_in_ext);
        self.new_search()
    }

    fn new_search(&mut self) {
        let assumptions = vec![self.selector.negate()];
        match self.solve(&assumptions) {
            Some(ext) => {
                self.current = Some(ext);
                self.state = ComputerState::Complete
            }
            None => self.state = ComputerState::None,
        }
    }

    fn split_current_args(&self) -> (Vec<Literal>, Vec<Literal>) {
        let current = self.current.as_ref().unwrap();
        let mut in_ext_bool = vec![false; self.af.n_arguments()];
        current.iter().for_each(|a| in_ext_bool[a.id()] = true);
        let mut not_in_ext = Vec::with_capacity(self.af.n_arguments());
        let mut in_ext = Vec::with_capacity(self.af.n_arguments());
        in_ext_bool.iter().enumerate().for_each(|(i, b)| {
            let lit = Literal::from(complete_semantics_solver::arg_id_to_solver_var(i) as isize);
            match *b {
                true => in_ext.push(lit),
                false => not_in_ext.push(lit),
            }
        });
        (in_ext, not_in_ext)
    }

    fn solve(&mut self, assumptions: &[Literal]) -> Option<Vec<&'a Argument<T>>> {
        self.solver
            .solve_under_assumptions(assumptions)
            .unwrap_model()
            .map(|new_ext_assignment| {
                let ext = new_ext_assignment
                    .iter()
                    .filter_map(|(var, opt_v)| match opt_v {
                        Some(true) => complete_semantics_solver::arg_id_from_solver_var(var)
                            .and_then(|id| {
                                if id < self.af.n_arguments() {
                                    Some(id)
                                } else {
                                    None
                                }
                            })
                            .map(|id| self.af.argument_set().get_argument_by_id(id)),
                        _ => None,
                    })
                    .collect();
                ext
            })
    }
}

impl<T> Drop for PreferredExtensionComputer<'_, T>
where
    T: LabelType,
{
    fn drop(&mut self) {
        self.solver.add_clause(vec![self.selector]);
    }
}

impl<T> SingleExtensionComputer<T> for PreferredSemanticsSolver<'_, T>
where
    T: LabelType,
{
    fn compute_one_extension(&mut self) -> Option<Vec<&Argument<T>>> {
        let mut merged = Vec::new();
        for cc_af in crate::iter_connected_components(self.af) {
            let mut solver = (self.solver_factory)();
            complete_semantics_solver::encode_complete_semantics_constraints(
                &cc_af,
                solver.as_mut(),
            );
            let mut computer = PreferredExtensionComputer::new(&cc_af, solver);
            while computer.state != ComputerState::Preferred {
                computer.compute_next();
            }
            for cc_arg in computer.current.take().unwrap() {
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
        let cc_af = crate::connected_component_of(self.af, arg);
        let cc_arg = cc_af.argument_set().get_argument(arg.label()).unwrap();
        let mut solver = (self.solver_factory)();
        complete_semantics_solver::encode_complete_semantics_constraints(&cc_af, solver.as_mut());
        let mut computer = PreferredExtensionComputer::new(&cc_af, solver);
        loop {
            computer.compute_next();
            match computer.state {
                ComputerState::Preferred => {
                    if !computer.current.as_ref().unwrap().contains(&cc_arg) {
                        return false;
                    }
                }
                ComputerState::Complete => {
                    if computer.current.as_ref().unwrap().contains(&cc_arg) {
                        computer.discard_current_search();
                    }
                }
                ComputerState::None => return true,
                _ => {}
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::AspartixReader;

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
}
