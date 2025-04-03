use super::{FlatABACompleteConstraintsEncoder, FlatABAConstraintsEncoder, FlatABAFramework};
use crate::{
    aa::Argument,
    sat::{self, SatSolver, SatSolverFactoryFn},
    solvers::{CredulousAcceptanceComputer, SatEncoder},
    utils::LabelType,
};

/// A SAT-based solver for the complete semantics dedicated to Flat ABA frameworks.
///
/// A definition of the complete extensions of an Argumentation Framework is given in the [tracks definition](https://argumentationcompetition.org/2025/tracks.html) of ICCMA'25 competition.
///
/// The implementation of the [CredulousAcceptanceComputer] problems relies on a single call to a SAT solver.
pub struct FlatABACompleteSemanticsSolver<'a, T>
where
    T: LabelType,
{
    af: &'a FlatABAFramework<T>,
    solver_factory: Box<SatSolverFactoryFn>,
}

impl<'a, T> FlatABACompleteSemanticsSolver<'a, T>
where
    T: LabelType,
{
    /// Creates a new argumentation solver for Complete semantics problems applied on ABA frameworks.
    /// This function takes as input the framework; the default SAT solver factory is used (see [default_solver](crate::sat::default_solver)).
    pub fn new(af: &'a FlatABAFramework<T>) -> Self
    where
        T: LabelType,
    {
        Self::new_with_sat_solver_factory(af, Box::new(|| sat::default_solver()))
    }

    /// Creates a new argumentation solver for Complete semantics problems applied on ABA frameworks.
    /// This function takes as input the framework and the SAT solver factory.
    pub fn new_with_sat_solver_factory(
        af: &'a FlatABAFramework<T>,
        solver_factory: Box<SatSolverFactoryFn>,
    ) -> Self
    where
        T: LabelType,
    {
        Self { af, solver_factory }
    }
}

impl<T> SatEncoder for FlatABACompleteSemanticsSolver<'_, T>
where
    T: LabelType,
{
    fn encode(&mut self) -> Box<dyn SatSolver> {
        let mut solver = (self.solver_factory)();
        let encoder = FlatABACompleteConstraintsEncoder;
        encoder.encode_constraints(self.af, solver.as_mut());
        solver
    }
}

impl<T> CredulousAcceptanceComputer<T> for FlatABACompleteSemanticsSolver<'_, T>
where
    T: LabelType,
{
    fn are_credulously_accepted(&mut self, args: &[&T]) -> bool {
        let mut solver = (self.solver_factory)();
        let encoder = FlatABACompleteConstraintsEncoder;
        encoder.encode_constraints(self.af, solver.as_mut());
        let args = args
            .iter()
            .map(|a| self.af.argument_set().get_argument(a).unwrap())
            .collect::<Vec<_>>();
        let lits = args
            .iter()
            .map(|a| encoder.arg_to_lit(*a))
            .collect::<Vec<_>>();
        solver
            .solve_under_assumptions(&lits)
            .unwrap_model()
            .is_some()
    }

    fn are_credulously_accepted_with_certificate(
        &mut self,
        _args: &[&T],
    ) -> (bool, Option<Vec<&Argument<T>>>) {
        unimplemented!()
    }
}
