use super::{
    dynamic_constraints_encoder::{self, DynamicConstraintsEncoder},
    DynamicSolver,
};
use crate::{
    aa::{AAFramework, Argument},
    encodings::ConstraintsEncoder,
    sat::{self, Assignment, Literal, SatSolver, SatSolverFactoryFn},
    solvers::{
        maximal_extension_computer::{self, MaximalExtensionComputerState},
        CredulousAcceptanceComputer, SkepticalAcceptanceComputer,
    },
    utils::LabelType,
};
use anyhow::Result;
use std::{cell::RefCell, rc::Rc};

/// A dynamic solver dedicated to the preferred semantics.
pub struct DynamicPreferredSemanticsSolver<T>
where
    T: LabelType,
{
    encoder: DynamicConstraintsEncoder<T>,
    solver: Rc<RefCell<Box<dyn SatSolver>>>,
}

impl<T> DynamicPreferredSemanticsSolver<T>
where
    T: LabelType,
{
    /// Builds a new SAT based dynamic solver for the preferred semantics.
    ///
    /// The underlying SAT solver is one returned by [default_solver](crate::sat::default_solver).
    pub fn new() -> Self
    where
        T: LabelType,
    {
        Self::new_with_sat_solver_factory(Box::new(|| sat::default_solver()))
    }

    /// Builds a new SAT based dynamic solver for the preferred semantics.
    ///
    /// The SAT solver to use in given through the solver factory.
    pub fn new_with_sat_solver_factory(solver_factory: Box<SatSolverFactoryFn>) -> Self
    where
        T: LabelType,
    {
        let solver = Rc::new(RefCell::new((solver_factory)()));
        Self {
            encoder: dynamic_constraints_encoder::new_for_complete_semantics(Rc::clone(&solver)),
            solver,
        }
    }
}

impl<T> Default for DynamicPreferredSemanticsSolver<T>
where
    T: LabelType,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<T> DynamicSolver<T> for DynamicPreferredSemanticsSolver<T>
where
    T: LabelType,
{
    fn new_argument(&mut self, label: T) {
        self.encoder.new_argument(label)
    }

    fn remove_argument(&mut self, label: &T) -> Result<()> {
        self.encoder.remove_argument(label)
    }

    fn new_attack(&mut self, from: &T, to: &T) -> Result<()> {
        self.encoder.new_attack(from, to)
    }

    fn remove_attack(&mut self, from: &T, to: &T) -> Result<()> {
        self.encoder.remove_attack(from, to)
    }
}

impl<T> CredulousAcceptanceComputer<T> for DynamicPreferredSemanticsSolver<T>
where
    T: LabelType,
{
    fn is_credulously_accepted(&mut self, _arg: &T) -> bool {
        unimplemented!()
    }

    fn is_credulously_accepted_with_certificate(
        &mut self,
        _arg: &T,
    ) -> (bool, Option<Vec<&Argument<T>>>) {
        unimplemented!()
    }
}

impl<T> SkepticalAcceptanceComputer<T> for DynamicPreferredSemanticsSolver<T>
where
    T: LabelType,
{
    fn is_skeptically_accepted(&mut self, arg: &T) -> bool {
        let constraints_encoder = LocalConstraintsEncoder {
            encoder: &self.encoder,
        };
        let mut computer = maximal_extension_computer::new_for_preferred_semantics(
            self.encoder.af(),
            Rc::clone(&self.solver),
            &constraints_encoder,
        );
        computer.set_additional_assumptions(self.encoder.assumptions().to_vec());
        let arg = self.encoder.af().argument_set().get_argument(arg).unwrap();
        loop {
            computer.compute_next();
            match computer.state() {
                MaximalExtensionComputerState::Maximal => {
                    if !computer.current().contains(&arg) {
                        return false;
                    }
                }
                MaximalExtensionComputerState::Intermediate => {
                    let current = computer.current();
                    if current.contains(&arg) {
                        computer.discard_current_search();
                    } else if self
                        .encoder
                        .af()
                        .iter_attacks_to(arg)
                        .any(|att| current.contains(&att.attacker()))
                    {
                        return false;
                    }
                }
                MaximalExtensionComputerState::None => return true,
                _ => {}
            }
        }
    }

    fn is_skeptically_accepted_with_certificate(
        &mut self,
        _arg: &T,
    ) -> (bool, Option<Vec<&Argument<T>>>) {
        unimplemented!()
    }
}

struct LocalConstraintsEncoder<'a, T>
where
    T: LabelType,
{
    encoder: &'a DynamicConstraintsEncoder<T>,
}

impl<T> ConstraintsEncoder<T> for LocalConstraintsEncoder<'_, T>
where
    T: LabelType,
{
    fn encode_constraints(&self, _af: &AAFramework<T>, _solver: &mut dyn sat::SatSolver) {
        unimplemented!()
    }

    fn encode_range_constraints(
        &self,
        _af: &AAFramework<T>,
        _solver: &mut dyn sat::SatSolver,
    ) -> usize {
        unimplemented!()
    }

    fn assignment_to_extension<'a>(
        &self,
        _assignment: &Assignment,
        _af: &'a AAFramework<T>,
    ) -> Vec<&'a Argument<T>> {
        unimplemented!()
    }

    fn arg_to_lit(&self, arg: &Argument<T>) -> Literal {
        self.encoder.arg_to_lit(arg.label())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn coreo_test() {
        let mut solver = DynamicPreferredSemanticsSolver::new();
        solver.new_argument(1);
        solver.new_argument(2);
        solver.new_attack(&1, &2).unwrap();
        assert!(solver.is_skeptically_accepted(&1));
        assert!(!solver.is_skeptically_accepted(&2));

        solver.remove_attack(&1, &2).unwrap();
        assert!(solver.is_skeptically_accepted(&1));
        assert!(solver.is_skeptically_accepted(&2));

        solver.new_argument(3);
        solver.new_attack(&3, &2).unwrap();
        solver.new_attack(&2, &1).unwrap();
        assert!(solver.is_skeptically_accepted(&1));
        assert!(!solver.is_skeptically_accepted(&2));
        assert!(solver.is_skeptically_accepted(&3));

        solver.remove_argument(&1).unwrap();
        solver.new_argument(4);
        solver.new_attack(&4, &3).unwrap();
        solver.new_attack(&3, &4).unwrap();
        assert!(!solver.is_skeptically_accepted(&2));
        assert!(!solver.is_skeptically_accepted(&3));
        assert!(!solver.is_skeptically_accepted(&4));
    }
}
