use super::{
    buffered_dynamic_constraints_encoder::BufferedDynamicConstraintsEncoder, DynamicSolver,
};
use crate::{
    aa::{AAFramework, Argument, ArgumentSet, Semantics},
    sat::{self, SatSolver, SatSolverFactoryFn},
    solvers::{CredulousAcceptanceComputer, SkepticalAcceptanceComputer},
    utils::LabelType,
};
use anyhow::Result;
use std::{cell::RefCell, rc::Rc};

/// A dynamic solver dedicated to the complete semantics.
pub struct DynamicStableSemanticsSolver<T>
where
    T: LabelType,
{
    af: AAFramework<T>,
    buffered_encoder: BufferedDynamicConstraintsEncoder<T>,
    solver: Rc<RefCell<Box<dyn SatSolver>>>,
}

impl<T> DynamicStableSemanticsSolver<T>
where
    T: LabelType,
{
    /// Builds a new SAT based dynamic solver for the complete semantics.
    ///
    /// The underlying SAT solver is one returned by [default_solver](crate::sat::default_solver).
    pub fn new() -> Self
    where
        T: LabelType,
    {
        Self::new_with_sat_solver_factory(Box::new(|| sat::default_solver()))
    }

    /// Builds a new SAT based dynamic solver for the complete semantics.
    ///
    /// The SAT solver to use in given through the solver factory.
    pub fn new_with_sat_solver_factory(solver_factory: Box<SatSolverFactoryFn>) -> Self
    where
        T: LabelType,
    {
        let solver = Rc::new(RefCell::new((solver_factory)()));
        Self {
            af: AAFramework::new_with_argument_set(ArgumentSet::new_with_labels(&[])),
            buffered_encoder: BufferedDynamicConstraintsEncoder::new(
                Rc::clone(&solver),
                Semantics::ST,
            ),
            solver,
        }
    }
}

impl<T> Default for DynamicStableSemanticsSolver<T>
where
    T: LabelType,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<T> DynamicSolver<T> for DynamicStableSemanticsSolver<T>
where
    T: LabelType,
{
    fn new_argument(&mut self, label: T) {
        self.buffered_encoder.buffer_new_argument(label)
    }

    fn remove_argument(&mut self, label: &T) -> Result<()> {
        self.buffered_encoder.buffer_remove_argument(label)
    }

    fn new_attack(&mut self, from: &T, to: &T) -> Result<()> {
        self.buffered_encoder.buffer_new_attack(from, to)
    }

    fn remove_attack(&mut self, from: &T, to: &T) -> Result<()> {
        self.buffered_encoder.buffer_remove_attack(from, to)
    }
}

impl<T> CredulousAcceptanceComputer<T> for DynamicStableSemanticsSolver<T>
where
    T: LabelType,
{
    fn are_credulously_accepted_with_certificate(
        &mut self,
        args: &[&T],
    ) -> (bool, Option<Vec<&Argument<T>>>) {
        if args.len() > 1 {
            panic!("acceptance queries for more than one argument are not available for dynamic solvers");
        }
        let arg = args[0];
        if let (Some(b), Some(e)) = self.buffered_encoder.is_credulously_accepted(arg) {
            return (
                b,
                Some(
                    e.iter()
                        .map(|id| self.af.argument_set().get_argument_by_id(*id))
                        .collect(),
                ),
            );
        }
        self.buffered_encoder.update_encoding(&mut self.af);
        let encoder_ref = self.buffered_encoder.encoder();
        let mut assumptions = Vec::with_capacity(encoder_ref.assumptions().len() + 1);
        assumptions.append(&mut encoder_ref.assumptions().to_vec());
        assumptions.push(encoder_ref.arg_to_lit(&self.af, arg));
        match self
            .solver
            .borrow_mut()
            .solve_under_assumptions(&assumptions)
            .unwrap_model()
        {
            Some(m) => {
                let proved_accepted = m
                    .iter()
                    .filter_map(|(v, b)| {
                        if b != Some(false) {
                            if let Some(arg) = encoder_ref.solver_var_to_arg(&self.af, v) {
                                return Some(arg.label().clone());
                            }
                        }
                        None
                    })
                    .collect();
                let extension = encoder_ref.assignment_to_extension(&self.af, m);
                self.buffered_encoder.add_credulous_computation(
                    proved_accepted,
                    vec![],
                    Some(extension.clone()),
                );
                (true, Some(extension))
            }
            None => {
                self.buffered_encoder
                    .add_credulous_computation(vec![], vec![arg.clone()], None);
                (false, None)
            }
        }
    }

    fn are_credulously_accepted(&mut self, args: &[&T]) -> bool {
        self.are_credulously_accepted_with_certificate(args).0
    }
}

impl<T> SkepticalAcceptanceComputer<T> for DynamicStableSemanticsSolver<T>
where
    T: LabelType,
{
    fn are_skeptically_accepted_with_certificate(
        &mut self,
        args: &[&T],
    ) -> (bool, Option<Vec<&Argument<T>>>) {
        if args.len() > 1 {
            panic!("acceptance queries for more than one argument are not available for dynamic solvers");
        }
        let arg = args[0];
        if let (Some(b), Some(e)) = self.buffered_encoder.is_skeptically_accepted(arg) {
            return (
                b,
                Some(
                    e.iter()
                        .map(|id| self.af.argument_set().get_argument_by_id(*id))
                        .collect(),
                ),
            );
        }
        self.buffered_encoder.update_encoding(&mut self.af);
        let encoder_ref = self.buffered_encoder.encoder();
        let mut assumptions = Vec::with_capacity(encoder_ref.assumptions().len() + 1);
        assumptions.append(&mut encoder_ref.assumptions().to_vec());
        assumptions.push(encoder_ref.arg_to_lit(&self.af, arg).negate());
        match self
            .solver
            .borrow_mut()
            .solve_under_assumptions(&assumptions)
            .unwrap_model()
        {
            Some(m) => {
                let proved_refused = m
                    .iter()
                    .filter_map(|(v, b)| {
                        if b != Some(true) {
                            if let Some(arg) = encoder_ref.solver_var_to_arg(&self.af, v) {
                                return Some(arg.label().clone());
                            }
                        }
                        None
                    })
                    .collect();
                let extension = encoder_ref.assignment_to_extension(&self.af, m);
                self.buffered_encoder.add_skeptical_computation(
                    vec![],
                    proved_refused,
                    Some(extension.clone()),
                );
                (false, Some(extension))
            }
            None => {
                let proved_refused = self
                    .af
                    .iter_attacks_from(self.af.argument_set().get_argument(arg).unwrap())
                    .map(|att| att.attacked().label().clone())
                    .collect();
                self.buffered_encoder.add_skeptical_computation(
                    vec![arg.clone()],
                    proved_refused,
                    None,
                );
                (true, None)
            }
        }
    }

    fn are_skeptically_accepted(&mut self, args: &[&T]) -> bool {
        return self.are_skeptically_accepted_with_certificate(args).0;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn coreo_test() {
        let mut solver = DynamicStableSemanticsSolver::new();
        solver.new_argument(1);
        solver.new_argument(2);
        solver.new_attack(&1, &2).unwrap();
        assert!(solver.is_credulously_accepted(&1));
        assert!(!solver.is_credulously_accepted(&2));
        assert!(solver.is_skeptically_accepted(&1));
        assert!(!solver.is_skeptically_accepted(&2));

        solver.remove_attack(&1, &2).unwrap();
        assert!(solver.is_credulously_accepted(&1));
        assert!(solver.is_credulously_accepted(&2));
        assert!(solver.is_skeptically_accepted(&1));
        assert!(solver.is_skeptically_accepted(&2));

        solver.new_argument(3);
        solver.new_attack(&3, &2).unwrap();
        solver.new_attack(&2, &1).unwrap();
        assert!(solver.is_credulously_accepted(&1));
        assert!(!solver.is_credulously_accepted(&2));
        assert!(solver.is_credulously_accepted(&3));
        assert!(solver.is_skeptically_accepted(&1));
        assert!(!solver.is_skeptically_accepted(&2));
        assert!(solver.is_skeptically_accepted(&3));

        solver.remove_argument(&1).unwrap();
        solver.new_argument(4);
        solver.new_attack(&4, &3).unwrap();
        solver.new_attack(&3, &4).unwrap();
        assert!(solver.is_credulously_accepted(&2));
        assert!(solver.is_credulously_accepted(&3));
        assert!(solver.is_credulously_accepted(&4));
        assert!(!solver.is_skeptically_accepted(&2));
        assert!(!solver.is_skeptically_accepted(&3));
        assert!(!solver.is_skeptically_accepted(&4));
    }
}
