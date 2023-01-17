use super::{
    buffered_dynamic_constraints_encoder::BufferedDynamicConstraintsEncoder, DynamicSolver,
};
use crate::{
    aa::{Argument, Semantics},
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
    fn is_credulously_accepted(&mut self, arg: &T) -> bool {
        if let Some(b) = self.buffered_encoder.is_credulously_accepted(arg) {
            return b;
        }
        let encoder_ref = self.buffered_encoder.encoder();
        let mut assumptions = Vec::with_capacity(encoder_ref.assumptions().len() + 1);
        assumptions.append(&mut encoder_ref.assumptions().to_vec());
        assumptions.push(encoder_ref.arg_to_lit(arg));
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
                            if let Some(arg) = encoder_ref.solver_var_to_arg(v) {
                                return Some(arg.label().clone());
                            }
                        }
                        None
                    })
                    .collect();
                std::mem::drop(encoder_ref);
                self.buffered_encoder
                    .add_credulous_computation(proved_accepted, vec![]);
                true
            }
            None => {
                std::mem::drop(encoder_ref);
                self.buffered_encoder
                    .add_credulous_computation(vec![], vec![arg.clone()]);
                false
            }
        }
    }

    fn is_credulously_accepted_with_certificate(
        &mut self,
        _arg: &T,
    ) -> (bool, Option<Vec<&Argument<T>>>) {
        unimplemented!()
    }
}

impl<T> SkepticalAcceptanceComputer<T> for DynamicStableSemanticsSolver<T>
where
    T: LabelType,
{
    fn is_skeptically_accepted(&mut self, arg: &T) -> bool {
        if let Some(b) = self.buffered_encoder.is_skeptically_accepted(arg) {
            return b;
        }
        let encoder_ref = self.buffered_encoder.encoder();
        let mut assumptions = Vec::with_capacity(encoder_ref.assumptions().len() + 1);
        assumptions.append(&mut encoder_ref.assumptions().to_vec());
        assumptions.push(encoder_ref.arg_to_lit(arg).negate());
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
                            if let Some(arg) = encoder_ref.solver_var_to_arg(v) {
                                return Some(arg.label().clone());
                            }
                        }
                        None
                    })
                    .collect();
                std::mem::drop(encoder_ref);
                self.buffered_encoder
                    .add_skeptical_computation(vec![], proved_refused);
                false
            }
            None => {
                let proved_refused = encoder_ref
                    .af()
                    .iter_attacks_from(encoder_ref.af().argument_set().get_argument(arg).unwrap())
                    .map(|att| att.attacked().label().clone())
                    .collect();
                std::mem::drop(encoder_ref);
                self.buffered_encoder
                    .add_skeptical_computation(vec![arg.clone()], proved_refused);
                true
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
