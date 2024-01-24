use super::buffered_dynamic_constraints_encoder_attacks::BufferedDynamicConstraintsEncoder;
use crate::{
    aa::{AAFramework, Argument, ArgumentSet, Semantics},
    dynamics::DynamicSolver,
    sat::{self, SatSolver, SatSolverFactoryFn},
    solvers::{CredulousAcceptanceComputer, SkepticalAcceptanceComputer},
    utils::LabelType,
};
use anyhow::Result;
use std::{cell::RefCell, rc::Rc};

/// A dynamic solver dedicated to the complete semantics.
///
/// This solver sets assumptions variables on attacks, in the spirit of µ-Toksia at ICCMA'23.
/// When a new encoding occurs, a set of SAT variables is reserved for new arguments to come.
/// When the set of reserved arguments is exhausted, a re-encoding is made.
pub struct DynamicCompleteSemanticsSolverAttacks<T>
where
    T: LabelType,
{
    af: AAFramework<T>,
    buffered_encoder: BufferedDynamicConstraintsEncoder<T>,
    solver: Rc<RefCell<Box<dyn SatSolver>>>,
}

impl<T> DynamicCompleteSemanticsSolverAttacks<T>
where
    T: LabelType,
{
    /// Builds a new SAT based dynamic solver for the complete semantics.
    ///
    /// The underlying SAT solver is one returned by [default_solver](crate::sat::default_solver).
    ///
    /// When encoding a problem, the number of reserved arguments is equal to the current number of arguments.
    pub fn new() -> Self
    where
        T: LabelType,
    {
        Self::new_with_sat_solver_factory_and_arg_factor(Box::new(|| sat::default_solver()), 2.)
    }

    /// Builds a new SAT based dynamic solver for the complete semantics.
    ///
    /// The underlying SAT solver is one returned by [default_solver](crate::sat::default_solver).
    ///
    /// For `n` arguments at the moment the problem is encoded, `n*(factor -1)` additional arguments are reserved.
    pub fn new_with_arg_factor(arg_factor: f64) -> Self
    where
        T: LabelType,
    {
        Self::new_with_sat_solver_factory_and_arg_factor(
            Box::new(|| sat::default_solver()),
            arg_factor,
        )
    }

    /// Builds a new SAT based dynamic solver for the complete semantics.
    ///
    /// The SAT solver to use in given through the solver factory.
    pub fn new_with_sat_solver_factory_and_arg_factor(
        solver_factory: Box<SatSolverFactoryFn>,
        arg_factor: f64,
    ) -> Self
    where
        T: LabelType,
    {
        let solver = Rc::new(RefCell::new((solver_factory)()));
        Self {
            af: AAFramework::new_with_argument_set(ArgumentSet::new_with_labels(&[])),
            buffered_encoder: BufferedDynamicConstraintsEncoder::new_with_arg_factor(
                Rc::clone(&solver),
                solver_factory,
                Semantics::CO,
                arg_factor,
            ),
            solver,
        }
    }
}

impl<T> Default for DynamicCompleteSemanticsSolverAttacks<T>
where
    T: LabelType,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<T> DynamicSolver<T> for DynamicCompleteSemanticsSolverAttacks<T>
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

impl<T> CredulousAcceptanceComputer<T> for DynamicCompleteSemanticsSolverAttacks<T>
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
        let mut assumptions = Vec::new();
        assumptions.append(&mut encoder_ref.assumptions(&self.af).to_vec());
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
                            if let Some(arg) = self
                                .buffered_encoder
                                .encoder()
                                .solver_var_to_arg(&self.af, v)
                            {
                                return Some(arg.label().clone());
                            }
                        }
                        None
                    })
                    .collect();
                let extension = self
                    .buffered_encoder
                    .encoder()
                    .assignment_to_extension(&self.af, m);
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

impl<T> SkepticalAcceptanceComputer<T> for DynamicCompleteSemanticsSolverAttacks<T>
where
    T: LabelType,
{
    fn are_skeptically_accepted(&mut self, _args: &[&T]) -> bool {
        unimplemented!()
    }

    fn are_skeptically_accepted_with_certificate(
        &mut self,
        _args: &[&T],
    ) -> (bool, Option<Vec<&Argument<T>>>) {
        unimplemented!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn coreo_test() {
        let mut solver = DynamicCompleteSemanticsSolverAttacks::new();
        solver.new_argument(1);
        solver.new_argument(2);
        solver.new_attack(&1, &2).unwrap();
        assert!(solver.is_credulously_accepted(&1));
        assert!(!solver.is_credulously_accepted(&2));

        solver.remove_attack(&1, &2).unwrap();
        assert!(solver.is_credulously_accepted(&1));
        assert!(solver.is_credulously_accepted(&2));

        solver.new_argument(3);
        solver.new_attack(&3, &2).unwrap();
        solver.new_attack(&2, &1).unwrap();
        assert!(solver.is_credulously_accepted(&1));
        assert!(!solver.is_credulously_accepted(&2));
        assert!(solver.is_credulously_accepted(&3));

        solver.remove_argument(&1).unwrap();
        solver.new_argument(4);
        solver.new_attack(&4, &3).unwrap();
        solver.new_attack(&3, &4).unwrap();
        assert!(solver.is_credulously_accepted(&2));
        assert!(solver.is_credulously_accepted(&3));
        assert!(solver.is_credulously_accepted(&4));
    }

    #[test]
    fn coreo_test_1_5() {
        let mut solver = DynamicCompleteSemanticsSolverAttacks::new_with_arg_factor(1.5);
        solver.new_argument(1);
        solver.new_argument(2);
        solver.new_attack(&1, &2).unwrap();
        assert!(solver.is_credulously_accepted(&1));
        assert!(!solver.is_credulously_accepted(&2));

        solver.remove_attack(&1, &2).unwrap();
        assert!(solver.is_credulously_accepted(&1));
        assert!(solver.is_credulously_accepted(&2));

        solver.new_argument(3);
        solver.new_attack(&3, &2).unwrap();
        solver.new_attack(&2, &1).unwrap();
        assert!(solver.is_credulously_accepted(&1));
        assert!(!solver.is_credulously_accepted(&2));
        assert!(solver.is_credulously_accepted(&3));

        solver.remove_argument(&1).unwrap();
        solver.new_argument(4);
        solver.new_attack(&4, &3).unwrap();
        solver.new_attack(&3, &4).unwrap();
        assert!(solver.is_credulously_accepted(&2));
        assert!(solver.is_credulously_accepted(&3));
        assert!(solver.is_credulously_accepted(&4));
    }

    #[test]
    fn coreo_test_1_25() {
        let mut solver = DynamicCompleteSemanticsSolverAttacks::new_with_arg_factor(1.25);
        solver.new_argument(1);
        solver.new_argument(2);
        solver.new_attack(&1, &2).unwrap();
        assert!(solver.is_credulously_accepted(&1));
        assert!(!solver.is_credulously_accepted(&2));

        solver.remove_attack(&1, &2).unwrap();
        assert!(solver.is_credulously_accepted(&1));
        assert!(solver.is_credulously_accepted(&2));

        solver.new_argument(3);
        solver.new_attack(&3, &2).unwrap();
        solver.new_attack(&2, &1).unwrap();
        assert!(solver.is_credulously_accepted(&1));
        assert!(!solver.is_credulously_accepted(&2));
        assert!(solver.is_credulously_accepted(&3));

        solver.remove_argument(&1).unwrap();
        solver.new_argument(4);
        solver.new_attack(&4, &3).unwrap();
        solver.new_attack(&3, &4).unwrap();
        assert!(solver.is_credulously_accepted(&2));
        assert!(solver.is_credulously_accepted(&3));
        assert!(solver.is_credulously_accepted(&4));
    }

    #[test]
    fn test_del_unencoded_arg() {
        let mut solver = DynamicCompleteSemanticsSolverAttacks::new();
        solver.new_argument(1);
        solver.new_argument(2);
        solver.remove_argument(&2).unwrap();
        assert!(solver.is_credulously_accepted_with_certificate(&1).0);
    }
}
