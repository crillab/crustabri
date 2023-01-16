use super::{
    buffered_dynamic_constraints_encoder::BufferedDynamicConstraintsEncoder,
    dynamic_constraints_encoder::DynamicConstraintsEncoder, DynamicSolver,
};
use crate::{
    aa::{AAFramework, Argument, Semantics},
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
    buffered_encoder: BufferedDynamicConstraintsEncoder<T>,
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
            buffered_encoder: BufferedDynamicConstraintsEncoder::new(
                Rc::clone(&solver),
                Semantics::PR,
            ),
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
        if let Some(b) = self.buffered_encoder.is_skeptically_accepted(arg) {
            return b;
        }
        let encoder_ref = self.buffered_encoder.encoder();
        let constraints_encoder = LocalConstraintsEncoder {
            encoder: &encoder_ref,
        };
        let mut computer = maximal_extension_computer::new_for_preferred_semantics(
            encoder_ref.af(),
            Rc::clone(&self.solver),
            &constraints_encoder,
        );
        computer.set_additional_assumptions(encoder_ref.assumptions().to_vec());
        let arg = encoder_ref.af().argument_set().get_argument(arg).unwrap();
        let mut first_maximal = true;
        let mut in_all_maximal = None;
        let mut missing_in_one_maximal =
            vec![false; 1 + encoder_ref.af().max_argument_id().unwrap_or_default()];
        let bool_slice_to_labels = |v: &[bool]| {
            v.iter()
                .enumerate()
                .filter_map(|(i, b)| {
                    if *b && encoder_ref.af().argument_set().has_argument_with_id(i) {
                        Some(
                            encoder_ref
                                .af()
                                .argument_set()
                                .get_argument_by_id(i)
                                .label()
                                .clone(),
                        )
                    } else {
                        None
                    }
                })
                .collect()
        };
        let (result, proved_accepted_bool, proved_refused_bool) = loop {
            computer.compute_next();
            match computer.state() {
                MaximalExtensionComputerState::Maximal => {
                    let mut in_current =
                        vec![false; 1 + encoder_ref.af().max_argument_id().unwrap_or_default()];
                    computer.current().iter().for_each(|a| {
                        in_current[a.id()] = true;
                    });
                    let arg_is_missing = !in_current[arg.id()];
                    if first_maximal {
                        in_all_maximal = Some(in_current);
                    } else {
                        let in_all_maximal_ref = in_all_maximal.as_mut().unwrap().as_mut_slice();
                        in_current.iter().enumerate().for_each(|(i, b)| {
                            if !b {
                                in_all_maximal_ref[i] = false;
                                missing_in_one_maximal[i] = true;
                            }
                        });
                    }
                    first_maximal = false;
                    if arg_is_missing {
                        break (false, vec![], missing_in_one_maximal);
                    }
                }
                MaximalExtensionComputerState::Intermediate => {
                    let current = computer.current();
                    if current.contains(&arg) {
                        computer.discard_current_search();
                    } else if encoder_ref
                        .af()
                        .iter_attacks_to(arg)
                        .any(|att| current.contains(&att.attacker()))
                    {
                        break (false, vec![], missing_in_one_maximal);
                    }
                }
                MaximalExtensionComputerState::None => {
                    break (
                        true,
                        in_all_maximal.unwrap_or_default(),
                        missing_in_one_maximal,
                    );
                }
                _ => {}
            }
        };
        let proved_accepted = bool_slice_to_labels(&proved_accepted_bool);
        let proved_refused = bool_slice_to_labels(&proved_refused_bool);
        std::mem::drop(computer);
        std::mem::drop(encoder_ref);
        self.buffered_encoder
            .add_skeptical_computation(proved_accepted, proved_refused);
        result
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