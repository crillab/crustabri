use super::{
    buffered_dynamic_constraints_encoder::BufferedDynamicConstraintsEncoder,
    dynamic_constraints_encoder::DynamicConstraintsEncoder, DynamicSolver,
};
use crate::{
    aa::{AAFramework, Argument, ArgumentSet, Semantics},
    encodings::ConstraintsEncoder,
    sat::{self, Assignment, Literal, SatSolver, SatSolverFactoryFn},
    solvers::{
        maximal_extension_computer::{
            self, MaximalExtensionComputer, MaximalExtensionComputerState,
        },
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
    af: AAFramework<T>,
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
            af: AAFramework::new_with_argument_set(ArgumentSet::new_with_labels(&[])),
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
    fn are_credulously_accepted(&mut self, _args: &[&T]) -> bool {
        unimplemented!()
    }

    fn are_credulously_accepted_with_certificate(
        &mut self,
        _args: &[&T],
    ) -> (bool, Option<Vec<&Argument<T>>>) {
        unimplemented!()
    }
}

impl<T> SkepticalAcceptanceComputer<T> for DynamicPreferredSemanticsSolver<T>
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
        let constraints_encoder = LocalConstraintsEncoder {
            encoder: encoder_ref,
            af: &self.af,
        };
        let mut computer = maximal_extension_computer::new_for_preferred_semantics(
            &self.af,
            Rc::clone(&self.solver),
            &constraints_encoder,
        );
        computer.set_additional_assumptions(encoder_ref.assumptions().to_vec());
        let arg = self.af.argument_set().get_argument(arg).unwrap();
        let mut first_maximal = true;
        let mut in_all_maximal = None;
        let mut missing_in_one_maximal =
            vec![false; 1 + self.af.max_argument_id().unwrap_or_default()];
        let bool_slice_to_labels = |v: &[bool]| {
            v.iter()
                .enumerate()
                .filter_map(|(i, b)| {
                    if *b && self.af.argument_set().has_argument_with_id(i) {
                        Some(self.af.argument_set().get_argument_by_id(i).label().clone())
                    } else {
                        None
                    }
                })
                .collect()
        };
        let compute_in_current_bool = |c: &MaximalExtensionComputer<T>| {
            let mut in_current = vec![false; 1 + self.af.max_argument_id().unwrap_or_default()];
            c.current().iter().for_each(|a| {
                in_current[a.id()] = true;
            });
            in_current
        };
        let add_defeated_in_current_to_missing =
            |c: &MaximalExtensionComputer<T>, m: &mut [bool]| {
                c.current().iter().for_each(|attacker| {
                    self.af
                        .iter_attacks_from_id(attacker.id())
                        .for_each(|att| m[att.attacked().id()] = true);
                });
            };
        let (result, proved_accepted_bool, proved_refused_bool, extension) = loop {
            computer.compute_next();
            match computer.state() {
                MaximalExtensionComputerState::Maximal => {
                    let in_current = compute_in_current_bool(&computer);
                    add_defeated_in_current_to_missing(&computer, &mut missing_in_one_maximal);
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
                        break (
                            false,
                            vec![],
                            missing_in_one_maximal,
                            Some(computer.current().to_vec()),
                        );
                    }
                }
                MaximalExtensionComputerState::Intermediate => {
                    let current = computer.current();
                    add_defeated_in_current_to_missing(&computer, &mut missing_in_one_maximal);
                    if current.contains(&arg) {
                        if first_maximal {
                            let in_current = compute_in_current_bool(&computer);
                            in_all_maximal = Some(in_current);
                        }
                        first_maximal = false;
                        computer.discard_current_search();
                    }
                }
                MaximalExtensionComputerState::None => {
                    break (
                        true,
                        in_all_maximal.unwrap_or_default(),
                        missing_in_one_maximal,
                        None,
                    );
                }
                _ => {}
            }
        };
        let proved_accepted = bool_slice_to_labels(&proved_accepted_bool);
        let proved_refused = bool_slice_to_labels(&proved_refused_bool);
        std::mem::drop(computer);
        self.buffered_encoder.add_skeptical_computation(
            proved_accepted,
            proved_refused,
            extension.clone(),
        );
        (result, extension)
    }

    fn are_skeptically_accepted(&mut self, args: &[&T]) -> bool {
        self.are_skeptically_accepted_with_certificate(args).0
    }
}

struct LocalConstraintsEncoder<'a, T>
where
    T: LabelType,
{
    encoder: &'a DynamicConstraintsEncoder,
    af: &'a AAFramework<T>,
}

impl<T> ConstraintsEncoder<T> for LocalConstraintsEncoder<'_, T>
where
    T: LabelType,
{
    fn encode_constraints(&self, _af: &AAFramework<T>, _solver: &mut dyn sat::SatSolver) {
        unimplemented!()
    }

    fn encode_constraints_and_range(&self, _af: &AAFramework<T>, _solver: &mut dyn sat::SatSolver) {
        unimplemented!()
    }

    fn first_range_var(&self, _n_args: usize) -> usize {
        unimplemented!()
    }

    fn assignment_to_extension<'a>(
        &self,
        assignment: &Assignment,
        af: &'a AAFramework<T>,
    ) -> Vec<&'a Argument<T>> {
        assignment
            .iter()
            .filter_map(|(var, opt_v)| match opt_v {
                Some(true) => self.encoder.solver_var_to_arg(af, var),
                _ => None,
            })
            .collect()
    }

    fn arg_to_lit(&self, arg: &Argument<T>) -> Literal {
        self.encoder.arg_to_lit(self.af, arg.label())
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

    #[test]
    fn test_wrong_witness() {
        let mut solver = DynamicPreferredSemanticsSolver::new();
        solver.new_argument(28);
        assert!(solver.is_skeptically_accepted(&28));
        solver.new_argument(41);
        solver.new_attack(&28, &41).unwrap();
        let (status, witness) = solver.is_skeptically_accepted_with_certificate(&41);
        assert!(!status);
        assert_eq!(1, witness.unwrap().len());
    }
}
