use std::{cell::RefCell, rc::Rc};

use super::{aux_var_constraints_encoder, exp_constraints_encoder, ConstraintsEncoder};
use crate::{
    aa::{AAFramework, Argument},
    sat::{clause, Assignment, Literal, SatSolver},
    utils::{Label, LabelType},
};

const DEFENDER_SETS_PROD_THRESHOLD: usize = 1 << 5;

/// An encoder that mix `aux_var` and `exp` encodings depending on the number of clauses to generate.
#[derive(Default)]
pub struct HybridCompleteConstraintsEncoder {
    attacker_disjunction_vars: Rc<RefCell<Vec<Option<usize>>>>,
    next_free_var_id: Rc<RefCell<usize>>,
}

impl HybridCompleteConstraintsEncoder {
    fn encode_attack_constraints_for_arg<T>(
        af: &AAFramework<T>,
        solver: &mut dyn SatSolver,
        arg: &Label<T>,
        attacker_disjunction_vars: Rc<RefCell<Vec<Option<usize>>>>,
        next_free_var_id: Rc<RefCell<usize>>,
    ) where
        T: LabelType,
    {
        let attacked_id = arg.id();
        let attacked_solver_var = Self::arg_id_to_solver_var(attacked_id) as isize;
        let (defender_sets, conflict_freeness_clauses) =
            exp_constraints_encoder::compute_defender_sets(af, arg);
        if defender_sets.is_empty() {
            solver.add_clause(clause![attacked_solver_var]);
            return;
        }
        if defender_sets.iter().any(|s| s.is_empty()) {
            solver.add_clause(clause![-attacked_solver_var]);
            return;
        }
        let mut product = 1;
        for s in &defender_sets {
            product *= s.len();
            if product >= DEFENDER_SETS_PROD_THRESHOLD {
                break;
            }
        }
        if product < DEFENDER_SETS_PROD_THRESHOLD {
            exp_constraints_encoder::encode_nontrivial_attack_constraints_for_arg(
                arg,
                solver,
                defender_sets,
                conflict_freeness_clauses,
            );
        } else {
            Self::create_attacker_disjunction_vars_for_attackers_of(
                af,
                solver,
                Rc::clone(&attacker_disjunction_vars),
                Rc::clone(&next_free_var_id),
                arg,
            );
            aux_var_constraints_encoder::encode_complete_semantics_attack_constraints_for_arg(
                af,
                solver,
                arg,
                &Self::arg_id_to_solver_var,
                &|id| {
                    Self::arg_id_to_solver_disjunction_var(
                        Rc::clone(&attacker_disjunction_vars),
                        id,
                    )
                    .unwrap()
                },
            );
        }
    }

    pub(crate) fn encode_range_constraint<T>(
        af: &AAFramework<T>,
        solver: &mut dyn SatSolver,
        arg: &Label<T>,
        n_args: usize,
        attacker_disjunction_vars: Rc<RefCell<Vec<Option<usize>>>>,
    ) where
        T: LabelType,
    {
        let opt_var = attacker_disjunction_vars.borrow()[arg.id()];
        if let Some(att_disj_var) = opt_var {
            let att_disj_lit = att_disj_var as isize;
            let range_var = Self::arg_id_to_range_var(n_args, arg.id()) as isize;
            let arg_var = Self::arg_id_to_solver_var(arg.id()) as isize;
            solver.add_clause(clause!(-arg_var, range_var));
            solver.add_clause(clause!(-att_disj_lit, range_var));
            solver.add_clause(clause!(-range_var, arg_var, att_disj_lit));
        } else {
            let range_var = Self::arg_id_to_range_var(n_args, arg.id()) as isize;
            let arg_var = Self::arg_id_to_solver_var(arg.id()) as isize;
            solver.add_clause(clause![-arg_var, range_var]);
            let mut full_cl = vec![Literal::from(range_var).negate(), Literal::from(arg_var)];
            af.iter_attacks_to(arg).for_each(|att| {
                full_cl.push(Literal::from(
                    Self::arg_id_to_solver_var(att.attacker().id()) as isize,
                ));
            });
            solver.add_clause(full_cl);
        }
    }

    pub(crate) fn arg_id_to_solver_var(id: usize) -> usize {
        id + 1
    }

    pub(crate) fn arg_id_from_solver_var(v: usize) -> Option<usize> {
        Some(v - 1)
    }

    pub(crate) fn arg_id_to_range_var(n_args: usize, id: usize) -> usize {
        n_args + id + 1
    }

    fn arg_id_to_solver_disjunction_var(
        attacker_disjunction_vars: Rc<RefCell<Vec<Option<usize>>>>,
        id: usize,
    ) -> Option<usize> {
        attacker_disjunction_vars.borrow()[id]
    }

    fn create_attacker_disjunction_vars_for_attackers_of<T>(
        af: &AAFramework<T>,
        solver: &mut dyn SatSolver,
        attacker_disjunction_vars: Rc<RefCell<Vec<Option<usize>>>>,
        next_free_var_id: Rc<RefCell<usize>>,
        arg: &Label<T>,
    ) where
        T: LabelType,
    {
        af.iter_attacks_to(arg).for_each(|att| {
            let attacker_id = att.attacker().id();
            let opt_var = attacker_disjunction_vars.borrow()[attacker_id];
            if opt_var.is_some() {
                return;
            }
            let disjunction_var = *next_free_var_id.borrow();
            *next_free_var_id.borrow_mut() += 1;
            attacker_disjunction_vars.borrow_mut()[attacker_id] = Some(disjunction_var);
            aux_var_constraints_encoder::encode_disjunction_var_with(
                af,
                solver,
                att.attacker(),
                disjunction_var as isize,
                &Self::arg_id_to_solver_var,
            )
        });
    }
}

impl<T> ConstraintsEncoder<T> for HybridCompleteConstraintsEncoder
where
    T: LabelType,
{
    fn encode_constraints(&self, af: &AAFramework<T>, solver: &mut dyn SatSolver) {
        solver.reserve(af.n_arguments());
        *self.attacker_disjunction_vars.borrow_mut() = vec![None; af.n_arguments()];
        *self.next_free_var_id.borrow_mut() = 1 + af.n_arguments();
        af.argument_set().iter().for_each(|arg| {
            Self::encode_attack_constraints_for_arg(
                af,
                solver,
                arg,
                Rc::clone(&self.attacker_disjunction_vars),
                Rc::clone(&self.next_free_var_id),
            );
        });
    }

    fn encode_constraints_and_range(&self, af: &AAFramework<T>, solver: &mut dyn SatSolver) {
        solver.reserve(af.n_arguments() << 1);
        *self.attacker_disjunction_vars.borrow_mut() = vec![None; af.n_arguments()];
        *self.next_free_var_id.borrow_mut() = 1 + (af.n_arguments() << 1);
        af.argument_set().iter().for_each(|arg| {
            Self::encode_attack_constraints_for_arg(
                af,
                solver,
                arg,
                Rc::clone(&self.attacker_disjunction_vars),
                Rc::clone(&self.next_free_var_id),
            );
            Self::encode_range_constraint(
                af,
                solver,
                arg,
                af.n_arguments(),
                Rc::clone(&self.attacker_disjunction_vars),
            );
        });
    }

    fn first_range_var(&self, n_args: usize) -> usize {
        Self::arg_id_to_range_var(n_args, 0)
    }

    fn assignment_to_extension<'a>(
        &self,
        assignment: &Assignment,
        af: &'a AAFramework<T>,
    ) -> Vec<&'a Argument<T>> {
        assignment
            .iter()
            .filter_map(|(var, opt_v)| match opt_v {
                Some(true) => Self::arg_id_from_solver_var(var)
                    .and_then(|id| {
                        if id < af.n_arguments() {
                            Some(id)
                        } else {
                            None
                        }
                    })
                    .map(|id| af.argument_set().get_argument_by_id(id)),
                _ => None,
            })
            .collect()
    }

    fn arg_to_lit(&self, arg: &Argument<T>) -> Literal {
        Literal::from(Self::arg_id_to_solver_var(arg.id()) as isize)
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        aa::{AAFramework, ArgumentSet},
        encodings::{ConstraintsEncoder, HybridCompleteConstraintsEncoder},
        sat::default_solver,
    };

    #[test]
    fn test_no_attacks() {
        let af = AAFramework::new_with_argument_set(ArgumentSet::new_with_labels(&["a0"]));
        let encoder = HybridCompleteConstraintsEncoder::default();
        let mut solver = default_solver();
        encoder.encode_constraints(&af, solver.as_mut());
        assert_ne!(solver.n_vars(), 0);
    }
}
