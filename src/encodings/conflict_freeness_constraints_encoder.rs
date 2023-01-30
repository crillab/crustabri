use super::{ConstraintsEncoder, DefaultCompleteConstraintsEncoder};
use crate::{
    aa::{AAFramework, Argument},
    sat::{clause, Assignment, Literal, SatSolver},
    utils::{Label, LabelType},
};

/// The default encoder for the conflict-freeness based semantics.
#[derive(Default)]
pub struct DefaultConflictFreenessConstraintsEncoder;

impl DefaultConflictFreenessConstraintsEncoder {
    fn encode_attack_constraints_for_arg<T>(
        af: &AAFramework<T>,
        solver: &mut dyn SatSolver,
        arg: &Label<T>,
    ) where
        T: LabelType,
    {
        let attacked_id = arg.id();
        let attacked_solver_var =
            DefaultCompleteConstraintsEncoder::arg_id_to_solver_var(attacked_id) as isize;
        af.iter_attacks_to(arg).for_each(|att| {
            let attacker_id = att.attacker().id();
            let attacker_solver_var =
                DefaultCompleteConstraintsEncoder::arg_id_to_solver_var(attacker_id) as isize;
            solver.add_clause(clause![-attacked_solver_var, -attacker_solver_var,]);
        });
    }
}

impl<T> ConstraintsEncoder<T> for DefaultConflictFreenessConstraintsEncoder
where
    T: LabelType,
{
    fn encode_constraints(&self, af: &AAFramework<T>, solver: &mut dyn SatSolver) {
        af.argument_set().iter().for_each(|arg| {
            Self::encode_attack_constraints_for_arg(af, solver, arg);
            DefaultCompleteConstraintsEncoder::encode_disjunction_var(af, solver, arg);
        });
    }

    fn encode_constraints_and_range(&self, af: &AAFramework<T>, solver: &mut dyn SatSolver) {
        af.argument_set().iter().for_each(|arg| {
            Self::encode_attack_constraints_for_arg(af, solver, arg);
            DefaultCompleteConstraintsEncoder::encode_disjunction_var(af, solver, arg);
            DefaultCompleteConstraintsEncoder::encode_range_constraint(
                solver,
                arg,
                af.n_arguments(),
            );
        });
    }

    fn assignment_to_extension<'a>(
        &self,
        assignment: &Assignment,
        af: &'a AAFramework<T>,
    ) -> Vec<&'a Argument<T>> {
        assignment
            .iter()
            .filter_map(|(var, opt_v)| match opt_v {
                Some(true) => DefaultCompleteConstraintsEncoder::arg_id_from_solver_var(var)
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
        Literal::from(DefaultCompleteConstraintsEncoder::arg_id_to_solver_var(arg.id()) as isize)
    }
}
