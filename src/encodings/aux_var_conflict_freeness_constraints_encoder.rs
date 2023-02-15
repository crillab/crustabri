use super::{AuxVarCompleteConstraintsEncoder, ConstraintsEncoder};
use crate::{
    aa::{AAFramework, Argument},
    sat::{clause, Assignment, Literal, SatSolver},
    utils::{Label, LabelType},
};

/// An encoder for the conflict-freeness based semantics adding auxiliary variables to make it polynomial.
#[derive(Default)]
pub struct AuxVarConflictFreenessConstraintsEncoder;

impl AuxVarConflictFreenessConstraintsEncoder {
    fn encode_attack_constraints_for_arg<T>(
        af: &AAFramework<T>,
        solver: &mut dyn SatSolver,
        arg: &Label<T>,
    ) where
        T: LabelType,
    {
        let attacked_id = arg.id();
        let attacked_solver_var =
            AuxVarCompleteConstraintsEncoder::arg_id_to_solver_var(attacked_id) as isize;
        af.iter_attacks_to(arg).for_each(|att| {
            let attacker_id = att.attacker().id();
            let attacker_solver_var =
                AuxVarCompleteConstraintsEncoder::arg_id_to_solver_var(attacker_id) as isize;
            solver.add_clause(clause![-attacked_solver_var, -attacker_solver_var,]);
        });
    }
}

impl<T> ConstraintsEncoder<T> for AuxVarConflictFreenessConstraintsEncoder
where
    T: LabelType,
{
    fn encode_constraints(&self, af: &AAFramework<T>, solver: &mut dyn SatSolver) {
        af.argument_set().iter().for_each(|arg| {
            Self::encode_attack_constraints_for_arg(af, solver, arg);
        });
    }

    fn encode_constraints_and_range(&self, af: &AAFramework<T>, solver: &mut dyn SatSolver) {
        af.argument_set().iter().for_each(|arg| {
            Self::encode_attack_constraints_for_arg(af, solver, arg);
            AuxVarCompleteConstraintsEncoder::encode_disjunction_var(af, solver, arg);
            AuxVarCompleteConstraintsEncoder::encode_range_constraint(
                solver,
                arg,
                af.n_arguments(),
            );
        });
    }

    fn first_range_var(&self, n_args: usize) -> usize {
        AuxVarCompleteConstraintsEncoder::arg_id_to_range_var(n_args, 0)
    }

    fn assignment_to_extension<'a>(
        &self,
        assignment: &Assignment,
        af: &'a AAFramework<T>,
    ) -> Vec<&'a Argument<T>> {
        assignment
            .iter()
            .filter_map(|(var, opt_v)| match opt_v {
                Some(true) => AuxVarCompleteConstraintsEncoder::arg_id_from_solver_var(var)
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
        Literal::from(AuxVarCompleteConstraintsEncoder::arg_id_to_solver_var(arg.id()) as isize)
    }
}
