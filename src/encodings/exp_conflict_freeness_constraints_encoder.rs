use super::{ConstraintsEncoder, ExpCompleteConstraintsEncoder};
use crate::{
    aa::{AAFramework, Argument},
    sat::{clause, Assignment, Literal, SatSolver},
    utils::{Label, LabelType},
};

/// An encoder for the conflict-freeness based semantics adding auxiliary variables to make it polynomial.
#[derive(Default)]
pub struct ExpConflictFreenessConstraintsEncoder;

impl ExpConflictFreenessConstraintsEncoder {
    fn encode_attack_constraints_for_arg<T>(
        af: &AAFramework<T>,
        solver: &mut dyn SatSolver,
        arg: &Label<T>,
    ) where
        T: LabelType,
    {
        let attacked_id = arg.id();
        let attacked_solver_var =
            ExpCompleteConstraintsEncoder::arg_id_to_solver_var(attacked_id) as isize;
        af.iter_attacks_to(arg).for_each(|att| {
            let attacker_id = att.attacker().id();
            let attacker_solver_var =
                ExpCompleteConstraintsEncoder::arg_id_to_solver_var(attacker_id) as isize;
            solver.add_clause(clause![-attacked_solver_var, -attacker_solver_var]);
        });
    }
}

impl<T> ConstraintsEncoder<T> for ExpConflictFreenessConstraintsEncoder
where
    T: LabelType,
{
    fn encode_constraints(&self, af: &AAFramework<T>, solver: &mut dyn SatSolver) {
        solver.reserve(af.n_arguments());
        af.argument_set().iter().for_each(|arg| {
            Self::encode_attack_constraints_for_arg(af, solver, arg);
        });
    }

    fn encode_constraints_and_range(&self, af: &AAFramework<T>, solver: &mut dyn SatSolver) {
        solver.reserve(af.n_arguments() << 1);
        af.argument_set().iter().for_each(|arg| {
            Self::encode_attack_constraints_for_arg(af, solver, arg);
            ExpCompleteConstraintsEncoder::encode_range_constraint(
                af,
                solver,
                arg,
                af.n_arguments(),
            );
        });
    }

    fn first_range_var(&self, n_args: usize) -> usize {
        ExpCompleteConstraintsEncoder::arg_id_to_range_var(n_args, 0)
    }

    fn assignment_to_extension<'a>(
        &self,
        assignment: &Assignment,
        af: &'a AAFramework<T>,
    ) -> Vec<&'a Argument<T>> {
        assignment
            .iter()
            .filter_map(|(var, opt_v)| match opt_v {
                Some(true) => ExpCompleteConstraintsEncoder::arg_id_from_solver_var(var)
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
        Literal::from(ExpCompleteConstraintsEncoder::arg_id_to_solver_var(arg.id()) as isize)
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        aa::{AAFramework, ArgumentSet},
        encodings::{ConstraintsEncoder, ExpConflictFreenessConstraintsEncoder},
        sat::default_solver,
    };

    #[test]
    fn test_no_attacks() {
        let af = AAFramework::new_with_argument_set(ArgumentSet::new_with_labels(&["a0"]));
        let encoder = ExpConflictFreenessConstraintsEncoder::default();
        let mut solver = default_solver();
        encoder.encode_constraints(&af, solver.as_mut());
        assert_ne!(solver.n_vars(), 0);
    }
}
