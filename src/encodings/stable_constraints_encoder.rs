use super::ConstraintsEncoder;
use crate::{
    aa::{AAFramework, Argument},
    sat::{clause, Assignment, Literal, SatSolver},
    utils::LabelType,
};

/// The default encoder for the stable semantics.
#[derive(Default)]
pub struct DefaultStableConstraintsEncoder;

impl<T> ConstraintsEncoder<T> for DefaultStableConstraintsEncoder
where
    T: LabelType,
{
    fn encode_constraints(&self, af: &AAFramework<T>, solver: &mut dyn SatSolver) {
        af.argument_set().iter().for_each(|arg| {
            let attacked_id = arg.id();
            let attacked_solver_var = arg_id_to_solver_var(attacked_id) as isize;
            let mut full_cl = clause![attacked_solver_var];
            af.iter_attacks_to(arg).for_each(|att| {
                let attacker_id = att.attacker().id();
                if attacked_id == attacker_id {
                    solver.add_clause(clause![-attacked_solver_var])
                } else {
                    let attacker_solver_var = arg_id_to_solver_var(attacker_id) as isize;
                    solver.add_clause(clause![-attacked_solver_var, -attacker_solver_var]);
                    full_cl.push(attacker_solver_var.into());
                }
            });
            solver.add_clause(full_cl);
        });
    }

    fn encode_range_constraints(&self, _af: &AAFramework<T>, _solver: &mut dyn SatSolver) -> usize {
        unimplemented!()
    }

    fn assignment_to_extension<'a>(
        &self,
        assignment: &Assignment,
        af: &'a AAFramework<T>,
    ) -> Vec<&'a Argument<T>> {
        assignment
            .iter()
            .filter(|(_, val)| val.unwrap_or(false))
            .map(|(v, _)| {
                af.argument_set()
                    .get_argument_by_id(arg_id_from_solver_var(v))
            })
            .collect()
    }

    fn arg_to_lit(&self, arg: &Argument<T>) -> Literal {
        Literal::from(arg_id_to_solver_var(arg.id()) as isize)
    }
}

fn arg_id_to_solver_var(id: usize) -> usize {
    id + 1
}

fn arg_id_from_solver_var(var: usize) -> usize {
    var - 1
}
