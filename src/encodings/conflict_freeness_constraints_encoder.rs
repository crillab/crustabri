use super::ConstraintsEncoder;
use crate::{
    aa::{AAFramework, Argument},
    sat::{clause, Assignment, Literal, SatSolver},
    utils::LabelType,
};

/// The default encoder for the conflict-freeness based semantics.
#[derive(Default)]
pub struct DefaultConflictFreenessConstraintsEncoder;

impl DefaultConflictFreenessConstraintsEncoder {
    fn encode_disjunction_vars<T>(&self, af: &AAFramework<T>, solver: &mut dyn SatSolver)
    where
        T: LabelType,
    {
        af.argument_set().iter().for_each(|arg| {
            let attacked_id = arg.id();
            let attacked_solver_var = arg_id_to_solver_var(attacked_id) as isize;
            let attacked_disjunction_solver_var =
                self.arg_id_to_solver_disjunction_var(attacked_id) as isize;
            solver.add_clause(clause![
                -attacked_solver_var,
                -attacked_disjunction_solver_var
            ]);
            let mut full_cl = clause![-attacked_disjunction_solver_var];
            af.iter_attacks_to(arg).for_each(|att| {
                let attacker_id = att.attacker().id();
                let attacker_solver_var = arg_id_to_solver_var(attacker_id) as isize;
                solver.add_clause(clause![
                    attacked_disjunction_solver_var,
                    -attacker_solver_var
                ]);
                full_cl.push(attacker_solver_var.into());
            });
            solver.add_clause(full_cl)
        });
    }

    fn arg_id_to_solver_disjunction_var(&self, id: usize) -> usize {
        arg_id_to_solver_var(id) - 1
    }

    fn arg_id_from_solver_var(&self, v: usize) -> Option<usize> {
        if v & 1 == 1 {
            None
        } else {
            Some((v >> 1) - 1)
        }
    }
}

impl<T> ConstraintsEncoder<T> for DefaultConflictFreenessConstraintsEncoder
where
    T: LabelType,
{
    fn encode_constraints(&self, af: &AAFramework<T>, solver: &mut dyn SatSolver) {
        self.encode_disjunction_vars(af, solver);
        af.argument_set().iter().for_each(|arg| {
            let attacked_id = arg.id();
            let attacked_solver_var = arg_id_to_solver_var(attacked_id) as isize;
            af.iter_attacks_to(arg).for_each(|att| {
                let attacker_id = att.attacker().id();
                let attacker_solver_var = arg_id_to_solver_var(attacker_id) as isize;
                solver.add_clause(clause![-attacked_solver_var, -attacker_solver_var,]);
            });
        });
    }

    fn encode_range_constraints(&self, af: &AAFramework<T>, solver: &mut dyn SatSolver) -> usize {
        af.argument_set().iter().for_each(|a| {
            let range_var = 1 + solver.n_vars() as isize;
            let arg_var = arg_id_to_solver_var(a.id()) as isize;
            let att_disj_var = self.arg_id_to_solver_disjunction_var(a.id()) as isize;
            solver.add_clause(clause!(-arg_var, range_var));
            solver.add_clause(clause!(-att_disj_var, range_var));
            solver.add_clause(clause!(-range_var, arg_var, att_disj_var));
        });
        solver.n_vars() + 1 - af.n_arguments()
    }

    fn assignment_to_extension<'a>(
        &self,
        assignment: &Assignment,
        af: &'a AAFramework<T>,
    ) -> Vec<&'a Argument<T>> {
        assignment
            .iter()
            .filter_map(|(var, opt_v)| match opt_v {
                Some(true) => {
                    DefaultConflictFreenessConstraintsEncoder::arg_id_from_solver_var(self, var)
                        .and_then(|id| {
                            if id < af.n_arguments() {
                                Some(id)
                            } else {
                                None
                            }
                        })
                        .map(|id| af.argument_set().get_argument_by_id(id))
                }
                _ => None,
            })
            .collect()
    }

    fn arg_to_lit(&self, arg: &Argument<T>) -> Literal {
        Literal::from(arg_id_to_solver_var(arg.id()) as isize)
    }
}

fn arg_id_to_solver_var(id: usize) -> usize {
    (id + 1) << 1
}
