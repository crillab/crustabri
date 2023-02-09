use super::ConstraintsEncoder;
use crate::{
    aa::{AAFramework, Argument},
    sat::{clause, Assignment, Literal, SatSolver},
    utils::{Label, LabelType},
};

/// An encoder for the complete semantics adding auxiliary variables to make it polynomial.
#[derive(Default)]
pub struct AuxVarCompleteConstraintsEncoder;

impl AuxVarCompleteConstraintsEncoder {
    pub(crate) fn encode_disjunction_var<T>(
        af: &AAFramework<T>,
        solver: &mut dyn SatSolver,
        arg: &Label<T>,
    ) where
        T: LabelType,
    {
        let attacked_id = arg.id();
        let attacked_solver_var = Self::arg_id_to_solver_var(attacked_id) as isize;
        let attacked_disjunction_solver_var =
            Self::arg_id_to_solver_disjunction_var(attacked_id) as isize;
        solver.add_clause(clause![
            -attacked_solver_var,
            -attacked_disjunction_solver_var
        ]);
        let mut full_cl = clause![-attacked_disjunction_solver_var];
        af.iter_attacks_to(arg).for_each(|att| {
            let attacker_id = att.attacker().id();
            let attacker_solver_var = Self::arg_id_to_solver_var(attacker_id) as isize;
            solver.add_clause(clause![
                attacked_disjunction_solver_var,
                -attacker_solver_var
            ]);
            full_cl.push(attacker_solver_var.into());
        });
        solver.add_clause(full_cl);
    }

    fn encode_attack_constraints_for_arg<T>(
        af: &AAFramework<T>,
        solver: &mut dyn SatSolver,
        arg: &Label<T>,
    ) where
        T: LabelType,
    {
        let attacked_id = arg.id();
        let attacked_solver_var = Self::arg_id_to_solver_var(attacked_id) as isize;
        let mut full_cl = clause![attacked_solver_var];
        af.iter_attacks_to(arg).for_each(|att| {
            let attacker_id = att.attacker().id();
            let attacker_disjunction_solver_var =
                Self::arg_id_to_solver_disjunction_var(attacker_id) as isize;
            solver.add_clause(clause![
                -attacked_solver_var,
                attacker_disjunction_solver_var
            ]);
            full_cl.push((-attacker_disjunction_solver_var).into());
        });
        solver.add_clause(full_cl);
    }

    pub(crate) fn encode_range_constraint<T>(
        solver: &mut dyn SatSolver,
        arg: &Label<T>,
        n_args: usize,
    ) where
        T: LabelType,
    {
        let range_var = Self::arg_id_to_range_var(n_args, arg.id()) as isize;
        let arg_var = Self::arg_id_to_solver_var(arg.id()) as isize;
        let att_disj_var = Self::arg_id_to_solver_disjunction_var(arg.id()) as isize;
        solver.add_clause(clause!(-arg_var, range_var));
        solver.add_clause(clause!(-att_disj_var, range_var));
        solver.add_clause(clause!(-range_var, arg_var, att_disj_var));
    }

    fn arg_id_to_solver_disjunction_var(id: usize) -> usize {
        Self::arg_id_to_solver_var(id) - 1
    }

    pub(crate) fn arg_id_to_solver_var(id: usize) -> usize {
        (id + 1) << 1
    }

    pub(crate) fn arg_id_from_solver_var(v: usize) -> Option<usize> {
        if v & 1 == 1 {
            None
        } else {
            Some((v >> 1) - 1)
        }
    }

    pub(crate) fn arg_id_to_range_var(n_args: usize, id: usize) -> usize {
        (n_args << 1) + id + 1
    }
}

impl<T> ConstraintsEncoder<T> for AuxVarCompleteConstraintsEncoder
where
    T: LabelType,
{
    fn encode_constraints(&self, af: &AAFramework<T>, solver: &mut dyn SatSolver) {
        af.argument_set().iter().for_each(|arg| {
            Self::encode_attack_constraints_for_arg(af, solver, arg);
            Self::encode_disjunction_var(af, solver, arg);
        });
    }

    fn encode_constraints_and_range(&self, af: &AAFramework<T>, solver: &mut dyn SatSolver) {
        af.argument_set().iter().for_each(|arg| {
            Self::encode_attack_constraints_for_arg(af, solver, arg);
            Self::encode_disjunction_var(af, solver, arg);
            Self::encode_range_constraint(solver, arg, af.n_arguments());
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
