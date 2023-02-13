use super::ConstraintsEncoder;
use crate::{
    aa::{AAFramework, Argument},
    sat::{clause, Assignment, Literal, SatSolver},
    utils::{Label, LabelType},
};
use permutator::CartesianProduct;

/// The encoder for the complete semantics following the one proposed by Besnard & Doutre.
#[derive(Default)]
pub struct ExpCompleteConstraintsEncoder;

impl ExpCompleteConstraintsEncoder {
    fn encode_attack_constraints_for_arg<T>(
        af: &AAFramework<T>,
        solver: &mut dyn SatSolver,
        arg: &Label<T>,
    ) where
        T: LabelType,
    {
        let attacked_id = arg.id();
        let attacked_solver_var = Self::arg_id_to_solver_var(attacked_id) as isize;
        let mut defender_sets = vec![];
        let mut iter_attacks_to_it = af.iter_attacks_to(arg).peekable();
        if iter_attacks_to_it.peek().is_none() {
            solver.add_clause(clause![attacked_solver_var]);
            return;
        }
        let mut clause_buffer = Vec::new();
        for att in iter_attacks_to_it {
            let attacker_id = att.attacker().id();
            let attacker_solver_var = Self::arg_id_to_solver_var(attacker_id) as isize;
            clause_buffer.push(clause![-attacked_solver_var, -attacker_solver_var]);
            let defenders = af
                .iter_attacks_to(att.attacker())
                .map(|def| {
                    Literal::from(Self::arg_id_to_solver_var(def.attacker().id()) as isize)
                        as Literal
                })
                .collect::<Vec<Literal>>();
            if defenders.is_empty() {
                solver.add_clause(clause![-attacked_solver_var]);
                return;
            }
            defender_sets.push(defenders);
        }
        clause_buffer
            .into_iter()
            .for_each(|cl| solver.add_clause(cl));
        defender_sets.iter().for_each(|d| {
            let mut cl = Vec::with_capacity(d.len() + 1);
            cl.push(Literal::from(attacked_solver_var).negate());
            cl.append(&mut d.clone());
            solver.add_clause(cl);
        });
        let defender_sets_refs = defender_sets
            .iter()
            .map(|v| v.as_slice())
            .collect::<Vec<&[Literal]>>();
        defender_sets_refs.cart_prod().for_each(|p| {
            let mut cl = Vec::with_capacity(p.len() + 1);
            cl.push(Literal::from(attacked_solver_var));
            p.iter().for_each(|l| cl.push(l.negate()));
            solver.add_clause(cl);
        });
    }

    pub(crate) fn encode_range_constraint<T>(
        af: &AAFramework<T>,
        solver: &mut dyn SatSolver,
        arg: &Label<T>,
        n_args: usize,
    ) where
        T: LabelType,
    {
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

    pub(crate) fn arg_id_to_solver_var(id: usize) -> usize {
        id + 1
    }

    pub(crate) fn arg_id_from_solver_var(v: usize) -> Option<usize> {
        Some(v - 1)
    }

    pub(crate) fn arg_id_to_range_var(n_args: usize, id: usize) -> usize {
        n_args + id + 1
    }
}

impl<T> ConstraintsEncoder<T> for ExpCompleteConstraintsEncoder
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
            Self::encode_range_constraint(af, solver, arg, af.n_arguments());
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
