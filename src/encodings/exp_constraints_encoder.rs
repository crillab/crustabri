//! A module dedicated to simple encodings that do not use auxiliary variables.

use super::ConstraintsEncoder;
use crate::{
    aa::AAFramework,
    sat::{clause, Literal, SatSolver},
    utils::{Label, LabelType},
};
use permutator::CartesianProduct;

enum EncodingType {
    ConflictFreeness,
    CompleteSemantics,
}

impl EncodingType {
    fn encode_constraints<T>(&self, af: &AAFramework<T>, solver: &mut dyn SatSolver)
    where
        T: LabelType,
    {
        match self {
            EncodingType::ConflictFreeness => {
                solver.reserve(af.n_arguments());
                af.argument_set().iter().for_each(|arg| {
                    encode_conflict_freeness_attack_constraints_for_arg(af, solver, arg);
                });
            }
            EncodingType::CompleteSemantics => {
                solver.reserve(af.n_arguments());
                af.argument_set().iter().for_each(|arg| {
                    encode_complete_semantics_attack_constraints_for_arg(af, solver, arg);
                });
            }
        }
    }

    fn encode_constraints_and_range<T>(&self, af: &AAFramework<T>, solver: &mut dyn SatSolver)
    where
        T: LabelType,
    {
        match self {
            EncodingType::ConflictFreeness => {
                solver.reserve(af.n_arguments() << 1);
                af.argument_set().iter().for_each(|arg| {
                    encode_conflict_freeness_attack_constraints_for_arg(af, solver, arg);
                    encode_range_constraint(af, solver, arg, af.n_arguments());
                });
            }
            EncodingType::CompleteSemantics => {
                solver.reserve(af.n_arguments() << 1);
                af.argument_set().iter().for_each(|arg| {
                    encode_complete_semantics_attack_constraints_for_arg(af, solver, arg);
                    encode_range_constraint(af, solver, arg, af.n_arguments());
                });
            }
        }
    }
}

/// Returns an encoder for conflict-freeness.
pub fn new_for_conflict_freeness() -> ExpConstraintsEncoder {
    ExpConstraintsEncoder(EncodingType::ConflictFreeness)
}

fn encode_conflict_freeness_attack_constraints_for_arg<T>(
    af: &AAFramework<T>,
    solver: &mut dyn SatSolver,
    arg: &Label<T>,
) where
    T: LabelType,
{
    let attacked_id = arg.id();
    let attacked_solver_var = arg_id_to_solver_var(attacked_id) as isize;
    af.iter_attacks_to(arg).for_each(|att| {
        let attacker_id = att.attacker().id();
        let attacker_solver_var = arg_id_to_solver_var(attacker_id) as isize;
        solver.add_clause(clause![-attacked_solver_var, -attacker_solver_var]);
    });
}

/// Returns an encoder for the complete semantics.
pub fn new_for_complete_semantics() -> ExpConstraintsEncoder {
    ExpConstraintsEncoder(EncodingType::CompleteSemantics)
}

fn encode_complete_semantics_attack_constraints_for_arg<T>(
    af: &AAFramework<T>,
    solver: &mut dyn SatSolver,
    arg: &Label<T>,
) where
    T: LabelType,
{
    let attacked_id = arg.id();
    let attacked_solver_var = arg_id_to_solver_var(attacked_id) as isize;
    let (defender_sets, conflict_freeness_clauses) = compute_defender_sets(af, arg);
    if defender_sets.is_empty() {
        solver.add_clause(clause![attacked_solver_var]);
        return;
    }
    if defender_sets.iter().any(|s| s.is_empty()) {
        solver.add_clause(clause![-attacked_solver_var]);
        return;
    }
    encode_nontrivial_attack_constraints_for_arg(
        arg,
        solver,
        defender_sets,
        conflict_freeness_clauses,
    );
}

pub(crate) fn compute_defender_sets<T>(
    af: &AAFramework<T>,
    arg: &Label<T>,
) -> (Vec<Vec<Literal>>, Vec<Vec<Literal>>)
where
    T: LabelType,
{
    let attacked_id = arg.id();
    let attacked_solver_var = arg_id_to_solver_var(attacked_id) as isize;
    let mut conflict_freeness_clauses = Vec::new();
    let mut defender_sets = vec![];
    for att in af.iter_attacks_to(arg) {
        let attacker_id = att.attacker().id();
        let attacker_solver_var = arg_id_to_solver_var(attacker_id) as isize;
        conflict_freeness_clauses.push(clause![-attacked_solver_var, -attacker_solver_var]);
        let defenders = af
            .iter_attacks_to(att.attacker())
            .map(|def| Literal::from(arg_id_to_solver_var(def.attacker().id()) as isize))
            .collect();
        defender_sets.push(defenders);
    }
    (defender_sets, conflict_freeness_clauses)
}

pub(crate) fn encode_nontrivial_attack_constraints_for_arg<T>(
    arg: &Label<T>,
    solver: &mut dyn SatSolver,
    defender_sets: Vec<Vec<Literal>>,
    conflict_freeness_clauses: Vec<Vec<Literal>>,
) where
    T: LabelType,
{
    let attacked_id = arg.id();
    let attacked_solver_var = arg_id_to_solver_var(attacked_id) as isize;
    conflict_freeness_clauses
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
    let range_var = arg_id_to_range_var(n_args, arg.id()) as isize;
    let arg_var = arg_id_to_solver_var(arg.id()) as isize;
    solver.add_clause(clause![-arg_var, range_var]);
    let mut full_cl = vec![Literal::from(range_var).negate(), Literal::from(arg_var)];
    af.iter_attacks_to(arg).for_each(|att| {
        full_cl.push(Literal::from(
            arg_id_to_solver_var(att.attacker().id()) as isize
        ));
    });
    solver.add_clause(full_cl);
}

fn arg_id_to_solver_var(id: usize) -> usize {
    id + 1
}

pub(crate) fn arg_id_from_solver_var(v: usize) -> Option<usize> {
    Some(v - 1)
}

fn arg_id_to_range_var(n_args: usize, id: usize) -> usize {
    n_args + id + 1
}

/// A common type for encodings that do not rely on auxiliary variables addition.
pub struct ExpConstraintsEncoder(EncodingType);

impl<T> ConstraintsEncoder<T> for ExpConstraintsEncoder
where
    T: LabelType,
{
    fn encode_constraints(&self, af: &AAFramework<T>, solver: &mut dyn SatSolver) {
        self.0.encode_constraints(af, solver)
    }

    fn encode_constraints_and_range(&self, af: &AAFramework<T>, solver: &mut dyn SatSolver) {
        self.0.encode_constraints_and_range(af, solver)
    }

    fn assignment_to_extension<'a>(
        &self,
        assignment: &crate::sat::Assignment,
        af: &'a AAFramework<T>,
    ) -> Vec<&'a crate::aa::Argument<T>> {
        assignment
            .iter()
            .filter_map(|(var, opt_v)| match opt_v {
                Some(true) => arg_id_from_solver_var(var)
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

    fn arg_to_lit(&self, arg: &crate::aa::Argument<T>) -> Literal {
        Literal::from(arg_id_to_solver_var(arg.id()) as isize)
    }

    fn first_range_var(&self, n_args: usize) -> usize {
        arg_id_to_range_var(n_args, 0)
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        aa::{AAFramework, ArgumentSet},
        encodings::{
            exp_constraints_encoder::{EncodingType, ExpConstraintsEncoder},
            ConstraintsEncoder,
        },
        sat::default_solver,
    };

    #[test]
    fn test_no_attacks_complete_semantics() {
        let af = AAFramework::new_with_argument_set(ArgumentSet::new_with_labels(&["a0"]));
        let encoder = ExpConstraintsEncoder(EncodingType::CompleteSemantics);
        let mut solver = default_solver();
        encoder.encode_constraints(&af, solver.as_mut());
        assert_ne!(solver.n_vars(), 0);
    }

    #[test]
    fn test_no_attacks_conflict_freeness() {
        let af = AAFramework::new_with_argument_set(ArgumentSet::new_with_labels(&["a0"]));
        let encoder = ExpConstraintsEncoder(EncodingType::ConflictFreeness);
        let mut solver = default_solver();
        encoder.encode_constraints(&af, solver.as_mut());
        assert_ne!(solver.n_vars(), 0);
    }
}
