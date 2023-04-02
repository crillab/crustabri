//! A module dedicated to encodings based on auxiliary variables addition.

use super::ConstraintsEncoder;
use crate::{
    aa::{AAFramework, Argument},
    sat::{clause, Assignment, Literal, SatSolver},
    utils::{Label, LabelType},
};

enum EncodingType {
    ConflictFreeness,
    Admissibility,
    CompleteSemantics,
}

impl EncodingType {
    fn encode_constraints<T>(&self, af: &AAFramework<T>, solver: &mut dyn SatSolver)
    where
        T: LabelType,
    {
        solver.reserve(af.n_arguments() << 1);
        match self {
            EncodingType::ConflictFreeness => {
                af.argument_set().iter().for_each(|arg| {
                    encode_conflict_freeness_attack_constraints_for_arg(af, solver, arg);
                });
            }
            EncodingType::Admissibility => {
                af.argument_set().iter().for_each(|arg| {
                    encode_admissibility_attack_constraints_for_arg(
                        af,
                        solver,
                        arg,
                        &arg_id_to_solver_var,
                        &arg_id_to_solver_disjunction_var,
                    );
                    encode_disjunction_var(af, solver, arg);
                });
            }
            EncodingType::CompleteSemantics => {
                af.argument_set().iter().for_each(|arg| {
                    encode_complete_semantics_attack_constraints_for_arg(
                        af,
                        solver,
                        arg,
                        &arg_id_to_solver_var,
                        &arg_id_to_solver_disjunction_var,
                    );
                    encode_disjunction_var(af, solver, arg);
                });
            }
        }
    }

    fn encode_constraints_and_range<T>(&self, af: &AAFramework<T>, solver: &mut dyn SatSolver)
    where
        T: LabelType,
    {
        solver.reserve(af.n_arguments() * 3);
        match self {
            EncodingType::ConflictFreeness => {
                af.argument_set().iter().for_each(|arg| {
                    encode_conflict_freeness_attack_constraints_for_arg(af, solver, arg);
                    encode_disjunction_var(af, solver, arg);
                    encode_range_constraint(solver, arg, af.n_arguments());
                });
            }
            EncodingType::Admissibility => {
                af.argument_set().iter().for_each(|arg| {
                    encode_admissibility_attack_constraints_for_arg(
                        af,
                        solver,
                        arg,
                        &arg_id_to_solver_var,
                        &arg_id_to_solver_disjunction_var,
                    );
                    encode_disjunction_var(af, solver, arg);
                    encode_range_constraint(solver, arg, af.n_arguments());
                });
            }
            EncodingType::CompleteSemantics => {
                af.argument_set().iter().for_each(|arg| {
                    encode_complete_semantics_attack_constraints_for_arg(
                        af,
                        solver,
                        arg,
                        &arg_id_to_solver_var,
                        &arg_id_to_solver_disjunction_var,
                    );
                    encode_disjunction_var(af, solver, arg);
                    encode_range_constraint(solver, arg, af.n_arguments());
                });
            }
        }
    }
}

/// Returns an encoder for conflict-freeness based on auxiliary variables addition.
pub fn new_for_conflict_freeness() -> AuxVarConstraintsEncoder {
    AuxVarConstraintsEncoder(EncodingType::ConflictFreeness)
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
        solver.add_clause(clause![-attacked_solver_var, -attacker_solver_var,]);
    });
}

/// Returns an encoder for admissibility based on auxiliary variables addition.
pub fn new_for_admissibility() -> AuxVarConstraintsEncoder {
    AuxVarConstraintsEncoder(EncodingType::Admissibility)
}

pub(crate) fn encode_admissibility_attack_constraints_for_arg<T>(
    af: &AAFramework<T>,
    solver: &mut dyn SatSolver,
    arg: &Label<T>,
    arg_id_to_solver_var: &dyn Fn(usize) -> usize,
    arg_id_to_solver_disjunction_var: &dyn Fn(usize) -> usize,
) where
    T: LabelType,
{
    let attacked_id = arg.id();
    let attacked_solver_var = arg_id_to_solver_var(attacked_id) as isize;
    af.iter_attacks_to(arg).for_each(|att| {
        let attacker_id = att.attacker().id();
        let attacker_disjunction_solver_var =
            arg_id_to_solver_disjunction_var(attacker_id) as isize;
        solver.add_clause(clause![
            -attacked_solver_var,
            attacker_disjunction_solver_var
        ]);
    });
}

/// Returns an encoder for the complete semantics based on auxiliary variables addition.
pub fn new_for_complete_semantics() -> AuxVarConstraintsEncoder {
    AuxVarConstraintsEncoder(EncodingType::CompleteSemantics)
}

pub(crate) fn encode_complete_semantics_attack_constraints_for_arg<T>(
    af: &AAFramework<T>,
    solver: &mut dyn SatSolver,
    arg: &Label<T>,
    arg_id_to_solver_var: &dyn Fn(usize) -> usize,
    arg_id_to_solver_disjunction_var: &dyn Fn(usize) -> usize,
) where
    T: LabelType,
{
    let attacked_id = arg.id();
    let attacked_solver_var = arg_id_to_solver_var(attacked_id) as isize;
    let mut full_cl = clause![attacked_solver_var];
    af.iter_attacks_to(arg).for_each(|att| {
        let attacker_id = att.attacker().id();
        let attacker_disjunction_solver_var =
            arg_id_to_solver_disjunction_var(attacker_id) as isize;
        solver.add_clause(clause![
            -attacked_solver_var,
            attacker_disjunction_solver_var
        ]);
        full_cl.push((-attacker_disjunction_solver_var).into());
    });
    solver.add_clause(full_cl);
}

pub(crate) fn encode_disjunction_var<T>(
    af: &AAFramework<T>,
    solver: &mut dyn SatSolver,
    arg: &Label<T>,
) where
    T: LabelType,
{
    let attacked_id = arg.id();
    let attacked_disjunction_solver_var = arg_id_to_solver_disjunction_var(attacked_id) as isize;
    encode_disjunction_var_with(
        af,
        solver,
        arg,
        attacked_disjunction_solver_var,
        &arg_id_to_solver_var,
    )
}

pub(crate) fn encode_disjunction_var_with<T>(
    af: &AAFramework<T>,
    solver: &mut dyn SatSolver,
    arg: &Label<T>,
    disjunction_var: isize,
    arg_id_to_solver_var: &dyn Fn(usize) -> usize,
) where
    T: LabelType,
{
    let arg_id = arg.id();
    let arg_var = arg_id_to_solver_var(arg_id) as isize;
    solver.add_clause(clause![-arg_var, -disjunction_var]);
    let mut full_cl = clause![-disjunction_var];
    af.iter_attacks_to(arg).for_each(|att| {
        let attacker_id = att.attacker().id();
        let attacker_solver_var = arg_id_to_solver_var(attacker_id) as isize;
        solver.add_clause(clause![disjunction_var, -attacker_solver_var]);
        full_cl.push(attacker_solver_var.into());
    });
    solver.add_clause(full_cl);
}

pub(crate) fn encode_range_constraint<T>(solver: &mut dyn SatSolver, arg: &Label<T>, n_args: usize)
where
    T: LabelType,
{
    let range_var = arg_id_to_range_var(n_args, arg.id()) as isize;
    let arg_var = arg_id_to_solver_var(arg.id()) as isize;
    let att_disj_var = arg_id_to_solver_disjunction_var(arg.id()) as isize;
    solver.add_clause(clause!(-arg_var, range_var));
    solver.add_clause(clause!(-att_disj_var, range_var));
    solver.add_clause(clause!(-range_var, arg_var, att_disj_var));
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

fn arg_id_to_solver_disjunction_var(id: usize) -> usize {
    arg_id_to_solver_var(id) - 1
}

pub(crate) fn arg_id_to_range_var(n_args: usize, id: usize) -> usize {
    (n_args << 1) + id + 1
}

/// A common type for encodings based on auxiliary variables addition.
pub struct AuxVarConstraintsEncoder(EncodingType);

impl<T> ConstraintsEncoder<T> for AuxVarConstraintsEncoder
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
        assignment: &Assignment,
        af: &'a AAFramework<T>,
    ) -> Vec<&'a Argument<T>> {
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
            aux_var_constraints_encoder::{AuxVarConstraintsEncoder, EncodingType},
            ConstraintsEncoder,
        },
        sat::default_solver,
    };

    #[test]
    fn test_no_attacks_complete_semantics() {
        let af = AAFramework::new_with_argument_set(ArgumentSet::new_with_labels(&["a0"]));
        let encoder = AuxVarConstraintsEncoder(EncodingType::CompleteSemantics);
        let mut solver = default_solver();
        encoder.encode_constraints(&af, solver.as_mut());
        assert_ne!(solver.n_vars(), 0);
    }

    #[test]
    fn test_no_attacks_admissibility() {
        let af = AAFramework::new_with_argument_set(ArgumentSet::new_with_labels(&["a0"]));
        let encoder = AuxVarConstraintsEncoder(EncodingType::Admissibility);
        let mut solver = default_solver();
        encoder.encode_constraints(&af, solver.as_mut());
        assert_ne!(solver.n_vars(), 0);
    }

    #[test]
    fn test_no_attacks_conflict_freeness() {
        let af = AAFramework::new_with_argument_set(ArgumentSet::new_with_labels(&["a0"]));
        let encoder = AuxVarConstraintsEncoder(EncodingType::ConflictFreeness);
        let mut solver = default_solver();
        encoder.encode_constraints(&af, solver.as_mut());
        assert_ne!(solver.n_vars(), 0);
    }
}
