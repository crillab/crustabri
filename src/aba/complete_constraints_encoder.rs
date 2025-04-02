use super::{FlatABAConstraintsEncoder, FlatABAFramework};
use crate::{
    aa::Argument,
    sat::{Assignment, Literal, SatSolver},
    utils::LabelType,
};

/// An encoder for complete semantics problems applied on flat ABA frameworks.
#[derive(Default)]
pub struct FlatABACompleteConstraintsEncoder;

impl<T> FlatABAConstraintsEncoder<T> for FlatABACompleteConstraintsEncoder
where
    T: LabelType,
{
    fn encode_constraints(&self, af: &FlatABAFramework<T>, solver: &mut dyn SatSolver) {
        encode_rules(af, solver);
        encode_contraries(af, solver);
        encode_defense(af, solver);
    }

    fn assignment_to_extension<'a>(
        &self,
        assignment: &Assignment,
        af: &'a FlatABAFramework<T>,
    ) -> Vec<&'a Argument<T>> {
        af.assumption_ids()
            .iter()
            .filter(|id| assignment.value_of(arg_id_to_solver_var(**id)) == Some(true))
            .map(|id| af.argument_set().get_argument_by_id(*id))
            .collect()
    }

    fn arg_to_lit(&self, arg: &Argument<T>) -> Literal {
        Literal::from(arg_id_to_solver_var(arg.id()))
    }
}

fn arg_id_to_solver_var(id: usize) -> isize {
    id as isize + 1
}

fn encode_rules<T>(af: &FlatABAFramework<T>, solver: &mut dyn SatSolver)
where
    T: LabelType,
{
    'outer: for (head, tails) in af.iter_rules_by_ids() {
        let head_solver_lit = Literal::from(arg_id_to_solver_var(head));
        match tails.len() {
            0 => {}
            1 => {
                encode_conjunction_eq(solver, &ids_to_lits(&tails[0]), head_solver_lit);
            }
            n => {
                let mut tail_vars = Vec::with_capacity(n);
                for tail in tails {
                    match tail.len() {
                        0 => {
                            solver.add_clause(vec![head_solver_lit]);
                            continue 'outer;
                        }
                        1 => {
                            tail_vars.push(Literal::from(arg_id_to_solver_var(tail[0])));
                        }
                        _ => {
                            let new_var = Literal::from(1 + solver.n_vars() as isize);
                            encode_conjunction_eq(solver, &ids_to_lits(tail), new_var);
                            tail_vars.push(new_var);
                        }
                    }
                }
                encode_disjunction_eq(solver, &tail_vars, head_solver_lit);
            }
        }
    }
}

fn encode_contraries<T>(af: &FlatABAFramework<T>, solver: &mut dyn SatSolver)
where
    T: LabelType,
{
    for (contrary, assumption) in af.iter_contraries_by_ids() {
        solver.add_clause(vec![
            Literal::from(arg_id_to_solver_var(contrary)).negate(),
            Literal::from(arg_id_to_solver_var(assumption)).negate(),
        ]);
    }
}

fn encode_defense<T>(af: &FlatABAFramework<T>, solver: &mut dyn SatSolver)
where
    T: LabelType,
{
    for assumption in af.assumption_ids() {
        let assumption_lit = Literal::from(arg_id_to_solver_var(*assumption));
        let contrary = if let Some(c) = af.contrary_of_id(*assumption) {
            c
        } else {
            solver.add_clause(vec![assumption_lit]);
            continue;
        };
        let contrary_tails = af.rule_tails_of_head_ids(contrary);
        let negation_of = |id| {
            if af.is_assumption_id(id) {
                af.contrary_of_id(id)
                    .map(|c| Literal::from(arg_id_to_solver_var(c)))
            } else {
                Some(Literal::from(arg_id_to_solver_var(id)).negate())
            }
        };
        match contrary_tails.len() {
            0 => solver.add_clause(vec![assumption_lit]),
            1 => {
                let disjuncts = contrary_tails[0]
                    .iter()
                    .filter_map(|id| negation_of(*id))
                    .collect::<Vec<_>>();
                encode_disjunction_eq(solver, &disjuncts, assumption_lit);
            }
            n => {
                let mut defense_vars = Vec::with_capacity(n);
                for contrary_tail in contrary_tails {
                    let contrary_tail_negations = contrary_tail
                        .iter()
                        .filter_map(|id| negation_of(*id))
                        .collect::<Vec<_>>();
                    match contrary_tail_negations.len() {
                        0 => solver.add_clause(vec![assumption_lit.negate()]),
                        1 => defense_vars.push(contrary_tail_negations[0]),
                        _ => {
                            let eq_lit = Literal::from(1 + solver.n_vars() as isize);
                            encode_disjunction_eq(solver, &contrary_tail_negations, eq_lit);
                            defense_vars.push(eq_lit);
                        }
                    }
                }
                encode_conjunction_eq(solver, &defense_vars, assumption_lit);
            }
        }
    }
}

fn encode_conjunction_eq(solver: &mut dyn SatSolver, conjuncts: &[Literal], eq_var: Literal) {
    if conjuncts.is_empty() {
        solver.add_clause(vec![eq_var]);
        return;
    }
    let mut full_clause = Vec::with_capacity(1 + conjuncts.len());
    full_clause.push(eq_var);
    for c in conjuncts {
        solver.add_clause(vec![eq_var.negate(), *c]);
        full_clause.push(c.negate());
    }
    solver.add_clause(full_clause);
}

fn encode_disjunction_eq(solver: &mut dyn SatSolver, disjuncts: &[Literal], eq_var: Literal) {
    if disjuncts.is_empty() {
        solver.add_clause(vec![eq_var.negate()]);
        return;
    }
    let mut full_clause = Vec::with_capacity(1 + disjuncts.len());
    full_clause.push(eq_var.negate());
    for c in disjuncts {
        solver.add_clause(vec![eq_var, c.negate()]);
        full_clause.push(*c);
    }
    solver.add_clause(full_clause);
}

fn ids_to_lits(ids: &[usize]) -> Vec<Literal> {
    ids.iter()
        .map(|id| Literal::from(arg_id_to_solver_var(*id)))
        .collect::<Vec<_>>()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        io::{FlatABAInstanceReader, FlatABAReader},
        sat::{self, SolvingResult},
    };

    const STR_INSTANCE: &str = r#"#
        p aba 8
        a 1
        a 2
        a 3
        a 4
        c 2 6
        c 3 7
        c 4 8
        r 5 1
        r 7 5 2
        r 6 3
        r 8 1 2
        "#;

    #[test]
    fn test_extensions() {
        let reader = FlatABAReader::default();
        let af = reader.read(&mut STR_INSTANCE.as_bytes()).unwrap();
        let mut solver = sat::default_solver();
        let encoder = FlatABACompleteConstraintsEncoder;
        encoder.encode_constraints(&af, solver.as_mut());
        let mut models = Vec::new();
        loop {
            match solver.solve() {
                SolvingResult::Satisfiable(assignment) => {
                    models.push(
                        encoder
                            .assignment_to_extension(&assignment, &af)
                            .iter()
                            .map(|l| *l.label())
                            .collect::<Vec<_>>(),
                    );
                    let mut blocking_cl = Vec::new();
                    for assumption in af.assumption_ids() {
                        let solver_var = arg_id_to_solver_var(*assumption);
                        if assignment.value_of(solver_var) == Some(true) {
                            blocking_cl.push(Literal::from(solver_var).negate());
                        } else {
                            blocking_cl.push(Literal::from(solver_var));
                        }
                    }
                    solver.add_clause(blocking_cl);
                }
                SolvingResult::Unsatisfiable => break,
                SolvingResult::Unknown => panic!(),
            }
        }
        assert_eq!(3, models.len());
        models.sort_unstable();
        assert_eq!(vec![vec![1], vec![1, 2], vec![1, 3, 4]], models,)
    }
}
