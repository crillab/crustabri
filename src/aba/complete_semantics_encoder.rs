use crate::{
    aa::Argument,
    sat::{Assignment, Literal, SatSolver},
    utils::LabelType,
};

use super::{FlatABACycleBreaker, FlatABAFramework};

/// An encoder dedicated to complete semantics for flat ABA frameworks.
pub struct CompleteSemanticsEncoder<T>
where
    T: LabelType,
{
    cycle_breaker: FlatABACycleBreaker<T>,
}

pub struct CompleteSemanticsEncoderEncodingData {
    solver: Box<dyn SatSolver>,
    varmap: VarMap,
}

impl CompleteSemanticsEncoderEncodingData {
    pub fn solver(&mut self) -> &mut dyn SatSolver {
        self.solver.as_mut()
    }
}

impl<T> CompleteSemanticsEncoder<T>
where
    T: LabelType,
{
    /// Creates an encoder dedicated to complete semantics for flat ABA frameworks.
    pub fn new(cycle_breaker: FlatABACycleBreaker<T>) -> Self {
        Self { cycle_breaker }
    }

    /// Encodes the constraints for the provided framework into the provided solver.
    pub fn encode_constraints(
        &self,
        af: &FlatABAFramework<T>,
        mut solver: Box<dyn SatSolver>,
    ) -> CompleteSemanticsEncoderEncodingData
    where
        T: LabelType,
    {
        let mut af = self.cycle_breaker.remove_cycles(af);
        af.reduce_not_derivable();
        let mut varmap = VarMap::new(&af, solver.as_mut());
        encode_rule_is_applied(&af, solver.as_mut(), &mut varmap);
        encode_rule_is_defeated(&af, solver.as_mut(), &mut varmap);
        encode_contraries(&af, solver.as_mut(), &mut varmap);
        encode_defense(&af, solver.as_mut(), &mut varmap);
        CompleteSemanticsEncoderEncodingData { solver, varmap }
    }

    /// Translates an argument into the literal that represent it.
    pub fn arg_to_lit(
        &self,
        arg: &Argument<T>,
        encoding_data: &mut CompleteSemanticsEncoderEncodingData,
    ) -> Literal {
        if let Some(v) = encoding_data.varmap.assumption_var(arg.id()) {
            v
        } else {
            encoding_data
                .varmap
                .atom_is_applied_var(arg.id(), encoding_data.solver.as_mut())
        }
    }

    /// Translates an assignment into the correponding extension.
    pub fn assignment_to_extension<'a>(
        &self,
        assignment: &Assignment,
        af: &'a FlatABAFramework<T>,
        encoding_data: &CompleteSemanticsEncoderEncodingData,
    ) -> Vec<&'a Argument<T>> {
        let mut extension = Vec::new();
        for assumption in af.assumption_ids() {
            if assignment.value_of(
                encoding_data
                    .varmap
                    .assumption_var(*assumption)
                    .unwrap()
                    .var(),
            ) == Some(true)
            {
                extension.push(af.argument_set().get_argument_by_id(*assumption));
            }
        }
        extension
    }
}

fn encode_rule_is_applied<T>(
    af: &FlatABAFramework<T>,
    solver: &mut dyn SatSolver,
    varmap: &mut VarMap,
) where
    T: LabelType,
{
    for (head, tails) in af
        .iter_rules_by_ids()
        .filter(|(h, _)| !af.is_assumption_id(*h))
    {
        for (tail_index, tail) in tails.iter().enumerate() {
            let mut conjuncts = Vec::with_capacity(tail.len());
            for t in tail {
                if let Some(v) = varmap.assumption_var(*t) {
                    conjuncts.push(v);
                } else {
                    conjuncts.push(varmap.atom_is_applied_var(*t, solver));
                }
            }
            encode_conjunction_eq(
                solver,
                conjuncts.as_slice(),
                varmap.rule_is_applied_var(head, tail_index),
            );
        }
    }
}

fn encode_rule_is_defeated<T>(
    af: &FlatABAFramework<T>,
    solver: &mut dyn SatSolver,
    varmap: &mut VarMap,
) where
    T: LabelType,
{
    for (head, tails) in af
        .iter_rules_by_ids()
        .filter(|(h, _)| !af.is_assumption_id(*h))
    {
        for (tail_index, tail) in tails.iter().enumerate() {
            let mut disjuncts = Vec::with_capacity(tail.len());
            for t in tail {
                if af.is_assumption_id(*t) {
                    match af.contrary_of_id(*t) {
                        Some(c) if af.is_assumption_id(c) => {
                            disjuncts.push(varmap.assumption_var(c).unwrap());
                        }
                        Some(c) => {
                            disjuncts.push(varmap.atom_is_applied_var(c, solver));
                        }
                        None => {}
                    }
                } else {
                    disjuncts.push(varmap.atom_is_defeated_var(*t, solver));
                }
            }
            encode_disjunction_eq(
                solver,
                disjuncts.as_slice(),
                varmap.rule_is_defeated_var(head, tail_index),
            );
        }
    }
}

fn encode_contraries<T>(af: &FlatABAFramework<T>, solver: &mut dyn SatSolver, varmap: &mut VarMap)
where
    T: LabelType,
{
    for (contrary, assumptions) in af.iter_contraries_by_ids() {
        for assumption in assumptions {
            let neg_assumption_var = varmap.assumption_var(*assumption).unwrap().negate();
            if af.is_assumption_id(contrary) {
                if *assumption == contrary {
                    solver.add_clause(vec![neg_assumption_var])
                } else {
                    solver.add_clause(vec![
                        neg_assumption_var,
                        varmap.assumption_var(contrary).unwrap().negate(),
                    ])
                }
            } else {
                let contrary_is_applied = varmap.atom_is_applied_var(contrary, solver);
                solver.add_clause(vec![neg_assumption_var, contrary_is_applied.negate()]);
            }
        }
    }
}

fn encode_defense<T>(af: &FlatABAFramework<T>, solver: &mut dyn SatSolver, varmap: &mut VarMap)
where
    T: LabelType,
{
    for assumption in af.assumption_ids() {
        let assumption_lit = varmap.assumption_var(*assumption).unwrap();
        match af.contrary_of_id(*assumption) {
            Some(c) if af.is_assumption_id(c) => match af.contrary_of_id(c) {
                Some(cc) if af.is_assumption_id(cc) => {
                    let contrary_of_contrary_lit = varmap.assumption_var(cc).unwrap();
                    solver.add_clause(vec![assumption_lit.negate(), contrary_of_contrary_lit]);
                    solver.add_clause(vec![assumption_lit, contrary_of_contrary_lit.negate()]);
                }
                Some(cc) => {
                    let contrary_is_defeated_lit = varmap.atom_is_applied_var(cc, solver);
                    solver.add_clause(vec![assumption_lit.negate(), contrary_is_defeated_lit]);
                    solver.add_clause(vec![assumption_lit, contrary_is_defeated_lit.negate()]);
                }
                None => solver.add_clause(vec![assumption_lit.negate()]),
            },
            Some(c) => {
                let contrary_is_defeated_lit = varmap.atom_is_defeated_var(c, solver);
                solver.add_clause(vec![assumption_lit.negate(), contrary_is_defeated_lit]);
                solver.add_clause(vec![assumption_lit, contrary_is_defeated_lit.negate()]);
            }
            None => {
                solver.add_clause(vec![assumption_lit]);
            }
        }
    }
}

struct VarMap {
    assumption_vars: Vec<Option<Literal>>,
    applied_rule_solver_vars: Vec<Vec<Literal>>,
    atom_is_applied_solver_vars: Vec<Option<Literal>>,
    defeated_rule_solver_vars: Vec<Vec<Literal>>,
    atom_is_defeated_solver_vars: Vec<Option<Literal>>,
}

impl VarMap {
    fn new<T>(af: &FlatABAFramework<T>, solver: &mut dyn SatSolver) -> Self
    where
        T: LabelType,
    {
        solver.reserve(af.n_assumptions());
        let mut assumption_vars = vec![None; af.argument_set().len()];
        for (i, assumption) in af.assumption_ids().iter().enumerate() {
            assumption_vars[*assumption] = Some(Literal::from(1 + i as isize));
        }
        let applied_rule_solver_vars = Self::generate_one_var_per_rule(af, solver);
        let defeated_rule_solver_vars = Self::generate_one_var_per_rule(af, solver);
        Self {
            assumption_vars,
            applied_rule_solver_vars,
            atom_is_applied_solver_vars: vec![None; af.argument_set().len()],
            defeated_rule_solver_vars,
            atom_is_defeated_solver_vars: vec![None; af.argument_set().len()],
        }
    }

    fn generate_one_var_per_rule<T>(
        af: &FlatABAFramework<T>,
        solver: &mut dyn SatSolver,
    ) -> Vec<Vec<Literal>>
    where
        T: LabelType,
    {
        let mut next_var_id = 1 + solver.n_vars() as isize;
        let mut defeated_rule_solver_vars = Vec::with_capacity(af.n_rules());
        for (head, tails) in af.iter_rules_by_ids() {
            let mut new_vars = Vec::with_capacity(tails.len());
            if !af.is_assumption_id(head) {
                for i in next_var_id..next_var_id + (tails.len() as isize) {
                    new_vars.push(Literal::from(i));
                }
                next_var_id += tails.len() as isize;
            }
            defeated_rule_solver_vars.push(new_vars);
        }
        solver.reserve(next_var_id as usize - 1);
        defeated_rule_solver_vars
    }

    fn assumption_var(&self, id: usize) -> Option<Literal> {
        self.assumption_vars[id]
    }

    fn atom_is_applied_var(&mut self, index: usize, solver: &mut dyn SatSolver) -> Literal {
        if let Some(a) = self.atom_is_applied_solver_vars[index] {
            return a;
        }
        let applied_rules_vars = self.applied_rule_solver_vars[index].as_slice();
        let a = if applied_rules_vars.len() == 1 {
            applied_rules_vars[0]
        } else {
            let a = Literal::from(1 + solver.n_vars() as isize);
            encode_disjunction_eq(solver, applied_rules_vars, a);
            a
        };
        self.atom_is_applied_solver_vars[index] = Some(a);
        a
    }

    fn rule_is_applied_var(&self, head: usize, tail_index: usize) -> Literal {
        self.applied_rule_solver_vars[head][tail_index]
    }

    fn atom_is_defeated_var(&mut self, index: usize, solver: &mut dyn SatSolver) -> Literal {
        if let Some(a) = self.atom_is_defeated_solver_vars[index] {
            return a;
        }
        let defeated_rules_vars = self.defeated_rule_solver_vars[index].as_slice();
        let a = if defeated_rules_vars.len() == 1 {
            defeated_rules_vars[0]
        } else {
            let a = Literal::from(1 + solver.n_vars() as isize);
            encode_conjunction_eq(solver, defeated_rules_vars, a);
            a
        };
        self.atom_is_defeated_solver_vars[index] = Some(a);
        a
    }

    fn rule_is_defeated_var(&self, head: usize, tail_index: usize) -> Literal {
        self.defeated_rule_solver_vars[head][tail_index]
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        io::{FlatABAInstanceReader, FlatABAReader},
        sat::{self, SolvingResult},
    };

    fn assert_extensions(str_af: &str, expected: Vec<Vec<usize>>) {
        let reader = FlatABAReader::default();
        let af = reader.read(&mut str_af.as_bytes()).unwrap();
        let encoder = CompleteSemanticsEncoder::new(FlatABACycleBreaker::new_for_usize());
        let mut encoding_data = encoder.encode_constraints(&af, sat::default_solver());
        let mut models = Vec::new();
        loop {
            match encoding_data.solver().solve() {
                SolvingResult::Satisfiable(assignment) => {
                    models.push(
                        encoder
                            .assignment_to_extension(&assignment, &af, &encoding_data)
                            .iter()
                            .map(|l| *l.label())
                            .collect::<Vec<_>>(),
                    );
                    let mut blocking_cl = Vec::new();
                    for assumption in af.assumption_ids() {
                        let solver_var = encoding_data.varmap.assumption_var(*assumption).unwrap();
                        if assignment.value_of(solver_var.var()) == Some(true) {
                            blocking_cl.push(solver_var.negate());
                        } else {
                            blocking_cl.push(solver_var);
                        }
                    }
                    encoding_data.solver.add_clause(blocking_cl);
                }
                SolvingResult::Unsatisfiable => break,
                SolvingResult::Unknown => panic!(),
            }
        }
        models.sort_unstable();
        assert_eq!(expected, models)
    }

    #[test]
    fn test_extensions_1() {
        assert_extensions(
            r#"#
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
        "#,
            vec![vec![1], vec![1, 2], vec![1, 3, 4]],
        );
    }

    #[test]
    fn test_extensions_2() {
        assert_extensions(
            r#"#
        p aba 4
        a 1
        c 1 3
        r 2 3
        r 2 1 4
        r 3 2 4
        r 3 4 2
        r 4 1
        r 4 3 2
        "#,
            vec![vec![]],
        );
    }

    #[test]
    fn test_extensions_3() {
        assert_extensions(
            r#"#
        p aba 4
        a 1
        c 1 4
        r 2 4 3
        r 3 2
        r 4 1 3
        r 4 2
        "#,
            vec![vec![1]],
        );
    }

    #[test]
    fn test_extensions_4() {
        assert_extensions(
            r#"#
        p aba 3
        a 1
        c 1 3
        r 3 1 2
        "#,
            vec![vec![1]],
        );
    }

    #[test]
    fn test_extensions_5() {
        assert_extensions(
            r#"#
        p aba 4
        a 1
        c 1 2
        r 2 1
        r 2 1 4
        r 3 4 1
        r 3 4
        r 4 1
        r 4 3
        "#,
            vec![vec![]],
        );
    }

    #[test]
    fn test_extensions_6() {
        assert_extensions(
            r#"#
        p aba 8
        a 1
        a 2
        c 1 2
        c 2 2
        r 3 8 1 5
        r 3 2 6
        r 4 3
        r 4 2 3
        r 5 1
        r 6 2 4
        r 6 4
        r 7 1 5 4
        r 7 3 4 5
        r 8 7 6 1
        r 8 5"#,
            vec![vec![]],
        );
    }

    #[test]
    fn test_extensions_7() {
        assert_extensions(
            r#"#
        p aba 8
        a 1
        a 2
        c 1 4
        c 2 1
        r 3 7 8 6
        r 3 8
        r 4 2
        r 5 1 7 8
        r 5 4
        r 6 4 8
        r 7 3
        r 8 4 6 1
        r 8 1"#,
            vec![vec![], vec![1], vec![2]],
        );
    }

    #[test]
    fn test_extensions_8() {
        assert_extensions(
            r#"#
        p aba 8
        a 1
        a 2
        c 1 2
        c 2 1
        r 3 1
        r 3 1 4 7
        r 4 7 2
        r 5 1 2
        r 6 1 5 3
        r 6 8
        r 7 1 3
        r 7 2 6
        r 8 3"#,
            vec![vec![], vec![1], vec![2]],
        );
    }

    #[test]
    fn test_cycle() {
        assert_extensions(
            r#"#
        p aba 3
        a 1
        c 1 2
        r 2 3
        r 3 2
        "#,
            vec![vec![1]],
        );
    }
    #[test]
    fn test_self_contrary() {
        assert_extensions(
            r#"#
            p aba 4
            a 1
            c 1 2
            r 2 1
            r 3 4
            r 4 1
            r 4 3"#,
            vec![vec![]],
        );
    }
}
