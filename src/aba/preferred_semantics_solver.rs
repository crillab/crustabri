use super::{CompleteSemanticsEncoder, FlatABACycleBreaker, FlatABAFramework};
use crate::{
    aa::Argument,
    sat::{Literal, SatSolverFactoryFn},
    solvers::SingleExtensionComputer,
    utils::LabelType,
};

/// A solver for preferred semantics problems applied on flat ABA frameworks.
pub struct FlatABAPreferredConstraintsSolver<'a, T>
where
    T: LabelType,
{
    af: &'a FlatABAFramework<T>,
    solver_factory: Box<SatSolverFactoryFn>,
    constraints_encoder: CompleteSemanticsEncoder<T>,
}

impl<'a, T> FlatABAPreferredConstraintsSolver<'a, T>
where
    T: LabelType,
{
    /// Creates a new solver for complete semantics problems applied on flat ABA frameworks.
    pub fn new(
        af: &'a FlatABAFramework<T>,
        solver_factory: Box<SatSolverFactoryFn>,
        cycle_breaker: FlatABACycleBreaker<T>,
    ) -> Self {
        Self {
            af,
            solver_factory,
            constraints_encoder: CompleteSemanticsEncoder::new(cycle_breaker),
        }
    }
}

impl<T> SingleExtensionComputer<T> for FlatABAPreferredConstraintsSolver<'_, T>
where
    T: LabelType,
{
    fn compute_one_extension(&mut self) -> Option<Vec<&Argument<T>>> {
        let solver = (self.solver_factory)();
        let mut encoding_data = self.constraints_encoder.encode_constraints(self.af, solver);
        let mut model = encoding_data.solver().solve().unwrap_model().unwrap();
        let mut extension =
            self.constraints_encoder
                .assignment_to_extension(&model, self.af, &encoding_data);
        let arg_set = self.af.argument_set();
        let mut solver_assumption: Option<Literal> = None;
        loop {
            if let Some(a) = solver_assumption {
                encoding_data.solver().add_clause(vec![a.negate()]);
            }
            let mut in_ext_bool = vec![false; arg_set.len()];
            for arg in &extension {
                in_ext_bool[arg.id()] = true;
            }
            let mut in_extension = Vec::new();
            let mut not_in_extension = Vec::new();
            for aba_assumption in self.af.assumption_ids() {
                let aba_assumption_lit = self.constraints_encoder.arg_to_lit(
                    arg_set.get_argument_by_id(*aba_assumption),
                    &mut encoding_data,
                );
                if in_ext_bool[*aba_assumption] {
                    in_extension.push(aba_assumption_lit);
                } else {
                    not_in_extension.push(aba_assumption_lit);
                }
            }
            solver_assumption = Some(Literal::from(1 + encoding_data.solver().n_vars() as isize));
            not_in_extension.push(solver_assumption.unwrap().negate());
            encoding_data.solver().add_clause(not_in_extension);
            in_extension.push(solver_assumption.unwrap());
            let opt_model = encoding_data
                .solver()
                .solve_under_assumptions(&in_extension)
                .unwrap_model();
            if opt_model.is_some() {
                model = opt_model.unwrap();
                extension = self.constraints_encoder.assignment_to_extension(
                    &model,
                    self.af,
                    &encoding_data,
                );
            } else {
                encoding_data
                    .solver()
                    .add_clause(vec![solver_assumption.unwrap().negate()]);
                break;
            }
        }
        Some(extension)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        io::{FlatABAInstanceReader, FlatABAReader},
        sat,
    };

    fn assert_se(str_af: &str, expected: Vec<Vec<usize>>) {
        let reader = FlatABAReader::default();
        let af = reader.read(&mut str_af.as_bytes()).unwrap();
        let mut solver = FlatABAPreferredConstraintsSolver::new(
            &af,
            Box::new(|| sat::default_solver()),
            FlatABACycleBreaker::new_for_usize(),
        );
        let actual = solver
            .compute_one_extension()
            .unwrap()
            .iter()
            .map(|l| *l.label())
            .collect::<Vec<_>>();
        assert!(expected.contains(&actual));
    }

    #[test]
    fn test_ok() {
        let str_af = r#"#
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
        assert_se(str_af, vec![vec![1, 2], vec![1, 3, 4]]);
    }
}
