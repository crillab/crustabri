use super::{constraints_encoder::EncodingData, CompleteSemanticsEncoder, FlatABAFramework};
use crate::{
    aa::Argument,
    sat::{Assignment, Literal, SatSolverFactory},
    solvers::{SingleExtensionComputer, SkepticalAcceptanceComputer},
    utils::LabelType,
};

/// A solver for preferred semantics problems applied on flat ABA frameworks.
pub struct FlatABAPreferredConstraintsSolver<'a, T>
where
    T: LabelType,
{
    af: &'a FlatABAFramework<T>,
    solver_factory: Box<dyn SatSolverFactory>,
    constraints_encoder: CompleteSemanticsEncoder<T>,
}

enum MaximalComputationResult<'a, T>
where
    T: LabelType,
{
    Maximal {
        extension: Vec<&'a Argument<T>>,
        model: Assignment,
    },
    Partial {
        extension: Vec<&'a Argument<T>>,
        _model: Assignment,
    },
    Unsat,
}

impl<'a, T> MaximalComputationResult<'a, T>
where
    T: LabelType,
{
    fn new_maximal(extension: Vec<&'a Argument<T>>, model: Assignment) -> Self {
        Self::Maximal { extension, model }
    }

    fn new_partial(extension: Vec<&'a Argument<T>>, _model: Assignment) -> Self {
        Self::Partial { extension, _model }
    }

    fn new_unsat() -> Self {
        Self::Unsat
    }

    fn unwrap_extension(self) -> Vec<&'a Argument<T>> {
        match self {
            MaximalComputationResult::Maximal { extension, .. }
            | MaximalComputationResult::Partial { extension, .. } => extension,
            MaximalComputationResult::Unsat => panic!(),
        }
    }
}

impl<'a, T> FlatABAPreferredConstraintsSolver<'a, T>
where
    T: LabelType,
{
    /// Creates a new solver for complete semantics problems applied on flat ABA frameworks.
    pub fn new(af: &'a FlatABAFramework<T>, solver_factory: Box<dyn SatSolverFactory>) -> Self {
        Self {
            af,
            solver_factory,
            constraints_encoder: CompleteSemanticsEncoder::new(),
        }
    }

    fn compute_maximal_under_assumptions_until(
        &self,
        encoding_data: &mut EncodingData,
        init_solver_assumptions: &[Literal],
        return_on: &[&Argument<T>],
    ) -> MaximalComputationResult<T> {
        let mut model = if let Some(m) = self
            .constraints_encoder
            .extension_under_literal_assumptions(init_solver_assumptions, self.af, encoding_data)
        {
            m
        } else {
            return MaximalComputationResult::new_unsat();
        };
        let mut extension =
            self.constraints_encoder
                .assignment_to_extension(&model, self.af, encoding_data);
        loop {
            let (mut in_extension, mut not_in_extension) =
                self.split_in_extension(&extension, encoding_data);
            in_extension.append(&mut init_solver_assumptions.to_vec());
            let new_solver_assumption = Literal::from(1 + encoding_data.solver().n_vars() as isize);
            not_in_extension.push(new_solver_assumption.negate());
            encoding_data.solver().add_clause(not_in_extension);
            in_extension.push(new_solver_assumption);
            let opt_model = self
                .constraints_encoder
                .extension_under_literal_assumptions(&in_extension, self.af, encoding_data);
            encoding_data
                .solver()
                .add_clause(vec![new_solver_assumption.negate()]);
            if opt_model.is_some() {
                model = opt_model.unwrap();
                extension = self.constraints_encoder.assignment_to_extension(
                    &model,
                    self.af,
                    encoding_data,
                );
                if return_on.iter().any(|a| extension.contains(a)) {
                    return MaximalComputationResult::new_partial(extension, model);
                }
            } else {
                break;
            }
        }
        MaximalComputationResult::new_maximal(extension, model)
    }

    fn split_in_extension(
        &self,
        extension: &[&Argument<T>],
        encoding_data: &mut EncodingData,
    ) -> (Vec<Literal>, Vec<Literal>) {
        let arg_set = self.af.argument_set();
        let mut in_ext_bool = vec![false; arg_set.len()];
        for arg in extension {
            in_ext_bool[arg.id()] = true;
        }
        let mut in_extension = Vec::new();
        let mut not_in_extension = Vec::new();
        for aba_assumption in self.af.assumption_ids() {
            let aba_assumption_lit = self
                .constraints_encoder
                .arg_to_lit(arg_set.get_argument_by_id(*aba_assumption), encoding_data);
            if in_ext_bool[*aba_assumption] {
                in_extension.push(aba_assumption_lit);
            } else {
                not_in_extension.push(aba_assumption_lit);
            }
        }
        (in_extension, not_in_extension)
    }
}

impl<T> SingleExtensionComputer<T> for FlatABAPreferredConstraintsSolver<'_, T>
where
    T: LabelType,
{
    fn compute_one_extension(&mut self) -> Option<Vec<&Argument<T>>> {
        let solver = self.solver_factory.new_solver();
        let mut encoding_data = self.constraints_encoder.encode_constraints(self.af, solver);
        Some(
            self.compute_maximal_under_assumptions_until(&mut encoding_data, &[], &[])
                .unwrap_extension(),
        )
    }
}

impl<T> SkepticalAcceptanceComputer<T> for FlatABAPreferredConstraintsSolver<'_, T>
where
    T: LabelType,
{
    fn are_skeptically_accepted(&mut self, args: &[&T]) -> bool {
        let solver = self.solver_factory.new_solver();
        let mut encoding_data = self.constraints_encoder.encode_constraints(self.af, solver);
        let return_on = args
            .iter()
            .map(|l| self.af.argument_set().get_argument(l).unwrap())
            .collect::<Vec<_>>();
        let mut solver_assumptions = Vec::new();
        let forgot_assumed_clauses = |a: &[Literal], d: &mut EncodingData| {
            for solver_assumption in a {
                d.solver().add_clause(vec![solver_assumption.negate()]);
            }
        };
        let discard_maximal = |a: &mut Vec<Literal>, e: &[&Argument<T>], d: &mut EncodingData| {
            let (_, mut not_in_extension) = self.split_in_extension(e, d);
            let new_solver_assumption = Literal::from(1 + d.solver().n_vars() as isize);
            not_in_extension.push(new_solver_assumption.negate());
            d.solver().add_clause(not_in_extension);
            a.push(new_solver_assumption);
        };
        let discard_partial = |a: &mut Vec<Literal>, e: &[&Argument<T>], d: &mut EncodingData| {
            let (mut in_extension, mut not_in_extension) = self.split_in_extension(e, d);
            in_extension.iter_mut().for_each(|l| *l = l.negate());
            let new_solver_assumption = Literal::from(1 + d.solver().n_vars() as isize);
            in_extension.push(new_solver_assumption.negate());
            d.solver().add_clause(in_extension);
            not_in_extension.push(new_solver_assumption.negate());
            d.solver().add_clause(not_in_extension);
            a.push(new_solver_assumption);
        };
        loop {
            let result = self.compute_maximal_under_assumptions_until(
                &mut encoding_data,
                &solver_assumptions,
                &return_on,
            );
            match result {
                MaximalComputationResult::Maximal { extension, model } => {
                    if return_on.iter().any(|arg| {
                        model.value_of(
                            self.constraints_encoder
                                .arg_to_lit(arg, &mut encoding_data)
                                .var(),
                        ) == Some(true)
                    }) {
                        discard_maximal(&mut solver_assumptions, &extension, &mut encoding_data);
                    } else {
                        forgot_assumed_clauses(&solver_assumptions, &mut encoding_data);
                        return false;
                    }
                }
                MaximalComputationResult::Partial { extension, .. } => {
                    discard_partial(&mut solver_assumptions, &extension, &mut encoding_data);
                }
                MaximalComputationResult::Unsat => {
                    forgot_assumed_clauses(&solver_assumptions, &mut encoding_data);
                    return true;
                }
            }
        }
    }

    fn are_skeptically_accepted_with_certificate(
        &mut self,
        _args: &[&T],
    ) -> (bool, Option<Vec<&Argument<T>>>) {
        unimplemented!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        io::{FlatABAInstanceReader, FlatABAReader},
        sat::DefaultSatSolverFactory,
    };

    fn assert_se(str_af: &str, expected: Vec<Vec<usize>>) {
        let reader = FlatABAReader::default();
        let af = reader.read(&mut str_af.as_bytes()).unwrap();
        let mut solver =
            FlatABAPreferredConstraintsSolver::new(&af, Box::new(DefaultSatSolverFactory));
        let actual = solver
            .compute_one_extension()
            .unwrap()
            .iter()
            .map(|l| *l.label())
            .collect::<Vec<_>>();
        assert!(expected.contains(&actual));
    }

    fn assert_ds(str_af: &str, expected: Vec<usize>) {
        let reader = FlatABAReader::default();
        let af = reader.read(&mut str_af.as_bytes()).unwrap();
        let mut solver =
            FlatABAPreferredConstraintsSolver::new(&af, Box::new(DefaultSatSolverFactory));
        let mut actual = Vec::new();
        for argument in af.argument_set().iter() {
            if solver.is_skeptically_accepted(argument.label()) {
                actual.push(*argument.label());
            }
        }
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_se() {
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

    #[test]
    fn test_ds_1() {
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
        assert_ds(str_af, vec![1, 5]);
    }

    #[test]
    fn test_ds_2() {
        let str_af = r#"#
        p aba 5
        a 1
        a 2
        c 1 5
        c 2 4
        r 3 5 1
        r 4 1
        r 5 4
        r 5 2
        "#;
        assert_ds(str_af, vec![2, 5]);
    }

    #[test]
    fn test_ds_3() {
        let str_af = r#"#
        p aba 5
        a 1
        r 4 5
        "#;
        assert_ds(str_af, vec![1]);
    }
}
