use super::{FlatABAFramework, StableSemanticsEncoder};
use crate::{
    aa::Argument,
    sat::SatSolverFactory,
    solvers::{CredulousAcceptanceComputer, SingleExtensionComputer, SkepticalAcceptanceComputer},
    utils::LabelType,
};

/// A solver for complete semantics problems applied on flat ABA frameworks.
pub struct FlatABAStableConstraintsSolver<'a, T>
where
    T: LabelType,
{
    af: &'a FlatABAFramework<T>,
    solver_factory: Box<dyn SatSolverFactory>,
    constraints_encoder: StableSemanticsEncoder<T>,
}

impl<'a, T> FlatABAStableConstraintsSolver<'a, T>
where
    T: LabelType,
{
    /// Creates a new solver for complete semantics problems applied on flat ABA frameworks.
    pub fn new(af: &'a FlatABAFramework<T>, solver_factory: Box<dyn SatSolverFactory>) -> Self {
        Self {
            af,
            solver_factory,
            constraints_encoder: StableSemanticsEncoder::new(),
        }
    }

    fn has_model_under_assumptions(&self, args: &[&T], assumptions_polarity: bool) -> bool {
        let solver = self.solver_factory.new_solver();
        let mut encoding_data = self.constraints_encoder.encode_constraints(self.af, solver);
        self.constraints_encoder
            .extension_under_assumptions(args, assumptions_polarity, self.af, &mut encoding_data)
            .is_some()
    }
}

impl<T> SingleExtensionComputer<T> for FlatABAStableConstraintsSolver<'_, T>
where
    T: LabelType,
{
    fn compute_one_extension(&mut self) -> Option<Vec<&Argument<T>>> {
        let solver = self.solver_factory.new_solver();
        let mut encoding_data = self.constraints_encoder.encode_constraints(self.af, solver);
        self.constraints_encoder
            .extension_under_assumptions(&[], true, self.af, &mut encoding_data)
            .map(|m| {
                self.constraints_encoder
                    .assignment_to_extension(&m, self.af, &encoding_data)
            })
    }
}

impl<T> CredulousAcceptanceComputer<T> for FlatABAStableConstraintsSolver<'_, T>
where
    T: LabelType,
{
    fn are_credulously_accepted(&mut self, args: &[&T]) -> bool {
        self.has_model_under_assumptions(args, true)
    }

    fn are_credulously_accepted_with_certificate(
        &mut self,
        _args: &[&T],
    ) -> (bool, Option<Vec<&Argument<T>>>) {
        unimplemented!()
    }
}

impl<T> SkepticalAcceptanceComputer<T> for FlatABAStableConstraintsSolver<'_, T>
where
    T: LabelType,
{
    fn are_skeptically_accepted(&mut self, args: &[&T]) -> bool {
        !self.has_model_under_assumptions(args, false)
    }

    fn are_skeptically_accepted_with_certificate(
        &mut self,
        _args: &[&T],
    ) -> (bool, Option<Vec<&Argument<T>>>) {
        unimplemented!()
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{
        io::{FlatABAInstanceReader, FlatABAReader},
        sat::DefaultSatSolverFactory,
    };

    fn assert_se(str_af: &str, expected: Vec<Vec<usize>>) {
        let reader = FlatABAReader::default();
        let af = reader.read(&mut str_af.as_bytes()).unwrap();
        let mut solver =
            FlatABAStableConstraintsSolver::new(&af, Box::new(DefaultSatSolverFactory));
        let actual = solver
            .compute_one_extension()
            .unwrap()
            .iter()
            .map(|l| *l.label())
            .collect::<Vec<_>>();
        assert!(expected.contains(&actual));
    }

    fn assert_dc(str_af: &str, expected: Vec<usize>) {
        let reader = FlatABAReader::default();
        let af = reader.read(&mut str_af.as_bytes()).unwrap();
        let mut solver =
            FlatABAStableConstraintsSolver::new(&af, Box::new(DefaultSatSolverFactory));
        let mut actual = Vec::new();
        for argument in af.argument_set().iter() {
            if solver.is_credulously_accepted(argument.label()) {
                actual.push(*argument.label());
            }
        }
        assert_eq!(expected, actual);
    }

    fn assert_ds(str_af: &str, expected: Vec<usize>) {
        let reader = FlatABAReader::default();
        let af = reader.read(&mut str_af.as_bytes()).unwrap();
        let mut solver =
            FlatABAStableConstraintsSolver::new(&af, Box::new(DefaultSatSolverFactory));
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
    fn test_dc_1() {
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
        assert_dc(str_af, vec![1, 2, 3, 4, 5, 6, 7, 8]);
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
}
