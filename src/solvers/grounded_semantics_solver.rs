use crate::{
    AAFramework, Argument, CredulousAcceptanceComputer, LabelType, SingleExtensionComputer,
    SkepticalAcceptanceComputer,
};

/// A solver used to solve queries for the grounded semantics.
pub struct GroundedSemanticsSolver<'a, T>
where
    T: LabelType,
{
    af: &'a AAFramework<T>,
}

impl<'a, T> GroundedSemanticsSolver<'a, T>
where
    T: LabelType,
{
    /// Builds a new solver dedicated to the grounded semantics.
    pub fn new(af: &'a AAFramework<T>) -> Self {
        Self { af }
    }
}

impl<T> SingleExtensionComputer<T> for GroundedSemanticsSolver<'_, T>
where
    T: LabelType,
{
    fn compute_one_extension(&mut self) -> Option<Vec<&Argument<T>>> {
        Some(crate::grounded_extension(self.af))
    }
}

impl<T> CredulousAcceptanceComputer<T> for GroundedSemanticsSolver<'_, T>
where
    T: LabelType,
{
    fn is_credulously_accepted(&mut self, arg: &Argument<T>) -> bool {
        self.is_credulously_accepted_with_certificate(arg).0
    }

    fn is_credulously_accepted_with_certificate(
        &mut self,
        arg: &Argument<T>,
    ) -> (bool, Option<Vec<&Argument<T>>>) {
        let ext = crate::grounded_extension(self.af);
        if ext.contains(&arg) {
            (true, Some(ext))
        } else {
            (false, None)
        }
    }
}

impl<T> SkepticalAcceptanceComputer<T> for GroundedSemanticsSolver<'_, T>
where
    T: LabelType,
{
    fn is_skeptically_accepted(&mut self, arg: &Argument<T>) -> bool {
        crate::grounded_extension(self.af).contains(&arg)
    }

    fn is_skeptically_accepted_with_certificate(
        &mut self,
        arg: &Argument<T>,
    ) -> (bool, Option<Vec<&Argument<T>>>) {
        let ext = crate::grounded_extension(self.af);
        if ext.contains(&arg) {
            (true, None)
        } else {
            (false, Some(ext))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{io::InstanceReader, AspartixReader};

    #[test]
    fn test_grounded_solver() {
        let instance = r#"
        arg(a0).
        arg(a1).
        att(a0,a1).
        "#;
        let reader = AspartixReader::default();
        let af = reader.read(&mut instance.as_bytes()).unwrap();
        let mut solver = GroundedSemanticsSolver::new(&af);
        let ext = solver.compute_one_extension().unwrap();
        assert_eq!(1, ext.len());
        assert_eq!("a0", ext[0].label());
        assert!(solver
            .is_credulously_accepted(af.argument_set().get_argument(&"a0".to_string()).unwrap()));
        assert!(!solver
            .is_credulously_accepted(af.argument_set().get_argument(&"a1".to_string()).unwrap()));
        assert!(solver
            .is_skeptically_accepted(af.argument_set().get_argument(&"a0".to_string()).unwrap()));
        assert!(!solver
            .is_skeptically_accepted(af.argument_set().get_argument(&"a1".to_string()).unwrap()));
    }

    #[test]
    fn test_certificates() {
        let instance = r#"
        arg(a0).
        arg(a1).
        att(a0,a1).
        "#;
        let reader = AspartixReader::default();
        let af = reader.read(&mut instance.as_bytes()).unwrap();
        let mut solver = GroundedSemanticsSolver::new(&af);
        assert_eq!(
            &["a0"],
            solver
                .is_credulously_accepted_with_certificate(
                    af.argument_set().get_argument(&"a0".to_string()).unwrap()
                )
                .1
                .unwrap()
                .iter()
                .map(|a| a.label())
                .cloned()
                .collect::<Vec<String>>()
                .as_slice()
        );
        assert_eq!(
            &["a0"],
            solver
                .is_skeptically_accepted_with_certificate(
                    af.argument_set().get_argument(&"a1".to_string()).unwrap()
                )
                .1
                .unwrap()
                .iter()
                .map(|a| a.label())
                .cloned()
                .collect::<Vec<String>>()
                .as_slice()
        );
        assert_eq!(
            (true, None),
            solver.is_skeptically_accepted_with_certificate(
                af.argument_set().get_argument(&"a0".to_string()).unwrap()
            )
        );
    }
}
