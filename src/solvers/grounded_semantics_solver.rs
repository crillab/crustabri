use super::{CredulousAcceptanceComputer, SingleExtensionComputer, SkepticalAcceptanceComputer};
use crate::{
    aa::{AAFramework, Argument},
    utils::LabelType,
};

/// A solver used to solve queries for the grounded semantics.
///
/// The (unique) grounded extension is the minimal complete extension (see [CompleteSemanticsSolver](crate::solvers::CompleteSemanticsSolver) for more information).
/// It is computed in time polynomial in the size of the framework.
///
/// This solver implements [SingleExtensionComputer] and both [CredulousAcceptanceComputer] and [SkepticalAcceptanceComputer] interfaces.
/// In these three cases, the computation resumes to the (polynomial time) computation of the grounded extension.
///
/// When a certificate is provided, the certificate is the grounded extension itself.
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
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::aa::{AAFramework};
    /// # use crustabri::utils::LabelType;
    /// # use crustabri::solvers::{SingleExtensionComputer, GroundedSemanticsSolver};
    /// fn search_one_extension<T>(af: &AAFramework<T>) where T: LabelType {
    ///     let mut solver = GroundedSemanticsSolver::new(af);
    ///     let ext = solver.compute_one_extension().unwrap();
    ///     println!("found the grounded extension: {:?}", ext);
    /// }
    /// # search_one_extension::<usize>(&AAFramework::default());
    /// ```
    pub fn new(af: &'a AAFramework<T>) -> Self {
        Self { af }
    }
}

impl<T> SingleExtensionComputer<T> for GroundedSemanticsSolver<'_, T>
where
    T: LabelType,
{
    fn compute_one_extension(&mut self) -> Option<Vec<&Argument<T>>> {
        Some(self.af.grounded_extension())
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
        let ext = self.af.grounded_extension();
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
        self.af.grounded_extension().contains(&arg)
    }

    fn is_skeptically_accepted_with_certificate(
        &mut self,
        arg: &Argument<T>,
    ) -> (bool, Option<Vec<&Argument<T>>>) {
        let ext = self.af.grounded_extension();
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
    use crate::io::{AspartixReader, InstanceReader};

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
