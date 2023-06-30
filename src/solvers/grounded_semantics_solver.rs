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
    fn are_credulously_accepted(&mut self, args: &[&T]) -> bool {
        self.are_credulously_accepted_with_certificate(args).0
    }

    fn are_credulously_accepted_with_certificate(
        &mut self,
        args: &[&T],
    ) -> (bool, Option<Vec<&Argument<T>>>) {
        let ext = self.af.grounded_extension();
        if args
            .iter()
            .any(|a| ext.contains(&self.af.argument_set().get_argument(a).unwrap()))
        {
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
    fn are_skeptically_accepted(&mut self, args: &[&T]) -> bool {
        self.are_skeptically_accepted_with_certificate(args).0
    }

    fn are_skeptically_accepted_with_certificate(
        &mut self,
        args: &[&T],
    ) -> (bool, Option<Vec<&Argument<T>>>) {
        let ext = self.af.grounded_extension();
        if args
            .iter()
            .any(|a| ext.contains(&self.af.argument_set().get_argument(a).unwrap()))
        {
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
        assert!(solver.is_credulously_accepted(&"a0".to_string()));
        assert!(!solver.is_credulously_accepted(&"a1".to_string()));
        assert!(solver.is_skeptically_accepted(&"a0".to_string()));
        assert!(!solver.is_skeptically_accepted(&"a1".to_string()));
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
                .is_credulously_accepted_with_certificate(&"a0".to_string())
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
                .is_skeptically_accepted_with_certificate(&"a1".to_string())
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
            solver.is_skeptically_accepted_with_certificate(&"a0".to_string())
        );
    }

    #[test]
    fn test_disj_credulous_acceptance() {
        let instance = r#"
        arg(a0).
        arg(a1).
        arg(a2).
        arg(a3).
        arg(a4).
        att(a0,a1).
        att(a1,a2).
        att(a1,a3).
        att(a2,a3).
        att(a2,a4).
        att(a3,a2).
        att(a3,a4).
        "#;
        let reader = AspartixReader::default();
        let af = reader.read(&mut instance.as_bytes()).unwrap();
        let mut solver = GroundedSemanticsSolver::new(&af);
        assert!(solver.are_credulously_accepted(&[&"a0".to_string(), &"a1".to_string()]));
        assert!(solver.are_credulously_accepted(&[&"a0".to_string(), &"a2".to_string()]));
        assert!(solver.are_credulously_accepted(&[&"a0".to_string(), &"a3".to_string()]));
        assert!(solver.are_credulously_accepted(&[&"a0".to_string(), &"a4".to_string()]));
        assert!(!solver.are_credulously_accepted(&[&"a1".to_string(), &"a2".to_string()]));
        assert!(!solver.are_credulously_accepted(&[&"a1".to_string(), &"a3".to_string()]));
        assert!(!solver.are_credulously_accepted(&[&"a1".to_string(), &"a4".to_string()]));
        assert!(!solver.are_credulously_accepted(&[&"a2".to_string(), &"a3".to_string()]));
        assert!(!solver.are_credulously_accepted(&[&"a2".to_string(), &"a4".to_string()]));
        assert!(!solver.are_credulously_accepted(&[&"a3".to_string(), &"a4".to_string()]));
    }

    #[test]
    fn test_disj_skeptical_acceptance() {
        let instance = r#"
        arg(a0).
        arg(a1).
        arg(a2).
        arg(a3).
        arg(a4).
        att(a0,a1).
        att(a1,a2).
        att(a1,a3).
        att(a2,a3).
        att(a2,a4).
        att(a3,a2).
        att(a3,a4).
        "#;
        let reader = AspartixReader::default();
        let af = reader.read(&mut instance.as_bytes()).unwrap();
        let mut solver = GroundedSemanticsSolver::new(&af);
        assert!(solver.are_skeptically_accepted(&[&"a0".to_string(), &"a1".to_string()]));
        assert!(solver.are_skeptically_accepted(&[&"a0".to_string(), &"a2".to_string()]));
        assert!(solver.are_skeptically_accepted(&[&"a0".to_string(), &"a3".to_string()]));
        assert!(solver.are_skeptically_accepted(&[&"a0".to_string(), &"a4".to_string()]));
        assert!(!solver.are_skeptically_accepted(&[&"a1".to_string(), &"a2".to_string()]));
        assert!(!solver.are_skeptically_accepted(&[&"a1".to_string(), &"a3".to_string()]));
        assert!(!solver.are_skeptically_accepted(&[&"a1".to_string(), &"a4".to_string()]));
        assert!(!solver.are_skeptically_accepted(&[&"a2".to_string(), &"a3".to_string()]));
        assert!(!solver.are_skeptically_accepted(&[&"a2".to_string(), &"a4".to_string()]));
        assert!(!solver.are_skeptically_accepted(&[&"a3".to_string(), &"a4".to_string()]));
    }
}
