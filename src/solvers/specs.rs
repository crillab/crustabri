use crate::{aa::Argument, utils::LabelType};

/// A trait for solvers able to compute an extension.
pub trait SingleExtensionComputer<T>
where
    T: LabelType,
{
    /// Computes a single extension.
    ///
    /// In case the problem admits no extension, [Option::None] is return.
    /// In case an extension is found, it is returned as a vector of arguments.
    fn compute_one_extension(&mut self) -> Option<Vec<&Argument<T>>>;
}

/// A trait for solvers able to check the credulous acceptance of an argument.
pub trait CredulousAcceptanceComputer<T>
where
    T: LabelType,
{
    /// Checks the credulous acceptance of an argument.
    ///
    /// # Panic
    ///
    /// If the provided argument does not belong to the argument set, this function must panic.
    fn is_credulously_accepted(&mut self, arg: &T) -> bool {
        self.are_credulously_accepted([arg].as_slice())
    }

    /// Checks the credulous acceptance of an argument, and provide a certificate if it is the case.
    ///
    /// The certificate is set to `None` if the result of the test is `false`.
    /// Otherwise, the certificate is provided as a set of arguments.
    /// The exact nature of this certificate depends on underlying semantics.
    ///
    /// # Panic
    ///
    /// If the provided arguments does not belong to the argument set, this function must panic.
    fn is_credulously_accepted_with_certificate(
        &mut self,
        arg: &T,
    ) -> (bool, Option<Vec<&Argument<T>>>) {
        self.are_credulously_accepted_with_certificate([arg].as_slice())
    }

    /// Checks the credulous acceptance of a disjunction of arguments.
    ///
    /// # Panic
    ///
    /// If one of the provided argument does not belong to the argument set, this function must panic.
    fn are_credulously_accepted(&mut self, args: &[&T]) -> bool;

    /// Checks the credulous acceptance of a disjunction of arguments, and provide a certificate if it is the case.
    ///
    /// The certificate is set to `None` if the result of the test is `false`.
    /// Otherwise, the certificate is provided as a set of arguments.
    /// The exact nature of this certificate depends on underlying semantics.
    ///
    /// # Panic
    ///
    /// If one of the provided arguments does not belong to the argument set, this function must panic.
    fn are_credulously_accepted_with_certificate(
        &mut self,
        args: &[&T],
    ) -> (bool, Option<Vec<&Argument<T>>>);
}

/// A trait for solvers able to check the skeptical acceptance of an argument.
pub trait SkepticalAcceptanceComputer<T>
where
    T: LabelType,
{
    /// Checks the skeptical acceptance of an argument.
    ///
    /// # Panic
    ///
    /// If the provided argument does not belong to the argument set, this function must panic.
    fn is_skeptically_accepted(&mut self, arg: &T) -> bool {
        self.are_skeptically_accepted([arg].as_slice())
    }

    /// Checks the skeptical acceptance of an argument, and provide a certificate if it is the case.
    ///
    /// The certificate is set to `None` if the result of the test is `true`.
    /// Otherwise, the certificate is provided as a set of arguments.
    /// The exact nature of this certificate depends on underlying semantics.
    ///
    /// /// # Panic
    ///
    /// If the provided argument does not belong to the argument set, this function must panic.
    fn is_skeptically_accepted_with_certificate(
        &mut self,
        arg: &T,
    ) -> (bool, Option<Vec<&Argument<T>>>) {
        self.are_skeptically_accepted_with_certificate([arg].as_slice())
    }

    /// Checks the skeptical acceptance of a disjunction of arguments.
    ///
    /// # Panic
    ///
    /// If one of the provided arguments does not belong to the argument set, this function must panic.
    fn are_skeptically_accepted(&mut self, args: &[&T]) -> bool;

    /// Checks the skeptical acceptance of a disjunction of arguments, and provide a certificate if it is the case.
    ///
    /// The certificate is set to `None` if the result of the test is `true`.
    /// Otherwise, the certificate is provided as a set of arguments.
    /// The exact nature of this certificate depends on underlying semantics.
    ///
    /// /// # Panic
    ///
    /// If one of the provided arguments does not belong to the argument set, this function must panic.
    fn are_skeptically_accepted_with_certificate(
        &mut self,
        args: &[&T],
    ) -> (bool, Option<Vec<&Argument<T>>>);
}
