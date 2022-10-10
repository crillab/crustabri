use crate::{Argument, LabelType};

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
    fn is_credulously_accepted(&mut self, arg: &Argument<T>) -> bool;
}

/// A trait for solvers able to check the skeptical acceptance of an argument.
pub trait SkepticalAcceptanceComputer<T>
where
    T: LabelType,
{
    /// Checks the skeptical acceptance of an argument.
    fn is_skeptically_accepted(&mut self, arg: &Argument<T>) -> bool;
}
