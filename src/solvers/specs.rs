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
