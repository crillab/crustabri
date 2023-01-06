use crate::utils::LabelType;
use anyhow::Result;

/// A trait for argumentation solvers that are able to deal with dynamic argumentation frameworks.
///
/// Dynamic AF are frameworks that evolve during the time.
/// A solver may use some information gathered during previous computations in order to speedup further searches.
pub trait DynamicSolver<T>
where
    T: LabelType,
{
    /// Adds a new argument to the underlying AF.
    fn new_argument(&mut self, label: T);

    /// Removes an argument from the underlying AF.
    fn remove_argument(&mut self, label: &T) -> Result<()>;

    /// Adds an attack to the underlying AF.
    fn new_attack(&mut self, from: &T, to: &T) -> Result<()>;

    /// Removes an attack from the underlying AF.
    fn remove_attack(&mut self, from: &T, to: &T) -> Result<()>;
}
