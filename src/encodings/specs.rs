use crate::{
    aa::{AAFramework, Argument},
    sat::{Assignment, Literal, SatSolver},
    utils::LabelType,
};

/// The trait for encoders from AF to SAT.
pub trait ConstraintsEncoder<T>
where
    T: LabelType,
{
    /// Encodes the constraints for the underlying semantics into the SAT solver.
    fn encode_constraints(&self, af: &AAFramework<T>, solver: &mut dyn SatSolver);

    /// Adds some variables and constraints to encode the range of extensions.
    fn encode_range_constraints(&self, af: &AAFramework<T>, solver: &mut dyn SatSolver) -> usize;

    /// Translates back a SAT assignment into the corresponding set of arguments.
    fn assignment_to_extension<'a>(
        &self,
        assignment: &Assignment,
        af: &'a AAFramework<T>,
    ) -> Vec<&'a Argument<T>>;

    /// Translates an argument into the literal that represent it.
    fn arg_to_lit(&self, arg: &Argument<T>) -> Literal;
}
