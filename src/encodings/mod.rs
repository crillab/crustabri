//! Objects used to encode semantics into SAT solvers.

use crate::utils::LabelType;

pub mod aux_var_constraints_encoder;

/// Returns the default encoder for complete semantics.
pub fn new_default_complete_constraints_encoder<T>() -> Box<dyn ConstraintsEncoder<T>>
where
    T: LabelType,
{
    Box::new(aux_var_constraints_encoder::new_for_conflict_freeness())
}

pub mod exp_constraints_encoder;

/// Returns the default encoder for complete semantics.
pub fn new_default_conflict_freeness_encoder<T>() -> Box<dyn ConstraintsEncoder<T>>
where
    T: LabelType,
{
    Box::new(exp_constraints_encoder::new_for_conflict_freeness())
}

mod hybrid_complete_constraints_encoder;
pub use hybrid_complete_constraints_encoder::HybridCompleteConstraintsEncoder;

mod specs;
pub use specs::ConstraintsEncoder;

mod stable_constraints_encoder;
pub use stable_constraints_encoder::DefaultStableConstraintsEncoder;
