//! Objects used to encode semantics into SAT solvers.

mod aux_var_complete_constraints_encoder;
pub use aux_var_complete_constraints_encoder::AuxVarCompleteConstraintsEncoder;

mod exp_complete_constraints_encoder;
pub use exp_complete_constraints_encoder::ExpCompleteConstraintsEncoder;

mod aux_var_conflict_freeness_constraints_encoder;
pub use aux_var_conflict_freeness_constraints_encoder::AuxVarConflictFreenessConstraintsEncoder;

mod exp_conflict_freeness_constraints_encoder;
pub use exp_conflict_freeness_constraints_encoder::ExpConflictFreenessConstraintsEncoder;

mod specs;
pub use specs::ConstraintsEncoder;

mod stable_constraints_encoder;
pub use stable_constraints_encoder::DefaultStableConstraintsEncoder;

/// The default encoder for the complete semantics.
pub type DefaultCompleteConstraintsEncoder = AuxVarCompleteConstraintsEncoder;

/// The default encoder for the conflict-freeness based semantics.
pub type DefaultConflictFreenessConstraintsEncoder = AuxVarConflictFreenessConstraintsEncoder;
