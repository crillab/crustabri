//! This module contains the main material used to define Abstract Argumentation frameworks and their related problems.

mod aa_framework;
pub use aa_framework::AAFramework;
pub use aa_framework::Attack;

mod arguments;
pub use arguments::Argument;
pub use arguments::ArgumentSet;

mod problem;
pub use problem::Query;
pub use problem::Semantics;
