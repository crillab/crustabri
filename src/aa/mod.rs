//! This module contains the main material used to define Abstract Argumentation.

mod aa_framework;
pub use aa_framework::AAFramework;
pub use aa_framework::Attack;

mod arguments;
pub use arguments::Argument;
pub use arguments::ArgumentSet;
pub use arguments::LabelType;

mod problem;
pub use problem::iter_problem_strings;
pub use problem::read_problem_string;
pub use problem::Query;
pub use problem::Semantics;
