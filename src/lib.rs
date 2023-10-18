//! Crustabri is a RUST ABstract argumentation Reasoner Implementation.
//!
//! This library provides datastructures and functions used to handle argumentation frameworks and to execute queries on them.
//! Take a look at the example below to get an overview, and browse this documentation to see its capabilities.
//!
//! # Example
//!
//! ```
//! # use crustabri::aa::{ArgumentSet, AAFramework};
//! # use crustabri::solvers::{SingleExtensionComputer, StableSemanticsSolver};
//! let labels = vec!["a", "b", "c"];
//! let arguments = ArgumentSet::new_with_labels(&labels);
//! let mut framework = AAFramework::new_with_argument_set(arguments);
//! framework.new_attack(&labels[0], &labels[1]);
//! let mut solver = StableSemanticsSolver::new(&framework);
//! let opt_ext = solver.compute_one_extension();
//! if let Some(ext) = opt_ext {
//!     println!("found an extension: {:?}", ext);
//! } else {
//!     println!("the problem has no stable extension");
//! }
//! ```

#![warn(missing_docs)]

pub mod aa;

pub mod dynamics;
pub mod dynamics_attacks;

pub mod encodings;

pub mod io;

pub mod solvers;

pub mod sat;

pub mod utils;
