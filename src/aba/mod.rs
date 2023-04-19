//! A module containing the material needed to handle Assumption-based Argumentation frameworks.

mod aba_framework_instantiation;
pub use aba_framework_instantiation::ABAFrameworkInstantiation;

mod aba_framework;
pub use aba_framework::ABAFramework;

mod atom_support_computer;

mod language;
pub use language::Atom;
pub use language::Language;

mod io;
pub use io::Iccma23ABAReader;
pub use io::Iccma23ABAWriter;
