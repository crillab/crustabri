//! Miscellaneous components used in the library.

mod connected_components_computer;
pub use connected_components_computer::ConnectedComponentsComputer;

mod grounded_extension_computer;
pub(crate) use grounded_extension_computer::grounded_extension;
