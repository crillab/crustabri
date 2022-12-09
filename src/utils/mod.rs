//! Miscellaneous components used in the library.

mod connected_components_computer;
pub(crate) use connected_components_computer::ConnectedComponentsComputer;

mod label;
pub(crate) use label::Label;
pub use label::LabelSet;
pub use label::LabelType;

mod grounded_extension_computer;
pub(crate) use grounded_extension_computer::grounded_extension;
