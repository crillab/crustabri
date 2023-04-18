//! Miscellaneous components used in the library.

mod connected_components_computer;
pub(crate) use connected_components_computer::ConnectedComponentsComputer;

mod equivalency_computer;
pub use equivalency_computer::EquivalencyComputer;

mod label;
pub use label::Label;
pub use label::LabelSet;
pub use label::LabelType;

mod grounded_extension_computer;
pub(crate) use grounded_extension_computer::grounded_extension;
