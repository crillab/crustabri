use crate::utils::Label;
use crate::utils::LabelSet;
use crate::utils::LabelType;
use anyhow::Result;

/// Handles a single argument.
///
/// Each argument has a label and an identifier which are unique in an argument set.
/// This uniqueness condition imposes arguments are made from [ArgumentSet] objects, and not directly by the [Argument] struct.
/// If an argument is deleted from its set, a new one with the same label may be created;
/// however, the id of the removed argument will not be used for a newer argument.
///
/// The type of the labels must be [`LabelType`] instances.
/// The type associated with an argument is the one associated with its argument set.
///
/// # Example
///
/// ```
/// # use crustabri::aa::{Argument};
/// # use crustabri::utils::LabelType;
/// fn describe_argument<T: LabelType>(a: &Argument<T>) {
///     println!("argument with id {} has the label {}", a.id(), a.label())    ;
/// }
/// ```
pub type Argument<T> = Label<T>;

/// Handles a set of arguments in an Abstract Argumentation framework.
///
/// This structure ensures all arguments have unique identifiers and labels.
/// Arguments are created by giving their labels, while identifiers are determined by the argument set at their creation.
///
/// Arguments may be deleted.
/// If an argument is deleted from its set, a new one with the same label may be created;
/// however, the id of the removed argument will not be used for a newer argument.
///
/// The type of the labels must be [`LabelType`] instances.
/// The type associated with an argument is the one associated with its argument set.
#[derive(Default)]
pub struct ArgumentSet<T>(LabelSet<T>)
where
    T: LabelType;

impl<T> ArgumentSet<T>
where
    T: LabelType,
{
    /// Builds a new argument set given the labels of the arguments.
    ///
    /// If a label appears multiple times, the first occurrence is the only one that is considered.
    /// Each argument will be assigned an id equal to its index in the provided slice of argument labels (after the removal of the duplicates).
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::aa::ArgumentSet;
    /// let labels = vec!["a", "b"];
    /// let arguments = ArgumentSet::new_with_labels(&labels);
    /// assert_eq!(2, arguments.len());
    /// assert_eq!(0, arguments.get_argument(&"a").unwrap().id());
    /// assert_eq!(1, arguments.get_argument(&"b").unwrap().id());
    /// ```
    pub fn new_with_labels(labels: &[T]) -> Self {
        Self(LabelSet::new_with_labels(labels))
    }

    /// Adds a new argument to this set.
    ///
    /// The id of the new argument is the previous maximal id that have been given (including arguments that have been deleted) plus one.
    /// In an argument with the same label is already defined, no argument is added.
    ///
    /// ```
    /// # use crustabri::aa::ArgumentSet;
    /// let arg_labels = vec!["a", "b"];
    /// let mut arguments = ArgumentSet::new_with_labels(&arg_labels);
    /// assert_eq!(2, arguments.len());
    /// arguments.new_argument("c");
    /// assert_eq!(3, arguments.len());
    /// assert_eq!(2, arguments.get_argument(&"c").unwrap().id());
    /// arguments.new_argument("c");
    /// assert_eq!(3, arguments.len());
    /// ```
    pub fn new_argument(&mut self, label: T) {
        self.0.new_label(label)
    }

    /// Removes an argument from this set.
    ///
    /// The argument id will not be attributed to new arguments, but an argument with the same label can be added.
    ///
    /// An error is returned if no argument with the provided label exists.
    ///
    /// ```
    /// # use crustabri::aa::ArgumentSet;
    /// let arg_labels = vec!["a", "b"];
    /// let mut arguments = ArgumentSet::new_with_labels(&arg_labels);
    /// assert_eq!(2, arguments.len());
    /// assert_eq!(1, arguments.get_argument(&"b").unwrap().id());
    /// assert!(arguments.remove_argument(&"b").is_ok());
    /// assert!(arguments.remove_argument(&"b").is_err());
    /// assert_eq!(1, arguments.len());
    /// arguments.new_argument("b");
    /// assert_eq!(2, arguments.len());
    /// assert_eq!(2, arguments.get_argument(&"b").unwrap().id());
    /// ```
    pub fn remove_argument(&mut self, label: &T) -> Result<Argument<T>> {
        self.0.remove_label(label)
    }

    /// Returns the number of arguments in the set.
    ///
    /// This number does not take into account the arguments that have been removed.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::aa::ArgumentSet;
    /// let arg_labels = vec!["a", "b"];
    /// let mut arguments = ArgumentSet::new_with_labels(&arg_labels);
    /// assert_eq!(2, arguments.len());
    /// arguments.remove_argument(&"b");
    /// assert_eq!(1, arguments.len());
    /// ```
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Returns the maximal argument id given so far, or `None` if no argument has been added yet.
    ///
    /// This id may refer to a removed argument.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::aa::ArgumentSet;
    /// let arg_labels = vec!["a", "b"];
    /// let mut arguments = ArgumentSet::new_with_labels(&arg_labels);
    /// assert_eq!(1, arguments.max_id().unwrap());
    /// arguments.remove_argument(&"b");
    /// assert_eq!(1, arguments.max_id().unwrap());
    /// ```
    pub fn max_id(&self) -> Option<usize> {
        self.0.max_id()
    }

    /// Returns `true` if and only if the set has no argument.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::aa::ArgumentSet;
    /// let arg_labels = vec!["a", "b"];
    /// let mut arguments = ArgumentSet::new_with_labels(&arg_labels);
    /// assert!(!arguments.is_empty());
    /// arguments.remove_argument(&"a");
    /// arguments.remove_argument(&"b");
    /// assert!(arguments.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Returns the argument associated to an argument label.
    ///
    /// In case no such argument exists, an error is returned.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::aa::ArgumentSet;
    /// let labels = vec!["a", "b", "c"];
    /// let arguments = ArgumentSet::new_with_labels(&labels);
    /// assert!(arguments.get_argument(&"a").is_ok());
    /// assert!(arguments.get_argument(&"d").is_err());
    /// ```
    pub fn get_argument(&self, label: &T) -> Result<&Argument<T>> {
        self.0.get_label(label)
    }

    /// Returns the argument with the corresponding id.
    ///
    /// Indexes are [usize] from 0 to `n - 1`, where `n` is the number of arguments created so far in this set.
    /// Beware that arguments may be removed; in this case, their identifiers does not refer anymore to existing arguments, making this function panic.
    ///
    /// # Panics
    ///
    /// Panics if no argument has such id.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::aa::ArgumentSet;
    /// let labels = vec!["a", "b", "c"];
    /// let arguments = ArgumentSet::new_with_labels(&labels);
    /// assert_eq!(&labels[0], arguments.get_argument_by_id(0).label());
    /// assert_eq!(&labels[1], arguments.get_argument_by_id(1).label());
    /// assert_eq!(&labels[2], arguments.get_argument_by_id(2).label());
    /// ```
    pub fn get_argument_by_id(&self, id: usize) -> &Argument<T> {
        self.0.get_label_by_id(id)
    }

    /// Returns `true` if and only if an argument with the provided id exists.
    ///
    /// If the argument existed but has been remove, this function returns `false`.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::aa::ArgumentSet;
    /// let labels = vec!["a", "b", "c"];
    /// let mut arguments = ArgumentSet::new_with_labels(&labels);
    /// arguments.remove_argument(&"b");
    /// assert!(arguments.has_argument_with_id(0));
    /// assert!(!arguments.has_argument_with_id(1));
    /// assert!(arguments.has_argument_with_id(2));
    /// ```
    pub fn has_argument_with_id(&self, id: usize) -> bool {
        self.0.has_label_with_id(id)
    }

    /// Returns an iterator to the arguments.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::aa::ArgumentSet;
    /// let labels = vec!["a", "b", "c"];
    /// let arguments = ArgumentSet::new_with_labels(&labels);
    /// assert_eq!(3, arguments.iter().count());
    /// ```
    pub fn iter(&self) -> impl Iterator<Item = &Argument<T>> + '_ {
        self.0.iter()
    }
}
