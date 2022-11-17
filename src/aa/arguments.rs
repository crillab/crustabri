use anyhow::{anyhow, Result};
use std::collections::HashMap;
use std::fmt::Debug;
use std::fmt::Display;
use std::hash::Hash;

/// The trait for argument labels.
///
/// Arguments may be labeled by any type implementing some traits allowing their use in maps and their display.
/// This trait is just a shortcut used to combine them.
///
/// Simple types like [usize] and [String] implements [LabelType].
pub trait LabelType: Clone + Debug + Display + Eq + Hash {}
impl<T: Clone + Debug + Display + Eq + Hash> LabelType for T {}

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
/// # use crustabri::aa::{Argument, LabelType};
/// fn describe_argument<T: LabelType>(a: &Argument<T>) {
///     println!("argument with id {} has the label {}", a.id(), a.label())    ;
/// }
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Argument<T: LabelType> {
    id: usize,
    label: T,
}

impl<T> Argument<T>
where
    T: LabelType,
{
    /// Returns the label of the argument.
    pub fn label(&self) -> &T {
        &self.label
    }

    /// Returns the id of the argument.
    pub fn id(&self) -> usize {
        self.id
    }
}

impl<T> Display for Argument<T>
where
    T: LabelType,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.label)
    }
}

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
pub struct ArgumentSet<T>
where
    T: LabelType,
{
    arguments: Vec<Option<Argument<T>>>,
    label_to_id: HashMap<T, usize>,
    n_removed: usize,
}

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
        let mut argument_set = ArgumentSet {
            arguments: Vec::with_capacity(labels.len()),
            label_to_id: HashMap::with_capacity(labels.len()),
            n_removed: 0,
        };
        labels
            .iter()
            .for_each(|l| argument_set.new_argument(l.clone()));
        argument_set.arguments.shrink_to_fit();
        argument_set.label_to_id.shrink_to_fit();
        argument_set
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
        self.label_to_id.entry(label.clone()).or_insert_with(|| {
            self.arguments.push(Some(Argument {
                id: self.arguments.len(),
                label,
            }));
            self.arguments.len() - 1
        });
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
        match self.label_to_id.remove(label) {
            Some(id) => {
                self.n_removed += 1;
                Ok(self.arguments[id].take().unwrap())
            }
            None => Err(anyhow!("no such argument: {}", label)),
        }
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
        self.arguments.len() - self.n_removed
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
        if self.arguments.is_empty() {
            None
        } else {
            Some(self.arguments.len() - 1)
        }
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
        self.arguments.len() == self.n_removed
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
        self.label_to_id
            .get(label)
            .and_then(|i| self.arguments[*i].as_ref())
            .ok_or_else(|| anyhow!("no such argument: {}", label))
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
        self.arguments[id].as_ref().unwrap()
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
        id < self.arguments.len() && self.arguments[id].is_some()
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
        self.arguments.iter().filter_map(|o| o.as_ref())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_with_labels() {
        let arg_labels = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        let args = ArgumentSet::new_with_labels(&arg_labels);
        assert_eq!(3, args.arguments.len());
        assert_eq!(3, args.label_to_id.len());
        assert_eq!(3, args.len());
        assert!(!args.is_empty());
        for (i, opt_a) in args.arguments.iter().enumerate() {
            let a = opt_a.as_ref().unwrap();
            assert_eq!(i, a.id);
            assert_eq!(arg_labels[i], a.label);
        }
    }

    #[test]
    fn test_new_with_empty_labels() {
        let args = ArgumentSet::new_with_labels(&[] as &[String]);
        assert_eq!(0, args.len());
        assert!(args.is_empty());
    }

    #[test]
    fn test_new_repeated_labels() {
        let arg_labels = vec!["a".to_string(), "b".to_string(), "a".to_string()];
        let args = ArgumentSet::new_with_labels(&arg_labels);
        assert_eq!(2, args.arguments.len());
    }

    #[test]
    fn test_into_iterator() {
        let arg_labels = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        let args = ArgumentSet::new_with_labels(&arg_labels);
        let mut iter_labels: Vec<String> = Vec::with_capacity(arg_labels.len());
        for arg in args.iter() {
            iter_labels.push(arg.label.clone())
        }
        assert_eq!(arg_labels, iter_labels);
    }

    #[test]
    fn test_get_argument() {
        let labels = vec!["a", "b", "c"];
        let arguments = ArgumentSet::new_with_labels(&labels);
        assert!(arguments.get_argument(&"a").is_ok());
        assert!(arguments.get_argument(&"d").is_err());
    }

    #[test]
    fn test_add_arguments() {
        let arg_labels = vec!["a".to_string(), "b".to_string()];
        let mut args = ArgumentSet::new_with_labels(&arg_labels);
        args.new_argument("c".to_string());
        args.new_argument("c".to_string());
        assert_eq!(3, args.arguments.len());
        assert_eq!(2, args.get_argument(&"c".to_string()).unwrap().id())
    }

    #[test]
    fn test_remove_argument() {
        let arg_labels = vec!["a".to_string(), "b".to_string()];
        let mut args = ArgumentSet::new_with_labels(&arg_labels);
        args.n_removed = 0;
        assert_eq!(2, args.arguments.len());
        args.remove_argument(&"b".to_string()).unwrap();
        args.n_removed = 1;
        assert_eq!(1, args.len());
    }

    #[test]
    #[should_panic(expected = "no such argument: c")]
    fn test_remove_nonexisting_argument() {
        let arg_labels = vec!["a".to_string(), "b".to_string()];
        let mut args = ArgumentSet::new_with_labels(&arg_labels);
        args.remove_argument(&"c".to_string()).unwrap();
    }

    #[test]
    fn test_max_id() {
        let mut args = ArgumentSet::default();
        assert!(args.max_id().is_none());
        args.new_argument("a");
        assert_eq!(0, args.max_id().unwrap());
        args.new_argument("a");
        assert_eq!(0, args.max_id().unwrap());
    }
}
