use anyhow::{anyhow, Result};
use std::collections::HashMap;
use std::fmt::Debug;
use std::fmt::Display;
use std::hash::Hash;

/// The trait for argument labels.
///
/// Arguments may be labeled by any type implementing some traits.
/// This trait is used to combine them.
pub trait LabelType: Clone + Debug + Display + Eq + Hash {}
impl<T: Clone + Debug + Display + Eq + Hash> LabelType for T {}

/// Handles a single argument.
///
/// Each argument has a label and an identifier which is unique in an argument set.
/// The label must be a [`LabelType`].
///
/// Arguments are built by [`ArgumentSet`] objects.
///
/// [`LabelType`]: trait.LabelType.html
/// [`ArgumentSet`]: struct.ArgumentSet.html
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
    ///
    /// Example
    ///
    /// ```
    /// # use crustabri::{Argument, LabelType};
    /// fn describe_argument<T: LabelType>(a: &Argument<T>) {
    ///     println!("argument with id {} has the label {}", a.id(), a.label())    ;
    /// }
    /// ```
    pub fn label(&self) -> &T {
        &self.label
    }

    /// Returns the id of the argument.
    ///
    /// Example
    ///
    /// ```
    /// # use crustabri::{Argument, LabelType};
    /// fn describe_argument<T: LabelType>(a: &Argument<T>) {
    ///     println!("argument with id {} has the label {}", a.id(), a.label())    ;
    /// }
    /// ```
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

/// Handles the set of arguments of an AA framework.
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
    /// Each argument will be assigned an id equal to its index in the provided slice of argument labels.
    /// If a label appears multiple times, the first occurrence is the only one that is considered.
    ///
    /// # Arguments
    ///
    /// * `labels` - the argument labels
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::ArgumentSet;
    /// let labels = vec!["a", "b", "c"];
    /// let arguments = ArgumentSet::new_with_labels(&labels);
    /// assert_eq!(3, arguments.len());
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
    /// The id of the new argument is the previous maximal id plus one.
    /// In an argument with the same label is already defined, no argument is added.
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
    /// The argument id will not be attributed to new arguments.
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
    /// # Example
    ///
    /// ```
    /// # use crustabri::ArgumentSet;
    /// let labels = vec!["a", "b", "c"];
    /// let arguments = ArgumentSet::new_with_labels(&labels);
    /// assert_eq!(3, arguments.len());
    /// ```
    pub fn len(&self) -> usize {
        self.arguments.len() - self.n_removed
    }

    /// Returns the maximal argument id given so far, or `None` if no argument has been added yet.
    ///
    /// This id may refer to a removed argument.
    pub fn max_id(&self) -> Option<usize> {
        if self.arguments.is_empty() {
            None
        } else {
            Some(self.arguments.len() - 1)
        }
    }

    /// Returns `true` iff the set has no argument.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::ArgumentSet;
    /// let labels = vec!["a", "b", "c"];
    /// let arguments = ArgumentSet::new_with_labels(&labels);
    /// assert!(!arguments.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.arguments.len() == self.n_removed
    }

    /// Returns the unique index associated to an argument label.
    ///
    /// If no such label exists, an error is returned.
    ///
    /// See constructor methods for information about indexes.
    ///
    /// # Arguments
    ///
    /// * `label` - the argument label
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::ArgumentSet;
    /// let labels = vec!["a", "b", "c"];
    /// let arguments = ArgumentSet::new_with_labels(&labels);
    /// assert_eq!(0, arguments.get_argument_index(&labels[0]).unwrap());
    /// assert_eq!(1, arguments.get_argument_index(&labels[1]).unwrap());
    /// assert_eq!(2, arguments.get_argument_index(&labels[2]).unwrap());
    /// ```
    pub fn get_argument_index(&self, label: &T) -> Result<usize> {
        self.label_to_id
            .get(label)
            .ok_or_else(|| anyhow!("no such argument: {}", label))
            .map(|i| *i)
    }

    /// Returns the argument associated to an argument label.
    ///
    /// # Arguments
    ///
    /// * `label` - the argument label
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::ArgumentSet;
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
    /// See constructor methods for information about indexes.
    ///
    /// # Panics
    ///
    /// Panics if no argument has such id.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::ArgumentSet;
    /// let labels = vec!["a", "b", "c"];
    /// let arguments = ArgumentSet::new_with_labels(&labels);
    /// assert_eq!(&labels[0], arguments.get_argument_by_id(0).label());
    /// assert_eq!(&labels[1], arguments.get_argument_by_id(1).label());
    /// assert_eq!(&labels[2], arguments.get_argument_by_id(2).label());
    /// ```
    pub fn get_argument_by_id(&self, id: usize) -> &Argument<T> {
        self.arguments[id].as_ref().unwrap()
    }

    /// Returns an iterator to the arguments.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::ArgumentSet;
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
}
