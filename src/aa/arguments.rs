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
pub struct ArgumentSet<T>
where
    T: LabelType,
{
    arguments: Vec<Argument<T>>,
    label_to_id: HashMap<T, usize>,
}

impl<T> ArgumentSet<T>
where
    T: LabelType,
{
    /// Builds a new argument set given the label of the arguments.
    ///
    /// Each argument will be assigned an id equal to its index in the provided slice of argument labels.
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
    /// let arguments = ArgumentSet::new(&labels);
    /// assert_eq!(3, arguments.len());
    /// ```
    pub fn new(labels: &[T]) -> Self {
        let mut label_to_id = HashMap::new();
        ArgumentSet {
            arguments: labels
                .iter()
                .enumerate()
                .map(|(i, s)| {
                    label_to_id.insert(s.clone(), i);
                    Argument {
                        id: i,
                        label: s.clone(),
                    }
                })
                .collect(),
            label_to_id,
        }
    }

    /// Returns the number of arguments in the set.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::ArgumentSet;
    /// let labels = vec!["a", "b", "c"];
    /// let arguments = ArgumentSet::new(&labels);
    /// assert_eq!(3, arguments.len());
    /// ```
    pub fn len(&self) -> usize {
        self.arguments.len()
    }

    /// Returns `true` iff the set has no argument.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::ArgumentSet;
    /// let labels = vec!["a", "b", "c"];
    /// let arguments = ArgumentSet::new(&labels);
    /// assert!(!arguments.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.arguments.is_empty()
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
    /// let arguments = ArgumentSet::new(&labels);
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
    /// let arguments = ArgumentSet::new(&labels);
    /// assert!(arguments.get_argument(&"a").is_ok());
    /// assert!(arguments.get_argument(&"d").is_err());
    /// ```
    pub fn get_argument(&self, label: &T) -> Result<&Argument<T>> {
        self.label_to_id
            .get(label)
            .map(|i| &self.arguments[*i])
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
    /// let arguments = ArgumentSet::new(&labels);
    /// assert_eq!(&labels[0], arguments.get_argument_by_id(0).label());
    /// assert_eq!(&labels[1], arguments.get_argument_by_id(1).label());
    /// assert_eq!(&labels[2], arguments.get_argument_by_id(2).label());
    /// ```
    pub fn get_argument_by_id(&self, id: usize) -> &Argument<T> {
        &self.arguments[id]
    }

    /// Returns an iterator to the arguments.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::ArgumentSet;
    /// let labels = vec!["a", "b", "c"];
    /// let arguments = ArgumentSet::new(&labels);
    /// assert_eq!(3, arguments.iter().count());
    /// ```
    pub fn iter(&self) -> std::slice::Iter<'_, Argument<T>> {
        self.arguments.iter()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new() {
        let arg_labels = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        let args = ArgumentSet::new(&arg_labels);
        assert_eq!(3, args.arguments.len());
        assert_eq!(3, args.label_to_id.len());
        assert_eq!(3, args.len());
        assert!(!args.is_empty());
        for (i, a) in args.arguments.iter().enumerate() {
            assert_eq!(i, a.id);
            assert_eq!(arg_labels[i], a.label);
        }
    }

    #[test]
    fn test_new_empty() {
        let args = ArgumentSet::new(&[] as &[String]);
        assert_eq!(0, args.len());
        assert!(args.is_empty());
    }

    #[test]
    fn test_into_iterator() {
        let arg_labels = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        let args = ArgumentSet::new(&arg_labels);
        let mut iter_labels: Vec<String> = Vec::with_capacity(arg_labels.len());
        for arg in args.iter() {
            iter_labels.push(arg.label.clone())
        }
        assert_eq!(arg_labels, iter_labels);
    }

    #[test]
    fn test_get_argument() {
        let labels = vec!["a", "b", "c"];
        let arguments = ArgumentSet::new(&labels);
        assert!(arguments.get_argument(&"a").is_ok());
        assert!(arguments.get_argument(&"d").is_err());
    }
}
