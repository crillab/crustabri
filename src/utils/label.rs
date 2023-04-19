use anyhow::{anyhow, Result};
use std::{
    collections::HashMap,
    fmt::{Debug, Display},
    hash::Hash,
};

/// The trait for argument and atom labels.
///
/// Arguments and atoms may be labeled by any type implementing some traits allowing their use in maps and their display.
/// This trait is just a shortcut used to combine them.
///
/// Simple types like [usize] and [String] implements [LabelType].
pub trait LabelType: Clone + Debug + Display + Eq + Hash {}
impl<T: Clone + Debug + Display + Eq + Hash> LabelType for T {}

/// An (abstract) argument type, associated with a unique identifier.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Label<T>
where
    T: LabelType,
{
    id: usize,
    label: T,
}

impl<T> Label<T>
where
    T: LabelType,
{
    pub(crate) fn new(id: usize, label: T) -> Self {
        Self { id, label }
    }

    /// Returns the argument label.
    pub fn label(&self) -> &T {
        &self.label
    }

    /// Returns the argument associated with the label.
    pub fn id(&self) -> usize {
        self.id
    }
}

impl<T> Display for Label<T>
where
    T: LabelType,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.label)
    }
}

/// Handles a set of labels, each one with a unique id.
///
/// This structure ensures all labels have a unique identifier.
///
/// Labels may be deleted.
/// If a label is deleted from its set, it can be added again later;
/// however, the id of the removed label will not be used for a newer label (even if is is equivalent to the removed one).
///
/// The type of the labels must be [`LabelType`] instances.
#[derive(Default)]
pub struct LabelSet<T>
where
    T: LabelType,
{
    labels: Vec<Option<Label<T>>>,
    label_to_id: HashMap<T, usize>,
    n_removed: usize,
}

impl<T> LabelSet<T>
where
    T: LabelType,
{
    /// Builds a new label set initialized with a set of labels.
    ///
    /// If a label appears multiple times, the first occurrence is the only one that is considered.
    /// Each label will be assigned an id equal to its index in the provided slice of labels (after the removal of the duplicates).
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::utils::LabelSet;
    /// let labels = vec!["a", "b"];
    /// let labels = LabelSet::new_with_labels(&labels);
    /// assert_eq!(2, labels.len());
    /// assert_eq!(0, labels.get_label(&"a").unwrap().id());
    /// assert_eq!(1, labels.get_label(&"b").unwrap().id());
    /// ```
    pub fn new_with_labels(labels: &[T]) -> Self {
        let mut label_set = LabelSet {
            labels: Vec::with_capacity(labels.len()),
            label_to_id: HashMap::with_capacity(labels.len()),
            n_removed: 0,
        };
        labels.iter().for_each(|l| label_set.new_label(l.clone()));
        label_set.labels.shrink_to_fit();
        label_set.label_to_id.shrink_to_fit();
        label_set
    }

    /// Adds a new label to this set.
    ///
    /// The id of the new label is the previous maximal id that have been given (including labels that have been deleted) plus one.
    /// In the label is already present in the set, nothing is added.
    ///
    /// ```
    /// # use crustabri::utils::LabelSet;
    /// let labels = vec!["a", "b"];
    /// let mut label_set = LabelSet::new_with_labels(&labels);
    /// assert_eq!(2, label_set.len());
    /// label_set.new_label("c");
    /// assert_eq!(3, label_set.len());
    /// assert_eq!(2, label_set.get_label(&"c").unwrap().id());
    /// label_set.new_label("c");
    /// assert_eq!(3, label_set.len());
    /// ```
    pub fn new_label(&mut self, label: T) {
        self.label_to_id.entry(label.clone()).or_insert_with(|| {
            self.labels.push(Some(Label::new(self.labels.len(), label)));
            self.labels.len() - 1
        });
    }

    /// Removes a label from this set.
    ///
    /// The label id will not be attributed to new labels.
    /// If the same label is added later, a new id will be attributed to id.
    ///
    /// An error is returned if the label is not present in the set.
    ///
    /// ```
    /// # use crustabri::utils::LabelSet;
    /// let labels = vec!["a", "b"];
    /// let mut label_set = LabelSet::new_with_labels(&labels);
    /// assert_eq!(2, label_set.len());
    /// assert_eq!(1, label_set.get_label(&"b").unwrap().id());
    /// assert!(label_set.remove_label(&"b").is_ok());
    /// assert!(label_set.remove_label(&"b").is_err());
    /// assert_eq!(1, label_set.len());
    /// label_set.new_label("b");
    /// assert_eq!(2, label_set.len());
    /// assert_eq!(2, label_set.get_label(&"b").unwrap().id());
    /// ```
    pub fn remove_label(&mut self, label: &T) -> Result<Label<T>> {
        match self.label_to_id.remove(label) {
            Some(id) => {
                self.n_removed += 1;
                Ok(self.labels[id].take().unwrap())
            }
            None => Err(anyhow!("no such label: {}", label)),
        }
    }

    /// Returns the number of labels in the set.
    ///
    /// This number does not take into account the labels that have been removed.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::utils::LabelSet;
    /// let labels = vec!["a", "b"];
    /// let mut label_set = LabelSet::new_with_labels(&labels);
    /// assert_eq!(2, label_set.len());
    /// label_set.remove_label(&"b");
    /// assert_eq!(1, label_set.len());
    /// ```
    pub fn len(&self) -> usize {
        self.labels.len() - self.n_removed
    }

    /// Returns the maximal label id given so far, or `None` if no label has been added yet.
    ///
    /// This id may refer to a removed label.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::utils::LabelSet;
    /// let labels = vec!["a", "b"];
    /// let mut label_set = LabelSet::new_with_labels(&labels);
    /// assert_eq!(1, label_set.max_id().unwrap());
    /// label_set.remove_label(&"b");
    /// assert_eq!(1, label_set.max_id().unwrap());
    /// ```
    pub fn max_id(&self) -> Option<usize> {
        if self.labels.is_empty() {
            None
        } else {
            Some(self.labels.len() - 1)
        }
    }

    /// Returns `true` if and only if the set has no label.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::utils::LabelSet;
    /// let labels = vec!["a", "b"];
    /// let mut label_set = LabelSet::new_with_labels(&labels);
    /// assert!(!label_set.is_empty());
    /// label_set.remove_label(&"a");
    /// label_set.remove_label(&"b");
    /// assert!(label_set.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.labels.len() == self.n_removed
    }

    /// Returns the label object associated to a label.
    ///
    /// In case no such label exists, an error is returned.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::utils::LabelSet;
    /// let labels = vec!["a", "b", "c"];
    /// let labels = LabelSet::new_with_labels(&labels);
    /// assert!(labels.get_label(&"a").is_ok());
    /// assert!(labels.get_label(&"d").is_err());
    /// ```
    pub fn get_label(&self, label: &T) -> Result<&Label<T>> {
        self.label_to_id
            .get(label)
            .and_then(|i| self.labels[*i].as_ref())
            .ok_or_else(|| anyhow!("no such label: {}", label))
    }

    /// Returns the label with the corresponding id.
    ///
    /// Indexes are [usize] from 0 to `n - 1`, where `n` is the number of labels created so far in this set.
    /// Beware that labels may be removed; in this case, their identifiers does not refer anymore to existing labels, making this function panic.
    ///
    /// # Panics
    ///
    /// Panics if no label has such id.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::utils::LabelSet;
    /// let labels = vec!["a", "b", "c"];
    /// let label_set = LabelSet::new_with_labels(&labels);
    /// assert_eq!(&labels[0], label_set.get_label_by_id(0).label());
    /// assert_eq!(&labels[1], label_set.get_label_by_id(1).label());
    /// assert_eq!(&labels[2], label_set.get_label_by_id(2).label());
    /// ```
    pub fn get_label_by_id(&self, id: usize) -> &Label<T> {
        self.labels[id].as_ref().unwrap()
    }

    /// Returns `true` if and only if a label with the provided id exists.
    ///
    /// If the label existed but has been remove, this function returns `false`.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::utils::LabelSet;
    /// let labels = vec!["a", "b", "c"];
    /// let mut labels = LabelSet::new_with_labels(&labels);
    /// labels.remove_label(&"b");
    /// assert!(labels.has_label_with_id(0));
    /// assert!(!labels.has_label_with_id(1));
    /// assert!(labels.has_label_with_id(2));
    /// ```
    pub fn has_label_with_id(&self, id: usize) -> bool {
        id < self.labels.len() && self.labels[id].is_some()
    }

    /// Returns an iterator to the labels.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::utils::LabelSet;
    /// let labels = vec!["a", "b", "c"];
    /// let labels = LabelSet::new_with_labels(&labels);
    /// assert_eq!(3, labels.iter().count());
    /// ```
    pub fn iter(&self) -> impl Iterator<Item = &Label<T>> + '_ {
        self.labels.iter().filter_map(|o| o.as_ref())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_with_labels() {
        let str_labels = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        let labels = LabelSet::new_with_labels(&str_labels);
        assert_eq!(3, labels.labels.len());
        assert_eq!(3, labels.label_to_id.len());
        assert_eq!(3, labels.len());
        assert!(!labels.is_empty());
        for (i, opt_a) in labels.labels.iter().enumerate() {
            let a = opt_a.as_ref().unwrap();
            assert_eq!(i, a.id());
            assert_eq!(&str_labels[i], a.label());
        }
    }

    #[test]
    fn test_new_with_empty_labels() {
        let args = LabelSet::new_with_labels(&[] as &[String]);
        assert_eq!(0, args.len());
        assert!(args.is_empty());
    }

    #[test]
    fn test_new_repeated_labels() {
        let str_labels = vec!["a".to_string(), "b".to_string(), "a".to_string()];
        let labels = LabelSet::new_with_labels(&str_labels);
        assert_eq!(2, labels.labels.len());
    }

    #[test]
    fn test_into_iterator() {
        let str_labels = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        let labels = LabelSet::new_with_labels(&str_labels);
        let mut iter_labels: Vec<String> = Vec::with_capacity(str_labels.len());
        for l in labels.iter() {
            iter_labels.push(l.label().clone())
        }
        assert_eq!(str_labels, iter_labels);
    }

    #[test]
    fn test_get_label() {
        let str_labels = vec!["a", "b", "c"];
        let labels = LabelSet::new_with_labels(&str_labels);
        assert!(labels.get_label(&"a").is_ok());
        assert!(labels.get_label(&"d").is_err());
    }

    #[test]
    fn test_add_labels() {
        let str_labels = vec!["a".to_string(), "b".to_string()];
        let mut labels = LabelSet::new_with_labels(&str_labels);
        labels.new_label("c".to_string());
        labels.new_label("c".to_string());
        assert_eq!(3, labels.labels.len());
        assert_eq!(2, labels.get_label(&"c".to_string()).unwrap().id())
    }

    #[test]
    fn test_remove_label() {
        let str_labels = vec!["a".to_string(), "b".to_string()];
        let mut labels = LabelSet::new_with_labels(&str_labels);
        labels.n_removed = 0;
        assert_eq!(2, labels.labels.len());
        labels.remove_label(&"b".to_string()).unwrap();
        labels.n_removed = 1;
        assert_eq!(1, labels.len());
    }

    #[test]
    #[should_panic(expected = "no such label: c")]
    fn test_remove_nonexisting_label() {
        let str_labels = vec!["a".to_string(), "b".to_string()];
        let mut labels = LabelSet::new_with_labels(&str_labels);
        labels.remove_label(&"c".to_string()).unwrap();
    }

    #[test]
    fn test_max_id() {
        let mut labels = LabelSet::default();
        assert!(labels.max_id().is_none());
        labels.new_label("a");
        assert_eq!(0, labels.max_id().unwrap());
        labels.new_label("a");
        assert_eq!(0, labels.max_id().unwrap());
    }
}
