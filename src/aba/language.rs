use crate::utils::{Label, LabelSet, LabelType};
use anyhow::Result;

/// Handles an atom of the language.
///
/// Each atom has a label and an identifier which are unique in a language.
/// This uniqueness condition imposes atoms are made from [Language] objects, and not directly by the [Atom] struct.
///
/// The type of the labels must be [`LabelType`] instances.
/// The type associated with an atom is the one associated with its language.
pub type Atom<T> = Label<T>;

/// Handles the atoms that may be used in an ABA framework.
///
/// # Example
///
/// ```
/// # use crustabri::aba::Language;
/// let language = Language::new_with_labels(&["a", "b", "c", "p", "q", "r", "s", "t"]);
/// for (i,s) in language.iter().enumerate() {
///     assert_eq!(i, language.get_atom(s.label()).unwrap().id());
///     assert_eq!(s, language.get_atom_by_id(i));
///     println!("atom {} is {}", i, s.label());
/// }
/// ```
pub struct Language<T>(LabelSet<T>)
where
    T: LabelType;

impl<T> Language<T>
where
    T: LabelType,
{
    /// Builds a new language given the labels of the atoms.
    ///
    /// Each atom will be assigned an id equal to its index in the provided slice of atom names.
    /// If a label appears multiple times, the first occurrence is the only one that is considered.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::aba::Language;
    /// let language = Language::new_with_labels(&["a", "b", "c", "p", "q", "r", "s", "t"]);
    /// for (i,s) in language.iter().enumerate() {
    ///     let label = format!("{}", s.label());
    ///     println!("atom {} is {}", i, &label);
    /// }
    /// ```
    pub fn new_with_labels(labels: &[T]) -> Self {
        Self(LabelSet::new_with_labels(labels))
    }

    /// Returns the number of atoms in the language.
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Returns `true` iff the language has no atom .
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Returns the unique index associated to an atom label.
    ///
    /// See constructor methods for indices.
    /// An error is returned if no atom corresponds to the provided label.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::aba::Language;
    /// let language = Language::new_with_labels(&["a", "b", "c", "p", "q", "r", "s", "t"]);
    /// for (i,s) in language.iter().enumerate() {
    ///     assert_eq!(i, language.get_atom(s.label()).unwrap().id());
    /// }
    /// ```
    pub fn get_atom(&self, label: &T) -> Result<&Atom<T>> {
        self.0.get_label(label)
    }

    /// Returns the atom with the corresponding identifier.
    ///
    /// # Panics
    ///
    /// Panics if atom has the corresponding identifier.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::aba::Language;
    /// let language = Language::new_with_labels(&["a", "b", "c", "p", "q", "r", "s", "t"]);
    /// for (i,s) in language.iter().enumerate() {
    ///     assert_eq!(s, language.get_atom_by_id(i));
    /// }
    /// ```
    pub fn get_atom_by_id(&self, id: usize) -> &Atom<T> {
        self.0.get_label_by_id(id)
    }

    /// Provides an iterator to the atoms.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::aba::Language;
    /// let language = Language::new_with_labels(&["a", "b", "c", "p", "q", "r", "s", "t"]);
    /// for (i,s) in language.iter().enumerate() {
    ///     println!("atom {} is {}", i, s.label());
    /// }
    /// ```
    pub fn iter(&self) -> impl Iterator<Item = &Atom<T>> {
        self.0.iter()
    }
}
