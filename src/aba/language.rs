use crate::aa::LabelType;
use anyhow::{anyhow, Result};
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::fmt::Debug;

/// Handles an atom of the language.
///
/// Each atom has a label and an identifier which are unique in a language.
/// This uniqueness condition imposes atoms are made from [Language] objects, and not directly by the [Atom] struct.
///
/// The type of the labels must be [`LabelType`] instances.
/// The type associated with an atom is the one associated with its language.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Atom<T>
where
    T: LabelType,
{
    id: usize,
    label: T,
}

impl<T> Atom<T>
where
    T: LabelType,
{
    /// Returns the id of the atom.
    pub fn label(&self) -> &T {
        &self.label
    }

    /// Returns the label of the atom.
    pub fn id(&self) -> usize {
        self.id
    }
}

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
#[derive(Debug, Clone)]
pub struct Language<T>
where
    T: LabelType,
{
    atoms: Vec<Atom<T>>,
    label_to_id: HashMap<T, usize>,
}

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
    pub fn new_with_labels(atoms: &[T]) -> Self {
        let mut name_to_id = HashMap::new();
        let mut language = Vec::with_capacity(atoms.len());
        for s in atoms.iter() {
            match name_to_id.entry(s.clone()) {
                Entry::Occupied(_) => continue,
                Entry::Vacant(e) => {
                    e.insert(language.len());
                }
            }
            language.push(Atom {
                id: language.len(),
                label: s.clone(),
            });
        }
        Language {
            atoms: language,
            label_to_id: name_to_id,
        }
    }

    /// Returns the number of atoms in the language.
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.atoms.len()
    }

    /// Returns `true` iff the language has no atom .
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.atoms.is_empty()
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
        self.label_to_id
            .get(label)
            .map(|i| &self.atoms[*i])
            .ok_or_else(|| anyhow!("no such atom: {}", label))
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
        &self.atoms[id]
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
        self.atoms.iter()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new() {
        let atoms = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        let l = Language::new_with_labels(&atoms);
        assert_eq!(3, l.atoms.len());
        assert_eq!(3, l.label_to_id.len());
        assert_eq!(3, l.len());
        assert!(!l.is_empty());
        for (i, s) in l.atoms.iter().enumerate() {
            assert_eq!(i, s.id);
            assert_eq!(atoms[i], s.label);
        }
    }

    #[test]
    fn test_new_empty() {
        let l = Language::new_with_labels(&[] as &[String]);
        assert_eq!(0, l.len());
        assert!(l.is_empty());
    }

    #[test]
    fn test_atom_debug() {
        let atoms = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        let l = Language::new_with_labels(&atoms);
        assert_eq!(format!("{:?}", l.atoms[0]), format!("{:?}", l.atoms[0]));
        assert_ne!(format!("{:?}", l.atoms[0]), format!("{:?}", l.atoms[1]));
    }

    #[test]
    fn test_language_debug() {
        let atoms1 = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        let l1 = Language::new_with_labels(&atoms1);
        let atoms2 = vec!["a".to_string(), "b".to_string(), "d".to_string()];
        let l2 = Language::new_with_labels(&atoms2);
        assert_eq!(format!("{:?}", l1), format!("{:?}", l1));
        assert_ne!(format!("{:?}", l1), format!("{:?}", l2));
    }

    #[test]
    fn test_duplicate_atom() {
        let atoms = vec!["a".to_string(), "a".to_string()];
        assert_eq!(1, Language::new_with_labels(&atoms).len());
    }
}
