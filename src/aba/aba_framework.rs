use crate::aba::language::Atom;
use crate::aba::language::Language;
use crate::utils::LabelType;
use anyhow::{anyhow, Context, Result};
use std::fmt::Debug;

#[derive(Clone, Debug, PartialEq)]
enum AtomType {
    NotAssumption,
    Assumption { contrary_index: usize },
}

/// A rule in an ABA framework.
pub struct Rule<'a, T>
where
    T: LabelType,
{
    rule_ids: &'a (usize, Vec<usize>),
    language: &'a Language<T>,
}

impl<'a, T> Rule<'a, T>
where
    T: LabelType,
{
    /// Returns the head of the rule.
    pub fn head(&self) -> &Atom<T> {
        self.language.get_atom_by_id(self.rule_ids.0)
    }

    /// Returns the body of the rule.
    pub fn iter_body(&self) -> impl Iterator<Item = &Atom<T>> + '_ {
        self.rule_ids
            .1
            .iter()
            .map(|i| self.language.get_atom_by_id(*i))
    }

    pub(crate) fn head_id(&self) -> usize {
        self.rule_ids.0
    }

    pub(crate) fn body_ids(&self) -> &[usize] {
        &self.rule_ids.1
    }
}

/// Handles a flat ABA framework.
///
/// [ABAFramework] objects hold a language, including the assumptions and their contrary, and the rules built on top of this language.
/// Such kind of framework is initialized with its languages. Assumptions, contraries and rules are defined after with dedicated methods
/// ensuring the constraints on them (no assumption on rule heads, each assumption has a contrary, ...).
///
/// # Example
///
/// ```
/// # use crustabri::aba::ABAFramework;
/// # use crustabri::aba::Language;
/// let language = Language::new_with_labels(&["a", "b", "c", "p", "q", "r", "s", "t"]);
/// let rules = [
///    ("p", vec![&"q", &"a"]),
///    ("q", vec![]),
///    ("r", vec![&"b", &"c"]),
/// ];
/// let assumptions = [ // tuples give assumptions and their contraries
///     ("a", "r"),
///     ("b", "s"),
///     ("c", "t"),
/// ];
/// let mut aba_framework = ABAFramework::new_with_language(language);
/// for (head, tail) in &rules {
///     aba_framework.new_rule(&head, tail).unwrap();
/// }
/// for (assumption, contrary) in &assumptions {
///     aba_framework.new_assumption(assumption, contrary).unwrap();
/// }
/// ```
pub struct ABAFramework<T>
where
    T: LabelType,
{
    language: Language<T>,
    is_head_of_rule: Vec<bool>,
    atom_type: Vec<AtomType>,
    assumption_indices: Vec<usize>,
    rules: Vec<(usize, Vec<usize>)>,
}

impl<T> ABAFramework<T>
where
    T: LabelType,
{
    /// Builds a ABA framework given its associated language.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::aba::ABAFramework;
    /// # use crustabri::aba::Language;
    /// let language = Language::new_with_labels(&["a", "b", "c", "p", "q", "r", "s", "t"]);
    /// let aba_framework = ABAFramework::new_with_language(language);
    /// ```
    pub fn new_with_language(language: Language<T>) -> Self {
        let language_len = language.len();
        ABAFramework {
            language,
            is_head_of_rule: vec![false; language_len],
            atom_type: vec![AtomType::NotAssumption; language_len],
            assumption_indices: Vec::new(),
            rules: Vec::new(),
        }
    }

    /// Adds a rule to the framework.
    ///
    /// The atoms in the head and the tail are given by their labels.
    /// If an atom is not part of the language of the framework, an error is returned.
    ///
    /// Since ABA frameworks under consideration are flat, an error is also returned if the head of the rule has been set as an assumption.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::aba::ABAFramework;
    /// # use crustabri::aba::Language;
    /// let language = Language::new_with_labels(&["a", "b", "c", "p", "q", "r", "s", "t"]);
    /// let rules = [
    ///    ("p", vec![&"q", &"a"]),
    ///    ("q", vec![]),
    ///    ("r", vec![&"b", &"c"]),
    /// ];
    /// let mut aba_framework = ABAFramework::new_with_language(language);
    /// for (head, tail) in &rules {
    ///     aba_framework.new_rule(head, &tail).unwrap();
    /// }
    /// aba_framework.new_rule(&"x", &[&"y"]).unwrap_err();
    /// ```
    pub fn new_rule(&mut self, head: &T, body: &[&T]) -> Result<()> {
        let mut body_vec = Vec::with_capacity(body.len());
        let context = || {
            format!(
                "cannot add a rule with {:?} as head and {:?} as body",
                head, body
            )
        };
        for b in body {
            body_vec.push(self.language.get_atom(b).with_context(context)?.id());
        }
        let head_atom_index = self.language.get_atom(head).with_context(context)?.id();
        if matches!(self.atom_type[head_atom_index], AtomType::Assumption { .. }) {
            return Err(anyhow!(
                "cannot set an assumption ({:?}) as the head of a rule in a flat ABA framework",
                head
            ));
        }
        self.rules.push((head_atom_index, body_vec));
        self.is_head_of_rule[head_atom_index] = true;
        Ok(())
    }

    /// Returns the rule at the given index.
    ///
    /// # Panics
    ///
    /// This method panics if the provided index does not refer to an existing rule.
    pub(crate) fn get_rule_by_id(&self, index: usize) -> Rule<T> {
        Rule {
            rule_ids: &self.rules[index],
            language: &self.language,
        }
    }

    /// Sets a language atom as an assumption. Its contrary atom must be provided.
    ///
    /// The atom names must refer to existing atoms.
    /// The new assumption must not be already set as an assumption, or be set as the head of a rule.
    /// The contrary atom must be different from the assumption.
    /// If one of these conditions is not met, an error is returned.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::aba::ABAFramework;
    /// # use crustabri::aba::Language;
    /// let language = Language::new_with_labels(&["a", "b", "c", "p", "q", "r", "s", "t"]);
    /// let assumptions = [ // tuples give assumptions and their contraries
    ///     ("a", "r"),
    ///     ("b", "s"),
    ///     ("c", "t"),
    /// ];
    /// let mut aba_framework = ABAFramework::new_with_language(language);
    /// for (assumption, contrary) in &assumptions {
    ///     aba_framework.new_assumption(assumption, contrary).unwrap();
    /// }
    /// ```
    pub fn new_assumption(&mut self, assumption: &T, contrary: &T) -> Result<()> {
        let context = || {
            format!(
                "cannot set {:?} as an assumption with {:?} as contrary",
                assumption, contrary
            )
        };
        let assumption_index = self
            .language
            .get_atom(assumption)
            .with_context(context)?
            .id();
        if self.is_head_of_rule[assumption_index] {
            return Err(anyhow!(
                "cannot set an assumption ({:?}) which is already the head of a rule in a flat ABA framework",
                assumption
            ));
        }
        let contrary_index = self.language.get_atom(contrary).with_context(context)?.id();
        match self.atom_type[assumption_index] {
            AtomType::Assumption { .. } => {
                return Err(anyhow!(
                    "atom already registered as an assumption: {}",
                    assumption
                ))
            }
            _ => self.atom_type[assumption_index] = AtomType::Assumption { contrary_index },
        };
        self.assumption_indices.push(assumption_index);
        Ok(())
    }

    /// Returns the number of assumptions defined so far.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::utils::LabelType;
    /// # use crustabri::aba::ABAFramework;
    /// fn debug_assumptions<T: LabelType>(f: &ABAFramework<T>) {
    ///     assert_eq!(f.n_assumptions(), f.iter_assumptions().count())
    /// }
    /// ```
    pub fn n_assumptions(&self) -> usize {
        self.assumption_indices.len()
    }

    /// Returns `true` iff the provided atom (given by its label) corresponds to an assumption.
    ///
    /// An error is returned if the provided label does not refer to a valid language element.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::utils::LabelType;
    /// # use crustabri::aba::ABAFramework;
    /// fn debug_assumptions<T: LabelType>(f: &ABAFramework<T>) {
    ///     for a in f.iter_assumptions() {
    ///         assert!(f.is_assumption(a.label()).unwrap());
    ///     }
    /// }
    /// ```
    pub fn is_assumption(&self, s: &T) -> Result<bool> {
        let index = self
            .language
            .get_atom(s)
            .context("cannot check if the atom is an assumption")?
            .id();
        Ok(matches!(self.atom_type[index], AtomType::Assumption { .. }))
    }

    /// Return an iterator the the assumptions of the language.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::aba::ABAFramework;
    /// # use crustabri::utils::LabelType;
    /// fn debug_assumptions<T: LabelType>(f: &ABAFramework<T>) {
    ///     for a in f.iter_assumptions() {
    ///         println!(
    ///             "assumption {} admits {} as contrary",
    ///             a.label(),
    ///             f.get_contrary(a.label()).unwrap().label()
    ///         );
    ///     }
    /// }
    /// ```
    pub fn iter_assumptions(&self) -> impl Iterator<Item = &Atom<T>> + '_ {
        self.assumption_indices
            .iter()
            .map(move |i| self.language.get_atom_by_id(*i))
    }

    /// Returns the assumption ids.
    pub(crate) fn assumption_ids(&self) -> &[usize] {
        self.assumption_indices.as_slice()
    }

    /// Returns the contrary of an assumption given by its label.
    ///
    /// If the provided label does not refer to the contrary of an assumption, an error is returned.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::aba::ABAFramework;
    /// # use crustabri::utils::LabelType;
    /// fn debug_assumptions<T: LabelType>(f: &ABAFramework<T>) {
    ///     let mut n_assumptions = 0;
    ///     for a in f.iter_assumptions() {
    ///         n_assumptions += 1;
    ///         assert!(f.is_assumption(a.label()).unwrap());
    ///         println!(
    ///             "assumption {} admits {} as contrary",
    ///             a.label(),
    ///             f.get_contrary(a.label()).unwrap().label()
    ///         );
    ///     }
    ///     assert_eq!(n_assumptions, f.n_assumptions());
    /// }
    /// ```
    pub fn get_contrary(&self, s: &T) -> Result<&Atom<T>> {
        let index = self
            .language
            .get_atom(s)
            .context("cannot get the contrary of the assumption")?
            .id();
        match self.atom_type[index] {
            AtomType::NotAssumption => Err(anyhow!("atom {:?} is not an assumption", s)),
            AtomType::Assumption { contrary_index } => {
                Ok(self.language.get_atom_by_id(contrary_index))
            }
        }
    }

    /// Returns the index of contrary of an assumption given by its name if it exists, or `None`.
    ///
    /// The name must be a valid atom name.
    pub(crate) fn try_get_contrary_index_by_id(&self, id: usize) -> Option<usize> {
        match self.atom_type[id] {
            AtomType::NotAssumption => None,
            AtomType::Assumption { contrary_index } => Some(contrary_index),
        }
    }

    /// Returns the underlying language.
    pub fn language(&self) -> &Language<T> {
        &self.language
    }

    /// Returns the atom with the corresponding identifier.
    ///
    /// # Panics
    ///
    /// Panics if the provided identifier does not refer to an existing atom.
    pub(crate) fn get_atom_by_id(&self, id: usize) -> &Atom<T> {
        self.language.get_atom_by_id(id)
    }

    /// Returns the number of rules of the framework.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::aba::ABAFramework;
    /// # use crustabri::utils::LabelType;
    /// fn debug_rules<T: LabelType>(f: &ABAFramework<T>) {
    ///     assert_eq!(f.n_rules(), f.iter_rules().count());
    /// }
    /// ```
    pub fn n_rules(&self) -> usize {
        self.rules.len()
    }

    /// Provides an iterator to the rules.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::aba::{ABAFramework, Atom};
    /// # use crustabri::utils::LabelType;
    /// fn debug_rules<T: LabelType>(f: &ABAFramework<T>) {
    ///     for (i,r) in f.iter_rules().enumerate() {
    ///         println!(
    ///             "rule {}: head={}, body={:?}",
    ///             i,
    ///             r.head(),
    ///             r.iter_body().collect::<Vec<&Atom<T>>>(),
    ///         );
    ///     }
    /// }
    /// ```
    pub fn iter_rules(&self) -> impl Iterator<Item = Rule<T>> + '_ {
        (0..self.rules.len()).map(|i| self.get_rule_by_id(i))
    }

    /// Provides an iterator to the arguments, as defined in ABA frameworks.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::aba::ABAFramework;
    /// # use crustabri::utils::LabelType;
    /// fn debug_arguments<T: LabelType>(f: &ABAFramework<T>) {
    ///     for (i,a) in f.iter_arguments().enumerate() {
    ///         println!("arg {}: {:?}", i, a);
    ///     }
    /// }
    /// ```
    pub fn iter_arguments(&self) -> impl Iterator<Item = (Atom<T>, Vec<Atom<T>>)> + '_ {
        self.iter_rules()
            .filter_map(|r| {
                if r.body_ids().is_empty() {
                    return Some((r.head().clone(), Vec::new()));
                }
                let new_body: Vec<Atom<T>> = r
                    .iter_body()
                    .filter(|s| matches!(self.atom_type[s.id()], AtomType::Assumption { .. }))
                    .cloned()
                    .collect();
                if new_body.is_empty() {
                    None
                } else {
                    Some((r.head().clone(), new_body))
                }
            })
            .chain(
                self.iter_assumptions()
                    .map(|s| (s.clone(), vec![s.clone()])),
            )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_rule() {
        let r = (0, vec![1, 2]);
        assert_eq!(0, r.0);
        assert_eq!(vec![1, 2], r.1);
    }

    #[test]
    pub fn test_with_capacity() {
        let atoms = vec!["a", "b", "c"];
        let l = Language::new_with_labels(&atoms);
        let mut framework = ABAFramework::new_with_language(l);
        assert_eq!(0, framework.rules.len());
        framework.new_rule(&"a", &[&"b", &"c"]).unwrap();
        assert_eq!(1, framework.rules.len());
        let r = &framework.rules[0];
        assert_eq!(0, r.0);
        assert_eq!(vec![1, 2], r.1);
    }

    #[test]
    fn test_add_rule_wrong_name_1() {
        let atoms = vec!["a", "b", "c"];
        let l = Language::new_with_labels(&atoms);
        let mut framework = ABAFramework::new_with_language(l);
        framework.new_rule(&"d", &[&"b", &"c"]).unwrap_err();
    }

    #[test]
    fn test_add_rule_wrong_name_2() {
        let atoms = vec!["a", "b", "c"];
        let l = Language::new_with_labels(&atoms);
        let mut framework = ABAFramework::new_with_language(l);
        framework.new_rule(&"a", &[&"d", &"c"]).unwrap_err();
    }

    #[test]
    fn test_new_assumption_ok() {
        let atoms = vec!["a", "b", "c"];
        let l = Language::new_with_labels(&atoms);
        let mut f = ABAFramework::new_with_language(l);
        assert_eq!(0, f.n_assumptions());
        f.new_assumption(&"a", &"b").unwrap();
        assert_eq!(1, f.n_assumptions());
        assert_eq!(AtomType::Assumption { contrary_index: 1 }, f.atom_type[0]);
    }

    #[test]
    fn test_new_assumption_unknown_name_1() {
        let atoms = vec!["a", "b", "c"];
        let l = Language::new_with_labels(&atoms);
        let mut f = ABAFramework::new_with_language(l);
        f.new_assumption(&"d", &"a").unwrap_err();
    }

    #[test]
    fn test_new_assumption_unknown_name_2() {
        let atoms = vec!["a", "b", "c"];
        let l = Language::new_with_labels(&atoms);
        let mut f = ABAFramework::new_with_language(l);
        f.new_assumption(&"a", &"d").unwrap_err();
    }

    #[test]
    fn test_new_assumption_already_registered() {
        let atoms = vec!["a", "b", "c"];
        let l = Language::new_with_labels(&atoms);
        let mut f = ABAFramework::new_with_language(l);
        f.new_assumption(&"a", &"b").unwrap();
        f.new_assumption(&"a", &"b").unwrap_err();
    }

    #[test]
    fn test_is_assumption() {
        let atoms = vec!["a", "b", "c"];
        let l = Language::new_with_labels(&atoms);
        let mut f = ABAFramework::new_with_language(l);
        f.new_assumption(&"a", &"b").unwrap();
        assert!(f.is_assumption(&"a").unwrap());
        assert!(!f.is_assumption(&"b").unwrap());
    }

    #[test]
    fn test_is_assumption_unknown_name() {
        let atoms = vec!["a", "b", "c"];
        let l = Language::new_with_labels(&atoms);
        let mut f = ABAFramework::new_with_language(l);
        f.new_assumption(&"a", &"b").unwrap();
        f.is_assumption(&"d").unwrap_err();
    }

    #[test]
    fn test_get_contrary() {
        let atoms = vec!["a", "b", "c"];
        let l = Language::new_with_labels(&atoms);
        let mut f = ABAFramework::new_with_language(l);
        f.new_assumption(&"a", &"b").unwrap();
        assert_eq!(&"b", f.get_contrary(&"a").unwrap().label());
    }

    #[test]
    fn test_get_contrary_unknown_name() {
        let atoms = vec!["a", "b", "c"];
        let l = Language::new_with_labels(&atoms);
        let mut f = ABAFramework::new_with_language(l);
        f.new_assumption(&"a", &"b").unwrap();
        f.get_contrary(&"d").unwrap_err();
    }

    #[test]
    fn test_get_contrary_not_an_assumption() {
        let atoms = vec!["a", "b", "c"];
        let l = Language::new_with_labels(&atoms);
        let mut f = ABAFramework::new_with_language(l);
        f.new_assumption(&"a", &"b").unwrap();
        f.get_contrary(&"b").unwrap_err();
    }

    #[test]
    fn test_add_head_as_assumption() {
        let atoms = vec!["a", "b", "c"];
        let l = Language::new_with_labels(&atoms);
        let mut framework = ABAFramework::new_with_language(l);
        framework.new_rule(&"a", &[&"b", &"c"]).unwrap();
        framework.new_assumption(&"a", &"b").unwrap_err();
    }

    #[test]
    fn test_new_assumption_as_head() {
        let atoms = vec!["a", "b", "c"];
        let l = Language::new_with_labels(&atoms);
        let mut framework = ABAFramework::new_with_language(l);
        framework.new_assumption(&"a", &"b").unwrap();
        framework.new_rule(&"a", &[&"b", &"c"]).unwrap_err();
    }

    fn check_rule(
        rule: &Rule<&'static str>,
        expected_head: &'static str,
        expected_body: &[&'static str],
    ) -> bool {
        if rule.head().label() != &expected_head {
            return false;
        }
        if rule.body_ids().len() != expected_body.len() {
            return false;
        }
        rule.iter_body()
            .enumerate()
            .all(|(i, a)| a.label() == &expected_body[i])
    }

    fn toni_tutorial_ex() -> ABAFramework<&'static str> {
        let l = Language::new_with_labels(&["a", "b", "c", "p", "q", "r", "s", "t"]);
        let mut framework = ABAFramework::new_with_language(l);
        framework.new_assumption(&"a", &"r").unwrap();
        framework.new_assumption(&"b", &"s").unwrap();
        framework.new_assumption(&"c", &"t").unwrap();
        framework.new_rule(&"p", &[&"q", &"a"]).unwrap();
        framework.new_rule(&"q", &[] as &[&&str]).unwrap();
        framework.new_rule(&"r", &[&"b", &"c"]).unwrap();
        framework
    }

    #[test]
    fn test_iter_rules() {
        let framework = toni_tutorial_ex();
        let rules: Vec<Rule<&str>> = framework.iter_rules().collect();
        assert_eq!(3, rules.len());
        assert!(check_rule(&rules[0], "p", &["q", "a"]));
        assert!(check_rule(&rules[1], "q", &[] as &[&str]));
        assert!(check_rule(&rules[2], "r", &["b", "c"]));
    }

    #[test]
    pub fn test_rule_debug() {
        let atoms = vec!["a", "b", "c"];
        let l = Language::new_with_labels(&atoms);
        let mut framework = ABAFramework::new_with_language(l);
        framework.new_rule(&"a", &[&"b"]).unwrap();
        framework.new_rule(&"a", &[&"c"]).unwrap();
        assert_eq!(
            format!("{:?}", framework.rules[0]),
            format!("{:?}", framework.rules[0])
        );
        assert_ne!(
            format!("{:?}", framework.rules[0]),
            format!("{:?}", framework.rules[1])
        );
    }
}
