use crate::{
    aa::{Argument, ArgumentSet},
    utils::{Label, LabelType},
};
use anyhow::{anyhow, Context, Result};

/// A Flat Assumption-Based Argumentation framework as defined by Bondarenko et al.
pub struct FlatABAFramework<T>
where
    T: LabelType,
{
    arguments: ArgumentSet<T>,
    assumptions_map: Vec<Option<Option<usize>>>,
    assumptions_vec: Vec<usize>,
    contraries_map: Vec<Vec<usize>>,
    contraries_vec: Vec<usize>,
    rules: Vec<Vec<Vec<usize>>>,
    n_rules: usize,
}

impl<T> FlatABAFramework<T>
where
    T: LabelType,
{
    /// Builds a Flat ABA framework with its initial argument set.
    pub fn new_with_argument_set(arguments: ArgumentSet<T>) -> Self {
        let n_arguments = arguments.len();
        Self {
            arguments,
            assumptions_map: vec![None; n_arguments],
            assumptions_vec: vec![],
            contraries_map: vec![vec![]; n_arguments],
            contraries_vec: vec![],
            rules: vec![vec![]; n_arguments],
            n_rules: 0,
        }
    }

    /// Returns the number of assumptions in this framework.
    pub fn n_assumptions(&self) -> usize {
        self.assumptions_vec.len()
    }

    /// Returns the number of contraries in this framework.
    pub fn n_contraries(&self) -> usize {
        self.contraries_vec.len()
    }

    /// Returns the number of rules in this framework.
    pub fn n_rules(&self) -> usize {
        self.n_rules
    }

    /// Declares an existing argument as an assumption given its label.
    ///
    /// # Errors
    ///
    /// An error is returned if the argument does not exists or if it was already set as an assumption or a contrary.
    pub fn set_as_assumption(&mut self, atom: &T) -> Result<()> {
        let id = self.label_to_argument(atom)?.id();
        self.set_as_assumption_by_id(id)
    }

    /// Declares an existing argument as an assumption given its id.
    ///
    /// # Errors
    ///
    /// An error is returned if the argument does not exists or if it was already set as an assumption or a contrary.
    pub fn set_as_assumption_by_id(&mut self, id: usize) -> Result<()> {
        if self.assumptions_map[id].is_some() || !self.contraries_map[id].is_empty() {
            Err(anyhow!("cannot set as assumption an atom ({}) which is already set as assumption or contrary", self.arguments.get_argument_by_id(id).label()))
        } else {
            self.assumptions_map[id] = Some(None);
            self.assumptions_vec.push(id);
            Ok(())
        }
    }

    /// Declares an existing argument as a contrary given its label and the one of its related assumption.
    ///
    /// # Errors
    ///
    /// An error is returned if the argument does not exists or if it was already set as an assumption or a contrary.
    /// An error is also returned if a contrary has already been set for the assumption.
    pub fn set_as_contrary(&mut self, contrary: &T, assumption: &T) -> Result<()> {
        let contrary_id = self.label_to_argument(contrary)?.id();
        let assumption_id = self.label_to_argument(assumption)?.id();
        self.set_as_contrary_by_ids(contrary_id, assumption_id)
    }

    /// Declares an existing argument as a contrary given its id and the one of its related assumption.
    ///
    /// # Errors
    ///
    /// An error is returned if the argument does not exists or if it was already set as an assumption or a contrary.
    /// An error is also returned if a contrary has already been set for the assumption.
    pub fn set_as_contrary_by_ids(&mut self, contrary: usize, assumption: usize) -> Result<()> {
        match self.assumptions_map[assumption] {
            None => Err(anyhow!(
                r#"atom "{}" is not an assumption"#,
                self.argument_set().get_argument_by_id(assumption).id()
            )),
            Some(Some(_)) => Err(anyhow!(
                r#"assumption "{}" has already a contrary"#,
                self.argument_set().get_argument_by_id(assumption).id()
            )),
            Some(None) => {
                self.assumptions_map[assumption] = Some(Some(contrary));
                let contrary_map_vec = &mut self.contraries_map[contrary];
                if contrary_map_vec.is_empty() {
                    self.contraries_vec.push(contrary);
                }
                contrary_map_vec.push(assumption);
                Ok(())
            }
        }
    }

    /// Adds a new rule given its head and its tail; the arguments are given by their labels.
    ///
    /// # Errors
    ///
    /// An error is returned if one of the arguments does not exists or the head is an assumption.
    pub fn add_rule(&mut self, head: &T, tail: Vec<&T>) -> Result<()> {
        let head_id = self.label_to_argument(head)?.id();
        let tail_id_vec = tail
            .iter()
            .map(|l| self.label_to_argument(l).map(|a| a.id()))
            .collect::<Result<Vec<_>>>()?;
        self.add_rule_by_ids(head_id, tail_id_vec)
    }

    /// Adds a new rule given its head and its tail; the arguments are given by their ids.
    ///
    /// # Errors
    ///
    /// An error is returned if one of the arguments does not exists or the head is an assumption.
    pub fn add_rule_by_ids(&mut self, head_id: usize, tail_id_vec: Vec<usize>) -> Result<()> {
        if self.assumptions_map[head_id].is_some() {
            return Err(anyhow!(
                "the head of a rule (here {}) cannot be an assumption",
                self.arguments.get_argument_by_id(head_id).label()
            ));
        }
        self.rules[head_id].push(tail_id_vec);
        self.n_rules += 1;
        Ok(())
    }

    pub(crate) fn swap_remove_rule_by_id_and_index(&mut self, head_id: usize, tail_index: usize) {
        self.rules[head_id].swap_remove(tail_index);
        self.n_rules -= 1;
    }

    pub(crate) fn remove_rules_with_head_id(&mut self, head_id: usize) {
        self.n_rules -= self.rules[head_id].len();
        self.rules[head_id].clear();
    }

    fn label_to_argument(&self, label: &T) -> Result<&Argument<T>> {
        self.arguments
            .get_argument(label)
            .with_context(|| format!("while retrieving argument {label} from its label"))
    }

    /// Returns the underlying argument set.
    pub fn argument_set(&self) -> &ArgumentSet<T> {
        &self.arguments
    }

    /// Iterates over the assumption labels.
    pub fn iter_assumptions(&self) -> impl Iterator<Item = &Label<T>> + '_ {
        self.assumptions_vec
            .iter()
            .map(|id| self.argument_set().get_argument_by_id(*id))
    }

    /// Returns a slice containing the ids of the assumption.
    pub fn assumption_ids(&self) -> &[usize] {
        &self.assumptions_vec
    }

    /// Returns true if and only if the provided atom (given by its id) is an assumption.
    pub fn is_assumption_id(&self, id: usize) -> bool {
        self.assumptions_map[id].is_some()
    }

    /// Iterates over the contraries, yielding couples (contrary, base_assumptions).
    pub fn iter_contraries(
        &self,
    ) -> impl Iterator<Item = (&Label<T>, impl Iterator<Item = &Label<T>> + '_)> + '_ {
        self.contraries_vec.iter().map(|id| {
            (
                self.argument_set().get_argument_by_id(*id),
                self.contraries_map[*id]
                    .iter()
                    .map(|i| self.argument_set().get_argument_by_id(*i)),
            )
        })
    }

    /// Iterates over the contraries, yielding couples (contrary id, base_assumption ids).
    pub fn iter_contraries_by_ids(&self) -> impl Iterator<Item = (usize, &[usize])> + '_ {
        self.contraries_vec
            .iter()
            .map(|id| (*id, self.contraries_map[*id].as_slice()))
    }

    /// Given an id, returns the contrary of it if it refers to an assumption which contrary is declared
    pub fn contrary_of_id(&self, id: usize) -> Option<usize> {
        self.assumptions_map[id].and_then(|c| c)
    }

    /// Returns the assumptions of which the atom with the provided id is the contrary.
    pub fn is_contrary_of_id(&self, contrary: usize) -> &[usize] {
        self.contraries_map[contrary].as_slice()
    }

    /// Iterates over the atoms, returning couples (head, tails).
    /// If an atom does not belong to any rule head, then (atom, vec![]) is yielded.
    ///
    /// The item type is a couple composed of a head and the set of tails which have this head.
    /// Arguments are given by labels.
    pub fn iter_rules(&self) -> impl Iterator<Item = (&Label<T>, Vec<Vec<&Label<T>>>)> + '_ {
        self.rules.iter().enumerate().map(|(head, tails)| {
            (
                self.argument_set().get_argument_by_id(head),
                tails
                    .iter()
                    .map(|t| {
                        t.iter()
                            .map(|id| self.argument_set().get_argument_by_id(*id))
                            .collect()
                    })
                    .collect(),
            )
        })
    }

    /// Iterates over the atoms, returning couples (head, tails).
    /// If an atom does not belong to any rule head, then (atom, vec![]) is yielded.
    ///
    /// The item type is a couple composed of a head and the set of tails which have this head.
    /// Arguments are given by ids.
    pub fn iter_rules_by_ids(&self) -> impl Iterator<Item = (usize, &Vec<Vec<usize>>)> + '_ {
        self.rules.iter().enumerate()
    }

    /// Returns tail of rules which has the given head id.
    pub fn rule_tails_of_head_ids(&self, head_id: usize) -> &[Vec<usize>] {
        &self.rules[head_id]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_metrics() {
        let labels: Vec<usize> = (1..=5).collect();
        let mut af = FlatABAFramework::new_with_argument_set(ArgumentSet::new_with_labels(&labels));
        assert_eq!(5, af.argument_set().len());
        assert_eq!(0, af.n_assumptions());
        assert_eq!(0, af.n_contraries());
        assert_eq!(0, af.n_rules());
        af.set_as_assumption(&1).unwrap();
        af.set_as_assumption(&2).unwrap();
        af.set_as_assumption(&3).unwrap();
        af.set_as_contrary(&4, &1).unwrap();
        af.set_as_contrary(&5, &2).unwrap();
        af.add_rule(&4, vec![&2, &3]).unwrap();
        assert_eq!(5, af.argument_set().len());
        assert_eq!(3, af.n_assumptions());
        assert_eq!(2, af.n_contraries());
        assert_eq!(1, af.n_rules());
        assert_eq!(
            (1..=3)
                .map(|i| af.argument_set().get_argument(&i).unwrap().id())
                .collect::<Vec<_>>(),
            af.assumption_ids()
        );
        for i in 1..=5 {
            let id = af.argument_set().get_argument(&i).unwrap().id();
            assert_eq!(af.assumption_ids().contains(&id), af.is_assumption_id(id),)
        }
    }

    #[test]
    fn test_add_as_assumption() {
        let labels: Vec<usize> = (1..=5).collect();
        let mut af = FlatABAFramework::new_with_argument_set(ArgumentSet::new_with_labels(&labels));
        assert_eq!(0, af.n_assumptions());
        af.set_as_assumption(&1).unwrap();
        assert_eq!(1, af.n_assumptions());
        assert!(af.set_as_assumption(&1).is_err());
        assert_eq!(1, af.n_assumptions());
    }

    #[test]
    fn test_add_as_contrary() {
        let labels: Vec<usize> = (1..=5).collect();
        let mut af = FlatABAFramework::new_with_argument_set(ArgumentSet::new_with_labels(&labels));
        af.set_as_assumption(&1).unwrap();
        let id1 = af.argument_set().get_argument(&1).unwrap().id();
        let id4 = af.argument_set().get_argument(&4).unwrap().id();
        assert!(af.is_contrary_of_id(id4).is_empty());
        assert!(af.contrary_of_id(id1).is_none());
        assert_eq!(0, af.n_contraries());
        af.set_as_contrary(&4, &1).unwrap();
        assert_eq!(&[id1], af.is_contrary_of_id(id4));
        assert_eq!(Some(id4), af.contrary_of_id(id1));
        assert_eq!(1, af.n_contraries());
        assert_eq!(Some(id4), af.contrary_of_id(id1));
        assert!(af.set_as_contrary(&4, &2).is_err());
        assert!(af.set_as_contrary(&5, &1).is_err());
        assert_eq!(1, af.n_contraries());
        assert_eq!(
            vec![(
                af.argument_set().get_argument_by_id(id4),
                vec![af.argument_set().get_argument_by_id(id1)],
            )],
            af.iter_contraries()
                .map(|(c, a)| (c, a.collect::<Vec<_>>()))
                .collect::<Vec<_>>(),
        );
        assert_eq!(
            vec![(id4, &[id1] as &[usize])],
            af.iter_contraries_by_ids().collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_add_rules() {
        let labels: Vec<usize> = (1..=3).collect();
        let mut af = FlatABAFramework::new_with_argument_set(ArgumentSet::new_with_labels(&labels));
        af.set_as_assumption(&1).unwrap();
        assert_eq!(0, af.n_rules());
        assert!(af.add_rule(&1, vec![]).is_err());
        assert_eq!(0, af.n_rules());
        af.add_rule(&2, vec![]).unwrap();
        af.add_rule(&2, vec![&1]).unwrap();
        assert_eq!(2, af.n_rules());
        assert_eq!(
            vec![
                (af.argument_set().get_argument(&1).unwrap(), vec![]),
                (
                    af.argument_set().get_argument(&2).unwrap(),
                    vec![vec![], vec![af.argument_set().get_argument(&1).unwrap()]]
                ),
                (af.argument_set().get_argument(&3).unwrap(), vec![]),
            ],
            af.iter_rules().collect::<Vec<_>>(),
        );
        assert_eq!(
            vec![
                (af.argument_set().get_argument(&1).unwrap().id(), &vec![]),
                (
                    af.argument_set().get_argument(&2).unwrap().id(),
                    &vec![
                        vec![],
                        vec![af.argument_set().get_argument(&1).unwrap().id()]
                    ]
                ),
                (af.argument_set().get_argument(&3).unwrap().id(), &vec![]),
            ],
            af.iter_rules_by_ids().collect::<Vec<_>>(),
        );
    }

    #[test]
    fn test_assumption_as_contrary() {
        let labels: Vec<usize> = (1..=3).collect();
        let mut af = FlatABAFramework::new_with_argument_set(ArgumentSet::new_with_labels(&labels));
        af.set_as_assumption(&1).unwrap();
        af.set_as_assumption(&2).unwrap();
        af.set_as_contrary(&2, &1).unwrap();
    }

    #[test]
    fn test_contrary_of_multiple_assumptions() {
        let labels: Vec<usize> = (1..=3).collect();
        let mut af = FlatABAFramework::new_with_argument_set(ArgumentSet::new_with_labels(&labels));
        af.set_as_assumption(&1).unwrap();
        af.set_as_assumption(&2).unwrap();
        af.set_as_contrary(&3, &1).unwrap();
        af.set_as_contrary(&3, &2).unwrap();
        let contrary_ids = af.iter_contraries_by_ids().collect::<Vec<_>>();
        assert_eq!(1, contrary_ids.len());
        assert_eq!(2, contrary_ids[0].1.len());
    }
}
