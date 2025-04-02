use crate::{
    aa::{Argument, ArgumentSet},
    utils::{Label, LabelType},
};
use anyhow::{anyhow, Context, Result};

#[derive(Clone, Copy, PartialEq, Eq)]
enum AtomType {
    Assumption(Option<usize>),
    Contrary(usize),
    Default,
}

impl AtomType {
    fn unwrap_contrary_assumption(&self) -> usize {
        if let Self::Contrary(a) = self {
            *a
        } else {
            panic!()
        }
    }
}

/// A Flat Assumption-Based Argumentation framework as defined by Bondarenko et al.
pub struct FlatABAFramework<T>
where
    T: LabelType,
{
    arguments: ArgumentSet<T>,
    atom_types: Vec<AtomType>,
    assumptions: Vec<usize>,
    contraries: Vec<usize>,
    rules: Vec<Vec<Vec<usize>>>,
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
            atom_types: vec![AtomType::Default; n_arguments],
            assumptions: vec![],
            contraries: vec![],
            rules: vec![vec![]; n_arguments],
        }
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
        self.assumptions.push(id);
        self.set_as_by_id(id, AtomType::Assumption(None))
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
        self.contraries.push(contrary);
        if self.atom_types[assumption] != AtomType::Assumption(None) {
            return Err(anyhow!(
                r#"assumption "{}" has already a contrary"#,
                self.argument_set().get_argument_by_id(assumption).id()
            ));
        }
        self.atom_types[assumption] = AtomType::Assumption(Some(contrary));
        self.set_as_by_id(contrary, AtomType::Contrary(assumption))
    }

    fn set_as_by_id(&mut self, id: usize, atom_type: AtomType) -> Result<()> {
        if self.atom_types[id] != AtomType::Default {
            Err(anyhow!("cannot set as assumption or contrary an atom ({}) which is already set as assumption or contrary", self.arguments.get_argument_by_id(id).label()))
        } else {
            self.atom_types[id] = atom_type;
            Ok(())
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
        if matches!(self.atom_types[head_id], AtomType::Assumption(_)) {
            return Err(anyhow!(
                "the head of a rule (here {}) cannot be an assumption",
                self.arguments.get_argument_by_id(head_id).label()
            ));
        }
        self.rules[head_id].push(tail_id_vec);
        Ok(())
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
        self.assumptions
            .iter()
            .map(|id| self.argument_set().get_argument_by_id(*id))
    }

    /// Returns a slice containing the ids of the assumption.
    pub fn assumption_ids(&self) -> &[usize] {
        &self.assumptions
    }

    /// Returns true if and only if the provided atom (given by its id) is an assumption.
    pub fn is_assumption_id(&self, id: usize) -> bool {
        matches!(self.atom_types[id], AtomType::Assumption(_))
    }

    /// Iterates over the contraries, yielding couples (contrary, base_assumption).
    pub fn iter_contraries(&self) -> impl Iterator<Item = (&Label<T>, &Label<T>)> + '_ {
        self.contraries.iter().map(|id| {
            (
                self.argument_set().get_argument_by_id(*id),
                self.argument_set()
                    .get_argument_by_id(self.atom_types[*id].unwrap_contrary_assumption()),
            )
        })
    }

    /// Iterates over the contraries, yielding couples (contrary id, base_assumption id).
    pub fn iter_contraries_by_ids(&self) -> impl Iterator<Item = (usize, usize)> + '_ {
        self.contraries
            .iter()
            .map(|id| (*id, self.atom_types[*id].unwrap_contrary_assumption()))
    }

    /// Given an id, returns the contrary of it if it refers to an assumption which id is declared
    pub fn contrary_of_id(&self, id: usize) -> Option<usize> {
        if let AtomType::Assumption(Some(c)) = self.atom_types[id] {
            Some(c)
        } else {
            None
        }
    }

    /// Check if an atom given by its id is the contrary of an assumption.
    /// The assumption is returned if it is the case.
    pub fn is_contrary_of_id(&self, contrary: usize) -> Option<usize> {
        if let AtomType::Contrary(a) = self.atom_types[contrary] {
            Some(a)
        } else {
            None
        }
    }

    /// Iterates over the rules.
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

    /// Iterates over the rules.
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
