use super::FlatABAFramework;
use crate::{
    aa::ArgumentSet,
    utils::{Label, LabelType},
};

pub type NewLabelFn<T> = dyn Fn(&Label<T>, usize) -> T;

/// A structure used to break cycles in a Flat ABA by applying the algorithm described in:
///
/// Tuomo Lehtonen, Anna Rapberger, Markus Ulbricht, Johannes Peter Wallner:
/// Argumentation Frameworks Induced by Assumption-based Argumentation: Relating Size and Complexity. KR 2023: 440-450
pub struct FlatABACycleBreaker<T>
where
    T: LabelType,
{
    new_label_fn: Box<NewLabelFn<T>>,
}

impl FlatABACycleBreaker<usize> {
    /// Creates a new breaker for usize-labelled frameworks.
    pub fn new_for_usize() -> Self {
        FlatABACycleBreaker::new_with_new_label_fn(Box::new(|_init_arg, new_id| 1 + new_id))
    }
}

impl<T> FlatABACycleBreaker<T>
where
    T: LabelType,
{
    /// Creates a new breaker for frameworks given a function used to create new labels.
    ///
    /// Given a label of the initial framework and the id of the new label, this function must output a unique label.
    pub fn new_with_new_label_fn(new_label_fn: Box<NewLabelFn<T>>) -> Self {
        Self { new_label_fn }
    }

    /// Translates an input framework into a new one without cycles.
    pub fn remove_cycles(&self, init_af: &FlatABAFramework<T>) -> FlatABAFramework<T> {
        let translation_table = IdTranslationTable::new(init_af);
        let init_arg_set = init_af.argument_set();
        let mut labels = Vec::with_capacity(translation_table.n_total_atoms());
        for init_arg in init_arg_set.iter() {
            labels.push(init_arg.label().clone());
        }
        for _depth in 1..translation_table.depth() {
            for i in 0..init_arg_set.len() {
                if !init_af.is_assumption_id(i) {
                    labels.push((self.new_label_fn)(
                        init_arg_set.get_argument_by_id(i),
                        labels.len(),
                    ));
                }
            }
        }
        let mut new_af =
            FlatABAFramework::new_with_argument_set(ArgumentSet::new_with_labels(&labels));
        for assumption in init_af.assumption_ids() {
            new_af.set_as_assumption_by_id(*assumption).unwrap();
        }
        for (contrary, assumptions) in init_af.iter_contraries_by_ids() {
            for assumption in assumptions {
                new_af
                    .set_as_contrary_by_ids(contrary, *assumption)
                    .unwrap();
            }
        }
        for (head, tails) in init_af.iter_rules_by_ids() {
            for tail in tails {
                if tail.iter().all(|id| init_af.is_assumption_id(*id)) {
                    for depth in 0..translation_table.depth() {
                        new_af
                            .add_rule_by_ids(translation_table.atom_id(head, depth), tail.clone())
                            .unwrap();
                    }
                } else {
                    for depth in 0..(translation_table.depth() - 1) {
                        new_af
                            .add_rule_by_ids(
                                translation_table.atom_id(head, depth),
                                tail.iter()
                                    .map(|i| translation_table.atom_id(*i, depth + 1))
                                    .collect(),
                            )
                            .unwrap();
                    }
                }
            }
        }
        new_af
    }
}

struct IdTranslationTable {
    init_n_atoms: usize,
    n_assumptions: usize,
    non_assumption_atom_index: Vec<Option<usize>>,
    depth: usize,
}

impl IdTranslationTable {
    fn new<T>(init_af: &FlatABAFramework<T>) -> Self
    where
        T: LabelType,
    {
        let init_n_atoms = init_af.argument_set().len();
        let depth = init_n_atoms - init_af.assumption_ids().len();
        let mut non_assumption_atom_index = vec![None; init_n_atoms];
        let mut next = 0;
        #[allow(clippy::needless_range_loop)]
        for i in 0..init_n_atoms {
            if !init_af.is_assumption_id(i) {
                non_assumption_atom_index[i] = Some(next);
                next += 1;
            }
        }
        Self {
            init_n_atoms,
            n_assumptions: init_af.n_assumptions(),
            non_assumption_atom_index,
            depth,
        }
    }

    fn n_total_atoms(&self) -> usize {
        self.init_n_atoms + (self.depth - 1) * (self.init_n_atoms - self.n_assumptions)
    }

    fn depth(&self) -> usize {
        self.depth
    }

    fn atom_id(&self, init_id: usize, depth: usize) -> usize {
        if depth == 0 {
            init_id
        } else if let Some(i) = self.non_assumption_atom_index[init_id] {
            self.init_n_atoms + (depth - 1) * (self.init_n_atoms - self.n_assumptions) + i
        } else {
            init_id
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ok() {
        let labels: Vec<usize> = (1..=3).collect();
        let mut af = FlatABAFramework::new_with_argument_set(ArgumentSet::new_with_labels(&labels));
        af.set_as_assumption(&1).unwrap();
        af.add_rule(&2, vec![&1]).unwrap();
        af.add_rule(&2, vec![&3]).unwrap();
        af.add_rule(&3, vec![&2]).unwrap();
        let cycle_breaker = FlatABACycleBreaker::new_for_usize();
        let new_af = cycle_breaker.remove_cycles(&af);
        assert_eq!(5, new_af.argument_set().len());
        assert_eq!(1, new_af.n_assumptions());
        assert_eq!(4, new_af.n_rules());
        let mut new_rules = new_af
            .iter_rules_by_ids()
            .flat_map(|(head, tails)| tails.iter().map(move |tail| (head, tail.to_vec())))
            .collect::<Vec<_>>();
        new_rules.sort_unstable();
        assert_eq!(
            vec![(1, vec![0]), (1, vec![4]), (2, vec![3]), (3, vec![0])],
            new_rules
        );
    }
}
