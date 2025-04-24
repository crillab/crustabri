use super::FlatABAFramework;
use crate::utils::LabelType;

impl<T> FlatABAFramework<T>
where
    T: LabelType,
{
    /// Removes the rules that cannot be derived.
    pub fn reduce_not_derivable(&mut self) {
        let n_arguments = self.argument_set().len();
        let mut tail_atom_to_rule = vec![vec![]; n_arguments];
        let mut atom_queue = vec![];
        let mut atom_is_derivable = vec![false; n_arguments];
        for (head, tails) in self.iter_rules_by_ids() {
            if self.is_assumption_id(head) {
                atom_queue.push(head);
                atom_is_derivable[head] = true;
                continue;
            }
            for (tail_index, tail) in tails.iter().enumerate() {
                if tail.is_empty() {
                    atom_queue.push(head);
                    atom_is_derivable[head] = true;
                }
                for t in tail {
                    tail_atom_to_rule[*t].push((head, tail_index));
                }
            }
        }
        while let Some(atom) = atom_queue.pop() {
            for (head, tail_index) in &tail_atom_to_rule[atom] {
                if atom_is_derivable[*head] {
                    continue;
                }
                if self.rule_tails_of_head_ids(*head)[*tail_index]
                    .iter()
                    .all(|t| atom_is_derivable[*t])
                {
                    atom_queue.push(*head);
                    atom_is_derivable[*head] = true;
                }
            }
        }
        self.remove_rules_with_underivable_atom(&atom_is_derivable);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::aa::ArgumentSet;

    #[test]
    fn test_reduce_1() {
        let labels: Vec<usize> = (1..=2).collect();
        let mut af = FlatABAFramework::new_with_argument_set(ArgumentSet::new_with_labels(&labels));
        af.add_rule(&2, vec![&1]).unwrap();
        assert_eq!(1, af.n_rules());
        af.reduce_not_derivable();
        assert_eq!(0, af.n_rules());
    }

    #[test]
    fn test_reduce_2() {
        let labels: Vec<usize> = (1..=4).collect();
        let mut af = FlatABAFramework::new_with_argument_set(ArgumentSet::new_with_labels(&labels));
        af.set_as_assumption(&1).unwrap();
        af.set_as_contrary(&4, &1).unwrap();
        af.add_rule(&2, vec![&4, &3]).unwrap();
        af.add_rule(&3, vec![&2]).unwrap();
        af.add_rule(&4, vec![&1, &3]).unwrap();
        af.add_rule(&4, vec![&2]).unwrap();
        assert_eq!(4, af.n_rules());
        af.reduce_not_derivable();
        assert_eq!(0, af.n_rules());
    }

    #[test]
    fn test_reduce_3() {
        let labels: Vec<usize> = (1..=4).collect();
        let mut af = FlatABAFramework::new_with_argument_set(ArgumentSet::new_with_labels(&labels));
        af.set_as_assumption(&1).unwrap();
        af.set_as_contrary(&4, &1).unwrap();
        af.add_rule(&2, vec![&4, &3]).unwrap();
        af.add_rule(&3, vec![&2]).unwrap();
        af.add_rule(&4, vec![&1, &3]).unwrap();
        af.add_rule(&4, vec![&2]).unwrap();
        assert_eq!(4, af.n_rules());
        af.reduce_not_derivable();
        assert_eq!(0, af.n_rules());
    }

    #[test]
    fn test_reduce_4() {
        let labels: Vec<usize> = (1..=4).collect();
        let mut af = FlatABAFramework::new_with_argument_set(ArgumentSet::new_with_labels(&labels));
        af.set_as_assumption(&1).unwrap();
        af.set_as_contrary(&3, &1).unwrap();
        af.add_rule(&2, vec![&3]).unwrap();
        af.add_rule(&2, vec![&1, &4]).unwrap();
        af.add_rule(&3, vec![&2, &4]).unwrap();
        af.add_rule(&3, vec![&4, &2]).unwrap();
        af.add_rule(&4, vec![&1]).unwrap();
        af.add_rule(&4, vec![&3, &2]).unwrap();
        assert_eq!(6, af.n_rules());
        af.reduce_not_derivable();
        assert_eq!(6, af.n_rules());
    }
}
