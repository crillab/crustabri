use crate::aba::aba_framework::ABAFramework;
use crate::utils::LabelType;
use permutator::CartesianProduct;

#[derive(Clone, Debug, PartialEq)]
enum AtomDerivationType {
    Assumption,
    Rules(Vec<usize>),
}

/// An objet used to compute the set of assumptions supporting the atoms of an ABA framework.
pub struct AtomSupport<'a, T>
where
    T: LabelType,
{
    framework: &'a ABAFramework<T>,
    supports: Vec<Option<Vec<Vec<usize>>>>,
    supports_cache: Vec<Option<Option<Vec<Vec<usize>>>>>,
}

impl<'a, T> AtomSupport<'a, T>
where
    T: LabelType,
{
    /// Computes the set of assumptions supporting the atoms of an ABA framework.
    pub fn compute(framework: &'a ABAFramework<T>) -> Self {
        let derivable_atoms = compute_derivables(framework);
        let language_len = framework.language().len();
        let mut sc = AtomSupport {
            framework,
            supports: vec![None; language_len],
            supports_cache: vec![None; language_len],
        };
        for i in 0..sc.framework.language().len() {
            sc.supports[i] = sc.compute_derivation_from_assumptions(vec![i], &derivable_atoms);
        }
        sc
    }

    /// Iterates over the possible supports of each atom.
    ///
    /// Each element of the iterator concerns an atom.
    /// The first is the one of index 0, the second the one of index 1, and so on.
    ///
    /// If an atom has no support, the corresponding element is `None`.
    /// In the other case, the element is a `Some` instance containing the vector of the possible supports.
    /// Supports are given as vectors of assumption identifiers.
    ///
    /// An assumption has only one support: itself.
    pub fn iter_supports(&self) -> std::slice::Iter<'_, Option<Vec<Vec<usize>>>> {
        self.supports.iter()
    }

    fn compute_derivation_from_assumptions(
        &mut self,
        path: Vec<usize>,
        derivable_atoms: &[Option<AtomDerivationType>],
    ) -> Option<Vec<Vec<usize>>> {
        let current = *path.last().unwrap();
        if path[0..path.len() - 1].contains(&current) {
            return None;
        }
        if let Some(cached) = &self.supports_cache[current] {
            return cached.clone();
        }
        let result = match &derivable_atoms[current] {
            None => None,
            Some(AtomDerivationType::Assumption) => Some(vec![vec![current]]),
            Some(AtomDerivationType::Rules(rules)) => {
                let mut domain_union = Vec::with_capacity(rules.len());
                let mut got_solution = false;
                rules.iter().for_each(|rule_index| {
                    let mut rule_domains = Vec::new();
                    let rule = self.framework.get_rule_by_id(*rule_index);
                    let mut got_cycle = false;
                    if rule.body_ids().is_empty() {
                        domain_union.push(vec![]);
                        got_solution = true;
                        return;
                    }
                    rule.body_ids().iter().for_each(|body_id| {
                        let mut path_clone = path.clone();
                        path_clone.push(*body_id);
                        if let Some(domain) =
                            self.compute_derivation_from_assumptions(path_clone, derivable_atoms)
                        {
                            rule_domains.push(domain);
                        } else {
                            got_cycle = true;
                        }
                    });
                    if !got_cycle {
                        got_solution = true;
                        let rule_domain_refs = rule_domains
                            .iter()
                            .map(|v| v.as_slice())
                            .collect::<Vec<&[Vec<usize>]>>();
                        let mut rule_derivations = rule_domain_refs
                            .as_slice()
                            .cart_prod()
                            .map(|p| {
                                let mut d = p.iter().fold(Vec::new(), |mut acc, x| {
                                    acc.append(&mut x.as_slice().to_vec());
                                    acc
                                });
                                d.sort_unstable();
                                d.dedup();
                                d
                            })
                            .collect::<Vec<Vec<usize>>>();
                        domain_union.append(&mut rule_derivations);
                    }
                });
                if got_solution {
                    domain_union.sort_unstable();
                    domain_union.dedup();
                    Some(domain_union)
                } else {
                    None
                }
            }
        };
        if result.is_some() {
            self.supports_cache[current] = Some(result.clone());
        }
        result
    }
}

fn compute_derivables<T>(framework: &ABAFramework<T>) -> Vec<Option<AtomDerivationType>>
where
    T: LabelType,
{
    use AtomDerivationType::*;
    let mut derivable_atoms = vec![None; framework.language().len()];
    for index in framework.assumption_ids() {
        derivable_atoms[*index] = Some(Assumption);
    }
    let mut derivable_rules = vec![false; framework.n_rules()];
    let mut new_derivable_rules = vec![];
    loop {
        new_derivable_rules.clear();
        for (i, _) in derivable_rules.iter().enumerate().filter(|(_, v)| !*v) {
            let r = framework.get_rule_by_id(i);
            let mut is_derivable = true;
            for b in r.body_ids().iter() {
                if derivable_atoms[*b].is_none() {
                    is_derivable = false;
                    break;
                }
            }
            if is_derivable {
                match &mut derivable_atoms[r.head_id()] {
                    None => derivable_atoms[r.head_id()] = Some(Rules(vec![i])),
                    Some(Assumption) => panic!("ABA framework is not flat"),
                    Some(Rules(v)) => v.push(i),
                }
                new_derivable_rules.push(i);
            }
        }
        new_derivable_rules
            .iter()
            .for_each(|i| derivable_rules[*i] = true);
        if new_derivable_rules.is_empty() {
            break derivable_atoms;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::aba::language::Language;

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
    fn test_compute_derivables() {
        use AtomDerivationType::*;
        let f = toni_tutorial_ex();
        let derivable_atoms = compute_derivables(&f);
        assert_eq!(
            vec![
                Some(Assumption),
                Some(Assumption),
                Some(Assumption),
                Some(Rules(vec![0])),
                Some(Rules(vec![1])),
                Some(Rules(vec![2])),
                None,
                None
            ],
            derivable_atoms
        );
    }

    #[test]
    fn test_compute_derivables_with_loop() {
        use AtomDerivationType::*;
        let mut f = toni_tutorial_ex();
        f.new_rule(&"p", &[&"s"]).unwrap();
        f.new_rule(&"s", &[&"p"]).unwrap();
        let derivable_atoms = compute_derivables(&f);
        assert_eq!(
            vec![
                Some(Assumption),
                Some(Assumption),
                Some(Assumption),
                Some(Rules(vec![0, 3])),
                Some(Rules(vec![1])),
                Some(Rules(vec![2])),
                Some(Rules(vec![4])),
                None
            ],
            derivable_atoms
        );
    }

    #[test]
    fn test_supports_computer() {
        let f = toni_tutorial_ex();
        let sc = AtomSupport::compute(&f);
        assert_eq!(
            vec![
                Some(vec![vec![0]]),
                Some(vec![vec![1]]),
                Some(vec![vec![2]]),
                Some(vec![vec![0]]),
                Some(vec![vec![]]),
                Some(vec![vec![1, 2]]),
                None,
                None
            ],
            sc.supports
        );
    }

    #[test]
    fn test_supports_with_loop() {
        let mut f = toni_tutorial_ex();
        f.new_rule(&"p", &[&"s"]).unwrap();
        f.new_rule(&"s", &[&"p"]).unwrap();
        let sc = AtomSupport::compute(&f);
        assert_eq!(
            vec![
                Some(vec![vec![0]]),
                Some(vec![vec![1]]),
                Some(vec![vec![2]]),
                Some(vec![vec![0]]),
                Some(vec![vec![]]),
                Some(vec![vec![1, 2]]),
                Some(vec![vec![0]]),
                None
            ],
            sc.supports
        );
    }

    #[test]
    fn test_derive_contrary() {
        use AtomDerivationType::*;
        let l = Language::new_with_labels(&[0, 1, 2, 3, 4, 5, 6, 7, 8]);
        let mut framework = ABAFramework::new_with_language(l);
        framework.new_assumption(&0, &5).unwrap();
        framework.new_assumption(&1, &6).unwrap();
        framework.new_rule(&4, &[&0]).unwrap();
        framework.new_rule(&6, &[&4]).unwrap();
        framework.new_rule(&7, &[&6]).unwrap();
        framework.new_rule(&5, &[&7]).unwrap();
        framework.new_rule(&7, &[&3, &5]).unwrap();
        framework.new_rule(&3, &[&6]).unwrap();
        framework.new_rule(&8, &[&7]).unwrap();
        framework.new_rule(&6, &[&8, &3]).unwrap();
        let derivables = compute_derivables(&framework);
        assert_eq!(
            vec![
                Some(Assumption),
                Some(Assumption),
                None,
                Some(Rules(vec![5])),
                Some(Rules(vec![0])),
                Some(Rules(vec![3])),
                Some(Rules(vec![1, 7])),
                Some(Rules(vec![2, 4])),
                Some(Rules(vec![6])),
            ],
            derivables
        );
        let sc = AtomSupport::compute(&framework);
        assert_eq!(
            vec![
                Some(vec![vec![0]]),
                Some(vec![vec![1]]),
                None,
                Some(vec![vec![0]]),
                Some(vec![vec![0]]),
                Some(vec![vec![0]]),
                Some(vec![vec![0]]),
                Some(vec![vec![0]]),
                Some(vec![vec![0]]),
            ],
            sc.supports
        );
    }
}
