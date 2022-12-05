use crate::aa::LabelType;
use crate::aba::aba_framework::ABAFramework;
use crate::aba::aba_framework::Rule;

struct AssumptionSet {
    data: Vec<bool>,
    list: Vec<usize>,
}

impl AssumptionSet {
    fn new(n_atoms: usize) -> Self {
        AssumptionSet {
            data: vec![false; n_atoms],
            list: vec![],
        }
    }

    fn add(&mut self, index: usize) {
        if !self.data[index] {
            self.data[index] = true;
            self.list.push(index);
        }
    }

    fn get(&self) -> Vec<usize> {
        self.list.clone()
    }

    fn clear(&mut self) {
        for i in self.list.iter() {
            self.data[*i] = false;
        }
        self.list.clear();
    }
}

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
    closed: Vec<bool>,
    assumption_set: AssumptionSet,
}

impl<'a, T> AtomSupport<'a, T>
where
    T: LabelType,
{
    /// Computes the set of assumptions supporting the atoms of an ABA framework.
    pub fn compute(framework: &'a ABAFramework<T>) -> Self {
        let derivable_atoms = compute_derivables(framework);
        let language_len = framework.language_len();
        let mut sc = AtomSupport {
            framework,
            supports: vec![None; language_len],
            closed: vec![false; language_len],
            assumption_set: AssumptionSet::new(language_len),
        };
        for i in 0..sc.framework.language_len() {
            sc.close_atom(vec![i], &derivable_atoms);
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

    fn close_atom(&mut self, path: Vec<usize>, derivable_atoms: &[Option<AtomDerivationType>]) {
        use AtomDerivationType::*;
        let i = *path.last().expect("path must be non-empty");
        if self.closed[i] {
            return;
        }
        match &derivable_atoms[i] {
            None => {}
            Some(Assumption) => {
                self.supports[i] = Some(vec![vec![i]]) // only one manner to be derived: itself
            }
            Some(Rules(rules)) => {
                self.supports[i] = Some(vec![]);
                for rule_index in rules.iter() {
                    let rule = self.framework.get_rule_by_id(*rule_index);
                    let mut skip = false;
                    for v in rule.body_ids().iter() {
                        let mut occurrences = 0;
                        for p in path.iter() {
                            if v == p {
                                occurrences += 1;
                                if occurrences >= 2 {
                                    break;
                                }
                            }
                        }
                        if occurrences >= 2 {
                            skip = true;
                            break;
                        }
                    }
                    if skip {
                        continue;
                    }
                    for b in rule.body_ids() {
                        let mut path_clone = path.clone();
                        path_clone.push(*b);
                        self.close_atom(path_clone, derivable_atoms);
                    }
                    let mut new_supports =
                        rule_supports(&rule, &mut self.supports, &mut self.assumption_set);
                    self.supports[i].as_mut().unwrap().append(&mut new_supports);
                }
                self.supports[i] = Some(remove_duplicates(self.supports[i].as_ref().unwrap()));
            }
        }
        self.closed[i] = true;
    }
}

fn rule_supports<T>(
    r: &Rule<T>,
    supports: &mut [Option<Vec<Vec<usize>>>],
    assumption_set: &mut AssumptionSet,
) -> Vec<Vec<usize>>
where
    T: LabelType,
{
    let body = r.body_ids();
    if body.is_empty() {
        return vec![vec![]];
    }
    let mut res = supports[body[0]]
        .as_ref()
        .unwrap_or_else(|| panic!("atom with id {} should be closed", body[0]))
        .clone();
    let product_merge = |init: Vec<Vec<usize>>,
                         new: &[Vec<usize>],
                         assumption_set: &mut AssumptionSet|
     -> Vec<Vec<usize>> {
        let mut res = vec![];
        for a in init {
            for b in new {
                assumption_set.clear();
                a.iter().for_each(|v| assumption_set.add(*v));
                b.iter().for_each(|v| assumption_set.add(*v));
                res.push(assumption_set.get());
            }
        }
        remove_duplicates(res.as_slice())
    };
    for b in body.iter().skip(1) {
        res = product_merge(
            res,
            supports[*b]
                .as_ref()
                .unwrap_or_else(|| panic!("atom with id {} should be closed", b)),
            assumption_set,
        );
    }
    res
}

fn remove_duplicates(data: &[Vec<usize>]) -> Vec<Vec<usize>> {
    let mut res = vec![];
    for (i, s) in data.iter().enumerate() {
        let mut c = s.to_vec();
        c.sort();
        let mut add = true;
        for p in res.iter().take(i) {
            if c == *p {
                add = false;
                break;
            }
        }
        if add {
            res.push(c);
        }
    }
    res
}

fn compute_derivables<T>(framework: &ABAFramework<T>) -> Vec<Option<AtomDerivationType>>
where
    T: LabelType,
{
    use AtomDerivationType::*;
    let mut derivable_atoms = vec![None; framework.language_len()];
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

    #[test]
    fn test_remove_duplicates() {
        let data = vec![vec![1], vec![1, 2], vec![2, 1], vec![2]];
        let no_dup = remove_duplicates(data.as_slice());
        assert_eq!(3, no_dup.len());
        no_dup.iter().find(|s| **s == vec![1]).unwrap();
        no_dup
            .iter()
            .find(|s| **s == vec![1, 2] || **s == vec![2, 1])
            .unwrap();
        no_dup.iter().find(|s| **s == vec![2]).unwrap();
    }

    fn toni_tutorial_ex() -> ABAFramework<&'static str> {
        let l = Language::new_with_labels(&["a", "b", "c", "p", "q", "r", "s", "t"]);
        let mut framework = ABAFramework::with_capacity(l, 3, 3);
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
    fn test_rule_support_empty_body() {
        let f = toni_tutorial_ex();
        let mut assumption_set = AssumptionSet::new(8);
        let actual = rule_supports(
            &f.get_rule_by_id(1),
            &mut [None, None, None, None, None, None, None, None],
            &mut assumption_set,
        );
        assert_eq!(vec![vec![] as Vec<usize>], actual);
    }

    #[test]
    fn test_rule_support_assumption_only_body() {
        let f = toni_tutorial_ex();
        let mut assumption_set = AssumptionSet::new(8);
        let actual = rule_supports(
            &f.get_rule_by_id(2),
            &mut [
                None,
                Some(vec![vec![1]]),
                Some(vec![vec![2]]),
                None,
                None,
                None,
                None,
                None,
            ],
            &mut assumption_set,
        );
        assert_eq!(vec![vec![1_usize, 2]], actual);
    }

    #[test]
    #[should_panic]
    fn test_rule_support_body_not_closed() {
        let f = toni_tutorial_ex();
        let mut assumption_set = AssumptionSet::new(8);
        rule_supports(
            &f.get_rule_by_id(2),
            &mut [None, None, None, None, None, None, None, None],
            &mut assumption_set,
        );
    }

    #[test]
    fn test_rule_support_inference() {
        let f = toni_tutorial_ex();
        let mut assumption_set = AssumptionSet::new(8);
        let actual = rule_supports(
            &f.get_rule_by_id(0),
            &mut [
                Some(vec![vec![0]]),
                None,
                None,
                None,
                Some(vec![vec![]]),
                None,
                None,
                None,
            ],
            &mut assumption_set,
        );
        assert_eq!(vec![vec![0_usize]], actual);
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
}
