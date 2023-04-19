use super::{Label, LabelType};
use crate::aa::{AAFramework, ArgumentSet};

enum EqClass {
    Grounded(Vec<usize>),
    GroundedDefeated(Vec<usize>),
    NotGrounded(Vec<usize>),
}

impl EqClass {
    fn iter(&self) -> impl Iterator<Item = &usize> + '_ {
        match self {
            EqClass::Grounded(v) | EqClass::GroundedDefeated(v) | EqClass::NotGrounded(v) => {
                v.iter()
            }
        }
    }

    fn first(&self) -> usize {
        match self {
            EqClass::Grounded(v) | EqClass::GroundedDefeated(v) | EqClass::NotGrounded(v) => v[0],
        }
    }
}

/// An object used to reduce AFs by computing argument equivalency classes for admissible semantics.
pub struct EquivalencyComputer<'a, T>
where
    T: LabelType,
{
    init_af: &'a AAFramework<T>,
    reduced_af: AAFramework<T>,
    classes: Vec<EqClass>,
    init_to_reduced_id: Vec<usize>,
}

impl<'a, T> EquivalencyComputer<'a, T>
where
    T: LabelType,
{
    /// Computes a reduced AF and returns an instance a structure allowing to handle it.
    pub fn new(init_af: &'a AAFramework<T>) -> Self {
        let classes = compute_classes(init_af);
        let (reduced_af, init_to_reduced_id) = reduce_af(init_af, &classes);
        Self {
            init_af,
            reduced_af,
            classes,
            init_to_reduced_id,
        }
    }

    /// REturns the reduced AF.
    pub fn reduced_af(&self) -> &AAFramework<T> {
        &self.reduced_af
    }

    /// Given an argument that belongs to the initial AF, returns the corresponding argument in the reduced AF.
    pub fn init_to_reduced_arg(&self, init_arg: &Label<T>) -> &Label<T> {
        self.reduced_af.argument_set().get_argument_by_id(
            self.init_to_reduced_id[self
                .init_af
                .argument_set()
                .get_argument_by_id(init_arg.id())
                .id()],
        )
    }

    /// Given an argument of the reduced AF, returns the set of corresponding arguments in the initial AF.
    pub fn reduced_arg_to_init_args(&self, reduced_arg: &Label<T>) -> Vec<&Label<T>> {
        self.classes[reduced_arg.id()]
            .iter()
            .map(|id| self.init_af.argument_set().get_argument_by_id(*id))
            .collect()
    }
}

fn compute_classes<T>(af: &AAFramework<T>) -> Vec<EqClass>
where
    T: LabelType,
{
    let mut n_attacks_to = vec![0; af.n_arguments()];
    af.iter_attacks()
        .for_each(|att| n_attacks_to[att.attacked().id()] += 1);
    let mut classes = Vec::new();
    if let Some((grounded, defeated)) = compute_grounded_classes(af, &n_attacks_to) {
        if !grounded.is_empty() {
            classes.push(EqClass::Grounded(grounded));
        }
        if !defeated.is_empty() {
            classes.push(EqClass::GroundedDefeated(defeated));
        }
    } else {
        return (0..af.n_arguments())
            .map(|i| EqClass::NotGrounded(vec![i]))
            .collect();
    }
    let mut in_classes = vec![false; af.n_arguments()];
    classes
        .iter()
        .for_each(|c| c.iter().for_each(|id| in_classes[*id] = true));
    let mut propagations = vec![None; af.n_arguments()];
    for arg in 0..af.n_arguments() {
        if in_classes[arg] {
            continue;
        }
        let opt_arg_propagations = if propagations[arg].is_some() {
            std::mem::replace(&mut propagations[arg], Some(Vec::new()))
        } else {
            propagate(af, &n_attacks_to, &[arg]).map(|p| p.0)
        };
        let mut arg_class = vec![arg];
        in_classes[arg] = true;
        let mut arg_propagations = if let Some(p) = opt_arg_propagations {
            p
        } else {
            classes.push(EqClass::NotGrounded(arg_class));
            continue;
        };
        arg_propagations.retain(|id| !in_classes[*id] && *id > arg);
        arg_propagations.iter().for_each(|id| {
            propagations[*id] = match propagate(af, &n_attacks_to, &[*id]) {
                Some(p) => Some(p.0),
                None => Some(Vec::new()),
            };
            if propagations[*id].as_ref().unwrap().contains(&arg) {
                arg_class.push(*id);
                in_classes[*id] = true;
                propagations[*id] = Some(Vec::new());
            }
        });
        classes.push(EqClass::NotGrounded(arg_class));
    }
    classes
}

fn compute_grounded_classes<T>(
    af: &AAFramework<T>,
    n_attacks_to: &[usize],
) -> Option<(Vec<usize>, Vec<usize>)>
where
    T: LabelType,
{
    let to_propagate: Vec<usize> = n_attacks_to
        .iter()
        .enumerate()
        .filter_map(|(arg, n)| if *n == 0 { Some(arg) } else { None })
        .collect();
    propagate(af, n_attacks_to, &to_propagate)
}

fn propagate<T>(
    af: &AAFramework<T>,
    n_attacks_to: &[usize],
    args: &[usize],
) -> Option<(Vec<usize>, Vec<usize>)>
where
    T: LabelType,
{
    let mut local_n_attacks_to = n_attacks_to.to_vec();
    let mut propagated = args.to_vec();
    let mut in_propagated = vec![false; af.n_arguments()];
    args.iter().for_each(|id| in_propagated[*id] = true);
    let mut next_index = 0;
    let mut defeated = Vec::new();
    let mut in_defeated = vec![false; af.n_arguments()];
    while next_index < propagated.len() {
        let id = propagated[next_index];
        next_index += 1;
        if af
            .iter_attacks_from_id(id)
            .try_for_each(|att| {
                let attacked = att.attacked().id();
                if in_propagated[attacked] {
                    return Err(());
                }
                if !in_defeated[attacked] {
                    defeated.push(attacked);
                    in_defeated[attacked] = true;
                    af.iter_attacks_from_id(attacked).for_each(|def| {
                        let defended = def.attacked().id();
                        if !args.contains(&defended) {
                            local_n_attacks_to[defended] -= 1;
                            if local_n_attacks_to[defended] == 0 {
                                propagated.push(defended);
                                in_propagated[defended] = true;
                            }
                        }
                    });
                }
                Ok(())
            })
            .is_err()
        {
            return None;
        };
    }
    Some((propagated, defeated))
}

fn reduce_af<T>(init_af: &AAFramework<T>, classes: &[EqClass]) -> (AAFramework<T>, Vec<usize>)
where
    T: LabelType,
{
    let reduced_labels = classes
        .iter()
        .map(|cl| {
            init_af
                .argument_set()
                .get_argument_by_id(cl.first())
                .label()
        })
        .cloned()
        .collect::<Vec<T>>();
    let mut init_to_reduced_id = vec![0; init_af.n_arguments()];
    classes.iter().enumerate().for_each(|(class_id, class)| {
        class
            .iter()
            .for_each(|arg_id| init_to_reduced_id[*arg_id] = class_id)
    });
    let reduced_arg_set = ArgumentSet::new_with_labels(&reduced_labels);
    let mut reduced_af = AAFramework::new_with_argument_set(reduced_arg_set);
    init_af.iter_attacks().for_each(|att| {
        let reduced_from_id = init_to_reduced_id[att.attacker().id()];
        if matches!(classes[reduced_from_id], EqClass::GroundedDefeated(_)) {
            return;
        }
        reduced_af
            .new_attack(
                &reduced_labels[reduced_from_id],
                &reduced_labels[init_to_reduced_id[att.attacked().id()]],
            )
            .unwrap();
    });
    (reduced_af, init_to_reduced_id)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::io::{Iccma23Reader, InstanceReader};

    impl EqClass {
        fn unwrap(self) -> Vec<usize> {
            match self {
                EqClass::Grounded(v) | EqClass::GroundedDefeated(v) | EqClass::NotGrounded(v) => v,
            }
        }
    }

    #[test]
    fn test_grounded_classes_path() {
        let apx = "p af 4\n1 2\n2 3\n3 4\n";
        let af = Iccma23Reader::default().read(&mut apx.as_bytes()).unwrap();
        let mut init_n_attacks_to = vec![0; af.n_arguments()];
        af.iter_attacks()
            .for_each(|att| init_n_attacks_to[att.attacked().id()] += 1);
        let (grounded, defeated) = compute_grounded_classes(&af, &init_n_attacks_to).unwrap();
        assert_eq!(vec![0, 2], grounded);
        assert_eq!(vec![1, 3], defeated);
    }

    #[test]
    fn test_grounded_classes_hierarchy() {
        let apx = "p af 7\n1 2\n1 3\n2 4\n2 5\n3 4\n3 5\n4 6\n4 7\n5 6\n5 7\n";
        let af = Iccma23Reader::default().read(&mut apx.as_bytes()).unwrap();
        let mut init_n_attacks_to = vec![0; af.n_arguments()];
        af.iter_attacks()
            .for_each(|att| init_n_attacks_to[att.attacked().id()] += 1);
        let (grounded, defeated) = compute_grounded_classes(&af, &init_n_attacks_to).unwrap();
        assert_eq!(vec![0, 3, 4], grounded);
        assert_eq!(vec![1, 2, 5, 6], defeated);
    }

    #[test]
    fn test_grounded_classes_with_ring_of_3() {
        let apx = "p af 4\n1 2\n2 3\n3 4\n4 2\n";
        let af = Iccma23Reader::default().read(&mut apx.as_bytes()).unwrap();
        let mut init_n_attacks_to = vec![0; af.n_arguments()];
        af.iter_attacks()
            .for_each(|att| init_n_attacks_to[att.attacked().id()] += 1);
        let (grounded, defeated) = compute_grounded_classes(&af, &init_n_attacks_to).unwrap();
        assert_eq!(vec![0, 2], grounded);
        assert_eq!(vec![1, 3], defeated);
    }

    #[test]
    fn test_grounded_classes_with_ring_of_4() {
        let apx = "p af 5\n1 2\n2 3\n3 4\n4 5\n5 2\n";
        let af = Iccma23Reader::default().read(&mut apx.as_bytes()).unwrap();
        let mut init_n_attacks_to = vec![0; af.n_arguments()];
        af.iter_attacks()
            .for_each(|att| init_n_attacks_to[att.attacked().id()] += 1);
        let (grounded, defeated) = compute_grounded_classes(&af, &init_n_attacks_to).unwrap();
        assert_eq!(vec![0, 2, 4], grounded);
        assert_eq!(vec![1, 3], defeated);
    }

    #[test]
    fn test_propagate_ring_of_3() {
        let apx = "p af 3\n1 2\n2 3\n3 1\n";
        let af = Iccma23Reader::default().read(&mut apx.as_bytes()).unwrap();
        let mut init_n_attacks_to = vec![0; af.n_arguments()];
        af.iter_attacks()
            .for_each(|att| init_n_attacks_to[att.attacked().id()] += 1);
        assert!(propagate(&af, &init_n_attacks_to, &[0]).is_none());
    }

    #[test]
    fn test_propagate_ring_of_4() {
        let apx = "p af 4\n1 2\n2 3\n3 4\n4 1\n";
        let af = Iccma23Reader::default().read(&mut apx.as_bytes()).unwrap();
        let mut init_n_attacks_to = vec![0; af.n_arguments()];
        af.iter_attacks()
            .for_each(|att| init_n_attacks_to[att.attacked().id()] += 1);
        let (propagated, defeated) = propagate(&af, &init_n_attacks_to, &[0]).unwrap();
        assert_eq!(vec![0, 2], propagated);
        assert_eq!(vec![1, 3], defeated);
    }

    #[test]
    fn test_compute_classes_ring_of_3() {
        let apx = "p af 3\n1 2\n2 3\n3 1\n";
        let af = Iccma23Reader::default().read(&mut apx.as_bytes()).unwrap();
        let eq_classes = compute_classes(&af);
        assert_eq!(
            vec![vec![0], vec![1], vec![2]],
            eq_classes
                .into_iter()
                .map(|c| c.unwrap())
                .collect::<Vec<Vec<usize>>>()
        );
    }

    #[test]
    fn test_compute_classes_ring_of_4() {
        let apx = "p af 4\n1 2\n2 3\n3 4\n4 1\n";
        let af = Iccma23Reader::default().read(&mut apx.as_bytes()).unwrap();
        let eq_classes = compute_classes(&af);
        assert_eq!(
            vec![vec![0, 2], vec![1, 3]],
            eq_classes
                .into_iter()
                .map(|c| c.unwrap())
                .collect::<Vec<Vec<usize>>>()
        );
    }

    #[test]
    fn test_autoattack() {
        let apx = "p af 3\n1 2\n2 3\n3 3\n";
        let af = Iccma23Reader::default().read(&mut apx.as_bytes()).unwrap();
        let eq_classes = compute_classes(&af);
        assert_eq!(
            vec![vec![0], vec![1], vec![2]],
            eq_classes
                .into_iter()
                .map(|c| c.unwrap())
                .collect::<Vec<Vec<usize>>>()
        );
    }

    #[test]
    fn test_reduce_grounded_path() {
        let apx = "p af 3\n1 2\n2 3\n";
        let af = Iccma23Reader::default().read(&mut apx.as_bytes()).unwrap();
        let reducer = EquivalencyComputer::new(&af);
        assert_eq!(2, reducer.reduced_af().n_arguments());
        assert_eq!(1, reducer.reduced_af().n_attacks());
    }
}
