use crate::{AAFramework, Argument, ArgumentSet, LabelType};
use std::iter::Peekable;

/// Returns the connected component the argument belongs to.
pub fn connected_component_of<T>(af: &AAFramework<T>, arg: &Argument<T>) -> AAFramework<T>
where
    T: LabelType,
{
    let connected_component = find_connected_component_of(
        af,
        arg,
        &mut vec![false; af.argument_set().len()],
        &mut af.argument_set().iter().peekable(),
    );
    extract_connected_component(af, &connected_component)
}

/// Iterates over the connected components of an AF.
pub fn iter_connected_components<T>(
    af: &AAFramework<T>,
) -> impl Iterator<Item = AAFramework<T>> + '_
where
    T: LabelType,
{
    let connected_components = find_connected_components(af);
    ConnectedComponentsIter {
        af,
        connected_components,
        next: 0,
    }
}

fn find_connected_components<T>(af: &AAFramework<T>) -> Vec<Vec<&Argument<T>>>
where
    T: LabelType,
{
    let mut in_connected_components = vec![false; 1 + af.max_argument_id()];
    let mut next = af.argument_set().iter().peekable();
    let mut connected_components = Vec::new();
    while next.peek().is_some() {
        let current = find_connected_component_of(
            af,
            next.next().unwrap(),
            &mut in_connected_components,
            &mut next,
        );
        connected_components.push(current);
    }
    connected_components
}

fn find_connected_component_of<'a, I, T>(
    af: &'a AAFramework<T>,
    arg: &'a Argument<T>,
    in_connected_components: &mut [bool],
    next: &mut Peekable<I>,
) -> Vec<&'a Argument<T>>
where
    T: LabelType,
    I: Iterator<Item = &'a Argument<T>>,
{
    in_connected_components[arg.id()] = true;
    let mut current = vec![arg];
    let mut newly_in_current = vec![arg];
    let update_next = |n: &mut Peekable<I>, icc: &mut [bool]| {
        while let Some(arg) = n.peek() {
            if icc[arg.id()] {
                n.next();
            } else {
                break;
            }
        }
    };
    update_next(next, in_connected_components);
    while !newly_in_current.is_empty() {
        let arg = newly_in_current.pop().unwrap();
        let mut add_to_current = |a: &'a Argument<T>| {
            if !in_connected_components[a.id()] {
                in_connected_components[a.id()] = true;
                current.push(a);
                newly_in_current.push(a);
                if next.peek() == Some(&a) {
                    update_next(next, in_connected_components)
                }
            }
        };
        af.iter_attacks_from(arg).for_each(|att| {
            add_to_current(att.attacked());
        });
        af.iter_attacks_to(arg).for_each(|att| {
            add_to_current(att.attacker());
        });
    }
    current
}

fn extract_connected_component<T>(
    af: &AAFramework<T>,
    connected_component: &[&Argument<T>],
) -> AAFramework<T>
where
    T: LabelType,
{
    let mut arg_mapping = vec![None; 1 + af.max_argument_id()];
    connected_component
        .iter()
        .enumerate()
        .for_each(|(i, a)| arg_mapping[a.id()] = Some(i));
    let labels = connected_component
        .iter()
        .map(|a| a.label().clone())
        .collect::<Vec<T>>();
    let arguments = ArgumentSet::new_with_labels(&labels);
    let mut new_af = AAFramework::new_with_argument_set(arguments);
    af.iter_attacks().for_each(|att| {
        if let Some(new_i) = arg_mapping[att.attacker().id()] {
            let new_j = arg_mapping[att.attacked().id()].unwrap();
            new_af.new_attack_by_ids(new_i, new_j).unwrap();
        }
    });
    new_af
}

pub struct ConnectedComponentsIter<'a, T>
where
    T: LabelType,
{
    af: &'a AAFramework<T>,
    connected_components: Vec<Vec<&'a Argument<T>>>,
    next: usize,
}

impl<T> Iterator for ConnectedComponentsIter<'_, T>
where
    T: LabelType,
{
    type Item = AAFramework<T>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.next == self.connected_components.len() {
            None
        } else {
            let new_af =
                extract_connected_component(self.af, &self.connected_components[self.next]);
            self.next += 1;
            Some(new_af)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{io::InstanceReader, AspartixReader, AspartixWriter};
    use std::io::Cursor;

    #[test]
    fn test_connected_components_of() {
        let instance = r#"
        arg(a0).
        arg(a1).
        att(a0,a1).
        "#;
        let reader = AspartixReader::default();
        let af = reader.read(&mut instance.as_bytes()).unwrap();
        let arg = af.argument_set().get_argument(&"a1".to_string()).unwrap();
        let writer = AspartixWriter::default();
        let mut buffer0 = Cursor::new(Vec::new());
        writer.write_framework(&af, &mut buffer0).unwrap();
        let mut buffer1 = Cursor::new(Vec::new());
        writer
            .write_framework(&connected_component_of(&af, arg), &mut buffer1)
            .unwrap();
        let s0 = String::from_utf8(buffer0.into_inner()).unwrap();
        let mut lines0 = s0.split('\n').collect::<Vec<&str>>();
        lines0.sort_unstable();
        let s1 = String::from_utf8(buffer1.into_inner()).unwrap();
        let mut lines1 = s1.split('\n').collect::<Vec<&str>>();
        lines1.sort_unstable();
        assert_eq!(lines0, lines1,)
    }

    #[test]
    fn test_connected_components() {
        let instance = r#"
        arg(a0).
        arg(a1).
        arg(a2).
        att(a1,a2).
        "#;
        let reader = AspartixReader::default();
        let af = reader.read(&mut instance.as_bytes()).unwrap();
        let components = iter_connected_components(&af).collect::<Vec<AAFramework<String>>>();
        let writer = AspartixWriter::default();
        let mut instance0 = Cursor::new(Vec::new());
        writer
            .write_framework(&components[0], &mut instance0)
            .unwrap();
        assert_eq!(
            "arg(a0).\n",
            String::from_utf8(instance0.into_inner()).unwrap()
        );
        let mut instance1 = Cursor::new(Vec::new());
        writer
            .write_framework(&components[1], &mut instance1)
            .unwrap();
        assert_eq!(
            "arg(a1).\narg(a2).\natt(a1,a2).\n",
            String::from_utf8(instance1.into_inner()).unwrap()
        );
    }

    #[test]
    fn test_connected_components_after_arg_removal() {
        let instance = r#"
        arg(a0).
        arg(a1).
        arg(a2).
        att(a0,a1).
        att(a1,a2).
        "#;
        let reader = AspartixReader::default();
        let mut af = reader.read(&mut instance.as_bytes()).unwrap();
        assert_eq!(1, iter_connected_components(&af).count());
        af.remove_argument(&"a1".to_string()).unwrap();
        let components_after = iter_connected_components(&af).collect::<Vec<AAFramework<String>>>();
        assert_eq!(2, components_after.len());
        let writer = AspartixWriter::default();
        let mut instance0 = Cursor::new(Vec::new());
        writer
            .write_framework(&components_after[0], &mut instance0)
            .unwrap();
        assert_eq!(
            "arg(a0).\n",
            String::from_utf8(instance0.into_inner()).unwrap()
        );
        let mut instance1 = Cursor::new(Vec::new());
        writer
            .write_framework(&components_after[1], &mut instance1)
            .unwrap();
        assert_eq!(
            "arg(a2).\n",
            String::from_utf8(instance1.into_inner()).unwrap()
        );
    }
}
