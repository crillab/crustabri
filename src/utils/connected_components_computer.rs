use crate::{AAFramework, Argument, ArgumentSet, LabelType};

/// Returns the connected component the argument belongs to.
pub fn connected_component_of<T>(af: &AAFramework<T>, arg: &Argument<T>) -> AAFramework<T>
where
    T: LabelType,
{
    let connected_component = find_connected_component_of(
        af,
        arg.id(),
        &mut vec![false; af.argument_set().len()],
        &mut 0,
    );
    extract_connected_component(af, &connected_component)
}

/// Iterates over the connected components of an AF.
pub fn iter_connected_components<T>(af: &AAFramework<T>) -> ConnectedComponentsIter<T>
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

fn find_connected_components<T>(af: &AAFramework<T>) -> Vec<Vec<usize>>
where
    T: LabelType,
{
    let mut in_connected_components = vec![false; af.n_arguments()];
    let mut next = 0;
    let mut connected_components = Vec::new();
    while next < in_connected_components.len() {
        let current =
            find_connected_component_of(af, next, &mut in_connected_components, &mut next);
        connected_components.push(current);
    }
    connected_components
}

fn find_connected_component_of<T>(
    af: &AAFramework<T>,
    arg: usize,
    in_connected_components: &mut [bool],
    next: &mut usize,
) -> Vec<usize>
where
    T: LabelType,
{
    in_connected_components[arg] = true;
    let mut current = vec![arg];
    let mut newly_in_current = vec![arg];
    let update_next = |n: &mut usize, icc: &mut [bool]| {
        while *n < icc.len() && icc[*n] {
            *n += 1;
        }
    };
    update_next(next, in_connected_components);
    while !newly_in_current.is_empty() {
        let arg = newly_in_current.pop().unwrap();
        let mut add_to_current = |a: usize| {
            if !in_connected_components[a] {
                in_connected_components[a] = true;
                current.push(a);
                newly_in_current.push(a);
                if a == *next {
                    update_next(next, in_connected_components)
                }
            }
        };
        af.attack_ids_from(arg)
            .iter()
            .for_each(|att| add_to_current(af.attacks()[*att].1));
        af.attack_ids_to(arg)
            .iter()
            .for_each(|att| add_to_current(af.attacks()[*att].0));
    }
    current
}

fn extract_connected_component<T>(
    af: &AAFramework<T>,
    connected_component: &[usize],
) -> AAFramework<T>
where
    T: LabelType,
{
    let mut arg_mapping = vec![None; af.n_arguments()];
    connected_component
        .iter()
        .enumerate()
        .for_each(|(i, a)| arg_mapping[*a] = Some(i));
    let labels = connected_component
        .iter()
        .map(|i| af.argument_set().get_argument_by_id(*i).label().clone())
        .collect::<Vec<T>>();
    let arguments = ArgumentSet::new(&labels);
    let mut new_af = AAFramework::new(arguments);
    af.attacks().iter().for_each(|(i, j)| {
        if let Some(new_i) = arg_mapping[*i] {
            let new_j = arg_mapping[*j].unwrap();
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
    connected_components: Vec<Vec<usize>>,
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
}
