use super::LabelType;
use crate::aa::{AAFramework, Argument, ArgumentSet};

/// An object used to decompose an AF into its connected components.
///
/// Connected components are returned as other AFs.
/// Be careful that arguments in such sub-AFs shares the labels of the initial AF but identifiers differ.
pub struct ConnectedComponentsComputer<'a, T>
where
    T: LabelType,
{
    init_af: &'a AAFramework<T>,
    in_connected_components: Vec<bool>,
    next_arg_id: usize,
}

impl<'a, T> ConnectedComponentsComputer<'a, T>
where
    T: LabelType,
{
    /// Builds a new connected component computer for an AF.
    pub fn new(af: &'a AAFramework<T>) -> Self {
        let mut c = ConnectedComponentsComputer {
            init_af: af,
            in_connected_components: vec![false; 1 + af.max_argument_id().unwrap_or_default()],
            next_arg_id: 0,
        };
        c.update_next();
        c
    }

    /// Computes and merge the connected component in which the provided arguments belongs.
    ///
    /// The arguments must exist, and the related connected component must not have been computed yet.
    ///
    /// # Panics
    ///
    /// If the argument does not exist, or if the connected component containing one of the argument has already been computed,
    /// this function panics.
    pub fn merged_connected_components_of(&mut self, args: &[&'a Argument<T>]) -> AAFramework<T> {
        if args.iter().any(|a| self.in_connected_components[a.id()]) {
            panic!("this connected component was already computed");
        }
        let mut connected_component = Vec::new();
        args.iter().for_each(|a| {
            if !self.in_connected_components[a.id()] {
                connected_component.append(&mut self.find_connected_component_of(a))
            }
        });
        self.extract_connected_component(&connected_component)
    }

    /// Computes a connected component that have not been computed yet.
    ///
    /// In case no such connected component exists, `None` is returned.
    pub fn next_connected_component(&mut self) -> Option<AAFramework<T>> {
        if self.init_af.argument_set().is_empty()
            || self.next_arg_id == self.in_connected_components.len()
        {
            None
        } else {
            let connected_component = self.find_connected_component_of(
                self.init_af
                    .argument_set()
                    .get_argument_by_id(self.next_arg_id),
            );
            Some(self.extract_connected_component(&connected_component))
        }
    }

    fn find_connected_component_of(&mut self, arg: &'a Argument<T>) -> Vec<&'a Argument<T>> {
        self.in_connected_components[arg.id()] = true;
        let mut current = vec![arg];
        let mut newly_in_current = vec![arg];
        self.update_next();
        while !newly_in_current.is_empty() {
            let arg = newly_in_current.pop().unwrap();
            self.init_af
                .iter_attacks_from(arg)
                .chain(self.init_af.iter_attacks_to(arg))
                .for_each(|att| {
                    let a = if att.attacked() == arg {
                        att.attacker()
                    } else {
                        att.attacked()
                    };
                    if !self.in_connected_components[a.id()] {
                        self.in_connected_components[a.id()] = true;
                        current.push(a);
                        newly_in_current.push(a);
                        if self.next_arg_id == a.id() {
                            self.update_next()
                        }
                    }
                });
        }
        current
    }

    fn update_next(&mut self) {
        while self.next_arg_id < self.in_connected_components.len()
            && (self.in_connected_components[self.next_arg_id]
                || !self
                    .init_af
                    .argument_set()
                    .has_argument_with_id(self.next_arg_id))
        {
            self.next_arg_id += 1;
        }
    }

    fn extract_connected_component(&self, connected_component: &[&Argument<T>]) -> AAFramework<T>
    where
        T: LabelType,
    {
        let mut arg_mapping = vec![None; 1 + self.init_af.max_argument_id().unwrap()];
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
        self.init_af.iter_attacks().for_each(|att| {
            if let Some(new_i) = arg_mapping[att.attacker().id()] {
                let new_j = arg_mapping[att.attacked().id()].unwrap();
                new_af.new_attack_by_ids(new_i, new_j).unwrap();
            }
        });
        new_af
    }

    /// Iterates over the connected components of an AF.
    pub fn iter_connected_components(af: &AAFramework<T>) -> ConnectedComponentsIterator<T>
    where
        T: LabelType,
    {
        ConnectedComponentsIterator {
            computer: ConnectedComponentsComputer::new(af),
        }
    }
}

pub struct ConnectedComponentsIterator<'a, T>
where
    T: LabelType,
{
    computer: ConnectedComponentsComputer<'a, T>,
}

impl<'a, T> Iterator for ConnectedComponentsIterator<'a, T>
where
    T: LabelType,
{
    type Item = AAFramework<T>;

    fn next(&mut self) -> Option<Self::Item> {
        self.computer.next_connected_component()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::io::{AspartixReader, AspartixWriter, InstanceReader};
    use std::io::Cursor;

    impl<'a, T> ConnectedComponentsComputer<'a, T>
    where
        T: LabelType,
    {
        fn connected_component_of(&mut self, arg: &'a Argument<T>) -> AAFramework<T> {
            self.merged_connected_components_of(&[arg])
        }
    }

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
        let mut cc = ConnectedComponentsComputer::new(&af);
        writer
            .write_framework(&cc.connected_component_of(arg), &mut buffer1)
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
    #[should_panic(expected = "this connected component was already computed")]
    fn test_connected_components_of_twice() {
        let instance = r#"
        arg(a0).
        arg(a1).
        att(a0,a1).
        "#;
        let reader = AspartixReader::default();
        let af = reader.read(&mut instance.as_bytes()).unwrap();
        let arg = af.argument_set().get_argument(&"a1".to_string()).unwrap();
        let mut cc = ConnectedComponentsComputer::new(&af);
        cc.connected_component_of(arg);
        cc.connected_component_of(arg);
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
        let components = ConnectedComponentsComputer::iter_connected_components(&af)
            .collect::<Vec<AAFramework<String>>>();
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
        assert_eq!(
            1,
            ConnectedComponentsComputer::iter_connected_components(&af).count()
        );
        af.remove_argument(&"a1".to_string()).unwrap();
        let components_after = ConnectedComponentsComputer::iter_connected_components(&af)
            .collect::<Vec<AAFramework<String>>>();
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
