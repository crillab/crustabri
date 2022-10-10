use crate::{Argument, ArgumentSet, LabelType};
use anyhow::{anyhow, Context, Result};

/// An Abstract Argumentation framework as defined in Dung semantics.
pub struct AAFramework<T>
where
    T: LabelType,
{
    arguments: ArgumentSet<T>,
    attacks: Vec<(usize, usize)>,
    attacks_from: Vec<Vec<usize>>,
    attacks_to: Vec<Vec<usize>>,
}

/// An attack, represented as a couple of two arguments.
///
/// Attacks are built by [`AAFramework`] objects.
pub struct Attack<'a, T>(&'a Argument<T>, &'a Argument<T>)
where
    T: LabelType;

impl<'a, T> Attack<'a, T>
where
    T: LabelType,
{
    /// Returns the attacker.
    ///
    /// Example
    ///
    /// ```
    /// # use crustabri::{Attack, LabelType};
    /// fn describe_attack<T: LabelType>(attack: &Attack<T>) {
    ///     println!("{} attacks {}", attack.attacker(), attack.attacked());
    /// }
    /// ```
    pub fn attacker(&self) -> &'a Argument<T> {
        self.0
    }

    /// Returns the attacked argument.
    ///
    /// Example
    ///
    /// ```
    /// # use crustabri::{Attack, LabelType};
    /// fn describe_attack<T: LabelType>(attack: &Attack<T>) {
    ///     println!("{} attacks {}", attack.attacker(), attack.attacked());
    /// }
    /// ```
    pub fn attacked(&self) -> &'a Argument<T> {
        self.1
    }
}

impl<T> AAFramework<T>
where
    T: LabelType,
{
    /// Builds an AA framework.
    ///
    /// The set of arguments used in the framework must be provided.
    ///
    /// # Arguments
    ///
    /// * `arguments` - the set of arguments
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::{ArgumentSet, AAFramework};
    /// let arguments = ArgumentSet::new(&["a", "b", "c"]);
    /// let framework = AAFramework::new(arguments);
    /// assert_eq!(3, framework.argument_set().len());
    /// assert_eq!(0, framework.iter_attacks().count());
    /// ```
    pub fn new(arguments: ArgumentSet<T>) -> Self {
        let attacks_from = (0..arguments.len()).map(|_| vec![]).collect();
        let attacks_to = (0..arguments.len()).map(|_| vec![]).collect();
        AAFramework {
            arguments,
            attacks: vec![],
            attacks_from,
            attacks_to,
        }
    }

    /// Adds a new attack given the labels of the source and destination arguments.
    ///
    /// If the provided arguments are undefined, an error is returned.
    /// Else, the attack is added.
    ///
    /// If the attack already exists, it is added another time (no checks are made for existence).
    ///
    /// # Arguments
    ///
    /// * `from` - the label of the source arguments (attacker)
    /// * `to` - the label of the destination argument (attacked)
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::{ArgumentSet, AAFramework};
    /// let labels = vec!["a", "b", "c"];
    /// let arguments = ArgumentSet::new(&labels);
    /// let mut framework = AAFramework::new(arguments);
    /// assert_eq!(0, framework.iter_attacks().count());
    /// framework.new_attack(&labels[0], &labels[1]);
    /// assert_eq!(1, framework.iter_attacks().count());
    /// ```
    pub fn new_attack(&mut self, from: &T, to: &T) -> Result<()> {
        let context = || format!("cannot add an attack from {:?} to {:?}", from, to,);
        let attacker_id = self
            .arguments
            .get_argument_index(from)
            .with_context(context)?;
        let attacked_id = self
            .arguments
            .get_argument_index(to)
            .with_context(context)?;
        self.attacks.push((attacker_id, attacked_id));
        self.attacks_from[attacker_id].push(self.attacks.len() - 1);
        self.attacks_to[attacked_id].push(self.attacks.len() - 1);
        Ok(())
    }

    /// Adds a new attack given the IDs of the source and destination arguments.
    ///
    /// If the provided arguments are undefined, an error is returned.
    /// Else, the attack is added.
    ///
    /// If the attack already exists, it is added another time (no checks are made for existence).
    ///
    /// # Arguments
    ///
    /// * `from` - the id of the source arguments (attacker)
    /// * `to` - the id of the destination argument (attacked)
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::{ArgumentSet, AAFramework};
    /// let labels = vec!["a", "b", "c"];
    /// let arguments = ArgumentSet::new(&labels);
    /// let mut framework = AAFramework::new(arguments);
    /// assert_eq!(0, framework.iter_attacks().count());
    /// framework.new_attack_by_ids(0, 1); // "a" attacks "b"
    /// assert_eq!(1, framework.iter_attacks().count());
    /// ```
    pub fn new_attack_by_ids(&mut self, from: usize, to: usize) -> Result<()> {
        let n_arguments = self.arguments.len();
        if from >= n_arguments || to >= n_arguments {
            return Err(anyhow!(
                "cannot add an attack from identifiers {:?} to {:?}; max id is {}",
                from,
                to,
                n_arguments - 1
            ));
        }
        self.attacks.push((from, to));
        Ok(())
    }

    /// Returns the argument set of the framework.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::{ArgumentSet, AAFramework};
    /// let labels = vec!["a", "b", "c"];
    /// let arguments = ArgumentSet::new(&labels);
    /// let framework = AAFramework::new(arguments);
    /// assert_eq!(3, framework.argument_set().len());
    /// ```
    pub fn argument_set(&self) -> &ArgumentSet<T> {
        &self.arguments
    }

    /// Provides an iterator to the attacks.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::{ArgumentSet, AAFramework};
    /// let labels = vec!["a", "b", "c"];
    /// let arguments = ArgumentSet::new(&labels);
    /// let mut framework = AAFramework::new(arguments);
    /// assert_eq!(0, framework.iter_attacks().count());
    /// framework.new_attack_by_ids(0, 1); // "a" attacks "b"
    /// assert_eq!(1, framework.iter_attacks().count());
    /// ```
    pub fn iter_attacks(&self) -> AttacksIter<T> {
        AttacksIter {
            af: self,
            index_iter: Box::new(0..self.attacks.len()),
        }
    }

    /// Provides an iterator to the attacks in which the attacked argument is the one given by the id.
    pub fn iter_attacks_to_id(&self, attacked_id: usize) -> AttacksIter<T> {
        AttacksIter {
            af: self,
            index_iter: Box::new(self.attacks_to[attacked_id].iter().cloned()),
        }
    }

    /// Returns the number of arguments in this framework.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::{ArgumentSet, AAFramework};
    /// let labels = vec!["a", "b", "c"];
    /// let arguments = ArgumentSet::new(&labels);
    /// let mut framework = AAFramework::new(arguments);
    /// assert_eq!(3, framework.n_arguments());
    /// ```
    pub fn n_arguments(&self) -> usize {
        self.argument_set().len()
    }

    /// Returns the number of attacks in this framework.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::{ArgumentSet, AAFramework};
    /// let labels = vec!["a", "b", "c"];
    /// let arguments = ArgumentSet::new(&labels);
    /// let mut framework = AAFramework::new(arguments);
    /// assert_eq!(0, framework.n_attacks());
    /// framework.new_attack_by_ids(0, 1); // "a" attacks "b"
    /// assert_eq!(1, framework.n_attacks());
    /// ```
    pub fn n_attacks(&self) -> usize {
        self.attacks.len()
    }

    /// Computes and return the grounded extension of this argumentation framework.
    pub fn grounded_extension(&self) -> Vec<&Argument<T>> {
        let mut ext = vec![];
        let mut n_processed_args = 0;
        let mut defeated_args = vec![false; self.n_arguments()];
        let mut attacked_by = self
            .attacks_to
            .iter()
            .enumerate()
            .map(|(i, v)| {
                let n = v.len();
                if n == 0 {
                    ext.push(self.argument_set().get_argument_by_id(i))
                }
                n
            })
            .collect::<Vec<usize>>();
        while n_processed_args < ext.len() {
            let id = ext[n_processed_args].id();
            self.attacks_from[id].iter().for_each(|defeating_att| {
                let (_, defeated) = self.attacks[*defeating_att];
                if !defeated_args[defeated] {
                    defeated_args[defeated] = true;
                    self.attacks_from[defeated].iter().for_each(|att| {
                        let (_, attacked) = self.attacks[*att];
                        if attacked_by[attacked] == 1 {
                            ext.push(self.argument_set().get_argument_by_id(attacked))
                        } else {
                            attacked_by[attacked] -= 1;
                        }
                    })
                }
            });
            n_processed_args += 1;
        }
        ext
    }
}

pub struct AttacksIter<'a, T>
where
    T: LabelType,
{
    af: &'a AAFramework<T>,
    index_iter: Box<dyn Iterator<Item = usize> + 'a>,
}

impl<'a, T> Iterator for AttacksIter<'a, T>
where
    T: LabelType + 'a,
{
    type Item = Attack<'a, T>;

    fn next(&mut self) -> Option<Self::Item> {
        self.index_iter.next().map(|i| {
            let att = &self.af.attacks[i];
            Attack(
                self.af.arguments.get_argument_by_id(att.0),
                self.af.arguments.get_argument_by_id(att.1),
            )
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_n_args() {
        let arg_labels = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        let args = ArgumentSet::new(&arg_labels);
        let af = AAFramework::new(args);
        assert_eq!(3, af.n_arguments());
    }

    #[test]
    fn test_new_attack_ok() {
        let arg_labels = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        let args = ArgumentSet::new(&arg_labels);
        let mut attacks = AAFramework::new(args);
        assert_eq!(0, attacks.n_attacks());
        attacks.new_attack(&arg_labels[0], &arg_labels[0]).unwrap();
        assert_eq!(1, attacks.n_attacks());
        assert_eq!((0, 0), attacks.attacks[0]);
    }

    #[test]
    fn test_new_attack_unknown_label_1() {
        let arg_labels = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        let args = ArgumentSet::new(&arg_labels);
        let mut attacks = AAFramework::new(args);
        attacks
            .new_attack(&"d".to_string(), &arg_labels[0])
            .unwrap_err();
    }

    #[test]
    fn test_new_attack_unknown_label_2() {
        let arg_labels = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        let args = ArgumentSet::new(&arg_labels);
        let mut attacks = AAFramework::new(args);
        attacks
            .new_attack(&arg_labels[0], &"d".to_string())
            .unwrap_err();
    }

    #[test]
    fn test_new_attack_by_ids_ok() {
        let arg_labels = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        let args = ArgumentSet::new(&arg_labels);
        let mut attacks = AAFramework::new(args);
        assert_eq!(0, attacks.n_attacks());
        attacks.new_attack_by_ids(0, 0).unwrap();
        assert_eq!(1, attacks.n_attacks());
        assert_eq!((0, 0), attacks.attacks[0]);
    }

    #[test]
    fn test_new_attack_by_ids_unknown_id_1() {
        let arg_labels = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        let args = ArgumentSet::new(&arg_labels);
        let mut attacks = AAFramework::new(args);
        attacks.new_attack_by_ids(3, 0).unwrap_err();
    }

    #[test]
    fn test_new_attack_by_ids_unknown_id_2() {
        let arg_labels = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        let args = ArgumentSet::new(&arg_labels);
        let mut attacks = AAFramework::new(args);
        attacks.new_attack_by_ids(0, 3).unwrap_err();
    }

    #[test]
    fn test_grounded_extension_1() {
        let arg_labels = vec!["a", "b", "c", "d", "e", "f"];
        let args = ArgumentSet::new(&arg_labels);
        let mut af = AAFramework::new(args);
        af.new_attack(&"a", &"b").unwrap();
        af.new_attack(&"b", &"c").unwrap();
        af.new_attack(&"b", &"d").unwrap();
        af.new_attack(&"c", &"e").unwrap();
        af.new_attack(&"d", &"e").unwrap();
        af.new_attack(&"e", &"f").unwrap();
        let mut grounded = af
            .grounded_extension()
            .iter()
            .map(|a| *a.label())
            .collect::<Vec<&str>>();
        grounded.sort_unstable();
        assert_eq!(vec!["a", "c", "d", "f"], grounded)
    }

    #[test]
    fn test_grounded_extension_2() {
        let arg_labels = vec!["x", "a", "b", "c", "d", "e", "f"];
        let args = ArgumentSet::new(&arg_labels);
        let mut af = AAFramework::new(args);
        af.new_attack(&"x", &"a").unwrap();
        af.new_attack(&"a", &"b").unwrap();
        af.new_attack(&"b", &"c").unwrap();
        af.new_attack(&"b", &"d").unwrap();
        af.new_attack(&"c", &"e").unwrap();
        af.new_attack(&"d", &"e").unwrap();
        af.new_attack(&"e", &"f").unwrap();
        let mut grounded = af
            .grounded_extension()
            .iter()
            .map(|a| *a.label())
            .collect::<Vec<&str>>();
        grounded.sort_unstable();
        assert_eq!(vec!["b", "e", "x"], grounded)
    }
}
