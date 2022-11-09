use crate::{Argument, ArgumentSet, LabelType};
use anyhow::{anyhow, Context, Result};

/// An Abstract Argumentation framework as defined in Dung semantics.
#[derive(Default)]
pub struct AAFramework<T>
where
    T: LabelType,
{
    arguments: ArgumentSet<T>,
    attacks: Vec<Option<(usize, usize)>>,
    attacks_from: Vec<Vec<usize>>,
    attacks_to: Vec<Vec<usize>>,
    n_removed_attacks: usize,
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
    /// The set of arguments used in the framework is provided.
    ///
    /// # Arguments
    ///
    /// * `arguments` - the set of arguments
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::{ArgumentSet, AAFramework};
    /// let arguments = ArgumentSet::new_with_labels(&["a", "b", "c"]);
    /// let framework = AAFramework::new_with_argument_set(arguments);
    /// assert_eq!(3, framework.argument_set().len());
    /// assert_eq!(0, framework.iter_attacks().count());
    /// ```
    pub fn new_with_argument_set(arguments: ArgumentSet<T>) -> Self {
        let attacks_from = (0..arguments.len()).map(|_| vec![]).collect();
        let attacks_to = (0..arguments.len()).map(|_| vec![]).collect();
        AAFramework {
            arguments,
            attacks: vec![],
            attacks_from,
            attacks_to,
            n_removed_attacks: 0,
        }
    }

    /// Adds a new argument to this argumentation framework.
    pub fn new_argument(&mut self, label: T) {
        let old_len = self.arguments.len();
        self.arguments.new_argument(label);
        if self.arguments.len() > old_len {
            self.attacks_from.push(Vec::new());
            self.attacks_to.push(Vec::new());
        }
    }

    /// Removes an argument from this argumentation framework.
    ///
    /// The argument id will not be attributed to new arguments.
    pub fn remove_argument(&mut self, label: &T) -> Result<()> {
        let removed = self.arguments.remove_argument(label)?;
        let removed_id = removed.id();
        let try_remove_attack = |i: &usize| {
            if self.attacks[*i].take().is_some() {
                self.n_removed_attacks += 1;
            }
        };
        self.attacks_from[removed_id]
            .iter()
            .chain(self.attacks_to[removed_id].iter())
            .for_each(try_remove_attack);
        self.attacks_from[removed_id].clear();
        self.attacks_to[removed_id].clear();
        Ok(())
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
    /// let arguments = ArgumentSet::new_with_labels(&labels);
    /// let mut framework = AAFramework::new_with_argument_set(arguments);
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
        self.attacks.push(Some((attacker_id, attacked_id)));
        self.attacks_from[attacker_id].push(self.attacks.len() - 1);
        self.attacks_to[attacked_id].push(self.attacks.len() - 1);
        Ok(())
    }

    /// Removes an attack.
    ///
    /// If the provided attack or one of its arguments does not belong to this framework, an error is returned.
    pub fn remove_attack(&mut self, from: &T, to: &T) -> Result<()> {
        let context = || format!("while removing an attack from {:?} to {:?}", from, to);
        let attacker_id = self
            .arguments
            .get_argument_index(from)
            .with_context(context)?;
        let attacked_id = self
            .arguments
            .get_argument_index(to)
            .with_context(context)?;
        let attacks_from = &self.attacks_from[attacker_id];
        match attacks_from
            .iter()
            .position(|i| self.attacks[*i] == Some((attacker_id, attacked_id)))
        {
            Some(pos_in_attacks_from) => {
                let attack_id = attacks_from[pos_in_attacks_from];
                self.attacks[attack_id] = None;
                let pos_in_attacks_to = self.attacks_to[attacked_id]
                    .iter()
                    .position(|att_id| *att_id == attack_id)
                    .unwrap();
                self.attacks_to[attacked_id].swap_remove(pos_in_attacks_to);
                self.attacks_from.swap_remove(pos_in_attacks_from);
                self.n_removed_attacks += 1;
                Ok(())
            }
            None => Err(anyhow!("no such attack")),
        }
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
    /// let arguments = ArgumentSet::new_with_labels(&labels);
    /// let mut framework = AAFramework::new_with_argument_set(arguments);
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
        self.attacks.push(Some((from, to)));
        self.attacks_from[from].push(self.attacks.len() - 1);
        self.attacks_to[to].push(self.attacks.len() - 1);
        Ok(())
    }

    /// Returns the argument set of the framework.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::{ArgumentSet, AAFramework};
    /// let labels = vec!["a", "b", "c"];
    /// let arguments = ArgumentSet::new_with_labels(&labels);
    /// let framework = AAFramework::new_with_argument_set(arguments);
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
    /// let arguments = ArgumentSet::new_with_labels(&labels);
    /// let mut framework = AAFramework::new_with_argument_set(arguments);
    /// assert_eq!(0, framework.iter_attacks().count());
    /// framework.new_attack_by_ids(0, 1); // "a" attacks "b"
    /// assert_eq!(1, framework.iter_attacks().count());
    /// ```
    pub fn iter_attacks(&self) -> impl Iterator<Item = Attack<'_, T>> + '_ {
        self.attacks
            .iter()
            .filter_map(|o| o.as_ref())
            .map(|(a, b)| {
                Attack(
                    self.arguments.get_argument_by_id(*a),
                    self.arguments.get_argument_by_id(*b),
                )
            })
    }

    /// Provides an iterator to the attacks that have the given argument as attacker.
    pub fn iter_attacks_from(&self, arg: &Argument<T>) -> impl Iterator<Item = Attack<'_, T>> + '_ {
        self.attacks_from[arg.id()]
            .iter()
            .map(|i| &self.attacks[*i])
            .filter_map(|o| o.as_ref())
            .map(|(a, b)| {
                Attack(
                    self.arguments.get_argument_by_id(*a),
                    self.arguments.get_argument_by_id(*b),
                )
            })
    }

    /// Provides an iterator to the attacks that have the given argument as attacked.
    pub fn iter_attacks_to(&self, arg: &Argument<T>) -> impl Iterator<Item = Attack<'_, T>> + '_ {
        self.attacks_to[arg.id()]
            .iter()
            .map(|i| &self.attacks[*i])
            .filter_map(|o| o.as_ref())
            .map(|(a, b)| {
                Attack(
                    self.arguments.get_argument_by_id(*a),
                    self.arguments.get_argument_by_id(*b),
                )
            })
    }

    /// Provides an iterator to the attacks in which the attacked argument is the one given by the id.
    pub fn iter_attacks_to_id(
        &self,
        attacked_id: usize,
    ) -> impl Iterator<Item = Attack<'_, T>> + '_ {
        self.attacks_to[attacked_id]
            .iter()
            .map(|i| &self.attacks[*i])
            .filter_map(|o| o.as_ref())
            .map(|(a, b)| {
                Attack(
                    self.arguments.get_argument_by_id(*a),
                    self.arguments.get_argument_by_id(*b),
                )
            })
    }

    /// Returns the number of arguments in this framework.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::{ArgumentSet, AAFramework};
    /// let labels = vec!["a", "b", "c"];
    /// let arguments = ArgumentSet::new_with_labels(&labels);
    /// let mut framework = AAFramework::new_with_argument_set(arguments);
    /// assert_eq!(3, framework.n_arguments());
    /// ```
    pub fn n_arguments(&self) -> usize {
        self.argument_set().len()
    }

    /// Returns the maximal argument id given so far.
    ///
    /// This id may refer to a removed argument.
    pub fn max_argument_id(&self) -> usize {
        self.argument_set().max_id()
    }

    /// Returns the number of attacks in this framework.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::{ArgumentSet, AAFramework};
    /// let labels = vec!["a", "b", "c"];
    /// let arguments = ArgumentSet::new_with_labels(&labels);
    /// let mut framework = AAFramework::new_with_argument_set(arguments);
    /// assert_eq!(0, framework.n_attacks());
    /// framework.new_attack_by_ids(0, 1); // "a" attacks "b"
    /// assert_eq!(1, framework.n_attacks());
    /// ```
    pub fn n_attacks(&self) -> usize {
        self.attacks.len() - self.n_removed_attacks
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_n_args() {
        let arg_labels = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        let args = ArgumentSet::new_with_labels(&arg_labels);
        let af = AAFramework::new_with_argument_set(args);
        assert_eq!(3, af.n_arguments());
    }

    #[test]
    fn test_new_attack_ok() {
        let arg_labels = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        let args = ArgumentSet::new_with_labels(&arg_labels);
        let mut attacks = AAFramework::new_with_argument_set(args);
        assert_eq!(0, attacks.n_attacks());
        attacks.new_attack(&arg_labels[0], &arg_labels[0]).unwrap();
        assert_eq!(1, attacks.n_attacks());
        assert_eq!((0, 0), attacks.attacks[0].unwrap());
    }

    #[test]
    fn test_new_attack_unknown_label_1() {
        let arg_labels = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        let args = ArgumentSet::new_with_labels(&arg_labels);
        let mut attacks = AAFramework::new_with_argument_set(args);
        attacks
            .new_attack(&"d".to_string(), &arg_labels[0])
            .unwrap_err();
    }

    #[test]
    fn test_new_attack_unknown_label_2() {
        let arg_labels = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        let args = ArgumentSet::new_with_labels(&arg_labels);
        let mut attacks = AAFramework::new_with_argument_set(args);
        attacks
            .new_attack(&arg_labels[0], &"d".to_string())
            .unwrap_err();
    }

    #[test]
    fn test_new_attack_by_ids_ok() {
        let arg_labels = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        let args = ArgumentSet::new_with_labels(&arg_labels);
        let mut attacks = AAFramework::new_with_argument_set(args);
        assert_eq!(0, attacks.n_attacks());
        attacks.new_attack_by_ids(0, 0).unwrap();
        assert_eq!(1, attacks.n_attacks());
        assert_eq!((0, 0), attacks.attacks[0].unwrap());
    }

    #[test]
    fn test_new_attack_by_ids_unknown_id_1() {
        let arg_labels = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        let args = ArgumentSet::new_with_labels(&arg_labels);
        let mut attacks = AAFramework::new_with_argument_set(args);
        attacks.new_attack_by_ids(3, 0).unwrap_err();
    }

    #[test]
    fn test_new_attack_by_ids_unknown_id_2() {
        let arg_labels = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        let args = ArgumentSet::new_with_labels(&arg_labels);
        let mut attacks = AAFramework::new_with_argument_set(args);
        attacks.new_attack_by_ids(0, 3).unwrap_err();
    }

    #[test]
    fn test_new_argument() {
        let arg_labels = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        let args = ArgumentSet::new_with_labels(&arg_labels);
        let mut af = AAFramework::new_with_argument_set(args);
        af.new_argument("d".to_string());
        assert_eq!(4, af.n_arguments());
        af.new_argument("d".to_string());
        assert_eq!(4, af.n_arguments());
    }

    #[test]
    fn test_remove_attack() {
        let arg_labels = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        let args = ArgumentSet::new_with_labels(&arg_labels);
        let mut af = AAFramework::new_with_argument_set(args);
        assert_eq!(0, af.n_attacks());
        for i in 0..3 {
            for j in 0..3 {
                af.new_attack(&arg_labels[i], &arg_labels[j]).unwrap();
            }
        }
        assert_eq!(9, af.n_attacks());
        assert!(af.remove_attack(&arg_labels[0], &arg_labels[0]).is_ok());
        assert!(af.remove_attack(&arg_labels[0], &arg_labels[0]).is_err());
        assert_eq!(8, af.n_attacks());
        assert!(af
            .iter_attacks()
            .all(|att| att.attacker().label() != "a" || att.attacked().label() != "a"));
    }

    #[test]
    fn test_remove_argument() {
        let arg_labels = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        let args = ArgumentSet::new_with_labels(&arg_labels);
        let mut af = AAFramework::new_with_argument_set(args);
        assert_eq!(0, af.n_attacks());
        for i in 0..3 {
            for j in 0..3 {
                af.new_attack(&arg_labels[i], &arg_labels[j]).unwrap();
            }
        }
        assert_eq!(9, af.n_attacks());
        assert!(af.remove_argument(&arg_labels[0]).is_ok());
        assert!(af.remove_argument(&arg_labels[0]).is_err());
        assert_eq!(4, af.n_attacks());
        assert!(af
            .iter_attacks()
            .all(|att| att.attacker().label() != "a" && att.attacked().label() != "a"));
    }
}
