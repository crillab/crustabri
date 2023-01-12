use super::{Argument, ArgumentSet};
use crate::utils::{self, LabelType};
use anyhow::{anyhow, Context, Result};

/// An Abstract Argumentation framework as defined in Dung semantics.
///
/// [AAFramework] objects hold both an argument set and the attacks between these arguments.
/// They maintain the coherence between the arguments and the attacks:
/// if an argument is removed, then all the attacks involving it are also removed.
///
/// While the majority of the functions defined in this objects are related to the addition and deletion of arguments and attacks,
/// some computation methods are defined here. See e.g. the [grounded_extension](Self::grounded_extension) function.
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
///
/// Since attacks refer to [Argument] objects which themselves refer to [AAFramework] objects, it is impossible to remove an argument if [Attack] objects are handled out of their framework.
/// This implies that the arguments n the attack always exists (i.e. you do not have to check if the two arguments still exist).
///
/// # Example
///
/// ```
/// # use crustabri::aa::AAFramework;
/// # use crustabri::utils::LabelType;
/// fn print_af_attacks<T>(af: &AAFramework<T>) where T: LabelType {
///     af
///         .iter_attacks()
///         .for_each(|att| println!("{} attacks {}", att.attacker(), att.attacked()));
/// }
/// ```
pub struct Attack<'a, T>(&'a Argument<T>, &'a Argument<T>)
where
    T: LabelType;

impl<'a, T> Attack<'a, T>
where
    T: LabelType,
{
    /// Returns the attacker.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::aa::{Attack};
    /// # use crustabri::utils::LabelType;
    /// fn describe_attack<T: LabelType>(attack: &Attack<T>) {
    ///     println!("{} attacks {}", attack.attacker(), attack.attacked());
    /// }
    /// ```
    pub fn attacker(&self) -> &'a Argument<T> {
        self.0
    }

    /// Returns the attacked argument.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::aa::{Attack};
    /// # use crustabri::utils::LabelType;
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
    /// Builds an AA framework with its initial argument set.
    ///
    /// Although a set of arguments is provided, it may change over the time.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::aa::{ArgumentSet, AAFramework};
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

    /// Adds a new argument to this argumentation framework given its label.
    ///
    /// If such an argument already exists, the AF is left unchanged.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::aa::{ArgumentSet, AAFramework};
    /// let arg_labels = vec!["a".to_string(), "b".to_string(), "c".to_string()];
    /// let args = ArgumentSet::new_with_labels(&arg_labels);
    /// let mut af = AAFramework::new_with_argument_set(args);
    /// af.new_argument("d".to_string());
    /// assert_eq!(4, af.n_arguments());
    /// af.new_argument("d".to_string());
    /// assert_eq!(4, af.n_arguments());
    /// ```
    pub fn new_argument(&mut self, label: T) {
        let old_len = self.arguments.len();
        self.arguments.new_argument(label);
        if self.arguments.len() > old_len {
            self.attacks_from.push(Vec::new());
            self.attacks_to.push(Vec::new());
        }
    }

    /// Removes an argument from this argumentation framework and all the related attacks.
    ///
    /// The argument id will not be attributed to new arguments.
    /// See [Argument] for more information on argument identifiers.
    ///
    /// If no argument in the AF has the same label as provided, this function returns an error.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::aa::{ArgumentSet, AAFramework};
    /// let arg_labels = vec!["a".to_string(), "b".to_string(), "c".to_string()];
    /// let args = ArgumentSet::new_with_labels(&arg_labels);
    /// let mut af = AAFramework::new_with_argument_set(args);
    /// assert_eq!(0, af.n_attacks());
    /// // adding all the possible attacks
    /// for i in 0..3 {
    ///     for j in 0..3 {
    ///         af.new_attack(&arg_labels[i], &arg_labels[j]).unwrap();
    ///     }
    /// }
    /// assert_eq!(9, af.n_attacks());
    /// // removing argument "a"
    /// assert!(af.remove_argument(&arg_labels[0]).is_ok());
    /// assert!(af.remove_argument(&arg_labels[0]).is_err());
    /// assert_eq!(4, af.n_attacks());
    /// assert!(af
    ///     .iter_attacks()
    ///     .all(|att| att.attacker().label() != "a" && att.attacked().label() != "a"));
    /// ```
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
        self.attacks_from[removed_id] = Vec::new();
        self.attacks_to[removed_id] = Vec::new();
        Ok(())
    }

    /// Adds a new attack given the labels of the source and destination arguments.
    ///
    /// If the provided arguments are undefined, an error is returned.
    /// Else, the attack is added.
    ///
    /// If the attack already exists, no new attack is added and no error is returned.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::aa::{ArgumentSet, AAFramework};
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
            .get_argument(from)
            .with_context(context)?
            .id();
        let attacked_id = self.arguments.get_argument(to).with_context(context)?.id();
        if !self.attacks_from[attacker_id]
            .iter()
            .any(|id| self.attacks[*id] == Some((attacker_id, attacked_id)))
        {
            self.attacks.push(Some((attacker_id, attacked_id)));
            self.attacks_from[attacker_id].push(self.attacks.len() - 1);
            self.attacks_to[attacked_id].push(self.attacks.len() - 1);
        }
        Ok(())
    }

    /// Removes an attack given the labels of the source and destination arguments.
    ///
    /// If the provided attack or one of its arguments does not belong to this framework, an error is returned.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::aa::{ArgumentSet, AAFramework};
    /// let labels = vec!["a", "b", "c"];
    /// let arguments = ArgumentSet::new_with_labels(&labels);
    /// let mut framework = AAFramework::new_with_argument_set(arguments);
    /// assert_eq!(0, framework.iter_attacks().count());
    /// framework.new_attack(&labels[0], &labels[1]);
    /// assert_eq!(1, framework.iter_attacks().count());
    /// assert!(framework.remove_attack(&labels[0], &labels[1]).is_ok());
    /// assert!(framework.remove_attack(&labels[0], &labels[1]).is_err());
    pub fn remove_attack(&mut self, from: &T, to: &T) -> Result<()> {
        let context = || format!("while removing an attack from {:?} to {:?}", from, to);
        let attacker_id = self
            .arguments
            .get_argument(from)
            .with_context(context)?
            .id();
        let attacked_id = self.arguments.get_argument(to).with_context(context)?.id();
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
                self.attacks_from[attacker_id].swap_remove(pos_in_attacks_from);
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
    pub(crate) fn new_attack_by_ids(&mut self, from: usize, to: usize) -> Result<()> {
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
    /// # use crustabri::aa::{ArgumentSet, AAFramework};
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
    /// # use crustabri::aa::{ArgumentSet, AAFramework};
    /// let labels = vec!["a", "b", "c"];
    /// let arguments = ArgumentSet::new_with_labels(&labels);
    /// let mut framework = AAFramework::new_with_argument_set(arguments);
    /// assert_eq!(0, framework.iter_attacks().count());
    /// framework.new_attack(&"a", &"b");
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
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::aa::{ArgumentSet, AAFramework};
    /// let labels = vec!["a", "b", "c"];
    /// let arguments = ArgumentSet::new_with_labels(&labels);
    /// let mut af = AAFramework::new_with_argument_set(arguments);
    /// af.new_attack(&"a", &"b");
    /// assert_eq!(1, af.iter_attacks_from(af.argument_set().get_argument(&"a").unwrap()).count());
    /// assert_eq!(0, af.iter_attacks_from(af.argument_set().get_argument(&"b").unwrap()).count());
    pub fn iter_attacks_from(&self, arg: &Argument<T>) -> impl Iterator<Item = Attack<'_, T>> + '_ {
        self.iter_attacks_from_id(arg.id())
    }

    pub(crate) fn iter_attacks_from_id(
        &self,
        arg_id: usize,
    ) -> impl Iterator<Item = Attack<'_, T>> + '_ {
        self.attacks_from[arg_id]
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
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::aa::{ArgumentSet, AAFramework};
    /// let labels = vec!["a", "b", "c"];
    /// let arguments = ArgumentSet::new_with_labels(&labels);
    /// let mut af = AAFramework::new_with_argument_set(arguments);
    /// af.new_attack(&"a", &"b");
    /// assert_eq!(0, af.iter_attacks_to(af.argument_set().get_argument(&"a").unwrap()).count());
    /// assert_eq!(1, af.iter_attacks_to(af.argument_set().get_argument(&"b").unwrap()).count());
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

    /// Returns the number of arguments in this framework.
    ///
    /// See [ArgumentSet::len] for more information.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::aa::{ArgumentSet, AAFramework};
    /// let labels = vec!["a", "b", "c"];
    /// let arguments = ArgumentSet::new_with_labels(&labels);
    /// let mut framework = AAFramework::new_with_argument_set(arguments);
    /// assert_eq!(3, framework.n_arguments());
    /// ```
    pub fn n_arguments(&self) -> usize {
        self.argument_set().len()
    }

    /// Returns the maximal argument id given so far, or `None` if no argument has been added yet.
    ///
    /// See [ArgumentSet::max_id] for more information.
    pub fn max_argument_id(&self) -> Option<usize> {
        self.argument_set().max_id()
    }

    /// Returns the number of attacks in this framework.
    ///
    /// Removed attacks do not count.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::aa::{ArgumentSet, AAFramework};
    /// let labels = vec!["a", "b", "c"];
    /// let arguments = ArgumentSet::new_with_labels(&labels);
    /// let mut framework = AAFramework::new_with_argument_set(arguments);
    /// assert_eq!(0, framework.n_attacks());
    /// framework.new_attack(&"a", &"b");
    /// assert_eq!(1, framework.n_attacks());
    /// framework.remove_attack(&"a", &"b");
    /// assert_eq!(0, framework.n_attacks());
    /// ```
    pub fn n_attacks(&self) -> usize {
        self.attacks.len() - self.n_removed_attacks
    }

    /// Computes the grounded extension of the AF.
    ///
    /// The grounded extension is the minimal complete extension (see [CompleteSemanticsSolver](crate::solvers::CompleteSemanticsSolver) for more information).
    /// It is computed in time polynomial in the size of the framework.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::aa::{ArgumentSet, AAFramework};
    /// let arg_labels = vec!["a", "b", "c", "d", "e", "f"];
    /// let args = ArgumentSet::new_with_labels(&arg_labels);
    /// let mut af = AAFramework::new_with_argument_set(args);
    /// af.new_attack(&"a", &"b").unwrap();
    /// af.new_attack(&"b", &"c").unwrap();
    /// af.new_attack(&"b", &"d").unwrap();
    /// af.new_attack(&"c", &"e").unwrap();
    /// af.new_attack(&"d", &"e").unwrap();
    /// af.new_attack(&"e", &"f").unwrap();
    /// let mut grounded_labels = af.grounded_extension()
    ///     .iter()
    ///     .map(|a| *a.label())
    ///     .collect::<Vec<&str>>();
    /// grounded_labels.sort_unstable();
    /// assert_eq!(vec!["a", "c", "d", "f"], grounded_labels)
    /// ```
    pub fn grounded_extension(&self) -> Vec<&Argument<T>> {
        utils::grounded_extension(self)
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

    #[test]
    fn test_new_attack_already_exists() {
        let arg_labels = vec!["a"];
        let args = ArgumentSet::new_with_labels(&arg_labels);
        let mut af = AAFramework::new_with_argument_set(args);
        assert_eq!(0, af.n_attacks());
        af.new_attack(&"a", &"a").unwrap();
        assert_eq!(1, af.n_attacks());
        af.new_attack(&"a", &"a").unwrap();
        assert_eq!(1, af.n_attacks());
    }

    #[test]
    fn test_add_attack_on_new_arg_after_att_removal() {
        let arg_labels = vec!["a"];
        let args = ArgumentSet::new_with_labels(&arg_labels);
        let mut af = AAFramework::new_with_argument_set(args);
        af.new_attack(&"a", &"a").unwrap();
        af.remove_attack(&"a", &"a").unwrap();
        af.new_argument("b");
        af.new_attack(&"b", &"b").unwrap();
        assert_eq!(
            1,
            af.iter_attacks_from(af.argument_set().get_argument(&"b").unwrap())
                .count()
        )
    }
}
