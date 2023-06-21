use super::{atom_support_computer::AtomSupport, ABAFramework, Atom};
use crate::{
    aa::{AAFramework, Argument, ArgumentSet},
    utils::{Label, LabelType},
};
use std::{fmt::Display, rc::Rc};

/// An ABA framework instantiation to an AA framework.
///
/// This objects allows the translation from flat ABA frameworks to Abstract frameworks in order to solver them using algorithms defined for [AAFramework] objects.
/// [AAFramework] extensions can also be mapped back to their related set of assumptions in order to answer queries on [ABAFramework] objects.
///
/// # Example
///
/// ```
/// # use crustabri::utils::LabelType;
/// # use crustabri::aba::{ABAFramework, ABAFrameworkInstantiation, Atom};
/// # use crustabri::solvers::{CredulousAcceptanceComputer, SingleExtensionComputer, StableSemanticsSolver};
/// fn compute_stable_extension_in_term_of_assumptions<T>(aba: &ABAFramework<T>)
/// where T: LabelType
/// {
///     let instantiation = ABAFrameworkInstantiation::instantiate(aba);
///     let mut extension_computer = StableSemanticsSolver::new(instantiation.instantiated());
///     if let Some(ext) = extension_computer.compute_one_extension() {
///         let assumptions = instantiation.instantiated_extension_to_aba_assumptions(&ext);
///         println!("ABA admits a stable extensions: {:?}", assumptions);
///     } else {
///         println!("ABA admits no stable extensions");
///     }
/// }
///
/// fn check_stable_assumption_cred_acceptance<T>(aba: &ABAFramework<T>, assumption: &Atom<T>)
/// where T: LabelType
/// {
///     let instantiation = ABAFrameworkInstantiation::instantiate(aba);
///     let mut acceptance_checker = StableSemanticsSolver::new(instantiation.instantiated());
///     let assumption_arg = instantiation.aba_assumption_to_instantiated_arg(assumption);
///     if acceptance_checker.is_credulously_accepted(assumption_arg.label()) {
///         println!("the argument is credulously accepted");
///     } else {
///         println!("the argument is not credulously accepted");
///     }
/// }
/// ```
pub struct ABAFrameworkInstantiation<'a, T>
where
    T: LabelType,
{
    aba_framework: &'a ABAFramework<T>,
    aa_framework: AAFramework<InstantiationLabel<'a, T>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct InstantiationLabel<'a, T>
where
    T: LabelType,
{
    deduction: Rc<Deduction<'a, T>>,
}

impl<T> InstantiationLabel<'_, T>
where
    T: LabelType,
{
    pub fn claim(&self) -> &Label<T> {
        self.deduction.claim
    }
}

impl<'a, T> Display for InstantiationLabel<'a, T>
where
    T: LabelType,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{")?;
        if !self.deduction.support.is_empty() {
            write!(f, "{}", self.deduction.support[0].label())?;
            for s in &self.deduction.support[1..] {
                write!(f, ", {}", s.label())?
            }
        }
        write!(f, "}} ⊢ {}", self.deduction.claim.label())
    }
}

impl<'a, T> ABAFrameworkInstantiation<'a, T>
where
    T: LabelType,
{
    /// Computes an instantiation of the ABA framework.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::utils::LabelType;
    /// # use crustabri::aba::{ABAFrameworkInstantiation, ABAFramework};
    /// fn instantiation_data<T>(aba: &ABAFramework<T>)
    /// where T: LabelType
    /// {
    ///     let instantiation = ABAFrameworkInstantiation::instantiate(aba);
    ///     println!(
    ///         "instantiated AA framework has {} arguments and {} attacks",
    ///         instantiation.instantiated().n_arguments(),
    ///         instantiation.instantiated().n_attacks(),
    ///     )
    /// }
    /// ```
    pub fn instantiate(aba_framework: &'a ABAFramework<T>) -> Self {
        let deductions = build_deductions(aba_framework);
        let mut aa_framework = AAFramework::new_with_argument_set(ArgumentSet::new_with_labels(
            &deductions
                .data
                .iter()
                .map(|d| InstantiationLabel {
                    deduction: Rc::clone(d),
                })
                .collect::<Vec<InstantiationLabel<T>>>(),
        ));
        add_attacks(&mut aa_framework, aba_framework, &deductions);
        ABAFrameworkInstantiation {
            aba_framework,
            aa_framework,
        }
    }

    /// Returns a reference to the instantiated abstract framework.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::utils::LabelType;
    /// # use crustabri::aba::{ABAFrameworkInstantiation, ABAFramework};
    /// fn instantiation_data<T>(aba: &ABAFramework<T>)
    /// where T: LabelType
    /// {
    ///     let instantiation = ABAFrameworkInstantiation::instantiate(aba);
    ///     println!(
    ///         "instantiated AA framework has {} arguments and {} attacks",
    ///         instantiation.instantiated().n_arguments(),
    ///         instantiation.instantiated().n_attacks(),
    ///     )
    /// }
    /// ```
    pub fn instantiated(&self) -> &AAFramework<InstantiationLabel<'a, T>> {
        &self.aa_framework
    }

    /// Returns the set of ABA assumptions involved in the provided AA extension.
    ///
    /// This functions allows to translate back an extension of the instantiated AA framework into a set of ABA assumptions.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::utils::LabelType;
    /// # use crustabri::aba::{ABAFramework, ABAFrameworkInstantiation};
    /// # use crustabri::solvers::{SingleExtensionComputer, StableSemanticsSolver};
    /// fn compute_stable_extension_in_term_of_assumptions<T>(aba: &ABAFramework<T>)
    /// where T: LabelType
    /// {
    ///     let instantiation = ABAFrameworkInstantiation::instantiate(aba);
    ///     let mut extension_computer = StableSemanticsSolver::new(instantiation.instantiated());
    ///     if let Some(ext) = extension_computer.compute_one_extension() {
    ///         let assumptions = instantiation.instantiated_extension_to_aba_assumptions(&ext);
    ///         println!("ABA admits a stable extensions: {:?}", assumptions);
    ///     } else {
    ///         println!("ABA admits no stable extensions");
    ///     }
    /// }
    /// ```
    pub fn instantiated_extension_to_aba_assumptions(
        &self,
        extension: &'a [&Argument<InstantiationLabel<T>>],
    ) -> Vec<&'a Atom<T>> {
        let mut in_result = vec![false; self.aba_framework.language().len()];
        extension
            .iter()
            .filter_map(|arg| {
                let claim = arg.label().deduction.claim;
                if self.aba_framework.is_assumption(claim.label()).unwrap() {
                    if in_result[claim.id()] {
                        None
                    } else {
                        in_result[claim.id()] = true;
                        Some(claim)
                    }
                } else {
                    None
                }
            })
            .collect()
    }

    /// Returns the argument of the instantiated AA framework corresponding to the given ABA assumption.
    ///
    /// This function may be useful to compute acceptance computations on the AA framework to determine acceptance of an assumption in the ABA framework.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::utils::LabelType;
    /// # use crustabri::aba::{ABAFramework, ABAFrameworkInstantiation, Atom};
    /// # use crustabri::solvers::{CredulousAcceptanceComputer, StableSemanticsSolver};
    /// fn check_stable_assumption_cred_acceptance<T>(aba: &ABAFramework<T>, assumption: &Atom<T>)
    /// where T: LabelType
    /// {
    ///     let instantiation = ABAFrameworkInstantiation::instantiate(aba);
    ///     let mut acceptance_checker = StableSemanticsSolver::new(instantiation.instantiated());
    ///     let assumption_arg = instantiation.aba_assumption_to_instantiated_arg(assumption);
    ///     if acceptance_checker.is_credulously_accepted(assumption_arg.label()) {
    ///         println!("the argument is credulously accepted");
    ///     } else {
    ///         println!("the argument is not credulously accepted");
    ///     }
    /// }
    /// ```
    pub fn aba_assumption_to_instantiated_arg(
        &self,
        assumption: &'a Atom<T>,
    ) -> &'a Argument<InstantiationLabel<T>> {
        self.aa_framework
            .argument_set()
            .get_argument(&InstantiationLabel {
                deduction: Rc::new(Deduction {
                    claim: assumption,
                    support: vec![assumption],
                }),
            })
            .unwrap()
    }
}

// A deduction in the sense of ABA, eg. a rule where assumptions imply an atom.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
struct Deduction<'a, T>
where
    T: LabelType,
{
    claim: &'a Atom<T>,
    support: Vec<&'a Atom<T>>,
}

struct LayeredDeductionVec<'a, T>
where
    T: LabelType,
{
    data: Vec<Rc<Deduction<'a, T>>>,
    layer_indices: Vec<usize>,
}

impl<'a, T> LayeredDeductionVec<'a, T>
where
    T: LabelType,
{
    fn new(n_layer_indices: usize) -> Self {
        LayeredDeductionVec {
            data: vec![],
            layer_indices: Vec::with_capacity(n_layer_indices),
        } // kcov-ignore
    }

    fn new_layer(&mut self, layer_len: usize) {
        self.layer_indices.push(self.data.len());
        self.data.reserve(layer_len);
    }

    fn add(&mut self, deduction: Deduction<'a, T>) {
        self.data.push(Rc::new(deduction))
    }

    fn all(&self) -> &[Rc<Deduction<'a, T>>] {
        &self.data
    }

    fn layer_range(&self, layer_index: usize) -> (usize, usize) {
        match layer_index {
            n if n >= self.layer_indices.len() => panic!("no such layer index: {}", n),
            n if n == self.layer_indices.len() - 1 => (self.layer_indices[n], self.data.len()),
            n => (self.layer_indices[n], self.layer_indices[n + 1]),
        }
    }
}

fn build_deductions<T>(aba_framework: &ABAFramework<T>) -> LayeredDeductionVec<T>
where
    T: LabelType,
{
    let supports_for_claims = AtomSupport::compute(aba_framework);
    let mut deductions = LayeredDeductionVec::new(aba_framework.language().len());
    for (i, opt_supports) in supports_for_claims.iter_supports().enumerate() {
        if opt_supports.is_none() {
            deductions.new_layer(0);
            continue;
        }
        let supports = opt_supports.as_ref().unwrap();
        deductions.new_layer(supports.len());
        let claim = aba_framework.get_atom_by_id(i);
        for support in supports.iter() {
            deductions.add(Deduction {
                claim,
                support: support
                    .iter()
                    .map(|i| aba_framework.get_atom_by_id(*i))
                    .collect(),
            })
        }
    }
    deductions
}

fn add_attacks<'a, T>(
    aa: &mut AAFramework<InstantiationLabel<'a, T>>,
    aba: &'a ABAFramework<T>,
    deductions: &LayeredDeductionVec<'a, T>,
) where
    T: LabelType,
{
    for (i, d) in deductions.all().iter().enumerate() {
        for s in &d.support {
            if let Some(j) = aba.try_get_contrary_index_by_id(s.id()) {
                let (min_bound, max_bound) = deductions.layer_range(j);
                (min_bound..max_bound).for_each(|k| aa.new_attack_by_ids(k, i).unwrap())
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::aba::Iccma23ABAReader;

    #[test]
    fn test_assumption_is_own_contrary() {
        let instance = "p aba 1\na 1\nc 1 1";
        let aba = Iccma23ABAReader::default()
            .read(&mut instance.as_bytes())
            .unwrap();
        let instantiation = ABAFrameworkInstantiation::instantiate(&aba);
        assert_eq!(1, instantiation.instantiated().n_arguments());
        assert_eq!(1, instantiation.instantiated().n_attacks());
        let attack = instantiation.instantiated().iter_attacks().next().unwrap();
        assert_eq!(attack.attacked().label(), attack.attacker().label());
    }
}
