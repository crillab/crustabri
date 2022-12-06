use super::{atom_support_computer::AtomSupport, ABAFramework, Atom};
use crate::aa::{AAFramework, Argument, ArgumentSet, LabelType};
use std::{fmt::Display, rc::Rc};

/// An ABA framework instantiation to an AA framework.
///
/// Contains both the initial ABA framework and the instantiated AA framework, and the arguments/attacks mappings.
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
    /// Instantiates an ABA framework, producing an AA framework.
    ///
    /// # Arguments
    ///
    /// * `aba_framework` - the ABA framework
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
    pub fn instantiated(&self) -> &AAFramework<InstantiationLabel<'a, T>> {
        &self.aa_framework
    }

    /// Returns a mutable reference to the instantiated abstract framework.
    pub fn instantiated_mut(&mut self) -> &mut AAFramework<InstantiationLabel<'a, T>> {
        &mut self.aa_framework
    }

    /// Returns the set of ABA assumptions involved in the provided AA extension.
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
