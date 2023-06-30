use super::dynamic_constraints_encoder::DynamicConstraintsEncoder;
use crate::{
    aa::{AAFramework, Argument, Semantics},
    sat::SatSolver,
    utils::LabelType,
};
use anyhow::Result;
use std::{
    cell::{Cell, RefCell},
    rc::Rc,
};

enum DynamicsEvent<T>
where
    T: LabelType,
{
    NewArgument(T),
    RemoveArgument(T),
    NewAttack(T, T),
    RemoveAttack(T, T),
    CredulousAcceptanceComputation {
        proved_accepted: Vec<T>,
        proved_refused: Vec<T>,
        extension: Option<Vec<usize>>,
    },
    SkepticalAcceptanceComputation {
        proved_accepted: Vec<T>,
        proved_refused: Vec<T>,
        extension: Option<Vec<usize>>,
    },
}

pub struct BufferedDynamicConstraintsEncoder<T>
where
    T: LabelType,
{
    buffer: Vec<DynamicsEvent<T>>,
    next_to_encode: Cell<usize>,
    encoder: DynamicConstraintsEncoder,
}

impl<T> BufferedDynamicConstraintsEncoder<T>
where
    T: LabelType,
{
    pub fn new(solver: Rc<RefCell<Box<dyn SatSolver>>>, semantics: Semantics) -> Self {
        let mut encoder = DynamicConstraintsEncoder::new(solver, semantics);
        encoder.enable_update_attacks_to_constraints(false);
        BufferedDynamicConstraintsEncoder {
            buffer: Vec::new(),
            next_to_encode: Cell::new(0),
            encoder,
        }
    }

    pub fn buffer_new_argument(&mut self, label: T) {
        self.buffer.push(DynamicsEvent::NewArgument(label))
    }

    pub fn buffer_remove_argument(&mut self, label: &T) -> Result<()> {
        self.buffer
            .push(DynamicsEvent::RemoveArgument(label.clone()));
        Ok(())
    }

    pub fn buffer_new_attack(&mut self, from: &T, to: &T) -> Result<()> {
        self.buffer
            .push(DynamicsEvent::NewAttack(from.clone(), to.clone()));
        Ok(())
    }

    pub fn buffer_remove_attack(&mut self, from: &T, to: &T) -> Result<()> {
        self.buffer
            .push(DynamicsEvent::RemoveAttack(from.clone(), to.clone()));
        Ok(())
    }

    pub fn update_encoding(&mut self, af: &mut AAFramework<T>) {
        let mut update_attacks_to = Vec::new();
        let mut update_attacks_to_bool = vec![false; 1 + af.max_argument_id().unwrap_or_default()];
        let mut must_update_attacks_to = |arg_id: usize| {
            if update_attacks_to_bool.len() <= arg_id {
                update_attacks_to_bool.resize(arg_id + 1, false);
            }
            if !update_attacks_to_bool[arg_id] {
                update_attacks_to_bool[arg_id] = true;
                update_attacks_to.push(arg_id);
            }
        };
        fn label_to_id<U>(af: &AAFramework<U>, label: &U) -> usize
        where
            U: LabelType,
        {
            af.argument_set().get_argument(label).unwrap().id()
        }
        self.buffer[self.next_to_encode.get()..]
            .iter()
            .for_each(|e| match e {
                DynamicsEvent::NewArgument(l) => {
                    self.encoder.new_argument(af, l.clone());
                    must_update_attacks_to(label_to_id(af, l));
                }
                DynamicsEvent::RemoveArgument(l) => {
                    let arg_id = af.argument_set().get_argument(l).unwrap().id();
                    for id in af
                        .iter_attacks_from_id(arg_id)
                        .map(|att| att.attacked().id())
                        .filter(|id| *id != arg_id)
                    {
                        must_update_attacks_to(id);
                    }
                    self.encoder.remove_argument(af, l).unwrap()
                }
                DynamicsEvent::NewAttack(l0, l1) => {
                    self.encoder.new_attack(af, l0, l1).unwrap();
                    must_update_attacks_to(label_to_id(af, l1));
                }
                DynamicsEvent::RemoveAttack(l0, l1) => {
                    self.encoder.remove_attack(af, l0, l1).unwrap();
                    must_update_attacks_to(label_to_id(af, l1));
                }
                DynamicsEvent::SkepticalAcceptanceComputation { .. }
                | DynamicsEvent::CredulousAcceptanceComputation { .. } => {}
            });
        self.encoder.enable_update_attacks_to_constraints(true);
        update_attacks_to
            .into_iter()
            .filter(|id| af.argument_set().has_argument_with_id(*id))
            .for_each(|id| self.encoder.update_attacks_to_constraints(af, id));
        self.encoder.enable_update_attacks_to_constraints(false);
        self.next_to_encode.set(self.buffer.len());
    }

    pub fn encoder(&self) -> &DynamicConstraintsEncoder {
        &self.encoder
    }

    pub fn add_credulous_computation(
        &mut self,
        proved_accepted: Vec<T>,
        proved_refused: Vec<T>,
        extension: Option<Vec<&Argument<T>>>,
    ) {
        self.buffer
            .push(DynamicsEvent::CredulousAcceptanceComputation {
                proved_accepted,
                proved_refused,
                extension: extension.map(|v| v.iter().map(|a| a.id()).collect()),
            })
    }

    pub fn is_credulously_accepted(&self, label: &T) -> (Option<bool>, Option<Vec<usize>>) {
        for e in self.buffer.iter().rev() {
            match e {
                DynamicsEvent::CredulousAcceptanceComputation {
                    proved_accepted,
                    proved_refused,
                    extension,
                } => {
                    if proved_accepted.contains(label) && extension.is_some() {
                        return (Some(true), Some(extension.clone().unwrap()));
                    }
                    if proved_refused.contains(label) {
                        return (Some(false), None);
                    }
                }
                DynamicsEvent::SkepticalAcceptanceComputation {
                    proved_accepted,
                    extension,
                    ..
                } => {
                    if proved_accepted.contains(label) && extension.is_some() {
                        return (Some(true), Some(extension.clone().unwrap()));
                    }
                }
                _ => break,
            }
        }
        (None, None)
    }

    pub fn add_skeptical_computation(
        &mut self,
        proved_accepted: Vec<T>,
        proved_refused: Vec<T>,
        extension: Option<Vec<&Argument<T>>>,
    ) {
        self.buffer
            .push(DynamicsEvent::SkepticalAcceptanceComputation {
                proved_accepted,
                proved_refused,
                extension: extension.map(|v| v.iter().map(|a| a.id()).collect()),
            })
    }

    pub fn is_skeptically_accepted(&self, label: &T) -> (Option<bool>, Option<Vec<usize>>) {
        for e in self.buffer.iter().rev() {
            match e {
                DynamicsEvent::SkepticalAcceptanceComputation {
                    proved_accepted,
                    proved_refused,
                    extension,
                } => {
                    if proved_accepted.contains(label) {
                        return (Some(true), None);
                    }
                    if proved_refused.contains(label) && extension.is_some() {
                        return (Some(false), Some(extension.clone().unwrap()));
                    }
                }
                DynamicsEvent::CredulousAcceptanceComputation {
                    proved_refused,
                    extension,
                    ..
                } => {
                    if proved_refused.contains(label) && extension.is_some() {
                        return (Some(false), Some(extension.clone().unwrap()));
                    }
                }
                _ => break,
            }
        }
        (None, None)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sat;

    #[test]
    fn test_one_new_var_for_multiple_attacks_to_arg() {
        let mut af = AAFramework::default();
        let solver = Rc::new(RefCell::new(sat::default_solver()));
        let mut history = BufferedDynamicConstraintsEncoder::new(Rc::clone(&solver), Semantics::CO);
        history.buffer_new_argument("a");
        history.buffer_new_argument("b");
        history.buffer_new_argument("c");
        history.buffer_new_attack(&"a", &"b").unwrap();
        history.update_encoding(&mut af);
        let n_vars = solver.borrow().n_vars();
        history.buffer_new_attack(&"a", &"c").unwrap();
        history.buffer_new_attack(&"b", &"c").unwrap();
        history.update_encoding(&mut af);
        assert_eq!(n_vars + 1, solver.borrow().n_vars());
    }
}
