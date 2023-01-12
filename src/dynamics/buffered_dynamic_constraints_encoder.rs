use super::dynamic_constraints_encoder::DynamicConstraintsEncoder;
use crate::{aa::Semantics, sat::SatSolver, utils::LabelType};
use anyhow::Result;
use std::{
    cell::{Cell, Ref, RefCell},
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
}

pub struct BufferedDynamicConstraintsEncoder<T>
where
    T: LabelType,
{
    buffer: Vec<DynamicsEvent<T>>,
    next_to_encode: Cell<usize>,
    encoder: RefCell<DynamicConstraintsEncoder<T>>,
}

impl<T> BufferedDynamicConstraintsEncoder<T>
where
    T: LabelType,
{
    pub fn new(solver: Rc<RefCell<Box<dyn SatSolver>>>, semantics: Semantics) -> Self {
        let encoder = RefCell::new(DynamicConstraintsEncoder::new(solver, semantics));
        encoder
            .borrow_mut()
            .enable_update_attacks_to_constraints(false);
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

    pub fn update_encoding(&self) {
        let mut update_attacks_to = Vec::new();
        let mut update_attacks_to_bool = vec![
            false;
            1 + self
                .encoder
                .borrow()
                .af()
                .max_argument_id()
                .unwrap_or_default()
        ];
        let mut must_update_attacks_to = |arg_id: usize| {
            if update_attacks_to_bool.len() <= arg_id {
                update_attacks_to_bool.resize(arg_id + 1, false);
            }
            if !update_attacks_to_bool[arg_id] {
                update_attacks_to_bool[arg_id] = true;
                update_attacks_to.push(arg_id);
            }
        };
        fn label_to_id<U>(encoder_ref: Ref<DynamicConstraintsEncoder<U>>, label: &U) -> usize
        where
            U: LabelType,
        {
            encoder_ref
                .af()
                .argument_set()
                .get_argument(label)
                .unwrap()
                .id()
        }
        self.buffer[self.next_to_encode.get()..]
            .iter()
            .for_each(|e| match e {
                DynamicsEvent::NewArgument(l) => {
                    self.encoder.borrow_mut().new_argument(l.clone());
                    must_update_attacks_to(label_to_id(self.encoder.borrow(), l));
                }
                DynamicsEvent::RemoveArgument(l) => {
                    let arg_id = self
                        .encoder
                        .borrow()
                        .af()
                        .argument_set()
                        .get_argument(l)
                        .unwrap()
                        .id();
                    for id in self
                        .encoder
                        .borrow()
                        .af()
                        .iter_attacks_from_id(arg_id)
                        .map(|att| att.attacked().id())
                        .filter(|id| *id != arg_id)
                    {
                        must_update_attacks_to(id);
                    }
                    self.encoder.borrow_mut().remove_argument(l).unwrap()
                }
                DynamicsEvent::NewAttack(l0, l1) => {
                    self.encoder.borrow_mut().new_attack(l0, l1).unwrap();
                    must_update_attacks_to(label_to_id(self.encoder.borrow(), l1));
                }
                DynamicsEvent::RemoveAttack(l0, l1) => {
                    self.encoder.borrow_mut().remove_attack(l0, l1).unwrap();
                    must_update_attacks_to(label_to_id(self.encoder.borrow(), l1));
                }
            });
        self.encoder
            .borrow_mut()
            .enable_update_attacks_to_constraints(true);
        update_attacks_to
            .into_iter()
            .for_each(|id| self.encoder.borrow_mut().update_attacks_to_constraints(id));
        self.encoder
            .borrow_mut()
            .enable_update_attacks_to_constraints(false);
        self.next_to_encode.set(self.buffer.len());
    }

    pub fn encoder(&self) -> Ref<DynamicConstraintsEncoder<T>> {
        self.update_encoding();
        self.encoder.borrow()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sat;

    #[test]
    fn test_one_new_var_for_multiple_attacks_to_arg() {
        let solver = Rc::new(RefCell::new(sat::default_solver()));
        let mut history = BufferedDynamicConstraintsEncoder::new(Rc::clone(&solver), Semantics::CO);
        history.buffer_new_argument("a");
        history.buffer_new_argument("b");
        history.buffer_new_argument("c");
        history.buffer_new_attack(&"a", &"b").unwrap();
        history.update_encoding();
        let n_vars = solver.borrow().n_vars();
        history.buffer_new_attack(&"a", &"c").unwrap();
        history.buffer_new_attack(&"b", &"c").unwrap();
        history.update_encoding();
        assert_eq!(n_vars + 1, solver.borrow().n_vars());
    }
}
