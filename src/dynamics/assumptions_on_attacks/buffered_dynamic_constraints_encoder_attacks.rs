use super::dynamic_constraints_encoder_attacks::DynamicConstraintsEncoder;
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
    solver_factory: Box<dyn Fn() -> Box<dyn SatSolver>>,
}

impl<T> BufferedDynamicConstraintsEncoder<T>
where
    T: LabelType,
{
    pub fn new_with_arg_factor(
        solver: Rc<RefCell<Box<dyn SatSolver>>>,
        solver_factory: Box<dyn Fn() -> Box<dyn SatSolver>>,
        semantics: Semantics,
        arg_factor: f64,
    ) -> Self {
        let encoder = DynamicConstraintsEncoder::new_with_arg_factor(solver, semantics, arg_factor);
        BufferedDynamicConstraintsEncoder {
            buffer: Vec::new(),
            next_to_encode: Cell::new(0),
            encoder,
            solver_factory,
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
        self.buffer[self.next_to_encode.get()..]
            .iter()
            .for_each(|e| match e {
                DynamicsEvent::NewArgument(l) => {
                    self.encoder.new_argument(af, l.clone());
                }
                DynamicsEvent::RemoveArgument(l) => self.encoder.remove_argument(af, l).unwrap(),
                DynamicsEvent::NewAttack(l0, l1) => {
                    self.encoder.new_attack(af, l0, l1).unwrap();
                }
                DynamicsEvent::RemoveAttack(l0, l1) => {
                    self.encoder.remove_attack(af, l0, l1).unwrap();
                }
                DynamicsEvent::SkepticalAcceptanceComputation { .. }
                | DynamicsEvent::CredulousAcceptanceComputation { .. } => {}
            });
        self.encoder
            .update_encoding(af, self.solver_factory.as_ref());
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
