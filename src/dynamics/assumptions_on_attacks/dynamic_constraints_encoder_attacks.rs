use crate::{
    aa::{AAFramework, Argument, Semantics},
    sat::{Assignment, Literal, SatSolver},
    utils::LabelType,
};
use anyhow::Result;
use std::{cell::RefCell, rc::Rc};

pub struct DynamicConstraintsEncoder {
    semantics: Semantics,
    arg_id_to_solver_var: Vec<Option<usize>>,
    solver_vars: Vec<SolverVarType>,
    solver: Rc<RefCell<Box<dyn SatSolver>>>,
    arg_factor: f64,
    next_dummy_arg_var: usize,
    n_arg_vars: usize,
    need_to_encode: bool,
}

#[derive(Debug)]
enum SolverVarType {
    Argument(usize),
    AttackerDisjunctionVar,
    AttackAssumption,
    Ignored,
}

impl DynamicConstraintsEncoder {
    pub fn new_with_arg_factor(
        solver: Rc<RefCell<Box<dyn SatSolver>>>,
        semantics: Semantics,
        arg_factor: f64,
    ) -> Self {
        Self {
            semantics,
            arg_id_to_solver_var: Vec::new(),
            solver_vars: vec![SolverVarType::Ignored],
            solver,
            arg_factor,
            next_dummy_arg_var: 0,
            n_arg_vars: 0,
            need_to_encode: true,
        }
    }

    pub fn assumptions<T: LabelType>(&self, af: &AAFramework<T>) -> Vec<Literal> {
        let mut assumptions: Vec<_> = (1 + self.n_arg_vars..)
            .take(self.n_arg_vars * self.n_arg_vars)
            .map(|i| Literal::from(i as isize).negate())
            .collect();
        af.iter_attacks().for_each(|att| {
            let index = (self.arg_id_to_solver_var[att.attacked().id()].unwrap() - 1)
                * self.n_arg_vars
                + self.arg_id_to_solver_var[att.attacker().id()].unwrap()
                - 1;
            assumptions[index] = Literal::from((1 + index + self.n_arg_vars) as isize);
        });
        assumptions
    }

    pub fn arg_to_lit<T: LabelType>(&self, af: &AAFramework<T>, arg: &T) -> Literal {
        let arg = af.argument_set().get_argument(arg).unwrap();
        Literal::from(self.arg_id_to_solver_var[arg.id()].unwrap() as isize)
    }

    pub fn new_argument<T: LabelType>(&mut self, af: &mut AAFramework<T>, label: T) {
        af.new_argument(label);
        if self.next_dummy_arg_var >= self.n_arg_vars {
            self.need_to_encode = true;
        }
        if self.need_to_encode {
            return;
        }
        let arg_id = af.max_argument_id().unwrap();
        self.arg_id_to_solver_var
            .push(Some(self.next_dummy_arg_var));
        self.solver_vars[self.next_dummy_arg_var] = SolverVarType::Argument(arg_id);
        if self.semantics == Semantics::CO {
            self.solver_vars[self.next_dummy_arg_var + self.n_arg_vars * (1 + self.n_arg_vars)] =
                SolverVarType::AttackerDisjunctionVar;
        }
        self.next_dummy_arg_var += 1;
    }

    pub fn update_encoding<T: LabelType>(
        &mut self,
        af: &mut AAFramework<T>,
        solver_factory: &dyn Fn() -> Box<dyn SatSolver>,
    ) {
        match self.semantics {
            Semantics::CO => self.update_encoding_for_complete_semantics(af, solver_factory),
            Semantics::ST => self.update_encoding_for_stable_semantics(af, solver_factory),
            _ => panic!(),
        }
    }

    pub fn update_encoding_for_stable_semantics<T: LabelType>(
        &mut self,
        af: &mut AAFramework<T>,
        solver_factory: &dyn Fn() -> Box<dyn SatSolver>,
    ) {
        if !self.need_to_encode {
            return;
        }
        self.need_to_encode = false;
        *self.solver.borrow_mut() = (solver_factory)();
        let n_args = af.n_arguments();
        self.n_arg_vars = (n_args as f64 * self.arg_factor) as usize;
        self.solver
            .borrow_mut()
            .reserve(self.n_arg_vars * (1 + self.n_arg_vars));
        self.solver_vars = vec![SolverVarType::Ignored];
        self.arg_id_to_solver_var = vec![None; 1 + af.max_argument_id().unwrap_or_default()];
        af.argument_set().iter().for_each(|a| {
            self.arg_id_to_solver_var[a.id()] = Some(self.solver_vars.len());
            self.solver_vars.push(SolverVarType::Argument(a.id()));
        });
        (0..self.n_arg_vars - n_args).for_each(|_| self.solver_vars.push(SolverVarType::Ignored));
        (0..self.n_arg_vars * self.n_arg_vars)
            .for_each(|_| self.solver_vars.push(SolverVarType::AttackAssumption));
        self.next_dummy_arg_var = n_args + 1;
        (1..=self.n_arg_vars).for_each(|arg_var| {
            let arg_lit = Literal::from(arg_var as isize);
            let mut clause = Vec::with_capacity(1 + self.n_arg_vars);
            clause.push(arg_lit);
            (1..=self.n_arg_vars).for_each(|attacker_var| {
                let aux_lit = Literal::from(self.solver.borrow().n_vars() as isize + 1);
                let attacker_lit = Literal::from(attacker_var as isize);
                let attack_lit = Literal::from(
                    (1 + self.n_arg_vars + self.n_arg_vars * (arg_var - 1) + attacker_var - 1)
                        as isize,
                );
                self.solver
                    .borrow_mut()
                    .add_clause(vec![aux_lit.negate(), attacker_lit]);
                self.solver
                    .borrow_mut()
                    .add_clause(vec![aux_lit.negate(), attack_lit]);
                self.solver.borrow_mut().add_clause(vec![
                    aux_lit,
                    attacker_lit.negate(),
                    attack_lit.negate(),
                ]);
                clause.push(aux_lit);
                self.solver.borrow_mut().add_clause(vec![
                    attack_lit.negate(),
                    arg_lit.negate(),
                    attacker_lit.negate(),
                ]);
            });
            self.solver.borrow_mut().add_clause(clause);
        });
    }

    pub fn update_encoding_for_complete_semantics<T: LabelType>(
        &mut self,
        af: &mut AAFramework<T>,
        solver_factory: &dyn Fn() -> Box<dyn SatSolver>,
    ) {
        if !self.need_to_encode {
            return;
        }
        self.need_to_encode = false;
        *self.solver.borrow_mut() = (solver_factory)();
        let n_args = af.n_arguments();
        self.n_arg_vars = (n_args as f64 * self.arg_factor) as usize;
        self.solver
            .borrow_mut()
            .reserve(self.n_arg_vars * (2 + self.n_arg_vars));
        self.solver_vars = vec![SolverVarType::Ignored];
        self.arg_id_to_solver_var = vec![None; 1 + af.max_argument_id().unwrap_or_default()];
        af.argument_set().iter().for_each(|a| {
            self.arg_id_to_solver_var[a.id()] = Some(self.solver_vars.len());
            self.solver_vars.push(SolverVarType::Argument(a.id()));
        });
        (0..self.n_arg_vars - n_args).for_each(|_| self.solver_vars.push(SolverVarType::Ignored));
        (0..self.n_arg_vars * self.n_arg_vars)
            .for_each(|_| self.solver_vars.push(SolverVarType::AttackAssumption));
        af.argument_set().iter().for_each(|_| {
            self.solver_vars.push(SolverVarType::AttackerDisjunctionVar);
        });
        (0..self.n_arg_vars - n_args).for_each(|_| self.solver_vars.push(SolverVarType::Ignored));
        self.next_dummy_arg_var = n_args + 1;
        (1..=self.n_arg_vars).for_each(|arg_var| {
            let arg_lit = Literal::from(arg_var as isize);
            let arg_att_disj_lit =
                Literal::from((arg_var + self.n_arg_vars * (1 + self.n_arg_vars)) as isize);
            self.solver
                .borrow_mut()
                .add_clause(vec![arg_lit.negate(), arg_att_disj_lit.negate()]);
            let mut clause = Vec::with_capacity(1 + self.n_arg_vars);
            clause.push(arg_lit);
            (1..=self.n_arg_vars).for_each(|attacker_var| {
                let aux_lit = Literal::from(self.solver.borrow().n_vars() as isize + 1);
                let attacker_att_disj_lit = Literal::from(
                    (attacker_var + self.n_arg_vars * (1 + self.n_arg_vars)) as isize,
                );
                let attack_lit = Literal::from(
                    (1 + self.n_arg_vars + self.n_arg_vars * (arg_var - 1) + attacker_var - 1)
                        as isize,
                );
                self.solver
                    .borrow_mut()
                    .add_clause(vec![aux_lit.negate(), attacker_att_disj_lit.negate()]);
                self.solver
                    .borrow_mut()
                    .add_clause(vec![aux_lit.negate(), attack_lit]);
                self.solver.borrow_mut().add_clause(vec![
                    aux_lit,
                    attacker_att_disj_lit,
                    attack_lit.negate(),
                ]);
                clause.push(aux_lit);
                self.solver.borrow_mut().add_clause(vec![
                    attack_lit.negate(),
                    arg_lit.negate(),
                    attacker_att_disj_lit,
                ]);
            });
            self.solver.borrow_mut().add_clause(clause);
        });
        (1..=self.n_arg_vars).for_each(|arg_var| {
            let arg_att_disj_lit =
                Literal::from((arg_var + self.n_arg_vars * (1 + self.n_arg_vars)) as isize);
            let mut clause = Vec::with_capacity(1 + self.n_arg_vars);
            clause.push(arg_att_disj_lit.negate());
            (1..=self.n_arg_vars).for_each(|attacker_var| {
                let aux_lit = Literal::from(self.solver.borrow().n_vars() as isize + 1);
                let attacker_lit = Literal::from(attacker_var as isize);
                let attack_lit = Literal::from(
                    (1 + self.n_arg_vars + self.n_arg_vars * (arg_var - 1) + attacker_var - 1)
                        as isize,
                );
                self.solver
                    .borrow_mut()
                    .add_clause(vec![aux_lit.negate(), attacker_lit]);
                self.solver
                    .borrow_mut()
                    .add_clause(vec![aux_lit.negate(), attack_lit]);
                self.solver.borrow_mut().add_clause(vec![
                    aux_lit,
                    attacker_lit.negate(),
                    attack_lit.negate(),
                ]);
                clause.push(aux_lit);
                self.solver.borrow_mut().add_clause(vec![
                    attack_lit.negate(),
                    arg_att_disj_lit,
                    attacker_lit.negate(),
                ]);
            });
            self.solver.borrow_mut().add_clause(clause);
        });
    }

    pub fn remove_argument<T: LabelType>(
        &mut self,
        af: &mut AAFramework<T>,
        label: &T,
    ) -> Result<()> {
        let arg = af.argument_set().get_argument(label)?;
        let arg_id = arg.id();
        af.remove_argument(label)?;
        if arg_id < self.arg_id_to_solver_var.len() {
            if let Some(solver_var) = self.arg_id_to_solver_var[arg_id] {
                self.solver_vars[solver_var] = SolverVarType::Ignored;
                self.solver
                    .borrow_mut()
                    .add_clause(vec![Literal::from(solver_var as isize)]);
            }
            self.arg_id_to_solver_var[arg_id] = None;
        }
        Ok(())
    }

    pub fn new_attack<T: LabelType>(
        &mut self,
        af: &mut AAFramework<T>,
        from: &T,
        to: &T,
    ) -> Result<()> {
        af.new_attack(from, to)
    }

    pub fn remove_attack<T: LabelType>(
        &mut self,
        af: &mut AAFramework<T>,
        from: &T,
        to: &T,
    ) -> Result<()> {
        af.remove_attack(from, to)
    }

    pub fn solver_var_to_arg<'a, T: LabelType>(
        &self,
        af: &'a AAFramework<T>,
        solver_var: usize,
    ) -> Option<&'a Argument<T>> {
        if solver_var >= self.solver_vars.len() {
            return None;
        }
        if let SolverVarType::Argument(arg_id) = self.solver_vars[solver_var] {
            return Some(af.argument_set().get_argument_by_id(arg_id));
        } else {
            None
        }
    }

    pub fn assignment_to_extension<'a, T: LabelType>(
        &self,
        af: &'a AAFramework<T>,
        assignment: Assignment,
    ) -> Vec<&'a Argument<T>> {
        assignment
            .iter()
            .filter_map(|(v, b)| {
                if b == Some(true) {
                    self.solver_var_to_arg(af, v)
                } else {
                    None
                }
            })
            .collect()
    }
}
