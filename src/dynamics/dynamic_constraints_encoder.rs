use crate::{
    aa::{AAFramework, Argument, ArgumentSet, Semantics},
    sat::{Literal, SatSolver},
    utils::LabelType,
};
use anyhow::Result;
use std::{cell::RefCell, rc::Rc};

pub struct DynamicConstraintsEncoder<T>
where
    T: LabelType,
{
    semantics: Semantics,
    af: AAFramework<T>,
    arg_id_to_solver_var: Vec<Option<usize>>,
    arg_id_to_attacker_set_selector_var: Vec<Option<usize>>,
    solver_vars: Vec<SolverVarType>,
    solver: Rc<RefCell<Box<dyn SatSolver>>>,
    assumptions: Vec<Literal>,
    update_attacks_to_constraints: bool,
}

#[derive(Debug)]
enum SolverVarType {
    Argument(usize),
    AttackerDisjunctionVar(usize),
    AttackerSetSelector(usize),
    Ignored,
}

impl<T> DynamicConstraintsEncoder<T>
where
    T: LabelType,
{
    pub fn new(solver: Rc<RefCell<Box<dyn SatSolver>>>, semantics: Semantics) -> Self
    where
        T: LabelType,
    {
        Self {
            semantics,
            af: AAFramework::new_with_argument_set(ArgumentSet::new_with_labels(&[])),
            arg_id_to_solver_var: Vec::new(),
            arg_id_to_attacker_set_selector_var: Vec::new(),
            solver_vars: vec![SolverVarType::Ignored],
            solver,
            assumptions: Vec::new(),
            update_attacks_to_constraints: true,
        }
    }

    pub fn af(&self) -> &AAFramework<T> {
        &self.af
    }

    pub fn assumptions(&self) -> &[Literal] {
        &self.assumptions
    }

    pub fn arg_to_lit(&self, arg: &T) -> Literal {
        let arg = self.af.argument_set().get_argument(arg).unwrap();
        Literal::from(self.arg_id_to_solver_var[arg.id()].unwrap() as isize)
    }

    pub fn new_argument(&mut self, label: T) {
        self.af.new_argument(label);
        let arg_id = self.af.max_argument_id().unwrap();
        let solver_var = self.new_solver_var(SolverVarType::Argument(arg_id));
        match self.semantics {
            Semantics::CO | Semantics::PR => {
                let attacker_disjunction_var =
                    self.new_solver_var(SolverVarType::AttackerDisjunctionVar(arg_id));
                self.solver.borrow_mut().add_clause(vec![
                    Literal::from(solver_var as isize).negate(),
                    Literal::from(attacker_disjunction_var as isize).negate(),
                ]);
            }
            _ => {}
        }
        self.arg_id_to_solver_var.push(Some(solver_var));
        self.arg_id_to_attacker_set_selector_var.push(None);
        self.update_attacks_to_constraints(arg_id);
    }

    fn new_solver_var(&mut self, var_type: SolverVarType) -> usize {
        self.solver_vars.push(var_type);
        self.solver_vars.len() - 1
    }

    pub(crate) fn enable_update_attacks_to_constraints(&mut self, v: bool) {
        self.update_attacks_to_constraints = v;
    }

    pub(crate) fn update_attacks_to_constraints(&mut self, to_arg_id: usize) {
        if !self.update_attacks_to_constraints {
            return;
        }
        if let Some(s) = self.arg_id_to_attacker_set_selector_var[to_arg_id] {
            self.remove_selector(s);
            self.arg_id_to_attacker_set_selector_var[to_arg_id] = None;
        }
        let attacker_set_selector_var =
            self.new_solver_var(SolverVarType::AttackerSetSelector(to_arg_id));
        let attacker_set_selector_lit = Literal::from(attacker_set_selector_var as isize);
        self.assumptions.push(attacker_set_selector_lit);
        self.arg_id_to_attacker_set_selector_var[to_arg_id] = Some(attacker_set_selector_var);
        let attackers_ids = self
            .af
            .iter_attacks_to(self.af.argument_set().get_argument_by_id(to_arg_id))
            .map(|att| att.attacker().id())
            .collect::<Vec<usize>>();
        match self.semantics {
            Semantics::CO | Semantics::PR => self
                .add_attacks_to_constraints_for_complete_semantics(
                    to_arg_id,
                    &attackers_ids,
                    attacker_set_selector_lit,
                ),
            Semantics::ST => self.add_attacks_to_constraints_for_stable_semantics(
                to_arg_id,
                &attackers_ids,
                attacker_set_selector_lit,
            ),
            _ => {}
        }
    }

    fn add_attacks_to_constraints_for_complete_semantics(
        &self,
        to_arg_id: usize,
        attackers_ids: &[usize],
        attacker_set_selector_lit: Literal,
    ) {
        let mut full_cl = Vec::with_capacity(2 + attackers_ids.len());
        full_cl.push(attacker_set_selector_lit.negate());
        let to_arg_lit = Literal::from(self.arg_id_to_solver_var[to_arg_id].unwrap() as isize);
        full_cl.push(to_arg_lit);
        for attacker_id in attackers_ids.iter() {
            let attacker_attacker_disjunction_lit =
                Literal::from(1 + self.arg_id_to_solver_var[*attacker_id].unwrap() as isize);
            full_cl.push(attacker_attacker_disjunction_lit.negate());
            self.solver.borrow_mut().add_clause(vec![
                attacker_set_selector_lit.negate(),
                to_arg_lit.negate(),
                attacker_attacker_disjunction_lit,
            ]);
        }
        self.solver.borrow_mut().add_clause(full_cl);
        let mut full_cl = Vec::with_capacity(2 + attackers_ids.len());
        full_cl.push(attacker_set_selector_lit.negate());
        let attacker_disjunction_lit =
            Literal::from(1 + self.arg_id_to_solver_var[to_arg_id].unwrap() as isize);
        full_cl.push(attacker_disjunction_lit.negate());
        for attacker_id in attackers_ids {
            let attacker_lit =
                Literal::from(self.arg_id_to_solver_var[*attacker_id].unwrap() as isize);
            full_cl.push(attacker_lit);
            self.solver.borrow_mut().add_clause(vec![
                attacker_set_selector_lit.negate(),
                attacker_disjunction_lit,
                attacker_lit.negate(),
            ]);
        }
        self.solver.borrow_mut().add_clause(full_cl);
    }

    fn add_attacks_to_constraints_for_stable_semantics(
        &self,
        to_arg_id: usize,
        attackers_ids: &[usize],
        attacker_set_selector_lit: Literal,
    ) {
        let mut full_cl = Vec::with_capacity(2 + attackers_ids.len());
        full_cl.push(attacker_set_selector_lit.negate());
        let to_arg_lit = Literal::from(self.arg_id_to_solver_var[to_arg_id].unwrap() as isize);
        full_cl.push(to_arg_lit);
        for attacker_id in attackers_ids.iter() {
            let attacker_lit =
                Literal::from(self.arg_id_to_solver_var[*attacker_id].unwrap() as isize);
            full_cl.push(attacker_lit);
            self.solver.borrow_mut().add_clause(vec![
                attacker_set_selector_lit.negate(),
                to_arg_lit.negate(),
                attacker_lit.negate(),
            ]);
        }
        self.solver.borrow_mut().add_clause(full_cl);
    }

    fn remove_selector(&mut self, selector: usize) {
        self.solver_vars[selector] = SolverVarType::Ignored;
        let selector_lit = Literal::from(selector as isize);
        self.solver
            .borrow_mut()
            .add_clause(vec![selector_lit.negate()]);
        self.assumptions.swap_remove(
            self.assumptions
                .iter()
                .position(|l| l == &selector_lit)
                .unwrap(),
        );
    }

    pub fn remove_argument(&mut self, label: &T) -> Result<()> {
        let arg = self.af.argument_set().get_argument(label)?;
        let arg_id = arg.id();
        let attacked_constraints_to_update = self
            .af
            .iter_attacks_from(arg)
            .map(|att| att.attacked().id())
            .filter(|id| *id != arg_id)
            .collect::<Vec<usize>>();
        self.af.remove_argument(label)?;
        let solver_var = self.arg_id_to_solver_var[arg_id].unwrap();
        self.arg_id_to_solver_var[arg_id] = None;
        if let Some(s) = self.arg_id_to_attacker_set_selector_var[arg_id] {
            self.remove_selector(s);
            self.arg_id_to_attacker_set_selector_var[arg_id] = None;
        }
        self.solver_vars[solver_var] = SolverVarType::Ignored;
        self.solver
            .borrow_mut()
            .add_clause(vec![Literal::from(solver_var as isize)]);
        attacked_constraints_to_update
            .iter()
            .for_each(|id| self.update_attacks_to_constraints(*id));
        Ok(())
    }

    pub fn new_attack(&mut self, from: &T, to: &T) -> Result<()> {
        self.af.new_attack(from, to)?;
        let to_id = self.af.argument_set().get_argument(to).unwrap().id();
        self.update_attacks_to_constraints(to_id);
        Ok(())
    }

    pub fn remove_attack(&mut self, from: &T, to: &T) -> Result<()> {
        self.af.remove_attack(from, to)?;
        let to_id = self.af.argument_set().get_argument(to).unwrap().id();
        self.update_attacks_to_constraints(to_id);
        Ok(())
    }

    pub fn solver_var_to_arg(&self, solver_var: usize) -> Option<&Argument<T>> {
        if let SolverVarType::Argument(arg_id) = self.solver_vars[solver_var] {
            return Some(self.af().argument_set().get_argument_by_id(arg_id));
        } else {
            None
        }
    }
}
