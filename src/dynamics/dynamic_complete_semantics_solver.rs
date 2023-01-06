use std::{cell::RefCell, rc::Rc};

use super::DynamicSolver;
use crate::{
    aa::{AAFramework, Argument, ArgumentSet},
    sat::{self, Literal, SatSolver, SatSolverFactoryFn},
    solvers::CredulousAcceptanceComputer,
    utils::LabelType,
};
use anyhow::Result;

/// A dynamic solver dedicated to the complete semantics.
pub struct DynamicCompleteSemanticsSolver<T>
where
    T: LabelType,
{
    encoder: DynamicCompleteConstraintsEncoder<T>,
    solver: Rc<RefCell<Box<dyn SatSolver>>>,
}

impl<T> DynamicCompleteSemanticsSolver<T>
where
    T: LabelType,
{
    /// Builds a new SAT based dynamic solver for the complete semantics.
    ///
    /// The underlying SAT solver is one returned by [default_solver](crate::sat::default_solver).
    pub fn new() -> Self
    where
        T: LabelType,
    {
        Self::new_with_sat_solver_factory(Box::new(|| sat::default_solver()))
    }

    /// Builds a new SAT based dynamic solver for the complete semantics.
    ///
    /// The SAT solver to use in given through the solver factory.
    pub fn new_with_sat_solver_factory(solver_factory: Box<SatSolverFactoryFn>) -> Self
    where
        T: LabelType,
    {
        let solver = Rc::new(RefCell::new((solver_factory)()));
        Self {
            encoder: DynamicCompleteConstraintsEncoder::new(Rc::clone(&solver)),
            solver,
        }
    }
}

impl<T> Default for DynamicCompleteSemanticsSolver<T>
where
    T: LabelType,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<T> DynamicSolver<T> for DynamicCompleteSemanticsSolver<T>
where
    T: LabelType,
{
    fn new_argument(&mut self, label: T) {
        self.encoder.new_argument(label)
    }

    fn remove_argument(&mut self, label: &T) -> Result<()> {
        self.encoder.remove_argument(label)
    }

    fn new_attack(&mut self, from: &T, to: &T) -> Result<()> {
        self.encoder.new_attack(from, to)
    }

    fn remove_attack(&mut self, from: &T, to: &T) -> Result<()> {
        self.encoder.remove_attack(from, to)
    }
}

impl<T> CredulousAcceptanceComputer<T> for DynamicCompleteSemanticsSolver<T>
where
    T: LabelType,
{
    fn is_credulously_accepted(&mut self, arg: &T) -> bool {
        let mut assumptions = Vec::with_capacity(self.encoder.assumptions().len() + 1);
        assumptions.append(&mut self.encoder.assumptions().to_vec());
        assumptions.push(self.encoder.arg_to_lit(arg));
        self.solver
            .borrow_mut()
            .solve_under_assumptions(&assumptions)
            .unwrap_model()
            .is_some()
    }

    fn is_credulously_accepted_with_certificate(
        &mut self,
        _arg: &T,
    ) -> (bool, Option<Vec<&Argument<T>>>) {
        unimplemented!()
    }
}

pub struct DynamicCompleteConstraintsEncoder<T>
where
    T: LabelType,
{
    af: AAFramework<T>,
    arg_id_to_solver_var: Vec<Option<usize>>,
    arg_id_to_attacker_set_selector_var: Vec<Option<usize>>,
    solver_vars: Vec<SolverVarType>,
    solver: Rc<RefCell<Box<dyn SatSolver>>>,
    assumptions: Vec<Literal>,
}

#[derive(Debug)]
enum SolverVarType {
    Argument(usize),
    AttackerDisjunctionVar(usize),
    AttackerSetSelector(usize),
    Ignored,
}

impl<T> DynamicCompleteConstraintsEncoder<T>
where
    T: LabelType,
{
    pub fn new(solver: Rc<RefCell<Box<dyn SatSolver>>>) -> Self
    where
        T: LabelType,
    {
        Self {
            af: AAFramework::new_with_argument_set(ArgumentSet::new_with_labels(&[])),
            arg_id_to_solver_var: Vec::new(),
            arg_id_to_attacker_set_selector_var: Vec::new(),
            solver_vars: vec![SolverVarType::Ignored],
            solver,
            assumptions: Vec::new(),
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

    pub fn arg_id_from_solver_var(&self, solver_var: usize) -> Option<usize> {
        match self.solver_vars[solver_var] {
            SolverVarType::Argument(arg) => Some(arg),
            _ => None,
        }
    }

    pub fn new_argument(&mut self, label: T) {
        self.af.new_argument(label);
        let arg_id = self.af.max_argument_id().unwrap();
        let solver_var = self.new_solver_var(SolverVarType::Argument(arg_id));
        let attacker_disjunction_var =
            self.new_solver_var(SolverVarType::AttackerDisjunctionVar(arg_id));
        self.arg_id_to_solver_var.push(Some(solver_var));
        self.arg_id_to_attacker_set_selector_var.push(None);
        self.solver.borrow_mut().add_clause(vec![
            Literal::from(solver_var as isize).negate(),
            Literal::from(attacker_disjunction_var as isize).negate(),
        ]);
        self.update_attacks_to_constraints(arg_id);
    }

    fn new_solver_var(&mut self, var_type: SolverVarType) -> usize {
        self.solver_vars.push(var_type);
        self.solver_vars.len() - 1
    }

    fn update_attacks_to_constraints(&mut self, to_arg_id: usize) {
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
                Literal::from(self.arg_id_to_solver_var[attacker_id].unwrap() as isize);
            full_cl.push(attacker_lit);
            self.solver.borrow_mut().add_clause(vec![
                attacker_set_selector_lit.negate(),
                attacker_disjunction_lit,
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
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn coreo_test() {
        let mut solver = DynamicCompleteSemanticsSolver::new();
        solver.new_argument(1);
        solver.new_argument(2);
        solver.new_attack(&1, &2).unwrap();
        assert!(solver.is_credulously_accepted(&1));
        assert!(!solver.is_credulously_accepted(&2));

        solver.remove_attack(&1, &2).unwrap();
        assert!(solver.is_credulously_accepted(&1));
        assert!(solver.is_credulously_accepted(&2));

        solver.new_argument(3);
        solver.new_attack(&3, &2).unwrap();
        solver.new_attack(&2, &1).unwrap();
        assert!(solver.is_credulously_accepted(&1));
        assert!(!solver.is_credulously_accepted(&2));
        assert!(solver.is_credulously_accepted(&3));

        solver.remove_argument(&1).unwrap();
        solver.new_argument(4);
        solver.new_attack(&4, &3).unwrap();
        solver.new_attack(&3, &4).unwrap();
        assert!(solver.is_credulously_accepted(&2));
        assert!(solver.is_credulously_accepted(&3));
        assert!(solver.is_credulously_accepted(&4));
    }
}
