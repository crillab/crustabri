use crate::{
    aa::{AAFramework, Argument},
    encodings::ConstraintsEncoder,
    sat::{Assignment, Literal, SatSolver},
    utils::LabelType,
};
use std::{cell::RefCell, rc::Rc};

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub(crate) enum MaximalExtensionComputerState {
    Maximal,
    Intermediate,
    JustDiscarded,
    None,
    Init,
}

pub(crate) struct MaximalExtensionComputerStateData<'a, T>
where
    T: LabelType,
{
    pub(crate) af: &'a AAFramework<T>,
    pub(crate) current_arg_set: &'a [&'a Argument<T>],
    pub(crate) constraints_encoder: &'a dyn ConstraintsEncoder<T>,
    pub(crate) current_model: Option<&'a Assignment>,
    pub(crate) selector: Literal,
}

// A type for functions aiming at increasing an intermediate extension.
//
// IN: this object's data.
// OUT: the SAT solver assumptions to add to compute the next set of arguments; it must contain the negated selector.
type IncreaseCurrentFn<T> =
    Box<dyn for<'a> Fn(MaximalExtensionComputerStateData<'a, T>) -> Vec<Literal>>;

// A type for functions used to discard the current search for a maximal extension.
//
// IN: this object's data.
type DiscardCurrentFn<T> = Box<dyn for<'a> Fn(MaximalExtensionComputerStateData<'a, T>)>;

// A type for functions used to discard a maximal extension.
//
// IN: this object's data.
type DiscardMaximalFn<T> = Box<dyn for<'a> Fn(MaximalExtensionComputerStateData<'a, T>)>;

pub(crate) struct MaximalExtensionComputer<'a, 'b, T>
where
    T: LabelType,
{
    af: &'a AAFramework<T>,
    solver: Rc<RefCell<Box<dyn SatSolver>>>,
    additional_assumptions: Vec<Literal>,
    constraints_encoder: &'b dyn ConstraintsEncoder<T>,
    current_extension: Option<Vec<&'a Argument<T>>>,
    current_model: Option<Assignment>,
    state: MaximalExtensionComputerState,
    selector: Literal,
    increase_current_fn: Option<IncreaseCurrentFn<T>>,
    discard_current_fn: Option<DiscardCurrentFn<T>>,
    discard_maximal_fn: Option<DiscardMaximalFn<T>>,
}

impl<'a, 'b, T> MaximalExtensionComputer<'a, 'b, T>
where
    T: LabelType,
{
    pub fn new(
        af: &'a AAFramework<T>,
        solver: Rc<RefCell<Box<dyn SatSolver>>>,
        constraints_encoder: &'b dyn ConstraintsEncoder<T>,
    ) -> Self {
        let selector = Literal::from(1 + solver.borrow().n_vars() as isize);
        Self {
            af,
            solver,
            additional_assumptions: vec![],
            constraints_encoder,
            current_extension: None,
            current_model: None,
            state: MaximalExtensionComputerState::Init,
            selector,
            increase_current_fn: None,
            discard_current_fn: None,
            discard_maximal_fn: None,
        }
    }

    pub fn set_increase_current_fn(&mut self, increase_current_fn: IncreaseCurrentFn<T>) {
        self.increase_current_fn = Some(increase_current_fn);
    }

    pub fn set_discard_maximal_fn(&mut self, discard_maximal_fn: DiscardMaximalFn<T>) {
        self.discard_maximal_fn = Some(discard_maximal_fn);
    }

    pub fn set_discard_current_fn(&mut self, discard_current_fn: DiscardCurrentFn<T>) {
        self.discard_current_fn = Some(discard_current_fn);
    }

    pub fn set_additional_assumptions(&mut self, assumptions: Vec<Literal>) {
        self.additional_assumptions = assumptions;
    }

    pub fn state(&self) -> MaximalExtensionComputerState {
        self.state
    }

    pub fn compute_maximal(mut self) -> Vec<&'a Argument<T>> {
        while self.state != MaximalExtensionComputerState::Maximal {
            self.compute_next();
        }
        self.current_extension.take().unwrap()
    }

    pub fn compute_next(&mut self) {
        match &self.state {
            MaximalExtensionComputerState::Maximal => self.discard_maximal_and_new_search(),
            MaximalExtensionComputerState::Intermediate => self.increase_current(),
            MaximalExtensionComputerState::JustDiscarded => self.new_search(),
            MaximalExtensionComputerState::None => panic!("no more extensions"),
            MaximalExtensionComputerState::Init => self.compute_grounded(),
        };
    }

    fn compute_grounded(&mut self) {
        self.current_extension = Some(self.af.grounded_extension());
        self.state = MaximalExtensionComputerState::Intermediate;
    }

    fn increase_current(&mut self) {
        let assumptions =
            (self.increase_current_fn.as_ref().unwrap())(MaximalExtensionComputerStateData {
                af: self.af,
                current_arg_set: self.current_extension.as_ref().unwrap(),
                constraints_encoder: self.constraints_encoder,
                current_model: self.current_model.as_ref(),
                selector: self.selector,
            });
        match self.solve(&assumptions) {
            Some((assignment, ext)) => {
                self.current_extension = Some(ext);
                self.current_model = Some(assignment);
                self.state = MaximalExtensionComputerState::Intermediate
            }
            None => self.state = MaximalExtensionComputerState::Maximal,
        }
    }

    fn discard_maximal_and_new_search(&mut self) {
        (self.discard_maximal_fn.as_ref().unwrap())(MaximalExtensionComputerStateData {
            af: self.af,
            current_arg_set: self.current_extension.as_ref().unwrap(),
            constraints_encoder: self.constraints_encoder,
            current_model: self.current_model.as_ref(),
            selector: self.selector,
        });
        self.new_search()
    }

    pub(crate) fn discard_current_search(&mut self) {
        (self.discard_current_fn.as_ref().unwrap())(MaximalExtensionComputerStateData {
            af: self.af,
            current_arg_set: self.current_extension.as_ref().unwrap(),
            constraints_encoder: self.constraints_encoder,
            current_model: self.current_model.as_ref(),
            selector: self.selector,
        });
        self.state = MaximalExtensionComputerState::JustDiscarded;
    }

    pub(crate) fn state_data(&mut self) -> MaximalExtensionComputerStateData<T> {
        MaximalExtensionComputerStateData {
            af: self.af,
            current_arg_set: self.current_extension.as_ref().unwrap(),
            constraints_encoder: self.constraints_encoder,
            current_model: self.current_model.as_ref(),
            selector: self.selector,
        }
    }

    fn new_search(&mut self) {
        let assumptions = vec![self.selector.negate()];
        match self.solve(&assumptions) {
            Some((assignment, ext)) => {
                self.current_extension = Some(ext);
                self.current_model = Some(assignment);
                self.state = MaximalExtensionComputerState::Intermediate
            }
            None => self.state = MaximalExtensionComputerState::None,
        }
    }

    fn solve(&mut self, assumptions: &[Literal]) -> Option<(Assignment, Vec<&'a Argument<T>>)> {
        let mut effective_assumptions =
            Vec::with_capacity(assumptions.len() + self.additional_assumptions.len());
        effective_assumptions.append(&mut assumptions.to_vec());
        effective_assumptions.append(&mut self.additional_assumptions.clone());
        self.solver
            .borrow_mut()
            .solve_under_assumptions(&effective_assumptions)
            .unwrap_model()
            .map(|new_ext_assignment| {
                let ext = self
                    .constraints_encoder
                    .assignment_to_extension(&new_ext_assignment, self.af);
                (new_ext_assignment, ext)
            })
    }

    pub fn take_current(mut self) -> Vec<&'a Argument<T>> {
        self.current_extension.take().unwrap()
    }

    pub fn current(&self) -> &[&'a Argument<T>] {
        self.current_extension.as_ref().unwrap()
    }
}

impl<T> Drop for MaximalExtensionComputer<'_, '_, T>
where
    T: LabelType,
{
    fn drop(&mut self) {
        self.solver.borrow_mut().add_clause(vec![self.selector]);
    }
}

pub(crate) fn new_for_preferred_semantics<'a, 'b, T>(
    af: &'a AAFramework<T>,
    solver: Rc<RefCell<Box<dyn SatSolver>>>,
    constraints_encoder: &'b dyn ConstraintsEncoder<T>,
) -> MaximalExtensionComputer<'a, 'b, T>
where
    T: LabelType,
{
    let mut computer = MaximalExtensionComputer::new(af, Rc::clone(&solver), constraints_encoder);
    let solver_clone = Rc::clone(&solver);
    computer.set_increase_current_fn(Box::new(move |fn_data| {
        let (mut in_ext, mut not_in_ext) = split_in_extension(
            fn_data.af,
            fn_data.current_arg_set,
            fn_data.af.n_arguments(),
            fn_data.constraints_encoder,
        );
        not_in_ext.push(fn_data.selector);
        in_ext.push(fn_data.selector.negate());
        solver_clone.borrow_mut().add_clause(not_in_ext);
        in_ext
    }));
    let discard_fn = Box::new(move |fn_data: MaximalExtensionComputerStateData<T>| {
        let (_, mut not_in_ext) = split_in_extension(
            fn_data.af,
            fn_data.current_arg_set,
            fn_data.af.n_arguments(),
            fn_data.constraints_encoder,
        );
        not_in_ext.push(fn_data.selector);
        solver.borrow_mut().add_clause(not_in_ext);
    });
    computer.set_discard_current_fn(discard_fn.clone());
    computer.set_discard_maximal_fn(discard_fn);
    computer
}

pub(crate) fn split_in_extension<T>(
    af: &AAFramework<T>,
    current: &[&Argument<T>],
    n_args: usize,
    constraints_encoder: &dyn ConstraintsEncoder<T>,
) -> (Vec<Literal>, Vec<Literal>)
where
    T: LabelType,
{
    let mut in_ext_bool = vec![false; n_args];
    current.iter().for_each(|a| {
        let id = a.id();
        if id >= in_ext_bool.len() {
            in_ext_bool.resize(id + 1, false);
        }
        in_ext_bool[a.id()] = true
    });
    let mut not_in_ext = Vec::with_capacity(n_args);
    let mut in_ext = Vec::with_capacity(n_args);
    in_ext_bool.iter().enumerate().for_each(|(i, b)| {
        if !af.argument_set().has_argument_with_id(i) {
            return;
        }
        let lit = constraints_encoder.arg_to_lit(af.argument_set().get_argument_by_id(i));
        match *b {
            true => in_ext.push(lit),
            false => not_in_ext.push(lit),
        }
    });
    (in_ext, not_in_ext)
}

pub(crate) fn new_for_ideal_semantics<'a, 'b, T>(
    af: &'a AAFramework<T>,
    solver: Rc<RefCell<Box<dyn SatSolver>>>,
    constraints_encoder: &'b dyn ConstraintsEncoder<T>,
    assumptions_for_forbidden_args: Vec<Literal>,
) -> MaximalExtensionComputer<'a, 'b, T>
where
    T: LabelType,
{
    let mut computer = MaximalExtensionComputer::new(af, Rc::clone(&solver), constraints_encoder);
    computer.set_increase_current_fn(Box::new(move |fn_data| {
        let (mut in_ext, mut not_in_ext) = split_in_extension(
            fn_data.af,
            fn_data.current_arg_set,
            fn_data.af.n_arguments(),
            fn_data.constraints_encoder,
        );
        not_in_ext.push(fn_data.selector);
        in_ext.push(fn_data.selector.negate());
        in_ext.append(&mut assumptions_for_forbidden_args.to_vec());
        solver.borrow_mut().add_clause(not_in_ext);
        in_ext
    }));
    computer
}
