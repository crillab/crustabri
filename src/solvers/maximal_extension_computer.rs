use super::utils;
use crate::{
    aa::{AAFramework, Argument, LabelType},
    sat::{Assignment, Literal, SatSolver},
};

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
    pub(crate) sat_solver: &'a mut dyn SatSolver,
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

pub(crate) struct MaximalExtensionComputer<'a, T>
where
    T: LabelType,
{
    af: &'a AAFramework<T>,
    solver: Box<dyn SatSolver>,
    current_extension: Option<Vec<&'a Argument<T>>>,
    current_model: Option<Assignment>,
    state: MaximalExtensionComputerState,
    selector: Literal,
    increase_current_fn: Option<IncreaseCurrentFn<T>>,
    discard_current_fn: Option<DiscardCurrentFn<T>>,
    discard_maximal_fn: Option<DiscardMaximalFn<T>>,
}

impl<'a, T> MaximalExtensionComputer<'a, T>
where
    T: LabelType,
{
    pub fn new(af: &'a AAFramework<T>, solver: Box<dyn SatSolver>) -> Self {
        let selector = Literal::from(1 + solver.n_vars() as isize);
        Self {
            af,
            solver,
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
                sat_solver: self.solver.as_mut(),
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
            sat_solver: self.solver.as_mut(),
            current_model: self.current_model.as_ref(),
            selector: self.selector,
        });
        self.new_search()
    }

    pub(crate) fn discard_current_search(&mut self) {
        (self.discard_current_fn.as_ref().unwrap())(MaximalExtensionComputerStateData {
            af: self.af,
            current_arg_set: self.current_extension.as_ref().unwrap(),
            sat_solver: self.solver.as_mut(),
            current_model: self.current_model.as_ref(),
            selector: self.selector,
        });
        self.state = MaximalExtensionComputerState::JustDiscarded;
    }

    pub(crate) fn state_data(&mut self) -> MaximalExtensionComputerStateData<T> {
        MaximalExtensionComputerStateData {
            af: self.af,
            current_arg_set: self.current_extension.as_ref().unwrap(),
            sat_solver: self.solver.as_mut(),
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
        self.solver
            .solve_under_assumptions(assumptions)
            .unwrap_model()
            .map(|new_ext_assignment| {
                let ext = utils::assignment_to_complete_extension(&new_ext_assignment, self.af);
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

impl<T> Drop for MaximalExtensionComputer<'_, T>
where
    T: LabelType,
{
    fn drop(&mut self) {
        self.solver.add_clause(vec![self.selector]);
    }
}
