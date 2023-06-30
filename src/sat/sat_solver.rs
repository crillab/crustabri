use super::cadical_solver::CadicalSolver;
use std::{
    fmt::Display,
    num::{NonZeroIsize, NonZeroUsize},
};

/// A variable in a SAT solver.
///
/// A variable is represented by a non-null positive integer.
/// It can be obtained through the [From] trait from an integer type.
/// Trying to get a variable from a negative or null integer creates a panic.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Variable(NonZeroUsize);

macro_rules! impl_var_from {
    ($t: ty) => {
        impl From<$t> for Variable {
            fn from(v: $t) -> Self {
                Self(NonZeroUsize::try_from(v as usize).unwrap())
            }
        }
    };
}
impl_var_from!(usize);
impl_var_from!(u128);
impl_var_from!(u64);
impl_var_from!(u32);
impl_var_from!(u16);
impl_var_from!(u8);

macro_rules! impl_var_from_neg {
    ($t: ty) => {
        impl From<$t> for Variable {
            fn from(v: $t) -> Self {
                if v < 0 {
                    panic!("cannot build a variable from a negative integer")
                }
                Self(NonZeroUsize::try_from(v as usize).unwrap())
            }
        }
    };
}
impl_var_from_neg!(isize);
impl_var_from_neg!(i128);
impl_var_from_neg!(i64);
impl_var_from_neg!(i32);
impl_var_from_neg!(i16);
impl_var_from_neg!(i8);

impl From<Variable> for usize {
    fn from(v: Variable) -> Self {
        v.0.into()
    }
}

/// A literal in a SAT solver.
///
/// A literal is represented by a non-null integer, representing a variable (absolute value of the integer) with a polarity (given by the sign).
/// It can be obtained through the [From] trait from a signed integer type.
/// Trying to get a literal from a null integer creates a panic.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Literal(NonZeroIsize);

impl Literal {
    /// Returns the literal with the same variable but the opposite polarity.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::sat::Literal;
    /// fn always_ok(l: Literal) {
    ///     assert_ne!(l, l.negate());
    ///     assert_eq!(l, l.negate().negate());
    /// }
    /// # always_ok(Literal::from(1));
    /// ```
    pub fn negate(self) -> Self {
        Self::from(-self.0.get())
    }

    /// Returns the underlying variable.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::sat::Literal;
    /// fn are_opposite_literals(l0: Literal, l1: Literal) -> bool {
    ///     l0 != l1 && l0.var() == l1.var()
    /// }
    /// # assert!(are_opposite_literals(Literal::from(1), Literal::from(-1)));
    /// ```
    pub fn var(&self) -> Variable {
        Variable(self.0.unsigned_abs())
    }
}

macro_rules! impl_lit_from {
    ($t: ty) => {
        impl From<$t> for Literal {
            fn from(l: $t) -> Self {
                Self(NonZeroIsize::try_from(l as isize).unwrap())
            }
        }
    };
}
impl_lit_from!(isize);
impl_lit_from!(i128);
impl_lit_from!(i64);
impl_lit_from!(i32);
impl_lit_from!(i16);
impl_lit_from!(i8);

impl From<Literal> for isize {
    fn from(l: Literal) -> Self {
        l.0.into()
    }
}

impl Display for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// Builds a clause from a list of integers.
macro_rules! clause {
    () => (
        vec![] as Vec<Literal>
    );
    ($($x:expr),+ $(,)?) => (
        [$($x),+].into_iter().map(crate::sat::Literal::from).collect::<Vec<crate::sat::Literal>>()
    );
}

pub(crate) use clause;

/// An assignment of a set of variables.
///
/// Inside the set of variables involved in the assignment, some may be unassigned.
/// This is the reason why accessors to assigned value return an [Option<bool>].
#[derive(Debug, PartialEq, Eq)]
pub struct Assignment(Vec<Option<bool>>);

impl Assignment {
    pub(crate) fn new(assignment: Vec<Option<bool>>) -> Self {
        Self(assignment)
    }

    /// Returns the value potentially assigned to the variable.
    ///
    /// The result in an [Option].
    /// In case the variable is not assigned, [Option::None] is returned.
    /// Else, [Option::Some] is returned and contains the assigned value.
    ///
    /// In order to iterate over an assignment, prefer the [iter](Self::iter) function.
    ///
    /// # Panic
    ///
    /// If the provided variable does not belong to the underlying problem, this function panics.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::sat::{Assignment, self};
    /// # fn get_assignment() -> Assignment {let mut s = sat::default_solver(); s.solve().unwrap_model().unwrap()}
    /// let assignment = get_assignment(); // user defined function
    /// # fn get_n_vars() -> usize {0}
    /// let n_vars = get_n_vars(); // user defined function
    /// for i in 1 ..= n_vars {
    ///     match assignment.value_of(i) {
    ///         Some(v) => println!("var {} is set to {}", i, v),
    ///         None => println!("var {} is left unassigned", i),
    ///     }
    /// }
    /// ```
    pub fn value_of<T>(&self, v: T) -> Option<bool>
    where
        T: Into<Variable>,
    {
        self.0[usize::from(v.into()) - 1]
    }

    /// Iterates over an assignment.
    ///
    /// Yielded values are [Option].
    /// In case the variable is not assigned, [Option::None] is returned.
    /// Else, [Option::Some] is returned and contains the assigned value.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::sat::{Assignment, self};
    /// # fn get_assignment() -> Assignment {let mut s = sat::default_solver(); s.solve().unwrap_model().unwrap()}
    /// let assignment = get_assignment(); // user defined function
    /// assignment.iter().for_each(|opt_lit| {
    ///     match opt_lit {
    ///         (i, Some(v)) => println!("var {} is set to {}", i, v),
    ///         (i, None) => println!("var {} is left unassigned", i),
    ///     }
    /// });
    /// ```
    pub fn iter(&self) -> impl Iterator<Item = (usize, Option<bool>)> + '_ {
        self.0.iter().enumerate().map(|(i, l)| (i + 1, *l))
    }
}

pub(crate) struct AssignmentIterator<'a> {
    assignment: &'a Assignment,
    next: usize,
}

impl Iterator for AssignmentIterator<'_> {
    type Item = (usize, Option<bool>);

    fn next(&mut self) -> Option<Self::Item> {
        if self.next == self.assignment.0.len() {
            None
        } else {
            self.next += 1;
            Some((self.next, self.assignment.0[self.next - 1]))
        }
    }
}

/// The result produced by a SAT solver search process.
///
/// This object handles positive result (satisfiable, with a model), negative result (unsatisfiable) and also erroneous invocations (timeout, solver crash, ...).
/// Models are given by a dedicated [Assignment] object.
///
/// In case a solver can't fail, one can safely call the [unwrap_model](Self::unwrap_model) function to safely get the result as an [Option].
#[derive(Debug, PartialEq, Eq)]
pub enum SolvingResult {
    /// The solver found a model
    Satisfiable(Assignment),
    /// The solver proved there is no model
    Unsatisfiable,
    /// The solver was not able to decide
    Unknown,
}

impl SolvingResult {
    /// Returns the underlying model if it exists, or [Option::None].
    ///
    /// # Panics
    ///
    /// If the solving result is set to [SolvingResult::Unknown], this function panics.
    pub fn unwrap_model(self) -> Option<Assignment> {
        match self {
            SolvingResult::Satisfiable(assignment) => Some(assignment),
            SolvingResult::Unsatisfiable => None,
            SolvingResult::Unknown => {
                panic!(r#"cannot unwrap solving result when the solver returned "Unknown""#)
            }
        }
    }
}

/// A trait for SAT solvers.
pub trait SatSolver {
    /// Adds a clause to this solver.
    ///
    /// The variables involved in the clause are automatically declared.
    fn add_clause(&mut self, cl: Vec<Literal>);

    /// Solves the problem formed by the clauses added so far.
    ///
    /// This function can return a positive result (satisfiable, with a model), a negative result (unsatisfiable) or a value indicating the solver was not able to check the satisfiability of the underlying formula.
    /// See the [SolvingResult] documentation for more information.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::sat::{self, Literal, SatSolver, SolvingResult};
    /// fn try_to_solve(s: &mut dyn SatSolver) {
    ///     match s.solve() {
    ///         SolvingResult::Satisfiable(assignment) => {
    ///             println!("a model was found for the problem");
    ///             for i in 1..s.n_vars() {
    ///                 match assignment.value_of(i) {
    ///                     Some(v) => println!("var {} is set to {}", i, v),
    ///                     None => println!("var {} is left unassigned", i),
    ///                 }
    ///             }
    ///         }
    ///         SolvingResult::Unsatisfiable => println!("the problem has no model"),
    ///         SolvingResult::Unknown => println!("solver was not able to determine")
    ///     }
    /// }
    /// # try_to_solve(sat::default_solver().as_mut())
    /// ```
    fn solve(&mut self) -> SolvingResult;

    /// Solves the problem formed by the clauses added so far and the provided assumptions.
    ///
    /// This function can return a positive result (satisfiable, with a model), a negative result (unsatisfiable) or a value indicating the solver was not able to check the satisfiability of the underlying formula.
    /// See the [SolvingResult] documentation for more information.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::sat::{self, Literal, SatSolver, SolvingResult};
    /// fn try_to_solve_under_assumptions(s: &mut dyn SatSolver, assumptions: &[Literal]) {
    ///     match s.solve_under_assumptions(assumptions) {
    ///         SolvingResult::Satisfiable(assignment) => {
    ///             println!("a model was found for the problem with literals {:?}", assumptions);
    ///             for i in 1..s.n_vars() {
    ///                 match assignment.value_of(i) {
    ///                     Some(v) => println!("var {} is set to {}", i, v),
    ///                     None => println!("var {} is left unassigned", i),
    ///                 }
    ///             }
    ///         }
    ///         SolvingResult::Unsatisfiable => println!(
    ///             "the problem has no model with literals {:?}",
    ///             assumptions
    ///         ),
    ///         SolvingResult::Unknown => println!("solver was not able to determine")
    ///     }
    /// }
    /// # try_to_solve_under_assumptions(sat::default_solver().as_mut(), &[])
    fn solve_under_assumptions(&mut self, assumptions: &[Literal]) -> SolvingResult;

    /// Returns the number of variables defined so far.
    ///
    /// This number is equal to the highest variable identifier used in added clauses.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::sat::{self, Literal};
    /// let mut solver = sat::default_solver();
    /// assert_eq!(0, solver.n_vars());
    /// solver.add_clause(vec![Literal::from(1), Literal::from(-2)]);
    /// assert_eq!(2, solver.n_vars());
    /// ```
    fn n_vars(&self) -> usize;

    /// Adds a listener to this SAT solver.
    fn add_listener(&mut self, listener: Box<dyn SolvingListener>);

    /// Creates all the variables from 1 to the given value, if needed.
    fn reserve(&mut self, new_max_id: usize);
}

/// An interface for objects listening SAT solver activity.
pub trait SolvingListener {
    /// Advises the listener a SAT solving will start with the count of variables and clauses involved.
    fn solving_start(&self, n_vars: usize, n_clauses: usize);

    /// Advises the listener the current solving operation ended, providing the result.
    fn solving_end(&self, result: &SolvingResult);
}

/// Returns the default SAT solver.
///
/// This is currently the [CadicalSolver].
pub fn default_solver() -> Box<dyn SatSolver> {
    Box::<CadicalSolver>::default()
}

/// The type of solver factories.
///
/// SAT solver factories are functions without parameters that return a SAT solver.
pub type SatSolverFactoryFn = dyn Fn() -> Box<dyn SatSolver>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_var_from_pos() {
        let v = Variable::from(1);
        assert_eq!(1, usize::from(v))
    }

    #[test]
    #[allow(unused_must_use)]
    #[should_panic]
    fn test_var_from_null() {
        Variable::from(0);
    } // kcov-ignore

    #[test]
    #[allow(unused_must_use)]
    #[should_panic]
    fn test_var_from_neg() {
        Variable::from(-1);
    } // kcov-ignore

    #[test]
    fn test_lit_from_pos() {
        let l = Literal::from(1);
        assert_eq!(1, isize::from(l))
    }

    #[test]
    #[allow(unused_must_use)]
    #[should_panic]
    fn test_lit_from_null() {
        Literal::from(0);
    } // kcov-ignore

    #[test]
    fn test_lit_from_neg() {
        let l = Literal::from(-1);
        assert_eq!(-1, isize::from(l))
    }

    #[test]
    fn test_solving_result_unwrap_model_some() {
        assert_eq!(
            Some(Assignment::new(vec![])),
            SolvingResult::Satisfiable(Assignment::new(vec![])).unwrap_model()
        );
    }

    #[test]
    fn test_solving_result_unwrap_model_none() {
        assert_eq!(None, SolvingResult::Unsatisfiable.unwrap_model());
    }

    #[test]
    #[should_panic]
    fn test_solving_result_unwrap_model_unknown() {
        SolvingResult::Unknown.unwrap_model();
    } // kcov-ignore

    #[test]
    fn test_negate_lit() {
        assert_eq!(Literal::from(-1), Literal::from(1).negate());
        assert_eq!(Literal::from(1), Literal::from(-1).negate());
    }
}
