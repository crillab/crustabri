use super::{
    sat_solver::{SolvingListener, SolvingResult},
    Assignment, Literal, SatSolver,
};
use std::io::{BufRead, BufReader, Cursor, Read};

type SolvingFn = dyn Fn(DimacsInstanceRead) -> Box<dyn Read>;

pub struct DimacsInstanceRead {
    preamble: Cursor<String>,
    clauses: Cursor<String>,
    assumptions: Cursor<String>,
}

impl Read for DimacsInstanceRead {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        let r = self.preamble.read(buf)?;
        if r > 0 {
            return Ok(r);
        }
        let r = self.clauses.read(buf)?;
        if r > 0 {
            return Ok(r);
        }
        let r = self.assumptions.read(buf)?;
        if r > 0 {
            return Ok(r);
        }
        Ok(0)
    }
}

const DEFAULT_BUFFER_CAP: usize = 1 << 20;

pub struct BufferedSatSolver {
    n_vars: usize,
    n_clauses: usize,
    clauses: String,
    solving_fn: Box<SolvingFn>,
    listeners: Vec<Box<dyn SolvingListener>>,
}

impl BufferedSatSolver {
    pub fn new(solving_fn: Box<SolvingFn>) -> Self {
        Self {
            n_vars: 0,
            n_clauses: 0,
            clauses: String::with_capacity(DEFAULT_BUFFER_CAP),
            solving_fn,
            listeners: Vec::new(),
        }
    }
}

impl SatSolver for BufferedSatSolver {
    fn add_clause(&mut self, cl: Vec<Literal>) {
        cl.iter().for_each(|l| {
            self.n_vars = usize::max(self.n_vars, usize::from(l.var()));
            self.clauses.push_str(&format!("{} ", l));
        });
        self.clauses.push('0');
        self.clauses.push('\n');
        self.n_clauses += 1;
    }

    fn solve(&mut self) -> SolvingResult {
        self.solve_under_assumptions(&[])
    }

    fn solve_under_assumptions(&mut self, assumptions: &[Literal]) -> SolvingResult {
        self.listeners
            .iter()
            .for_each(|l| l.solving_start(self.n_vars(), self.n_clauses));
        let preamble = format!(
            "p cnf {} {}\n",
            self.n_vars,
            self.n_clauses + assumptions.len()
        );
        let assumptions =
            assumptions
                .iter()
                .map(|a| format!("{} 0\n", a))
                .fold(String::new(), |mut acc, a| {
                    acc.push_str(&a);
                    acc
                });
        let instance_reader = DimacsInstanceRead {
            assumptions: Cursor::new(assumptions),
            clauses: Cursor::new(self.clauses.clone()),
            preamble: Cursor::new(preamble),
        };
        let solver_output = BufReader::new((self.solving_fn)(instance_reader));
        let context = "error while reading solving function output in BufferedSatSolver";
        let mut status = None;
        let mut assignment = vec![None; self.n_vars];
        let mut assignment_line_seen = false;
        let mut assignment_line_end = false;
        for line in solver_output.lines().map(|r| match r {
            Ok(l) => l,
            Err(e) => panic!("{}: {}", context, e),
        }) {
            let mut set_status = |b| {
                if status.is_some() {
                    panic!("{}: multiple status lines", context)
                }
                status = Some(b);
            };
            if line == "s SATISFIABLE" {
                set_status(true);
            } else if line == "s UNSATISFIABLE" {
                set_status(false);
            } else if line.starts_with("v ") {
                assignment_line_seen = true;
                line.split_ascii_whitespace().skip(1).for_each(|w| {
                    let n = match w.parse::<isize>() {
                        Ok(n) => n,
                        Err(_) => panic!(r#"{}: "{}" is not a literal"#, context, w),
                    };
                    if n == 0 {
                        if assignment_line_end {
                            panic!("{}: multiple zeroes on value line", context)
                        } else {
                            assignment_line_end = true;
                        }
                    } else {
                        let v = n.unsigned_abs() - 1;
                        if v >= self.n_vars {
                            panic!("{}: a variable in value line is out of bounds", context)
                        }
                        assignment[v] = Some(n > 0);
                    }
                });
            } else if !line.starts_with("c ") && line != "c" && line != "v" && !line.is_empty() {
                panic!(r#"{}: unexpected line "{}""#, context, line)
            }
        }
        let solving_result = match status {
            Some(true) => {
                if assignment_line_seen {
                    SolvingResult::Satisfiable(Assignment::new(assignment))
                } else {
                    SolvingResult::Unknown
                }
            }
            Some(false) => SolvingResult::Unsatisfiable,
            None => SolvingResult::Unknown,
        };
        self.listeners
            .iter()
            .for_each(|l| l.solving_end(&solving_result));
        solving_result
    }

    fn n_vars(&self) -> usize {
        self.n_vars
    }

    fn add_listener(&mut self, listener: Box<dyn SolvingListener>) {
        self.listeners.push(listener);
    }

    fn reserve(&mut self, new_max_id: usize) {
        if new_max_id > self.n_vars {
            self.n_vars = new_max_id;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sat::sat_solver::clause;

    fn input_check_solving_fn(expected_input: &'static str) -> Box<SolvingFn> {
        Box::new(move |mut r| {
            let mut buffer = String::new();
            r.read_to_string(&mut buffer).unwrap();
            assert_eq!(expected_input, buffer);
            Box::new(&[] as &[u8])
        })
    }

    #[test]
    fn test_input_ok() {
        let expected = "p cnf 2 3\n1 2 0\n-1 -2 0\n1 0\n";
        let mut s = BufferedSatSolver::new(input_check_solving_fn(expected));
        s.add_clause(clause![1, 2]);
        s.add_clause(clause![-1, -2]);
        s.solve_under_assumptions(&[1.into()]);
    }

    fn fake_output_solving_fn(output: &'static str) -> Box<SolvingFn> {
        Box::new(|_| Box::new(output.as_bytes()))
    }

    #[test]
    fn test_output_sat_ok() {
        let solver_output = "s SATISFIABLE\nv -1 2 0\n";
        let mut s = BufferedSatSolver::new(fake_output_solving_fn(solver_output));
        s.add_clause(clause![-1, 2]);
        let assignment = s.solve().unwrap_model().unwrap();
        assert!(!assignment.value_of(1).unwrap());
        assert!(assignment.value_of(2).unwrap());
    }

    #[test]
    fn test_output_sat_ok_with_v_lines_without_lits() {
        let solver_output = "s SATISFIABLE\nv\nv -1 2 0\nv\n";
        let mut s = BufferedSatSolver::new(fake_output_solving_fn(solver_output));
        s.add_clause(clause![-1, 2]);
        let assignment = s.solve().unwrap_model().unwrap();
        assert!(!assignment.value_of(1).unwrap());
        assert!(assignment.value_of(2).unwrap());
    }

    #[test]
    fn test_output_sat_ok_multiple_v_lines() {
        let solver_output = "s SATISFIABLE\nv 1\nv 2\nv 0\n";
        let mut s = BufferedSatSolver::new(fake_output_solving_fn(solver_output));
        s.add_clause(clause![1, 2]);
        let assignment = s.solve().unwrap_model().unwrap();
        assert!(assignment.value_of(1).unwrap());
        assert!(assignment.value_of(2).unwrap());
    }

    #[test]
    fn test_output_sat_no_s_line() {
        let solver_output = "v 1 2 0\n";
        let mut s = BufferedSatSolver::new(fake_output_solving_fn(solver_output));
        s.add_clause(clause![1, 2]);
        assert_eq!(SolvingResult::Unknown, s.solve());
    }

    #[test]
    fn test_output_sat_no_v_line() {
        let solver_output = "s SATISFIABLE\n";
        let mut s = BufferedSatSolver::new(fake_output_solving_fn(solver_output));
        s.add_clause(clause![1, 2]);
        assert_eq!(SolvingResult::Unknown, s.solve());
    }

    #[test]
    #[should_panic(
        expected = "error while reading solving function output in BufferedSatSolver: a variable in value line is out of bounds"
    )]
    fn test_output_sat_var_out_of_bounds() {
        let solver_output = "s SATISFIABLE\nv 1 2 3 0\n";
        let mut s = BufferedSatSolver::new(fake_output_solving_fn(solver_output));
        s.add_clause(clause![1, 2]);
        s.solve();
    }

    #[test]
    #[should_panic(
        expected = r#"error while reading solving function output in BufferedSatSolver: "foo" is not a literal"#
    )]
    fn test_output_sat_not_a_var() {
        let solver_output = "s SATISFIABLE\nv 1 2 foo 0\n";
        let mut s = BufferedSatSolver::new(fake_output_solving_fn(solver_output));
        s.add_clause(clause![1, 2]);
        s.solve();
    }

    #[test]
    #[should_panic(
        expected = "error while reading solving function output in BufferedSatSolver: multiple status lines"
    )]
    fn test_output_sat_multiple_status_lines() {
        let solver_output = "s SATISFIABLE\ns SATISFIABLE\nv 1 2 3 0\n";
        let mut s = BufferedSatSolver::new(fake_output_solving_fn(solver_output));
        s.add_clause(clause![1, 2]);
        s.solve();
    }

    #[test]
    #[should_panic(
        expected = "error while reading solving function output in BufferedSatSolver: multiple zeroes on value line"
    )]
    fn test_output_sat_multiple_zeroes_in_v_lines() {
        let solver_output = "s SATISFIABLE\nv 1 0\nv 2 0\n";
        let mut s = BufferedSatSolver::new(fake_output_solving_fn(solver_output));
        s.add_clause(clause![1, 2]);
        s.solve();
    }

    #[test]
    fn test_output_unsat_ok() {
        let solver_output = "s UNSATISFIABLE\n";
        let mut s = BufferedSatSolver::new(fake_output_solving_fn(solver_output));
        s.add_clause(clause![1]);
        s.add_clause(clause![-1]);
        assert!(s.solve().unwrap_model().is_none());
    }

    #[test]
    fn test_output_comment() {
        let solver_output = "c foo\ns UNSATISFIABLE\n";
        let mut s = BufferedSatSolver::new(fake_output_solving_fn(solver_output));
        s.add_clause(clause![1]);
        s.add_clause(clause![-1]);
        assert!(s.solve().unwrap_model().is_none());
    }

    #[test]
    fn test_output_comment_with_no_message() {
        let solver_output = "c\ns UNSATISFIABLE\n";
        let mut s = BufferedSatSolver::new(fake_output_solving_fn(solver_output));
        s.add_clause(clause![1]);
        s.add_clause(clause![-1]);
        assert!(s.solve().unwrap_model().is_none());
    }

    #[test]
    fn test_output_no_s_line() {
        let solver_output = "";
        let mut s = BufferedSatSolver::new(fake_output_solving_fn(solver_output));
        s.add_clause(clause![1, 2]);
        assert_eq!(SolvingResult::Unknown, s.solve());
    }

    #[test]
    #[should_panic(
        expected = r#"error while reading solving function output in BufferedSatSolver: unexpected line "foo""#
    )]
    fn test_output_unexpected_line() {
        let solver_output = "foo\ns SATISFIABLE\nv 1 2 3 0\n";
        let mut s = BufferedSatSolver::new(fake_output_solving_fn(solver_output));
        s.add_clause(clause![1, 2]);
        s.solve();
    }
}
