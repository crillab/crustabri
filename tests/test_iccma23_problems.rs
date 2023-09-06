use assert_cmd::Command;
use crustabri::aa::Query;
use predicates::{reflection::PredicateReflection, Predicate};
use std::fmt::Display;

fn test_problems(cargo_bin: &str) {
    let mut cmd = Command::cargo_bin(cargo_bin).unwrap();
    cmd.arg("--problems");
    cmd.assert().success().stdout(CheckProblemsPredicate);
}

struct CheckProblemsPredicate;

impl Display for CheckProblemsPredicate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "CheckProblemsPredicate")
    }
}

impl PredicateReflection for CheckProblemsPredicate {
    fn parameters<'a>(
        &'a self,
    ) -> Box<dyn Iterator<Item = predicates::reflection::Parameter<'a>> + 'a> {
        let params = vec![];
        Box::new(params.into_iter())
    }

    fn children<'a>(&'a self) -> Box<dyn Iterator<Item = predicates::reflection::Child<'a>> + 'a> {
        let params = vec![];
        Box::new(params.into_iter())
    }
}

impl Predicate<[u8]> for CheckProblemsPredicate {
    fn eval(&self, content: &[u8]) -> bool {
        let mut str_content = String::from_utf8(content.to_vec()).unwrap();
        if !str_content.starts_with('[') || !str_content.ends_with("]\n") {
            return false;
        }
        str_content.remove(0);
        str_content.remove(str_content.len() - 1);
        str_content.remove(str_content.len() - 1);
        let mut actual_problems = str_content.split(',').collect::<Vec<&str>>();
        actual_problems.sort_unstable();
        let mut expected_problems = Query::iter_problem_strings().collect::<Vec<String>>();
        expected_problems.sort_unstable();
        expected_problems == actual_problems
    }
}

#[test]
fn test_iccma23() {
    test_problems("crustabri_iccma23")
}
