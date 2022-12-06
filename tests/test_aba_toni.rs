use assert_cmd::Command;
use assert_fs::{prelude::FileWriteStr, NamedTempFile};
use predicates::{
    prelude::{predicate, PredicateBooleanExt},
    BoxPredicate,
};

const INSTANCE: &str = r#"p aba 8
a 1
a 2
a 3
c 1 6
c 2 7
c 3 8
r 4 5 1
r 5
r 6 2 3
"#;

fn test_answer_for_track(
    track: &str,
    possible_answers: &[&str],
    additional_arg: Option<&str>,
) -> Result<(), Box<dyn std::error::Error>> {
    let file = NamedTempFile::new("toni.aba")?;
    file.write_str(INSTANCE)?;
    let mut cmd = Command::cargo_bin("crustabri_iccma23_aba")?;
    cmd.arg("-f").arg(file.path()).arg("-p").arg(track);
    if let Some(a) = additional_arg {
        cmd.arg("-a").arg(a);
    }
    let mut pred = BoxPredicate::new(predicate::never());
    for a in possible_answers {
        pred = BoxPredicate::new(pred.or(predicate::str::contains(*a)));
    }
    cmd.assert().success().stdout(pred);
    file.close().unwrap();
    Ok(())
}

#[test]
fn test_complete_se() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("SE-CO", &["w 2 3\n", "w 3 2\n"], None)
}

#[test]
fn test_complete_dc_1() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("DC-CO", &["NO"], Some("1"))
}

#[test]
fn test_complete_dc_2() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("DC-CO", &["YES"], Some("2"))
}

#[test]
fn test_complete_dc_3() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("DC-CO", &["YES"], Some("3"))
}

#[test]
fn test_complete_ds_1() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("DS-CO", &["NO"], Some("1"))
}

#[test]
fn test_complete_ds_2() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("DS-CO", &["YES"], Some("2"))
}

#[test]
fn test_complete_ds_3() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("DS-CO", &["YES"], Some("3"))
}

#[test]
fn test_preferred_se() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("SE-PR", &["w 2 3\n", "w 3 2\n"], None)
}

#[test]
fn test_preferred_dc_1() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("DC-PR", &["NO"], Some("1"))
}

#[test]
fn test_preferred_dc_2() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("DC-PR", &["YES"], Some("2"))
}

#[test]
fn test_preferred_dc_3() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("DC-PR", &["YES"], Some("3"))
}

#[test]
fn test_preferred_ds_1() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("DS-PR", &["NO"], Some("1"))
}

#[test]
fn test_preferred_ds_2() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("DS-PR", &["YES"], Some("2"))
}

#[test]
fn test_preferred_ds_3() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("DS-PR", &["YES"], Some("3"))
}

#[test]
fn test_stable_se() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("SE-ST", &["w 2 3\n", "w 3 2\n"], None)
}

#[test]
fn test_stable_dc_1() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("DC-ST", &["NO"], Some("1"))
}

#[test]
fn test_stable_dc_2() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("DC-ST", &["YES"], Some("2"))
}

#[test]
fn test_stable_dc_3() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("DC-ST", &["YES"], Some("3"))
}

#[test]
fn test_stable_ds_1() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("DS-ST", &["NO"], Some("1"))
}

#[test]
fn test_stable_ds_2() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("DS-ST", &["YES"], Some("2"))
}

#[test]
fn test_stable_ds_3() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("DS-ST", &["YES"], Some("3"))
}
