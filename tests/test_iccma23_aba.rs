use assert_cmd::Command;
use assert_fs::{prelude::FileWriteStr, NamedTempFile};
use predicates::{
    prelude::{predicate, PredicateBooleanExt},
    BoxPredicate,
};

fn test_answer_for_track_and_instance(
    instance: &str,
    track: &str,
    possible_answers: &[&'static str],
    additional_arg: Option<&str>,
) -> Result<(), Box<dyn std::error::Error>> {
    let file = NamedTempFile::new("instance.aba")?;
    file.write_str(instance)?;
    let mut cmd = Command::cargo_bin("crustabri_iccma23_aba")?;
    cmd.arg("-f").arg(file.path()).arg("-p").arg(track);
    if let Some(a) = additional_arg {
        cmd.arg("-a").arg(a);
    }
    let mut pred: BoxPredicate<str> = BoxPredicate::new(predicate::never());
    for a in possible_answers {
        pred = BoxPredicate::new(pred.or(predicate::eq(*a)));
    }
    cmd.assert().success().stdout(pred);
    file.close().unwrap();
    Ok(())
}

#[test]
fn test_dc_co_assumption_is_its_own_contrary() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track_and_instance("p aba 1\na 1\nc 1 1\n", "DC-CO", &["NO\n"], Some("1"))
}

#[test]
fn test_se_st_assumption_is_its_own_contrary() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track_and_instance("p aba 1\na 1\nc 1 1\n", "SE-ST", &["NO\n"], None)
}
