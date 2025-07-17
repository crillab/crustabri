use assert_cmd::Command;
use assert_fs::{prelude::FileWriteStr, NamedTempFile};
use predicates::{
    prelude::{predicate, PredicateBooleanExt},
    BoxPredicate,
};

const INSTANCE: &str = r#"p af 4
1 2
1 3
2 1
2 3
3 4
4 3
"#;

fn test_answer_for_track(
    track: &str,
    possible_answers: &[&'static str],
    additional_arg: Option<&str>,
) -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track_and_instance(INSTANCE, track, possible_answers, additional_arg)
}

fn test_answer_for_track_and_instance(
    instance: &str,
    track: &str,
    possible_answers: &[&'static str],
    additional_arg: Option<&str>,
) -> Result<(), Box<dyn std::error::Error>> {
    let file = NamedTempFile::new("test_instance.aa")?;
    file.write_str(instance)?;
    let mut cmd = Command::cargo_bin("scalop_iccma23")?;
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
fn test_complete_se() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track(
        "SE-CO",
        &["w\n", "w 1 4\n", "w 4 1\n", "w 2 4\n", "w 4 2\n"],
        None,
    )
}

#[test]
fn test_complete_dc_1() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("DC-CO", &["YES\nw 1 4\n", "YES\nw 4 1\n"], Some("1"))
}

#[test]
fn test_complete_dc_2() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("DC-CO", &["YES\nw 2 4\n", "YES\nw 4 2\n"], Some("2"))
}

#[test]
fn test_complete_dc_3() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("DC-CO", &["NO\n"], Some("3"))
}

#[test]
fn test_complete_dc_4() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track(
        "DC-CO",
        &[
            "YES\nw 1 4\n",
            "YES\nw 4 1\n",
            "YES\nw 2 4\n",
            "YES\nw 4 2\n",
        ],
        Some("4"),
    )
}

#[test]
fn test_complete_ds_1() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track(
        "DS-CO",
        &["NO\nw\n", "NO\nw 2 4\n", "NO\nw 4 2\n"],
        Some("1"),
    )
}

#[test]
fn test_complete_ds_2() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track(
        "DS-CO",
        &["NO\nw\n", "NO\nw 1 4\n", "NO\nw 4 1\n"],
        Some("2"),
    )
}

#[test]
fn test_complete_ds_3() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track(
        "DS-CO",
        &[
            "NO\nw\n",
            "NO\nw 2 4\n",
            "NO\nw 4 2\n",
            "NO\nw 1 4\n",
            "NO\nw 4 1\n",
        ],
        Some("3"),
    )
}

#[test]
fn test_complete_ds_4() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("DS-CO", &["NO\nw\n"], Some("4"))
}

#[test]
fn test_preferred_se() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("SE-PR", &["w 1 4\n", "w 4 1\n", "w 2 4\n", "w 4 2\n"], None)
}

#[test]
fn test_preferred_dc_1() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("DC-PR", &["YES\nw 1 4\n", "YES\nw 4 1\n"], Some("1"))
}

#[test]
fn test_preferred_dc_2() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("DC-PR", &["YES\nw 2 4\n", "YES\nw 4 2\n"], Some("2"))
}

#[test]
fn test_preferred_dc_3() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("DC-PR", &["NO\n"], Some("3"))
}

#[test]
fn test_preferred_dc_4() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track(
        "DC-PR",
        &[
            "YES\nw 1 4\n",
            "YES\nw 4 1\n",
            "YES\nw 2 4\n",
            "YES\nw 4 2\n",
        ],
        Some("4"),
    )
}

#[test]
fn test_preferred_ds_1() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("DS-PR", &["NO\nw 2 4\n", "NO\nw 4 2\n"], Some("1"))
}

#[test]
fn test_preferred_ds_2() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("DS-PR", &["NO\nw 1 4\n", "NO\nw 4 1\n"], Some("2"))
}

#[test]
fn test_preferred_ds_3() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track(
        "DS-PR",
        &["NO\nw 2 4\n", "NO\nw 4 2\n", "NO\nw 1 4\n", "NO\nw 4 1\n"],
        Some("3"),
    )
}

#[test]
fn test_preferred_ds_4() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("DS-PR", &["YES\n"], Some("4"))
}

#[test]
fn test_stable_se() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("SE-ST", &["w 1 4\n", "w 4 1\n", "w 2 4\n", "w 4 2\n"], None)
}

#[test]
fn test_stable_dc_1() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("DC-ST", &["YES\nw 1 4\n", "YES\nw 4 1\n"], Some("1"))
}

#[test]
fn test_stable_dc_2() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("DC-ST", &["YES\nw 2 4\n", "YES\nw 4 2\n"], Some("2"))
}

#[test]
fn test_stable_dc_3() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("DC-ST", &["NO\n"], Some("3"))
}

#[test]
fn test_stable_dc_4() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track(
        "DC-ST",
        &[
            "YES\nw 1 4\n",
            "YES\nw 4 1\n",
            "YES\nw 2 4\n",
            "YES\nw 4 2\n",
        ],
        Some("4"),
    )
}

#[test]
fn test_stable_ds_1() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("DS-ST", &["NO\nw 2 4\n", "NO\nw 4 2\n"], Some("1"))
}

#[test]
fn test_stable_ds_2() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("DS-ST", &["NO\nw 1 4\n", "NO\nw 4 1\n"], Some("2"))
}

#[test]
fn test_stable_ds_3() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track(
        "DS-ST",
        &["NO\nw 2 4\n", "NO\nw 4 2\n", "NO\nw 1 4\n", "NO\nw 4 1\n"],
        Some("3"),
    )
}

#[test]
fn test_stable_ds_4() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("DS-ST", &["YES\n"], Some("4"))
}

#[test]
fn test_semistable_se() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track(
        "SE-SST",
        &["w 1 4\n", "w 4 1\n", "w 2 4\n", "w 4 2\n"],
        None,
    )
}

#[test]
fn test_semistable_dc_1() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("DC-SST", &["YES\nw 1 4\n", "YES\nw 4 1\n"], Some("1"))
}

#[test]
fn test_semistable_dc_2() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("DC-SST", &["YES\nw 2 4\n", "YES\nw 4 2\n"], Some("2"))
}

#[test]
fn test_semistable_dc_3() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("DC-SST", &["NO\n"], Some("3"))
}

#[test]
fn test_semistable_dc_4() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track(
        "DC-SST",
        &[
            "YES\nw 1 4\n",
            "YES\nw 4 1\n",
            "YES\nw 2 4\n",
            "YES\nw 4 2\n",
        ],
        Some("4"),
    )
}

#[test]
fn test_semistable_ds_1() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("DS-SST", &["NO\nw 2 4\n", "NO\nw 4 2\n"], Some("1"))
}

#[test]
fn test_semistable_ds_2() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("DS-SST", &["NO\nw 1 4\n", "NO\nw 4 1\n"], Some("2"))
}

#[test]
fn test_semistable_ds_3() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track(
        "DS-SST",
        &["NO\nw 2 4\n", "NO\nw 4 2\n", "NO\nw 1 4\n", "NO\nw 4 1\n"],
        Some("3"),
    )
}

#[test]
fn test_semistable_ds_4() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("DS-SST", &["YES\n"], Some("4"))
}

#[test]
fn test_stage_se() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track(
        "SE-STG",
        &["w 1 4\n", "w 4 1\n", "w 2 4\n", "w 4 2\n"],
        None,
    )
}

#[test]
fn test_stage_dc_1() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("DC-STG", &["YES\nw 1 4\n", "YES\nw 4 1\n"], Some("1"))
}

#[test]
fn test_stage_dc_2() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("DC-STG", &["YES\nw 2 4\n", "YES\nw 4 2\n"], Some("2"))
}

#[test]
fn test_stage_dc_3() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("DC-STG", &["NO\n"], Some("3"))
}

#[test]
fn test_stage_dc_4() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track(
        "DC-STG",
        &[
            "YES\nw 1 4\n",
            "YES\nw 4 1\n",
            "YES\nw 2 4\n",
            "YES\nw 4 2\n",
        ],
        Some("4"),
    )
}

#[test]
fn test_stage_ds_1() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("DS-STG", &["NO\nw 2 4\n", "NO\nw 4 2\n"], Some("1"))
}

#[test]
fn test_stage_ds_2() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("DS-STG", &["NO\nw 1 4\n", "NO\nw 4 1\n"], Some("2"))
}

#[test]
fn test_stage_ds_3() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track(
        "DS-STG",
        &["NO\nw 2 4\n", "NO\nw 4 2\n", "NO\nw 1 4\n", "NO\nw 4 1\n"],
        Some("3"),
    )
}

#[test]
fn test_stage_ds_4() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("DS-STG", &["YES\n"], Some("4"))
}

#[test]
fn test_ideal_se() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("SE-ID", &["w 4\n"], None)
}

#[test]
fn test_ideal_dc_1() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("DC-ID", &["NO\n"], Some("1"))
}

#[test]
fn test_ideal_dc_2() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("DC-ID", &["NO\n"], Some("2"))
}

#[test]
fn test_ideal_dc_3() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("DC-ID", &["NO\n"], Some("3"))
}

#[test]
fn test_ideal_dc_4() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("DC-ID", &["YES\nw 4\n"], Some("4"))
}

#[test]
fn test_ideal_ds_1() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("DS-ID", &["NO\nw 4\n"], Some("1"))
}

#[test]
fn test_ideal_ds_2() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("DS-ID", &["NO\nw 4\n"], Some("2"))
}

#[test]
fn test_ideal_ds_3() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("DS-ID", &["NO\nw 4\n"], Some("3"))
}

#[test]
fn test_ideal_ds_4() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track("DS-ID", &["YES\n"], Some("4"))
}

#[test]
fn test_stg_se_no_constraints() -> Result<(), Box<dyn std::error::Error>> {
    test_answer_for_track_and_instance(
        "p af 2",
        "DC-STG",
        &["YES\nw 1 2\n", "YES\nw 2 1\n"],
        Some("1"),
    )
}
