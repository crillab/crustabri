use assert_cmd::Command;
use predicates::prelude::predicate;

fn test_authors(cargo_bin: &str) {
    let app_name = option_env!("CARGO_PKG_NAME").unwrap_or("unknown app name");
    let app_version = option_env!("CARGO_PKG_VERSION").unwrap_or("unknown version");
    let authors = option_env!("CARGO_PKG_AUTHORS")
        .map(|v| v.replace(':', ", "))
        .unwrap_or_else(|| "unknown authors".to_string());
    let expected = format!("{} {}\n{}\n", app_name, app_version, authors);
    let mut cmd = Command::cargo_bin(cargo_bin).unwrap();
    cmd.assert()
        .success()
        .stdout(predicate::eq(expected.as_str()));
}

#[test]
fn test_iccma23() {
    test_authors("scalop_iccma23")
}
