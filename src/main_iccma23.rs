use anyhow::{anyhow, Context, Result};
use app::common::ARG_INPUT;
use clap::{App, ArgMatches};
use std::{
    ffi::OsString,
    fs::File,
    io::{BufRead, BufReader},
};

mod app;

const COMMON_ARGS: [&str; 2] = ["--logging-level", "off"];

fn main() {
    let app = app::common::create_app_helper();
    let fake_params = translate_args_os_params();
    app.launch_app_with_args(fake_params);
}

fn translate_args_os_params() -> Vec<OsString> {
    let real_args = std::env::args_os().skip(1).collect::<Vec<OsString>>();
    let new_args: Box<dyn Iterator<Item = OsString>> = if real_args.is_empty() {
        Box::new(
            std::iter::once("authors".to_string().into())
                .chain(COMMON_ARGS.iter().map(|s| s.into())),
        )
    } else if real_args == ["--problems"] {
        Box::new(
            std::iter::once("problems".to_string().into())
                .chain(COMMON_ARGS.iter().map(|s| s.into())),
        )
    } else {
        let fake_app = App::new(option_env!("CARGO_PKG_NAME").unwrap_or("unknown app name"))
            .arg(app::common::input_args())
            .args(&app::common::problem_args());
        let fake_app_matches = fake_app.get_matches();
        if is_aba(&fake_app_matches).is_ok_and(|b| b) {
            Box::new(
                std::iter::once("solve-aba".to_string().into())
                    .chain(real_args)
                    .chain(COMMON_ARGS.iter().map(|s| s.into())),
            )
        } else {
            Box::new(
                std::iter::once("solve".to_string().into())
                    .chain(real_args)
                    .chain(COMMON_ARGS.iter().map(|s| s.into()))
                    .chain(
                        ["--with-certificate", "--reader", "iccma23"]
                            .iter()
                            .map(|s| s.into()),
                    ),
            )
        }
    };
    std::iter::once(std::env::args_os().next().unwrap())
        .chain(new_args)
        .collect()
}

fn is_aba(arg_matches: &ArgMatches) -> Result<bool> {
    let path = arg_matches.value_of(ARG_INPUT).unwrap();
    let mut reader = BufReader::new(File::open(path).context("while opening input file")?);
    let mut buffer = String::new();
    reader
        .read_line(&mut buffer)
        .context("while reading first line of input file")?;
    let mut words = buffer.split_whitespace();
    if words.next() != Some("p") {
        return Err(anyhow!(r#"first word of input file must be "p""#));
    }
    let is_aba = match words.next() {
        Some("af") => false,
        Some("aba") => true,
        Some(_) | None => return Err(anyhow!(r#"first word of input file must be "p""#)),
    };
    Ok(is_aba)
}
