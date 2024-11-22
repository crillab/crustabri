use super::{
    app_helper::AppHelper, command::Command, AuthorsCommand, CheckCommand, EncodeToSatCommand,
    ProblemsCommand, SolveCommand,
};
use anyhow::{Context, Result};
use clap::Arg;
use crustabri::{aa::AAFramework, io::InstanceReader, utils::LabelType};
use log::{info, warn};
use std::{
    fs::{self, File},
    io::{BufReader, Read},
    path::PathBuf,
};

pub(crate) fn create_app_helper() -> AppHelper<'static> {
    let app_name = option_env!("CARGO_PKG_NAME").unwrap_or("unknown app name");
    let app_version = option_env!("CARGO_PKG_VERSION").unwrap_or("unknown version");
    let authors = option_env!("CARGO_PKG_AUTHORS").unwrap_or("unknown authors");
    let mut app = AppHelper::new(
        app_name,
        app_version,
        authors,
        "Crustabri, an abstract argumentation solver.",
    );
    let commands: Vec<Box<dyn Command>> = vec![
        Box::new(AuthorsCommand::new(app_name, app_version, authors)),
        Box::new(CheckCommand::new()),
        Box::new(EncodeToSatCommand::new()),
        Box::new(ProblemsCommand::new()),
        Box::new(SolveCommand::new()),
    ];
    for c in commands {
        app.add_command(c);
    }
    app
}

pub(crate) const ARG_INPUT: &str = "INPUT";

pub(crate) fn input_args() -> Arg<'static, 'static> {
    Arg::with_name(ARG_INPUT)
        .short("f")
        .empty_values(false)
        .multiple(false)
        .help("the input file that contains the AF")
        .required(true)
}

pub(crate) const ARG_PROBLEM: &str = "PROBLEM";
pub(crate) const ARG_ARG: &str = "ARG";

pub(crate) fn problem_args() -> Vec<Arg<'static, 'static>> {
    vec![
        Arg::with_name(ARG_PROBLEM)
            .short("p")
            .empty_values(false)
            .multiple(false)
            .help("the problem to solve")
            .required(true),
        Arg::with_name(ARG_ARG)
            .short("a")
            .empty_values(false)
            .multiple(false)
            .help("the argument (for DC/DS queries)")
            .required(false),
    ]
}

pub(crate) const ARG_READER: &str = "READER";

pub(crate) fn reader_arg() -> Arg<'static, 'static> {
    Arg::with_name(ARG_READER)
        .short("r")
        .long("reader")
        .empty_values(false)
        .multiple(false)
        .possible_values(&["apx", "iccma23", "iccma23_aba"])
        .default_value("iccma23")
        .help("the input file format")
        .required(false)
}

pub(crate) const ARG_ENCODING: &str = "ENCODING";

pub(crate) fn encoding_arg() -> Arg<'static, 'static> {
    Arg::with_name(ARG_ENCODING)
        .long("encoding")
        .empty_values(false)
        .multiple(false)
        .possible_values(&["aux_var", "exp", "hybrid"])
        .help("the SAT encoding to use (not relevant for ST semantics)")
        .required(false)
}

pub(crate) fn read_file_path<T>(
    file_path: &str,
    reader: &mut dyn InstanceReader<T>,
) -> Result<AAFramework<T>>
where
    T: LabelType,
{
    reader.add_warning_handler(Box::new(|line, msg| warn!("at line {}: {}", line, msg)));
    let af = read_file_path_with(file_path, &|r| reader.read(r))?;
    info!(
        "the argumentation framework has {} argument(s) and {} attack(s)",
        af.n_arguments(),
        af.n_attacks(),
    );
    Ok(af)
}

pub(crate) fn read_file_path_with<F, R>(file_path: &str, reader: &F) -> Result<R>
where
    F: Fn(&mut dyn Read) -> Result<R>,
{
    let canonicalized = canonicalize_file_path(file_path)?;
    info!("reading input file {:?}", canonicalized);
    let mut file_reader = BufReader::new(File::open(canonicalized)?);
    (reader)(&mut file_reader)
}

/// Canonicalize a path given by the user.
pub(crate) fn canonicalize_file_path(file_path: &str) -> Result<PathBuf> {
    fs::canonicalize(PathBuf::from(file_path))
        .with_context(|| format!(r#"while opening file "{}""#, file_path))
}

#[cfg(feature = "iccma")]
#[allow(dead_code)]
pub(crate) fn translate_args_for_iccma() -> Vec<std::ffi::OsString> {
    use crate::app::cli_manager;

    const COMMON_ARGS: [&str; 2] = ["--logging-level", "off"];

    let real_args = std::env::args_os()
        .skip(1)
        .collect::<Vec<std::ffi::OsString>>();
    let new_args: Vec<std::ffi::OsString> = if real_args.is_empty() {
        std::iter::once("authors".to_string().into())
            .chain(COMMON_ARGS.iter().map(|s| s.into()))
            .collect()
    } else if real_args == ["--problems"] {
        std::iter::once("problems".to_string().into())
            .chain(COMMON_ARGS.iter().map(|s| s.into()))
            .collect()
    } else {
        let mut new_args: Vec<std::ffi::OsString> = std::iter::once("solve".to_string().into())
            .chain(real_args)
            .chain(
                ["--with-certificate", "--reader", "iccma23"]
                    .iter()
                    .map(|s| s.into()),
            )
            .collect();
        if std::env::args_os().all(|arg| arg.to_str().unwrap() != "--logging-level") {
            let fake_app =
                clap::App::new(option_env!("CARGO_PKG_NAME").unwrap_or("unknown app name"))
                    .arg(input_args())
                    .args(&problem_args())
                    .arg(cli_manager::logging_level_cli_arg_with_default_value("off"));
            let fake_app_matches = fake_app.get_matches();
            let logging_level = fake_app_matches
                .value_of(cli_manager::APP_HELPER_LOGGING_LEVEL_ARG)
                .unwrap()
                .to_string();
            new_args.append(&mut vec!["--logging-level".into(), logging_level.into()]);
        }
        new_args
    };
    std::iter::once(std::env::args_os().next().unwrap())
        .chain(new_args)
        .collect()
}
