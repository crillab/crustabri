use super::{
    app_helper::AppHelper, command::Command, AuthorsCommand, CheckCommand, EncodeToSatCommand,
    ProblemsCommand, SolveABACommand, SolveCommand,
};
use anyhow::{Context, Result};
use clap::{Arg, ArgMatches};
use crustabri::{
    aa::AAFramework,
    io::InstanceReader,
    sat::{
        DefaultSatSolverFactory, ExternalSatSolverFactory, IpasirSatSolverFactory,
        SatSolverFactory, SolvingListener, SolvingResult,
    },
    utils::LabelType,
};
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
        Box::new(SolveABACommand::new()),
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

const ARG_EXTERNAL_SAT_SOLVER: &str = "EXTERNAL_SAT_SOLVER";
const ARG_EXTERNAL_SAT_SOLVER_OPTIONS: &str = "EXTERNAL_SAT_SOLVER_OPTIONS";
const ARG_IPASIR_LIBRARY: &str = "ARG_IPASIR_LIBRARY";

pub(crate) fn external_sat_solver_args() -> Vec<Arg<'static, 'static>> {
    vec![
        Arg::with_name(ARG_EXTERNAL_SAT_SOLVER)
            .long("external-sat-solver")
            .empty_values(false)
            .multiple(false)
            .help("a path to an external SAT solver to replace the embedded one")
            .required(false),
        Arg::with_name(ARG_EXTERNAL_SAT_SOLVER_OPTIONS)
            .long("external-sat-solver-opt")
            .requires(ARG_EXTERNAL_SAT_SOLVER)
            .empty_values(false)
            .multiple(true)
            .help("a option to give to the external SAT solver")
            .required(false),
        Arg::with_name(ARG_IPASIR_LIBRARY)
            .long("ipasir-library")
            .empty_values(false)
            .multiple(false)
            .help("a path to a shared library containing an IPASIR compatible SAT solver")
            .required(false)
            .conflicts_with(ARG_EXTERNAL_SAT_SOLVER),
    ]
}

pub(crate) fn create_sat_solver_factory(
    arg_matches: &ArgMatches<'_>,
) -> Result<Box<dyn SatSolverFactory>> {
    let external_solver = arg_matches
        .value_of(ARG_EXTERNAL_SAT_SOLVER)
        .map(|s| s.to_string());
    let external_solver_options = arg_matches
        .values_of(ARG_EXTERNAL_SAT_SOLVER_OPTIONS)
        .map(|v| v.map(|o| o.to_string()).collect::<Vec<String>>())
        .unwrap_or_default();
    let ipasir_library = arg_matches
        .value_of(ARG_IPASIR_LIBRARY)
        .map(|s| s.to_string());
    if let Some(s) = external_solver {
        let path = canonicalize_file_path(&s)?;
        info!("using {path:?} for problems requiring a SAT solver");
        let mut factory = ExternalSatSolverFactory::new(
            path.to_str().unwrap().to_string(),
            external_solver_options,
        );
        factory.add_solver_listener(Box::new(|| {
            Box::<SatSolvingLogger>::default() as Box<dyn SolvingListener>
        }));
        Ok(Box::new(factory))
    } else if let Some(s) = ipasir_library {
        let path = canonicalize_file_path(&s)?;
        info!("using {path:?} IPASIR library for problems requiring a SAT solver");
        let factory = IpasirSatSolverFactory::new(path.to_str().unwrap());
        info!("IPASIR signature is {}", factory.ipasir_signature());
        let result = Box::new(factory);
        Ok(result)
    } else {
        info!("using the default SAT solver for problems requiring a SAT solver");
        Ok(Box::new(DefaultSatSolverFactory))
    }
}

#[derive(Default)]
struct SatSolvingLogger;

impl SolvingListener for SatSolvingLogger {
    fn solving_start(&self, n_vars: usize, n_clauses: usize) {
        info!(
            "launching SAT solver on an instance with {} variables and {} clauses",
            n_vars, n_clauses
        );
    }

    fn solving_end(&self, result: &SolvingResult) {
        let r = match result {
            SolvingResult::Satisfiable(_) => "SAT",
            SolvingResult::Unsatisfiable => "UNSAT",
            SolvingResult::Unknown => "UNKNOWN",
        };
        info!("SAT solver ended with result {}", r);
    }
}

#[cfg(feature = "iccma")]
#[allow(dead_code)]
pub(crate) fn translate_args_for_iccma() -> Vec<std::ffi::OsString> {
    use crate::app::cli_manager::{self, APP_HELPER_LOGGING_LEVEL_ARG};

    const COMMON_ARGS: [&str; 2] = ["--logging-level", "off"];

    let mut real_args = std::env::args_os()
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
        let fake_app = clap::App::new(option_env!("CARGO_PKG_NAME").unwrap_or("unknown app name"))
            .arg(input_args())
            .args(&problem_args())
            .arg(cli_manager::logging_level_cli_arg_with_default_value("off"));
        let fake_app_matches = fake_app.get_matches();
        let mut new_args: Vec<std::ffi::OsString> = if is_aba(&fake_app_matches).is_ok_and(|b| b) {
            vec!["solve-aba".to_string().into()]
        } else {
            ["solve", "--with-certificate", "--reader", "iccma23"]
                .iter()
                .map(|s| s.into())
                .collect()
        };
        if !std::env::args_os().any(|arg| arg.to_str().unwrap().starts_with("--logging-level=")) {
            new_args.push("--logging-level".to_string().into());
            new_args.push(
                fake_app_matches
                    .value_of(APP_HELPER_LOGGING_LEVEL_ARG)
                    .unwrap()
                    .to_string()
                    .into(),
            );
        }
        new_args.append(&mut real_args);
        new_args
    };
    std::iter::once(std::env::args_os().next().unwrap())
        .chain(new_args)
        .collect()
}

#[cfg(feature = "iccma")]
#[allow(dead_code)]
fn is_aba(arg_matches: &ArgMatches) -> Result<bool> {
    use anyhow::anyhow;
    use std::io::BufRead;

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
