use super::{
    app_helper::AppHelper, command::Command, AuthorsCommand, CheckCommand, EncodeToSatCommand,
    ProblemsCommand, SolveABACommand, SolveCommand,
};
use anyhow::{Context, Result};
use clap::{Arg, ArgMatches};
use crustabri::{
    aa::AAFramework,
    io::InstanceReader,
    sat::{self, ExternalSatSolver, SatSolver, SatSolverFactoryFn, SolvingListener, SolvingResult},
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

pub(crate) const ARG_EXTERNAL_SAT_SOLVER: &str = "EXTERNAL_SAT_SOLVER";
pub(crate) const ARG_EXTERNAL_SAT_SOLVER_OPTIONS: &str = "EXTERNAL_SAT_SOLVER_OPTIONS";

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
    ]
}

pub(crate) fn create_sat_solver_factory(arg_matches: &ArgMatches<'_>) -> Box<SatSolverFactoryFn> {
    let external_solver = arg_matches
        .value_of(ARG_EXTERNAL_SAT_SOLVER)
        .map(|s| s.to_string());
    let external_solver_options = arg_matches
        .values_of(ARG_EXTERNAL_SAT_SOLVER_OPTIONS)
        .map(|v| v.map(|o| o.to_string()).collect::<Vec<String>>())
        .unwrap_or_default();
    if let Some(s) = external_solver {
        info!("using {} for problems requiring a SAT solver", s);
        Box::new(move || {
            let mut s = ExternalSatSolver::new(s.to_string(), external_solver_options.clone());
            s.add_listener(Box::<SatSolvingLogger>::default());
            Box::new(s)
        })
    } else {
        info!("using the default SAT solver for problems requiring a SAT solver");
        Box::new(|| {
            let mut s = sat::default_solver();
            s.add_listener(Box::<SatSolvingLogger>::default());
            s
        })
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
