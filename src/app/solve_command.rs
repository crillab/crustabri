use super::common;
use anyhow::{anyhow, Context, Result};
use crustabri::{
    AAFramework, Argument, AspartixWriter, CompleteSemanticsSolver, CredulousAcceptanceComputer,
    ExternalSatSolver, GroundedSemanticsSolver, PreferredSemanticsSolver, Query,
    SatSolverFactoryFn, Semantics, SingleExtensionComputer, SkepticalAcceptanceComputer,
    StableSemanticsSolver,
};
use crusti_app_helper::{
    info, logging_level_cli_arg, warn, AppSettings, Arg, ArgMatches, Command, SubCommand,
};

const CMD_NAME: &str = "solve";

const ARG_PROBLEM: &str = "PROBLEM";
const ARG_ARG: &str = "ARG";
const ARG_EXTERNAL_SAT_SOLVER: &str = "EXTERNAL_SAT_SOLVER";
const ARG_EXTERNAL_SAT_SOLVER_OPTIONS: &str = "EXTERNAL_SAT_SOLVER_OPTIONS";

pub(crate) struct SolveCommand;

impl SolveCommand {
    pub(crate) fn new() -> Self {
        SolveCommand
    }
}

impl<'a> Command<'a> for SolveCommand {
    fn name(&self) -> &str {
        CMD_NAME
    }

    fn clap_subcommand(&self) -> crusti_app_helper::App<'a, 'a> {
        SubCommand::with_name(CMD_NAME)
            .about("Solves an argumentation framework problem")
            .setting(AppSettings::DisableVersion)
            .arg(common::input_args())
            .arg(
                Arg::with_name(ARG_PROBLEM)
                    .short("p")
                    .empty_values(false)
                    .multiple(false)
                    .help("the problem to solve")
                    .required(true),
            )
            .arg(
                Arg::with_name(ARG_ARG)
                    .short("a")
                    .empty_values(false)
                    .multiple(false)
                    .help("the argument (for DC/DS queries)")
                    .required(false),
            )
            .args(&external_sat_solver_args())
            .arg(logging_level_cli_arg())
    }

    fn execute(&self, arg_matches: &crusti_app_helper::ArgMatches<'_>) -> Result<()> {
        let file = arg_matches.value_of(common::ARG_INPUT).unwrap();
        let af = common::read_aspartix_file_path(file)?;
        let arg = arg_matches
            .value_of(ARG_ARG)
            .map(|a| af.argument_set().get_argument(&a.to_string()))
            .transpose()
            .context("while parsing the argument passed to the command line")?;
        let (query, semantics) =
            crustabri::read_problem_string(arg_matches.value_of(ARG_PROBLEM).unwrap())?;
        check_arg_definition(query, &arg)?;
        match query {
            Query::SE => compute_one_extension(&af, semantics, arg_matches),
            Query::DC => check_credulous_acceptance(&af, semantics, arg.unwrap(), arg_matches),
            Query::DS => check_skeptical_acceptance(&af, semantics, arg.unwrap(), arg_matches),
        }
    }
}

fn external_sat_solver_args() -> Vec<Arg<'static, 'static>> {
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

fn check_arg_definition(query: Query, arg: &Option<&Argument<String>>) -> Result<()> {
    match query {
        Query::SE => {
            if arg.is_some() {
                warn!(
                    "unexpected argument on the command line (useless for query {})",
                    query.as_ref()
                );
            }
            Ok(())
        }
        Query::DC | Query::DS => {
            if arg.is_none() {
                Err(anyhow!(
                    "missing argument on the command line (required for query {})",
                    query.as_ref()
                ))
            } else {
                Ok(())
            }
        }
    }
}

fn compute_one_extension(
    af: &AAFramework<String>,
    semantics: Semantics,
    arg_matches: &ArgMatches<'_>,
) -> Result<()> {
    let mut solver: Box<dyn SingleExtensionComputer<String>> = match semantics {
        Semantics::GR | Semantics::CO => Box::new(GroundedSemanticsSolver::new(af)),
        Semantics::PR => Box::new(PreferredSemanticsSolver::new_with_sat_solver_factory(
            af,
            create_sat_solver_factory(arg_matches),
        )),
        Semantics::ST => Box::new(StableSemanticsSolver::new_with_sat_solver_factory(
            af,
            create_sat_solver_factory(arg_matches),
        )),
    };
    let writer = AspartixWriter::default();
    let mut out = std::io::stdout();
    match solver.compute_one_extension() {
        Some(ext) => writer.write_single_extension(&mut out, &ext),
        None => writer.write_no_extension(&mut out),
    }
}

fn check_credulous_acceptance(
    af: &AAFramework<String>,
    semantics: Semantics,
    arg: &Argument<String>,
    arg_matches: &ArgMatches<'_>,
) -> Result<()> {
    let mut solver: Box<dyn CredulousAcceptanceComputer<String>> = match semantics {
        Semantics::GR => Box::new(GroundedSemanticsSolver::new(af)),
        Semantics::CO | Semantics::PR => {
            Box::new(CompleteSemanticsSolver::new_with_sat_solver_factory(
                af,
                create_sat_solver_factory(arg_matches),
            ))
        }
        Semantics::ST => Box::new(StableSemanticsSolver::new_with_sat_solver_factory(
            af,
            create_sat_solver_factory(arg_matches),
        )),
    };
    let writer = AspartixWriter::default();
    let mut out = std::io::stdout();
    let acceptance_status = solver.is_credulously_accepted(arg);
    writer.write_acceptance_status(&mut out, acceptance_status)
}

fn check_skeptical_acceptance(
    af: &AAFramework<String>,
    semantics: Semantics,
    arg: &Argument<String>,
    arg_matches: &ArgMatches<'_>,
) -> Result<()> {
    let mut solver: Box<dyn SkepticalAcceptanceComputer<String>> = match semantics {
        Semantics::GR | Semantics::CO => Box::new(GroundedSemanticsSolver::new(af)),
        Semantics::PR => Box::new(PreferredSemanticsSolver::new_with_sat_solver_factory(
            af,
            create_sat_solver_factory(arg_matches),
        )),
        Semantics::ST => Box::new(StableSemanticsSolver::new_with_sat_solver_factory(
            af,
            create_sat_solver_factory(arg_matches),
        )),
    };
    let writer = AspartixWriter::default();
    let mut out = std::io::stdout();
    let acceptance_status = solver.is_skeptically_accepted(arg);
    writer.write_acceptance_status(&mut out, acceptance_status)
}

fn create_sat_solver_factory(arg_matches: &ArgMatches<'_>) -> Box<SatSolverFactoryFn> {
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
            Box::new(ExternalSatSolver::new(
                s.to_string(),
                external_solver_options.clone(),
            ))
        })
    } else {
        info!("using the default SAT solver for problems requiring a SAT solver");
        Box::new(|| crustabri::default_solver())
    }
}
