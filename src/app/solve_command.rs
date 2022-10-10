use super::common;
use anyhow::{anyhow, Context, Result};
use crustabri::{
    AAFramework, Argument, AspartixWriter, CredulousAcceptanceComputer, Query, Semantics,
    SingleExtensionComputer, SkepticalAcceptanceComputer, StableEncodingSolver,
};
use crusti_app_helper::{warn, AppSettings, Arg, Command, SubCommand};

const CMD_NAME: &str = "solve";

const ARG_PROBLEM: &str = "PROBLEM";
const ARG_ARG: &str = "ARG";

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
                    .help("the problem to solver")
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
            Query::SE => compute_one_extension(&af, semantics),
            Query::DC => check_credulous_acceptance(&af, semantics, arg.unwrap()),
            Query::DS => check_skeptical_acceptance(&af, semantics, arg.unwrap()),
        }
    }
}

fn check_arg_definition(query: Query, arg: &Option<&Argument<String>>) -> Result<()> {
    match query {
        Query::SE => {
            if arg.is_some() {
                warn!(
                    "unexpected argument on the command line (useless for query {})",
                    query.to_short_str()
                );
            }
            Ok(())
        }
        Query::DC | Query::DS => {
            if arg.is_none() {
                Err(anyhow!(
                    "missing argument on the command line (required for query {})",
                    query.to_short_str()
                ))
            } else {
                Ok(())
            }
        }
    }
}

fn compute_one_extension(af: &AAFramework<String>, semantics: Semantics) -> Result<()> {
    let mut solver = match semantics {
        Semantics::ST => Box::new(StableEncodingSolver::new(af)),
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
) -> Result<()> {
    let mut solver = match semantics {
        Semantics::ST => Box::new(StableEncodingSolver::new(af)),
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
) -> Result<()> {
    let mut solver = match semantics {
        Semantics::ST => Box::new(StableEncodingSolver::new(af)),
    };
    let writer = AspartixWriter::default();
    let mut out = std::io::stdout();
    let acceptance_status = solver.is_skeptically_accepted(arg);
    writer.write_acceptance_status(&mut out, acceptance_status)
}
