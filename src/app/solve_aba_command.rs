use super::{
    cli_manager,
    command::Command,
    common::{self, ARG_ARG, ARG_PROBLEM},
};
use anyhow::{anyhow, Context, Result};
use clap::{App, AppSettings, ArgMatches, SubCommand};
use crustabri::{
    aa::{Argument, Query, Semantics},
    aba::{
        FlatABACompleteConstraintsSolver, FlatABACycleBreaker, FlatABAFramework,
        FlatABAPreferredConstraintsSolver,
    },
    io::{FlatABAInstanceReader, FlatABAReader, Iccma23Writer, ResponseWriter},
    solvers::{CredulousAcceptanceComputer, SingleExtensionComputer, SkepticalAcceptanceComputer},
};
use log::{info, warn};

const CMD_NAME: &str = "solve-aba";

pub(crate) struct SolveABACommand;

impl SolveABACommand {
    pub(crate) fn new() -> Self {
        SolveABACommand
    }
}

impl<'a> Command<'a> for SolveABACommand {
    fn name(&self) -> &str {
        CMD_NAME
    }

    fn clap_subcommand(&self) -> App<'a, 'a> {
        SubCommand::with_name(CMD_NAME)
            .about("Solves an argumentation framework problem")
            .setting(AppSettings::DisableVersion)
            .arg(common::input_args())
            .args(&common::problem_args())
            .args(&common::external_sat_solver_args())
            .arg(cli_manager::logging_level_cli_arg())
    }

    fn execute(&self, arg_matches: &ArgMatches<'_>) -> Result<()> {
        execute_with_reader_and_writer(
            arg_matches,
            &mut FlatABAReader::default(),
            &mut Iccma23Writer,
        )
    }
}

fn execute_with_reader_and_writer(
    arg_matches: &ArgMatches<'_>,
    reader: &mut dyn FlatABAInstanceReader<usize>,
    writer: &mut dyn ResponseWriter<usize>,
) -> Result<()> {
    let file = arg_matches.value_of(common::ARG_INPUT).unwrap();
    reader.add_warning_handler(Box::new(|line, msg| warn!("at line {}: {}", line, msg)));
    let af = common::read_file_path_with(file, &|r| reader.read(r))?;
    info!(
        "the argumentation framework has {} arguments, {} assumptions, {} contraries and {} rules",
        af.argument_set().len(),
        af.n_assumptions(),
        af.n_contraries(),
        af.n_rules(),
    );
    let arg = arg_matches
        .value_of(ARG_ARG)
        .map(|a| reader.read_arg_from_str(&af, a))
        .transpose()
        .context("while parsing the argument passed to the command line")?;
    let (query, semantics) =
        Query::read_problem_string(arg_matches.value_of(ARG_PROBLEM).unwrap())?;
    let args = arg.map(|a| vec![a]);
    check_args_definition(query, args.as_ref())?;
    let mut out = std::io::stdout();
    let mut acceptance_status_writer = |status, opt_certificate: Option<Vec<&Argument<usize>>>| {
        writer.write_acceptance_status(&mut out, status)?;
        if let Some(c) = opt_certificate {
            writer.write_single_extension(&mut out, c.as_slice())?
        }
        Ok(())
    };
    match query {
        Query::SE => compute_one_extension(
            &af,
            semantics,
            &mut |opt_model| match opt_model {
                Some(m) => writer.write_single_extension(&mut out, &m),
                None => writer.write_no_extension(&mut out),
            },
            arg_matches,
        ),
        Query::DC => check_credulous_acceptance(
            &af,
            semantics,
            vec![arg.unwrap()],
            arg_matches,
            &mut acceptance_status_writer,
        ),
        Query::DS => check_skeptical_acceptance(
            &af,
            semantics,
            vec![arg.unwrap()],
            arg_matches,
            &mut acceptance_status_writer,
        ),
    }
}

fn check_args_definition<T>(query: Query, args: Option<T>) -> Result<()> {
    match query {
        Query::SE => {
            if args.is_some() {
                warn!(
                    "unexpected argument on the command line (useless for query {})",
                    query.as_ref()
                );
            }
            Ok(())
        }
        Query::DC | Query::DS => {
            if args.is_none() {
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

fn compute_one_extension<F>(
    af: &FlatABAFramework<usize>,
    semantics: Semantics,
    writing_fn: &mut F,
    arg_matches: &ArgMatches<'_>,
) -> Result<()>
where
    F: FnMut(Option<Vec<&Argument<usize>>>) -> Result<()>,
{
    let mut solver: Box<dyn SingleExtensionComputer<usize>> = match semantics {
        Semantics::PR => Box::new(FlatABAPreferredConstraintsSolver::new(
            af,
            common::create_sat_solver_factory(arg_matches),
            FlatABACycleBreaker::new_for_usize(),
        )),
        _ => return Err(anyhow!("unsupported semantics")),
    };
    (writing_fn)(solver.compute_one_extension())
}

fn check_credulous_acceptance<F>(
    af: &FlatABAFramework<usize>,
    semantics: Semantics,
    args: Vec<&Argument<usize>>,
    arg_matches: &ArgMatches<'_>,
    writing_fn: &mut F,
) -> Result<()>
where
    F: FnMut(bool, Option<Vec<&Argument<usize>>>) -> Result<()>,
{
    let mut solver: Box<dyn CredulousAcceptanceComputer<usize>> = match semantics {
        Semantics::CO => Box::new(FlatABACompleteConstraintsSolver::new(
            af,
            common::create_sat_solver_factory(arg_matches),
            FlatABACycleBreaker::new_for_usize(),
        )),
        _ => return Err(anyhow!("unsupported semantics")),
    };
    let acceptance_status =
        solver.are_credulously_accepted(&args.iter().map(|a| a.label()).collect::<Vec<&usize>>());
    (writing_fn)(acceptance_status, None)
}

fn check_skeptical_acceptance<F>(
    af: &FlatABAFramework<usize>,
    semantics: Semantics,
    args: Vec<&Argument<usize>>,
    arg_matches: &ArgMatches<'_>,
    writing_fn: &mut F,
) -> Result<()>
where
    F: FnMut(bool, Option<Vec<&Argument<usize>>>) -> Result<()>,
{
    let mut solver: Box<dyn SkepticalAcceptanceComputer<usize>> = match semantics {
        Semantics::PR => Box::new(FlatABAPreferredConstraintsSolver::new(
            af,
            common::create_sat_solver_factory(arg_matches),
            FlatABACycleBreaker::new_for_usize(),
        )),
        _ => return Err(anyhow!("unsupported semantics")),
    };
    let acceptance_status =
        solver.are_skeptically_accepted(&args.iter().map(|a| a.label()).collect::<Vec<&usize>>());
    (writing_fn)(acceptance_status, None)
}
