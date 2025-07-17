use super::{
    cli_manager,
    command::Command,
    common::{self, ARG_ARG, ARG_PROBLEM},
};
use anyhow::{anyhow, Context, Result};
use clap::{App, AppSettings, Arg, ArgMatches, SubCommand};
use log::{info, warn};
use scalop::{
    aa::{AAFramework, Argument, Query, Semantics},
    encodings::{
        aux_var_constraints_encoder, exp_constraints_encoder, ConstraintsEncoder,
        HybridCompleteConstraintsEncoder,
    },
    io::{
        AspartixReader, AspartixWriter, Iccma23Reader, Iccma23Writer, InstanceReader,
        ResponseWriter,
    },
    solvers::{
        CompleteSemanticsSolver, CredulousAcceptanceComputer, GroundedSemanticsSolver,
        IdealSemanticsSolver, PreferredSemanticsSolver, SemiStableSemanticsSolver,
        SingleExtensionComputer, SkepticalAcceptanceComputer, StableSemanticsSolver,
        StageSemanticsSolver,
    },
    utils::LabelType,
};

const CMD_NAME: &str = "solve";

const ARG_CERTIFICATE: &str = "CERTIFICATE";

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

    fn clap_subcommand(&self) -> App<'a, 'a> {
        SubCommand::with_name(CMD_NAME)
            .about("Solves an argumentation framework problem")
            .setting(AppSettings::DisableVersion)
            .arg(common::input_args())
            .arg(common::reader_arg())
            .args(&common::problem_args())
            .args(&common::external_sat_solver_args())
            .arg(cli_manager::logging_level_cli_arg())
            .arg(
                Arg::with_name(ARG_CERTIFICATE)
                    .short("c")
                    .long("with-certificate")
                    .takes_value(false)
                    .help("generate a certificate when possible")
                    .required(false),
            )
            .arg(common::encoding_arg())
    }

    fn execute(&self, arg_matches: &ArgMatches<'_>) -> Result<()> {
        match arg_matches.value_of(common::ARG_READER).unwrap() {
            "apx" => execute_with_reader_and_writer(
                arg_matches,
                &mut AspartixReader::default(),
                &mut AspartixWriter,
            ),
            "iccma23" => execute_with_reader_and_writer(
                arg_matches,
                &mut Iccma23Reader::default(),
                &mut Iccma23Writer,
            ),
            _ => unreachable!(),
        }
    }
}

fn execute_with_reader_and_writer<T>(
    arg_matches: &ArgMatches<'_>,
    reader: &mut dyn InstanceReader<T>,
    writer: &mut dyn ResponseWriter<T>,
) -> Result<()>
where
    T: LabelType,
{
    let file = arg_matches.value_of(common::ARG_INPUT).unwrap();
    let af = common::read_file_path(file, reader)?;
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
    let mut acceptance_status_writer = |status, opt_certificate: Option<Vec<&Argument<T>>>| {
        writer.write_acceptance_status(&mut out, status)?;
        if let Some(c) = opt_certificate {
            writer.write_single_extension(&mut out, c.as_slice())?
        }
        Ok(())
    };
    match query {
        Query::SE => {
            compute_one_extension(
                &af,
                semantics,
                arg_matches,
                &mut |opt_model| match opt_model {
                    Some(m) => writer.write_single_extension(&mut out, &m),
                    None => writer.write_no_extension(&mut out),
                },
            )
        }
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

fn compute_one_extension<F, T>(
    af: &AAFramework<T>,
    semantics: Semantics,
    arg_matches: &ArgMatches<'_>,
    writing_fn: &mut F,
) -> Result<()>
where
    T: LabelType,
    F: FnMut(Option<Vec<&Argument<T>>>) -> Result<()>,
{
    let mut solver: Box<dyn SingleExtensionComputer<T>> = match semantics {
        Semantics::GR | Semantics::CO => {
            warn_on_unexpected_encoding(arg_matches);
            Box::new(GroundedSemanticsSolver::new(af))
        }
        Semantics::PR => Box::new(
            PreferredSemanticsSolver::new_with_sat_solver_factory_and_constraints_encoder(
                af,
                common::create_sat_solver_factory(arg_matches)
                    .context("while creating the SAT solver factory")?,
                create_encoder(arg_matches, semantics).unwrap(),
            ),
        ),
        Semantics::ST => Box::new(StableSemanticsSolver::new_with_sat_solver_factory(
            af,
            common::create_sat_solver_factory(arg_matches)
                .context("while creating the SAT solver factory")?,
        )),
        Semantics::SST => Box::new(
            SemiStableSemanticsSolver::new_with_sat_solver_factory_and_constraints_encoder(
                af,
                common::create_sat_solver_factory(arg_matches)
                    .context("while creating the SAT solver factory")?,
                create_encoder(arg_matches, semantics).unwrap(),
            ),
        ),
        Semantics::STG => Box::new(
            StageSemanticsSolver::new_with_sat_solver_factory_and_constraints_encoder(
                af,
                common::create_sat_solver_factory(arg_matches)
                    .context("while creating the SAT solver factory")?,
                create_encoder(arg_matches, semantics).unwrap(),
            ),
        ),
        Semantics::ID => Box::new(
            IdealSemanticsSolver::new_with_sat_solver_factory_and_constraints_encoder(
                af,
                common::create_sat_solver_factory(arg_matches)
                    .context("while creating the SAT solver factory")?,
                create_encoder(arg_matches, semantics).unwrap(),
            ),
        ),
    };
    (writing_fn)(solver.compute_one_extension())
}

fn check_credulous_acceptance<F, T>(
    af: &AAFramework<T>,
    semantics: Semantics,
    args: Vec<&Argument<T>>,
    arg_matches: &ArgMatches<'_>,
    writing_fn: &mut F,
) -> Result<()>
where
    T: LabelType,
    F: FnMut(bool, Option<Vec<&Argument<T>>>) -> Result<()>,
{
    let mut solver: Box<dyn CredulousAcceptanceComputer<T>> = match semantics {
        Semantics::GR => {
            warn_on_unexpected_encoding(arg_matches);
            Box::new(GroundedSemanticsSolver::new(af))
        }
        Semantics::CO | Semantics::PR => Box::new(
            CompleteSemanticsSolver::new_with_sat_solver_factory_and_constraints_encoder(
                af,
                common::create_sat_solver_factory(arg_matches)
                    .context("while creating the SAT solver factory")?,
                create_encoder(arg_matches, semantics).unwrap(),
            ),
        ),
        Semantics::ST => Box::new(StableSemanticsSolver::new_with_sat_solver_factory(
            af,
            common::create_sat_solver_factory(arg_matches)
                .context("while creating the SAT solver factory")?,
        )),
        Semantics::SST => Box::new(
            SemiStableSemanticsSolver::new_with_sat_solver_factory_and_constraints_encoder(
                af,
                common::create_sat_solver_factory(arg_matches)
                    .context("while creating the SAT solver factory")?,
                create_encoder(arg_matches, semantics).unwrap(),
            ),
        ),
        Semantics::STG => Box::new(
            StageSemanticsSolver::new_with_sat_solver_factory_and_constraints_encoder(
                af,
                common::create_sat_solver_factory(arg_matches)
                    .context("while creating the SAT solver factory")?,
                create_encoder(arg_matches, semantics).unwrap(),
            ),
        ),
        Semantics::ID => Box::new(
            IdealSemanticsSolver::new_with_sat_solver_factory_and_constraints_encoder(
                af,
                common::create_sat_solver_factory(arg_matches)
                    .context("while creating the SAT solver factory")?,
                create_encoder(arg_matches, semantics).unwrap(),
            ),
        ),
    };
    let with_certificate = arg_matches.is_present(ARG_CERTIFICATE);
    if with_certificate {
        let (acceptance_status, certificate) = solver.are_credulously_accepted_with_certificate(
            &args.iter().map(|a| a.label()).collect::<Vec<&T>>(),
        );
        (writing_fn)(acceptance_status, certificate)
    } else {
        let acceptance_status =
            solver.are_credulously_accepted(&args.iter().map(|a| a.label()).collect::<Vec<&T>>());
        (writing_fn)(acceptance_status, None)
    }
}

fn check_skeptical_acceptance<F, T>(
    af: &AAFramework<T>,
    semantics: Semantics,
    args: Vec<&Argument<T>>,
    arg_matches: &ArgMatches<'_>,
    writing_fn: &mut F,
) -> Result<()>
where
    T: LabelType,
    F: FnMut(bool, Option<Vec<&Argument<T>>>) -> Result<()>,
{
    let mut solver: Box<dyn SkepticalAcceptanceComputer<T>> = match semantics {
        Semantics::GR | Semantics::CO => {
            warn_on_unexpected_encoding(arg_matches);
            Box::new(GroundedSemanticsSolver::new(af))
        }
        Semantics::PR => Box::new(
            PreferredSemanticsSolver::new_with_sat_solver_factory_and_constraints_encoder(
                af,
                common::create_sat_solver_factory(arg_matches)
                    .context("while creating the SAT solver factory")?,
                create_encoder(arg_matches, semantics).unwrap(),
            ),
        ),
        Semantics::ST => Box::new(StableSemanticsSolver::new_with_sat_solver_factory(
            af,
            common::create_sat_solver_factory(arg_matches)
                .context("while creating the SAT solver factory")?,
        )),
        Semantics::SST => Box::new(
            SemiStableSemanticsSolver::new_with_sat_solver_factory_and_constraints_encoder(
                af,
                common::create_sat_solver_factory(arg_matches)
                    .context("while creating the SAT solver factory")?,
                create_encoder(arg_matches, semantics).unwrap(),
            ),
        ),
        Semantics::STG => Box::new(
            StageSemanticsSolver::new_with_sat_solver_factory_and_constraints_encoder(
                af,
                common::create_sat_solver_factory(arg_matches)
                    .context("while creating the SAT solver factory")?,
                create_encoder(arg_matches, semantics).unwrap(),
            ),
        ),
        Semantics::ID => Box::new(
            IdealSemanticsSolver::new_with_sat_solver_factory_and_constraints_encoder(
                af,
                common::create_sat_solver_factory(arg_matches)
                    .context("while creating the SAT solver factory")?,
                create_encoder(arg_matches, semantics).unwrap(),
            ),
        ),
    };
    let with_certificate = arg_matches.is_present(ARG_CERTIFICATE);
    if with_certificate {
        let (acceptance_status, certificate) = solver.are_skeptically_accepted_with_certificate(
            &args.iter().map(|a| a.label()).collect::<Vec<&T>>(),
        );
        (writing_fn)(acceptance_status, certificate)
    } else {
        let acceptance_status =
            solver.are_skeptically_accepted(&args.iter().map(|a| a.label()).collect::<Vec<&T>>());
        (writing_fn)(acceptance_status, None)
    }
}

fn create_encoder<T>(
    arg_matches: &ArgMatches<'_>,
    sem: Semantics,
) -> Option<Box<dyn ConstraintsEncoder<T>>>
where
    T: LabelType,
{
    let encoding_as_str = |default_value| {
        let str_encoding = arg_matches
            .value_of(common::ARG_ENCODING)
            .unwrap_or(default_value);
        info!(r#"encoding strategy is "{}""#, str_encoding);
        str_encoding
    };
    match sem {
        Semantics::GR | Semantics::ST => None,
        Semantics::STG => match encoding_as_str("exp") {
            "aux_var" => Some(Box::new(
                aux_var_constraints_encoder::new_for_conflict_freeness(),
            )),
            "exp" => Some(Box::new(
                exp_constraints_encoder::new_for_conflict_freeness(),
            )),
            "hybrid" => {
                warn!(
                    r#"irrelevant encoding value "hybrid" for STG semantics; falling back to default "exp""#
                );
                Some(Box::new(
                    exp_constraints_encoder::new_for_conflict_freeness(),
                ))
            }
            _ => unreachable!(),
        },
        Semantics::PR if arg_matches.value_of(ARG_PROBLEM).unwrap() == "SE-PR" => {
            match encoding_as_str("aux_var") {
                "aux_var" => Some(Box::new(
                    aux_var_constraints_encoder::new_for_admissibility(),
                )),
                "exp" => Some(Box::new(
                    exp_constraints_encoder::new_for_complete_semantics(),
                )),
                "hybrid" => Some(Box::<HybridCompleteConstraintsEncoder>::default()),
                _ => unreachable!(),
            }
        }
        _ => match encoding_as_str("aux_var") {
            "aux_var" => Some(Box::new(
                aux_var_constraints_encoder::new_for_complete_semantics(),
            )),
            "exp" => Some(Box::new(
                exp_constraints_encoder::new_for_complete_semantics(),
            )),
            "hybrid" => Some(Box::<HybridCompleteConstraintsEncoder>::default()),
            _ => unreachable!(),
        },
    }
}

fn warn_on_unexpected_encoding(arg_matches: &ArgMatches<'_>) {
    if arg_matches.value_of(common::ARG_ENCODING).is_some() {
        warn!("irrelevant encoding parameter for problem; ignoring it")
    }
}
