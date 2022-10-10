use super::common;
use anyhow::Result;
use crustabri::{
    AAFramework, AspartixWriter, Query, Semantics, SingleExtensionComputer, StableEncodingSolver,
};
use crusti_app_helper::{AppSettings, Arg, Command, SubCommand};

const CMD_NAME: &str = "solve";

const ARG_PROBLEM: &str = "PROBLEM";

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
    }

    fn execute(&self, arg_matches: &crusti_app_helper::ArgMatches<'_>) -> Result<()> {
        let file = arg_matches.value_of(common::ARG_INPUT).unwrap();
        let af = common::read_aspartix_file_path(file)?;
        let (query, semantics) =
            crustabri::read_problem_string(arg_matches.value_of(ARG_PROBLEM).unwrap())?;
        match query {
            Query::SE => compute_one_extension(af, semantics),
        }
    }
}

fn compute_one_extension(af: AAFramework<String>, semantics: Semantics) -> Result<()> {
    let mut solver = match semantics {
        Semantics::ST => Box::new(StableEncodingSolver::new(&af)),
    };
    let writer = AspartixWriter::default();
    let mut out = std::io::stdout();
    match solver.compute_one_extension() {
        Some(ext) => writer.write_single_extension(&mut out, &ext),
        None => writer.write_no_extension(&mut out),
    }
}
