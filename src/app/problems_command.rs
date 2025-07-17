use super::{cli_manager, command::Command};
use anyhow::Result;
use clap::{App, AppSettings, ArgMatches, SubCommand};
use scalop::aa::Query;

const CMD_NAME: &str = "problems";

pub(crate) struct ProblemsCommand;

impl ProblemsCommand {
    pub(crate) fn new() -> Self {
        ProblemsCommand
    }
}

impl<'a> Command<'a> for ProblemsCommand {
    fn name(&self) -> &str {
        CMD_NAME
    }

    fn clap_subcommand(&self) -> App<'a, 'a> {
        SubCommand::with_name(CMD_NAME)
            .about("Displays the problems handled by the solver")
            .setting(AppSettings::DisableVersion)
            .arg(cli_manager::logging_level_cli_arg())
    }

    fn execute(&self, _arg_matches: &ArgMatches<'_>) -> Result<()> {
        let problems = Query::iter_problem_strings().fold(String::new(), |mut acc, s| {
            if !acc.is_empty() {
                acc.push(',')
            };
            acc.push_str(&s);
            acc
        });
        println!("[{}]", problems);
        Ok(())
    }
}
