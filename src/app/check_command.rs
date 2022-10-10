use super::common;
use anyhow::Result;
use crusti_app_helper::{AppSettings, Command, SubCommand};

const CMD_NAME: &str = "check";

pub(crate) struct CheckCommand;

impl CheckCommand {
    pub(crate) fn new() -> Self {
        CheckCommand
    }
}

impl<'a> Command<'a> for CheckCommand {
    fn name(&self) -> &str {
        CMD_NAME
    }

    fn clap_subcommand(&self) -> crusti_app_helper::App<'a, 'a> {
        SubCommand::with_name(CMD_NAME)
            .about("Checks Aspartix files for errors")
            .setting(AppSettings::DisableVersion)
            .arg(common::input_args())
    }

    fn execute(&self, arg_matches: &crusti_app_helper::ArgMatches<'_>) -> Result<()> {
        let file = arg_matches.value_of(common::ARG_INPUT).unwrap();
        common::read_aspartix_file_path(file)?;
        Ok(())
    }
}
