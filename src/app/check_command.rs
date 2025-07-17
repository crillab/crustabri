use super::{cli_manager, command::Command, common};
use anyhow::Result;
use clap::{App, AppSettings, ArgMatches, SubCommand};
use scalop::io::{AspartixReader, Iccma23Reader};

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

    fn clap_subcommand(&self) -> App<'a, 'a> {
        SubCommand::with_name(CMD_NAME)
            .about("Checks input AF files for errors")
            .setting(AppSettings::DisableVersion)
            .arg(common::input_args())
            .arg(common::reader_arg())
            .arg(cli_manager::logging_level_cli_arg())
    }

    fn execute(&self, arg_matches: &ArgMatches<'_>) -> Result<()> {
        let file = arg_matches.value_of(common::ARG_INPUT).unwrap();
        match arg_matches.value_of(common::ARG_READER).unwrap() {
            "apx" => common::read_file_path(file, &mut AspartixReader::default()).map(|_| ()),
            "iccma23" => common::read_file_path(file, &mut Iccma23Reader::default()).map(|_| ()),
            _ => unreachable!(),
        }?;
        Ok(())
    }
}
