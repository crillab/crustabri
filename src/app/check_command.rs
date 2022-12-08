use super::common;
use anyhow::Result;
use crustabri::{
    aba::Iccma23ABAReader,
    io::{AspartixReader, Iccma23Reader},
};
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
            .about("Checks input AF files for errors")
            .setting(AppSettings::DisableVersion)
            .arg(common::input_args())
            .arg(common::reader_arg())
            .arg(crusti_app_helper::logging_level_cli_arg())
    }

    fn execute(&self, arg_matches: &crusti_app_helper::ArgMatches<'_>) -> Result<()> {
        let file = arg_matches.value_of(common::ARG_INPUT).unwrap();
        match arg_matches.value_of(common::ARG_READER).unwrap() {
            "apx" => common::read_file_path(file, &mut AspartixReader::default()).map(|_| ()),
            "iccma23" => common::read_file_path(file, &mut Iccma23Reader::default()).map(|_| ()),
            "iccma23_aba" => common::read_file_path_with(file, &|r| {
                let mut aba_reader = Iccma23ABAReader::default();
                aba_reader.read(r)
            })
            .map(|_| ()),
            _ => unreachable!(),
        }?;
        Ok(())
    }
}
