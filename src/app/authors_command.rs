use super::{cli_manager, command::Command};
use anyhow::Result;
use clap::{App, AppSettings, ArgMatches, SubCommand};

const CMD_NAME: &str = "authors";

pub(crate) struct AuthorsCommand<'a> {
    app_name: &'a str,
    app_version: &'a str,
    authors: &'a str,
}

impl<'a> AuthorsCommand<'a> {
    pub(crate) fn new(app_name: &'a str, app_version: &'a str, authors: &'a str) -> Self {
        AuthorsCommand {
            app_name,
            app_version,
            authors,
        }
    }
}

impl<'a> Command<'a> for AuthorsCommand<'a> {
    fn name(&self) -> &str {
        CMD_NAME
    }

    fn clap_subcommand(&self) -> App<'a, 'a> {
        SubCommand::with_name(CMD_NAME)
            .about("Displays app version and authors")
            .setting(AppSettings::DisableVersion)
            .arg(cli_manager::logging_level_cli_arg())
    }

    fn execute(&self, _arg_matches: &ArgMatches<'_>) -> Result<()> {
        println!("{} {}", self.app_name, self.app_version);
        println!("{}", self.authors.replace(':', ", "));
        Ok(())
    }
}
