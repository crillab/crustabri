use anyhow::Result;
use crusti_app_helper::{AppSettings, Command, SubCommand};

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

    fn clap_subcommand(&self) -> crusti_app_helper::App<'a, 'a> {
        SubCommand::with_name(CMD_NAME)
            .about("Displays app version and authors")
            .setting(AppSettings::DisableVersion)
            .arg(crusti_app_helper::logging_level_cli_arg())
    }

    fn execute(&self, _arg_matches: &crusti_app_helper::ArgMatches<'_>) -> Result<()> {
        println!("{} {}", self.app_name, self.app_version);
        println!("{}", self.authors.replace(':', ", "));
        Ok(())
    }
}
