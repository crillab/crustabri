use anyhow::Result;
use clap::App;
use clap::ArgMatches;

/// A trait for the app available commands.
///
/// Commands provide their own CLI argument requirements (using clap)
/// and execute themselves given the CLI arguments.
///
/// Each command must have a unique name.
pub trait Command<'a> {
    /// Returns the name of the command.
    fn name(&self) -> &str;

    /// Returns the clap subcommand describing the available CLI arguments for this command.
    fn clap_subcommand(&self) -> App<'a, 'a>;

    /// Executes the command given its arguments.
    /// The function returns `Ok(())` iff the main app should exit with a success status code.
    ///
    /// The arguments are the one returned by clap by calling one of its `get_matches` methods.
    ///
    /// # Arguments
    ///
    /// * `arg_matches` - the arguments for the command
    fn execute(&self, arg_matches: &ArgMatches<'_>) -> Result<()>;
}
