use app::{AuthorsCommand, CheckCommand, ProblemsCommand, SolveCommand};
use crusti_app_helper::{AppHelper, Command};

mod app;

const AUTHORS: &str = "Jean-Marie Lagniez <lagniez@cril.fr>, Emmanuel Lonca <lonca@cril.fr> and Jean-Guy Mailly <jean-guy.mailly@u-paris.fr>";

fn main() {
    let app_name = option_env!("CARGO_PKG_NAME").unwrap_or("unknown app name");
    let app_version = option_env!("CARGO_PKG_VERSION").unwrap_or("unknown version");
    let mut app = AppHelper::new(
        app_name,
        app_version,
        AUTHORS,
        "Crustabri, an abstract argumentation solver.",
    );
    let commands: Vec<Box<dyn Command>> = vec![
        Box::new(AuthorsCommand::new(app_name, app_version, AUTHORS)),
        Box::new(CheckCommand::new()),
        Box::new(ProblemsCommand::new()),
        Box::new(SolveCommand::new()),
    ];
    for c in commands {
        app.add_command(c);
    }
    app.launch_app();
}
