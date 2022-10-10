use app::{CheckCommand, SolveCommand};
use crusti_app_helper::{AppHelper, Command};

mod app;

fn main() {
    let mut app = AppHelper::new(
        option_env!("CARGO_PKG_NAME").unwrap_or("unknown app name"),
        option_env!("CARGO_PKG_VERSION").unwrap_or("unknown version"),
        "Emmanuel Lonca <lonca@cril.fr>",
        "Crustabri, an abstract argumentation solver.",
    );
    let commands: Vec<Box<dyn Command>> =
        vec![Box::new(CheckCommand::new()), Box::new(SolveCommand::new())];
    for c in commands {
        app.add_command(c);
    }
    crusti_app_helper::init_logger();
    app.launch_app();
}
