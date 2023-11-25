use clap::Parser;

#[derive(clap::Parser)]
pub struct App {
    #[command(subcommand)]
    cmd: Command,
}

#[derive(clap::Subcommand)]
pub enum Command {
    #[clap(name = "repl")]
    Repl,

    #[clap(name = "run", alias = "r")]
    Run,
}

fn main() {
    tilog::init_logger(
        tilog::Config::default()
            .with_level(tilog::Level::Info)
            .with_emoji(true),
    );
    let app = App::parse();

    match app.cmd {
        Command::Repl => drop::repl(),
        Command::Run => drop::run(),
    }
}
