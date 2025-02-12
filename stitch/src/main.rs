use clap::{Parser, Subcommand};

mod instantiate;
use instantiate::{InstantiateArgs, instantiate_main};
mod common;
use common::CommonArgs;

#[derive(Parser)]
struct App {
    /// The subcommand to run
    #[clap(subcommand)]
    subcommand: StitchCommand,

    /// Command arguments
    #[clap(flatten)]
    common_args: CommonArgs,
}



#[derive(Subcommand)]
enum StitchCommand {
    /// Create an SV wrapper that instantiates a module
    /// with different sets of parameters
    Instantiate(InstantiateArgs),
}

fn main() {
    let app = App::parse();

    match app.subcommand {
        StitchCommand::Instantiate(args) => instantiate_main(&args, &app.common_args),
    }
}
