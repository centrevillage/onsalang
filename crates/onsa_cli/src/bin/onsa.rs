//! The `onsa` command (spec §18.2): its arguments, and the commands of
//! `onsa_cli` on the file system, the standard output and the standard error.

use clap::Parser;

fn main() -> std::process::ExitCode {
    let cli = onsa_cli::Cli::parse();
    let (mut out, mut err) = (std::io::stdout(), std::io::stderr());
    let mut io = onsa_cli::Io::new(&mut out, &mut err, &onsa_cli::Disk);
    std::process::ExitCode::from(onsa_cli::run_command(cli.command, &mut io))
}
