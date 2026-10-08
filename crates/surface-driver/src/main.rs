//! Driver binary for the gandr language toolchain.
//!
//! Installs as `gandr`. The driver owns the argument surface and the process
//! boundary: it parses an invocation, routes it through the surface
//! dispatcher, and renders the outcome. It accepts `--help` and `--version`;
//! a bare invocation prints the dispatcher's status report.

use std::io::Write as _;

/// gandr language toolchain driver.
#[derive(Debug, clap::Parser)]
#[command(name = "gandr", version, about)]
struct Cli;

/// Parse the driver's arguments, route the invocation, render the outcome.
///
/// # Specification
/// - requires: nothing of the caller; the arguments come from the process
///   environment and every accepted form is argument-free.
/// - ensures: [`Cli`] parses before anything is written, so `--help`,
///   `--version`, and an argument error take clap's own exit path and the
///   dispatcher is reached only on a bare `gandr` invocation.
/// - provides: one status line on standard output naming the driver version and
///   the dispatcher's status report, flushed before the process returns. The
///   postcondition stays prose: it orders the driver's own exit paths — the
///   argument surface parses before anything is written — which is a property
///   of the run rather than a predicate over one entry state and one returned
///   value, and the status line is an effect on standard output rather than an
///   observation this call can make.
/// - fails: returns the write or flush error when standard output is closed,
///   full, or otherwise unwritable; the runtime reports it and exits nonzero.
/// - panics: none. The status line goes through a locked handle and the
///   fallible `writeln!` rather than `println!`, whose internal write-failure
///   path aborts. Clap leaves by process exit rather than by panic on `--help`,
///   `--version`, and argument errors, and its command-definition assertions
///   fire only under `debug_assertions`.
///
/// # Errors
/// - [`std::io::Error`]: the underlying failure from writing the status line to
///   standard output, or from the flush that follows it.
fn main() -> Result<(), std::io::Error>
{
    let _cli = <Cli as clap::Parser>::parse();
    let outcome = gandr_surface_dispatcher::dispatch(gandr_surface_dispatcher::Invocation::Status);
    let gandr_surface_dispatcher::Outcome::Status(report) = outcome;
    let mut stdout = std::io::stdout().lock();
    writeln!(stdout, "gandr {} — {report}", env!("CARGO_PKG_VERSION"))?;
    stdout.flush()?;
    Ok(())
}
