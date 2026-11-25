//! The integration tests of `gandr-lang`: one target, each area its own
//! `cfg(test)` module, so a witness path reads `tests::<area>::<name>`.

#[cfg(test)]
mod cli;
#[cfg(test)]
mod net;
#[cfg(test)]
mod rand;
#[cfg(test)]
mod reals;
#[cfg(test)]
mod wasi;

/// The variables of the environment that name a jobserver of the build
/// tools, as the pool of the driver reads them.
#[cfg(test)]
const JOBSERVERS: [&str; 3] = ["CARGO_MAKEFLAGS", "MAKEFLAGS", "MFLAGS"];

/// The width of a driver that a test starts when the environment names
/// none: the test threads of a run multiply it, so it stays small.
#[cfg(test)]
const TEST_WIDTH: &str = "2";

/// A command of the driver at `program`, with no jobserver in its
/// environment and a bounded width.
///
/// The environment of a test run can name the jobserver of the host, which
/// each build of the host shares. A driver under it runs a part only on one
/// of its tokens, so on a busy host a hub of a test waits for a token past
/// the bound of the test. A driver with no jobserver runs at the width of
/// the host unless `GANDR_JOBS` caps it, so the command takes
/// [`TEST_WIDTH`] when the environment names no `GANDR_JOBS`. A test that
/// needs a jobserver or a width of its own names it after this call.
///
/// # Specification
/// - ensures: the command runs `program`, no variable of [`JOBSERVERS`] reaches
///   it, and `GANDR_JOBS` is the environment's or [`TEST_WIDTH`].
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a hub of a test under a jobserver with no token answers
///   in seconds, and the drivers of a run hold a bounded pool each.
/// - witness: `tests::cli::a_view_follows_what_an_editor_holds_open`
/// - witness: `tests::cli::the_toolset_checks_a_corpus_as_the_command_line_does_6765`
#[cfg(test)]
fn unbound(program: impl AsRef<std::ffi::OsStr>) -> std::process::Command
{
    let mut command = std::process::Command::new(program);
    for name in JOBSERVERS {
        command.env_remove(name);
    }
    if std::env::var_os("GANDR_JOBS").is_none() {
        command.env("GANDR_JOBS", TEST_WIDTH);
    }
    command
}
