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

/// A command of the driver at `program`, with no jobserver in its
/// environment.
///
/// The environment of a test run can name the jobserver of the host, which
/// each build of the host shares. A driver under it runs a part only on one
/// of its tokens, so on a busy host a hub of a test waits for a token past
/// the bound of the test. A test that needs a jobserver names its own after
/// this call.
///
/// # Specification
/// - ensures: the command runs `program`, and no variable of [`JOBSERVERS`]
///   reaches it.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a hub of a test under a jobserver with no token answers
///   in seconds.
/// - witness: `tests::cli::a_view_follows_what_an_editor_holds_open`
#[cfg(test)]
fn unbound(program: impl AsRef<std::ffi::OsStr>) -> std::process::Command
{
    let mut command = std::process::Command::new(program);
    for name in JOBSERVERS {
        command.env_remove(name);
    }
    command
}
