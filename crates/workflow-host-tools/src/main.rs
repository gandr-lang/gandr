//! `host-tools`: builds the tools of `mise.toml` that publish no binary for
//! a target, once for each version, into a directory of keys.
//!
//! `host-tools build --target TRIPLE --into DIR --mise-version VERSION` reads
//! the table `.config/host-tools/builds.toml`, `mise.lock` and the builder's
//! configuration. It builds each tool of the target whose key does not stand,
//! one after another, and prints one line for each tool as its build ends.
//!
//! # Exit codes
//!
//! - `0`: the key of each tool of the target stands; also `--help` and
//!   `--version`.
//! - `2`: a tool's build failed, or the run was refused before the first build;
//!   also a malformed invocation.

use std::io::Write as _;
use std::path::PathBuf;
use std::process::ExitCode;

use anodized::spec;
use gandr_workflow_host_tools::Builds;
use gandr_workflow_host_tools::Built;
use gandr_workflow_host_tools::Host;
use gandr_workflow_host_tools::HostToolsError;
use gandr_workflow_host_tools::Input;
use gandr_workflow_host_tools::Lock;
use gandr_workflow_host_tools::Processes;
use gandr_workflow_host_tools::Target;
use gandr_workflow_host_tools::Version;
use gandr_workflow_host_tools::build;
use gandr_workflow_host_tools::plan;

/// The exit code of a failed build, a refusal or a malformed invocation.
const REFUSED: u8 = 2;

/// Builds the tools that publish no binary for a target.
#[repr(transparent)]
#[derive(Debug, clap::Parser)]
#[command(name = "host-tools", version, about)]
struct Cli
{
    /// What to do.
    #[command(subcommand)]
    command: Command,
}

/// The subcommands.
#[derive(Debug, clap::Subcommand)]
enum Command
{
    /// Builds each tool of a target whose key does not stand.
    Build
    {
        /// The target triple, as `riscv64gc-unknown-linux-gnu`.
        #[arg(long)]
        target: String,
        /// The directory of the keys, `<target>/<install name>/<version>`.
        #[arg(long)]
        into: PathBuf,
        /// The pin of mise, the version that mise itself builds at.
        #[arg(long)]
        mise_version: String,
        /// The table of the tools to build.
        #[arg(long, default_value = ".config/host-tools/builds.toml")]
        builds: PathBuf,
        /// The lock of the tools' versions.
        #[arg(long, default_value = "mise.lock")]
        lock: PathBuf,
        /// The builder's configuration;
        /// `$XDG_CONFIG_HOME/gandr/host-tools.toml` when absent.
        #[arg(long)]
        host: Option<PathBuf>,
    },
}

/// Parses the invocation, builds and chooses the exit code.
///
/// # Specification
/// - requires: nothing.
/// - ensures: exits `0` after the key of each tool of the target stands, or
///   after printing help or the version; exits `2` after a failed build, a
///   refusal or a usage message, each printed.
/// - provides: the process boundary.
/// - fails: never; every refusal is an exit code.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a key that stands, a build the host's configuration
///   refuses and an invocation with no target; a swapped stream or exit code
///   changes the observed process result.
/// - witness: `tests::cli::a_key_that_stands_is_kept_and_exits_zero`
/// - witness: `tests::cli::a_build_the_host_refuses_is_named_and_exits_two`
/// - witness: `tests::cli::a_malformed_invocation_exits_two`
#[spec(ensures: |ret| ret == ExitCode::SUCCESS || ret == ExitCode::from(REFUSED))]
fn main() -> ExitCode
{
    let cli = match <Cli as clap::Parser>::try_parse() {
        Ok(cli) => cli,
        Err(error) => {
            return match (error.print(), error.use_stderr()) {
                (Ok(()), false) => ExitCode::SUCCESS,
                (Ok(()), true) | (Err(_), _) => ExitCode::from(REFUSED),
            };
        },
    };
    match run(cli) {
        Ok(code) => code,
        Err(error) => match writeln!(std::io::stderr(), "host-tools: {error}") {
            Ok(()) | Err(_) => ExitCode::from(REFUSED),
        },
    }
}

/// Runs the subcommand `cli` names: success when each tool's key stands at
/// its end, the refusal's code when a build failed.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the table, the lock and the configuration are read before the
///   first build. Each tool of the target builds in the table's order, its
///   commands' output in `<into>/.logs/<target>.<install name>.<version>.log`,
///   and standard output receives one line for it as its build ends: `kept`,
///   `built` with the seconds it took, or `failed` with the refusal. The result
///   is success when no build failed, and the refusal's code otherwise.
/// - provides: the whole subcommand.
/// - fails: [`HostToolsError::Io`] or [`HostToolsError::Toml`] when the table,
///   the lock or the configuration cannot be read; every refusal of [`plan()`];
///   [`HostToolsError::Output`] when standard output cannot be written.
/// - panics: none.
/// - executable: none — the outcome is the keys on disk and the bytes on
///   standard output.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — a key that stands is kept; a build that the host's
///   configuration refuses is named, and the run reports a failure.
/// - witness: `tests::cli::a_key_that_stands_is_kept_and_exits_zero`
/// - witness: `tests::cli::a_build_the_host_refuses_is_named_and_exits_two`
fn run(cli: Cli) -> Result<ExitCode, HostToolsError>
{
    let Command::Build {
        target,
        into,
        mise_version,
        builds,
        lock,
        host,
    } = cli.command;
    let builds = Builds::read(&Input::read(&builds)?)?;
    let lock = Lock::read(&Input::read(&lock)?)?;
    let host_path = host.unwrap_or_else(|| config_home().join("gandr").join("host-tools.toml"));
    let host = if host_path.is_file() {
        Host::read(&Input::read(&host_path)?)?
    }
    else {
        Host::default()
    };
    let jobs = plan(
        &builds,
        &lock,
        &Version::from(mise_version.as_str()),
        &Target::from(target.as_str()),
    )?;
    let logs = into.join(".logs");
    std::fs::create_dir_all(&logs).map_err(|error| HostToolsError::Io {
        path: logs.clone(),
        message: error.to_string(),
    })?;
    let mut code = ExitCode::SUCCESS;
    for job in &jobs {
        let started = std::time::Instant::now();
        let mut processes = Processes {
            log: logs.join(format!(
                "{}.{}.{}.log",
                job.target, job.install_name, job.version
            )),
        };
        let line = match build(job, &into, &host, &mut processes) {
            Ok(Built::Kept) => format!("kept {} {}", job.key, job.version),
            Ok(Built::Built) => format!(
                "built {} {} in {} s",
                job.key,
                job.version,
                started.elapsed().as_secs()
            ),
            Err(error) => {
                code = ExitCode::from(REFUSED);
                format!("failed {} {}: {error}", job.key, job.version)
            },
        };
        writeln!(std::io::stdout(), "{line}").map_err(|error| HostToolsError::Output {
            message: error.to_string(),
        })?;
    }
    Ok(code)
}

/// The user's configuration directory: `$XDG_CONFIG_HOME`, else
/// `$HOME/.config`.
///
/// # Specification
/// trivial.
fn config_home() -> PathBuf
{
    std::env::var_os("XDG_CONFIG_HOME")
        .filter(|home| !home.is_empty())
        .map_or_else(
            || PathBuf::from(std::env::var_os("HOME").unwrap_or_default()).join(".config"),
            PathBuf::from,
        )
}
