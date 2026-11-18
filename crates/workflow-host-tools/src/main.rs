//! `host-tools`: builds the tools of `mise.toml` that publish no binary for
//! a target, once for each version, into a directory of keys, and copies
//! each key to the hosts that receive it.
//!
//! `host-tools build --target TRIPLE --into DIR --mise-version VERSION` reads
//! the table `.config/host-tools/builds.toml`, `mise.lock` and the builder's
//! configuration. It builds each tool of the target whose key does not stand,
//! one after another, and prints one line for each tool as its build ends.
//!
//! `host-tools push --into DIR --mise-version VERSION` does the same for the
//! target of each receiver that the builder's configuration names. It copies
//! each key to the receivers of its target as its build ends, and brings mise
//! to the pin on the builder and on each receiver.
//!
//! `host-tools check [--mise-version VERSION]` reads the tools of the
//! checkout that this host lacks. It prints one line for each of them, and
//! one line for the host's mise against the pin.
//!
//! # Exit codes
//!
//! - `0`: the key of each tool stands, and each push and update ended; for
//!   `check`, the host lacks no tool; also `--help` and `--version`.
//! - `2`: a tool's build, a push or an update failed, or the run was refused
//!   before the first build; for `check`, the host lacks a tool; also a
//!   malformed invocation.

extern crate alloc;

use alloc::collections::BTreeMap;
use core::fmt::Write as _;
use std::io::Write as _;
use std::path::PathBuf;
use std::process::ExitCode;

use anodized::spec;
use gandr_workflow_host_tools::Builds;
use gandr_workflow_host_tools::Built;
use gandr_workflow_host_tools::Host;
use gandr_workflow_host_tools::HostToolsError;
use gandr_workflow_host_tools::Input;
use gandr_workflow_host_tools::Json;
use gandr_workflow_host_tools::Listing;
use gandr_workflow_host_tools::Lock;
use gandr_workflow_host_tools::Machine;
use gandr_workflow_host_tools::Platform;
use gandr_workflow_host_tools::Processes;
use gandr_workflow_host_tools::Pruned;
use gandr_workflow_host_tools::Pushed;
use gandr_workflow_host_tools::Receiver;
use gandr_workflow_host_tools::Target;
use gandr_workflow_host_tools::Version;
use gandr_workflow_host_tools::build;
use gandr_workflow_host_tools::disabled;
use gandr_workflow_host_tools::lacks;
use gandr_workflow_host_tools::plan;
use gandr_workflow_host_tools::prune;
use gandr_workflow_host_tools::push;
use gandr_workflow_host_tools::retire;
use gandr_workflow_host_tools::settle;
use gandr_workflow_host_tools::update;

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
        /// The inputs of the build.
        #[command(flatten)]
        inputs: Inputs,
    },
    /// Builds the tools of each receiver's target, copies each key to its
    /// receivers, and brings mise to the pin on each host.
    Push
    {
        /// The inputs of the builds.
        #[command(flatten)]
        inputs: Inputs,
    },
    /// Reads the tools of the checkout that this host lacks, and the host's
    /// mise against the pin.
    Check
    {
        /// The pin of mise; the check prints no line for mise when absent.
        #[arg(long)]
        mise_version: Option<String>,
    },
}

/// The inputs of each subcommand.
#[derive(Debug, clap::Args)]
struct Inputs
{
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
}

/// The inputs, read: the table, the lock, the builder's configuration and
/// the pin of mise.
struct Read
{
    /// The table of the tools to build.
    builds: Builds,
    /// The lock of the tools' versions.
    lock: Lock,
    /// The builder's configuration.
    host: Host,
    /// The pin of mise.
    pin: Version,
    /// The directory of the keys.
    into: PathBuf,
    /// The directory of the logs, `<into>/.logs`.
    logs: PathBuf,
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

/// Runs the subcommand `cli` names: success when each tool's key stands and
/// each push and update ended, or when the host lacks no tool; the refusal's
/// code otherwise.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the table, the lock and the configuration are read before the
///   first build. `build` builds each tool of its target in the table's order,
///   its commands' output in `<into>/.logs/<target>.<install
///   name>.<version>.log`, and standard output receives one line for it as its
///   build ends: `kept`, `built` with the seconds it took, or `failed` with the
///   refusal. After each key that stands, the key of each other version of its
///   tool goes, with a line `retired` for each. `push` does nothing when the
///   configuration names no receiver. Otherwise it brings the builder's mise to
///   the pin, then builds the target of each receiver as `build` does. Before
///   the first build of a target with tools, it turns automatic installs off on
///   each receiver of the target, and prints `turned automatic installs off` or
///   `failed to turn automatic installs off` when that runs. After each build
///   that ends, it copies the key to each receiver of the target and prints
///   `pushed` or `failed to push` for each copy that runs. Last, it brings to
///   the pin each receiver that names no path of its mise, and prints `updated`
///   or `failed to update`. At its end, `build` and `push` remove the scratch
///   of the builds when no build holds it, and print `pruned the scratch` when
///   they remove it. `check` prints `host-tools: <platform> <lack>` for each
///   tool that the host lacks, in the listing's order, and writes the same
///   lines without the prefix into
///   `$XDG_STATE_HOME/gandr/host-tools-needs.txt`; with no lack, it removes
///   that file. With a pin, it then prints the host's mise against the pin. The
///   result is success when nothing failed and nothing lacks, and the refusal's
///   code otherwise.
/// - provides: the whole subcommand.
/// - fails: [`HostToolsError::Io`] or [`HostToolsError::Toml`] when the table,
///   the lock or the configuration cannot be read; every refusal of [`plan()`];
///   [`HostToolsError::Command`] when mise cannot answer the check;
///   [`HostToolsError::Listing`] when its answer is not the JSON the check
///   reads; [`HostToolsError::Output`] when standard output cannot be written.
/// - panics: none.
/// - executable: none — the outcome is the keys on disk, the receivers'
///   directories and the bytes on standard output.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — a key that stands is kept; a build that the host's
///   configuration refuses is named, and the run reports a failure; a push with
///   no receiver does nothing; a refused copy is named, and the run reports a
///   failure; a host that lacks a tool names it and records the need; a host
///   that lacks nothing clears its needs.
/// - witness: `tests::cli::a_key_that_stands_is_kept_and_exits_zero`
/// - witness: `tests::cli::a_build_the_host_refuses_is_named_and_exits_two`
/// - witness: `tests::cli::a_push_with_no_receiver_does_nothing`
/// - witness: `tests::cli::a_refused_copy_is_named_and_exits_two`
/// - witness: `tests::cli::a_host_that_lacks_a_tool_names_it_and_exits_two`
/// - witness: `tests::cli::a_host_that_lacks_no_tool_exits_zero_and_clears_its_needs`
fn run(cli: Cli) -> Result<ExitCode, HostToolsError>
{
    let mut code = ExitCode::SUCCESS;
    match cli.command {
        Command::Build { target, inputs } => {
            let read = Read::new(inputs)?;
            build_target(&read, &Target::from(target.as_str()), &[], &mut code)?;
            prune_scratch(&read, &mut code)?;
        },
        Command::Push { inputs } => {
            let read = Read::new(inputs)?;
            if read.host.receiver.is_empty() {
                return Ok(code);
            }
            update_host(&read, None, &mut code)?;
            let mut by_target: BTreeMap<&Target, Vec<&Receiver>> = BTreeMap::new();
            for receiver in &read.host.receiver {
                by_target
                    .entry(&receiver.target)
                    .or_default()
                    .push(receiver);
            }
            for (target, receivers) in &by_target {
                build_target(&read, target, receivers, &mut code)?;
            }
            for receiver in read
                .host
                .receiver
                .iter()
                .filter(|receiver| receiver.mise.is_none())
            {
                update_host(&read, Some(receiver), &mut code)?;
            }
            prune_scratch(&read, &mut code)?;
        },
        Command::Check { mise_version } => check(
            mise_version.as_deref().map(Version::from).as_ref(),
            &mut code,
        )?,
    }
    Ok(code)
}

/// A question that the check puts to mise.
#[derive(Clone, Copy, Debug)]
enum Query
{
    /// The tools of the checkout, `mise ls --current --json`.
    Tools,
    /// The tools that the host disables, `mise settings get disable_tools`.
    Disabled,
    /// The version of mise, `mise --version`.
    Version,
}

/// Read the tools of the checkout in the working directory that this host
/// lacks, and print one line for each, then the host's mise against `pin`.
/// A lack sets `code` to the refusal's code.
///
/// # Specification
/// trivial.
fn check(
    pin: Option<&Version>,
    code: &mut ExitCode,
) -> Result<(), HostToolsError>
{
    let platform = Platform::host();
    let listing = Listing::read(&mise(Query::Tools)?)?;
    let off = disabled(&mise(Query::Disabled)?)?;
    let checkout = std::env::current_dir().map_err(|error| HostToolsError::Io {
        path: PathBuf::from("."),
        message: error.to_string(),
    })?;
    let found = lacks(&listing, &off, Machine::host(), &checkout)?;
    let mut needs = String::new();
    for lack in &found {
        say(format_args!("host-tools: {platform} {lack}"))?;
        writeln!(needs, "{platform} {lack}").map_err(|error| HostToolsError::Output {
            message: error.to_string(),
        })?;
    }
    let needs_file = state_home().join("gandr").join("host-tools-needs.txt");
    let io = |error: std::io::Error| HostToolsError::Io {
        path: needs_file.clone(),
        message: error.to_string(),
    };
    if found.is_empty() {
        match std::fs::remove_file(&needs_file) {
            Err(error) if error.kind() != std::io::ErrorKind::NotFound => return Err(io(error)),
            Ok(()) | Err(_) => {},
        }
    }
    else {
        *code = ExitCode::from(REFUSED);
        if let Some(parent) = needs_file.parent() {
            std::fs::create_dir_all(parent).map_err(io)?;
        }
        std::fs::write(&needs_file, needs).map_err(io)?;
    }
    let Some(pin) = pin
    else {
        return Ok(());
    };
    let version = mise(Query::Version)?;
    let text: &str = version.as_ref();
    let running = text.split_whitespace().next().unwrap_or_default();
    if *pin == *running {
        say(format_args!("{platform} runs mise {running}, the pin"))
    }
    else {
        say(format_args!(
            "{platform} runs mise {running}, off the pin {pin}"
        ))
    }
}

/// Put `query` to mise in the working directory, and give its standard
/// output.
///
/// # Specification
/// trivial.
fn mise(query: Query) -> Result<Json, HostToolsError>
{
    let args: &[&str] = match query {
        Query::Tools => &["ls", "--current", "--json"],
        Query::Disabled => &["settings", "get", "disable_tools"],
        Query::Version => &["--version"],
    };
    let line = format!("mise {}", args.join(" "));
    let output = std::process::Command::new("mise")
        .args(args)
        .output()
        .map_err(|error| HostToolsError::Command {
            key: "mise".to_owned(),
            command: line.clone(),
            message: error.to_string(),
        })?;
    if !output.status.success() {
        return Err(HostToolsError::Command {
            key: "mise".to_owned(),
            command: line,
            message: format!(
                "exits with {}: {}",
                output.status,
                String::from_utf8_lossy(&output.stderr).trim()
            ),
        });
    }
    Ok(Json::from(String::from_utf8_lossy(&output.stdout).as_ref()))
}

impl Read
{
    /// Read the table, the lock and the builder's configuration that
    /// `inputs` names, and make the directory of the logs.
    ///
    /// # Specification
    /// trivial.
    fn new(inputs: Inputs) -> Result<Self, HostToolsError>
    {
        let builds = Builds::read(&Input::read(&inputs.builds)?)?;
        let lock = Lock::read(&Input::read(&inputs.lock)?)?;
        let host_path = inputs
            .host
            .unwrap_or_else(|| config_home().join("gandr").join("host-tools.toml"));
        let host = if host_path.is_file() {
            Host::read(&Input::read(&host_path)?)?
        }
        else {
            Host::default()
        };
        let logs = inputs.into.join(".logs");
        std::fs::create_dir_all(&logs).map_err(|error| HostToolsError::Io {
            path: logs.clone(),
            message: error.to_string(),
        })?;
        Ok(Self {
            builds,
            lock,
            host,
            pin: Version::from(inputs.mise_version.as_str()),
            into: inputs.into,
            logs,
        })
    }
}

/// Build each tool of `target` whose key does not stand, and copy each key
/// that stands at the end of its build to each of `receivers`. A failure
/// sets `code` to the refusal's code.
///
/// # Specification
/// trivial.
fn build_target(
    read: &Read,
    target: &Target,
    receivers: &[&Receiver],
    code: &mut ExitCode,
) -> Result<(), HostToolsError>
{
    let jobs = plan(&read.builds, &read.lock, &read.pin, target)?;
    for &receiver in receivers.iter().filter(|_| !jobs.is_empty()) {
        let mut processes = Processes {
            log: read.logs.join(format!("{}.settings.log", receiver.host)),
        };
        match settle(receiver, &read.into, &mut processes) {
            Ok(Pushed::Standing | Pushed::Skipped) => {},
            Ok(Pushed::Pushed) => say(format_args!(
                "turned automatic installs off on {}",
                receiver.host
            ))?,
            Err(error) => {
                *code = ExitCode::from(REFUSED);
                say(format_args!(
                    "failed to turn automatic installs off on {}: {error}",
                    receiver.host
                ))?;
            },
        }
    }
    for job in &jobs {
        let started = std::time::Instant::now();
        let mut processes = Processes {
            log: read.logs.join(format!(
                "{}.{}.{}.log",
                job.target, job.install_name, job.version
            )),
        };
        match build(job, &read.into, &read.host, &mut processes) {
            Ok(Built::Kept) => say(format_args!("kept {} {}", job.key, job.version))?,
            Ok(Built::Built) => say(format_args!(
                "built {} {} in {} s",
                job.key,
                job.version,
                started.elapsed().as_secs()
            ))?,
            Err(error) => {
                *code = ExitCode::from(REFUSED);
                say(format_args!("failed {} {}: {error}", job.key, job.version))?;
                continue;
            },
        }
        match retire(&read.into, job) {
            Ok(versions) => {
                for version in &versions {
                    say(format_args!("retired {} {version}", job.key))?;
                }
            },
            Err(error) => {
                *code = ExitCode::from(REFUSED);
                say(format_args!("failed to retire {}: {error}", job.key))?;
            },
        }
        for &receiver in receivers {
            match push(job, &read.into, receiver, &mut processes) {
                Ok(Pushed::Standing | Pushed::Skipped) => {},
                Ok(Pushed::Pushed) => say(format_args!(
                    "pushed {} {} to {}",
                    job.key, job.version, receiver.host
                ))?,
                Err(error) => {
                    *code = ExitCode::from(REFUSED);
                    say(format_args!(
                        "failed to push {} {} to {}: {error}",
                        job.key, job.version, receiver.host
                    ))?;
                },
            }
        }
    }
    Ok(())
}

/// Bring mise to the pin on `receiver`, or on the builder for `None`. A
/// failure sets `code` to the refusal's code.
///
/// # Specification
/// trivial.
fn update_host(
    read: &Read,
    receiver: Option<&Receiver>,
    code: &mut ExitCode,
) -> Result<(), HostToolsError>
{
    let host = receiver.map_or_else(
        || "the builder".to_owned(),
        |receiver| receiver.host.to_string(),
    );
    let mut processes = Processes {
        log: read.logs.join(format!("mise.{}.update.log", read.pin)),
    };
    match update(receiver, &read.into, &read.pin, &mut processes) {
        Ok(Pushed::Standing | Pushed::Skipped) => Ok(()),
        Ok(Pushed::Pushed) => say(format_args!("updated mise on {host} to {}", read.pin)),
        Err(error) => {
            *code = ExitCode::from(REFUSED);
            say(format_args!(
                "failed to update mise on {host} to {}: {error}",
                read.pin
            ))
        },
    }
}

/// Remove the scratch of the builds when no build holds it. A failure sets
/// `code` to the refusal's code.
///
/// # Specification
/// trivial.
fn prune_scratch(
    read: &Read,
    code: &mut ExitCode,
) -> Result<(), HostToolsError>
{
    match prune(&read.into) {
        Ok(Pruned::Removed) => say(format_args!("pruned the scratch")),
        Ok(Pruned::Busy | Pruned::Absent) => Ok(()),
        Err(error) => {
            *code = ExitCode::from(REFUSED);
            say(format_args!("failed to prune the scratch: {error}"))
        },
    }
}

/// Print `line` on standard output.
///
/// # Specification
/// trivial.
fn say(line: core::fmt::Arguments<'_>) -> Result<(), HostToolsError>
{
    writeln!(std::io::stdout(), "{line}").map_err(|error| HostToolsError::Output {
        message: error.to_string(),
    })
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

/// The user's state directory: `$XDG_STATE_HOME`, else `$HOME/.local/state`.
///
/// # Specification
/// trivial.
fn state_home() -> PathBuf
{
    std::env::var_os("XDG_STATE_HOME")
        .filter(|home| !home.is_empty())
        .map_or_else(
            || PathBuf::from(std::env::var_os("HOME").unwrap_or_default()).join(".local/state"),
            PathBuf::from,
        )
}
