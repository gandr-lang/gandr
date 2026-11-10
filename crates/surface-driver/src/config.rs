//! The user's configuration: the settings every face reads before its flags.
//!
//! # One file under the XDG configuration directory
//!
//! `gandr` reads `gandr/config.toml` under the user's configuration
//! directory: `$XDG_CONFIG_HOME` when it names an absolute path, and
//! `$HOME/.config` otherwise. It sets the spelling every face writes a
//! construct that has a glyph in, and whose recorded kernel verdicts a
//! `check` believes:
//!
//! ```toml
//! [presentation]
//! spelling = "ascii" # or "unicode", the default
//!
//! [kernel]
//! policy = "recheck" # or "trusted", the default
//! trusted = ["<64 hexadecimal digits>"] # beside this installation's key
//!
//! [reals]
//! profile = "bounded" # or "default", the default
//! ```
//!
//! The key path is the editor's `gandr.presentation.spelling` setting, and a
//! package's `package.gandr.toml` carries the same table, which the
//! dispatcher's presentation reader reads for both. The global `--spelling`
//! flag outranks the file for one invocation, and a project's manifest and an
//! editor's own setting outrank it for that editor's connection. A file that is
//! absent configures nothing; one that cannot be read, is not TOML, or names a
//! spelling there is none of is a fault: the driver says so on standard
//! error, `gandr: <path>: <fault>`, and exits `2` before any verb runs.
//!
//! A process reads and parses the file at most once, the first time a table
//! of it is asked for: [`Configuration`] holds the document, and the
//! presentation and the kernel policy are each read from it. A flag that
//! answers the spelling leaves the file unread until a `check` asks its
//! kernel policy.
//!
//! **Alternatives.** A directories crate (`etcetera`, `directories`) resolves
//! each platform's native directory, `~/Library/Application Support` on macOS
//! among them; one path rule on every platform is what a user documents and
//! what command-line tools on macOS follow, and it is two reads of the
//! environment. An environment variable would be a third layer the flag
//! already covers.
//!
//! **Reversal.** A request for each platform's native directory takes the
//! crate; a second setting that a project overrides key by key takes a layered
//! merge.
//!
//! # The kernel's key and its verdicts
//!
//! A `check` keeps the verdicts its kernel checked under a receipt signed with
//! this installation's key, `gandr/kernel.key` under the configuration
//! directory, minted from the operating system's entropy the first time a
//! `check` needs it; the receipts go to `gandr/verdicts/receipts` under the
//! cache directory. A later `check` admits a declaration on a recorded verdict
//! only when a key its policy trusts signed it: this installation's own, and
//! each that `kernel.trusted` lists by its public half, which `check
//! --verbosity detailed` prints after `signed by`. `policy = "recheck"`, or
//! `--recheck` for one invocation, checks every declaration and records
//! nothing. The `[kernel]` table is the user's file's alone: whose keys to
//! believe is an installation's decision, never a project's, so the
//! dispatcher's presentation reader does not read it. A table that names no
//! policy there is, or a key that is not one, is a fault as a bad spelling is.
//!
//! The same key and policy sign and believe the certified strata a `ua`
//! statement reads, kept in `gandr/verdicts/strata`. A later `check` replays
//! a stratum it believes against its catalogue, and certifies afresh one that
//! does not replay. `--recheck` reads and keeps no stratum.
//!
//! # The quotas of the exact reals
//!
//! `gandr run` serves the `Reals` operations of its program under one profile
//! of quotas, which `reals.profile` names. `default` takes the quotas of the
//! crate, and `bounded` takes smaller ones for plans that the user does not
//! trust. A file with no `[reals]` table takes `default`. A name that is no
//! profile is a fault, as a bad spelling is, and the run does not start. The
//! table is the user's file's alone: the quotas of a host are a decision of an
//! installation, never of a project.
//!
//! # Saves under the XDG cache directory
//!
//! The language server keeps the checkpoints an editor's save persists in
//! `gandr/checkpoints` under the user's cache directory: `$XDG_CACHE_HOME`
//! when it names an absolute path, and `$HOME/.cache` otherwise, by the same
//! rule. The directory is a cache: removing it costs the next open a whole
//! judgement, and nothing else. The kernel's receipts sit beside them, in
//! `gandr/verdicts`: removing it costs the next `check` a whole kernel pass
//! and each stratum's certification.
//!
//! # The store under the XDG data directory
//!
//! `gandr check` and `gandr lock` open the storage tier's store at
//! `gandr/store` under the user's data directory: `$XDG_DATA_HOME` when it
//! names an absolute path, and `$HOME/.local/share` otherwise, by the same
//! rule. A package's lock commits each dependency's identity there and records
//! the pointer. A pointer is a function of the identity alone, and each check
//! commits every identity again before it reads one, so removing the
//! directory costs the next check those commits and leaves every lock as it
//! stands.
//!
//! # Calls under the XDG state directory
//!
//! `gandr serve --port` keeps each call its toolset acknowledged, until a
//! runtime takes or refuses its result, in `gandr/calls` under the user's state
//! directory: `$XDG_STATE_HOME` when it names an absolute path, and
//! `$HOME/.local/state` otherwise, by the same rule. The file of a workspace
//! holds only the calls still pending. Removing it loses those calls: a hub
//! that restarts cannot answer them, and their callers wait on them.
//!
//! # The retries of the toolset
//!
//! The toolset of `gandr serve --port` tries a callback that fails again, as
//! the `[deliveries]` table names:
//!
//! ```toml
//! [deliveries]
//! first_ms = 250 # the wait before the first retry, the default
//! longest_ms = 30000 # the longest wait between two attempts, the default
//! retries = 8 # the attempts after the first, the default
//! ```
//!
//! Each wait doubles the wait before it, up to `longest_ms`. A key that is
//! absent takes its default. A value that is not a whole number in its range,
//! or a `longest_ms` shorter than `first_ms`, is a fault, as a bad spelling
//! is, and the hub does not start. The table is the user's file's alone: how
//! long a host waits on its runtimes is a decision of an installation, never
//! of a project.

use alloc::collections::BTreeSet;
use core::cell::OnceCell;
use core::fmt;
#[cfg(unix)]
use core::time::Duration;
use std::io;
use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
use gandr_kernel_core::verdict::KernelIdentity;
use gandr_surface_dispatcher::Presentation;
use gandr_surface_dispatcher::PresentationFault;
use gandr_surface_dispatcher::RealsProfile;
use gandr_surface_dispatcher::presented;
#[cfg(unix)]
use gandr_surface_mcp::Policy;
#[cfg(unix)]
use gandr_surface_mcp::Retries;

/// Whose recorded kernel verdicts a `check` believes.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Kernel
{
    /// `policy = "trusted"`, the default: a receipt this installation's key
    /// signed, or one of these.
    Trusting(BTreeSet<KernelIdentity>),
    /// `policy = "recheck"`: every declaration is checked, and nothing kept.
    Rechecking,
}

impl Default for Kernel
{
    /// Trusting this installation's key alone.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self::Trusting(BTreeSet::new())
    }
}

/// Why a table of the configuration file could not be read: its `[kernel]`,
/// its `[reals]` or its `[deliveries]`.
#[derive(Debug)]
pub struct TableFault
{
    /// The file.
    path: PathBuf,
    /// What went wrong, in words.
    why: String,
}

impl fmt::Display for TableFault
{
    /// Writes `<path>: <why>`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "{}: {}", self.path.display(), self.why)
    }
}

/// The configuration file under `home`, the XDG configuration home, or under
/// `fallback`, the user's home directory, when `home` names none.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `<home>/gandr/config.toml` when `home` is an absolute path, else
///   `<fallback>/.config/gandr/config.toml` when `fallback` is present, else
///   absent.
/// - provides: the one path rule the configuration is read at.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an absolute home, a relative one beside a fallback, and
///   neither are each resolved.
/// - witness: `config::tests::the_file_sits_under_the_xdg_configuration_home`
#[spec(ensures: |ref ret| ret.as_ref().is_none_or(|path| path.ends_with("gandr/config.toml")))]
fn located(
    home: Option<PathBuf>,
    fallback: Option<PathBuf>,
) -> Option<PathBuf>
{
    Some(
        directory(home, fallback, Path::new(".config"))?
            .join("gandr")
            .join("config.toml"),
    )
}

/// The user's directory of a kind: `home` when it is an absolute path, else
/// `default` under `fallback`, the user's home directory.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `home` when it is absolute, else `<fallback>/<default>` when
///   `fallback` is present, else absent.
/// - provides: the XDG rule the configuration and the cache share.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`located`] and [`checkpointed`].
/// - witness: `config::tests::the_file_sits_under_the_xdg_configuration_home`
/// - witness: `config::tests::saves_sit_under_the_xdg_cache_home_1816`
#[spec(ensures: |ref ret| ret.as_ref().is_none_or(|path| path.is_absolute() || path.ends_with(default)))]
fn directory(
    home: Option<PathBuf>,
    fallback: Option<PathBuf>,
    default: &Path,
) -> Option<PathBuf>
{
    match home {
        Some(home) if home.is_absolute() => Some(home),
        Some(_) | None => Some(fallback?.join(default)),
    }
}

/// The directory saves keep their checkpoints in, under `home`, the XDG cache
/// home, or under `fallback`, the user's home directory, when `home` names
/// none.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `<home>/gandr/checkpoints` when `home` is an absolute path, else
///   `<fallback>/.cache/gandr/checkpoints` when `fallback` is present, else
///   absent.
/// - provides: the one path rule saves are kept at.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an absolute home, a relative one beside a fallback, and
///   neither are each resolved.
/// - witness: `config::tests::saves_sit_under_the_xdg_cache_home_1816`
#[spec(ensures: |ref ret| ret.as_ref().is_none_or(|path| path.ends_with("gandr/checkpoints")))]
fn checkpointed(
    home: Option<PathBuf>,
    fallback: Option<PathBuf>,
) -> Option<PathBuf>
{
    Some(
        directory(home, fallback, Path::new(".cache"))?
            .join("gandr")
            .join("checkpoints"),
    )
}

/// The directory saves keep their checkpoints in, as [`checkpointed`] names it
/// under the process's environment.
///
/// # Specification
/// - requires: nothing.
/// - ensures: as [`checkpointed`] of `$XDG_CACHE_HOME` and `$HOME`.
/// - provides: where the language server keeps saves.
/// - fails: never.
/// - panics: none.
/// - executable: none — the result depends on the environment, which the
///   clauses cannot observe.
///
/// # Adequacy
/// - hypothesis: L3 — as [`checkpointed`].
/// - witness: `config::tests::saves_sit_under_the_xdg_cache_home_1816`
pub fn checkpoints() -> Option<PathBuf>
{
    checkpointed(
        std::env::var_os("XDG_CACHE_HOME").map(PathBuf::from),
        std::env::var_os("HOME").map(PathBuf::from),
    )
}

/// The directory the engine hub's toolset keeps its pending calls in,
/// `gandr/calls` under the user's state directory.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `<home>/gandr/calls` under `$XDG_STATE_HOME` and `$HOME` by
///   [`directory`]'s rule, with `.local/state` the default; absent when neither
///   names a directory.
/// - provides: where `gandr serve --port` keeps the rows of its calls.
/// - fails: never.
/// - panics: none.
/// - executable: none — the result depends on the environment.
///
/// # Adequacy
/// - hypothesis: L3 — a hub given a port under a scratch state home serves its
///   toolset.
/// - witness: `tests::cli::serve_offers_the_toolset_on_a_named_port`
#[cfg(unix)]
pub fn calls() -> Option<PathBuf>
{
    Some(
        directory(
            std::env::var_os("XDG_STATE_HOME").map(PathBuf::from),
            std::env::var_os("HOME").map(PathBuf::from),
            Path::new(".local/state"),
        )?
        .join("gandr")
        .join("calls"),
    )
}

/// This installation's kernel signing key, `gandr/kernel.key` under the
/// configuration directory [`located`] reads the file in.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `<home>/gandr/kernel.key` under `$XDG_CONFIG_HOME` and `$HOME` by
///   [`directory`]'s rule; absent when neither names a directory.
/// - fails: never.
/// - panics: none.
/// - executable: none — the result depends on the environment.
///
/// # Adequacy
/// - hypothesis: L3 — a `check` under a scratch configuration home mints its
///   key there and recalls under it.
/// - witness: `tests::cli::a_second_check_recalls_what_the_first_recorded_2799`
pub fn kernel_key() -> Option<PathBuf>
{
    Some(
        directory(
            std::env::var_os("XDG_CONFIG_HOME").map(PathBuf::from),
            std::env::var_os("HOME").map(PathBuf::from),
            Path::new(".config"),
        )?
        .join("gandr")
        .join("kernel.key"),
    )
}

/// The directory the store is rooted at, under `home`, the XDG data home, or
/// under `fallback`, the user's home directory, when `home` names none.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `<home>/gandr/store` when `home` is an absolute path, else
///   `<fallback>/.local/share/gandr/store` when `fallback` is present, else
///   absent.
/// - provides: the one path rule the store is rooted at.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an absolute home, a relative one beside a fallback, and
///   neither are each resolved.
/// - witness: `config::tests::the_store_sits_under_the_xdg_data_home_3157`
#[spec(ensures: |ref ret| ret.as_ref().is_none_or(|path| path.ends_with("gandr/store")))]
fn stored(
    home: Option<PathBuf>,
    fallback: Option<PathBuf>,
) -> Option<PathBuf>
{
    Some(
        directory(home, fallback, Path::new(".local/share"))?
            .join("gandr")
            .join("store"),
    )
}

/// The directory the store is rooted at, as [`stored`] names it under the
/// process's environment.
///
/// # Specification
/// - requires: nothing.
/// - ensures: as [`stored`] of `$XDG_DATA_HOME` and `$HOME`.
/// - provides: where `gandr check` and `gandr lock` open the store.
/// - fails: never.
/// - panics: none.
/// - executable: none — the result depends on the environment, which the
///   clauses cannot observe.
///
/// # Adequacy
/// - hypothesis: L3 — as [`stored`].
/// - witness: `config::tests::the_store_sits_under_the_xdg_data_home_3157`
pub fn store() -> Option<PathBuf>
{
    stored(
        std::env::var_os("XDG_DATA_HOME").map(PathBuf::from),
        std::env::var_os("HOME").map(PathBuf::from),
    )
}

/// The directory the installed toolchains are named in and the file the
/// default toolchain is named in, under the XDG data home or `$HOME` by
/// [`directory`]'s rule.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `<data>/gandr/toolchains` and `<data>/gandr/toolchain`, where
///   `<data>` is `$XDG_DATA_HOME` when absolute, else `$HOME/.local/share`;
///   absent when neither names a directory.
/// - provides: where `gandr toolchain` links and the proxy selects.
/// - fails: never.
/// - panics: none.
/// - executable: none — the result depends on the environment, which the
///   clauses cannot observe.
///
/// # Adequacy
/// - hypothesis: L3 — a link made under a scratch data home is selected from
///   it.
/// - witness: `tests::cli::a_linked_toolchain_is_the_one_the_proxy_runs`
pub fn toolchains() -> Option<(PathBuf, PathBuf)>
{
    let data = directory(
        std::env::var_os("XDG_DATA_HOME").map(PathBuf::from),
        std::env::var_os("HOME").map(PathBuf::from),
        Path::new(".local/share"),
    )?
    .join("gandr");
    Some((data.join("toolchains"), data.join("toolchain")))
}

/// The directory the kernel's receipts and strata are kept under,
/// `gandr/verdicts` under the cache directory [`checkpoints`] sits in.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `<home>/gandr/verdicts` under `$XDG_CACHE_HOME` and `$HOME` by
///   [`directory`]'s rule; absent when neither names a directory.
/// - fails: never.
/// - panics: none.
/// - executable: none — the result depends on the environment.
///
/// # Adequacy
/// - hypothesis: L3 — as [`kernel_key`].
/// - witness: `tests::cli::a_second_check_recalls_what_the_first_recorded_2799`
pub fn verdicts() -> Option<PathBuf>
{
    Some(
        directory(
            std::env::var_os("XDG_CACHE_HOME").map(PathBuf::from),
            std::env::var_os("HOME").map(PathBuf::from),
            Path::new(".cache"),
        )?
        .join("gandr")
        .join("verdicts"),
    )
}

/// The directory the checkouts of `gh:` coordinates are kept under,
/// `gandr/checkouts` under the cache directory [`checkpoints`] sits in.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `<home>/gandr/checkouts` under `$XDG_CACHE_HOME` and `$HOME` by
///   [`directory`]'s rule; absent when neither names a directory.
/// - fails: never.
/// - panics: none.
/// - executable: none — the result depends on the environment.
///
/// # Adequacy
/// - hypothesis: L3 — a `gh:` dependency locked by one run is read from its
///   checkout by the next.
/// - witness: `tests::cli::a_gh_coordinate_is_fetched_locked_and_read_again_4714`
pub fn checkouts() -> Option<PathBuf>
{
    Some(
        directory(
            std::env::var_os("XDG_CACHE_HOME").map(PathBuf::from),
            std::env::var_os("HOME").map(PathBuf::from),
            Path::new(".cache"),
        )?
        .join("gandr")
        .join("checkouts"),
    )
}

/// The user's configuration file, read and parsed at most once a process: its
/// `[presentation]`, its `[kernel]`, its `[reals]` and its `[deliveries]` are
/// tables of the one file.
///
/// # Specification
/// trivial.
#[derive(Debug, Default)]
#[repr(transparent)]
pub struct Configuration
{
    /// The file, read on the first question asked of it.
    read: OnceCell<Read>,
}

/// What reading the configuration file found.
///
/// # Specification
/// trivial.
#[derive(Debug)]
enum Read
{
    /// No directory is named, or no file is there.
    Absent,
    /// The file's text, parsed as TOML.
    Parsed
    {
        /// The file.
        path: PathBuf,
        /// The document, or why its text is not TOML.
        document: Result<toml::Table, toml::de::Error>,
    },
    /// The file exists and cannot be read.
    Unreadable
    {
        /// The file.
        path: PathBuf,
        /// The operating system's error.
        error: io::Error,
    },
}

impl Configuration
{
    /// The file [`located`] names under the process's environment, read and
    /// parsed the first time it is asked for.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the same reading on every call: the file is read once.
    /// - provides: one read of the file for every table it holds.
    /// - fails: never; a fault is the reading's, for each table to report.
    /// - panics: none.
    /// - executable: none — the result depends on the environment and the file
    ///   system, which the clauses cannot observe.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the spelling and a check's kernel policy each read
    ///   the file through the binary, the policy after the spelling in one
    ///   process.
    /// - witness: `tests::cli::the_configured_spelling_prints_and_the_flag_outranks_it_782`
    /// - witness: `tests::cli::a_second_check_recalls_what_the_first_recorded_2799`
    fn read(&self) -> &Read
    {
        self.read.get_or_init(|| {
            let home = std::env::var_os("XDG_CONFIG_HOME").map(PathBuf::from);
            let fallback = std::env::var_os("HOME").map(PathBuf::from);
            let Some(path) = located(home, fallback)
            else {
                return Read::Absent;
            };
            match std::fs::read_to_string(&path) {
                Ok(text) => Read::Parsed {
                    path,
                    document: toml::from_str(&text),
                },
                Err(error) if error.kind() == io::ErrorKind::NotFound => Read::Absent,
                Err(error) => Read::Unreadable { path, error },
            }
        })
    }

    /// The presentation the user's configuration file sets.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`presented`] reads the file's document; none when no
    ///   directory is named or no file is there.
    /// - provides: the settings `main` reads before any verb runs.
    /// - fails: a file that exists and cannot be read, and the faults of
    ///   [`presented`].
    /// - panics: none.
    /// - executable: none — the result depends on the environment and the file
    ///   system, which the clauses cannot observe.
    ///
    /// # Errors
    /// [`PresentationFault::Unreadable`], [`PresentationFault::Malformed`] and
    /// [`PresentationFault::Unset`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a configured spelling is printed, a flag outranks it,
    ///   and a malformed file stops the run, each through the binary.
    /// - witness: `tests::cli::the_configured_spelling_prints_and_the_flag_outranks_it_782`
    pub fn presentation(&self) -> Result<Presentation, PresentationFault>
    {
        match *self.read() {
            Read::Absent => Ok(Presentation::default()),
            Read::Parsed {
                ref path,
                ref document,
            } => presented(path.clone(), document.as_ref()),
            Read::Unreadable {
                ref path,
                ref error,
            } => Err(PresentationFault::Unreadable {
                path: path.clone(),
                error: io::Error::new(error.kind(), error.to_string()),
            }),
        }
    }

    /// The kernel policy the user's configuration file names.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`kernel_parsed`] reads the file's document; the default
    ///   policy when no directory is named or no file is there.
    /// - provides: whose verdicts a `check` believes.
    /// - fails: a file that exists and cannot be read, and the faults of
    ///   [`kernel_parsed`].
    /// - panics: none.
    /// - executable: none — the result depends on the environment and the file
    ///   system.
    ///
    /// # Errors
    /// [`TableFault`], naming the file.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a key `kernel.trusted` lists is believed through the
    ///   binary.
    /// - witness: `tests::cli::a_second_check_recalls_what_the_first_recorded_2799`
    pub fn kernel(&self) -> Result<Kernel, TableFault>
    {
        match *self.read() {
            Read::Absent => Ok(Kernel::default()),
            Read::Parsed {
                ref path,
                ref document,
            } => kernel_parsed(path, document.as_ref()),
            Read::Unreadable {
                ref path,
                ref error,
            } => Err(TableFault {
                path: path.clone(),
                why: format!("cannot be read: {error}"),
            }),
        }
    }

    /// The quotas of the exact reals that the user's configuration file names.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`reals_parsed`] reads the file's document; the default
    ///   profile when no directory is named or no file is there.
    /// - provides: the quotas of the `Reals` operations of a `run`.
    /// - fails: a file that exists and cannot be read, and the faults of
    ///   [`reals_parsed`].
    /// - panics: none.
    /// - executable: none — the result depends on the environment and the file
    ///   system.
    ///
    /// # Errors
    /// [`TableFault`], naming the file.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a configured profile bounds a run, and an unknown one
    ///   stops it before it starts, each through the binary.
    /// - witness: `tests::reals::a_configured_profile_bounds_the_run_5704`
    pub fn reals(&self) -> Result<RealsProfile, TableFault>
    {
        match *self.read() {
            Read::Absent => Ok(RealsProfile::default()),
            Read::Parsed {
                ref path,
                ref document,
            } => reals_parsed(path, document.as_ref()),
            Read::Unreadable {
                ref path,
                ref error,
            } => Err(TableFault {
                path: path.clone(),
                why: format!("cannot be read: {error}"),
            }),
        }
    }

    /// The policy that retries the deliveries of the toolset, as the user's
    /// configuration file names it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`deliveries_parsed`] reads the file's document; the
    ///   default policy when no directory is named or no file is there.
    /// - provides: the retries of `gandr serve --port`.
    /// - fails: a file that exists and cannot be read, and the faults of
    ///   [`deliveries_parsed`].
    /// - panics: none.
    /// - executable: none — the result depends on the environment and the file
    ///   system.
    ///
    /// # Errors
    /// [`TableFault`], naming the file.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each key, each default, a value out of its range and
    ///   a misshapen table are each read.
    /// - witness: `config::tests::a_delivery_policy_is_read_and_a_bad_one_refused_6340`
    #[cfg(unix)]
    pub fn deliveries(&self) -> Result<Policy, TableFault>
    {
        match *self.read() {
            Read::Absent => Ok(Policy::default()),
            Read::Parsed {
                ref path,
                ref document,
            } => deliveries_parsed(path, document.as_ref()),
            Read::Unreadable {
                ref path,
                ref error,
            } => Err(TableFault {
                path: path.clone(),
                why: format!("cannot be read: {error}"),
            }),
        }
    }
}

/// The kernel policy `read`, the contents of `path` parsed as TOML, names.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `kernel.policy` reads `trusted`, or nothing, as
///   [`Kernel::Trusting`] the keys `kernel.trusted` lists, and `recheck` as
///   [`Kernel::Rechecking`]; a document without a `kernel` table is the
///   default. Text that is not TOML, a `kernel` that is not a table, a policy
///   that is neither name, and a trusted key that is not 64 hexadecimal digits
///   are each a [`TableFault`].
/// - provides: the reading of the table, apart from reading the file.
/// - fails: the faults the ensures clause names.
/// - panics: none.
/// - executable: none — the clauses relate the document's text to the policy it
///   names, which the result alone does not carry.
///
/// # Errors
/// [`TableFault`], as above.
///
/// # Adequacy
/// - hypothesis: L3 — each policy, a trusted key, a short key, a key with a
///   digit that is not hexadecimal, an unknown policy and a misshapen table are
///   each read.
/// - witness: `config::tests::a_kernel_policy_is_read_and_a_bad_one_refused_2799`
fn kernel_parsed(
    path: &Path,
    read: Result<&toml::Table, &toml::de::Error>,
) -> Result<Kernel, TableFault>
{
    let fault = |why: String| TableFault {
        path: path.to_path_buf(),
        why,
    };
    let table = match read {
        Ok(table) => table,
        Err(error) => return Err(fault(format!("not TOML: {}", error.message()))),
    };
    let read = match table.get("kernel") {
        None => Ok(Kernel::default()),
        Some(&toml::Value::Table(ref kernel)) => kernel_read(kernel),
        Some(other) => Err(format!(
            "`kernel` is of type {}, not a table",
            other.type_str()
        )),
    };
    read.map_err(fault)
}

/// The profile that `read`, the contents of `path` parsed as TOML, names.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `reals.profile` reads the name of a [`RealsProfile`] as that
///   profile; a document without a `reals` table, or a table that names no
///   profile, is the default. Text that is not TOML, a `reals` that is not a
///   table, and a profile that is no name of [`RealsProfile::ALL`] are each a
///   [`TableFault`].
/// - provides: the reading of the table, apart from reading the file.
/// - fails: the faults the ensures clause names.
/// - panics: none.
/// - executable: none — the clauses relate the document's text to the profile
///   it names, which the result alone does not carry.
///
/// # Errors
/// [`TableFault`], as above.
///
/// # Adequacy
/// - hypothesis: L3 — each profile, no profile, an unknown name, a profile of
///   another type and a `reals` that is no table are each read.
/// - witness: `config::tests::a_reals_profile_is_read_and_an_unknown_one_refused_5704`
fn reals_parsed(
    path: &Path,
    read: Result<&toml::Table, &toml::de::Error>,
) -> Result<RealsProfile, TableFault>
{
    let fault = |why: String| TableFault {
        path: path.to_path_buf(),
        why,
    };
    let table = match read {
        Ok(table) => table,
        Err(error) => return Err(fault(format!("not TOML: {}", error.message()))),
    };
    let profile = match table.get("reals") {
        None => return Ok(RealsProfile::default()),
        Some(&toml::Value::Table(ref reals)) => reals.get("profile"),
        Some(other) => {
            return Err(fault(format!(
                "`reals` is of type {}, not a table",
                other.type_str()
            )));
        },
    };
    let Some(value) = profile
    else {
        return Ok(RealsProfile::default());
    };
    let named = value.as_str().and_then(|name| {
        RealsProfile::ALL
            .into_iter()
            .find(|profile| profile.to_string() == name)
    });
    named.ok_or_else(|| {
        let names: Vec<String> = RealsProfile::ALL
            .iter()
            .map(|profile| format!("`{profile}`"))
            .collect();
        fault(format!(
            "`reals.profile` is {}; it names {}",
            described(value),
            names.join(" or ")
        ))
    })
}

/// The delivery policy that `read`, the contents of `path` parsed as TOML,
/// names.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `deliveries.first_ms`, `deliveries.longest_ms` and
///   `deliveries.retries` read as the policy's first wait, longest wait and
///   retries. A key that is absent, or a document without a `deliveries` table,
///   takes the default. Text that is not TOML, a `deliveries` that is not a
///   table, a wait that is not a whole number of one at least, retries that are
///   not a whole number in the range of `u32`, and a longest wait shorter than
///   the first are each a [`TableFault`].
/// - provides: the reading of the table, apart from reading the file.
/// - fails: the faults the ensures clause names.
/// - panics: none.
/// - executable: none — the clauses relate the document's text to the policy it
///   names, which the result alone does not carry.
///
/// # Errors
/// [`TableFault`], as above.
///
/// # Adequacy
/// - hypothesis: L3 — each key, each default, a wait of zero, retries that are
///   no number, waits in the wrong order and a `deliveries` that is no table
///   are each read.
/// - witness: `config::tests::a_delivery_policy_is_read_and_a_bad_one_refused_6340`
#[cfg(unix)]
fn deliveries_parsed(
    path: &Path,
    read: Result<&toml::Table, &toml::de::Error>,
) -> Result<Policy, TableFault>
{
    let fault = |why: String| TableFault {
        path: path.to_path_buf(),
        why,
    };
    let table = match read {
        Ok(table) => table,
        Err(error) => return Err(fault(format!("not TOML: {}", error.message()))),
    };
    let deliveries = match table.get("deliveries") {
        None => return Ok(Policy::default()),
        Some(&toml::Value::Table(ref deliveries)) => deliveries,
        Some(other) => {
            return Err(fault(format!(
                "`deliveries` is of type {}, not a table",
                other.type_str()
            )));
        },
    };
    let whole = |key: &str, least: u64| match deliveries.get(key) {
        None => Ok(None),
        Some(&toml::Value::Integer(number)) => u64::try_from(number)
            .ok()
            .filter(|&number| number >= least)
            .map(Some)
            .ok_or_else(|| {
                fault(format!(
                    "`deliveries.{key}` is {number}; it is a whole number of {least} at least"
                ))
            }),
        Some(other) => Err(fault(format!(
            "`deliveries.{key}` is {}; it is a whole number",
            described(other)
        ))),
    };
    let default = Policy::default();
    let first = whole("first_ms", 1)?.map_or(default.first, Duration::from_millis);
    let longest = whole("longest_ms", 1)?.map_or(default.longest, Duration::from_millis);
    if longest < first {
        return Err(fault(String::from(
            "`deliveries.longest_ms` is shorter than `deliveries.first_ms`",
        )));
    }
    let retries = match whole("retries", 0)? {
        None => default.retries,
        Some(retries) => Retries(u32::try_from(retries).map_err(|_overflow| {
            fault(format!(
                "`deliveries.retries` is {retries}; it is {} at most",
                u32::MAX
            ))
        })?),
    };
    Ok(Policy {
        first,
        longest,
        retries,
    })
}

/// What a setting holds, in words: a string as itself, quoted; any other
/// value by its type.
///
/// # Specification
/// trivial.
fn described(value: &toml::Value) -> String
{
    match *value {
        toml::Value::String(ref name) => format!("`{name}`"),
        toml::Value::Integer(_)
        | toml::Value::Float(_)
        | toml::Value::Boolean(_)
        | toml::Value::Datetime(_)
        | toml::Value::Array(_)
        | toml::Value::Table(_) => format!("of type {}", value.type_str()),
    }
}

/// The policy the `kernel` table names, or what it holds that names none.
///
/// # Specification
/// trivial.
fn kernel_read(table: &toml::Table) -> Result<Kernel, String>
{
    let keys = "it lists keys of 64 hexadecimal digits";
    let trusted = match table.get("trusted") {
        None => BTreeSet::new(),
        Some(&toml::Value::Array(ref listed)) => listed
            .iter()
            .map(|key| {
                identity(key)
                    .ok_or_else(|| format!("`kernel.trusted` holds {}; {keys}", described(key)))
            })
            .collect::<Result<_, _>>()?,
        Some(other) => return Err(format!("`kernel.trusted` is {}; {keys}", described(other))),
    };
    match table.get("policy") {
        None => Ok(Kernel::Trusting(trusted)),
        Some(&toml::Value::String(ref name)) if name == "trusted" => Ok(Kernel::Trusting(trusted)),
        Some(&toml::Value::String(ref name)) if name == "recheck" => Ok(Kernel::Rechecking),
        Some(other) => Err(format!(
            "`kernel.policy` is {}; it names `trusted` or `recheck`",
            described(other)
        )),
    }
}

/// The key `key` spells, a string of 64 hexadecimal digits.
///
/// # Specification
/// trivial.
fn identity(key: &toml::Value) -> Option<KernelIdentity>
{
    let digits = match *key {
        toml::Value::String(ref hex) => hex.as_bytes(),
        toml::Value::Integer(_)
        | toml::Value::Float(_)
        | toml::Value::Boolean(_)
        | toml::Value::Datetime(_)
        | toml::Value::Array(_)
        | toml::Value::Table(_) => return None,
    };
    if digits.len() != 64 {
        return None;
    }
    let mut bytes = [0_u8; 32];
    for (byte, &[high, low]) in bytes.iter_mut().zip(digits.as_chunks::<2>().0) {
        let high = char::from(high).to_digit(16)?;
        let low = char::from(low).to_digit(16)?;
        *byte = u8::try_from(high.checked_mul(16)?.checked_add(low)?).ok()?;
    }
    Some(KernelIdentity::from(bytes))
}

#[cfg(test)]
mod tests
{
    use alloc::collections::BTreeSet;
    use std::path::Path;
    use std::path::PathBuf;

    use gandr_kernel_core::verdict::KernelIdentity;
    use gandr_surface_dispatcher::RealsProfile;

    use super::Kernel;
    use super::checkpointed;
    #[cfg(unix)]
    use super::deliveries_parsed;
    use super::kernel_parsed;
    use super::located;
    use super::reals_parsed;
    use super::stored;

    #[test]
    fn the_file_sits_under_the_xdg_configuration_home()
    {
        let file = |home: Option<&str>, fallback: Option<&str>| {
            located(home.map(PathBuf::from), fallback.map(PathBuf::from))
        };
        assert_eq!(
            file(Some("/xdg"), Some("/home/user")),
            Some(PathBuf::from("/xdg/gandr/config.toml"))
        );
        assert_eq!(
            file(Some("relative"), Some("/home/user")),
            Some(PathBuf::from("/home/user/.config/gandr/config.toml")),
            "a relative XDG_CONFIG_HOME is ignored, as the specification asks"
        );
        assert_eq!(
            file(None, Some("/home/user")),
            Some(PathBuf::from("/home/user/.config/gandr/config.toml"))
        );
        assert_eq!(file(None, None), None);
    }

    /// #1816: saves are kept under the XDG cache home by the configuration's
    /// own rule.
    #[test]
    fn saves_sit_under_the_xdg_cache_home_1816()
    {
        let directory = |home: Option<&str>, fallback: Option<&str>| {
            checkpointed(home.map(PathBuf::from), fallback.map(PathBuf::from))
        };
        assert_eq!(
            directory(Some("/xdg"), Some("/home/user")),
            Some(PathBuf::from("/xdg/gandr/checkpoints"))
        );
        assert_eq!(
            directory(Some("relative"), Some("/home/user")),
            Some(PathBuf::from("/home/user/.cache/gandr/checkpoints")),
            "a relative XDG_CACHE_HOME is ignored, as the specification asks"
        );
        assert_eq!(
            directory(None, Some("/home/user")),
            Some(PathBuf::from("/home/user/.cache/gandr/checkpoints"))
        );
        assert_eq!(directory(None, None), None);
    }

    /// #2799: the kernel's policy and the keys it trusts are read, and a
    /// policy or a key that names nothing is refused.
    #[test]
    fn a_kernel_policy_is_read_and_a_bad_one_refused_2799()
    {
        let read = |text: &str| {
            kernel_parsed(
                Path::new("/c/gandr/config.toml"),
                toml::from_str(text).as_ref(),
            )
        };
        let kernel = |text: &str| match read(text) {
            Ok(kernel) => kernel,
            Err(fault) => panic!("{text:?} is read: {fault}"),
        };
        let mut key = "00".repeat(31);
        key.push_str("aF");
        let mut spelled = [0_u8; 32];
        spelled[31] = 0xaf;
        assert_eq!(kernel(""), Kernel::Trusting(BTreeSet::new()));
        assert_eq!(
            kernel("[presentation]\nspelling = \"ascii\"\n"),
            Kernel::Trusting(BTreeSet::new()),
            "a file setting only its spelling trusts this installation alone"
        );
        assert_eq!(
            kernel(&format!("[kernel]\ntrusted = [\"{key}\"]\n")),
            Kernel::Trusting(BTreeSet::from([KernelIdentity::from(spelled)]))
        );
        assert_eq!(
            kernel(&format!(
                "[kernel]\npolicy = \"recheck\"\ntrusted = [\"{key}\"]\n"
            )),
            Kernel::Rechecking
        );
        let refused = |text: &str| match read(text) {
            Err(fault) => fault.to_string(),
            Ok(kernel) => panic!("{text:?} is refused: {kernel:?}"),
        };
        assert_eq!(
            refused("[kernel]\npolicy = \"lenient\"\n"),
            "/c/gandr/config.toml: `kernel.policy` is `lenient`; it names `trusted` or `recheck`"
        );
        let short = key.get(2 ..).expect("a key");
        assert_eq!(
            refused(&format!("[kernel]\ntrusted = [\"{short}\"]\n")),
            format!(
                "/c/gandr/config.toml: `kernel.trusted` holds `{short}`; it lists keys of 64 \
                 hexadecimal digits"
            )
        );
        let unhex = format!("{}g", key.get(1 ..).expect("a key"));
        assert_eq!(
            refused(&format!("[kernel]\ntrusted = [\"{unhex}\"]\n")),
            format!(
                "/c/gandr/config.toml: `kernel.trusted` holds `{unhex}`; it lists keys of 64 \
                 hexadecimal digits"
            )
        );
        assert_eq!(
            refused("kernel = 1\n"),
            "/c/gandr/config.toml: `kernel` is of type integer, not a table"
        );
    }

    /// #5704: the quotas of the exact reals are a profile that the file names,
    /// and a profile that names nothing is refused with the names there are.
    #[test]
    fn a_reals_profile_is_read_and_an_unknown_one_refused_5704()
    {
        let read = |text: &str| {
            reals_parsed(
                Path::new("/c/gandr/config.toml"),
                toml::from_str(text).as_ref(),
            )
        };
        let profile = |text: &str| match read(text) {
            Ok(profile) => profile,
            Err(fault) => panic!("{text:?} is read: {fault}"),
        };
        assert_eq!(profile(""), RealsProfile::Default);
        assert_eq!(
            profile("[kernel]\npolicy = \"recheck\"\n"),
            RealsProfile::Default,
            "a file without a `[reals]` table takes the default profile"
        );
        assert_eq!(profile("[reals]\n"), RealsProfile::Default);
        assert_eq!(
            profile("[reals]\nprofile = \"default\"\n"),
            RealsProfile::Default
        );
        assert_eq!(
            profile("[reals]\nprofile = \"bounded\"\n"),
            RealsProfile::Bounded
        );
        let refused = |text: &str| match read(text) {
            Err(fault) => fault.to_string(),
            Ok(profile) => panic!("{text:?} is refused: {profile:?}"),
        };
        assert_eq!(
            refused("[reals]\nprofile = \"fast\"\n"),
            "/c/gandr/config.toml: `reals.profile` is `fast`; it names `default` or `bounded`"
        );
        assert_eq!(
            refused("[reals]\nprofile = 1\n"),
            "/c/gandr/config.toml: `reals.profile` is of type integer; it names `default` or \
             `bounded`"
        );
        assert_eq!(
            refused("reals = 1\n"),
            "/c/gandr/config.toml: `reals` is of type integer, not a table"
        );
    }

    /// #6340: the retries of the toolset are a policy that the file names,
    /// and a value out of its range is refused with the range.
    #[cfg(unix)]
    #[test]
    fn a_delivery_policy_is_read_and_a_bad_one_refused_6340()
    {
        use core::time::Duration;

        use gandr_surface_mcp::Policy;
        use gandr_surface_mcp::Retries;

        let read = |text: &str| {
            deliveries_parsed(
                Path::new("/c/gandr/config.toml"),
                toml::from_str(text).as_ref(),
            )
        };
        let policy = |text: &str| match read(text) {
            Ok(policy) => policy,
            Err(fault) => panic!("{text:?} is read: {fault}"),
        };
        assert_eq!(policy(""), Policy::default());
        assert_eq!(policy("[deliveries]\n"), Policy::default());
        assert_eq!(
            policy("[deliveries]\nfirst_ms = 100\nlongest_ms = 400\nretries = 2\n"),
            Policy {
                first: Duration::from_millis(100),
                longest: Duration::from_millis(400),
                retries: Retries(2),
            }
        );
        assert_eq!(
            policy("[deliveries]\nretries = 0\n"),
            Policy {
                retries: Retries(0),
                ..Policy::default()
            },
            "a key that is absent takes its default"
        );
        let refused = |text: &str| match read(text) {
            Err(fault) => fault.to_string(),
            Ok(policy) => panic!("{text:?} is refused: {policy:?}"),
        };
        assert_eq!(
            refused("[deliveries]\nfirst_ms = 0\n"),
            "/c/gandr/config.toml: `deliveries.first_ms` is 0; it is a whole number of 1 at least"
        );
        assert_eq!(
            refused("[deliveries]\nretries = \"many\"\n"),
            "/c/gandr/config.toml: `deliveries.retries` is `many`; it is a whole number"
        );
        assert_eq!(
            refused("[deliveries]\nfirst_ms = 500\nlongest_ms = 100\n"),
            "/c/gandr/config.toml: `deliveries.longest_ms` is shorter than `deliveries.first_ms`"
        );
        assert_eq!(
            refused("deliveries = 1\n"),
            "/c/gandr/config.toml: `deliveries` is of type integer, not a table"
        );
    }

    /// #3157: the store is rooted under the XDG data home by the
    /// configuration's own rule.
    #[test]
    fn the_store_sits_under_the_xdg_data_home_3157()
    {
        let directory = |home: Option<&str>, fallback: Option<&str>| {
            stored(home.map(PathBuf::from), fallback.map(PathBuf::from))
        };
        assert_eq!(
            directory(Some("/xdg"), Some("/home/user")),
            Some(PathBuf::from("/xdg/gandr/store"))
        );
        assert_eq!(
            directory(Some("relative"), Some("/home/user")),
            Some(PathBuf::from("/home/user/.local/share/gandr/store")),
            "a relative XDG_DATA_HOME is ignored, as the specification asks"
        );
        assert_eq!(
            directory(None, Some("/home/user")),
            Some(PathBuf::from("/home/user/.local/share/gandr/store"))
        );
        assert_eq!(directory(None, None), None);
    }
}
