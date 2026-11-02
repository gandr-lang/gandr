//! Installed toolchains, the selection among them, and the driver as the
//! proxy that runs the selected one.
//!
//! # A toolchain is a directory holding a `gandr`
//!
//! A build of the driver is a toolchain once it is linked under a name:
//! `gandr toolchain link <name> <path>` writes the canonical `<path>` into the
//! file `<name>` of the toolchains directory, `gandr/toolchains` under the
//! user's data directory. The toolchain runs `<path>/gandr`. `gandr toolchain
//! default <name>` writes the name into `gandr/toolchain` beside that
//! directory, and `gandr toolchain list` prints each toolchain with its path.
//!
//! # The selection, and the exec
//!
//! Before it parses its arguments, the driver selects a toolchain:
//! `GANDR_TOOLCHAIN` when it is set, then the first line of the nearest
//! `gandr-toolchain` file in the working directory or an ancestor, then the
//! default. When the selected toolchain's `gandr` is another executable than
//! the running one, the driver replaces itself with it, with the same
//! arguments and `GANDR_TOOLCHAIN` naming the selection, so the new image
//! selects the same toolchain and runs. The driver runs itself when nothing
//! names a toolchain, when the selection names the running executable, and
//! for `gandr toolchain`, which manages the toolchains whatever is selected.
//! A name that names no installed toolchain is refused before any verb runs.
//!
//! **Choice.** The pin is a plain file, read in well under a millisecond
//! before any build runs. The workspace's own source is a program: reading a
//! field of it needs a build, and costs every invocation about four times the
//! driver's start. A link is a file holding a path rather than a symbolic
//! link, so the same directory serves every platform.
//!
//! **Reversal.** A pin that must sit in the workspace's source takes a reader
//! of that one field that runs no build.

use alloc::collections::BTreeMap;
use core::fmt;
use std::ffi::OsString;
use std::io;
use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
use quenchant_shape::shape::Maybe;

/// The variable that names the selected toolchain, ahead of every other
/// source.
pub const SELECTING: &str = "GANDR_TOOLCHAIN";

/// The file a directory pins its toolchain in, its first line the name.
const PIN: &str = "gandr-toolchain";

/// The executable a toolchain's directory holds.
const EXECUTABLE: &str = "gandr";

/// A toolchain's name: letters, digits, `.`, `-` and `_`, not opening with
/// `.`.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Name(String);

impl core::str::FromStr for Name
{
    type Err = ToolchainFault;

    /// Read `text` as a toolchain's name.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the name is `text`, nonempty, of letters, digits,
    ///   `.`, `-` and `_`, not opening with `.`.
    /// - fails: [`ToolchainFault::Misnamed`] otherwise.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ToolchainFault::Misnamed`], as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a name that would leave the toolchains directory is
    ///   refused.
    /// - witness: `toolchain::tests::a_name_stays_inside_the_directory`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |name| name.0 == text))]
    #[inline]
    fn from_str(text: &str) -> Result<Self, Self::Err>
    {
        let named = !text.is_empty()
            && !text.starts_with('.')
            && text
                .chars()
                .all(|glyph| glyph.is_ascii_alphanumeric() || matches!(glyph, '.' | '-' | '_'));
        if named {
            Ok(Self(text.to_owned()))
        }
        else {
            Err(ToolchainFault::Misnamed {
                name: text.to_owned(),
            })
        }
    }
}

impl fmt::Display for Name
{
    /// Writes the name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(&self.0)
    }
}

/// Where a selection's name came from.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Source
{
    /// The `GANDR_TOOLCHAIN` variable.
    Environment,
    /// A `gandr-toolchain` file, at this path.
    Pin(PathBuf),
    /// The default, named in this file.
    Default(PathBuf),
}

impl fmt::Display for Source
{
    /// Writes where the name came from.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Environment => write!(f, "`{SELECTING}`"),
            Self::Pin(ref path) => write!(f, "the pin {}", path.display()),
            Self::Default(ref path) => write!(f, "the default {}", path.display()),
        }
    }
}

/// A selected toolchain: its name and where the name came from.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Selected
{
    /// The toolchain's name.
    pub name: Name,
    /// Where the name came from.
    pub source: Source,
}

quenchant_shape::reason_enum! {
    /// Why no toolchain is selected.
    pub mod unselected {
        /// The reason the driver runs itself.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No variable, pin or default names one.
            Unnamed,
        }
    }
}

/// Why a toolchain could not be selected, linked or run.
#[derive(Debug)]
pub enum ToolchainFault
{
    /// Neither `$XDG_DATA_HOME` nor `$HOME` names a directory to keep
    /// toolchains in.
    Homeless,
    /// The name is not a toolchain's name.
    Misnamed
    {
        /// The name, as written.
        name: String,
    },
    /// The selection names no installed toolchain.
    Unknown
    {
        /// The name.
        name: Name,
        /// Where it came from.
        source: Source,
    },
    /// The toolchain's directory holds no `gandr`.
    Unexecutable
    {
        /// The toolchain's name.
        name: Name,
        /// The executable looked for.
        path: PathBuf,
    },
    /// The file system failed at `path`.
    Io
    {
        /// The path read or written.
        path: PathBuf,
        /// The failure.
        error: io::Error,
    },
}

impl fmt::Display for ToolchainFault
{
    /// Writes why, naming the toolchain and the path.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Homeless => {
                f.write_str("no directory keeps toolchains: set `XDG_DATA_HOME` or `HOME`")
            },
            Self::Misnamed { ref name } => write!(
                f,
                "`{name}` is not a toolchain's name: letters, digits, `.`, `-` and `_`, not opening with `.`"
            ),
            Self::Unknown {
                ref name,
                ref source,
            } => write!(
                f,
                "{source} names the toolchain `{name}`, which is not installed: `gandr toolchain link {name} <path>` installs it"
            ),
            Self::Unexecutable { ref name, ref path } => {
                write!(f, "the toolchain `{name}` holds no {}", path.display())
            },
            Self::Io {
                ref path,
                ref error,
            } => write!(f, "{}: {error}", path.display()),
        }
    }
}

impl core::error::Error for ToolchainFault
{
}

/// The toolchains directory and the default's file, under the user's data
/// directory.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the two paths [`crate::config::toolchains`] names.
/// - fails: [`ToolchainFault::Homeless`] when it names none.
/// - panics: none.
/// - executable: none — the result depends on the environment.
///
/// # Errors
/// [`ToolchainFault::Homeless`], as above.
///
/// # Adequacy
/// - hypothesis: L3 — as [`crate::config::toolchains`].
/// - witness: `tests::cli::a_linked_toolchain_is_the_one_the_proxy_runs`
fn homes() -> Result<(PathBuf, PathBuf), ToolchainFault>
{
    crate::config::toolchains().ok_or(ToolchainFault::Homeless)
}

/// The first line of the file at `path`, trimmed, or its absence.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the file's first line without surrounding space when the file
///   exists.
/// - provides: `named::Absent::Missing` when there is no file.
/// - fails: [`ToolchainFault::Io`] when the file exists and cannot be read.
/// - panics: none.
/// - executable: none — the answer is the file system's.
///
/// # Errors
/// [`ToolchainFault::Io`], as above.
///
/// # Adequacy
/// - hypothesis: L3 — a pin and a default are each read.
/// - witness: `tests::cli::the_environment_outranks_the_pin_and_the_pin_the_default`
fn first_line(path: &Path) -> Result<Maybe<String, named::Absent>, ToolchainFault>
{
    match std::fs::read_to_string(path) {
        Ok(text) => Ok(Maybe::Present(
            text.lines().next().unwrap_or_default().trim().to_owned(),
        )),
        Err(error) if error.kind() == io::ErrorKind::NotFound => {
            Ok(Maybe::Absent(named::Absent::Missing))
        },
        Err(error) => Err(ToolchainFault::Io {
            path: path.to_path_buf(),
            error,
        }),
    }
}

quenchant_shape::reason_enum! {
    /// Why a file names nothing.
    pub mod named {
        /// The reason.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The file does not exist.
            Missing,
        }
    }
}

/// The toolchain `environment`, a pin in `working` or an ancestor, or the
/// default in `default` selects, in that order.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the first of the three that names a toolchain, with its source.
/// - provides: `unselected::Absent::Unnamed` when none does.
/// - fails: [`ToolchainFault::Misnamed`] when the first that names one names no
///   valid name, and [`ToolchainFault::Io`] when a pin or the default cannot be
///   read.
/// - panics: none.
/// - executable: none — the answer is the file system's.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L3 — the environment outranks the pin, and the pin the
///   default, each through the binary.
/// - witness: `tests::cli::the_environment_outranks_the_pin_and_the_pin_the_default`
fn select(
    environment: Maybe<OsString, named::Absent>,
    working: &Path,
    default: &Path,
) -> Result<Maybe<Selected, unselected::Absent>, ToolchainFault>
{
    let selected = |name: String, source: Source| {
        name.parse::<Name>()
            .map(|name| Maybe::Present(Selected { name, source }))
    };
    if let Maybe::Present(name) = environment {
        return selected(name.to_string_lossy().into_owned(), Source::Environment);
    }
    for directory in working.ancestors() {
        let pin = directory.join(PIN);
        if let Maybe::Present(name) = first_line(&pin)? {
            return selected(name, Source::Pin(pin));
        }
    }
    match first_line(default)? {
        Maybe::Present(name) => selected(name, Source::Default(default.to_path_buf())),
        Maybe::Absent(named::Absent::Missing) => Ok(Maybe::Absent(unselected::Absent::Unnamed)),
    }
}

/// The executable the toolchain `selected` runs, read from its link in
/// `toolchains`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `<path>/gandr`, where `<path>` is the link's first line, and that
///   file exists.
/// - fails: [`ToolchainFault::Unknown`] when no link names it,
///   [`ToolchainFault::Unexecutable`] when its directory holds no `gandr`, and
///   [`ToolchainFault::Io`] when the link cannot be read.
/// - panics: none.
/// - executable: none — the answer is the file system's.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L3 — a linked toolchain runs, an unlinked one is refused.
/// - witness: `tests::cli::a_linked_toolchain_is_the_one_the_proxy_runs`
/// - witness: `tests::cli::a_name_no_toolchain_answers_is_refused_by_its_source`
fn executable(
    toolchains: &Path,
    selected: Selected,
) -> Result<PathBuf, ToolchainFault>
{
    let Selected { name, source } = selected;
    let Maybe::Present(directory) = first_line(&toolchains.join(&name.0))?
    else {
        return Err(ToolchainFault::Unknown { name, source });
    };
    let path = Path::new(&directory).join(EXECUTABLE);
    if path.is_file() {
        Ok(path)
    }
    else {
        Err(ToolchainFault::Unexecutable { name, path })
    }
}

/// What the proxy did when it returned.
#[derive(Debug)]
pub enum Proxied
{
    /// The running executable is the selected one, or none is selected: the
    /// driver goes on to its verb.
    Itself,
    /// The selected toolchain ran as a child and exited with this status, on
    /// a platform with no exec.
    #[cfg(not(unix))]
    Exited(std::process::ExitCode),
}

/// Run the selected toolchain in place of this process, or say that this
/// process is the one to run.
///
/// # Specification
/// - requires: called before the driver reads its arguments.
/// - ensures: [`Proxied::Itself`] when nothing names a toolchain, when the
///   arguments open with `toolchain`, or when the selected toolchain's `gandr`
///   is the running executable. Otherwise, on Unix, the process is replaced by
///   that executable with the same arguments and `GANDR_TOOLCHAIN` naming the
///   selection; elsewhere it runs as a child and its status is returned.
/// - fails: [`ToolchainFault`] when the selection cannot be read, names no
///   installed toolchain, or the exec fails.
/// - panics: none.
/// - executable: none — the outcome is another process's.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L3 — a linked toolchain runs in the driver's place, the
///   selection's sources rank in order, and an unknown name is refused.
/// - witness: `tests::cli::a_linked_toolchain_is_the_one_the_proxy_runs`
/// - witness: `tests::cli::the_environment_outranks_the_pin_and_the_pin_the_default`
/// - witness: `tests::cli::a_name_no_toolchain_answers_is_refused_by_its_source`
pub fn proxy() -> Result<Proxied, ToolchainFault>
{
    let mut arguments = std::env::args_os();
    let _program = arguments.next();
    let arguments: Vec<OsString> = arguments.collect();
    if arguments.first().is_some_and(|verb| verb == "toolchain") {
        return Ok(Proxied::Itself);
    }
    let environment =
        std::env::var_os(SELECTING).map_or(Maybe::Absent(named::Absent::Missing), Maybe::Present);
    let working = std::env::current_dir().map_err(|error| ToolchainFault::Io {
        path: PathBuf::from("."),
        error,
    })?;
    let (toolchains, default) = match crate::config::toolchains() {
        Some(homes) => homes,
        // With no data directory nothing but the variable can name a
        // toolchain, and none can be installed to answer it.
        None if matches!(environment, Maybe::Absent(_)) => return Ok(Proxied::Itself),
        None => return Err(ToolchainFault::Homeless),
    };
    let selected = match select(environment, &working, &default)? {
        Maybe::Present(selected) => selected,
        Maybe::Absent(unselected::Absent::Unnamed) => return Ok(Proxied::Itself),
    };
    let name = selected.name.clone();
    let path = executable(&toolchains, selected)?;
    let running = std::env::current_exe().and_then(std::fs::canonicalize);
    let target = std::fs::canonicalize(&path);
    if let (Ok(running), Ok(target)) = (running, target)
        && running == target
    {
        return Ok(Proxied::Itself);
    }
    let mut command = std::process::Command::new(&path);
    let _prepared = command.args(arguments).env(SELECTING, &name.0);
    exec(command, path)
}

/// Replace this process with `command`, which runs `path`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: never returns on success.
/// - fails: [`ToolchainFault::Io`] naming `path` when the exec fails.
/// - panics: none.
/// - executable: none — success replaces the process.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L3 — as [`proxy`].
/// - witness: `tests::cli::a_linked_toolchain_is_the_one_the_proxy_runs`
#[cfg(unix)]
fn exec(
    mut command: std::process::Command,
    path: PathBuf,
) -> Result<Proxied, ToolchainFault>
{
    use std::os::unix::process::CommandExt as _;

    let error = command.exec();
    Err(ToolchainFault::Io { path, error })
}

/// Run `command`, which runs `path`, as a child and return its status, on a
/// platform with no exec.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the child's exit code, its low byte, or 2 when it has none.
/// - fails: [`ToolchainFault::Io`] naming `path` when the child cannot start.
/// - panics: none.
/// - executable: none — the outcome is another process's.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L3 — as [`proxy`], on Unix alone.
/// - witness: `tests::cli::a_linked_toolchain_is_the_one_the_proxy_runs`
#[cfg(not(unix))]
fn exec(
    mut command: std::process::Command,
    path: PathBuf,
) -> Result<Proxied, ToolchainFault>
{
    let status = command
        .status()
        .map_err(|error| ToolchainFault::Io { path, error })?;
    let code = status
        .code()
        .and_then(|code| u8::try_from(code & 0xff).ok())
        .unwrap_or(2_u8);
    Ok(Proxied::Exited(std::process::ExitCode::from(code)))
}

/// Link the build in `path` as the toolchain `name`, replacing any link of
/// that name, and make it the default when none is set.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the toolchains directory holds `name`, naming `path`
///   canonicalised, and `path` holds a `gandr`. A default the file names is
///   kept; with none, `name` is the default.
/// - fails: [`ToolchainFault::Misnamed`], [`ToolchainFault::Homeless`],
///   [`ToolchainFault::Unexecutable`] when `path` holds no `gandr`, and
///   [`ToolchainFault::Io`] when a path cannot be resolved or written.
/// - panics: none.
/// - executable: none — the outcome is the file system's.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L3 — a linked build runs through the proxy and the first is
///   the default; a path with no `gandr` is refused.
/// - witness: `tests::cli::a_linked_toolchain_is_the_one_the_proxy_runs`
/// - witness: `tests::cli::the_environment_outranks_the_pin_and_the_pin_the_default`
pub fn link(
    name: &Name,
    path: &Path,
) -> Result<PathBuf, ToolchainFault>
{
    let (toolchains, default) = homes()?;
    let directory = std::fs::canonicalize(path).map_err(|error| ToolchainFault::Io {
        path: path.to_path_buf(),
        error,
    })?;
    let executable = directory.join(EXECUTABLE);
    if !executable.is_file() {
        return Err(ToolchainFault::Unexecutable {
            name: name.clone(),
            path: executable,
        });
    }
    let io = |at: &Path| {
        let at = at.to_path_buf();
        move |error| ToolchainFault::Io { path: at, error }
    };
    std::fs::create_dir_all(&toolchains).map_err(io(&toolchains))?;
    let link = toolchains.join(&name.0);
    let mut line = directory.into_os_string();
    line.push("\n");
    std::fs::write(&link, line.as_encoded_bytes()).map_err(io(&link))?;
    if first_line(&default)? == Maybe::Absent(named::Absent::Missing) {
        std::fs::write(&default, format!("{name}\n")).map_err(io(&default))?;
    }
    Ok(link)
}

/// Make the installed toolchain `name` the default.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the default's file names `name`, which is installed.
/// - fails: [`ToolchainFault::Homeless`], [`ToolchainFault::Unknown`] when
///   `name` is not installed, and [`ToolchainFault::Io`] when the file cannot
///   be written.
/// - panics: none.
/// - executable: none — the outcome is the file system's.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L3 — the default answers when no variable or pin does.
/// - witness: `tests::cli::the_environment_outranks_the_pin_and_the_pin_the_default`
pub fn make_default(name: &Name) -> Result<(), ToolchainFault>
{
    let (toolchains, default) = homes()?;
    let selected = Selected {
        name: name.clone(),
        source: Source::Default(default.clone()),
    };
    let _path = executable(&toolchains, selected)?;
    std::fs::write(&default, format!("{name}\n")).map_err(|error| ToolchainFault::Io {
        path: default,
        error,
    })
}

/// Each installed toolchain and the directory it runs from, by name.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one entry per link the toolchains directory holds; none when the
///   directory does not exist.
/// - fails: [`ToolchainFault::Homeless`], and [`ToolchainFault::Io`] when the
///   directory or a link cannot be read.
/// - panics: none.
/// - executable: none — the answer is the file system's.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L3 — a linked toolchain is listed with its path.
/// - witness: `tests::cli::a_linked_toolchain_is_the_one_the_proxy_runs`
pub fn installed() -> Result<BTreeMap<Name, PathBuf>, ToolchainFault>
{
    let (toolchains, _default) = homes()?;
    let entries = match std::fs::read_dir(&toolchains) {
        Ok(entries) => entries,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(BTreeMap::new()),
        Err(error) => {
            return Err(ToolchainFault::Io {
                path: toolchains,
                error,
            });
        },
    };
    let mut installed = BTreeMap::new();
    for entry in entries {
        let entry = entry.map_err(|error| ToolchainFault::Io {
            path: toolchains.clone(),
            error,
        })?;
        let Ok(name) = entry.file_name().to_string_lossy().parse::<Name>()
        else {
            continue;
        };
        if let Maybe::Present(directory) = first_line(&entry.path())? {
            let _listed = installed.insert(name, PathBuf::from(directory));
        }
    }
    Ok(installed)
}

/// The toolchain the working directory selects, as `proxy` would select it.
///
/// # Specification
/// - requires: nothing.
/// - ensures: as [`select`] under the process's environment and working
///   directory.
/// - fails: as [`select`], and [`ToolchainFault::Io`] when the working
///   directory cannot be read.
/// - panics: none.
/// - executable: none — the answer is the environment's.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L3 — `toolchain list` marks the toolchain the proxy runs.
/// - witness: `tests::cli::the_environment_outranks_the_pin_and_the_pin_the_default`
pub fn selected() -> Result<Maybe<Selected, unselected::Absent>, ToolchainFault>
{
    let (_toolchains, default) = homes()?;
    let working = std::env::current_dir().map_err(|error| ToolchainFault::Io {
        path: PathBuf::from("."),
        error,
    })?;
    let environment =
        std::env::var_os(SELECTING).map_or(Maybe::Absent(named::Absent::Missing), Maybe::Present);
    select(environment, &working, &default)
}

/// The toolchain the default's file names, or its absence.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the default's name when its file exists.
/// - provides: `named::Absent::Missing` when no default is set.
/// - fails: [`ToolchainFault::Homeless`], [`ToolchainFault::Misnamed`] when the
///   file names no valid name, and [`ToolchainFault::Io`] when it cannot be
///   read.
/// - panics: none.
/// - executable: none — the answer is the file system's.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L3 — `toolchain list` marks the default.
/// - witness: `tests::cli::the_environment_outranks_the_pin_and_the_pin_the_default`
pub fn selected_default() -> Result<Maybe<Name, named::Absent>, ToolchainFault>
{
    let (_toolchains, default) = homes()?;
    match first_line(&default)? {
        Maybe::Present(name) => name.parse().map(Maybe::Present),
        Maybe::Absent(reason) => Ok(Maybe::Absent(reason)),
    }
}

#[cfg(test)]
mod tests
{
    use super::Name;
    use super::ToolchainFault;

    #[test]
    fn a_name_stays_inside_the_directory()
    {
        for name in ["dev", "nightly-2026-11-02", "v0.3.1", "a_b"] {
            assert!(name.parse::<Name>().is_ok(), "`{name}` is a name");
        }
        for name in ["", ".", "..", ".hidden", "a/b", "../escape", "a b"] {
            assert!(
                matches!(name.parse::<Name>(), Err(ToolchainFault::Misnamed { .. })),
                "`{name}` is refused"
            );
        }
    }
}
