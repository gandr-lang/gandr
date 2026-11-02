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
//! arguments. The new image selects again, finds itself and runs. It sets no
//! variable of its own, so a running face selects as the user did and
//! follows a later switch. The driver runs itself when nothing
//! names a toolchain, when the selection names the running executable, and
//! for `gandr toolchain`, which manages the toolchains whatever is selected.
//! A name that names no installed toolchain is refused before any verb runs.
//!
//! The nearest package manifest's `[toolchain]` constraint then holds the
//! selection: [`constraint`] refuses a toolchain named outright that leaves
//! it unmet, and otherwise picks the default or the highest version meeting it.
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

mod constraint;

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
    /// The constraint of the package manifest at this path, which no
    /// selection the default makes meets.
    Manifest(PathBuf),
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
            Self::Manifest(ref path) => write!(f, "the constraint of {}", path.display()),
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
    /// The toolchain's `gandr` prints no description of itself.
    Undescribed
    {
        /// The toolchain's name.
        name: Name,
        /// Its `gandr`.
        path: PathBuf,
    },
    /// The toolchain named outright leaves a package's constraint unmet.
    Unmet
    {
        /// The toolchain's name.
        name: Name,
        /// Where the name came from.
        source: Source,
        /// The manifest stating the constraint.
        manifest: PathBuf,
        /// Each clause it leaves unmet.
        unmet: Vec<gandr_surface_dispatcher::Unmet>,
    },
    /// No installed toolchain meets a package's constraint.
    Unmeetable
    {
        /// The manifest stating the constraint.
        manifest: PathBuf,
        /// The nearest candidate, the default or else the highest version,
        /// and each clause it leaves unmet.
        nearest:
            Maybe<(Name, Vec<gandr_surface_dispatcher::Unmet>), constraint::undescribed::Absent>,
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
            Self::Undescribed { ref name, ref path } => write!(
                f,
                "the toolchain `{name}` describes no version and features: {} predates `gandr toolchain describe`",
                path.display()
            ),
            Self::Unmet {
                ref name,
                ref source,
                ref manifest,
                ref unmet,
            } => {
                write!(
                    f,
                    "{source} names the toolchain `{name}`, which leaves the constraint of {} unmet",
                    manifest.display()
                )?;
                for clause in unmet {
                    write!(f, "\n  {clause}")?;
                }
                Ok(())
            },
            Self::Unmeetable {
                ref manifest,
                ref nearest,
            } => {
                write!(
                    f,
                    "no installed toolchain meets the constraint of {}",
                    manifest.display()
                )?;
                if let Maybe::Present((ref name, ref unmet)) = *nearest {
                    write!(f, "; the nearest, `{name}`, leaves it unmet")?;
                    for clause in unmet {
                        write!(f, "\n  {clause}")?;
                    }
                }
                Ok(())
            },
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
///   is the running executable. The selection is [`select`]'s, held to the
///   nearest manifest's constraint as [`constraint::constrained`] holds it.
///   Otherwise, on Unix, the process is replaced by that executable with the
///   same arguments and environment; elsewhere it runs as a child and its
///   status is returned.
/// - fails: [`ToolchainFault`] when the selection cannot be read, names no
///   installed toolchain, leaves the constraint unmet, or the exec fails.
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
    let chosen = constraint::constrained(
        &toolchains,
        &working,
        select(environment, &working, &default)?,
    )?;
    let selected = match chosen {
        Maybe::Present(selected) => selected,
        Maybe::Absent(unselected::Absent::Unnamed) => return Ok(Proxied::Itself),
    };
    let path = executable(&toolchains, selected)?;
    let running = std::env::current_exe().and_then(std::fs::canonicalize);
    let target = std::fs::canonicalize(&path);
    if let (Ok(running), Ok(target)) = (running, target)
        && running == target
    {
        return Ok(Proxied::Itself);
    }
    let mut command = std::process::Command::new(&path);
    let _prepared = command.args(arguments);
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

/// The file an executable is, by its device and inode. A rebuild writes a new
/// file, so a rebuilt toolchain is another image at the same path.
///
/// # Specification
/// - invariant: two images are equal when they are one file.
///
/// # Adequacy
/// - hypothesis: L3 — a face follows a switch to another toolchain.
/// - witness: `tests::cli::a_language_server_follows_a_toolchain_switch`
#[cfg(unix)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Image
{
    /// The device holding the file.
    device: u64,
    /// The file's inode on that device.
    inode: u64,
}

#[cfg(unix)]
impl Image
{
    /// The image of the file `metadata` describes.
    ///
    /// # Specification
    /// trivial.
    fn of(metadata: &std::fs::Metadata) -> Self
    {
        use std::os::unix::fs::MetadataExt as _;

        Self {
            device: metadata.dev(),
            inode: metadata.ino(),
        }
    }

    /// The running process's image. On Linux it is read through
    /// `/proc/self/exe`, which names the running file even once a rebuild
    /// replaced its path.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the file the process runs, or the file its path names now
    ///   where no `/proc` names the running one.
    /// - fails: when neither can be read.
    /// - panics: none.
    /// - executable: none — the answer is the file system's.
    ///
    /// # Errors
    /// The error reading the running executable.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the type's.
    /// - witness: `tests::cli::a_language_server_follows_a_toolchain_switch`
    pub fn running() -> io::Result<Self>
    {
        #[cfg(target_os = "linux")]
        let running = std::fs::metadata("/proc/self/exe");
        #[cfg(not(target_os = "linux"))]
        let running = std::env::current_exe().and_then(std::fs::metadata);
        running.map(|metadata| Self::of(&metadata))
    }
}

quenchant_shape::reason_enum! {
    /// Why the selection names no other image than the running one.
    pub mod unmoved {
        /// The reason a face keeps its image.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The selection names the running image.
            Same,
            /// Nothing names a toolchain.
            Unselected,
            /// The selection, or the image it names, cannot be read.
            Unreadable,
            /// The face follows no selection: its socket is named, or its own
            /// image cannot be read.
            Unfollowed,
        }
    }
}

/// The selected toolchain's `gandr`, when it is another image than
/// `running`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the path when the selection, made as [`proxy`] makes it, names a
///   `gandr` that is another file than `running`. A selection that cannot be
///   read keeps the running image, so a face never stops serving because a
///   toolchain broke.
/// - panics: none.
/// - executable: none — the answer is the file system's.
///
/// # Adequacy
/// - hypothesis: L3 — a face notices a switch of the default.
/// - witness: `tests::cli::a_language_server_follows_a_toolchain_switch`
#[cfg(unix)]
pub fn moved(running: Image) -> Maybe<PathBuf, unmoved::Absent>
{
    let Ok((toolchains, default)) = homes()
    else {
        return Maybe::Absent(unmoved::Absent::Unreadable);
    };
    let Ok(working) = std::env::current_dir()
    else {
        return Maybe::Absent(unmoved::Absent::Unreadable);
    };
    let environment =
        std::env::var_os(SELECTING).map_or(Maybe::Absent(named::Absent::Missing), Maybe::Present);
    let chosen = select(environment, &working, &default)
        .and_then(|selected| constraint::constrained(&toolchains, &working, selected));
    let selected = match chosen {
        Ok(Maybe::Present(selected)) => selected,
        Ok(Maybe::Absent(unselected::Absent::Unnamed)) => {
            return Maybe::Absent(unmoved::Absent::Unselected);
        },
        Err(_unreadable) => return Maybe::Absent(unmoved::Absent::Unreadable),
    };
    let Ok(path) = executable(&toolchains, selected)
    else {
        return Maybe::Absent(unmoved::Absent::Unreadable);
    };
    match std::fs::metadata(&path) {
        Ok(metadata) if Image::of(&metadata) == running => Maybe::Absent(unmoved::Absent::Same),
        Ok(_) => Maybe::Present(path),
        Err(_unreadable) => Maybe::Absent(unmoved::Absent::Unreadable),
    }
}

/// The variable naming the handover file a face's relay of another build left
/// for the image it execs, the language server's or the model server's.
#[cfg(unix)]
pub const HANDOVER: &str = "GANDR_HANDOVER";

/// Replace this process with `path`, run with this process's arguments and
/// [`HANDOVER`] naming the file `handover`.
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
/// - hypothesis: L3 — a face execs the selected toolchain with its handover.
/// - witness: `tests::cli::a_language_server_follows_a_toolchain_switch`
#[cfg(unix)]
pub fn switch(
    path: PathBuf,
    handover: &Path,
) -> ToolchainFault
{
    use std::os::unix::process::CommandExt as _;

    let mut command = std::process::Command::new(&path);
    let _prepared = command
        .args(std::env::args_os().skip(1))
        .env(HANDOVER, handover);
    let error = command.exec();
    ToolchainFault::Io { path, error }
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
///   directory, held to the nearest manifest's constraint as
///   [`constraint::constrained`] holds it.
/// - fails: as [`select`] and [`constraint::constrained`], and
///   [`ToolchainFault::Io`] when the working directory cannot be read.
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
    let (toolchains, default) = homes()?;
    let working = std::env::current_dir().map_err(|error| ToolchainFault::Io {
        path: PathBuf::from("."),
        error,
    })?;
    let environment =
        std::env::var_os(SELECTING).map_or(Maybe::Absent(named::Absent::Missing), Maybe::Present);
    constraint::constrained(
        &toolchains,
        &working,
        select(environment, &working, &default)?,
    )
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
