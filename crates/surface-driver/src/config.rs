//! The user's configuration: the settings every face reads before its flags.
//!
//! # One file under the XDG configuration directory
//!
//! `gandr` reads `gandr/config.toml` under the user's configuration
//! directory: `$XDG_CONFIG_HOME` when it names an absolute path, and
//! `$HOME/.config` otherwise. Its one setting today is the spelling every
//! face writes a construct that has a glyph in:
//!
//! ```toml
//! [presentation]
//! spelling = "ascii" # or "unicode", the default
//! ```
//!
//! The key path is the editor's `gandr.presentation.spelling` setting, so a
//! project manifest can carry the same table unchanged once it exists. The
//! global `--spelling` flag outranks the file for one invocation, and an
//! editor's own setting outranks it for that editor's connection. A file that
//! is absent configures nothing; one that cannot be read, is not TOML, or names
//! a spelling there is none of is a fault: the driver says so on standard
//! error, `gandr: <path>: <fault>`, and exits `2` before any verb runs.
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
//! # Saves under the XDG cache directory
//!
//! The language server keeps the checkpoints an editor's save persists in
//! `gandr/checkpoints` under the user's cache directory: `$XDG_CACHE_HOME`
//! when it names an absolute path, and `$HOME/.cache` otherwise, by the same
//! rule. The directory is a cache: removing it costs the next open a whole
//! judgement, and nothing else.

use core::fmt;
use std::io;
use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
use gandr_surface_grammar::Spelling;

/// What the user's configuration sets; a setting it does not name is absent.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
#[repr(transparent)]
pub struct Configuration
{
    /// `presentation.spelling`.
    pub spelling: Option<Spelling>,
}

/// Why the configuration file could not be read.
#[derive(Debug)]
pub enum Fault
{
    /// The file exists but could not be read.
    Unreadable
    {
        /// The file.
        path: PathBuf,
        /// The operating system's error.
        error: io::Error,
    },
    /// The file is not TOML.
    Malformed
    {
        /// The file.
        path: PathBuf,
        /// The parser's error.
        error: toml::de::Error,
    },
    /// A setting holds a value it has no meaning for.
    Unset
    {
        /// The file.
        path: PathBuf,
        /// What the setting held and what it takes, in words.
        found: String,
    },
}

impl fmt::Display for Fault
{
    /// Writes `<path>: <fault>`.
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
            Self::Unreadable {
                ref path,
                ref error,
            } => write!(f, "{}: cannot be read: {error}", path.display()),
            Self::Malformed {
                ref path,
                ref error,
            } => write!(f, "{}: not TOML: {}", path.display(), error.message()),
            Self::Unset {
                ref path,
                ref found,
            } => write!(f, "{}: {found}", path.display()),
        }
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

/// The configuration `read`, the contents of `path` parsed as TOML, sets.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `presentation.spelling` reads `unicode` as [`Spelling::Unicode`]
///   and `ascii` as [`Spelling::Ascii`]; a document without it sets no
///   spelling. Text that is not TOML is [`Fault::Malformed`], and a
///   `presentation` that is not a table or a spelling that is not one of the
///   two names is [`Fault::Unset`].
/// - provides: the reading of the file, apart from finding it.
/// - fails: the faults the ensures clause names.
/// - panics: none.
///
/// # Errors
/// [`Fault::Malformed`] and [`Fault::Unset`], as above.
///
/// # Adequacy
/// - hypothesis: L3 — each spelling, an empty document, a document that is not
///   TOML, an unknown spelling and a misshapen table are each read.
/// - witness: `config::tests::a_spelling_is_read_and_a_bad_one_refused`
#[spec(ensures: |ref ret| !matches!(*ret, Err(Fault::Unreadable { .. })))]
fn parsed(
    path: PathBuf,
    read: Result<toml::Table, toml::de::Error>,
) -> Result<Configuration, Fault>
{
    let table = match read {
        Ok(table) => table,
        Err(error) => return Err(Fault::Malformed { path, error }),
    };
    let unset = |path: PathBuf, found: String| Fault::Unset { path, found };
    let presentation = match table.get("presentation") {
        None => return Ok(Configuration::default()),
        Some(&toml::Value::Table(ref presentation)) => presentation,
        Some(other) => {
            let kind = other.type_str();
            return Err(unset(
                path,
                format!("`presentation` is of type {kind}, not a table"),
            ));
        },
    };
    let spelling = match presentation.get("spelling") {
        None => None,
        Some(&toml::Value::String(ref name)) if name == "unicode" => Some(Spelling::Unicode),
        Some(&toml::Value::String(ref name)) if name == "ascii" => Some(Spelling::Ascii),
        Some(other) => {
            let held = match *other {
                toml::Value::String(ref name) => format!("`{name}`"),
                toml::Value::Integer(_)
                | toml::Value::Float(_)
                | toml::Value::Boolean(_)
                | toml::Value::Datetime(_)
                | toml::Value::Array(_)
                | toml::Value::Table(_) => format!("of type {}", other.type_str()),
            };
            return Err(unset(
                path,
                format!("`presentation.spelling` is {held}; it names `unicode` or `ascii`"),
            ));
        },
    };
    Ok(Configuration { spelling })
}

/// The user's configuration, read from the file [`located`] names under the
/// process's environment.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the configuration the file sets, as [`parsed`] reads it; no
///   configuration when no directory is named or no file is there.
/// - provides: the settings `main` reads before any verb runs.
/// - fails: a file that exists and cannot be read, and the faults of
///   [`parsed`].
/// - panics: none.
/// - executable: none — the result depends on the environment and the file
///   system, which the clauses cannot observe.
///
/// # Errors
/// [`Fault::Unreadable`], [`Fault::Malformed`] and [`Fault::Unset`].
///
/// # Adequacy
/// - hypothesis: L3 — a configured spelling is printed, a flag outranks it, and
///   a malformed file stops the run, each through the binary.
/// - witness: `tests::cli::the_configured_spelling_prints_and_the_flag_outranks_it_782`
pub fn read() -> Result<Configuration, Fault>
{
    let home = std::env::var_os("XDG_CONFIG_HOME").map(PathBuf::from);
    let fallback = std::env::var_os("HOME").map(PathBuf::from);
    let Some(path) = located(home, fallback)
    else {
        return Ok(Configuration::default());
    };
    match std::fs::read_to_string(&path) {
        Ok(text) => parsed(path, toml::from_str(&text)),
        Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(Configuration::default()),
        Err(error) => Err(Fault::Unreadable { path, error }),
    }
}

#[cfg(test)]
mod tests
{
    use std::path::PathBuf;

    use gandr_surface_grammar::Spelling;

    use super::Configuration;
    use super::Fault;
    use super::checkpointed;
    use super::located;
    use super::parsed;

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

    #[test]
    fn a_spelling_is_read_and_a_bad_one_refused()
    {
        let read = |text: &str| parsed(PathBuf::from("/c/gandr/config.toml"), toml::from_str(text));
        let spelling = |text: &str| match read(text) {
            Ok(Configuration { spelling }) => spelling,
            Err(fault) => panic!("{text:?} is read: {fault}"),
        };
        assert_eq!(
            spelling("[presentation]\nspelling = \"ascii\"\n"),
            Some(Spelling::Ascii)
        );
        assert_eq!(
            spelling("[presentation]\nspelling = \"unicode\"\n"),
            Some(Spelling::Unicode)
        );
        assert_eq!(spelling(""), None);
        assert_eq!(spelling("[presentation]\n"), None);
        assert!(matches!(
            read("[presentation\n"),
            Err(Fault::Malformed { .. })
        ));
        let refused = |text: &str| match read(text) {
            Err(fault @ Fault::Unset { .. }) => fault.to_string(),
            other => panic!("{text:?} is refused as unset: {other:?}"),
        };
        assert_eq!(
            refused("[presentation]\nspelling = \"latin\"\n"),
            "/c/gandr/config.toml: `presentation.spelling` is `latin`; it names `unicode` or \
             `ascii`"
        );
        assert_eq!(
            refused("[presentation]\nspelling = 1\n"),
            "/c/gandr/config.toml: `presentation.spelling` is of type integer; it names \
             `unicode` or `ascii`"
        );
        assert_eq!(
            refused("presentation = 1\n"),
            "/c/gandr/config.toml: `presentation` is of type integer, not a table"
        );
    }
}
