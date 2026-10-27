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
//! The key path is the editor's `gandr.presentation.spelling` setting, and a
//! package's `gandr.toml` carries the same table, which the dispatcher's
//! presentation reader reads for both. The global `--spelling` flag outranks
//! the file for one invocation, and a project's manifest and an editor's own
//! setting outrank it for that editor's connection. A file that is absent
//! configures nothing; one that cannot be read, is not TOML, or names a
//! spelling there is none of is a fault: the driver says so on standard
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

use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
use gandr_surface_dispatcher::Presentation;
use gandr_surface_dispatcher::PresentationFault;
use gandr_surface_dispatcher::read_presentation;

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

/// The user's configuration, read from the file [`located`] names under the
/// process's environment.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the presentation the file sets, as [`read_presentation`] reads
///   it; none when no directory is named or no file is there.
/// - provides: the settings `main` reads before any verb runs.
/// - fails: the faults of [`read_presentation`].
/// - panics: none.
/// - executable: none — the result depends on the environment and the file
///   system, which the clauses cannot observe.
///
/// # Errors
/// [`PresentationFault::Unreadable`], [`PresentationFault::Malformed`] and
/// [`PresentationFault::Unset`].
///
/// # Adequacy
/// - hypothesis: L3 — a configured spelling is printed, a flag outranks it, and
///   a malformed file stops the run, each through the binary.
/// - witness: `tests::cli::the_configured_spelling_prints_and_the_flag_outranks_it_782`
pub fn read() -> Result<Presentation, PresentationFault>
{
    let home = std::env::var_os("XDG_CONFIG_HOME").map(PathBuf::from);
    let fallback = std::env::var_os("HOME").map(PathBuf::from);
    located(home, fallback).map_or_else(|| Ok(Presentation::default()), read_presentation)
}

#[cfg(test)]
mod tests
{
    use std::path::PathBuf;

    use super::checkpointed;
    use super::located;

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
}
