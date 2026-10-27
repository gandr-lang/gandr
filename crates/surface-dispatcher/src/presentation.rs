//! A `[presentation]` table, read wherever one is written.
//!
//! # One table, two files
//!
//! The user's configuration file and a package's `gandr.toml` write the same
//! table, byte for byte:
//!
//! ```toml
//! [presentation]
//! spelling = "ascii" # or "unicode"
//! ```
//!
//! [`read_presentation`] reads it from either, and its key path is the
//! editor's `gandr.presentation.spelling` setting. Where several name a
//! spelling, the editor's own setting outranks the project's manifest, and the
//! manifest outranks the user's file; the driver's `--spelling` flag outranks
//! the file for one invocation.
//!
//! **The reader is one.** The alternative was the driver's configuration
//! module and the language server each reading their own file, which would
//! leave two spellings of the same table to drift apart. The choice reverses
//! if a project's table grows a key the user's file has no meaning for.

use core::fmt;
use std::io;
use std::path::PathBuf;

use anodized::spec;
use gandr_surface_grammar::Spelling;

/// What a `[presentation]` table sets; a setting it does not name is absent.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
#[repr(transparent)]
pub struct Presentation
{
    /// `presentation.spelling`.
    pub spelling: Option<Spelling>,
}

/// Why a file's `[presentation]` table could not be read.
#[derive(Debug)]
pub enum PresentationFault
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

impl fmt::Display for PresentationFault
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

/// The presentation `read`, the contents of `path` parsed as TOML, sets.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `presentation.spelling` reads as [`Spelling`] reads its name; a
///   document without it sets no spelling. Text that is not TOML is
///   [`PresentationFault::Malformed`], and a `presentation` that is not a table
///   or a spelling that is not one of the two names is
///   [`PresentationFault::Unset`].
/// - provides: the reading of a file's table, apart from reading the file.
/// - fails: the faults the ensures clause names.
/// - panics: none.
///
/// # Errors
/// [`PresentationFault::Malformed`] and [`PresentationFault::Unset`], as
/// above.
///
/// # Adequacy
/// - hypothesis: L3 — each spelling, an empty document, a document that is not
///   TOML, an unknown spelling and a misshapen table are each read.
/// - witness: `presentation::tests::a_spelling_is_read_and_a_bad_one_refused`
#[spec(ensures: |ref ret| !matches!(*ret, Err(PresentationFault::Unreadable { .. })))]
fn presented(
    path: PathBuf,
    read: Result<toml::Table, toml::de::Error>,
) -> Result<Presentation, PresentationFault>
{
    let table = match read {
        Ok(table) => table,
        Err(error) => return Err(PresentationFault::Malformed { path, error }),
    };
    let unset = |path: PathBuf, found: String| PresentationFault::Unset { path, found };
    let presentation = match table.get("presentation") {
        None => return Ok(Presentation::default()),
        Some(&toml::Value::Table(ref presentation)) => presentation,
        Some(other) => {
            let kind = other.type_str();
            return Err(unset(
                path,
                format!("`presentation` is of type {kind}, not a table"),
            ));
        },
    };
    let Some(stated) = presentation.get("spelling")
    else {
        return Ok(Presentation::default());
    };
    if let Some(Ok(spelling)) = stated.as_str().map(str::parse::<Spelling>) {
        return Ok(Presentation {
            spelling: Some(spelling),
        });
    }
    let held = match *stated {
        toml::Value::String(ref name) => format!("`{name}`"),
        toml::Value::Integer(_)
        | toml::Value::Float(_)
        | toml::Value::Boolean(_)
        | toml::Value::Datetime(_)
        | toml::Value::Array(_)
        | toml::Value::Table(_) => format!("of type {}", stated.type_str()),
    };
    Err(unset(
        path,
        format!("`presentation.spelling` is {held}; it names `unicode` or `ascii`"),
    ))
}

/// The presentation the file at `path` sets.
///
/// # Specification
/// - requires: nothing.
/// - ensures: as [`presented`] reads the file's text; no presentation when no
///   file is there.
/// - provides: the user's configuration and a project's manifest, read alike.
/// - fails: a file that exists and cannot be read, and the faults of
///   [`presented`].
/// - panics: none.
/// - executable: none — the result depends on the file system, which the
///   clauses cannot observe.
///
/// # Errors
/// [`PresentationFault::Unreadable`], [`PresentationFault::Malformed`] and
/// [`PresentationFault::Unset`].
///
/// # Adequacy
/// - hypothesis: L3 — an absent file sets nothing, a written one its spelling.
/// - witness: `presentation::tests::a_file_sets_its_spelling_and_an_absent_one_none`
#[inline]
pub fn read_presentation(path: PathBuf) -> Result<Presentation, PresentationFault>
{
    match std::fs::read_to_string(&path) {
        Ok(text) => presented(path, toml::from_str(&text)),
        Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(Presentation::default()),
        Err(error) => Err(PresentationFault::Unreadable { path, error }),
    }
}

#[cfg(test)]
mod tests
{
    use std::path::PathBuf;

    use gandr_surface_grammar::Spelling;

    use super::Presentation;
    use super::PresentationFault;
    use super::presented;
    use super::read_presentation;

    #[test]
    fn a_spelling_is_read_and_a_bad_one_refused()
    {
        let read =
            |text: &str| presented(PathBuf::from("/c/gandr/config.toml"), toml::from_str(text));
        let spelling = |text: &str| match read(text) {
            Ok(Presentation { spelling }) => spelling,
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
            Err(PresentationFault::Malformed { .. })
        ));
        let refused = |text: &str| match read(text) {
            Err(fault @ PresentationFault::Unset { .. }) => fault.to_string(),
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

    #[test]
    fn a_file_sets_its_spelling_and_an_absent_one_none()
    {
        let directory =
            std::env::temp_dir().join(format!("gandr-presentation-{}", std::process::id()));
        std::fs::create_dir_all(&directory).expect("the scratch directory is created");
        let file = directory.join("gandr.toml");
        assert_eq!(
            read_presentation(file.clone()).expect("an absent file reads"),
            Presentation::default(),
            "an absent file sets nothing"
        );
        std::fs::write(&file, "[presentation]\nspelling = \"ascii\"\n")
            .expect("the file is written");
        assert_eq!(
            read_presentation(file).expect("the file reads"),
            Presentation {
                spelling: Some(Spelling::Ascii)
            }
        );
        std::fs::remove_dir_all(&directory).expect("the scratch directory is removed");
    }
}
