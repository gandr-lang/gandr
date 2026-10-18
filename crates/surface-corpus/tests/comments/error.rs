//! The refusals a corpus-comment gate can meet, each naming what it refused.

use std::path::PathBuf;

/// Why the gate could not judge the fixture, or why a source could not be read.
///
/// # Specification
/// - provides: one variant per refusal; each carries the path or the text it
///   refused, so the message points at what must change.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CommentError
{
    /// The built-in grammar did not build.
    Grammar(String),
    /// A fixture path is not valid Unicode, or its key would make a ledger
    /// line ambiguous.
    File
    {
        /// The path.
        path: PathBuf,
        /// What is wrong with it.
        detail: String,
    },
    /// A fixture source could not be read.
    Read
    {
        /// The path.
        path: PathBuf,
        /// The operating-system detail.
        detail: String,
    },
    /// The parser did not commit a tree for a source.
    Parse
    {
        /// The ledger key of the source.
        file: String,
        /// The parser's refusal.
        detail: String,
    },
    /// A mold in a committed tree does not resolve under the grammar.
    Mold
    {
        /// The ledger key of the source.
        file: String,
        /// The grammar's refusal.
        detail: String,
    },
    /// The ledger could not be read or written.
    Ledger
    {
        /// The path.
        path: PathBuf,
        /// The operating-system detail.
        detail: String,
    },
    /// Standard error or standard output could not be written.
    Output(String),
}

impl core::fmt::Display for CommentError
{
    /// Describes the refusal and names its input.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes one line naming the variant's input and its detail.
    /// - provides: the message the binary prints before exiting with status 2.
    /// - fails: propagates the formatter's own write failure.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every variant's rendering names its input; a dropped
    ///   field or a swapped variant changes the asserted line.
    /// - witness: `tests::comments::error::tests::every_refusal_names_its_input`
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        match *self {
            Self::Grammar(ref detail) => {
                write!(f, "the built-in grammar did not build: {detail}")
            },
            Self::File {
                ref path,
                ref detail,
            } => write!(f, "{}: {detail}", path.display()),
            Self::Read {
                ref path,
                ref detail,
            } => write!(f, "{}: the source did not read: {detail}", path.display()),
            Self::Parse {
                ref file,
                ref detail,
            } => write!(f, "{file}: the parser did not commit a tree: {detail}"),
            Self::Mold {
                ref file,
                ref detail,
            } => write!(f, "{file}: a mold did not resolve: {detail}"),
            Self::Ledger {
                ref path,
                ref detail,
            } => write!(
                f,
                "{}: the ledger did not read or write: {detail}",
                path.display()
            ),
            Self::Output(ref detail) => write!(f, "the report did not write: {detail}"),
        }
    }
}

impl core::error::Error for CommentError
{
}

#[cfg(test)]
mod tests
{
    use std::path::Path;

    use super::CommentError;

    #[test]
    fn every_refusal_names_its_input()
    {
        let path = Path::new("crates/surface-corpus/fixture/uncommented.ledger");
        let rendered = [
            CommentError::Grammar("missing".to_owned()).to_string(),
            CommentError::File {
                path: path.to_owned(),
                detail: "a colon".to_owned(),
            }
            .to_string(),
            CommentError::Read {
                path: path.to_owned(),
                detail: "denied".to_owned(),
            }
            .to_string(),
            CommentError::Parse {
                file: "model/x.gandr".to_owned(),
                detail: "corrupt".to_owned(),
            }
            .to_string(),
            CommentError::Mold {
                file: "model/x.gandr".to_owned(),
                detail: "unknown".to_owned(),
            }
            .to_string(),
            CommentError::Ledger {
                path: path.to_owned(),
                detail: "denied".to_owned(),
            }
            .to_string(),
            CommentError::Output("closed".to_owned()).to_string(),
        ];
        assert!(
            rendered[0].contains("missing"),
            "a grammar refusal names its detail"
        );
        assert!(
            rendered[1].contains("uncommented.ledger") && rendered[1].contains("a colon"),
            "a file refusal names its path"
        );
        assert!(
            rendered[2].contains("denied"),
            "a read refusal names the operating-system detail"
        );
        assert!(
            rendered[3].contains("model/x.gandr") && rendered[3].contains("corrupt"),
            "a parse refusal names the file"
        );
        assert!(
            rendered[4].contains("unknown"),
            "a mold refusal names the grammar detail"
        );
        assert!(
            rendered[5].contains("uncommented.ledger"),
            "a ledger refusal names its path"
        );
        assert!(
            rendered[6].contains("closed"),
            "an output refusal names its detail"
        );
    }
}
