//! The failure of a unit test: each error that the unit tests propagate, as a
//! variant of its own type, so no test boxes a trait object (#7385).

use alloc::string::String;
use core::error::Error;
use core::fmt;
use core::num::TryFromIntError;
use std::path::PathBuf;

use gandr_surface_grammar::PbgError;
use gandr_surface_syntax::SyntaxError;
use gandr_theory_graphs::PrecDagError;
use gandr_theory_graphs::PrecSpecError;

use crate::CheckpointError;
use crate::MeldError;

/// File-read failure with the example path preserved.
#[derive(Debug)]
pub struct ReadSourceError
{
    /// The file that failed to read.
    pub path: PathBuf,
    /// The underlying failure.
    pub source: std::io::Error,
}

impl fmt::Display for ReadSourceError
{
    /// # Specification
    /// - ensures: the message names the requested path and original cause.
    /// - fails: propagates the formatter's write failure.
    /// - panics: none.
    /// - executable: none — the formatter's sink is write-only; observing the
    ///   emitted bytes would require replaying its side effects.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a directory read failure retains its path and cause
    ///   in the message; a rejecting sink detects swallowed errors.
    /// - witness: `parse::tests::source_reads_preserve_text_and_failure_context`
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "failed to read {}: {}", self.path.display(), self.source)
    }
}

impl Error for ReadSourceError
{
    /// # Specification
    /// trivial.
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            trait_object,
            reason = "signature: `Error::source` returns the trait object that `core`'s own signature fixes"
        )
    )]
    fn source(&self) -> Option<&(dyn Error + 'static)>
    {
        Some(&self.source)
    }
}

/// Declares the failure of a unit test from one list: a variant for each
/// error that the unit tests propagate, and the `From` that `?` uses for it.
macro_rules! failure {
    ($($(#[doc = $doc:literal])+ $variant:ident($error:ty),)+) => {
        /// The failure of a unit test.
        #[derive(Debug)]
        #[expect(
            dead_code,
            reason = "a failing test prints its failure through the derived Debug, which the dead-code analysis does not count as a read"
        )]
        pub enum Failure
        {
            $($(#[doc = $doc])+ $variant($error),)+
        }

        $(
            impl From<$error> for Failure
            {
                /// # Specification
                /// trivial.
                fn from(error: $error) -> Self
                {
                    Self::$variant(error)
                }
            }
        )+
    };
}

failure! {
    /// The test finds no value where it expects one, and the text names it.
    Absent(&'static str),
    /// The test states its failure in words.
    Stated(String),
    /// The grammar refuses its rules or a query.
    Grammar(PbgError),
    /// The melder refuses its input.
    Meld(MeldError),
    /// A checkpoint's bytes do not decode.
    Checkpoint(CheckpointError),
    /// The syntax layer refuses a value.
    Syntax(SyntaxError),
    /// The precedence graph refuses its specification.
    PrecDag(PrecDagError),
    /// The precedence specification refuses a group or an edge.
    PrecSpec(PrecSpecError),
    /// An integer does not fit its target type.
    Integer(TryFromIntError),
    /// A source file does not read.
    Read(ReadSourceError),
}
