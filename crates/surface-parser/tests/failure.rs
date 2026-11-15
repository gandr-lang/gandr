//! The failure of a test: each error that the suites propagate, as a variant
//! of its own type, so no test boxes a trait object (#7385).

use core::error::Error;
use core::fmt;
use core::fmt::Error as FormatError;
use core::num::ParseIntError;
use core::num::TryFromIntError;
use std::io::Error as IoError;
use std::path::PathBuf;

use gandr_surface_grammar::PbgError;
use gandr_surface_parser::MeldError;
use gandr_theory_graphs::PrecDagError;
use gandr_theory_graphs::PrecSpecError;
use gandr_workflow_sweep::SweepError;

/// File-read failure with path context retained for corpus and fixture reads.
#[derive(Debug)]
pub struct ReadSourceError
{
    /// The file that failed to read.
    pub path: PathBuf,
    /// The underlying failure.
    pub source: IoError,
}

impl fmt::Display for ReadSourceError
{
    /// # Specification
    /// - ensures: writes the failed path and underlying IO failure.
    /// - fails: propagates a formatter refusal.
    /// - executable: none — `Formatter` exposes neither its sink nor written
    ///   bytes for a postcondition; both observations require an external sink.
    ///
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a real directory-read error retains path and cause in
    ///   its display; a refusing `fmt::Write` sink must return `fmt::Error`.
    ///   Exact incidental wording is not pinned.
    /// - witness: `tests::acceptance::source_inventory_and_reads_preserve_context`
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

/// Declares the failure of a test from one list: a variant for each error
/// that the suites propagate, and the `From` that `?` uses for it.
macro_rules! failure {
    ($($(#[doc = $doc:literal])+ $variant:ident($error:ty),)+) => {
        /// The failure of a test.
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
    /// The precedence graph refuses its specification.
    PrecDag(PrecDagError),
    /// The precedence specification refuses a group or an edge.
    PrecSpec(PrecSpecError),
    /// A sweep refuses its corpus or its run.
    Sweep(SweepError),
    /// An integer does not fit its target type.
    Integer(TryFromIntError),
    /// A text does not parse as a number.
    Number(ParseIntError),
    /// A formatter's sink refuses its text.
    Format(FormatError),
    /// A file operation fails.
    Io(IoError),
    /// A source file does not read.
    Read(ReadSourceError),
}
