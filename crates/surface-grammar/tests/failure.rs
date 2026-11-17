//! The failure of a test: each error that the suites propagate, as a variant
//! of its own type, so no test boxes a trait object (#7385).

use core::fmt::Error as FormatError;
use core::num::TryFromIntError;
use std::io::Error as IoError;
use std::path::StripPrefixError;

use gandr_surface_grammar::HighlightError;
use gandr_surface_grammar::PbgError;
use gandr_surface_parser::MeldError;
use gandr_surface_render_remote::InvertedRange;
use gandr_surface_syntax::SyntaxError;
use gandr_theory_graphs::PrecDagError;
use gandr_theory_graphs::PrecSpecError;
use gandr_theory_graphs::WalkBuildError;

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
    /// The role table refuses a tree.
    Highlight(HighlightError),
    /// The syntax layer refuses a value.
    Syntax(SyntaxError),
    /// The melder refuses its input.
    Meld(MeldError),
    /// A range ends before it starts.
    Range(InvertedRange),
    /// The precedence graph refuses its specification.
    PrecDag(PrecDagError),
    /// The precedence specification refuses a group or an edge.
    PrecSpec(PrecSpecError),
    /// The walk refuses its graph.
    Walk(WalkBuildError),
    /// An integer does not fit its target type.
    Integer(TryFromIntError),
    /// A path does not start with its prefix.
    Prefix(StripPrefixError),
    /// A formatter's sink refuses its text.
    Format(FormatError),
    /// A file operation fails.
    Io(IoError),
}
