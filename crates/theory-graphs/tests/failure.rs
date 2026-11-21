//! The failure of a test: each error that the suites propagate, as a variant
//! of its own type, so no test boxes a trait object (#7385).

use core::num::TryFromIntError;

use gandr_theory_graphs::GraphValidationError;
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
    /// A graph's shape is out of its bounds.
    Graph(GraphValidationError),
    /// The precedence graph refuses its specification.
    PrecDag(PrecDagError),
    /// The precedence specification refuses a group or an edge.
    PrecSpec(PrecSpecError),
    /// The walk refuses its graph.
    Walk(WalkBuildError),
    /// An integer does not fit its target type.
    Integer(TryFromIntError),
}
