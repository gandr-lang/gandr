//! Where a hover has nothing to show yet: the gap at a position, named, and
//! the issue whose landing closes it.
//!
//! Every tile of a read document answers a hover. Where the engine holds
//! nothing for the position and has not refused it, the answer is a stub:
//! the tile as written, a sentence naming what is missing, and the closing
//! line rust-analyzer writes for an unstable feature, `The tracking issue for
//! this is: [#N]` with its link. [`Gap`] lists the gaps in the order a
//! position is tried; with the refusals [`crate::hover`] answers before them,
//! they cover every tile, so the corpus sweep in its tests refuses any tile
//! that hovers nothing.

use alloc::format;
use alloc::string::String;

use gandr_surface_lowering::TrackingIssue;

/// What a hover cannot show yet: a tile with no hover of its own, in the
/// order a position is tried, or a part of an answer still missing.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Gap
{
    /// An import whose address has a scheme, which nothing resolves.
    Foreign,
    /// The documentation of the module a path import reads.
    Undocumented,
    /// In a root form that declares nothing: a run target or a stray.
    Undeclared,
}

impl Gap
{
    /// The issue whose landing closes the gap.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub fn issue(self) -> TrackingIssue
    {
        match self {
            Self::Foreign => TrackingIssue::SCHEME,
            Self::Undocumented => TrackingIssue::DOCUMENTATION,
            Self::Undeclared => TrackingIssue::RUN_TARGET,
        }
    }

    /// The stub's closing paragraphs: the gap named, the tracking issue's
    /// line and its link's definition.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub fn closing(self) -> String
    {
        let what = match self {
            Self::Foreign => String::from("An address with a scheme resolves to nothing yet."),
            Self::Undocumented => String::from("Its module documentation is not shown yet."),
            Self::Undeclared => String::from("A form that declares nothing has no hover yet."),
        };
        let issue = self.issue();
        format!(
            "{what} The tracking issue for this is: [{issue}]\n\n[{issue}]: {}",
            issue.url()
        )
    }
}
