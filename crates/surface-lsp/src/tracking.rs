//! Where a hover has nothing to show yet: the gap at a position, named, and
//! the issue whose landing closes it.
//!
//! Every tile of a read document answers a hover. Where the engine holds
//! nothing for the position, the answer is a stub: the tile as written, a
//! sentence naming what is missing, and the closing line rust-analyzer writes
//! for an unstable feature, `The tracking issue for this is: [#N]` with its
//! link. [`Gap`] lists the gaps in the order a position is tried; together
//! they cover every tile, so the corpus sweep in [`crate::hover`]'s tests
//! refuses any tile that hovers nothing.

use alloc::format;
use alloc::string::String;
use core::fmt;

/// The issue on gandr's tracker whose landing closes a gap.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct TrackingIssue(u16);

impl TrackingIssue
{
    /// A module's documentation, which no face shows.
    pub const DOCUMENTATION: Self = Self(1135);
    /// A tile inside a form the engine types nothing in: a nested module's
    /// member, a descent claim, a member's signature.
    pub const INNER: Self = Self(1204);
    /// An import whose address has a scheme, which nothing resolves.
    pub const SCHEME: Self = Self(1233);
    /// A tile a declaration writes itself, past its head.
    pub const OWN_TILE: Self = Self(1202);
    /// A tile of a root form that declares nothing, which the lowering reads
    /// as no run target yet.
    pub const RUN_TARGET: Self = Self(1105);
    /// A tile inside a refused declaration or a source never judged.
    pub const UNJUDGED: Self = Self(1201);

    /// The issue's page.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub fn url(self) -> String
    {
        format!("https://github.com/gandr-lang/gandr/issues/{}", self.0)
    }
}

impl fmt::Display for TrackingIssue
{
    /// `#` and the issue's number.
    ///
    /// # Specification
    /// trivial.
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "#{}", self.0)
    }
}

/// What a hover cannot show yet: a tile with no hover of its own, in the
/// order a position is tried, or a part of an answer still missing.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Gap
{
    /// Inside a declaration the lowering or the checker refused: the engine
    /// typed nothing in it.
    Refused,
    /// In a source the engine refused as a whole: it typed nothing in it.
    Unjudged,
    /// An import whose address has a scheme, which nothing resolves.
    Foreign,
    /// The documentation of the module a path import reads.
    Undocumented,
    /// A tile a declaration writes itself past its head, of the rule named.
    Owned(&'static str),
    /// In a root form that declares nothing: a run target or a stray.
    Undeclared,
    /// Inside a declaration, where the engine typed nothing.
    Untyped,
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
            Self::Refused | Self::Unjudged => TrackingIssue::UNJUDGED,
            Self::Foreign => TrackingIssue::SCHEME,
            Self::Undocumented => TrackingIssue::DOCUMENTATION,
            Self::Owned(_) => TrackingIssue::OWN_TILE,
            Self::Undeclared => TrackingIssue::RUN_TARGET,
            Self::Untyped => TrackingIssue::INNER,
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
            Self::Refused => String::from("A form inside a refused declaration has no hover yet."),
            Self::Unjudged => String::from("A source the engine has not judged has no hover yet."),
            Self::Foreign => String::from("An address with a scheme resolves to nothing yet."),
            Self::Undocumented => String::from("Its module documentation is not shown yet."),
            Self::Owned(rule) => format!("A tile a `{rule}` writes itself has no hover yet."),
            Self::Undeclared => String::from("A form that declares nothing has no hover yet."),
            Self::Untyped => String::from("A form the engine typed nothing at has no hover yet."),
        };
        let issue = self.issue();
        format!(
            "{what} The tracking issue for this is: [{issue}]\n\n[{issue}]: {}",
            issue.url()
        )
    }
}
