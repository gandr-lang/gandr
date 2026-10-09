//! The one failure of a presentation: the layout engine refused.

use core::fmt;

use gandr_surface_layout::RenderError;
use gandr_surface_layout::error::BuildError;

/// Why a node could not be laid out.
///
/// A malformed source is not a failure: the printer writes `?` for what it
/// cannot read. What fails is the layout engine, at a ceiling it meters, and
/// a defect in the walk's own bookkeeping.
#[derive(Debug, Eq, PartialEq)]
pub enum PresentationError
{
    /// Building the document reached a build ceiling.
    Build(BuildError),
    /// Resolving or rendering the document reached a render ceiling.
    Render(RenderError),
    /// The walk ended holding other than one finished document, which its
    /// own scheduling excludes.
    Unbalanced,
}

impl From<BuildError> for PresentationError
{
    /// Wraps a build refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(error: BuildError) -> Self
    {
        Self::Build(error)
    }
}

impl From<RenderError> for PresentationError
{
    /// Wraps a render refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(error: RenderError) -> Self
    {
        Self::Render(error)
    }
}

impl fmt::Display for PresentationError
{
    /// Writes the failure as one sentence naming what refused.
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
            | Self::Build(ref error) => write!(f, "the presentation did not build: {error}"),
            | Self::Render(ref error) => write!(f, "the presentation did not render: {error}"),
            | Self::Unbalanced => {
                f.write_str("the presentation walk ended without exactly one document")
            },
        }
    }
}

impl core::error::Error for PresentationError
{
    /// The layout engine's refusal beneath this one.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the wrapped build or render error; nothing for an unbalanced
    ///   walk.
    /// - provides: the error chain a caller reports.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    fn source(&self) -> Option<&(dyn core::error::Error + 'static)>
    {
        match *self {
            | Self::Build(ref error) => Some(error),
            | Self::Render(ref error) => Some(error),
            | Self::Unbalanced => None,
        }
    }
}
