//! The one failure of a presentation: the layout engine refused.

use core::fmt;

use anodized::spec;
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
    /// - requires: nothing.
    /// - ensures: a one-line diagnostic preserving the wrapped failure's
    ///   details and distinguishing document construction from rendering.
    /// - provides: a human-readable presentation refusal.
    /// - fails: a formatting error if the destination refuses a write.
    /// - panics: none.
    /// - executable: none — the formatter exposes neither written output nor an
    ///   independent observer of the destination's write failures.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct build and render limit failures retain their
    ///   numeric bounds without line endings. Dropped, duplicated or replaced
    ///   bounds change this observer; exact wording and rejecting destinations
    ///   are outside these fixtures.
    /// - witness: `error::tests::error_details_preserve_their_limits_and_sources`
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — build and render limit failures expose their exact
    ///   typed causes, while an unbalanced walk has no cause. Erasing a cause,
    ///   changing its variant or replacing its bound changes this observer;
    ///   other layout failure payloads are outside these fixtures.
    /// - witness: `error::tests::error_details_preserve_their_limits_and_sources`
    #[spec(ensures: |ret| match *self {
        | Self::Build(ref error) => ret.and_then(|cause| cause.downcast_ref::<BuildError>()) == Some(error),
        | Self::Render(ref error) => ret.and_then(|cause| cause.downcast_ref::<RenderError>()) == Some(error),
        | Self::Unbalanced => ret.is_none(),
    })]
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

#[cfg(test)]
mod tests
{
    use alloc::string::ToString as _;
    use core::error::Error as _;

    use gandr_surface_layout::error::BuildLimitKind;
    use gandr_surface_layout::error::RenderLimitKind;

    use super::BuildError;
    use super::PresentationError;
    use super::RenderError;

    /// Diagnostic boundaries retain both concrete causes and numeric details.
    #[test]
    fn error_details_preserve_their_limits_and_sources()
    {
        let build = BuildError::LimitExceeded {
            kind: BuildLimitKind::DocNodes,
            limit: 17_u64.into(),
        };
        let render = RenderError::LimitExceeded {
            kind: RenderLimitKind::OutputBytes,
            limit: 29_u64.into(),
        };
        let build_error = PresentationError::Build(build);
        let render_error = PresentationError::Render(render);
        assert_eq!(
            build_error
                .source()
                .and_then(|cause| cause.downcast_ref::<BuildError>()),
            Some(&build),
        );
        assert!(matches!(
            render_error.source().and_then(|cause| cause.downcast_ref::<RenderError>()),
            Some(&RenderError::LimitExceeded { kind: RenderLimitKind::OutputBytes, limit })
                if limit == 29_u64.into()
        ));
        for (error, bound) in [(build_error, 17_u64), (render_error, 29_u64)] {
            let written = error.to_string();
            assert!(!written.contains(['\r', '\n']));
            assert!(
                written
                    .split_whitespace()
                    .filter_map(|part| part.parse::<u64>().ok())
                    .eq([bound])
            );
        }
        let unbalanced = PresentationError::Unbalanced;
        assert!(unbalanced.source().is_none());
        assert!(!unbalanced.to_string().contains(['\r', '\n']));
    }
}
