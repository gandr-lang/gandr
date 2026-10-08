//! The crate's single typed failure vocabulary, [`SyntaxError`].
//!
//! Every refusal names the exact position or staged node it rejected, because a
//! tree builder's caller is a parser whose own diagnostic has to point
//! somewhere. No operation in this crate panics, repairs a malformed span, or
//! admits a node it could not place.

use core::error::Error;
use core::fmt;

use crate::build::StagedId;
use crate::span::ByteOffset;
use crate::span::ByteSpan;

/// Every way this crate refuses an input.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum SyntaxError
{
    /// A span was offered whose end lies before its start.
    InvertedSpan
    {
        /// The offered start offset.
        start: ByteOffset,
        /// The offered end offset, below `start`.
        end: ByteOffset,
    },

    /// A span reached past the end of the source text it was read against.
    SpanOutsideSource
    {
        /// The offered span.
        span: ByteSpan,
        /// The end offset of the source, which the span exceeded.
        source_end: ByteOffset,
    },

    /// A span endpoint fell inside a multi-byte character.
    ///
    /// The offsets are byte offsets, so a span that lands mid-character names
    /// no text at all; reporting the offending endpoint is what lets a caller
    /// see which end of the span was mis-measured.
    SpanSplitsCharacter
    {
        /// The endpoint that is not a character boundary.
        offset: ByteOffset,
    },

    /// A staged node was named that this builder never minted.
    ///
    /// A staged identity carries the identity of the builder that minted it, so
    /// an identity from another builder is refused even when the two builders
    /// have staged the same number of nodes and the raw positions coincide.
    /// Without that stamp the foreign handle would resolve to whichever local
    /// node happened to sit at the position — a silent aliasing, not a refusal.
    UnknownStagedNode
    {
        /// The unresolvable identity.
        node: StagedId,
    },

    /// The process-wide builder-identity counter has no distinct value left.
    ///
    /// The counter refuses rather than wrapping: a reissued identity would let
    /// a handle from a retired builder resolve against a live one, which is the
    /// exact confusion the stamp exists to prevent.
    BuilderIdExhausted,

    /// A staged node was offered as a child a second time.
    ///
    /// The staged forest gives every node at most one parent, which is what
    /// makes the level-order layout finite: a node reachable twice would be
    /// copied twice, and a node reachable along two paths of different depths
    /// would have no single arena position.
    ChildAlreadyAttached
    {
        /// The identity offered twice.
        node: StagedId,
    },
}

impl fmt::Display for SyntaxError
{
    /// Write the refusal and the position it names.
    ///
    /// # Specification
    /// - requires: nothing; every variant renders.
    /// - ensures: writes one message per variant, each naming the offsets,
    ///   span, or staged identity its payload carries, so no two variants
    ///   render alike.
    /// - provides: the operator-facing sentence a caller prints for a refusal,
    ///   and the [`Error`] rendering the trait implementation below inherits.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            | Self::InvertedSpan { start, end } => {
                write!(f, "span end {end} lies before its start {start}")
            },
            | Self::SpanOutsideSource { span, source_end } => {
                write!(f, "span {span} reaches past the source end {source_end}")
            },
            | Self::SpanSplitsCharacter { offset } => {
                write!(f, "offset {offset} is not a character boundary")
            },
            | Self::UnknownStagedNode { node } => {
                write!(f, "staged node {node} was never minted by this builder")
            },
            | Self::BuilderIdExhausted => {
                f.write_str("no distinct builder identity remains to be issued")
            },
            | Self::ChildAlreadyAttached { node } => {
                write!(f, "staged node {node} already has a parent")
            },
        }
    }
}

impl Error for SyntaxError
{
}

#[cfg(test)]
mod tests
{
    use alloc::format;

    use super::SyntaxError;
    use crate::build::TreeBuilder;
    use crate::kind::NodeKind;
    use crate::span::ByteOffset;
    use crate::span::ByteSpan;
    use crate::span::SourceText;

    /// A span, for a rendering test that is not about minting spans.
    ///
    /// # Specification
    /// - requires: `start` is at or below `end`; a test about minting offers an
    ///   inverted pair to [`ByteSpan::new`] itself.
    /// - ensures: the span carrying exactly those endpoints.
    /// - provides: the span every rendering fixture below is read against.
    /// - panics: when the endpoints are inverted, so a fixture that violates
    ///   the precondition fails its own test rather than rendering a span the
    ///   crate would have refused.
    fn span(
        start: ByteOffset,
        end: ByteOffset,
    ) -> ByteSpan
    {
        ByteSpan::new(start, end).unwrap()
    }

    #[test]
    fn every_refusal_renders_its_own_position()
    {
        // One row per variant: a rendering asserted for some arms and not
        // others reads as coverage the suite does not have, and leaves the
        // unasserted arms free to render each other's text.
        let rendered = [
            (
                SyntaxError::InvertedSpan {
                    start: ByteOffset::from(7_usize),
                    end: ByteOffset::from(3_usize),
                },
                "span end 3 lies before its start 7",
            ),
            (
                SyntaxError::SpanOutsideSource {
                    span: span(ByteOffset::from(0_usize), ByteOffset::from(5_usize)),
                    source_end: ByteOffset::from(2_usize),
                },
                "span 0..5 reaches past the source end 2",
            ),
            (
                SyntaxError::SpanSplitsCharacter {
                    offset: ByteOffset::from(1_usize),
                },
                "offset 1 is not a character boundary",
            ),
            (
                SyntaxError::BuilderIdExhausted,
                "no distinct builder identity remains to be issued",
            ),
        ];

        for (error, expected) in rendered {
            assert_eq!(
                format!("{error}"),
                expected,
                "each refusal renders its own text"
            );
        }
    }

    #[test]
    fn the_staged_node_refusals_render_their_identity()
    {
        // The two staged-node variants carry a `StagedId`, which only a builder
        // can mint, so they are rendered from a real one rather than a
        // fabricated value.
        let mut builder = TreeBuilder::new(SourceText::from("ab")).unwrap();
        let node = builder
            .node(
                NodeKind::Name,
                span(ByteOffset::from(0_usize), ByteOffset::from(1_usize)),
                &[],
            )
            .unwrap();

        assert_eq!(
            format!("{}", SyntaxError::UnknownStagedNode { node }),
            format!("staged node {node} was never minted by this builder"),
            "the unknown-node rendering names the identity"
        );
        assert_eq!(
            format!("{}", SyntaxError::ChildAlreadyAttached { node }),
            format!("staged node {node} already has a parent"),
            "the already-attached rendering names the identity"
        );
    }
}
