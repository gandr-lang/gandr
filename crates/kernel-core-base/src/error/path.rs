//! The refusals of the path universe, with the round-trip direction and the
//! pattern position that each refusal names.

use core::fmt;

use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueTypeId;

use crate::error::replay::KernelVerdict;

/// A universe-path formation or reduction refusal.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PathError
{
    /// A finite session graph is malformed.
    Session(crate::error::session::SessionError),
    /// A supplied root does not resolve in the arena.
    Arena,
    /// An endpoint is not a quoted code.
    UnsupportedCode(ValueId),
    /// A code contains a former outside the closed first-order fragment.
    UnsupportedType(ValueTypeId),
    /// An equivalence annotation is not a native path classifier.
    ExpectedPath(ValueTypeId),
    /// A univalence's record synthesises no dependent pair whose first factor
    /// is the thunk of a map `U (A → F B)`.
    ExpectedEquivalence(ValueTypeId),
    /// Round-trip evidence has the wrong constructor coverage.
    Coverage(Direction),
    /// A kernel-generated round-trip claim did not replay positively.
    RoundTrip
    {
        /// The checked direction.
        direction: Direction,
        /// The constructor-pattern position.
        pattern: PatternPosition,
        /// The actual replay verdict.
        verdict: KernelVerdict,
    },
    /// A finite code or replay allowance was exhausted.
    Budget,
}

impl fmt::Display for PathError
{
    /// Render the specific path refusal.
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
            Self::Session(ref error) => error.fmt(f),
            Self::Arena => f.write_str("a universe-path root was unreadable"),
            Self::UnsupportedCode(_) => f.write_str("a universe-path endpoint was not quoted"),
            Self::UnsupportedType(_) => {
                f.write_str("a code was outside the native path vocabulary")
            },
            Self::ExpectedPath(_) => f.write_str("an equivalence annotation was not Path_U"),
            Self::ExpectedEquivalence(_) => {
                f.write_str("a univalence's record was not a bi-invertible map")
            },
            Self::Coverage(Direction::Source) => {
                f.write_str("incomplete source round-trip coverage")
            },
            Self::Coverage(Direction::Target) => {
                f.write_str("incomplete target round-trip coverage")
            },
            Self::RoundTrip {
                direction,
                pattern,
                verdict,
            } => {
                let direction = match direction {
                    Direction::Source => "source",
                    Direction::Target => "target",
                };
                let verdict = match verdict {
                    KernelVerdict::Convertible => "certified equality",
                    KernelVerdict::NotConvertible => "refuted equality",
                    KernelVerdict::Declined(_) => "replay declined",
                };
                write!(
                    f,
                    "{direction} round trip at pattern {}: {verdict}",
                    pattern.0
                )
            },
            Self::Budget => f.write_str("the universe-path allowance was exhausted"),
        }
    }
}

impl core::error::Error for PathError
{
}

/// The source or target round-trip obligation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Direction
{
    /// Backward after forward.
    Source,
    /// Forward after backward.
    Target,
}

/// A zero-based symbolic constructor-pattern position.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PatternPosition(pub usize);
