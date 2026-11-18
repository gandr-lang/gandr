//! The cut's orientation.
//!
//! [`Polarity`] is the evaluation-strategy orientation a cut `⟨p |ε c⟩`
//! carries: the axis on which a positive cut runs its producer first
//! (call-by-value) and a negative cut its consumer first (call-by-name). It is
//! not the value/computation sort of call-by-push-value, and not the variance
//! of a hole across a cell's faces, which the sequent alphabet derives
//! separately as [`CellVariance`].
//!
//! # Polarity
//!
//! `Polarity` is the cut's evaluation orientation: a positive cut runs its
//! producer first, a negative cut its consumer first, which is how a cut
//! resolves the critical pair of its two binders. It is not the
//! value/computation sort of call-by-push-value, and not the variance of a hole
//! across a cell's two faces, which the sequent alphabet derives separately as
//! `CellVariance`; the name collides with both in neighbouring literature, so
//! the axis is stated here.
//!
//! The enum lives in this crate because its only readers are here: the pattern
//! language, the reduction order and the η requirement. A crate of its own
//! would cost a crate for a two-variant enum with one consumer, and a core-tier
//! crate would put a core edge under a theory crate, which the layering
//! forbids. A core-tier sequent language imports this tag rather than minting
//! its own; a second theory crate that needs the tag without the substrate
//! moves it to a leaf theory crate.
//!
//! [`CellVariance`]: crate::sequent::CellVariance

/// The evaluation-strategy orientation of a cut.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Polarity
{
    /// A positive cut `⟨p |+ c⟩`: the producer runs first.
    Positive,
    /// A negative cut `⟨p |− c⟩`: the consumer runs first.
    Negative,
}
