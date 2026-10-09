//! The cut's orientation.
//!
//! [`Polarity`] is the evaluation-strategy orientation a cut `⟨p |ε c⟩`
//! carries: the axis on which a positive cut runs its producer first
//! (call-by-value) and a negative cut its consumer first (call-by-name). It is
//! not the value/computation sort of call-by-push-value, and not the variance
//! of a hole across a cell's faces, which the sequent alphabet derives
//! separately as [`CellVariance`].
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
