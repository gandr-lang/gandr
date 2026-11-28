//! Why a reduction does not replay, and whether a witness closes.

use crate::error::Count;
use crate::error::MorseError;

/// Whether a witness closes: its boundary runs from the one composite to the
/// other.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Closure
{
    /// The witness runs from the source to the target.
    Closes,
    /// The witness runs elsewhere.
    Open,
}

/// Why a scheme gives no equivalence, or a reduction does not replay.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Refusal<Cell, Fault>
{
    /// The gradient of the matching closes this many cycles.
    Cycle(Count),
    /// This many cells whose partner does not name them back.
    Unpaired(Count),
    /// This many partners that do not lie in the complex.
    Outside(Count),
    /// This many pairs that the complex's pairing condition refuses.
    Unpairable(Count),
    /// The equivalence and the matching, or two composed reductions, differ
    /// at this cell, or in their count alone.
    Unmatched(Option<Cell>),
    /// The witness at this cell does not close.
    Forged(Cell),
    /// The replacement of this redundant cell holds itself or a later removed
    /// cell, so the definitions run in a cycle.
    Circular(Cell),
    /// The image of this redundant cell still holds a removed cell.
    Unclosed(Cell),
    /// `φ` after `ι` moves this critical cell.
    Unretracted(Cell),
    /// The complex's own fault, or a walk past its budget.
    Morse(MorseError<Fault>),
}

impl<Cell, Fault> From<MorseError<Fault>> for Refusal<Cell, Fault>
{
    /// Wraps the collapse's refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(error: MorseError<Fault>) -> Self
    {
        Self::Morse(error)
    }
}

/// Nothing when two lists of cells are equal, or [`Refusal::Unmatched`] at
/// the cell of the first place where they differ.
///
/// # Specification
/// trivial.
///
/// # Errors
/// - [`Refusal::Unmatched`]: the lists differ, at the cell named, or in their
///   length alone.
#[inline]
pub fn matched<Cell, Fault>(
    found: &[Cell],
    held: &[Cell],
) -> Result<(), Refusal<Cell, Fault>>
where
    Cell: Clone + Eq,
{
    if found == held {
        return Ok(());
    }
    let at = found
        .iter()
        .zip(held)
        .position(|(found, held)| found != held)
        .unwrap_or_else(|| found.len().min(held.len()));
    Err(Refusal::Unmatched(
        found.get(at).or_else(|| held.get(at)).cloned(),
    ))
}
