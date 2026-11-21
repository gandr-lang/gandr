//! A sum of reductions: reductions of one type side by side, as one
//! reduction.
//!
//! Each cell of the sum is a cell of one part, and it names its part. Each
//! composite and each witness names its part too. A map reads the part of
//! what it receives and answers in that part, so the rows of two parts stay
//! apart even where their values agree. The source and the target are the
//! parts' sources and targets in part order. The replay replays each part in
//! part order, and a refusal names its part.
//!
//! A sum and then a reduction of its target compose through
//! [`Reduction::then`]: a family of families reduces part by part first, and
//! the parts' targets reduce together second.
//!
//! # References
//!
//! - `vault:01a1aa2d-a69c-7030-91e0-337d68d88151` — anchor: §
//!   presented-spaces-normal-forms. Reductions compose in sequence and from
//!   local to global, and a sum is the local side: one reduction for each part.

use alloc::vec::Vec;

use anodized::spec;

use crate::equivalence::Closure;
use crate::equivalence::Refusal;
use crate::error::MorseError;
use crate::reduction::Answer;
use crate::reduction::Reduction;

wrapper! {
    /// The place of a part in a sum, in part order.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct PartIndex(usize);
}

/// A value of one part of a sum: a cell, a composite or a witness, with the
/// part that it belongs to.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Summand<Value>
{
    /// The part that the value belongs to.
    part: PartIndex,
    /// The value, as its part reads it.
    value: Value,
}

impl<Value> Summand<Value>
{
    /// `value` in the part at `part`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        part: PartIndex,
        value: Value,
    ) -> Self
    {
        Self { part, value }
    }

    /// The part that the value belongs to.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn part(&self) -> PartIndex
    {
        self.part
    }

    /// The value, as its part reads it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn value(&self) -> &Value
    {
        &self.value
    }
}

/// Why a sum cannot answer.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SumFault<Fault>
{
    /// The sum holds no part at this place.
    NoPart(PartIndex),
    /// Two witnesses of two parts, which do not compose.
    Apart
    {
        /// The part of the first witness.
        first: PartIndex,
        /// The part of the second witness.
        second: PartIndex,
    },
    /// A part refuses with its own fault.
    Part
    {
        /// The part that refuses.
        part: PartIndex,
        /// The part's own fault.
        fault: Fault,
    },
}

/// The refusal of the part at `part`, read in the sum: each cell with its
/// part, and the part's own fault with its part. A refusal that names no cell
/// and no fault of the part keeps no part: a count, a budget or an overflow.
///
/// # Specification
/// trivial.
fn lifted<Cell, Fault>(
    part: PartIndex,
    refusal: Refusal<Cell, Fault>,
) -> Refusal<Summand<Cell>, SumFault<Fault>>
{
    let named = |cell| Summand::new(part, cell);
    match refusal {
        Refusal::Cycle(count) => Refusal::Cycle(count),
        Refusal::Unpaired(count) => Refusal::Unpaired(count),
        Refusal::Outside(count) => Refusal::Outside(count),
        Refusal::Unpairable(count) => Refusal::Unpairable(count),
        Refusal::Unmatched(cell) => Refusal::Unmatched(cell.map(named)),
        Refusal::Forged(cell) => Refusal::Forged(named(cell)),
        Refusal::Circular(cell) => Refusal::Circular(named(cell)),
        Refusal::Unclosed(cell) => Refusal::Unclosed(named(cell)),
        Refusal::Unretracted(cell) => Refusal::Unretracted(named(cell)),
        Refusal::Morse(MorseError::Complex(fault)) => {
            Refusal::Morse(MorseError::Complex(SumFault::Part { part, fault }))
        },
        Refusal::Morse(MorseError::PastBudget(budget)) => {
            Refusal::Morse(MorseError::PastBudget(budget))
        },
        Refusal::Morse(MorseError::Overflow) => Refusal::Morse(MorseError::Overflow),
    }
}

/// The cells that `cells` reads from each of `parts`, each with its part, in
/// part order.
///
/// # Specification
/// trivial.
fn named<R>(
    parts: &[R],
    cells: for<'part> fn(&'part R) -> &'part [R::Cell],
) -> Vec<Summand<R::Cell>>
where
    R: Reduction,
{
    parts
        .iter()
        .enumerate()
        .flat_map(|(index, part)| {
            let at = PartIndex::from(index);
            cells(part)
                .iter()
                .map(move |cell| Summand::new(at, cell.clone()))
        })
        .collect()
}

/// Reductions of one type side by side, as one reduction.
#[derive(Debug)]
pub struct Sum<R: Reduction>
{
    /// The parts, in part order.
    parts: Vec<R>,
    /// The parts' source cells, each with its part, in part order.
    source: Vec<Summand<R::Cell>>,
    /// The parts' target cells, each with its part, in part order.
    target: Vec<Summand<R::Cell>>,
}

impl<R: Reduction> Sum<R>
{
    /// The sum of `parts`, in their order.
    ///
    /// # Specification
    /// - ensures: the source is each part's source, and the target each part's
    ///   target, in part order, each cell with the place of its part.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a sum of two collapses of the triangle with other
    ///   pairs, whose cells coincide part by part. The cell observer rejects a
    ///   dropped part, two parts in the other order and a cell named with the
    ///   other part.
    /// - witness: `tests::equivalence::a_sum_reads_each_cell_in_its_own_part`
    #[spec(ensures: |output| output.source.iter().map(|cell| (cell.part, &cell.value))
            .eq(output.parts.iter().enumerate().flat_map(|(index, part)|
                part.source().iter().map(move |cell| (PartIndex::from(index), cell))))
        && output.target.iter().map(|cell| (cell.part, &cell.value))
            .eq(output.parts.iter().enumerate().flat_map(|(index, part)|
                part.target().iter().map(move |cell| (PartIndex::from(index), cell)))))]
    #[inline]
    #[must_use]
    pub fn new(parts: Vec<R>) -> Self
    {
        let source = named(&parts, R::source);
        let target = named(&parts, R::target);
        Self {
            parts,
            source,
            target,
        }
    }

    /// The answer of the part at `part` to `step`, with its refusal read in
    /// the sum.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// - [`SumFault::NoPart`]: the sum holds no part at `part`.
    /// - each refusal of the part, with its part.
    fn within<Value>(
        &mut self,
        part: PartIndex,
        step: impl FnOnce(&mut R) -> Answer<R, Value>,
    ) -> Answer<Self, Value>
    {
        let reduction = self
            .parts
            .get_mut(usize::from(part))
            .ok_or(Refusal::Morse(MorseError::Complex(SumFault::NoPart(part))))?;
        step(reduction).map_err(|refusal| lifted(part, refusal))
    }
}

impl<R: Reduction> Reduction for Sum<R>
{
    type Cell = Summand<R::Cell>;
    type Composite = Summand<R::Composite>;
    type Fault = SumFault<R::Fault>;
    type Witness = Summand<R::Witness>;

    /// Each part's source, in part order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn source(&self) -> &[Self::Cell]
    {
        &self.source
    }

    /// Each part's target, in part order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn target(&self) -> &[Self::Cell]
    {
        &self.target
    }

    /// The generator that the cell's part gives.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn generator(
        &mut self,
        cell: &Self::Cell,
    ) -> Answer<Self, Self::Composite>
    {
        let part = cell.part;
        self.within(part, |reduction| reduction.generator(&cell.value))
            .map(|value| Summand::new(part, value))
    }

    /// The collapse in the composite's part.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn collapse(
        &mut self,
        composite: &Self::Composite,
    ) -> Answer<Self, Self::Composite>
    {
        let part = composite.part;
        self.within(part, |reduction| reduction.collapse(&composite.value))
            .map(|value| Summand::new(part, value))
    }

    /// The inclusion in the composite's part.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn include(
        &mut self,
        composite: &Self::Composite,
    ) -> Answer<Self, Self::Composite>
    {
        let part = composite.part;
        self.within(part, |reduction| reduction.include(&composite.value))
            .map(|value| Summand::new(part, value))
    }

    /// The section in the composite's part.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn section(
        &mut self,
        composite: &Self::Composite,
    ) -> Answer<Self, Option<Self::Witness>>
    {
        let part = composite.part;
        self.within(part, |reduction| reduction.section(&composite.value))
            .map(|witness| witness.map(|value| Summand::new(part, value)))
    }

    /// The retraction in the composite's part.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn retraction(
        &mut self,
        composite: &Self::Composite,
    ) -> Answer<Self, Option<Self::Witness>>
    {
        let part = composite.part;
        self.within(part, |reduction| reduction.retraction(&composite.value))
            .map(|witness| witness.map(|value| Summand::new(part, value)))
    }

    /// The witness carried in its own part.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn include_witness(
        &mut self,
        witness: &Self::Witness,
    ) -> Answer<Self, Self::Witness>
    {
        let part = witness.part;
        self.within(part, |reduction| reduction.include_witness(&witness.value))
            .map(|value| Summand::new(part, value))
    }

    /// The witness carried in its own part.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn collapse_witness(
        &mut self,
        witness: &Self::Witness,
    ) -> Answer<Self, Self::Witness>
    {
        let part = witness.part;
        self.within(part, |reduction| reduction.collapse_witness(&witness.value))
            .map(|value| Summand::new(part, value))
    }

    /// The composite in the witnesses' part. Two witnesses of two parts do not
    /// compose.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn compose(
        &mut self,
        first: &Self::Witness,
        second: &Self::Witness,
    ) -> Answer<Self, Self::Witness>
    {
        let part = first.part;
        if second.part != part {
            return Err(Refusal::Morse(MorseError::Complex(SumFault::Apart {
                first: part,
                second: second.part,
            })));
        }
        self.within(part, |reduction| {
            reduction.compose(&first.value, &second.value)
        })
        .map(|value| Summand::new(part, value))
    }

    /// The replay in the witness's part. A witness never closes between
    /// composites of another part.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn closes(
        &mut self,
        witness: &Self::Witness,
        source: &Self::Composite,
        target: &Self::Composite,
    ) -> Answer<Self, Closure>
    {
        let part = witness.part;
        if source.part != part || target.part != part {
            return Ok(Closure::Open);
        }
        self.within(part, |reduction| {
            reduction.closes(&witness.value, &source.value, &target.value)
        })
    }

    /// Replay each part in part order.
    ///
    /// # Specification
    /// - ensures: `Ok` exactly when each part replays.
    /// - fails: the refusal of the first part that does not replay, each cell
    ///   in it with that part, and its own fault as [`SumFault::Part`].
    /// - panics: none.
    /// - executable: none — the body is the predicate.
    /// - intension: one replay of each part.
    ///
    /// # Errors
    /// - each [`Refusal`] of a part, with its part.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a sum of two collapses of the triangle replays, and a
    ///   sum of two composites whose second part reads other cells is refused
    ///   at that part's cell. The part observer rejects a refusal named with
    ///   the first part or with no part.
    /// - witness: `tests::equivalence::a_sum_reads_each_cell_in_its_own_part`
    /// - witness: `tests::equivalence::a_part_that_does_not_replay_is_refused_with_its_part`
    #[inline]
    fn replay(&mut self) -> Answer<Self, ()>
    {
        for (index, part) in self.parts.iter_mut().enumerate() {
            part.replay()
                .map_err(|refusal| lifted(PartIndex::from(index), refusal))?;
        }
        Ok(())
    }
}
