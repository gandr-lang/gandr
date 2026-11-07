//! A reduction of one complex onto another: the collapse, the inclusion, the
//! witnesses of the two inverse laws, and their replay, with the composite
//! of two reductions in sequence.
//!
//! A Morse collapse is one instance: an [`Equivalence`](crate::Equivalence)
//! read on its complex. The composite of two reductions collapses by the
//! first and then the second, and includes by the second and then the first.
//! Its witness at a cell is the first reduction's witness, then the second
//! reduction's witness at the collapsed cell, carried back by the first
//! inclusion. So two successive collapses compose into one reduction that
//! replays as one.
//!
//! Each removal of an equivalence, matched alone, is one Tietze move. Its
//! collapse is the backward move, which removes a cell that its partner
//! defines, and its inclusion is the forward move, which adds the cell back.
//! An equivalence collapses each cell as its removals do one at a time, the
//! last removal first.
//!
//! # Witnesses
//!
//! `tests::basis::each_removal_of_the_braid_reduction_is_one_tietze_move_6059`
//! in `theory-coherent-resolutions` matches each removal of the B₃⁺ reduction
//! alone, replays it, and composes the moves.
//! `tests::squier::brown_collapse_of_intop_factors_through_its_tietze_moves_6059`
//! in `surface-lowering` does the same for the removals of Brown's scheme on
//! a bar complex.
//!
//! # Boundaries
//!
//! - **A presentation's own letter.** The bar complex holds normal forms alone.
//!   So a letter that a rule defines drops by a move on the written
//!   presentation, before the resolution, and no removal of Brown's scheme
//!   holds it.
//! - **Torsion.** A sequence of moves and their inclusions certifies a simple
//!   equivalence, which is finer than an equivalence of the presented objects.
//!   Whitehead torsion is the complete obstruction. It lives in chains over the
//!   group ring of the fundamental group, so integer chains show none.
//!
//! # References
//!
//! - `Doré-2023-computing_spaces_type_theory` — exemplar: § 3.5 states the
//!   collapse `φ` and the inclusion `ι` of a graph with both inverse proofs,
//!   and § 3.6 lifts them to an equality of types, which composes. A
//!   [`Reduction`] states those four parts and their replay.
//! - `Ara-2025-polygraphs_rewriting_higher_categories` — newest: § 7.4.2, the
//!   retraction that each elementary Tietze transformation carries, and §
//!   7.4.6–7.4.8, the collapse of a collapsible generator, which keeps the
//!   Tietze class.
//! - `Waas-2025-stratified_homotopy_theory_generalized_simple_homotopy_theory_foundations_applications_intersections`
//!   — newest: § 2.1, simple homotopy equivalence and Whitehead torsion, and
//!   Example 2.3.2.2, the torsion of based chains over a ring.
//! - `vault:01a1aa2d-a69c-7030-91e0-337d68d88151` — anchor: §
//!   presented-spaces-stone-universe. The edit calculus takes its moves from
//!   the collapse, and each removal is one such move.

use alloc::borrow::Cow;
use alloc::vec::Vec;

use crate::equivalence::Closure;
use crate::equivalence::Refusal;
use crate::equivalence::matched;

/// What a step of the reduction `R` gives: its value, or a refusal at a cell
/// of `R`, with the fault of `R`'s complex.
pub type Answer<R, Value> = Result<Value, Refusal<<R as Reduction>::Cell, <R as Reduction>::Fault>>;

/// A reduction of a source complex onto a target complex, on composites of
/// one kind.
///
/// The collapse sends a composite of the source to one of the target, and
/// the inclusion sends a composite of the target back. The section gives a
/// witness from a composite to its inclusion after its collapse. The
/// retraction gives a witness from the collapse after the inclusion back to
/// a composite of the target. Each target cell is a source cell, so one
/// generator serves both.
pub trait Reduction
{
    /// A cell of the source.
    type Cell: Clone + Ord;
    /// A composite of cells.
    type Composite: Clone + Eq;
    /// A cell between two composites.
    type Witness: Clone;
    /// Why the complex cannot answer.
    type Fault;

    /// The cells of the source that the reduction reads.
    ///
    /// # Specification
    /// trivial.
    fn source(&self) -> &[Self::Cell];

    /// The cells of the target: the source cells that the inclusion includes.
    ///
    /// # Specification
    /// trivial.
    fn target(&self) -> &[Self::Cell];

    /// The source composite of `cell` alone.
    ///
    /// # Specification
    /// - requires: `cell` lies in the source.
    /// - provides: the generator of the source that `cell` names.
    /// - fails: with the complex's fault.
    /// - panics: none.
    /// - executable: none — a type-level block: a required method has no body
    ///   of its own, and each implementation states its own checks.
    ///
    /// # Errors
    /// - [`Refusal::Morse`]: the complex cannot read the cell.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the composed collapse of the triangle reads each cell
    ///   of the triangle.
    /// - witness: `tests::equivalence::two_collapses_compose_in_sequence`
    fn generator(
        &mut self,
        cell: &Self::Cell,
    ) -> Answer<Self, Self::Composite>;

    /// `φ` of a source composite: a composite of the target.
    ///
    /// # Specification
    /// - provides: the composite of the target that `composite` collapses to.
    /// - fails: with the complex's fault.
    /// - panics: none.
    /// - executable: none — a type-level block: a required method has no body
    ///   of its own, and each implementation states its own checks.
    ///
    /// # Errors
    /// - [`Refusal::Morse`]: the complex cannot collapse the composite.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the composed collapse of the triangle sends `b` and
    ///   `c` to `a`, and the edge `r` to the loop at `a`.
    /// - witness: `tests::equivalence::two_collapses_compose_in_sequence`
    fn collapse(
        &mut self,
        composite: &Self::Composite,
    ) -> Answer<Self, Self::Composite>;

    /// `ι` of a target composite: a composite of the source.
    ///
    /// # Specification
    /// - provides: the composite of the source that `composite` includes as.
    /// - fails: with the complex's fault.
    /// - panics: none.
    /// - executable: none — a type-level block: a required method has no body
    ///   of its own, and each implementation states its own checks.
    ///
    /// # Errors
    /// - [`Refusal::Morse`]: the complex cannot include the composite.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the composed inclusion of the loop is the whole
    ///   boundary of the triangle.
    /// - witness: `tests::equivalence::two_collapses_compose_in_sequence`
    fn include(
        &mut self,
        composite: &Self::Composite,
    ) -> Answer<Self, Self::Composite>;

    /// The witness from the source composite `composite` to `ι` after `φ` of
    /// it, or nothing where `ι ∘ φ` fixes it.
    ///
    /// # Specification
    /// - provides: a witness from `composite` to its inclusion after its
    ///   collapse.
    /// - fails: with the complex's fault.
    /// - panics: none.
    /// - executable: none — a type-level block: a required method has no body
    ///   of its own, and each implementation states its own checks.
    ///
    /// # Errors
    /// - [`Refusal::Morse`]: the complex cannot whisker the witnesses.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the composed witness of `c` runs from `c` to `a` in
    ///   the triangle.
    /// - witness: `tests::equivalence::two_collapses_compose_in_sequence`
    fn section(
        &mut self,
        composite: &Self::Composite,
    ) -> Answer<Self, Option<Self::Witness>>;

    /// The witness from `φ` after `ι` of the target composite `composite`
    /// back to it, or nothing where `φ ∘ ι` fixes it.
    ///
    /// # Specification
    /// - provides: a witness from the collapse of the inclusion of `composite`
    ///   to `composite`.
    /// - fails: with the complex's fault.
    /// - panics: none.
    /// - executable: none — a type-level block: a required method has no body
    ///   of its own, and each implementation states its own checks.
    ///
    /// # Errors
    /// - [`Refusal::Morse`]: the complex cannot build the witness.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a Morse collapse fixes each target cell, so the
    ///   composed collapse of the triangle gives each target cell back.
    /// - witness: `tests::equivalence::two_collapses_compose_in_sequence`
    fn retraction(
        &mut self,
        composite: &Self::Composite,
    ) -> Answer<Self, Option<Self::Witness>>;

    /// A witness of the target carried into the source: each target cell in
    /// it replaced by its inclusion.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// - [`Refusal::Morse`]: the complex cannot carry the witness.
    fn include_witness(
        &mut self,
        witness: &Self::Witness,
    ) -> Answer<Self, Self::Witness>;

    /// A witness of the source carried into the target: each removed cell in
    /// it replaced by its image.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// - [`Refusal::Morse`]: the complex cannot carry the witness.
    fn collapse_witness(
        &mut self,
        witness: &Self::Witness,
    ) -> Answer<Self, Self::Witness>;

    /// The vertical composite of `first` and then `second`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// - [`Refusal::Morse`]: the complex cannot compose the witnesses.
    fn compose(
        &mut self,
        first: &Self::Witness,
        second: &Self::Witness,
    ) -> Answer<Self, Self::Witness>;

    /// Whether `witness` runs from `source` to `target`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// - [`Refusal::Morse`]: the complex cannot read the witness.
    fn closes(
        &mut self,
        witness: &Self::Witness,
        source: &Self::Composite,
        target: &Self::Composite,
    ) -> Answer<Self, Closure>;

    /// Check the reduction: each refusal by name.
    ///
    /// # Specification
    /// - ensures: `Ok` exactly when every check of the reduction holds.
    /// - fails: the first check that fails comes back by name.
    /// - panics: none.
    /// - executable: none — a type-level block: a required method has no body
    ///   of its own, and each implementation states its own checks.
    ///
    /// # Errors
    /// - each [`Refusal`]: the check that fails.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the composed collapse of the triangle replays, and a
    ///   composite whose second reduction reads other cells is refused.
    /// - witness: `tests::equivalence::two_collapses_compose_in_sequence`
    /// - witness: `tests::equivalence::a_composite_over_other_cells_is_unmatched`
    fn replay(&mut self) -> Answer<Self, ()>;

    /// This reduction and then `next`, which reduces this one's target.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    fn then<Next>(
        self,
        next: Next,
    ) -> Then<Self, Next>
    where
        Self: Sized,
        Next: Reduction<
                Cell = Self::Cell,
                Composite = Self::Composite,
                Witness = Self::Witness,
                Fault = Self::Fault,
            >,
    {
        Then { first: self, next }
    }
}

/// Two reductions in sequence: the second reduces the first one's target.
#[derive(Debug)]
pub struct Then<First, Next>
{
    /// The first reduction.
    first: First,
    /// The reduction of the first one's target.
    next: Next,
}

/// The vertical composite of two optional witnesses, through `compose`; an
/// absent witness is an identity.
///
/// # Specification
/// trivial.
///
/// # Errors
/// - [`Refusal::Morse`]: the complex cannot compose the witnesses.
fn chained<R>(
    reduction: &mut R,
    first: Option<R::Witness>,
    second: Option<R::Witness>,
) -> Answer<R, Option<R::Witness>>
where
    R: Reduction,
{
    Ok(match (first, second) {
        (Some(first), Some(second)) => Some(reduction.compose(&first, &second)?),
        (Some(only), None) | (None, Some(only)) => Some(only),
        (None, None) => None,
    })
}

/// The round trip of `reduction` at its target cell `cell`, whose composite
/// is `own`: `φ` after `ι` gives `own` back, or the retraction closes between
/// them. The inclusion comes back, for the section of the cell.
///
/// # Specification
/// trivial.
///
/// # Errors
/// - each [`Refusal`] of the maps of `reduction`.
/// - [`Refusal::Unretracted`]: `φ ∘ ι` moves the cell.
fn round_trip<R>(
    reduction: &mut R,
    cell: &R::Cell,
    own: &R::Composite,
) -> Answer<R, R::Composite>
where
    R: Reduction,
{
    let included = reduction.include(own)?;
    let back = reduction.collapse(&included)?;
    if back == *own {
        return Ok(included);
    }
    let closes = match reduction.retraction(own)? {
        Some(ref witness) => reduction.closes(witness, &back, own)? == Closure::Closes,
        None => false,
    };
    if closes {
        Ok(included)
    }
    else {
        Err(Refusal::Unretracted(cell.clone()))
    }
}

impl<First, Next> Reduction for Then<First, Next>
where
    First: Reduction,
    Next: Reduction<
            Cell = First::Cell,
            Composite = First::Composite,
            Witness = First::Witness,
            Fault = First::Fault,
        >,
{
    type Cell = First::Cell;
    type Composite = First::Composite;
    type Fault = First::Fault;
    type Witness = First::Witness;

    /// The first reduction's source.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn source(&self) -> &[Self::Cell]
    {
        self.first.source()
    }

    /// The second reduction's target.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn target(&self) -> &[Self::Cell]
    {
        self.next.target()
    }

    /// The first reduction's generator.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn generator(
        &mut self,
        cell: &Self::Cell,
    ) -> Answer<Self, Self::Composite>
    {
        self.first.generator(cell)
    }

    /// The first collapse, then the second.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn collapse(
        &mut self,
        composite: &Self::Composite,
    ) -> Answer<Self, Self::Composite>
    {
        let middle = self.first.collapse(composite)?;
        self.next.collapse(&middle)
    }

    /// The second inclusion, then the first.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn include(
        &mut self,
        composite: &Self::Composite,
    ) -> Answer<Self, Self::Composite>
    {
        let middle = self.next.include(composite)?;
        self.first.include(&middle)
    }

    /// The first section, then the second section at the first collapse,
    /// carried back by the first inclusion.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn section(
        &mut self,
        composite: &Self::Composite,
    ) -> Answer<Self, Option<Self::Witness>>
    {
        let inner = self.first.section(composite)?;
        let middle = self.first.collapse(composite)?;
        let outer = match self.next.section(&middle)? {
            Some(ref witness) => Some(self.first.include_witness(witness)?),
            None => None,
        };
        chained(&mut self.first, inner, outer)
    }

    /// The first retraction at the second inclusion, carried by the second
    /// collapse, then the second retraction.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn retraction(
        &mut self,
        composite: &Self::Composite,
    ) -> Answer<Self, Option<Self::Witness>>
    {
        let middle = self.next.include(composite)?;
        let lower = match self.first.retraction(&middle)? {
            Some(ref witness) => Some(self.next.collapse_witness(witness)?),
            None => None,
        };
        let upper = self.next.retraction(composite)?;
        chained(&mut self.next, lower, upper)
    }

    /// The second carried by the first.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn include_witness(
        &mut self,
        witness: &Self::Witness,
    ) -> Answer<Self, Self::Witness>
    {
        let middle = self.next.include_witness(witness)?;
        self.first.include_witness(&middle)
    }

    /// The first collapse of the witness, then the second.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn collapse_witness(
        &mut self,
        witness: &Self::Witness,
    ) -> Answer<Self, Self::Witness>
    {
        let middle = self.first.collapse_witness(witness)?;
        self.next.collapse_witness(&middle)
    }

    /// The first reduction's composite.
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
        self.first.compose(first, second)
    }

    /// The first reduction's replay of a witness.
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
        self.first.closes(witness, source, target)
    }

    /// Replay each reduction, then the seam and both laws of the composite.
    ///
    /// The first target must be the second source, and the second generator
    /// of each of its cells the first collapse of the first generator. The
    /// replay keeps that first collapse for each seam cell. `φ` after `ι`
    /// gives each target cell's composite back, or the retraction closes
    /// between them. The section of each source cell closes. The round trip
    /// and the section of a source cell come together, in source order, and
    /// share one inclusion. A target cell outside the source comes last.
    ///
    /// # Specification
    /// - ensures: `Ok` exactly when both reductions replay and each check of
    ///   the composite holds.
    /// - fails: a refusal of either reduction comes back as it is. A seam that
    ///   differs is refused as [`Refusal::Unmatched`], a target cell that the
    ///   round trip moves as [`Refusal::Unretracted`], and a section that does
    ///   not close as [`Refusal::Forged`].
    /// - panics: none.
    /// - executable: none — the body is the predicate.
    /// - intension: both replays; one first generator, one first collapse and
    ///   one second generator for each seam cell; then for each source cell one
    ///   generator, one second collapse, one section, and one inclusion and one
    ///   collapse if it is a target cell or its section is not an identity. The
    ///   seam and the target are sorted once for the lookups.
    ///
    /// # Errors
    /// - each [`Refusal`] of either reduction.
    /// - [`Refusal::Unmatched`]: the seam differs.
    /// - [`Refusal::Unretracted`]: `φ ∘ ι` moves a target cell.
    /// - [`Refusal::Forged`]: a section does not close.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the composed collapse of the triangle replays, and a
    ///   second reduction over other cells is refused at the seam.
    /// - witness: `tests::equivalence::two_collapses_compose_in_sequence`
    /// - witness: `tests::equivalence::a_composite_over_other_cells_is_unmatched`
    #[inline]
    fn replay(&mut self) -> Answer<Self, ()>
    {
        self.first.replay()?;
        self.next.replay()?;
        matched(self.first.target(), self.next.source())?;
        let cells: Vec<Self::Cell> = self.next.source().to_vec();
        let mut seam: Vec<(Self::Cell, Self::Composite)> = Vec::with_capacity(cells.len());
        for cell in cells {
            let generator = self.first.generator(&cell)?;
            let lowered = self.first.collapse(&generator)?;
            if self.next.generator(&cell)? != lowered {
                return Err(Refusal::Unmatched(Some(cell)));
            }
            seam.push((cell, lowered));
        }
        seam.sort_unstable_by(|left, right| left.0.cmp(&right.0));
        let mut target: Vec<Self::Cell> = self.next.target().to_vec();
        target.sort_unstable();
        let mut source: Vec<Self::Cell> = self.first.source().to_vec();
        for cell in &source {
            let generator = self.first.generator(cell)?;
            let kept = seam
                .binary_search_by(|&(ref seamed, _)| seamed.cmp(cell))
                .ok()
                .and_then(|place| seam.get(place));
            let lowered = match kept {
                Some(&(_, ref lowered)) => Cow::Borrowed(lowered),
                None => Cow::Owned(self.first.collapse(&generator)?),
            };
            let own = self.next.collapse(&lowered)?;
            let included = if target.binary_search(cell).is_ok() {
                Some(round_trip(self, cell, &own)?)
            }
            else {
                None
            };
            let inner = self.first.section(&generator)?;
            let outer = match self.next.section(&lowered)? {
                Some(ref witness) => Some(self.first.include_witness(witness)?),
                None => None,
            };
            let Some(witness) = chained(&mut self.first, inner, outer)?
            else {
                continue;
            };
            let there = match included {
                Some(there) => there,
                None => self.include(&own)?,
            };
            if self.closes(&witness, &generator, &there)? == Closure::Open {
                return Err(Refusal::Forged(cell.clone()));
            }
        }
        source.sort_unstable();
        for cell in &target {
            if source.binary_search(cell).is_err() {
                let generator = self.generator(cell)?;
                let own = self.collapse(&generator)?;
                round_trip(self, cell, &own)?;
            }
        }
        Ok(())
    }
}
