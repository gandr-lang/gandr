//! The cell-admission linearity boundary: cell patterns are linear on the
//! left.
//!
//! A metavariable occurring twice on a cell's left-hand side is a copy on a
//! wire. A term-shaped store gets the copy free, because substitution copies,
//! but a circuit needs a comonoid the type may not have. The boundary refuses
//! the copy; a type supplying a cocommutative comonoid that hosts it
//! explicitly is a later generalization, not part of this module.
//!
//! # Admission, not construction
//!
//! The check governs which cells enter a store, never which patterns can be
//! built. [`crate::sequent::CellMeta::derive`] keeps computing the per-hole
//! metadata and refuses nothing, because non-linear command patterns are
//! legitimate internal shapes: a unification goal routinely carries a
//! repeated metavariable. So the refusal runs on the path that turns a
//! description into cells, and nowhere deeper.
//!
//! # The right-hand side is reported, not refused
//!
//! Linearity here is a redex-side condition. A right-hand side that repeats a
//! hole duplicates it, and that step growth is reported
//! ([`crate::sequent::CellMeta::step_growth`]) rather than refused: the cost
//! of a duplicating contractum is a budget question for the engine that fires
//! the cell, not a property of the rule.
//!
//! # A hole at two polarities is a seam, not a copy
//!
//! Holes are identified by name across a cell's two faces, so a name worn by
//! a producer and a consumer metavariable is one hole at two polarities: the
//! dinaturality seam the composition gate reads. That shape is not a copy and
//! is not refused, because the copy relation is per `(name, category)` pair,
//! which is exactly [`MetaVar`]'s own equality.

use anodized::spec;
use quenchant_shape::shape::Maybe;

use crate::alphabet::CellAlphabet;
use crate::cell::Cell;
use crate::pattern::Cat;
use crate::pattern::MetaVar;
use crate::sequent::SequentAlphabet;

/// A refused non-linear cell pattern: the admission diagnostic, naming the
/// copy.
///
/// The copied metavariable is the leftmost hole whose `(name, category)` pair
/// occurs more than once on the refused cell's left-hand side. Its rendering
/// names the hole and points at the respelling, so a reader is told what to
/// write instead.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct NonLinearPattern
{
    /// The copied hole.
    copied: MetaVar,
}

impl NonLinearPattern
{
    /// The copied hole: the metavariable whose `(name, category)` pair occurs
    /// more than once on the refused left-hand side.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn copied(&self) -> &MetaVar
    {
        &self.copied
    }
}

impl core::fmt::Display for NonLinearPattern
{
    /// Names the copied hole and the respelling.
    ///
    /// # Specification
    /// - ensures: the rendering names the hole's category and name, states that
    ///   cell patterns are linear, and shows how an idempotence or cancellation
    ///   law is respelled without the copy.
    /// - fails: the formatter's error when its output sink rejects a write.
    /// - panics: none.
    /// - executable: none — a formatter exposes no readable rendering at
    ///   function exit; the owned display result and sink failures are
    ///   witnessed.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — producer and consumer refusals retain their supplied
    ///   hole names in the rendered diagnostic, and a refusing sink propagates
    ///   its error. Lost identity and discarded write failures change the
    ///   observations; incidental prose is not pinned.
    /// - witness: `linearity::tests::refusal_payloads_and_rendering_preserve_hole_identity`
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        let side = match self.copied.cat() {
            | Cat::Producer => "producer",
            | Cat::Consumer => "consumer",
        };
        write!(
            f,
            "non-linear cell pattern: the {side} hole `{name}` occurs more than once on the \
             left-hand side, which is a copy on a wire, and a copy needs a comonoid the type may \
             not have; cell patterns are linear. Respell the rule with the copy named: an \
             idempotence or cancellation law written with a repeated hole — `and(x, x) ==> x`, \
             `x - x ==> 0` — is written instead by matching through the copying cell, exactly as a \
             fan-in cell must name its monoid, and a type supplying a cocommutative comonoid may \
             host the copy explicitly.",
            name = self.copied.hole(),
        )
    }
}

impl core::error::Error for NonLinearPattern
{
}

quenchant_shape::reason_enum! {
    /// Why a cell's left-hand side copies no hole.
    pub mod copy_search {
        /// The reason no copy is named.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// Every metavariable occurrence on the left-hand side is distinct.
            Linear,
        }
    }
}

/// The leftmost hole `cell`'s left-hand side copies: the alphabet-neutral
/// half of the linearity boundary.
///
/// Copying is judged by the alphabet's own metavariable equality over the
/// left-to-right occurrence list ([`CellAlphabet::metavariables`], which keeps
/// repeats). For the sequent alphabet that equality is the
/// `(name, category)` pair, so a hole worn at both polarities contributes one
/// occurrence per polarity and is not a copy.
///
/// # Specification
/// - requires: `A::metavariables` yields one entry per occurrence, left to
///   right, as the trait requires.
/// - ensures: the leftmost occurrence equal to a later occurrence on the same
///   left-hand side; the right-hand side is never read, because linearity is a
///   redex-side condition.
/// - provides: [`copy_search::Absent::Linear`] when every occurrence is
///   distinct.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the three decision surfaces (a repeat found, polarity
///   told apart, the side read) are separated by one copied pattern, one
///   two-polarity seam, and one cell linear on the left that repeats on the
///   right; the inhabitant suite of `gandr-theory-cell-complexes-tools` runs
///   the search over a second alphabet through the same interface.
/// - witness: `linearity::tests::a_repeated_producer_hole_is_the_copy`
/// - witness: `linearity::tests::a_hole_at_both_polarities_is_not_a_copy`
/// - witness: `linearity::tests::a_repeat_on_the_right_hand_side_is_not_a_copy`
/// - witness: `linearity::tests::admission_chooses_the_first_copied_occurrence_and_accepts_ground_terms`
#[inline]
#[spec(captures: occurrences = A::metavariables(cell.lhs()), ensures: |output| {
    let first = occurrences.iter().enumerate().find(|entry| occurrences.iter().skip(entry.0.saturating_add(1)).any(|later| later == entry.1));
    match output {
        Maybe::Present(ref copied) => first.is_some_and(|(_, expected)| copied == expected),
        Maybe::Absent(copy_search::Absent::Linear) => first.is_none(),
    }
})]
pub fn copied_hole<A>(cell: &Cell<A>) -> Maybe<A::Var, copy_search::Absent>
where
    A: CellAlphabet,
{
    let occurrences = A::metavariables(cell.lhs());
    for (index, var) in occurrences.iter().enumerate() {
        let mut later = occurrences.iter().skip(index.saturating_add(1));
        if later.any(|other| other == var) {
            return Maybe::Present(var.clone());
        }
    }
    Maybe::Absent(copy_search::Absent::Linear)
}

/// The admission boundary: admits `cell` only when its left-hand side copies
/// no hole.
///
/// This is the refusal every description-sourced cell runs before it enters
/// a store. It refuses nothing [`crate::sequent::CellMeta::derive`] computes:
/// metadata derivation and admission are separate, so internally built
/// non-linear patterns stay constructible, and a duplicating right-hand side
/// is admitted and reported by its step growth.
///
/// # Specification
/// - ensures: success exactly when [`copied_hole`] names no copy; the cell is
///   only read.
/// - fails: [`NonLinearPattern`] naming the leftmost copied hole.
/// - panics: none.
///
/// # Errors
/// [`NonLinearPattern`] when the left-hand side repeats a
/// `(name, category)` pair.
///
/// # Adequacy
/// - hypothesis: L3 — copied, linear and ground redexes separate both outcomes;
///   two distinct copied holes distinguish first-occurrence priority from
///   first-completed-repeat priority. Swapped categories, reversed admission
///   and a wrong refusal payload change the observation; right-hand repeats do
///   not alter the redex-side condition.
/// - witness: `linearity::tests::refusal_payloads_and_rendering_preserve_hole_identity`
/// - witness: `linearity::tests::admission_chooses_the_first_copied_occurrence_and_accepts_ground_terms`
/// - witness: `linearity::tests::a_hole_at_both_polarities_is_admitted`
/// - witness: `linearity::tests::a_linear_cell_is_admitted`
#[inline]
#[spec(ensures: |output| match output {
    Ok(()) => matches!(copied_hole(cell), Maybe::Absent(copy_search::Absent::Linear)),
    Err(ref refusal) => matches!(copied_hole(cell), Maybe::Present(ref copied) if refusal.copied() == copied),
})]
pub fn admit_linear_cell(cell: &Cell<SequentAlphabet>) -> Result<(), NonLinearPattern>
{
    match copied_hole(cell) {
        | Maybe::Present(copied) => Err(NonLinearPattern { copied }),
        | Maybe::Absent(copy_search::Absent::Linear) => Ok(()),
    }
}

#[cfg(test)]
mod tests
{
    use alloc::format;

    use super::*;
    use crate::boundary::CellInvertibility;
    use crate::pattern::CmdPat;
    use crate::pattern::ConsPat;
    use crate::pattern::ProdPat;
    use crate::polarity::Polarity;
    use crate::sequent::CellMeta;
    use crate::sequent::CellProvenance;
    use crate::sequent::Orientation;

    /// A surface-rule cell over the two given faces.
    ///
    /// # Specification
    /// trivial.
    fn rule_cell(
        lhs: CmdPat,
        rhs: CmdPat,
    ) -> Cell
    {
        Cell::new(
            lhs,
            rhs,
            Orientation::PolarityDerived,
            CellProvenance::SurfaceRule,
        )
    }

    /// `⟨x | and(x; α)⟩`: the elaborated shape of `rule and(x, x) ==> x`.
    ///
    /// # Specification
    /// trivial.
    fn idempotence_lhs() -> CmdPat
    {
        CmdPat::cut(
            Polarity::Positive,
            ProdPat::meta("x"),
            ConsPat::op("and", [ProdPat::meta("x")], ConsPat::meta("alpha")),
        )
    }

    /// `⟨r | seam(; r)⟩`: one hole worn at both polarities.
    ///
    /// # Specification
    /// trivial.
    fn seam_lhs() -> CmdPat
    {
        CmdPat::cut(
            Polarity::Positive,
            ProdPat::meta("r"),
            ConsPat::op("seam", [], ConsPat::meta("r")),
        )
    }

    #[test]
    fn a_repeated_producer_hole_is_the_copy()
    {
        let cell = rule_cell(
            idempotence_lhs(),
            CmdPat::cut(
                Polarity::Positive,
                ProdPat::meta("x"),
                ConsPat::meta("alpha"),
            ),
        );
        let Maybe::Present(copied) = copied_hole(&cell)
        else {
            panic!("the repeated hole is found");
        };
        assert_eq!(
            MetaVar::producer("x"),
            copied,
            "the copy is the producer hole x"
        );
    }

    #[test]
    fn a_hole_at_both_polarities_is_not_a_copy()
    {
        // `r` is worn by a producer and a consumer metavariable: one hole at
        // two polarities, so the copy relation — per `(name, category)` —
        // sees two distinct occurrences, not a repeat.
        let cell = rule_cell(seam_lhs(), seam_lhs());
        assert_eq!(
            Maybe::Absent(copy_search::Absent::Linear),
            copied_hole(&cell),
            "a seam is not a copy"
        );
    }

    #[test]
    fn a_repeat_on_the_right_hand_side_is_not_a_copy()
    {
        // `⟨x | dup(; α)⟩ ~> ⟨Pair(x, x) | α⟩` — linearity is a redex-side
        // condition, so duplication in the contractum is admitted.
        let cell = rule_cell(
            CmdPat::cut(
                Polarity::Positive,
                ProdPat::meta("x"),
                ConsPat::op("dup", [], ConsPat::meta("alpha")),
            ),
            CmdPat::cut(
                Polarity::Positive,
                ProdPat::ctor("Pair", [ProdPat::meta("x"), ProdPat::meta("x")]),
                ConsPat::meta("alpha"),
            ),
        );
        assert_eq!(
            Maybe::Absent(copy_search::Absent::Linear),
            copied_hole(&cell),
            "only the left-hand side is consulted"
        );
    }

    #[test]
    fn refusal_payloads_and_rendering_preserve_hole_identity()
    {
        use core::fmt::Write as _;

        struct RefusingWriter;
        impl core::fmt::Write for RefusingWriter
        {
            /// # Specification
            /// trivial.
            fn write_str(
                &mut self,
                _: &str,
            ) -> core::fmt::Result
            {
                Err(core::fmt::Error)
            }
        }
        for copied in [
            MetaVar::producer("requested_producer_42"),
            MetaVar::consumer("requested_consumer_81"),
        ] {
            let refusal = NonLinearPattern {
                copied: copied.clone(),
            };
            assert!(format!("{refusal}").contains(&format!("{}", copied.hole())));
            assert!(write!(&mut RefusingWriter, "{refusal}").is_err());
        }
        let cell = rule_cell(idempotence_lhs(), seam_lhs());
        assert_eq!(
            &MetaVar::producer("x"),
            admit_linear_cell(&cell)
                .expect_err("a copy is refused")
                .copied()
        );
    }

    #[test]
    fn admission_chooses_the_first_copied_occurrence_and_accepts_ground_terms()
    {
        let lhs = CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Tuple", [
                ProdPat::meta("first"),
                ProdPat::meta("second"),
                ProdPat::meta("second"),
                ProdPat::meta("first"),
            ]),
            ConsPat::top(),
        );
        let cell = rule_cell(lhs.clone(), lhs);
        assert_eq!(
            Maybe::Present(MetaVar::producer("first")),
            copied_hole(&cell)
        );
        assert_eq!(
            &MetaVar::producer("first"),
            admit_linear_cell(&cell)
                .expect_err("both holes are copied")
                .copied()
        );
        let ground = CmdPat::cut(
            Polarity::Negative,
            ProdPat::ctor("Zero", []),
            ConsPat::top(),
        );
        let ground_cell = rule_cell(ground.clone(), ground);
        assert_eq!(
            Maybe::Absent(copy_search::Absent::Linear),
            copied_hole(&ground_cell)
        );
        assert_eq!(Ok(()), admit_linear_cell(&ground_cell));
        let copied_consumer = CmdPat::cut(
            Polarity::Positive,
            ProdPat::meta("x"),
            ConsPat::op("repeat", [ProdPat::meta("x")], ConsPat::meta("x")),
        );
        let cell = rule_cell(copied_consumer.clone(), copied_consumer);
        assert_eq!(Maybe::Present(MetaVar::producer("x")), copied_hole(&cell));
    }

    #[test]
    fn a_hole_at_both_polarities_is_admitted()
    {
        let cell = rule_cell(seam_lhs(), seam_lhs());
        assert_eq!(
            Ok(()),
            admit_linear_cell(&cell),
            "the dinaturality seam is admitted"
        );
        let meta = CellMeta::derive(cell.lhs(), cell.rhs(), CellInvertibility::from(false));
        assert!(
            meta.vars().iter().all(|var| bool::from(var.linear())),
            "and the derived metadata agrees that the seam is linear"
        );
    }

    #[test]
    fn a_linear_cell_is_admitted()
    {
        let cell = rule_cell(
            CmdPat::cut(
                Polarity::Positive,
                ProdPat::ctor("Succ", [ProdPat::meta("m")]),
                ConsPat::op("add", [ProdPat::meta("n")], ConsPat::meta("alpha")),
            ),
            CmdPat::cut(
                Polarity::Positive,
                ProdPat::meta("m"),
                ConsPat::op(
                    "add",
                    [ProdPat::meta("n")],
                    ConsPat::frame("Succ", ConsPat::meta("alpha")),
                ),
            ),
        );
        assert_eq!(
            Ok(()),
            admit_linear_cell(&cell),
            "every hole occurs once on the left"
        );
    }
}
