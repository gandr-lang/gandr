//! Splices in the lowering: `~t` where a value is read is a hole the checker
//! fills by running the tactic `t` at the goal the hole stands at.
//!
//! # The reading
//!
//! - The operand is read as a tactic, never as a term: `assumption`, or
//!   `intro(t)` of a tactic `t`. Neither word is resolved as a name, so a
//!   binder named `assumption` leaves the tactic as it is. Any other operand,
//!   and a tactic of [`Tactic::INTROS`] introductions or more, is
//!   [`LoweringRefusal::UnknownTactic`] at the operand.
//! - The hole is nominated as a wildcard's is, its name carrying the tactic
//!   ([`gandr_core_term::hole::HoleId::spliced`]); the checker runs the tactic
//!   and judges its answer, and the kernel replays the filled declaration.
//! - A splice is a value: as a body's tail it is returned, as a literal is, and
//!   where a computation is read otherwise it is a form of the wrong sort.
//!   Where no type checks it, the checker refuses it as having no goal.

use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::tactic::Tactic;

use super::Former;
use super::Lowerer;
use super::Plan;
use super::Produced;
use super::Site;
use super::arguments;
use super::exhausted;
use super::implicit::Nomination;
use crate::error::LoweringRefusal;
use crate::form::Cursor;
use crate::form::Pieces;
use crate::form::Placed;
use crate::form::Shape;
use crate::form::TileName;
use crate::form::read_pieces;
use crate::form::shape_of;

#[cfg(test)]
mod tests;

/// The tactic answering the goal with a binder in scope.
const ASSUMPTION: &str = "assumption";

/// The tactic introducing a function's binder before its body's tactic.
const INTRO: &str = "intro";

impl<'source> Lowerer<'_, 'source>
{
    /// Classify the splice `~t` at `site`, the cursor at its `~`.
    ///
    /// # Specification
    /// - requires: `site` is a splice.
    /// - ensures: nominates a spliced hole carrying the tactic `t` writes and
    ///   plans the splice as that value hole, bridged to its reading as a value
    ///   is; `t` is left unread.
    /// - fails: [`crate::error::FragmentBoundary::WrongSort`] where a
    ///   computation is read and no value is returned;
    ///   [`LoweringRefusal::UnknownTactic`] at an operand writing no tactic;
    ///   the form's own refusal for a splice out of shape; the budget refusal
    ///   once no spliced name is left.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `~assumption` and `~intro(intro(assumption))` plan
    ///   holes carrying their tactics, a body's tail returned; operands writing
    ///   no tactic are refused at the operand, and a splice where a computation
    ///   is read and no value returned is refused of the wrong sort.
    /// - witness: `lower::splice::tests::a_splice_is_a_hole_carrying_its_tactic_2762`
    /// - witness: `lower::splice::tests::an_operand_writing_no_tactic_is_refused_2762`
    #[spec(ensures: |ret| ret.is_err() || matches!(
        self.plans.get(site.at.node),
        Some(&Plan::ValueHole(hole)) if hole.tactic().is_some()
    ))]
    pub(super) fn splice(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let _frame = self.require(site, Produced::Value)?;
        let _tilde = cursor.tile(TileName::TILDE);
        let operand = site.one(cursor.operands())?;
        exhausted(site, &cursor)?;
        let tactic = self.tactic(site, operand)?;
        let hole = self.nominate(Nomination::Spliced(tactic))?;
        self.plan(site, Plan::ValueHole(hole));
        Ok(())
    }

    /// The tactic the splice operand `operand` writes: `assumption` under as
    /// many `intro(…)` as enclose it.
    ///
    /// # Specification
    /// - requires: `operand` is the operand of the splice at `site`.
    /// - ensures: the tactic of one introduction per `intro(…)` enclosing
    ///   `assumption`.
    /// - fails: [`LoweringRefusal::UnknownTactic`] at `operand` when it, or
    ///   what an `intro(…)` in it encloses, is neither `assumption` nor a call
    ///   of `intro` on one argument, or encloses [`Tactic::INTROS`]
    ///   introductions or more; the form's own refusal for a call out of shape.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::splice`].
    /// - witness: `lower::splice::tests::a_splice_is_a_hole_carrying_its_tactic_2762`
    /// - witness: `lower::splice::tests::an_operand_writing_no_tactic_is_refused_2762`
    #[spec(ensures: |ret| ret.as_ref().map_or_else(
        |refusal| matches!(*refusal, LoweringRefusal::UnknownTactic { span } if span == operand.span)
            || !matches!(*refusal, LoweringRefusal::UnknownTactic { .. }),
        |tactic| u8::from(*tactic) < Tactic::INTROS,
    ))]
    fn tactic(
        &self,
        site: Site,
        operand: Placed,
    ) -> Result<Tactic, LoweringRefusal<'source>>
    {
        let unknown = LoweringRefusal::UnknownTactic { span: operand.span };
        let named = |at: Placed, word: &str| {
            self.tree.node(at.node).is_some_and(|node| {
                matches!(
                    shape_of(self.pbg, node),
                    Ok(Shape::Form {
                        former: Former::Name,
                        ..
                    })
                )
            }) && self.name_at(at).as_ref() == word
        };
        let mut called = Pieces::new();
        let mut written = Vec::new();
        let mut tactic = Tactic::ASSUMPTION;
        let mut at = operand;
        while !named(at, ASSUMPTION) {
            let Some(node) = self.tree.node(at.node)
            else {
                return Err(unknown);
            };
            let Shape::Form {
                former: Former::Call,
                ..
            } = shape_of(self.pbg, node)?
            else {
                return Err(unknown);
            };
            read_pieces(self.pbg, self.tree, at.node, &mut called)?;
            let mut cursor = Cursor::new(&called.pieces, at.span);
            let head = site.one(cursor.operands())?;
            written.clear();
            arguments(site, &mut cursor, &mut written)?;
            let (true, &[argument]) = (named(head, INTRO), written.as_slice())
            else {
                return Err(unknown);
            };
            let Some(inner) = self.tree.node(argument)
            else {
                return Err(unknown);
            };
            at = Placed::of(argument, inner);
            tactic = tactic.intro().ok_or(unknown)?;
        }
        Ok(tactic)
    }
}
