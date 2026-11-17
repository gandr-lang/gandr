//! Splices in the lowering: `~t` where a value is read is a hole the checker
//! fills by running the tactic `t` at the goal the hole stands at, and
//! `~ports e` is the record of the outputs of the call `e`.
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
//! - The operand `ports e`, with `e` a call that returns several outputs, is no
//!   tactic. The splice stands as `e`, and `e` stands as the record of its
//!   outputs, labelled as the callee labels them. This is the one place where
//!   such a call stands as one value: elsewhere the lowering refuses it
//!   [`LoweringRefusal::OutputsAsOneValue`]. A call that returns one value is
//!   [`LoweringRefusal::UnknownTactic`] at the operand.

use alloc::string::String;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::tactic::Tactic;
use gandr_kernel_term::FieldLabel;

use super::Expressions;
use super::ExpressionsRef;
use super::Families;
use super::Former;
use super::Plan;
use super::Produced;
use super::Site;
use super::arguments;
use super::arity;
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
use crate::lower::model::Models;

/// The tactic answering the goal with a binder in scope.
const ASSUMPTION: &str = "assumption";

/// The tactic introducing a function's binder before its body's tactic.
const INTRO: &str = "intro";

/// The collector of the outputs of a call into the record of its outputs.
const PORTS: &str = "ports";

impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> Expressions<'host, F>
{
    /// Classify the splice `~t` at `site`, the cursor at its `~`.
    ///
    /// # Specification
    /// - requires: `site` is a splice.
    /// - ensures: for `~ports e`, plans the splice as `e`, read where the
    ///   splice is read, and enters `e` in `packed` with the labels of its
    ///   outputs; otherwise nominates a spliced hole carrying the tactic `t`
    ///   writes and plans the splice as that value hole, bridged to its reading
    ///   as a value is; `t` is left unread.
    /// - fails: [`crate::error::FragmentBoundary::WrongSort`] where a
    ///   computation is read and no value is returned;
    ///   [`LoweringRefusal::UnknownTactic`] at an operand writing no tactic,
    ///   and at `ports e` of a call that returns one value; the form's own
    ///   refusal for a splice out of shape; the budget refusal once no spliced
    ///   name is left.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Cost
    /// - allocation: the labels of the outputs of `~ports e`, growth within the
    ///   outputs of the callee
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `~assumption` and `~intro(intro(assumption))` plan
    ///   holes carrying their tactics, a body's tail returned; operands writing
    ///   no tactic are refused at the operand, and a splice where a computation
    ///   is read and no value returned is refused of the wrong sort. `~ports e`
    ///   of a call of two outputs stands as `e`, and of a call of one value is
    ///   refused at the operand.
    /// - witness: `gandr-surface-lowering::lower::splice::tests::a_splice_is_a_hole_carrying_its_tactic_2762`
    /// - witness: `gandr-surface-lowering::lower::splice::tests::an_operand_writing_no_tactic_is_refused_2762`
    /// - witness: `gandr-surface-lowering::lower::arity::tests::a_call_of_outputs_standing_as_one_value_is_their_record`
    #[spec(ensures: |ret| ret.is_err() || match self.cx().plans.get(site.at.node) {
        Some(&Plan::ValueHole(hole)) => hole.tactic().is_some(),
        Some(&Plan::Transparent(collected)) => self.cx().packed.contains_key(&collected),
        _ => false,
    })]
    #[inline]
    pub fn splice(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::Value)?;
        let _tilde = cursor.tile(TileName::TILDE);
        let operand = site.one(cursor.operands())?;
        exhausted(site, &cursor)?;
        if let Some(collected) = self.shared().collected(site, operand)? {
            let Some(outputs) =
                Models::new(self.host()).called_outputs(frame, collected, site.at.node)?
            else {
                return Err(LoweringRefusal::UnknownTactic { span: operand.span });
            };
            let labels = outputs
                .iter()
                .map(|output| match output.key {
                    arity::Key::Label(name, _) => {
                        Some(FieldLabel::from(String::from(name.as_ref())))
                    },
                    arity::Key::Positional | arity::Key::Index(..) => None,
                })
                .collect();
            let _first = self.cx_mut().packed.insert(collected.node, labels);
            self.read(collected.node, site.reading);
            self.plan(site, Plan::Transparent(collected.node));
            return Ok(());
        }
        let tactic = self.shared().tactic(site, operand)?;
        let hole = self.nominate(Nomination::Spliced(tactic))?;
        self.plan(site, Plan::ValueHole(hole));
        Ok(())
    }
}

impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> ExpressionsRef<'host, F>
{
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
    /// - hypothesis: L3 — as
    ///   [`Self::splice`](crate::lower::Expressions::splice).
    /// - witness: `gandr-surface-lowering::lower::splice::tests::a_splice_is_a_hole_carrying_its_tactic_2762`
    /// - witness: `gandr-surface-lowering::lower::splice::tests::an_operand_writing_no_tactic_is_refused_2762`
    ///
    /// # Cost
    /// - allocation: the refusal of a form out of shape, error path
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
            self.cx().tree.node(at.node).is_some_and(|node| {
                matches!(
                    shape_of(self.cx().pbg, node),
                    Ok(Shape::Form {
                        former: Former::Name,
                        ..
                    })
                )
            }) && self.cx().name_at(at).as_ref() == word
        };
        let mut called = Pieces::new();
        let mut written = Vec::new();
        let mut tactic = Tactic::ASSUMPTION;
        let mut at = operand;
        while !named(at, ASSUMPTION) {
            let Some(node) = self.cx().tree.node(at.node)
            else {
                return Err(unknown);
            };
            let Shape::Form {
                former: Former::Call,
                ..
            } = shape_of(self.cx().pbg, node)?
            else {
                return Err(unknown);
            };
            read_pieces(self.cx().pbg, self.cx().tree, at.node, &mut called)?;
            let mut cursor = Cursor::new(&called.pieces, at.span);
            let head = site.one(cursor.operands())?;
            written.clear();
            arguments(site, &mut cursor, &mut written)?;
            let (true, &[argument]) = (named(head, INTRO), written.as_slice())
            else {
                return Err(unknown);
            };
            let Some(inner) = self.cx().tree.node(argument)
            else {
                return Err(unknown);
            };
            at = Placed::of(argument, inner);
            tactic = tactic.intro().ok_or(unknown)?;
        }
        Ok(tactic)
    }

    /// The call `e` that the splice operand `operand` collects, when it writes
    /// `ports e`.
    ///
    /// # Specification
    /// - requires: `operand` is the operand of the splice at `site`.
    /// - ensures: the one argument of `operand` when `operand` is a call whose
    ///   head is the word `ports`, not resolved as a name; nothing for any
    ///   other operand.
    /// - fails: the form's own refusal for a call out of shape.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Cost
    /// - allocation: the pieces and the arguments of the call, setup
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as
    ///   [`Self::splice`](crate::lower::Expressions::splice).
    /// - witness: `gandr-surface-lowering::lower::arity::tests::a_call_of_outputs_standing_as_one_value_is_their_record`
    #[spec(ensures: |ret| !matches!(ret, Ok(Some(collected)) if collected.node == operand.node))]
    fn collected(
        &self,
        site: Site,
        operand: Placed,
    ) -> Result<Option<Placed>, LoweringRefusal<'source>>
    {
        let Some(node) = self.cx().tree.node(operand.node)
        else {
            return Ok(None);
        };
        let Shape::Form {
            former: Former::Call,
            ..
        } = shape_of(self.cx().pbg, node)?
        else {
            return Ok(None);
        };
        let mut called = Pieces::new();
        read_pieces(self.cx().pbg, self.cx().tree, operand.node, &mut called)?;
        let mut cursor = Cursor::new(&called.pieces, operand.span);
        let head = site.one(cursor.operands())?;
        let mut written = Vec::new();
        arguments(site, &mut cursor, &mut written)?;
        let ports = self.cx().tree.node(head.node).is_some_and(|word| {
            matches!(
                shape_of(self.cx().pbg, word),
                Ok(Shape::Form {
                    former: Former::Name,
                    ..
                })
            )
        }) && self.cx().name_at(head).as_ref() == PORTS;
        let (true, &[argument]) = (ports, written.as_slice())
        else {
            return Ok(None);
        };
        Ok(self
            .cx()
            .tree
            .node(argument)
            .map(|inner| Placed::of(argument, inner)))
    }
}
