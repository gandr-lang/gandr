//! The block statement `module m = p ;`, which opens the model `p` as `m`
//! over the rest of its block.
//!
//! # An opening is a bind, so its sorts are fresh
//!
//! The statement binds what `return p` returns to `m`: the checker types the
//! rest of the block under a variable of `p`'s model type, never under `p`
//! itself. Each sort that type leaves abstract is therefore the projection of
//! a bound variable, a type no other opening and no outer type names, so two
//! openings of one model are two types and a member's value cannot leave the
//! block at the type its sort stands for. The block's answer type is stated
//! from outside, where `m` is not bound, so an opened sort reaching it is
//! refused by conversion. The kernel replays the same bind.
//!
//! # The model type is read off the declaration
//!
//! `p` is a name a binder or a declaration answers, written at a model type,
//! `Model(T)` or `Model(T) with sort C = A`. `m` is bound at that written
//! type, so `m.x` selects a component as it does off a parameter of the type,
//! and a sort the type fixes reads as its fixed type. Anything else has no
//! members to open and is refused [`LoweringRefusal::NotAModel`].

use anodized::spec;
use gandr_surface_syntax::NodeIndex;
use quenchant_shape::shape::Maybe;

use super::super::Frame;
use super::super::Lowerer;
use super::super::Plan;
use super::super::Reading;
use super::super::Site;
use super::super::Statement;
use super::super::StatementBinding;
use super::super::closed;
use super::super::exits;
use crate::error::FormFault;
use crate::error::LoweringRefusal;
use crate::form::Cursor;
use crate::form::FormName;
use crate::form::Former;
use crate::form::Placed;
use crate::form::TileName;

#[cfg(test)]
mod tests;

impl<'source> Lowerer<'_, 'source>
{
    /// Read one `module m = p ;` statement, its `module` tile `lead` already
    /// read.
    ///
    /// # Specification
    /// - requires: `cursor` stands just past `lead`; `frame` is the frame the
    ///   statement reads under.
    /// - ensures: `p` is read as a computation under `frame`, its value
    ///   returned, and the statement recorded as the bind of what it returns to
    ///   `m`; the frame binding `m` over `frame` at the model type `p` is
    ///   declared at, which the rest of the block reads under, is returned.
    /// - fails: a fault naming the statement for a tile out of shape; the
    ///   name's own resolution refusals; [`LoweringRefusal::NotAModel`] for a
    ///   `p` no binder or declaration written at a model type answers.
    /// - panics: none.
    ///
    /// # Errors
    /// The statement's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a parameter and a declaration at a model type each
    ///   open, their members read off the opened name; an integer and a name
    ///   nothing declares are refused.
    /// - witness: `lower::model::opening::tests::a_model_opens_as_a_bind_over_the_rest_of_its_block_4788`
    /// - witness: `lower::model::opening::tests::a_value_at_no_model_type_is_refused_4788`
    #[spec(
        captures: before = self.cx.statements.mark(),
        ensures: |ret| ret.is_err() || (self.cx.statements.mark() == before.next()
            && self.cx.statements.last().is_some_and(|last| last.origin == lead.node && matches!(last.binding, StatementBinding::Opening { .. }))),
    )]
    pub(in crate::lower) fn module_statement(
        &mut self,
        cursor: &mut Cursor<'_>,
        lead: Placed,
        frame: Frame,
    ) -> Result<Frame, LoweringRefusal<'source>>
    {
        let statement = Site {
            at: lead,
            name: FormName::MODULE_STATEMENT,
            reading: Reading::Computation(frame),
        };
        let Maybe::Present(binder) = cursor.tile(TileName::IDENTIFIER)
        else {
            return Err(statement.fault(cursor.here(), FormFault::MisplacedTile));
        };
        closed(statement, cursor, TileName::EQUALS)?;
        let opened = statement.one(cursor.operands())?;
        closed(statement, cursor, TileName::SEMICOLON)?;
        let stated = self.opened_declared(opened, frame)?;
        let _first = self.cx.opened_models.insert(opened.node, stated);
        let name = self.cx.name_at(binder);
        self.note_binder(binder, frame, name)?;
        let _result = self.cx.results.insert(opened.node);
        self.read(opened.node, Reading::Computation(frame));
        self.cx.statements.push(Statement {
            origin: lead.node,
            bound: opened.node,
            binding: StatementBinding::Opening {
                name: binder.node,
                stated,
                frame,
            },
            rest: exits::Rest::Bound,
        });

        Ok(Frame::Inner(self.cx.scope.extend_typed(
            frame,
            name,
            stated,
            Maybe::Present(binder.span),
        )))
    }

    /// The type node the operand `opened` of a module statement is declared
    /// at.
    ///
    /// # Specification
    /// - requires: `opened` is the statement's operand, read under `frame`.
    /// - ensures: the declared type node of the binder or declaration the name
    ///   resolves to.
    /// - fails: [`LoweringRefusal::NotAModel`] for an operand that is no name,
    ///   or a name no binder or declaration written at a type answers; the
    ///   name's own resolution refusals.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::module_statement`].
    /// - witness: `lower::model::opening::tests::a_value_at_no_model_type_is_refused_4788`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.cx.form_at(opened), Ok(Some((_, Former::Name)))))]
    fn opened_declared(
        &mut self,
        opened: Placed,
        frame: Frame,
    ) -> Result<NodeIndex, LoweringRefusal<'source>>
    {
        let refused = LoweringRefusal::NotAModel {
            span: opened.span,
            name: self.cx.name_at(opened),
        };
        match self.name_type(frame, opened)? {
            Maybe::Present(stated) => Ok(stated),
            Maybe::Absent(_) => Err(refused),
        }
    }

    /// Refuse the name at `site` when a module statement opens it and the type
    /// it is declared at plans as no model type: the classifying sweep plans
    /// that type before the name, never before the statement.
    ///
    /// # Specification
    /// - requires: `site` is a term name, planned.
    /// - ensures: success for a name no module statement opens, and for one
    ///   whose declared type plans, through transparent plans, as a model
    ///   type's bundle.
    /// - fails: [`LoweringRefusal::NotAModel`] otherwise.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::module_statement`].
    /// - witness: `lower::model::opening::tests::a_value_at_no_model_type_is_refused_4788`
    #[spec(ensures: |ret| ret.is_ok() || self.cx.opened_models.contains_key(&site.at.node))]
    pub(in crate::lower) fn opened_model(
        &self,
        site: Site,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let Some(&stated) = self.cx.opened_models.get(&site.at.node)
        else {
            return Ok(());
        };
        let mut at = stated;
        loop {
            match self.cx.plans.get(at) {
                Some(&Plan::Transparent(inner)) => at = inner,
                Some(&Plan::Bundle(_)) => return Ok(()),
                _ => {
                    return Err(LoweringRefusal::NotAModel {
                        span: site.at.span,
                        name: self.cx.name_at(site.at),
                    });
                },
            }
        }
    }
}
