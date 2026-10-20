//! Temporary access in the lowering: the statement that holds a value, the
//! access that lends it to a view, and the two eliminators that end the view.
//!
//! # A held value and a view are names in the linear zone
//!
//! `hold x = e ;` holds the value `e` in the linear slot `x` over the rest of
//! its block, as `fork` binds an endpoint over the rest of its block: the
//! core hold, whose scope is that rest. `access x as v { t } unwind { u }`
//! lends the slot `x` names and binds the view `v`, linearly, over the body
//! `t`; the unwind `u` reads where the access stands, and a missing unwind is
//! `unwind { pure unit }`. `resume(v, e)` and `abort(v)` end the view `v`
//! names, `e` read as a value. Each name a form lends or ends resolves to a
//! linear binder, counted among the linear binders alone as an endpoint is
//! (the `lower::session` module); a name resolving to anything else is
//! refused here, [`FragmentBoundary::Held`] for an access and
//! [`FragmentBoundary::View`] for an eliminator. Which linear binder it is —
//! a held value, a view or an endpoint — is the checker's to judge. A read of
//! either name elsewhere is a linear variable, which the checker reads as the
//! value the slot holds.
//!
//! - Alternatives: the held value as an ordinary binder, which the core's
//!   access could not lend; the view's name bound in the access's own frame,
//!   which would let the unwind name a view the abort has spent.
//! - Reversal: a core context whose zones share one index space.
//!
//! # The body and the unwind are no bodies
//!
//! No path through a function runs through an access's body or its unwind:
//! an exit there would leave the body with its view live, or the unwind
//! with the access half torn down, so an exit in either is refused as not in
//! tail. The last computation of each is its result, a value there returned
//! as a handled subject's is. A hold's scope is the rest of its block, which
//! an early exit commutes through, as it does a fork's parent: the hold binds
//! no intuitionistic variable (the `lower::exits` module). A hold in a block
//! whose ends an early exit continues is declined as unadmitted, as a fork
//! is: the rest copied under the hold would need its linear indices
//! renumbered past the held slot, which the commuting does not carry.
//! Reversal: a commuting that relocates linear indices too.

use anodized::spec;
use gandr_core_term::Zone;
use gandr_core_term::memory::MemoryForm;
use gandr_kernel_term::DeBruijnIndex;
use gandr_surface_syntax::NodeIndex;
use quenchant_shape::shape::Maybe;

use super::Block;
use super::Lowered;
use super::Lowerer;
use super::Plan;
use super::Produced;
use super::Reading;
use super::Resolved;
use super::Sink;
use super::Site;
use super::Statement;
use super::StatementBinding;
use super::closed;
use super::exhausted;
use super::exits;
use super::lowered;
use crate::error::FormFault;
use crate::error::FragmentBoundary;
use crate::error::LoweringRefusal;
use crate::form::Cursor;
use crate::form::FormName;
use crate::form::Piece;
use crate::form::Pieces;
use crate::form::Placed;
use crate::form::TileName;
use crate::origin::Origin;
use crate::resolve::Frame;

#[cfg(test)]
mod tests;

/// A temporary-access form, as the classification read it.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: each index names a linear binder where the form stands; an
///   access's body reads under the view's binder and its unwind where the
///   access stands.
/// - executable: none — the plan holds no scope to resolve its indices in.
///
/// # Adequacy
/// - hypothesis: L3 — the counter's hold, both accesses and both eliminators
///   lower to the core forms they name.
/// - witness: `lower::access::tests::the_counter_lowers_to_its_memory_forms`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Accessed
{
    /// `access x as v { t } unwind { u }`.
    Access
    {
        /// The held slot lent, a linear index where the access stands.
        held: DeBruijnIndex,
        /// The body, under the view's linear binder.
        body: Block,
        /// The unwind, where the access stands, when one is written.
        unwind: Maybe<Block, unwound::Absent>,
    },
    /// `resume(v, e)`.
    Resume
    {
        /// The view ended, a linear index.
        view: DeBruijnIndex,
        /// The value written back.
        value: NodeIndex,
    },
    /// `abort(v)`.
    Abort
    {
        /// The view ended, a linear index.
        view: DeBruijnIndex,
    },
}

impl<'source> Lowerer<'_, 'source>
{
    /// Read one `hold x = e ;` statement, its `hold` tile already read.
    ///
    /// # Specification
    /// - requires: `cursor` stands just past the statement's tile `hold`;
    ///   `frame` is the frame the statement reads under.
    /// - ensures: `e` is read as a value under `frame`; the statement is
    ///   recorded as the hold of `e` over the rest of the block, and the frame
    ///   binding `x` linearly over `frame`, which the rest of the block reads
    ///   under, is returned, its binder recorded as a held slot.
    /// - fails: a fault naming the hold statement for a tile out of shape, the
    ///   value hole's own fault and the binder's own refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The statement's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the counter holds its count over the rest of its
    ///   block, and both accesses name it past the views between.
    /// - witness: `lower::access::tests::the_counter_lowers_to_its_memory_forms`
    #[spec(
        captures: before = self.statements.len(),
        ensures: |ret| ret.is_err() || (self.statements.len() == before.saturating_add(1)
            && self.statements.last().is_some_and(|last| last.origin == hold.node && matches!(last.binding, StatementBinding::Held { .. }))),
    )]
    pub(super) fn hold(
        &mut self,
        cursor: &mut Cursor<'_>,
        hold: Placed,
        frame: Frame,
    ) -> Result<Frame, LoweringRefusal<'source>>
    {
        let statement = Site {
            at: hold,
            name: FormName::HOLD_STATEMENT,
            reading: Reading::Computation(frame),
        };
        let Maybe::Present(binder) = cursor.tile(TileName::IDENTIFIER)
        else {
            return Err(statement.fault(cursor.here(), FormFault::MisplacedTile));
        };
        closed(statement, cursor, TileName::EQUALS)?;
        let value = statement.one(cursor.operands())?;
        closed(statement, cursor, TileName::SEMICOLON)?;
        let name = self.name_at(binder);
        self.note_binder(binder, name)?;
        self.read(value.node, Reading::Value(frame));
        self.statements.push(Statement {
            origin: hold.node,
            bound: hold.node,
            binding: StatementBinding::Held { value: value.node },
            rest: exits::Rest::Bound,
        });

        let slot = self
            .scope
            .extend_linear(frame, name, Maybe::Present(binder.span));
        let _held = self.held.insert(slot);

        Ok(Frame::Inner(slot))
    }

    /// The linear index of the name written at `written`, read under
    /// `frame` by the form at `site`.
    ///
    /// # Specification
    /// - requires: `written` is an identifier tile of the form at `site`.
    /// - ensures: the linear index of the innermost binder of the name
    ///   `written` spells, when that binder is linear.
    /// - fails: [`LoweringRefusal::UnresolvedName`] for a name nothing binds;
    ///   `boundary` at the name for an intuitionistic binder or a declaration;
    ///   the name's own refusals.
    /// - panics: none.
    ///
    /// # Errors
    /// The name's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the counter's names resolve past the views between,
    ///   and a parameter lent or ended is refused at its name.
    /// - witness: `lower::access::tests::the_counter_lowers_to_its_memory_forms`
    /// - witness: `lower::access::tests::an_access_names_a_held_value_and_an_eliminator_its_view`
    #[spec(ensures: |ret| match ret {
        | Err(LoweringRefusal::OutOfFragment { span, boundary: refused, .. }) => refused != boundary || span == written.span,
        | _ => true,
    })]
    fn linear_slot(
        &mut self,
        frame: Frame,
        written: Placed,
        boundary: FragmentBoundary,
    ) -> Result<DeBruijnIndex, LoweringRefusal<'source>>
    {
        let subject = Site {
            at: written,
            name: FormName::IDENTIFIER,
            reading: Reading::Value(frame),
        };
        let spelled = self.name_at(written);
        match self.resolve_name(subject, frame, spelled)? {
            Maybe::Present(Resolved::Binder(bound)) if bound.zone == Zone::Linear => {
                Ok(bound.index)
            },
            Maybe::Present(_) => Err(subject.out(boundary)),
            Maybe::Absent(_) => Err(LoweringRefusal::UnresolvedName {
                span: written.span,
                name: spelled,
            }),
        }
    }

    /// Classify a temporary-access form: `access x as v { t } unwind { u }`,
    /// `resume(v, e)` or `abort(v)`.
    ///
    /// # Specification
    /// - requires: `site` is a temporary-access expression.
    /// - ensures: the form stands as a computation; an access lends the linear
    ///   slot `x` names, binds `v` linearly over its body and reads its unwind,
    ///   when written, under the form's frame, each block's last computation
    ///   its result; an eliminator ends the view its name resolves to, a
    ///   resume's value read as a value under the form's frame.
    /// - fails: the wrong-sort refusal where no computation is read;
    ///   [`FragmentBoundary::Held`] and [`FragmentBoundary::View`] at a name
    ///   that resolves to no linear binder; [`LoweringRefusal::UnresolvedName`]
    ///   for one nothing binds; a misplaced-tile fault for a form out of shape;
    ///   each block's and hole's own refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The form's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the counter's accesses with and without an unwind and
    ///   both eliminators, and each name refused.
    /// - witness: `lower::access::tests::the_counter_lowers_to_its_memory_forms`
    /// - witness: `lower::access::tests::an_access_names_a_held_value_and_an_eliminator_its_view`
    /// - witness: `lower::access::tests::an_exit_inside_an_access_is_refused`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.plans.get(usize::from(site.at.node)), Some(&Plan::Access(_))))]
    pub(super) fn access_form(
        &mut self,
        site: Site,
        pieces: &Pieces,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::Computation)?;
        let mut cursor = Cursor::new(&pieces.pieces, site.at.span);
        let Maybe::Present(Piece::Tile { label: keyword, .. }) = cursor.read()
        else {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        };
        let accessed = if keyword == TileName::ACCESS {
            self.access(site, pieces, frame)?
        }
        else {
            closed(site, &mut cursor, TileName::PAREN_OPEN)?;
            let Maybe::Present(written) = cursor.tile(TileName::IDENTIFIER)
            else {
                return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
            };
            if keyword == TileName::RESUME {
                closed(site, &mut cursor, TileName::COMMA)?;
                let value = site.one(cursor.operands())?;
                closed(site, &mut cursor, TileName::PAREN_CLOSE)?;
                exhausted(site, &cursor)?;
                let view = self.linear_slot(frame, written, FragmentBoundary::View)?;
                self.read(value.node, Reading::Value(frame));
                Accessed::Resume {
                    view,
                    value: value.node,
                }
            }
            else if keyword == TileName::ABORT {
                closed(site, &mut cursor, TileName::PAREN_CLOSE)?;
                exhausted(site, &cursor)?;
                Accessed::Abort {
                    view: self.linear_slot(frame, written, FragmentBoundary::View)?,
                }
            }
            else {
                return Err(site.fault(site.at.span, FormFault::MisplacedTile));
            }
        };
        self.plan(site, Plan::Access(accessed));

        Ok(())
    }

    /// Read an access, `access x as v { t } unwind { u }`, at `site` under
    /// `frame`.
    ///
    /// # Specification
    /// - requires: `pieces` are the access's own, from its `access` tile.
    /// - ensures: the slot `x` names, resolved under `frame`; `t` read as a
    ///   block under `v`'s linear binder over `frame`, and `u`, when written,
    ///   as a block under `frame`, each block's last computation its result.
    /// - fails: as [`Self::access_form`].
    /// - panics: none.
    ///
    /// # Errors
    /// The access's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::access_form`].
    /// - witness: `lower::access::tests::the_counter_lowers_to_its_memory_forms`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |accessed| matches!(*accessed, Accessed::Access { body, .. } if self.results.contains(&body.last))))]
    fn access(
        &mut self,
        site: Site,
        pieces: &Pieces,
        frame: Frame,
    ) -> Result<Accessed, LoweringRefusal<'source>>
    {
        let split = pieces
            .pieces
            .iter()
            .position(
                |piece| matches!(*piece, Piece::Tile { label, .. } if label == TileName::UNWIND),
            )
            .unwrap_or(pieces.pieces.len());
        let Some((head, tail)) = pieces.pieces.split_at_checked(split)
        else {
            return Err(site.fault(site.at.span, FormFault::MisplacedTile));
        };
        let mut cursor = Cursor::new(head, site.at.span);
        closed(site, &mut cursor, TileName::ACCESS)?;
        let Maybe::Present(lent) = cursor.tile(TileName::IDENTIFIER)
        else {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        };
        closed(site, &mut cursor, TileName::AS)?;
        let Maybe::Present(viewer) = cursor.tile(TileName::IDENTIFIER)
        else {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        };
        let held = self.linear_slot(frame, lent, FragmentBoundary::Held)?;
        let name = self.name_at(viewer);
        self.note_binder(viewer, name)?;
        let viewed = self
            .scope
            .extend_linear(frame, name, Maybe::Present(viewer.span));
        let body = self.block(site, &mut cursor, Frame::Inner(viewed))?;
        let _result = self.results.insert(body.last);
        let unwind = if tail.is_empty() {
            Maybe::Absent(unwound::Absent::Unwritten)
        }
        else {
            let mut cursor = Cursor::new(tail, site.at.span);
            closed(site, &mut cursor, TileName::UNWIND)?;
            let unwind = self.block(site, &mut cursor, frame)?;
            let _result = self.results.insert(unwind.last);
            Maybe::Present(unwind)
        };

        Ok(Accessed::Access { held, body, unwind })
    }

    /// Mint the temporary-access form `accessed` plans.
    ///
    /// # Specification
    /// - requires: every node the plan names is already minted or absent.
    /// - ensures: the memory form over its children's lowered nodes at
    ///   `origin`, an access's blocks minted as blocks and a missing unwind
    ///   minted as `pure unit` at `origin`; the first absence among the
    ///   children otherwise.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the counter's forms, an unwind written and one left
    ///   out.
    /// - witness: `lower::access::tests::the_counter_lowers_to_its_memory_forms`
    #[spec(ensures: |ret| match ret {
        | Maybe::Present(Lowered::Computation(id)) => sink.origins.computation(id) == Maybe::Present(origin),
        | Maybe::Present(_) => false,
        | Maybe::Absent(_) => true,
    })]
    pub(super) fn mint_access(
        &self,
        accessed: Accessed,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let form = match accessed {
            Accessed::Access { held, body, unwind } => {
                let body = match self.mint_block(body, sink) {
                    Maybe::Present(body) => body,
                    Maybe::Absent(reason) => return Maybe::Absent(reason),
                };
                let unwind = match unwind {
                    Maybe::Present(unwind) => match self.mint_block(unwind, sink) {
                        Maybe::Present(unwind) => unwind,
                        Maybe::Absent(reason) => return Maybe::Absent(reason),
                    },
                    Maybe::Absent(unwound::Absent::Unwritten) => {
                        let unit = sink.arena.value_unit();
                        sink.origins.record_value(unit, origin);
                        let returned = sink.arena.computation_return(unit);
                        sink.origins.record_computation(returned, origin);
                        returned
                    },
                };
                MemoryForm::Access { held, body, unwind }
            },
            Accessed::Resume { view, value } => match self.value_at(value) {
                Maybe::Present(value) => MemoryForm::Resume { view, value },
                Maybe::Absent(reason) => return Maybe::Absent(reason),
            },
            Accessed::Abort { view } => MemoryForm::Abort { view },
        };
        let id = sink.arena.computation_memory(form);

        Maybe::Present(sink.computation(id, origin))
    }
}

quenchant_shape::reason_enum! {
    /// Why an access has no unwind block.
    pub mod unwound {
        /// The access holds no `unwind` clause.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No unwind was written; the access unwinds by `pure unit`.
            Unwritten,
        }
    }
}
