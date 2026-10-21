//! Temporary access in the lowering: the statement that holds a value, the
//! access that lends it to a view in a mode, and the two eliminators that end
//! the view.
//!
//! # A held value and a view are names in the linear zone
//!
//! `hold x = e ;` holds the value `e` in the linear slot `x` over the rest of
//! its block, as `fork` binds an endpoint over the rest of its block: the
//! core hold, whose scope is that rest, at grade `ω`. `hold[1] x = e ;` holds
//! it at grade one; any other numeral is [`LoweringRefusal::GradedBridge`], as
//! on a thunk type. `access x as v { t }
//! unwind { u }` lends the slot `x` names exclusively and binds the view `v`,
//! linearly, over the body `t`; the unwind `u` reads where the access stands,
//! and a missing unwind is `unwind { pure unit }`. `access exclusive x as v { …
//! }` spells the same mode. `access shared x as v { t }` lends `x` shared: the
//! view ends with the body, so the form takes no unwind, and an `unwind`
//! after it is a misplaced tile. Either mode lends a place of `x` when an
//! index follows it, `access shared x[e] as v { t }`: `e` is read as a value
//! where the access stands, and the view is the element of `x` at `e`.
//! `resume(v, e)` and `abort(v)` end the view `v` names, `e` read as a value.
//! Each name a form lends or ends resolves to a linear binder, counted among
//! the linear binders alone as an endpoint is (the `lower::session` module);
//! a name resolving to anything else is refused here,
//! [`FragmentBoundary::Held`] for an access and [`FragmentBoundary::View`]
//! for an eliminator. Which linear binder it is — a held value, a view or an
//! endpoint — whether a view's mode admits an eliminator, and whether the
//! held value has elements an index reads are the checker's to judge. A read
//! of either name elsewhere is a linear variable, which the checker reads as
//! the value the slot holds.
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
//! whose ends an early exit continues is refused as unadmitted, as a fork
//! is: the rest copied under the hold would need its linear indices
//! renumbered past the held slot, which the commuting does not carry.

use anodized::spec;
use gandr_core_term::Zone;
use gandr_core_term::memory::AccessMode;
use gandr_core_term::memory::HoldGrade;
use gandr_core_term::memory::MemoryForm;
use gandr_core_term::memory::Place;
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
    /// `access x as v { t } unwind { u }` or `access shared x as v { t }`,
    /// either of a place `x[e]`.
    Access
    {
        /// The mode the slot is lent in, with an exclusive access's unwind
        /// when one is written.
        mode: AccessMode<Maybe<Block, unwound::Absent>>,
        /// The held slot lent, a linear index where the access stands.
        held: DeBruijnIndex,
        /// The place of the held value lent, its index read where the access
        /// stands.
        place: Place<NodeIndex>,
        /// The body, under the view's linear binder.
        body: Block,
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
    /// Read one `hold x = e ;` or `hold[g] x = e ;` statement, its `hold`
    /// tile already read.
    ///
    /// # Specification
    /// - requires: `cursor` stands just past the statement's tile `hold`;
    ///   `frame` is the frame the statement reads under.
    /// - ensures: the grade is read when a bracket follows `hold`, `ω`
    ///   otherwise; `e` is read as a value under `frame`; the statement is
    ///   recorded as the hold of `e` at the grade over the rest of the block,
    ///   and the frame binding `x` linearly over `frame`, which the rest of the
    ///   block reads under, is returned, its binder recorded as a held slot.
    /// - fails: a fault naming the hold statement for a tile out of shape, the
    ///   grade's refusal, the value hole's own fault and the binder's own
    ///   refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The statement's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the counter holds its count over the rest of its
    ///   block, and both accesses name it past the views between; a hold at
    ///   grade one carries its grade and a hold at grade two is refused at the
    ///   grade.
    /// - witness: `lower::access::tests::the_counter_lowers_to_its_memory_forms`
    /// - witness: `lower::access::tests::a_hold_lowers_at_its_grade`
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
        let grade = match cursor.tile(TileName::BRACKET_OPEN) {
            Maybe::Present(_) => self.hold_grade(statement, cursor)?,
            Maybe::Absent(_) => HoldGrade::Many,
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
            binding: StatementBinding::Held {
                value: value.node,
                grade,
                name: binder.node,
            },
            rest: exits::Rest::Bound,
        });

        let slot = self
            .scope
            .extend_linear(frame, name, Maybe::Present(binder.span));
        let _held = self.held.insert(slot);

        Ok(Frame::Inner(slot))
    }

    /// Read a hold's grade, `[n]`, past its `[`.
    ///
    /// # Specification
    /// - requires: `cursor` stands just past the grade's `[`.
    /// - ensures: `1` is [`HoldGrade::One`], the cursor past the `]`.
    /// - fails: [`LoweringRefusal::GradedBridge`] for any other numeral, at the
    ///   grade; a misplaced-tile fault for a grade out of shape.
    /// - panics: none.
    ///
    /// # Errors
    /// The grade's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `1` and `2`, each asserted as the grade or the exact
    ///   refusal.
    /// - witness: `lower::access::tests::a_hold_lowers_at_its_grade`
    #[spec(
        captures: first = cursor.peek(),
        ensures: |ret| match ret {
            | Ok(HoldGrade::One) => matches!(first, Maybe::Present(Piece::Tile { label: TileName::NUMBER, .. })),
            | Ok(HoldGrade::Many) => false,
            | Err(_) => true,
        },
    )]
    fn hold_grade(
        &self,
        site: Site,
        cursor: &mut Cursor<'_>,
    ) -> Result<HoldGrade, LoweringRefusal<'source>>
    {
        let Maybe::Present(Piece::Tile { label, at }) = cursor.read()
        else {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        };
        if label != TileName::NUMBER {
            return Err(site.fault(at.span, FormFault::MisplacedTile));
        }
        if self.name_at(at).as_ref() != "1" {
            return Err(LoweringRefusal::GradedBridge {
                span: at.span,
                grade: self.name_at(at),
            });
        }
        closed(site, cursor, TileName::BRACKET_CLOSE)?;

        Ok(HoldGrade::One)
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

    /// Read an access, `access x as v { t } unwind { u }` or
    /// `access shared x as v { t }`, either of a place `x[e]`, at `site` under
    /// `frame`.
    ///
    /// # Specification
    /// - requires: `pieces` are the access's own, from its `access` tile.
    /// - ensures: the mode the word after `access` names, exclusive when none
    ///   is written; the slot `x` names, resolved under `frame`; the index `e`,
    ///   when written, read as a value under `frame`; `t` read as a block under
    ///   `v`'s linear binder over `frame`, and an exclusive access's `u`, when
    ///   written, as a block under `frame`, each block's last computation its
    ///   result.
    /// - fails: as [`Self::access_form`]; a misplaced-tile fault at the
    ///   `unwind` of a shared access.
    /// - panics: none.
    ///
    /// # Errors
    /// The access's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::access_form`], and an access of a place
    ///   reads its index.
    /// - witness: `lower::access::tests::the_counter_lowers_to_its_memory_forms`
    /// - witness: `lower::access::tests::a_shared_access_lowers_without_an_unwind`
    /// - witness: `lower::access::tests::an_access_of_a_place_lowers_with_its_index`
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
        let mode = match cursor.tile(TileName::SHARED) {
            Maybe::Present(_) => AccessMode::Shared,
            Maybe::Absent(_) => {
                let _written = cursor.tile(TileName::EXCLUSIVE);
                AccessMode::Exclusive { unwind: () }
            },
        };
        let Maybe::Present(lent) = cursor.tile(TileName::IDENTIFIER)
        else {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        };
        let place = match cursor.tile(TileName::BRACKET_OPEN) {
            Maybe::Present(_) => {
                let index = site.one(cursor.operands())?;
                closed(site, &mut cursor, TileName::BRACKET_CLOSE)?;
                self.read(index.node, Reading::Value(frame));
                Place::At { index: index.node }
            },
            Maybe::Absent(_) => Place::Whole,
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
        let mut cursor = Cursor::new(tail, site.at.span);
        let mode = match (mode, tail.is_empty()) {
            (AccessMode::Shared, true) => AccessMode::Shared,
            // A shared view ends with its body: nothing aborts it, so there is
            // no unwind to run.
            (AccessMode::Shared, false) => {
                return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
            },
            (AccessMode::Exclusive { .. }, true) => AccessMode::Exclusive {
                unwind: Maybe::Absent(unwound::Absent::Unwritten),
            },
            (AccessMode::Exclusive { .. }, false) => {
                closed(site, &mut cursor, TileName::UNWIND)?;
                let unwind = self.block(site, &mut cursor, frame)?;
                let _result = self.results.insert(unwind.last);
                AccessMode::Exclusive {
                    unwind: Maybe::Present(unwind),
                }
            },
        };

        Ok(Accessed::Access {
            mode,
            held,
            place,
            body,
        })
    }

    /// Mint the temporary-access form `accessed` plans.
    ///
    /// # Specification
    /// - requires: every node the plan names is already minted or absent.
    /// - ensures: the memory form over its children's lowered nodes at
    ///   `origin`, an access's blocks minted as blocks, its index as a value,
    ///   and an exclusive access's missing unwind minted as `pure unit` at
    ///   `origin`; the first absence among the children otherwise.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the counter's forms, an unwind written and one left
    ///   out, and a shared access with none.
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
            Accessed::Access {
                mode,
                held,
                place,
                body,
            } => {
                let place = match place {
                    Place::Whole => Place::Whole,
                    Place::At { index } => match self.value_at(index) {
                        Maybe::Present(index) => Place::At { index },
                        Maybe::Absent(reason) => return Maybe::Absent(reason),
                    },
                };
                let body = match self.mint_block(body, sink) {
                    Maybe::Present(body) => body,
                    Maybe::Absent(reason) => return Maybe::Absent(reason),
                };
                let mode = match mode {
                    AccessMode::Shared => AccessMode::Shared,
                    AccessMode::Exclusive {
                        unwind: Maybe::Present(unwind),
                    } => match self.mint_block(unwind, sink) {
                        Maybe::Present(unwind) => AccessMode::Exclusive { unwind },
                        Maybe::Absent(reason) => return Maybe::Absent(reason),
                    },
                    AccessMode::Exclusive {
                        unwind: Maybe::Absent(unwound::Absent::Unwritten),
                    } => {
                        let unit = sink.arena.value_unit();
                        sink.origins.record_value(unit, origin);
                        let returned = sink.arena.computation_return(unit);
                        sink.origins.record_computation(returned, origin);
                        AccessMode::Exclusive { unwind: returned }
                    },
                };
                MemoryForm::Access {
                    mode,
                    held,
                    place,
                    body,
                }
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
