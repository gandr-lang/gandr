//! Temporary access in the lowering: the statement that holds a value, the
//! access that lends it to a view in a mode, and the two eliminators that end
//! the view.
//!
//! # A held value and a view are names in the linear zone
//!
//! `var x = e ;` holds the value `e` in the linear slot `x` over the rest of
//! its block, as `fork` binds an endpoint over the rest of its block: the
//! core hold, whose scope is that rest, at grade `ω`. `var[1] x = e ;` holds
//! it at grade one; any other numeral is [`LoweringRefusal::GradedBridge`], as
//! on a thunk type. `access x as v { t }
//! unwind { u }` lends the slot `x` names exclusively and binds the view `v`,
//! linearly, over the body `t`; the unwind `u` reads where the access stands,
//! and a missing unwind is `unwind { pure unit }`. `access exclusive x as v { …
//! }` spells the same mode. `access shared x as v { t }` lends `x` shared: the
//! view ends with the body, so the form takes no unwind, and an `unwind`
//! after it is a misplaced tile. Either mode lends a place of `x` when an
//! index follows it, `access shared x.#[e] as v { t }`: `e` is read as a value
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
use gandr_core_term::Binders;
use gandr_core_term::Value;
use gandr_core_term::Zone;
use gandr_core_term::memory::AccessMode;
use gandr_core_term::memory::HoldGrade;
use gandr_core_term::memory::MemoryForm;
use gandr_core_term::memory::Place;
use gandr_core_term::primitive::Arguments;
use gandr_core_term::primitive::Primitive;
use gandr_core_term::shift_value;
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
use crate::form::Former;
use crate::form::Piece;
use crate::form::Pieces;
use crate::form::Placed;
use crate::form::Run;
use crate::form::TileName;
use crate::origin::Insertion;
use crate::origin::Origin;
use crate::resolve::Frame;
use crate::resolve::ScopeId;
use crate::unbuilt::Unbuilt;

#[cfg(test)]
pub(in crate::lower) mod tests;

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
    /// either of a place `x.#[e]`.
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
    /// The place `self.#[e]` a method answering a view ends in: its receiver
    /// held and lent shared at `e`, the view judged at the element type, and
    /// the index answered.
    Place
    {
        /// The receiver, an intuitionistic index where the place stands.
        receiver: DeBruijnIndex,
        /// The index `e`, read as a value where the place stands.
        index: NodeIndex,
        /// The element type the method's result names, read as a value type
        /// where the place stands.
        element: NodeIndex,
    },
    /// A bare index `s.#[e]` of a held slot: the element at `e`, read through a
    /// shared view of it that answers what it views.
    Element
    {
        /// The held slot lent, a linear index where the index stands.
        held: DeBruijnIndex,
        /// The index `e`, read as a value where the index stands.
        index: NodeIndex,
    },
    /// A place assignment `p = e ;`, or `p += e ;` with the operator's row:
    /// `e`'s value bound first, then the place lent exclusively and written
    /// that value, or the row over the view and that value.
    Assign
    {
        /// The held slot written, a linear index where the statement stands.
        held: DeBruijnIndex,
        /// The place of the held value written, its index read where the
        /// statement stands.
        place: Place<NodeIndex>,
        /// The right side, read as a value where the statement stands.
        value: NodeIndex,
        /// The row a compound assignment applies to the view and the right
        /// side's value.
        combined: Maybe<Primitive, assigned::Absent>,
    },
}

/// A place assignment a block read, by its place's node.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `operator` is the assignment's tile, `=`, `+=`, `-=` or `*=`;
///   `value` is read as a value where the statement stands.
/// - executable: none — the record names nodes the classification reads.
///
/// # Adequacy
/// - hypothesis: L3 — a plain and a compound assignment each lower to the
///   access they write.
/// - witness: `lower::access::tests::a_place_assignment_writes_through_an_exclusive_view`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct Assignment
{
    /// The operator tile written after the place.
    operator: TileName,
    /// The right side.
    value: NodeIndex,
}

/// The tiles that write a place after it: `=`, `+=`, `-=` and `*=`.
pub(super) const ASSIGNING: [TileName; 4] = [
    TileName::EQUALS,
    TileName::PLUS_EQUALS,
    TileName::MINUS_EQUALS,
    TileName::TIMES_EQUALS,
];

impl<'source> Lowerer<'_, 'source>
{
    /// Read one `var x = e ;` or `var[g] x = e ;` statement, its keyword tile
    /// already read; `hold` is read as `var` until the corpus moves.
    ///
    /// # Specification
    /// - requires: `cursor` stands just past the statement's tile `var` or
    ///   `hold`; `frame` is the frame the statement reads under.
    /// - ensures: the grade is read when a bracket follows the keyword, `ω`
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
    ) -> Result<(DeBruijnIndex, ScopeId), LoweringRefusal<'source>>
    {
        let subject = Site {
            at: written,
            name: FormName::IDENTIFIER,
            reading: Reading::Value(frame),
        };
        let spelled = self.name_at(written);
        match self.resolve_name(subject, frame, spelled)? {
            Maybe::Present(Resolved::Binder(bound)) if bound.zone == Zone::Linear => {
                Ok((bound.index, bound.binder))
            },
            Maybe::Present(_) => Err(subject.out(boundary)),
            Maybe::Absent(_) => Err(LoweringRefusal::UnresolvedName {
                span: written.span,
                name: spelled,
            }),
        }
    }

    /// Classify a temporary-access form: `access x as v { t } unwind { u }`,
    /// `resume(v, e)`, `abort(v)` or a call's view block `e as v { t }`.
    ///
    /// # Specification
    /// - requires: `site` is a temporary-access expression.
    /// - ensures: the form stands as a computation; an access lends the linear
    ///   slot `x` names, binds `v` linearly over its body and reads its unwind,
    ///   when written, under the form's frame, each block's last computation
    ///   its result; an eliminator ends the view its name resolves to, a
    ///   resume's value read as a value under the form's frame, and the view's
    ///   binder is recorded as one a block ends; a view block stands as its
    ///   call, as [`Self::view_call`] plans it.
    /// - fails: the wrong-sort refusal where no computation is read;
    ///   [`FragmentBoundary::Held`] and [`FragmentBoundary::View`] at a name
    ///   that resolves to no linear binder; [`LoweringRefusal::UnresolvedName`]
    ///   for one nothing binds; a misplaced-tile fault for a form out of shape;
    ///   each block's and hole's own refusal; the view block's refusals.
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
    /// - witness: `lower::method::tests::a_view_block_lends_at_the_mode_it_asks`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.plans.get(site.at.node), Some(&(Plan::Access(_) | Plan::Method(_)))))]
    pub(super) fn access_form(
        &mut self,
        site: Site,
        pieces: &Pieces,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let mut cursor = Cursor::new(&pieces.pieces, site.at.span);
        if super::method::indexed(pieces).is_some() {
            return self.index_form(site, cursor);
        }
        if let Maybe::Present(Piece::Operand(_)) = cursor.peek() {
            return self.view_call(site, pieces);
        }
        let frame = self.require(site, Produced::Computation)?;
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
                let (view, ended) = self.linear_slot(frame, written, FragmentBoundary::View)?;
                let _first = self.ended_views.insert(ended);
                self.read(value.node, Reading::Value(frame));
                Accessed::Resume {
                    view,
                    value: value.node,
                }
            }
            else if keyword == TileName::ABORT {
                closed(site, &mut cursor, TileName::PAREN_CLOSE)?;
                exhausted(site, &cursor)?;
                let (view, ended) = self.linear_slot(frame, written, FragmentBoundary::View)?;
                let _first = self.ended_views.insert(ended);
                Accessed::Abort { view }
            }
            else {
                return Err(site.fault(site.at.span, FormFault::MisplacedTile));
            }
        };
        self.plan(site, Plan::Access(accessed));

        Ok(())
    }

    /// Read an access, `access x as v { t } unwind { u }` or
    /// `access shared x as v { t }`, either of a place `x.#[e]`, at `site`
    /// under `frame`.
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
        let opened = match cursor.tile(TileName::SELECT_OPEN) {
            Maybe::Present(at) => Maybe::Present(at),
            Maybe::Absent(_) => cursor.tile(TileName::BRACKET_OPEN),
        };
        let place = match opened {
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
        let (held, _) = self.linear_slot(frame, lent, FragmentBoundary::Held)?;
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

    /// Read a place assignment's operator and right side after its place,
    /// `run`, in the block `site` reads under `frame`.
    ///
    /// # Specification
    /// - requires: `cursor` stands at the assignment's operator tile, just past
    ///   the place `run`.
    /// - ensures: the place is one operand, recorded as an assignment of the
    ///   operator and the right side, which reads as a value under `frame`; the
    ///   cursor stands past the right side.
    /// - fails: the block's fault for a place or a right side that is not one
    ///   operand.
    /// - panics: none.
    ///
    /// # Errors
    /// The statement's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a plain and a compound assignment each lower to the
    ///   access they write.
    /// - witness: `lower::access::tests::a_place_assignment_writes_through_an_exclusive_view`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |place| self.assignments.contains_key(&place.node)))]
    pub(super) fn assignment(
        &mut self,
        site: Site,
        cursor: &mut Cursor<'_>,
        run: Run,
        frame: Frame,
    ) -> Result<Placed, LoweringRefusal<'source>>
    {
        let place = site.one(run)?;
        let Maybe::Present(Piece::Tile {
            label: operator, ..
        }) = cursor.read()
        else {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        };
        let value = site.one(cursor.operands())?;
        self.read(value.node, Reading::Value(frame));
        let _first = self.assignments.insert(place.node, Assignment {
            operator,
            value: value.node,
        });

        Ok(place)
    }

    /// Classify the place assignment whose place stands at `site`: the place a
    /// held slot's name, or an index of one, and `assignment` its operator and
    /// right side.
    ///
    /// # Specification
    /// - requires: `site` is the place a block read an assignment at; `pieces`
    ///   are its own.
    /// - ensures: the place stands as a computation, planned as the exclusive
    ///   access that writes the slot at the place, the index of an indexed
    ///   place read as a value under the statement's frame, and a compound
    ///   operator's row found by its spelling without the `=`; the head's name
    ///   keeps the slot it names.
    /// - fails: [`FragmentBoundary::Held`] at a place that is neither a name
    ///   nor an index of one, and at a name that resolves to no held slot;
    ///   [`LoweringRefusal::UnresolvedName`] for a name nothing binds;
    ///   [`FragmentBoundary::Unadmitted`] for an operator no row spells.
    /// - panics: none.
    ///
    /// # Errors
    /// The assignment's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a held name and a held list's index written plainly
    ///   and by a compound operator, and a parameter written, refused at its
    ///   name.
    /// - witness: `lower::access::tests::a_place_assignment_writes_through_an_exclusive_view`
    /// - witness: `lower::access::tests::an_assignment_writes_only_a_held_place`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.plans.get(site.at.node), Some(&Plan::Access(Accessed::Assign { .. }))))]
    pub(super) fn assign(
        &mut self,
        site: Site,
        former: Former,
        pieces: &Pieces,
        assignment: Assignment,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        use gandr_core_term::primitive::Operator;
        use gandr_core_term::primitive::PRELUDE;
        let frame = self.require(site, Produced::Computation)?;
        let (head, place) = match (former, pieces.pieces.as_slice()) {
            (Former::Name, _) => (site.at, Place::Whole),
            (
                Former::Access,
                &[
                    Piece::Operand(head),
                    Piece::Tile { label: opener, .. },
                    Piece::Operand(index),
                    Piece::Tile {
                        label: TileName::BRACKET_CLOSE,
                        ..
                    },
                ],
            ) if (opener == TileName::SELECT_OPEN || opener == TileName::BRACKET_OPEN)
                && matches!(self.form_at(head)?, Some((_, Former::Name))) =>
            {
                self.read(index.node, Reading::Value(frame));
                (head, Place::At { index: index.node })
            },
            _ => return Err(site.out(FragmentBoundary::Held)),
        };
        let (held, binder) = self.linear_slot(frame, head, FragmentBoundary::Held)?;
        if !self.held.contains(&binder) {
            let named = Site {
                at: head,
                name: FormName::IDENTIFIER,
                reading: Reading::Value(frame),
            };
            return Err(named.out(FragmentBoundary::Held));
        }
        let combined = if assignment.operator == TileName::EQUALS {
            Maybe::Absent(assigned::Absent::Plain)
        }
        else {
            let spelled = assignment.operator.as_ref().strip_suffix('=');
            let Some(&row) = PRELUDE.iter().find(|primitive| {
                matches!(primitive.operator(), Operator::Infix(spelling) if Some(spelling) == spelled)
            })
            else {
                return Err(site.out(FragmentBoundary::Unadmitted(Unbuilt::InfixForm)));
            };
            Maybe::Present(row)
        };
        self.plan(
            site,
            Plan::Access(Accessed::Assign {
                held,
                place,
                value: assignment.value,
                combined,
            }),
        );

        Ok(())
    }

    /// Mint the temporary-access form `accessed` plans.
    ///
    /// # Specification
    /// - requires: every node the plan names is already minted or absent.
    /// - ensures: the memory form over its children's lowered nodes at
    ///   `origin`, an access's blocks minted as blocks, its index as a value,
    ///   and an exclusive access's missing unwind minted as `pure unit` at
    ///   `origin`; a method's place `self.#[e]` minted as `hold p = self ;
    ///   access shared p.#[e] as v { run _ : a <- pure v ; pure e }`, `a` the
    ///   element type, every node below the hold marked as inserted for the
    ///   method; a held slot's element `s.#[e]` minted as `access shared s.#[e]
    ///   as v { pure v }`, its body marked as inserted for the read; the first
    ///   absence among the children otherwise.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the counter's forms, an unwind written and one left
    ///   out, a shared access with none, a method's place and a held slot's
    ///   element.
    /// - witness: `lower::access::tests::the_counter_lowers_to_its_memory_forms`
    /// - witness: `lower::method::tests::a_view_method_answers_its_place_index`
    /// - witness: `lower::method::tests::a_bare_index_reads_its_held_element`
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
            Accessed::Place {
                receiver,
                index,
                element,
            } => {
                let (index, element) = match (self.value_at(index), self.value_type_at(element)) {
                    (Maybe::Present(index), Maybe::Present(element)) => (index, element),
                    (Maybe::Absent(reason), _) | (_, Maybe::Absent(reason)) => {
                        return Maybe::Absent(reason);
                    },
                };
                let inner = origin.inserted(Insertion::Method);
                let viewed = sink
                    .arena
                    .value_variable(Zone::Linear, DeBruijnIndex::from(0_u32));
                sink.origins.record_value(viewed, inner);
                let read = sink.arena.computation_return(viewed);
                sink.origins.record_computation(read, inner);
                let judged = sink.arena.comp_type_returner(element);
                sink.origins.record_comp_type(judged, inner);
                let ascribed = sink.arena.computation_ascribe(read, judged);
                sink.origins.record_computation(ascribed, inner);
                // Past the ascription's binder the index's free variables are
                // one deeper.
                let answered =
                    shift_value(sink.arena, index, Binders::from(1_u32)).settle(sink.arena);
                if answered != index {
                    sink.origins.record_value(answered, inner);
                }
                let answer = sink.arena.computation_return(answered);
                sink.origins.record_computation(answer, inner);
                let body = sink.arena.computation_bind(ascribed, answer);
                sink.origins.record_computation(body, inner);
                let lent = sink.arena.computation_memory(MemoryForm::Access {
                    mode: AccessMode::Shared,
                    held: DeBruijnIndex::from(0_u32),
                    place: Place::At { index },
                    body,
                });
                sink.origins.record_computation(lent, inner);
                let receiver = sink.arena.value_variable(Zone::Intuitionistic, receiver);
                sink.origins.record_value(receiver, inner);
                MemoryForm::Hold {
                    value: receiver,
                    body: lent,
                    grade: HoldGrade::Many,
                }
            },
            Accessed::Element { held, index } => {
                let index = match self.value_at(index) {
                    Maybe::Present(index) => index,
                    Maybe::Absent(reason) => return Maybe::Absent(reason),
                };
                let inner = origin.inserted(Insertion::Method);
                let viewed = sink
                    .arena
                    .value_variable(Zone::Linear, DeBruijnIndex::from(0_u32));
                sink.origins.record_value(viewed, inner);
                let body = sink.arena.computation_return(viewed);
                sink.origins.record_computation(body, inner);
                MemoryForm::Access {
                    mode: AccessMode::Shared,
                    held,
                    place: Place::At { index },
                    body,
                }
            },
            Accessed::Assign {
                held,
                place,
                value,
                combined,
            } => return self.mint_assign((held, place), (value, combined), sink, origin),
        };
        let id = sink.arena.computation_memory(form);

        Maybe::Present(sink.computation(id, origin))
    }

    /// Mint the place assignment of `value` to the slot `held` at `place`:
    /// `run t <- pure e ; access x as v { resume(v, t) }`, or with a row `op`,
    /// `run t <- pure e ; access x as v { run w <- op(v, t) ; resume(v, w) }`;
    /// a computation `e` is bound itself, `run t <- e`.
    ///
    /// # Specification
    /// - requires: the right side and the place's index are minted or absent.
    /// - ensures: the bind of the right side's return, or of the computation a
    ///   nested right side holds, over the exclusive access of the slot at the
    ///   place, its index raised past the bind, whose body resumes the view
    ///   with the right side or with the row's result over the view and the
    ///   right side, and whose unwind is `pure unit`; the bind at `origin`,
    ///   every node below it inserted for the assignment.
    /// - fails: never; the first absence among the parts is answered.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a plain and a compound assignment of a name and of an
    ///   index, each asserted as the access it mints and judged.
    /// - witness: `lower::access::tests::a_place_assignment_writes_through_an_exclusive_view`
    #[spec(ensures: |ret| match ret {
        | Maybe::Present(Lowered::Computation(id)) => sink.origins.computation(id) == Maybe::Present(origin),
        | Maybe::Present(_) => false,
        | Maybe::Absent(_) => true,
    })]
    fn mint_assign(
        &self,
        (held, place): (DeBruijnIndex, Place<NodeIndex>),
        (value, combined): (NodeIndex, Maybe<Primitive, assigned::Absent>),
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let value = match self.value_at(value) {
            Maybe::Present(value) => value,
            Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        let inner = origin.inserted(Insertion::Assignment);
        let place = match place {
            Place::Whole => Place::Whole,
            Place::At { index } => match self.value_at(index) {
                Maybe::Present(index) => {
                    // Past the right side's binder the index's free variables
                    // are one deeper.
                    let raised =
                        shift_value(sink.arena, index, Binders::from(1_u32)).settle(sink.arena);
                    if raised != index {
                        sink.origins.record_value(raised, inner);
                    }
                    Place::At { index: raised }
                },
                Maybe::Absent(reason) => return Maybe::Absent(reason),
            },
        };
        let view = DeBruijnIndex::from(0_u32);
        let right = sink
            .arena
            .value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        sink.origins.record_value(right, inner);
        let body = match combined {
            Maybe::Present(row) => {
                let viewed = sink.arena.value_variable(Zone::Linear, view);
                sink.origins.record_value(viewed, inner);
                let call = sink
                    .arena
                    .computation_primitive(row, Arguments::Binary([viewed, right]));
                sink.origins.record_computation(call, inner);
                let written = sink
                    .arena
                    .value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
                sink.origins.record_value(written, inner);
                let resumed = sink.arena.computation_memory(MemoryForm::Resume {
                    view,
                    value: written,
                });
                sink.origins.record_computation(resumed, inner);
                let body = sink.arena.computation_bind(call, resumed);
                sink.origins.record_computation(body, inner);
                body
            },
            Maybe::Absent(assigned::Absent::Plain) => {
                let resumed = sink
                    .arena
                    .computation_memory(MemoryForm::Resume { view, value: right });
                sink.origins.record_computation(resumed, inner);
                resumed
            },
        };
        let unit = sink.arena.value_unit();
        sink.origins.record_value(unit, inner);
        let unwind = sink.arena.computation_return(unit);
        sink.origins.record_computation(unwind, inner);
        let lent = sink.arena.computation_memory(MemoryForm::Access {
            mode: AccessMode::Exclusive { unwind },
            held,
            place,
            body,
        });
        sink.origins.record_computation(lent, inner);
        // A computation written as the right side has no type to decide its
        // nesting by; it runs once, before the access, as a `let` runs it.
        let returned = if let Some(&Value::Nested(nested)) = sink.arena.value(value) {
            nested
        }
        else {
            let returned = sink.arena.computation_return(value);
            sink.origins.record_computation(returned, inner);
            returned
        };
        let id = sink.arena.computation_bind(returned, lent);

        Maybe::Present(sink.computation(id, origin))
    }
}

quenchant_shape::reason_enum! {
    /// Why an assignment applies no operator's row.
    pub mod assigned {
        /// The assignment is written `=`.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The place is written the right side's value itself.
            Plain,
        }
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
