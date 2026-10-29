//! Method calls in the lowering: a call `s.f(a, …)` whose `f` is a method of
//! a module in scope reads, writes or takes its receiver `s` as the method's
//! receiver mode says, a method that writes its receiver through holds it
//! over its body, and a method whose mode is deduced answers a place of its
//! receiver that each call lends at the mode its block asks.
//!
//! # A call is the access its receiver lends
//!
//! A method is a module member whose first parameter is `self`, written with
//! its type, at the mode [`ReceiverMode`] names. A call `s.f(a)` resolves `f`
//! among the methods of every module whose path `M.f` the call's source
//! names; a name two of them declare is [`LoweringRefusal::AmbiguousMethod`],
//! and a name none declares is no method call. A receiver held in a slot
//! lowers as the access its mode lends:
//!
//! | mode | `s.f(a)` lowers to |
//! |---|---|
//! | `self : shared T` | `access shared s as v { f(v, a) }` |
//! | `self : T` | `access s as v { (t, r) <- f(v, a) ; resume(v, t) ; pure r }` |
//! | `self : consumed T` | `x <- consume(s) ; f(x, a)` |
//!
//! A receiver that is no held slot is passed as the first argument when the
//! method reads or takes it, and refused as [`FragmentBoundary::Held`] when
//! the method writes it, since nothing holds what it would write back. The
//! arguments read where the call stands, under the view or the taken value
//! the form binds.
//!
//! # A written-through body returns what it wrote
//!
//! A method whose receiver is written through holds the receiver over its
//! body under the name `self`, so the body reads and lends it as a held slot,
//! and returns the slot's last value beside its answer: the body `b` of `def
//! f(self : T, …) -> -F R` lowers as `hold self = self ; r <- b ; pure (self,
//! r)`, and its declared result is `-F (T, R)`. Every exit of `b` ends `b`
//! inside the hold, so its value is the answer paired.
//!
//! # A deduced mode lends the place the method answers
//!
//! A method whose receiver is written at a mode its telescope binds, `def
//! f @[m : Mode] (self : m T, …) -> -F View[m](a) { self[e] }`, answers the
//! place `self[e]` of its receiver: never a value, and never a lens. It lowers
//! to the function answering the place's index, which lends its receiver's
//! place shared to judge the element there at `a`: `hold p = self ; access
//! shared p[e] as v { run _ : a <- pure v ; pure e }`, declared `-F Integer`.
//! Its body is that place alone; any other body, or a result other than
//! `-F View[m](a)` over the receiver's own mode, is
//! [`LoweringRefusal::ViewNotPlace`]. A call lends the place of a held
//! receiver at that index, the index computed reading the receiver shared:
//!
//! | call | lowers to |
//! |---|---|
//! | `s.f(a) as w { b }` | `i <- access shared s as v { f(v, a) } ; access[m] s[i] as w { b }` |
//! | `s.f(a)` | `i <- access shared s as v { f(v, a) } ; access shared s[i] as w { pure w }` |
//!
//! where `m` is exclusive when `b` ends `w` by `resume` or `abort` and shared
//! otherwise; an exclusive lend unwinds by `pure unit`. A receiver that is
//! no held slot has no place to lend, [`FragmentBoundary::Held`], and a block
//! after a call of any other method is [`LoweringRefusal::ViewOfNoPlace`].

use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Binders;
use gandr_core_term::CompType;
use gandr_core_term::CompTypeId;
use gandr_core_term::ComponentCount;
use gandr_core_term::ComputationId;
use gandr_core_term::ValueId;
use gandr_core_term::Zone;
use gandr_core_term::memory::AccessMode;
use gandr_core_term::memory::HoldGrade;
use gandr_core_term::memory::MemoryForm;
use gandr_core_term::memory::Place;
use gandr_core_term::shift_value_type;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_surface_syntax::NodeIndex;
use quenchant_shape::shape::Maybe;

use super::Block;
use super::Lowered;
use super::Lowerer;
use super::Parameter;
use super::Plan;
use super::Produced;
use super::Reading;
use super::Resolved;
use super::Sink;
use super::Site;
use super::Stretch;
use super::arguments;
use super::arity::Planned;
use super::closed;
use super::lowered;
use super::stretch;
use crate::CandidateCount;
use crate::SurfaceName;
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
use crate::form::read_pieces;
use crate::import::ImportResolution;
use crate::module::Container;
use crate::module::ReceiverMode;
use crate::module::SlotIndex;
use crate::module::Visibility;
use crate::namespace::NamePath;
use crate::namespace::PathResolution;
use crate::namespace::Recognized;
use crate::namespace::Segment;
use crate::origin::Insertion;
use crate::origin::Origin;
use crate::resolve::Bound;
use crate::resolve::Frame;
use crate::resolve::ScopeId;
use crate::resolve::binder_site;
use crate::unbuilt::Unbuilt;
use crate::unit::ImportTarget;
use crate::unit::SourceIndex;

#[cfg(test)]
mod tests;

/// What a method call does with its receiver.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: each held slot is a linear index where the call stands.
/// - executable: none — the plan holds no scope to resolve its indices in.
///
/// # Adequacy
/// - hypothesis: L3 — a call at each mode on a held receiver, and on one that
///   is not held.
/// - witness: `lower::method::tests::each_mode_lowers_to_its_access`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) enum Receiving
{
    /// The held slot read through a shared view.
    Read
    {
        /// The slot, a linear index.
        held: DeBruijnIndex,
    },
    /// The held slot written through an exclusive view.
    Written
    {
        /// The slot, a linear index.
        held: DeBruijnIndex,
    },
    /// The held slot taken, ending its hold.
    Taken
    {
        /// The slot, a linear index.
        held: DeBruijnIndex,
    },
    /// A receiver that is no held slot, read as a value where the call stands
    /// and passed as the first argument.
    Passed,
    /// The held slot's place the method answers, its index read through a
    /// shared view, lent to the call's block or read without one.
    Viewed
    {
        /// The slot, a linear index.
        held: DeBruijnIndex,
        /// The block the place is lent to.
        view: Maybe<ViewBlock, unviewed::Absent>,
    },
}

/// The block a call of a method answering a place lends the place to, `s.f(a)
/// as w { b }`.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `body` reads under `binder`, the view `w`'s linear binder over
///   the index's; `call` is the call `s.f(a)` the block follows.
/// - executable: none — the plan holds no scope.
///
/// # Adequacy
/// - hypothesis: L3 — a block that ends its view and one that reads it.
/// - witness: `lower::method::tests::a_view_block_lends_at_the_mode_it_asks`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct ViewBlock
{
    /// The view's binder, which a `resume` or `abort` in the block ends.
    binder: ScopeId,
    /// The block.
    body: Block,
    /// The call the block follows, whose own application stands there.
    call: NodeIndex,
}

quenchant_shape::reason_enum! {
    /// Why a call of a method answering a place lends it to no block.
    pub mod unviewed {
        /// The call has no block.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The call stands alone, reading its place.
            Read,
        }
    }
}

/// The place a method answering a view ends in, `self[e]`.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `element` is the view's element type `a` of the method's result
///   `-F View[m](a)`, read as a value type past every parameter.
/// - executable: none — the plan holds no scope.
///
/// # Adequacy
/// - hypothesis: L3 — a method answering its receiver's first element.
/// - witness: `lower::method::tests::a_view_method_answers_its_place_index`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[repr(transparent)]
pub(super) struct ViewPlace
{
    /// The view's element type.
    element: NodeIndex,
}

/// A method call, as the classification read it.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the arguments read under the binder the receiving opens: a view's
///   for a read or a write, the taken value's for a take; `head` is the call's
///   head `s.f` and `receiver` its `s`.
/// - executable: none — the plan holds no scope.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Receiving`].
/// - witness: `lower::method::tests::each_mode_lowers_to_its_access`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct Called
{
    /// The method's constant.
    method: ConstantIndex,
    /// What the call does with its receiver.
    receiving: Receiving,
    /// The arguments after the receiver, in the lowerer's operand store.
    arguments: Stretch,
    /// The call's head, `s.f`, which answers with the method.
    head: NodeIndex,
    /// The receiver `s`, which answers with the value the method receives.
    receiver: NodeIndex,
}

/// The receiver a written-through method's body holds.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `position` indexes the function's parameters and `index` is that
///   parameter's intuitionistic index past every parameter.
/// - executable: none — the plan holds no scope.
///
/// # Adequacy
/// - hypothesis: L3 — a written-through method's body and its declared result.
/// - witness: `lower::method::tests::a_written_through_body_returns_its_receiver`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct HeldReceiver
{
    /// The receiver's place among the function's parameters.
    position: usize,
    /// The receiver parameter's intuitionistic index past every parameter.
    index: DeBruijnIndex,
}

quenchant_shape::reason_enum! {
    /// Why a function holds no receiver over its body.
    pub mod unheld {
        /// The function holds no receiver.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The function is no method, or its method reads or takes its
            /// receiver.
            NotWrittenThrough,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why an index's head names no held slot.
    pub mod unlent {
        /// The index's head lends no held slot.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The head is no bare name.
            Unnamed,
            /// The name resolves to nothing, or to a binder that holds no
            /// slot.
            Unheld,
            /// The form is an instantiation whose bracket holds no number: a
            /// claim, never an element.
            Claimed,
        }
    }
}

impl<'source> Lowerer<'_, 'source>
{
    /// The receiver mode of the method the declaration at `site` is, when it
    /// is one.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the mode the collection recorded for the slot owning `site`;
    ///   nothing for a declaration that is no method.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`ReceiverMode`].
    /// - witness: `lower::method::tests::a_receiver_is_a_typed_first_self`
    #[spec(ensures: |ret| ret.is_none() || matches!(self.collected.owner_of(site.at.node), Maybe::Present(_)))]
    pub(super) fn receiver_mode(
        &self,
        site: Site,
    ) -> Option<ReceiverMode>
    {
        match self.collected.owner_of(site.at.node) {
            Maybe::Present(slot) => self.collected.receivers.get(&slot).copied(),
            Maybe::Absent(_) => None,
        }
    }

    /// Refuse a mode word or a mode variable written on a parameter of the
    /// function at `function` that is no receiver.
    ///
    /// # Specification
    /// - requires: `cursor` stands just past the parameter list's `(`;
    ///   `receiver` is the function's receiver mode.
    /// - ensures: `Ok` when every mode word stands on the first parameter of a
    ///   method, named `self`, and every moded type, `m T`, on that of a method
    ///   whose mode is deduced.
    /// - fails: [`LoweringRefusal::StrayReceiverMode`] at the first mode word
    ///   or mode variable that does not; [`LoweringRefusal::UnknownMold`]
    ///   reading a parameter's type.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a mode word on a top-level function's parameter and
    ///   on a method's second parameter, and a mode variable on a top-level
    ///   function's parameter, each refused at the word.
    /// - witness: `lower::method::tests::a_mode_word_off_a_receiver_is_refused`
    #[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(LoweringRefusal::StrayReceiverMode { .. } | LoweringRefusal::UnknownMold { .. })))]
    pub(super) fn stray_modes(
        &self,
        cursor: &Cursor<'_>,
        receiver: Option<ReceiverMode>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let mut ahead = cursor.clone();
        let mut position = 0_usize;
        let mut named = SurfaceName::from("");
        let mut after_colon = false;
        while let Maybe::Present(piece) = ahead.read() {
            let receiving = position == 0_usize && named.as_ref() == "self";
            let stray = match piece {
                Piece::Tile { label, .. } if label == TileName::PAREN_CLOSE => break,
                Piece::Tile { label, at } if label == TileName::IDENTIFIER && !after_colon => {
                    named = self.name_at(at);
                    None
                },
                Piece::Tile { label, .. } if label == TileName::COLON => {
                    after_colon = true;
                    None
                },
                Piece::Tile { label, at }
                    if after_colon
                        && (label == TileName::SHARED || label == TileName::CONSUMED) =>
                {
                    let receives =
                        receiving && receiver.is_some_and(|mode| mode != ReceiverMode::Deduced);
                    (!receives).then_some(at)
                },
                Piece::Operand(declared) if after_colon => match self.moded(declared)? {
                    Some((written, _)) => {
                        let receives = receiving && receiver == Some(ReceiverMode::Deduced);
                        (!receives).then_some(written)
                    },
                    None => None,
                },
                Piece::Tile { label, .. } if label == TileName::COMMA => {
                    position = position.saturating_add(1_usize);
                    after_colon = false;
                    None
                },
                Piece::Tile { .. } | Piece::Operand(_) => None,
            };
            if let Some(at) = stray {
                return Err(LoweringRefusal::StrayReceiverMode {
                    span: at.span,
                    mode: self.name_at(at),
                });
            }
        }

        Ok(())
    }

    /// The mode variable and the type a moded type `m T` at `declared` writes,
    /// when `declared` is one.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the variable's tile and the type after it for a moded type;
    ///   nothing for any other form.
    /// - fails: [`LoweringRefusal::UnknownMold`] reading the form.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a receiver at a mode variable, and a parameter whose
    ///   type is a type variable alone, `x : t`.
    /// - witness: `lower::method::tests::a_deduced_mode_is_erased_from_the_telescope`
    /// - witness: `lower::method::tests::a_mode_word_off_a_receiver_is_refused`
    #[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(LoweringRefusal::UnknownMold { .. })))]
    pub(super) fn moded(
        &self,
        declared: Placed,
    ) -> Result<Option<(Placed, Placed)>, LoweringRefusal<'source>>
    {
        let Some((_, Former::ModedType)) = self.form_at(declared)?
        else {
            return Ok(None);
        };
        let mut pieces = Pieces::new();
        read_pieces(self.pbg, self.tree, declared.node, &mut pieces)?;

        Ok(match *pieces.pieces.as_slice() {
            [
                Piece::Tile {
                    label: TileName::TYPE_VARIABLE,
                    at: written,
                },
                Piece::Operand(typed),
            ] => Some((written, typed)),
            _ => None,
        })
    }

    /// Refuse a moded type `m T` read as a type: a mode variable stands only
    /// on a method's receiver, whose parameter reads it before its type.
    ///
    /// The refusal marks the whole moded type. A type variable alone is a
    /// type, so the variable becomes a mode only beside the type after it,
    /// and either word may be the mistake: `x wit` for `x with` misspells the
    /// second.
    ///
    /// # Specification
    /// - requires: `cursor` stands at the form's first piece.
    /// - ensures: never `Ok`.
    /// - fails: [`LoweringRefusal::StrayReceiverMode`] over the moded type; a
    ///   misplaced tile when the form opens on none.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a moded type inside a parameter's type and one a
    ///   misspelt `with` leaves in a type, each refused over the whole moded
    ///   type; marking the variable alone misses the second word.
    /// - witness: `lower::method::tests::a_mode_word_off_a_receiver_is_refused`
    /// - witness: `lower::method::tests::a_mode_variable_off_a_receiver_is_refused_over_its_moded_type_3813`
    #[spec(ensures: |ret| ret.is_err())]
    pub(super) fn moded_type(
        &self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let Maybe::Present(written) = cursor.tile(TileName::TYPE_VARIABLE)
        else {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        };

        Err(LoweringRefusal::StrayReceiverMode {
            span: site.at.span,
            mode: self.name_at(written),
        })
    }

    /// Hold the receiver of a written-through method over its body: bind
    /// `self` linearly over `frame`, the frame past every parameter.
    ///
    /// # Specification
    /// - requires: `frame` is the frame past the function's parameters, which
    ///   `parameters` holds in the parameter store.
    /// - ensures: the frame binding `self` linearly over `frame`, recorded as a
    ///   held slot and written where the parameter `self` is, with the
    ///   receiver's place among the parameters and its index past them.
    /// - fails: the name's own refusals; [`FragmentBoundary::Held`] at the
    ///   function when no parameter `self` is bound.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a written-through method's body reads `self` as its
    ///   held slot.
    /// - witness: `lower::method::tests::a_written_through_body_returns_its_receiver`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&(held, _)| matches!(held, Frame::Inner(slot) if self.held.contains(&slot))))]
    pub(super) fn hold_receiver(
        &mut self,
        function: Site,
        frame: Frame,
        parameters: Stretch,
    ) -> Result<(Frame, HeldReceiver), LoweringRefusal<'source>>
    {
        let name = SurfaceName::from("self");
        let found = self.scope.resolve(frame, name, &mut self.fuel)?;
        let parameters = stretch(&self.parameters, parameters);
        let place = match found {
            Maybe::Present(bound) => parameters
                .iter()
                .position(|parameter| parameter.frame == bound.binder)
                .map(|position| (position, bound.index)),
            Maybe::Absent(_) => None,
        };
        let Some((position, index)) = place
        else {
            return Err(function.out(FragmentBoundary::Held));
        };
        let site = match parameters.get(position) {
            Some(parameter) => self.scope.site(parameter.frame),
            None => Maybe::Absent(binder_site::Absent::Unwritten),
        };
        let slot = self.scope.extend_linear(frame, name, site);
        let _held = self.held.insert(slot);

        Ok((Frame::Inner(slot), HeldReceiver { position, index }))
    }

    /// Classify the call at `site` as a method call when its head selects a
    /// method off a name.
    ///
    /// # Specification
    /// - requires: `cursor` stands at the call's head.
    /// - ensures: as [`Self::method_at`] with no view block.
    /// - fails: as [`Self::method_at`].
    /// - panics: none.
    ///
    /// # Errors
    /// The call's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::method_at`].
    /// - witness: `lower::method::tests::each_mode_lowers_to_its_access`
    #[spec(ensures: |ret| !matches!(ret, Ok(Planned(true))) || matches!(self.plans.get(site.at.node), Some(&Plan::Method(_))))]
    pub(super) fn method(
        &mut self,
        site: Site,
        cursor: &Cursor<'_>,
    ) -> Result<Planned, LoweringRefusal<'source>>
    {
        self.method_at(site, cursor, None)
    }

    /// Classify the view block `e as w { b }` at `site`: `e` a call of a
    /// method answering a place, which the block's view lends.
    ///
    /// # Specification
    /// - requires: `site` is a view block and `pieces` its own.
    /// - ensures: the block stands as the call [`Self::method_at`] plans of
    ///   `e`, lending the place to `b` under `w`.
    /// - fails: [`LoweringRefusal::ViewOfNoPlace`] at `e` when it is no call of
    ///   a method, or one of a method answering no place; the call's own
    ///   refusals.
    /// - panics: none.
    ///
    /// # Errors
    /// The block's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a block after a call of a method answering a place,
    ///   and after one of a method that reads its receiver.
    /// - witness: `lower::method::tests::a_view_block_lends_at_the_mode_it_asks`
    /// - witness: `lower::method::tests::a_view_block_after_no_place_is_refused`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.plans.get(site.at.node), Some(&Plan::Method(_))))]
    pub(super) fn view_call(
        &mut self,
        site: Site,
        pieces: &Pieces,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let mut cursor = Cursor::new(&pieces.pieces, site.at.span);
        let call = site.one(cursor.operands())?;
        let refused = LoweringRefusal::ViewOfNoPlace { span: call.span };
        let Some((_, Former::Call)) = self.form_at(call)?
        else {
            return Err(refused);
        };
        let mut called = Pieces::new();
        read_pieces(self.pbg, self.tree, call.node, &mut called)?;
        let head = Cursor::new(&called.pieces, call.span);
        match self.method_at(site, &head, Some((call.node, &mut cursor)))? {
            Planned(true) => Ok(()),
            Planned(false) => Err(refused),
        }
    }

    /// Classify the call `cursor` reads, at `site`, as a method call when its
    /// head selects a method off a name, lending a view block the place a
    /// method answering one answers.
    ///
    /// # Specification
    /// - requires: `cursor` stands at the call's head; `view`, when given,
    ///   names the call's node and stands at the `as` of the view block the
    ///   call heads.
    /// - ensures: a head `s.f` whose `s` is a name a binder or a declaration
    ///   answers and whose `f` one module in scope declares as a method stands
    ///   as a computation, planned as the call its receiver mode makes of a
    ///   receiver held in a slot, or of one passed as a value, as the module
    ///   documentation tabulates; each argument reads as a value under the
    ///   binder that call opens, and a view block's body under its view's
    ///   linear binder over the index's; any other call is left unplanned.
    /// - fails: [`LoweringRefusal::AmbiguousMethod`] at `f` for a method more
    ///   than one module in scope declares; the forward-member refusal for a
    ///   method declared at or after the call's declaration;
    ///   [`LoweringRefusal::ImplicitUnsupplied`] for a method with an implicit
    ///   telescope, which a call off its receiver supplies nothing;
    ///   [`FragmentBoundary::Held`] at `s` for a written-through call, or one
    ///   of a method answering a place, on a receiver that is no held slot;
    ///   [`LoweringRefusal::ViewOfNoPlace`] at `f` for a view block after a
    ///   method answering no place; the wrong-sort refusal where no computation
    ///   is read; the name's, the argument list's and the block's refusals.
    /// - panics: none.
    ///
    /// # Errors
    /// The call's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a call at each mode, a call on a receiver that is not
    ///   held, an ambiguous method, a forward one and one with an implicit
    ///   telescope; a call of a method answering a place with a block and
    ///   without one.
    /// - witness: `lower::method::tests::each_mode_lowers_to_its_access`
    /// - witness: `lower::method::tests::a_receiver_not_held_is_passed_or_refused`
    /// - witness: `lower::method::tests::a_method_two_modules_declare_is_refused_naming_both`
    /// - witness: `lower::method::tests::a_receiver_is_a_typed_first_self`
    /// - witness: `lower::method::tests::a_view_block_lends_at_the_mode_it_asks`
    #[spec(ensures: |ret| !matches!(ret, Ok(Planned(true))) || matches!(self.plans.get(site.at.node), Some(&Plan::Method(_))))]
    fn method_at(
        &mut self,
        site: Site,
        cursor: &Cursor<'_>,
        view: Option<(NodeIndex, &mut Cursor<'_>)>,
    ) -> Result<Planned, LoweringRefusal<'source>>
    {
        let mut ahead = cursor.clone();
        let Run::One(head) = ahead.operands()
        else {
            return Ok(Planned(false));
        };
        let Some((_, Former::Projection)) = self.form_at(head)?
        else {
            return Ok(Planned(false));
        };
        let mut pieces = Pieces::new();
        read_pieces(self.pbg, self.tree, head.node, &mut pieces)?;
        let &[
            Piece::Operand(target),
            Piece::Tile {
                label: TileName::DOT,
                ..
            },
            Piece::Tile {
                label: TileName::IDENTIFIER,
                at: selected,
            },
        ] = pieces.pieces.as_slice()
        else {
            return Ok(Planned(false));
        };
        let Some((_, Former::Name)) = self.form_at(target)?
        else {
            return Ok(Planned(false));
        };
        let method = self.name_at(selected);
        let Container::TopLevel(here) = self.collected.top(selected.span.start())
        else {
            return Ok(Planned(false));
        };
        let candidates = self.methods_named(method, here)?;
        let (slot, mode) = match *candidates.as_slice() {
            [] => return Ok(Planned(false)),
            [(slot, mode, _)] => (slot, mode),
            [(_, _, first), (_, _, second), ref rest @ ..] => {
                return Err(LoweringRefusal::AmbiguousMethod {
                    span: selected.span,
                    method,
                    first,
                    second,
                    more: CandidateCount::from(rest.len()),
                });
            },
        };
        let frame = self.require(site, Produced::Computation)?;
        let receiver = Site {
            at: target,
            name: FormName::IDENTIFIER,
            reading: Reading::Value(frame),
        };
        let resolved = match self.resolve_name(receiver, frame, self.name_at(target))? {
            Maybe::Present(resolved) => resolved,
            Maybe::Absent(_) => return Ok(Planned(false)),
        };
        let Some(entry) = self.collected.slots.get(usize::from(slot))
        else {
            return Err(site.out(FragmentBoundary::Unadmitted(Unbuilt::MethodCall)));
        };
        let (constant, declared) = (entry.constant, entry.named.span);
        if let Maybe::Present(own) = self.collected.owner_of(site.at.node)
            && slot >= own
        {
            return Err(LoweringRefusal::ForwardMemberReference {
                span: selected.span,
                name: method,
                declared,
            });
        }
        self.phased(site, slot)?;
        self.supplied_or_refused(site, constant)?;
        self.resolved(target.span, resolved);
        self.resolved(selected.span, Resolved::Declaration {
            constant,
            declared: Maybe::Absent(crate::resolve::binder_type::Absent::Untyped),
        });
        let held = match resolved {
            Resolved::Binder(bound) if self.held.contains(&bound.binder) => Some(bound.index),
            Resolved::Binder(_) | Resolved::Declaration { .. } => None,
        };
        let unwritten = || Maybe::Absent(binder_site::Absent::Unwritten);
        if view.is_some() && mode != ReceiverMode::Deduced {
            return Err(LoweringRefusal::ViewOfNoPlace {
                span: selected.span,
            });
        }
        let (receiving, inner) = match (mode, held) {
            (ReceiverMode::Shared, Some(held)) => (
                Receiving::Read { held },
                Frame::Inner(
                    self.scope
                        .extend_linear(frame, SurfaceName::from(""), unwritten()),
                ),
            ),
            (ReceiverMode::Exclusive, Some(held)) => (
                Receiving::Written { held },
                Frame::Inner(
                    self.scope
                        .extend_linear(frame, SurfaceName::from(""), unwritten()),
                ),
            ),
            (ReceiverMode::Consumed, Some(held)) => (
                Receiving::Taken { held },
                Frame::Inner(self.scope.extend(frame, SurfaceName::from(""), unwritten())),
            ),
            (ReceiverMode::Deduced, Some(held)) => {
                let view = match view {
                    Some((call, block)) => {
                        closed(site, block, TileName::AS)?;
                        let Maybe::Present(viewer) = block.tile(TileName::IDENTIFIER)
                        else {
                            return Err(site.fault(block.here(), FormFault::MisplacedTile));
                        };
                        let name = self.name_at(viewer);
                        self.note_binder(viewer, name)?;
                        let index = self.scope.extend(frame, SurfaceName::from(""), unwritten());
                        let binder = self.scope.extend_linear(
                            Frame::Inner(index),
                            name,
                            Maybe::Present(viewer.span),
                        );
                        let body = self.block(site, block, Frame::Inner(binder))?;
                        let _result = self.results.insert(body.last);
                        Maybe::Present(ViewBlock { binder, body, call })
                    },
                    None => Maybe::Absent(unviewed::Absent::Read),
                };
                (
                    Receiving::Viewed { held, view },
                    Frame::Inner(self.scope.extend_linear(
                        frame,
                        SurfaceName::from(""),
                        unwritten(),
                    )),
                )
            },
            (ReceiverMode::Shared | ReceiverMode::Consumed, None) => {
                self.read(target.node, Reading::Value(frame));
                (Receiving::Passed, frame)
            },
            (ReceiverMode::Exclusive | ReceiverMode::Deduced, None) => {
                return Err(receiver.out(FragmentBoundary::Held));
            },
        };
        let start = self.operands.len();
        arguments(site, &mut ahead, &mut self.operands)?;
        let written = Stretch {
            start,
            end: self.operands.len(),
        };
        for position in written.start .. written.end {
            if let Some(&argument) = self.operands.get(position) {
                self.read(argument, Reading::Value(inner));
            }
        }

        self.plan(
            site,
            Plan::Method(Called {
                method: constant,
                receiving,
                arguments: written,
                head: head.node,
                receiver: target.node,
            }),
        );

        Ok(Planned(true))
    }

    /// The mode variable written at `written` on the receiver of the method
    /// at `site`, when the method's telescope binds it as a mode.
    ///
    /// # Specification
    /// - requires: `written` is the variable of the receiver's moded type,
    ///   `self : m T`.
    /// - ensures: the name `written` spells.
    /// - fails: [`LoweringRefusal::UnresolvedName`] at `written` when the
    ///   method's telescope binds no mode of that name.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a mode variable its telescope binds, and one it does
    ///   not.
    /// - witness: `lower::method::tests::a_deduced_mode_is_erased_from_the_telescope`
    #[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(LoweringRefusal::UnresolvedName { .. })))]
    pub(super) fn mode_variable(
        &self,
        site: Site,
        written: Placed,
    ) -> Result<SurfaceName<'source>, LoweringRefusal<'source>>
    {
        let name = self.name_at(written);
        let bound = match self.collected.owner_of(site.at.node) {
            Maybe::Present(slot) => self
                .mode_binders
                .get(&slot)
                .is_some_and(|modes| modes.contains(&name)),
            Maybe::Absent(_) => false,
        };
        if !bound {
            return Err(LoweringRefusal::UnresolvedName {
                span: written.span,
                name,
            });
        }

        Ok(name)
    }

    /// The element type `a` of the result `-F View[m](a)`, or `View[m](a)`
    /// with the returner the lowering inserts at a result, a method whose
    /// receiver is at the mode `mode` declares, read as a value type under
    /// `frame`.
    ///
    /// # Specification
    /// - requires: `result` is the method's written result; `frame` is the
    ///   frame past every parameter.
    /// - ensures: the element's node, read as a value type under `frame`, and
    ///   the view type recorded as one a method's result declares.
    /// - fails: [`LoweringRefusal::ViewNotPlace`] at the result when it is
    ///   neither `-F View[m](a)` nor `View[m](a)`, and at its `m` when that
    ///   names a mode other than the receiver's; a fault reading the result's
    ///   pieces.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a method answering its receiver's first element, its
    ///   result written with its returner and without, and one declaring a
    ///   result of another shape.
    /// - witness: `lower::method::tests::a_view_method_answers_its_place_index`
    /// - witness: `lower::method::tests::a_view_method_answering_no_place_is_refused`
    #[spec(ensures: |ret| ret.is_err() || !self.view_types.is_empty())]
    pub(super) fn view_result(
        &mut self,
        result: Placed,
        mode: SurfaceName<'source>,
        frame: Frame,
    ) -> Result<NodeIndex, LoweringRefusal<'source>>
    {
        let refused = LoweringRefusal::ViewNotPlace { span: result.span };
        let mut pieces = Pieces::new();
        let view = match self.form_at(result)? {
            Some((_, Former::StagedType)) => result,
            Some((_, Former::ReturnerType)) => {
                read_pieces(self.pbg, self.tree, result.node, &mut pieces)?;
                let &[Piece::Tile { .. }, Piece::Operand(view)] = pieces.pieces.as_slice()
                else {
                    return Err(refused);
                };
                let Some((_, Former::StagedType)) = self.form_at(view)?
                else {
                    return Err(refused);
                };
                view
            },
            Some(_) | None => return Err(refused),
        };
        read_pieces(self.pbg, self.tree, view.node, &mut pieces)?;
        let &[
            Piece::Operand(head),
            Piece::Tile {
                label: TileName::BRACKET_OPEN,
                ..
            },
            Piece::Tile {
                label: TileName::IDENTIFIER,
                at: written,
            },
            Piece::Tile {
                label: TileName::BRACKET_CLOSE,
                ..
            },
            Piece::Tile {
                label: TileName::PAREN_OPEN,
                ..
            },
            Piece::Operand(element),
            Piece::Tile {
                label: TileName::PAREN_CLOSE,
                ..
            },
        ] = pieces.pieces.as_slice()
        else {
            return Err(refused);
        };
        let viewed = matches!(self.form_at(head)?, Some((_, Former::TypeHead)))
            && self.name_at(head).as_ref() == "View";
        if !viewed {
            return Err(refused);
        }
        if self.name_at(written) != mode {
            return Err(LoweringRefusal::ViewNotPlace { span: written.span });
        }
        let _fresh = self.view_types.insert(view.node);
        self.read(element.node, Reading::ValueType(frame));

        Ok(element.node)
    }

    /// Classify an index `s[e]` at `site`, its pieces under `cursor`.
    ///
    /// # Specification
    /// - requires: `site` is an index; `cursor` stands at its head.
    /// - ensures: the body of a method answering a view stands as its place, as
    ///   [`Self::view_place`] plans it; an index whose head names a held slot
    ///   stands as the element there, as [`Self::element`] plans it.
    /// - fails: [`FragmentBoundary::Unadmitted`] for an index anywhere else;
    ///   the place's and the element's refusals.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a method answering the element at a parameter's
    ///   index, a held list's element at a name, and an index of a list no slot
    ///   holds.
    /// - witness: `lower::method::tests::a_view_method_answers_its_place_index`
    /// - witness: `lower::method::tests::a_view_method_answering_no_place_is_refused`
    /// - witness: `lower::method::tests::a_bare_index_reads_its_held_element`
    #[spec(ensures: |ret| ret.is_err() || self.view_places.contains_key(&site.at.node)
        || matches!(self.plans.get(site.at.node), Some(&Plan::Access(super::access::Accessed::Element { .. }))))]
    pub(super) fn index_form(
        &mut self,
        site: Site,
        cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        if let Some(&place) = self.view_places.get(&site.at.node) {
            return self.view_place(site, cursor, place);
        }
        match self.lent_head(site)? {
            Maybe::Present(lent) => self.element(site, cursor, lent),
            Maybe::Absent(_) => Err(site.out(FragmentBoundary::Unadmitted(Unbuilt::Index))),
        }
    }

    /// The held slot the head of the index or instantiation at `site` names,
    /// as the binder its name resolves to where the form stands.
    ///
    /// # Specification
    /// - requires: `site` is an index `s[e]` or an instantiation `s[0]`.
    /// - ensures: the binder of the innermost name the head spells, when the
    ///   head is a bare name, that binder is a slot a `hold` binds, and an
    ///   instantiation's bracket holds one number; nothing is planned or
    ///   recorded.
    /// - fails: a fault reading the form's pieces or the head's form; the
    ///   resolution's exhausted allowance.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a held list's name at a name and at a number, and a
    ///   parameter's name no slot holds.
    /// - witness: `lower::method::tests::a_bare_index_reads_its_held_element`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |lent| match *lent {
        | Maybe::Present(bound) => self.held.contains(&bound.binder),
        | Maybe::Absent(_) => true,
    }))]
    pub(super) fn lent_head(
        &mut self,
        site: Site,
    ) -> Result<Maybe<Bound, unlent::Absent>, LoweringRefusal<'source>>
    {
        let mut scratch = core::mem::take(&mut self.scratch);
        let read = read_pieces(self.pbg, self.tree, site.at.node, &mut scratch);
        let parts = match *scratch.pieces.as_slice() {
            [Piece::Operand(head), _, Piece::Operand(resident), ..] => {
                Maybe::Present((head, resident))
            },
            _ => Maybe::Absent(unlent::Absent::Unnamed),
        };
        self.scratch = scratch;
        read?;
        let Maybe::Present((head, resident)) = parts
        else {
            return Ok(Maybe::Absent(unlent::Absent::Unnamed));
        };
        if !matches!(self.form_at(head)?, Some((_, Former::Name))) {
            return Ok(Maybe::Absent(unlent::Absent::Unnamed));
        }
        if matches!(self.form_at(site.at)?, Some((_, Former::Instantiation))) {
            let mut pieces = Pieces::new();
            read_pieces(self.pbg, self.tree, resident.node, &mut pieces)?;
            if !matches!(*pieces.pieces.as_slice(), [Piece::Tile {
                label: TileName::NUMBER,
                ..
            }]) {
                return Ok(Maybe::Absent(unlent::Absent::Claimed));
            }
        }
        let name = self.name_at(head);
        match self
            .scope
            .resolve(site.reading.frame(), name, &mut self.fuel)?
        {
            Maybe::Present(bound)
                if bound.zone == Zone::Linear && self.held.contains(&bound.binder) =>
            {
                Ok(Maybe::Present(bound))
            },
            Maybe::Present(_) | Maybe::Absent(_) => Ok(Maybe::Absent(unlent::Absent::Unheld)),
        }
    }

    /// Classify the element `s[e]` at `site` of the held slot `lent` names, its
    /// pieces under `cursor`: a view of the place used without a block, a read
    /// of it.
    ///
    /// # Specification
    /// - requires: `site` is an index `s[e]` or the instantiation a number in
    ///   the bracket molds as, `s[0]`; `lent` is the binder `s` resolves to
    ///   where the form stands, a held slot; `cursor` stands at its head.
    /// - ensures: the form stands as a computation, planned as the access that
    ///   lends the slot shared at `e` and answers what its view sees; `e` reads
    ///   as a value under the form's frame, an instantiation's number planned
    ///   as its literal; the head's name keeps the slot it names.
    /// - fails: the wrong-sort refusal where no computation is read;
    ///   [`FragmentBoundary::Unadmitted`] for a bracket holding anything but
    ///   one index; a malformed-literal refusal for an instantiation's number
    ///   out of shape; a fault naming the form for a tile out of place.
    /// - panics: none.
    ///
    /// # Errors
    /// The element's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a held list read at a name and at a number, each
    ///   asserted as the access it mints.
    /// - witness: `lower::method::tests::a_bare_index_reads_its_held_element`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.plans.get(site.at.node), Some(&Plan::Access(super::access::Accessed::Element { .. }))))]
    pub(super) fn element(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
        lent: Bound,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::Computation)?;
        let indexed = matches!(self.form_at(site.at)?, Some((_, Former::Access)));
        let head = site.one(cursor.operands())?;
        closed(site, &mut cursor, TileName::BRACKET_OPEN)?;
        let resident = site.one(cursor.operands())?;
        if let Maybe::Present(_) = cursor.at(TileName::COMMA) {
            let unbuilt = if indexed {
                Unbuilt::Index
            }
            else {
                Unbuilt::RecursiveClaim
            };
            return Err(site.out(FragmentBoundary::Unadmitted(unbuilt)));
        }
        closed(site, &mut cursor, TileName::BRACKET_CLOSE)?;
        if let Maybe::Present(_) = cursor.peek() {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        }
        self.resolved(head.span, Resolved::Binder(lent));
        if indexed {
            self.read(resident.node, Reading::Value(frame));
        }
        else {
            // A number in the bracket molds as an instantiation's type literal,
            // which no value reading takes: it is planned as its literal here.
            let mut pieces = Pieces::new();
            read_pieces(self.pbg, self.tree, resident.node, &mut pieces)?;
            let &[
                Piece::Tile {
                    label: TileName::NUMBER,
                    at: number,
                },
            ] = pieces.pieces.as_slice()
            else {
                return Err(site.out(FragmentBoundary::Reserved(Unbuilt::RecursiveClaim)));
            };
            let Maybe::Present(literal) =
                super::parse_literal(Former::Number, self.text_at(number))
            else {
                return Err(LoweringRefusal::MalformedLiteral {
                    span: number.span,
                    form: FormName::NUMBER,
                });
            };
            let numbered = Site {
                at: resident,
                name: FormName::NUMBER,
                reading: Reading::Value(frame),
            };
            self.plan(numbered, Plan::Literal(literal));
        }
        self.plan(
            site,
            Plan::Access(super::access::Accessed::Element {
                held: lent.index,
                index: resident.node,
            }),
        );

        Ok(())
    }

    /// Record the body `block` of a method answering a view of element type
    /// `element` as the place it answers.
    ///
    /// # Specification
    /// - requires: `block` is the method's body, read past every parameter.
    /// - ensures: the block's last computation is recorded as the place, with
    ///   `element`.
    /// - fails: [`LoweringRefusal::ViewNotPlace`] at the block's last
    ///   computation when the block has statements before it or it is no place
    ///   `s[e]`; a fault reading its form.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a method answering its receiver's first element, and
    ///   one whose body is a value.
    /// - witness: `lower::method::tests::a_view_method_answers_its_place_index`
    /// - witness: `lower::method::tests::a_view_method_answering_no_place_is_refused`
    #[spec(ensures: |ret| ret.is_err() || self.view_places.get(&block.last) == Some(&ViewPlace { element }))]
    pub(super) fn view_body(
        &mut self,
        function: Site,
        block: Block,
        element: NodeIndex,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let Some(node) = self.tree.node(block.last)
        else {
            return Err(LoweringRefusal::ViewNotPlace {
                span: function.at.span,
            });
        };
        let last = Placed::of(block.last, node);
        let shaped = match self.form_at(last)? {
            Some((_, Former::Instantiation)) => true,
            Some((_, Former::Access)) => {
                let mut pieces = Pieces::new();
                read_pieces(self.pbg, self.tree, last.node, &mut pieces)?;
                indexed(&pieces).is_some()
            },
            _ => false,
        };
        if block.statements.start != block.statements.end || !shaped {
            return Err(LoweringRefusal::ViewNotPlace { span: last.span });
        }
        let _first = self.view_places.insert(block.last, ViewPlace { element });

        Ok(())
    }

    /// Classify the body `self[e]` at `site` of a method answering a view
    /// whose element type `place` names.
    ///
    /// # Specification
    /// - requires: `site` is the place a method answering a view ends in,
    ///   recorded as its place: an index `self[e]`, or the instantiation a
    ///   number in the bracket molds as, `self[0]`; `cursor` stands at its
    ///   head.
    /// - ensures: the place stands as a computation, planned as the receiver
    ///   `self` resolves to, lent shared at `e`, which reads as a value under
    ///   the place's frame; an instantiation's number is planned as its
    ///   literal.
    /// - fails: [`LoweringRefusal::ViewNotPlace`] at the head when it is no
    ///   name `self` of an intuitionistic binder, and at the place when its
    ///   bracket holds anything but one index; a malformed-literal refusal for
    ///   an instantiation's number out of shape; the wrong-sort refusal where
    ///   no computation is read; a fault naming the place for a tile out of
    ///   place.
    /// - panics: none.
    ///
    /// # Errors
    /// The place's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a method answering its receiver's first element, one
    ///   answering the element at a parameter's index, and one answering a
    ///   place of another name.
    /// - witness: `lower::method::tests::a_view_method_answers_its_place_index`
    /// - witness: `lower::method::tests::a_view_method_answering_no_place_is_refused`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.plans.get(site.at.node), Some(&Plan::Access(super::access::Accessed::Place { .. }))))]
    pub(super) fn view_place(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
        place: ViewPlace,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::Computation)?;
        let refused = LoweringRefusal::ViewNotPlace { span: site.at.span };
        let indexed = matches!(self.form_at(site.at)?, Some((_, Former::Access)));
        let head = site.one(cursor.operands())?;
        closed(site, &mut cursor, TileName::BRACKET_OPEN)?;
        let resident = site.one(cursor.operands())?;
        closed(site, &mut cursor, TileName::BRACKET_CLOSE)?;
        if let Maybe::Present(_) = cursor.peek() {
            return Err(refused);
        }
        let named = matches!(self.form_at(head)?, Some((_, Former::Name)))
            && self.name_at(head).as_ref() == "self";
        let receiver = Site {
            at: head,
            name: FormName::IDENTIFIER,
            reading: Reading::Value(frame),
        };
        let resolved = if named {
            self.resolve_name(receiver, frame, self.name_at(head))?
        }
        else {
            return Err(LoweringRefusal::ViewNotPlace { span: head.span });
        };
        let Maybe::Present(Resolved::Binder(bound)) = resolved
        else {
            return Err(LoweringRefusal::ViewNotPlace { span: head.span });
        };
        if bound.zone != Zone::Intuitionistic {
            return Err(LoweringRefusal::ViewNotPlace { span: head.span });
        }
        self.resolved(head.span, Resolved::Binder(bound));
        if indexed {
            self.read(resident.node, Reading::Value(frame));
        }
        else {
            // A number in the bracket molds as an instantiation's type literal,
            // which no value reading takes: it is planned as its literal here.
            let mut pieces = Pieces::new();
            read_pieces(self.pbg, self.tree, resident.node, &mut pieces)?;
            let &[
                Piece::Tile {
                    label: TileName::NUMBER,
                    at: number,
                },
            ] = pieces.pieces.as_slice()
            else {
                return Err(refused);
            };
            let Maybe::Present(literal) =
                super::parse_literal(Former::Number, self.text_at(number))
            else {
                return Err(LoweringRefusal::MalformedLiteral {
                    span: number.span,
                    form: FormName::NUMBER,
                });
            };
            let numbered = Site {
                at: resident,
                name: FormName::NUMBER,
                reading: Reading::Value(frame),
            };
            self.plan(numbered, Plan::Literal(literal));
        }
        self.plan(
            site,
            Plan::Access(super::access::Accessed::Place {
                receiver: bound.index,
                index: resident.node,
                element: place.element,
            }),
        );

        Ok(())
    }

    /// Every method named `method` that a module in scope in the source `here`
    /// declares: its slot, its receiver mode and its module's name, in
    /// collection order.
    ///
    /// # Specification
    /// - requires: `here` is a source of the unit.
    /// - ensures: each method of that name whose module's path, joined with the
    ///   name, resolves to it as an exported component, and whose outermost
    ///   module `here` declares or one of `here`'s imports resolves to and
    ///   exports; a module of a sibling source `here` does not import is out of
    ///   scope, though the unit recognises its path, and so is one an imported
    ///   source keeps private.
    /// - fails: [`LoweringRefusal::BudgetExceeded`] when the walk up a nested
    ///   module's containers runs out of allowance.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a method one module declares, one two modules
    ///   declare, one a sibling source declares that the caller does not
    ///   import, and one of a module an imported source keeps private.
    /// - witness: `lower::method::tests::a_method_two_modules_declare_is_refused_naming_both`
    /// - witness: `tests::namespace::a_method_of_a_source_not_imported_is_out_of_scope`
    /// - witness: `tests::namespace::a_private_declaration_is_refused_to_its_importer_2687`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |found| found.iter().all(|&(slot, mode, _)| self.collected.receivers.get(&slot) == Some(&mode))))]
    fn methods_named(
        &mut self,
        method: SurfaceName<'source>,
        here: SourceIndex,
    ) -> Result<Vec<(SlotIndex, ReceiverMode, SurfaceName<'source>)>, LoweringRefusal<'source>>
    {
        let seen = |collected: &crate::module::Collected<'source>, target: SourceIndex, slot| {
            target == here
                || (collected.slot_visibility(slot) == Visibility::Public
                    && collected.imports.of(here).any(|import| {
                        import.resolution() == ImportResolution::Path(ImportTarget::Source(target))
                    }))
        };
        let mut found = Vec::new();
        let receivers: Vec<(SlotIndex, ReceiverMode)> = self
            .collected
            .receivers
            .iter()
            .map(|(&slot, &mode)| (slot, mode))
            .collect();
        for (slot, mode) in receivers {
            let Some(entry) = self.collected.slots.get(usize::from(slot))
            else {
                continue;
            };
            let Container::Module(module) = entry.container
            else {
                continue;
            };
            if entry.name != method {
                continue;
            }
            let mut segments = Vec::new();
            let mut declared_in = None;
            let mut at = Some(module);
            while let Some(structure) = at {
                self.fuel.spend()?;
                let Some(held) = self.collected.structures.get(usize::from(structure))
                else {
                    break;
                };
                segments.push(Segment::from(held.name.as_ref()));
                at = match held.container {
                    Container::Module(outer) => Some(outer),
                    Container::TopLevel(source) => {
                        declared_in = Some(source);
                        None
                    },
                };
            }
            segments.reverse();
            segments.push(Segment::from(method.as_ref()));
            let path = NamePath::from(segments);
            if declared_in.is_some_and(|source| seen(&self.collected, source, slot))
                && self.recognition.resolve_path(&path)
                    == PathResolution::Complete(Recognized::ModuleComponent)
                && self.exported.get(&path) == Some(&slot)
                && let Some(named) = self.collected.structures.get(usize::from(module))
            {
                found.push((slot, mode, named.name));
                if let Some(source) = declared_in {
                    self.collected.reach_source(here, source);
                }
            }
        }

        Ok(found)
    }

    /// Mint the method call `called` plans.
    ///
    /// # Specification
    /// - requires: every node the plan names is already minted or absent.
    /// - ensures: the call the module documentation tabulates for its
    ///   receiving, the method forced and applied to the receiver or its view
    ///   and then to each argument, the outermost node at `origin`, the method
    ///   at its head's origin, the value it receives at its receiver's origin,
    ///   a view block's call applied at that call's origin, and every other
    ///   node below it marked as inserted for the method; the first absence
    ///   among the receiver and the arguments otherwise.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::method`].
    /// - witness: `lower::method::tests::each_mode_lowers_to_its_access`
    #[spec(ensures: |ret| match ret {
        | Maybe::Present(Lowered::Computation(id)) => sink.origins.computation(id) == Maybe::Present(origin),
        | Maybe::Present(_) => false,
        | Maybe::Absent(_) => true,
    })]
    pub(super) fn mint_method(
        &self,
        called: Called,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let written = stretch(&self.operands, called.arguments);
        let mut passed = Vec::with_capacity(written.len());
        for &argument in written {
            match self.value_at(argument) {
                Maybe::Present(value) => passed.push(value),
                Maybe::Absent(reason) => return Maybe::Absent(reason),
            }
        }
        let inner = origin.inserted(Insertion::Method);
        let (head, receiver) = match (self.origin_at(called.head), self.origin_at(called.receiver))
        {
            (Maybe::Present(head), Maybe::Present(receiver)) => (head, receiver),
            (Maybe::Absent(reason), _) | (_, Maybe::Absent(reason)) => {
                return Maybe::Absent(reason);
            },
        };
        let view = |sink: &mut Sink<'_>| {
            let id = sink
                .arena
                .value_variable(Zone::Linear, DeBruijnIndex::from(0_u32));
            sink.origins.record_value(id, receiver);
            id
        };
        let id = match called.receiving {
            Receiving::Passed => {
                let passed_receiver = match self.value_at(called.receiver) {
                    Maybe::Present(value) => value,
                    Maybe::Absent(reason) => return Maybe::Absent(reason),
                };
                let id = applied(sink, called.method, (passed_receiver, &passed), [
                    head, inner, origin,
                ]);
                return Maybe::Present(Lowered::Computation(id));
            },
            Receiving::Read { held } => {
                let read = view(sink);
                let body = applied(sink, called.method, (read, &passed), [head, inner, inner]);
                sink.arena.computation_memory(MemoryForm::Access {
                    mode: AccessMode::Shared,
                    held,
                    place: Place::Whole,
                    body,
                })
            },
            Receiving::Written { held } => {
                let written = view(sink);
                let call = applied(sink, called.method, (written, &passed), [
                    head, inner, inner,
                ]);
                let variable = |sink: &mut Sink<'_>, index: u32| {
                    let id = sink
                        .arena
                        .value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index));
                    sink.origins.record_value(id, inner);
                    id
                };
                // Under the split, the value written back is 1 and the
                // answer 0; past the write-back's own binder, the answer is 1.
                let back = variable(sink, 1_u32);
                let resume = sink.arena.computation_memory(MemoryForm::Resume {
                    view: DeBruijnIndex::from(0_u32),
                    value: back,
                });
                sink.origins.record_computation(resume, inner);
                let answer = variable(sink, 1_u32);
                let returned = sink.arena.computation_return(answer);
                sink.origins.record_computation(returned, inner);
                let rest = sink.arena.computation_bind(resume, returned);
                sink.origins.record_computation(rest, inner);
                let pair = variable(sink, 0_u32);
                let split = sink
                    .arena
                    .computation_split(pair, ComponentCount::from(2_usize), rest);
                sink.origins.record_computation(split, inner);
                let body = sink.arena.computation_bind(call, split);
                sink.origins.record_computation(body, inner);
                let unit = sink.arena.value_unit();
                sink.origins.record_value(unit, inner);
                let unwind = sink.arena.computation_return(unit);
                sink.origins.record_computation(unwind, inner);
                sink.arena.computation_memory(MemoryForm::Access {
                    mode: AccessMode::Exclusive { unwind },
                    held,
                    place: Place::Whole,
                    body,
                })
            },
            Receiving::Taken { held } => {
                let taken = sink.arena.computation_memory(MemoryForm::Consume { held });
                sink.origins.record_computation(taken, inner);
                let value = sink
                    .arena
                    .value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
                sink.origins.record_value(value, receiver);
                let call = applied(sink, called.method, (value, &passed), [head, inner, inner]);
                sink.arena.computation_bind(taken, call)
            },
            Receiving::Viewed { held, view: block } => {
                let last = match block {
                    Maybe::Present(viewed) => match self.origin_at(viewed.call) {
                        Maybe::Present(origin) => origin,
                        Maybe::Absent(reason) => return Maybe::Absent(reason),
                    },
                    Maybe::Absent(_) => inner,
                };
                let read = view(sink);
                let call = applied(sink, called.method, (read, &passed), [head, inner, last]);
                let index = sink.arena.computation_memory(MemoryForm::Access {
                    mode: AccessMode::Shared,
                    held,
                    place: Place::Whole,
                    body: call,
                });
                sink.origins.record_computation(index, inner);
                // Past the index's binder the held slot keeps its linear
                // index, and the index is the innermost intuitionistic one.
                let at = sink
                    .arena
                    .value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
                sink.origins.record_value(at, inner);
                let (mode, body) = match block {
                    Maybe::Present(block) => {
                        let body = match self.mint_block(block.body, sink) {
                            Maybe::Present(body) => body,
                            Maybe::Absent(reason) => return Maybe::Absent(reason),
                        };
                        let mode = if self.ended_views.contains(&block.binder) {
                            let unit = sink.arena.value_unit();
                            sink.origins.record_value(unit, inner);
                            let unwind = sink.arena.computation_return(unit);
                            sink.origins.record_computation(unwind, inner);
                            AccessMode::Exclusive { unwind }
                        }
                        else {
                            AccessMode::Shared
                        };
                        (mode, body)
                    },
                    Maybe::Absent(unviewed::Absent::Read) => {
                        let lent = view(sink);
                        let read = sink.arena.computation_return(lent);
                        sink.origins.record_computation(read, inner);
                        (AccessMode::Shared, read)
                    },
                };
                let lent = sink.arena.computation_memory(MemoryForm::Access {
                    mode,
                    held,
                    place: Place::At { index: at },
                    body,
                });
                sink.origins.record_computation(lent, inner);
                sink.arena.computation_bind(index, lent)
            },
        };

        Maybe::Present(sink.computation(id, origin))
    }

    /// Wrap the body `body` of a written-through method in the hold of its
    /// receiver, returning the receiver's last value beside the body's
    /// answer.
    ///
    /// # Specification
    /// - requires: `body` was minted under the receiver's linear binder past
    ///   every parameter.
    /// - ensures: `hold self = x ; r <- body ; pure (self, r)`, `x` the
    ///   receiver parameter, every node marked as inserted for the method at
    ///   `origin`.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`HeldReceiver`].
    /// - witness: `lower::method::tests::a_written_through_body_returns_its_receiver`
    #[spec(ensures: |ret| sink.origins.computation(ret) == Maybe::Present(origin.inserted(Insertion::Method)))]
    pub(super) fn hold_body(
        receiver: HeldReceiver,
        body: ComputationId,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> ComputationId
    {
        let inner = origin.inserted(Insertion::Method);
        let value = sink
            .arena
            .value_variable(Zone::Intuitionistic, receiver.index);
        sink.origins.record_value(value, inner);
        let slot = sink
            .arena
            .value_variable(Zone::Linear, DeBruijnIndex::from(0_u32));
        sink.origins.record_value(slot, inner);
        let answer = sink
            .arena
            .value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        sink.origins.record_value(answer, inner);
        let pair = sink.arena.value_tuple(&[slot, answer]);
        sink.origins.record_value(pair, inner);
        let returned = sink.arena.computation_return(pair);
        sink.origins.record_computation(returned, inner);
        let bound = sink.arena.computation_bind(body, returned);
        sink.origins.record_computation(bound, inner);
        let held = sink.arena.computation_memory(MemoryForm::Hold {
            value,
            body: bound,
            grade: HoldGrade::Many,
        });
        sink.origins.record_computation(held, inner);

        held
    }

    /// The declared result of a written-through method whose written result
    /// is `declared`: the receiver's type paired before the answer.
    ///
    /// # Specification
    /// - requires: `parameters` are the function's own and `declared` its
    ///   written result, minted past every parameter.
    /// - ensures: `-F [row] (T, R)` for a written `-F [row] R`, `T` the
    ///   receiver's written type carried past the parameters from the
    ///   receiver's on that a later type names, every node marked as inserted
    ///   for the method at `origin`; nothing for any other result or a receiver
    ///   type that did not lower.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`HeldReceiver`].
    /// - witness: `lower::method::tests::a_written_through_body_returns_its_receiver`
    #[spec(ensures: |ret| match ret {
        | Maybe::Present(id) => sink.origins.comp_type(id) == Maybe::Present(origin.inserted(Insertion::Method)),
        | Maybe::Absent(_) => true,
    })]
    pub(super) fn written_result(
        &self,
        receiver: HeldReceiver,
        parameters: &[Parameter],
        declared: CompTypeId,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<CompTypeId, lowered::Absent>
    {
        let Some(&CompType::Returner {
            result,
            ref effects,
        }) = sink.arena.comp_type(declared)
        else {
            return Maybe::Absent(lowered::Absent::OtherSort);
        };
        let effects = effects.clone();
        let Some(&Parameter {
            declared: Maybe::Present(written),
            ..
        }) = parameters.get(receiver.position)
        else {
            return Maybe::Absent(lowered::Absent::Unstated);
        };
        let held = match self.value_type_at(written) {
            Maybe::Present(held) => held,
            Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        let past = parameters
            .get(receiver.position ..)
            .unwrap_or_default()
            .iter()
            .filter(|parameter| bool::from(self.scope.mentioned(parameter.frame)))
            .count();
        let past = Binders::from(u32::try_from(past).unwrap_or(u32::MAX));
        let carried = shift_value_type(sink.arena, held, past).settle(sink.arena);
        let inner = origin.inserted(Insertion::Method);
        let pair = sink.arena.value_type_product(&[carried, result]);
        sink.origins.record_value_type(pair, inner);
        let id = sink.arena.comp_type_returner_with_effects(pair, effects);
        sink.origins.record_comp_type(id, inner);

        Maybe::Present(id)
    }
}

/// The method `method` forced and applied to the receiver, then to each
/// argument of `values`; of `origins`, the method stands at the first, the
/// last application at the third, and every other node at the second.
///
/// # Specification
/// - requires: the receiver and every argument are values of the sink's arena.
/// - ensures: `force(method)` applied left to right, one application per value,
///   the method's constant recorded at `origins[0]`, the last application at
///   `origins[2]` and every other node at `origins[1]`.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Lowerer::mint_method`].
/// - witness: `lower::method::tests::each_mode_lowers_to_its_access`
#[spec(ensures: |ret| matches!(origins, [_, _, last] if sink.origins.computation(ret) == Maybe::Present(last)))]
fn applied(
    sink: &mut Sink<'_>,
    method: ConstantIndex,
    values: (ValueId, &[ValueId]),
    origins: [Origin; 3],
) -> ComputationId
{
    let (receiver, passed) = values;
    let [head, at, last] = origins;
    let constant = sink.arena.value_constant(method);
    sink.origins.record_value(constant, head);
    let mut applied = sink.arena.computation_force(constant);
    sink.origins.record_computation(applied, at);
    let mut remaining = passed.len();
    for &value in core::iter::once(&receiver).chain(passed) {
        applied = sink.arena.computation_application(applied, value);
        let here = if remaining == 0_usize { last } else { at };
        sink.origins.record_computation(applied, here);
        remaining = remaining.saturating_sub(1_usize);
    }

    applied
}

/// The operand `pieces` index when they read an index `s[e]`: an operand, then
/// its bracket.
///
/// # Specification
/// trivial.
pub(super) fn indexed(pieces: &Pieces) -> Option<Placed>
{
    match *pieces.pieces.as_slice() {
        [
            Piece::Operand(indexed),
            Piece::Tile {
                label: TileName::BRACKET_OPEN,
                ..
            },
            ..,
        ] => Some(indexed),
        _ => None,
    }
}
