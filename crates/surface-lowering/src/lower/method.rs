//! Method calls in the lowering: a call `s.f(a, …)` whose `f` is a method of
//! a module in scope reads, writes or takes its receiver `s` as the method's
//! receiver mode says, and a method that writes its receiver through holds it
//! over its body.
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
use super::lowered;
use super::stretch;
use crate::CandidateCount;
use crate::SurfaceName;
use crate::error::FragmentBoundary;
use crate::error::LoweringRefusal;
use crate::form::Cursor;
use crate::form::FormName;
use crate::form::Former;
use crate::form::Piece;
use crate::form::Pieces;
use crate::form::Run;
use crate::form::TileName;
use crate::form::read_pieces;
use crate::import::ImportResolution;
use crate::module::Container;
use crate::module::ReceiverMode;
use crate::module::SlotIndex;
use crate::namespace::NamePath;
use crate::namespace::PathResolution;
use crate::namespace::Recognized;
use crate::namespace::Segment;
use crate::origin::Insertion;
use crate::origin::Origin;
use crate::resolve::Frame;
use crate::resolve::binder_site;
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

    /// Refuse a mode word written on a parameter of the function at
    /// `function` that is no receiver.
    ///
    /// # Specification
    /// - requires: `cursor` stands just past the parameter list's `(`;
    ///   `receiver` is the function's receiver mode.
    /// - ensures: `Ok` when every mode word stands on the first parameter of a
    ///   method, named `self`.
    /// - fails: [`LoweringRefusal::StrayReceiverMode`] at the first mode word
    ///   that does not.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a mode word on a top-level function's parameter and
    ///   on a method's second parameter, each refused at the word.
    /// - witness: `lower::method::tests::a_mode_word_off_a_receiver_is_refused`
    #[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(LoweringRefusal::StrayReceiverMode { .. })))]
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
            match piece {
                Piece::Tile { label, .. } if label == TileName::PAREN_CLOSE => break,
                Piece::Tile { label, at } if label == TileName::IDENTIFIER && !after_colon => {
                    named = self.name_at(at);
                },
                Piece::Tile { label, .. } if label == TileName::COLON => after_colon = true,
                Piece::Tile { label, at }
                    if after_colon
                        && (label == TileName::SHARED || label == TileName::CONSUMED) =>
                {
                    let receives =
                        position == 0_usize && named.as_ref() == "self" && receiver.is_some();
                    if !receives {
                        return Err(LoweringRefusal::StrayReceiverMode {
                            span: at.span,
                            mode: self.name_at(at),
                        });
                    }
                },
                Piece::Tile { label, .. } if label == TileName::COMMA => {
                    position = position.saturating_add(1_usize);
                    after_colon = false;
                },
                Piece::Tile { .. } | Piece::Operand(_) => {},
            }
        }

        Ok(())
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
    /// - ensures: a head `s.f` whose `s` is a name a binder or a declaration
    ///   answers and whose `f` one module in scope declares as a method stands
    ///   as a computation, planned as the call its receiver mode makes of a
    ///   receiver held in a slot, or of one passed as a value, as the module
    ///   documentation tabulates; each argument reads as a value under the
    ///   binder that call opens; any other call is left unplanned.
    /// - fails: [`LoweringRefusal::AmbiguousMethod`] at `f` for a method more
    ///   than one module in scope declares; the forward-member refusal for a
    ///   method declared at or after the call's declaration;
    ///   [`LoweringRefusal::ImplicitUnsupplied`] for a method with an implicit
    ///   telescope, which a call off its receiver supplies nothing;
    ///   [`FragmentBoundary::Held`] at `s` for a written-through call on a
    ///   receiver that is no held slot; the wrong-sort refusal where no
    ///   computation is read; the name's and the argument list's refusals.
    /// - panics: none.
    ///
    /// # Errors
    /// The call's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a call at each mode, a call on a receiver that is not
    ///   held, an ambiguous method, a forward one and one with an implicit
    ///   telescope.
    /// - witness: `lower::method::tests::each_mode_lowers_to_its_access`
    /// - witness: `lower::method::tests::a_receiver_not_held_is_passed_or_refused`
    /// - witness: `lower::method::tests::a_method_two_modules_declare_is_refused_naming_both`
    /// - witness: `lower::method::tests::a_receiver_is_a_typed_first_self`
    #[spec(ensures: |ret| !matches!(ret, Ok(Planned(true))) || matches!(self.plans.get(site.at.node), Some(&Plan::Method(_))))]
    pub(super) fn method(
        &mut self,
        site: Site,
        cursor: &Cursor<'_>,
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
            return Err(site.out(FragmentBoundary::Unadmitted));
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
            (ReceiverMode::Shared | ReceiverMode::Consumed, None) => {
                self.read(target.node, Reading::Value(frame));
                (Receiving::Passed, frame)
            },
            (ReceiverMode::Exclusive, None) => return Err(receiver.out(FragmentBoundary::Held)),
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

    /// Every method named `method` that a module in scope in the source `here`
    /// declares: its slot, its receiver mode and its module's name, in
    /// collection order.
    ///
    /// # Specification
    /// - requires: `here` is a source of the unit.
    /// - ensures: each method of that name whose module's path, joined with the
    ///   name, resolves to it as an exported component, and whose outermost
    ///   module `here` declares or one of `here`'s imports resolves to; a
    ///   module of a sibling source `here` does not import is out of scope,
    ///   though the unit recognises its path.
    /// - fails: [`LoweringRefusal::BudgetExceeded`] when the walk up a nested
    ///   module's containers runs out of allowance.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a method one module declares, one two modules
    ///   declare, and one a sibling source declares that the caller does not
    ///   import.
    /// - witness: `lower::method::tests::a_method_two_modules_declare_is_refused_naming_both`
    /// - witness: `tests::namespace::a_method_of_a_source_not_imported_is_out_of_scope`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |found| found.iter().all(|&(slot, mode, _)| self.collected.receivers.get(&slot) == Some(&mode))))]
    fn methods_named(
        &mut self,
        method: SurfaceName<'source>,
        here: SourceIndex,
    ) -> Result<Vec<(SlotIndex, ReceiverMode, SurfaceName<'source>)>, LoweringRefusal<'source>>
    {
        let seen = |collected: &crate::module::Collected<'source>, target: SourceIndex| {
            target == here
                || collected.imports.of(here).any(|import| {
                    import.resolution() == ImportResolution::Path(ImportTarget::Source(target))
                })
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
            if declared_in.is_some_and(|source| seen(&self.collected, source))
                && self.recognition.resolve_path(&path)
                    == PathResolution::Complete(Recognized::ModuleComponent)
                && self.exported.get(&path) == Some(&slot)
                && let Some(named) = self.collected.structures.get(usize::from(module))
            {
                found.push((slot, mode, named.name));
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
    ///   and every other node below it marked as inserted for the method; the
    ///   first absence among the receiver and the arguments otherwise.
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
