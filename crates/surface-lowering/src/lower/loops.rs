//! Loops: `loop`, `while`, `for`, `break` and `continue`, lowered into the
//! fixpoint former, whose body runs in the continuation the loop was entered
//! with.
//!
//! # The fixpoint reading
//!
//! A loop binds its own body as a recursive thunk, `fix k. b`, with no descent
//! claim: a loop need not end, so its evidence is partial.
//!
//! - `loop { b }` is `fix k. b'`.
//! - `while c { b }` is `fix k. x ← c; case x { inl _ => b', inr _ => return ()
//!   }`: the condition is read where a computation is and bound inside the
//!   fixpoint, so every pass tests it again, and the false branch is the loop's
//!   `break`. A value written as the condition is returned, and `x ← return v;
//!   N` written as its beta step `N[v/x]`, as the commuting writes a
//!   returner's, since the checker synthesises no returner it binds.
//! - `for x in xs { b }` is `(fix k. λ r. case r { nil => return (), cons(x, t)
//!   => b' }) xs`, structural on `r`: the list case binds the tail one stage
//!   below the list it reads, so the stage ends the loop. The empty list is the
//!   loop's `break`, and in `b'` a pass runs again on the tail, `(force k) t`,
//!   where a `loop` or a `while` forces `k` alone. The fixpoint's arrow is read
//!   off the list's type and the type the loop is checked against, the applied
//!   fixpoint's checking rule.
//! - In `b'`, every place a path through the body ends without an exit runs the
//!   loop again: `e` becomes `x ← e; split x (); force k`, the result discarded
//!   as a block's statement discards it, so it must be unit. `continue` is
//!   `force k` where it stands.
//! - `break(v)` is `return v` and a bare `break` is `return ()`, each a local
//!   end of the loop's own position: the commuting continues it with what
//!   follows the loop, or leaves it where the loop ends the body.
//!
//! The loop's own binder carries a name no identifier spells, so a written
//! name never resolves to it and `continue` finds the nearest one; a `for`
//! loop's remaining tail carries another, found inside the loop's own binder.
//!
//! - choice: the one fixpoint former the core has, at partial evidence, its
//!   binder the thunk a pass forces to run the next.
//! - alternatives: a local recursive function the body calls, whose binder
//!   would be an exit boundary, so a `return` inside would leave only that
//!   function; a join point, which the core, the checker, the machine and the
//!   kernel would each have to learn.
//! - reversal: join points in the core and the kernel, at which a pass's end is
//!   a jump to the loop's head.
//!
//! # Exits at each boundary
//!
//! A loop stands only where a path through a body passes, as an exit does,
//! and the commuting puts it where the body ends; its fixpoint is then checked
//! against the body's own type. `return` and `become` inside a loop therefore
//! leave the function, as they do outside one. `break` and `continue` leave
//! the nearest loop and nothing else: a function, a lambda, a thunk or a
//! copattern clause inside a loop has a body of its own, and one written there
//! is [`LoweringRefusal::OutsideLoop`]. A capability scope inside a loop
//! keeps its handler's frame live while its subject runs, so a `break` or a
//! `continue` there is [`LoweringRefusal::AcrossHandler`]; a loop inside the
//! subject is a loop as any other. The machine runs a loop's body in the
//! continuation the loop was entered with, so an exit through a loop, and a
//! `become` inside one, leaves no frame of the loop's behind.
//!
//! # Loop-carried state
//!
//! State a loop carries lives in held slots (the `lower::access` module). A
//! `loop` or a `while` that names a slot held around it threads the slot
//! through its passes as the fixpoint's accumulator. With one slot:
//!
//! ```text
//! (fix k. λ s. hold c = s; b) c
//! ```
//!
//! - The first pass takes the slot's content. Each pass holds it again under
//!   the slot's own name, so the body reads and writes its own copy.
//! - A pass's end runs `(force k) c`, handing the next pass the content as the
//!   pass left it.
//! - Several slots travel as a tuple: `λ p. split p (s₁, …, sₙ)`, each held
//!   again in turn.
//!
//! What follows the loop runs at its `break`s, inside the passes, so it is
//! read under the slots held again and sees what the last pass left there.
//! A loop threads only as a statement or the last computation of a block
//! whose ends continue no enclosing block; a loop elsewhere sees the binders
//! around it unchanged on every pass, as a `for` always does.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use core::cmp::Reverse;

use anodized::spec;
use gandr_core_term::ComponentCount;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::ValueId;
use gandr_core_term::Zone;
use gandr_core_term::instantiate_computation_traced;
use gandr_core_term::memory::MemoryForm;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FixpointEvidence;
use gandr_surface_syntax::NodeIndex;
use quenchant_shape::shape::Maybe;

use super::Block;
use super::Lowered;
use super::Lowerer;
use super::Plan;
use super::Produced;
use super::Reading;
use super::Sink;
use super::Site;
use super::closed;
use super::exhausted;
use super::exits::Leaves;
use super::exits::mark_copies;
use super::exits::record_copies;
use super::lowered;
use super::native::answered;
use crate::error::CrossedExit;
use crate::error::FormFault;
use crate::error::FragmentBoundary;
use crate::error::LoopExit;
use crate::error::LoweringRefusal;
use crate::form::Cursor;
use crate::form::Former;
use crate::form::Placed;
use crate::form::Shape;
use crate::form::TileName;
use crate::form::shape_of;
use crate::form::tile_label;
use crate::origin::Insertion;
use crate::origin::Origin;
use crate::resolve::Frame;
use crate::resolve::ScopeId;
use crate::resolve::SurfaceName;
use crate::resolve::binder_site;

#[cfg(test)]
mod tests;

/// The name a loop's own binder carries: no identifier spells it, so no
/// written name resolves to it.
///
/// # Specification
/// trivial.
fn iteration() -> SurfaceName<'static>
{
    SurfaceName::from(" loop")
}

/// The name a `for` loop's remaining tail carries: no identifier spells it,
/// so no written name resolves to it.
///
/// # Specification
/// trivial.
fn remaining() -> SurfaceName<'static>
{
    SurfaceName::from(" tail")
}

/// Where a pass through a loop's body runs the loop again from.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct Reentry
{
    /// The index the loop's own binder has.
    own: DeBruijnIndex,
    /// The index a `for` loop's remaining tail has, which the next pass steps
    /// through.
    tail: Maybe<DeBruijnIndex, passed::Absent>,
    /// The held slots the next pass takes, when the loop threads any.
    carried: Maybe<Carried, carried::Absent>,
}

quenchant_shape::reason_enum! {
    /// Why a loop's next pass steps through no tail.
    pub(super) mod passed {
        /// The loop iterates no list.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// A `loop` or a `while` runs its next pass over nothing.
            Unlisted,
        }
    }
}

/// The held slots a pass hands the loop's next pass, where the pass stands:
/// the innermost slot's linear index and how many slots there are, each next
/// one a linear index further out.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct Carried
{
    /// The linear index the innermost slot has.
    innermost: DeBruijnIndex,
    /// How many slots the loop threads.
    count: ComponentCount,
}

quenchant_shape::reason_enum! {
    /// Why a loop's next pass takes no held slot.
    pub(super) mod carried {
        /// The loop threads none.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No slot held around the loop is named inside it, or the loop
            /// stands where it cannot thread one.
            Unthreaded,
        }
    }
}

/// The value a threading loop's pass takes: the one slot read, or the tuple
/// of the slots read in the order `indices` names them, outermost first.
///
/// # Specification
/// - requires: `indices` names at least one linear index in scope where the
///   value is minted.
/// - ensures: the linear variable at the one index; otherwise the tuple of the
///   linear variables at `indices`, in order; every node minted at `origin`.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a `while` threading one slot passes it, and one threading
///   two passes both, in order.
/// - witness: `lower::loops::tests::a_loop_threads_the_slots_it_names_through_its_passes`
#[spec(ensures: |ret| sink.arena.value(ret).is_some())]
fn slots(
    indices: impl ExactSizeIterator<Item = DeBruijnIndex>,
    sink: &mut Sink<'_>,
    origin: Origin,
) -> ValueId
{
    let mut read = Vec::with_capacity(indices.len());
    for index in indices {
        let slot = sink.arena.value_variable(Zone::Linear, index);
        sink.origins.record_value(slot, origin);
        read.push(slot);
    }
    if let &[one] = read.as_slice() {
        return one;
    }
    let tuple = sink.arena.value_tuple(&read);
    sink.origins.record_value(tuple, origin);
    tuple
}

/// The linear indices of `carried`'s slots, outermost first.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one index per slot, from `innermost + count - 1` down to
///   `innermost`, each saturating at the index width.
/// - fails: never.
/// - panics: none.
/// - executable: none — the specification facade wraps the body in a closure,
///   which cannot return the opaque iterator; the witness reads the pass it
///   builds.
///
/// # Adequacy
/// - hypothesis: L3 — a pass of a `while` threading two slots hands both on,
///   the outer first.
/// - witness: `lower::loops::tests::a_loop_threads_the_slots_it_names_through_its_passes`
fn outermost_first(carried: Carried) -> impl ExactSizeIterator<Item = DeBruijnIndex>
{
    (0 .. usize::from(carried.count)).rev().map(move |outward| {
        u32::try_from(outward)
            .ok()
            .and_then(|outward| u32::from(carried.innermost).checked_add(outward))
            .map_or_else(|| DeBruijnIndex::from(u32::MAX), DeBruijnIndex::from)
    })
}

/// The pass `reentry` runs: the force of the loop's own binder, applied to the
/// remaining tail when the loop is a `for`, or to the slots it threads.
///
/// # Specification
/// - requires: `reentry`'s indices are in scope where the pass is minted.
/// - ensures: `force k`, `(force k) t` or `(force k) c`, every node below the
///   pass at `origin`; the caller records the pass itself.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a `continue` in a `while` and one in a `for` each run
///   their loop again, the second on its tail; a pass of a threading loop hands
///   the next its slots.
/// - witness: `lower::loops::tests::a_continue_runs_its_own_loop_again`
/// - witness: `lower::loops::tests::a_for_steps_through_its_list`
/// - witness: `lower::loops::tests::a_loop_threads_the_slots_it_names_through_its_passes`
#[spec(ensures: |ret| sink.arena.computation(ret).is_some())]
pub(super) fn again(
    reentry: Reentry,
    sink: &mut Sink<'_>,
    origin: Origin,
) -> ComputationId
{
    let itself = sink.arena.value_variable(Zone::Intuitionistic, reentry.own);
    sink.origins.record_value(itself, origin);
    let forced = sink.arena.computation_force(itself);
    let argument = match (reentry.tail, reentry.carried) {
        (Maybe::Present(tail), _) => {
            let tail = sink.arena.value_variable(Zone::Intuitionistic, tail);
            sink.origins.record_value(tail, origin);
            tail
        },
        (Maybe::Absent(_), Maybe::Present(carried)) => {
            slots(outermost_first(carried), sink, origin)
        },
        (Maybe::Absent(_), Maybe::Absent(_)) => return forced,
    };
    sink.origins.record_computation(forced, origin);
    sink.arena.computation_application(forced, argument)
}

impl<'source> Lowerer<'_, 'source>
{
    /// Classify a loop, `loop { … }`.
    ///
    /// # Specification
    /// - requires: `site` is a `loop` in term position.
    /// - ensures: a loop standing as a computation where a path through a body
    ///   passes binds itself in a frame extending its own, then the slots it
    ///   threads, reads its block under that frame as a loop's body, and is
    ///   planned over it.
    /// - provides: the unconditional loop.
    /// - fails: yields the wrong-sort refusal outside computation position, the
    ///   not-in-tail refusal where no path passes, the block's own refusal, and
    ///   the unreachable refusal for statements after one every path of which
    ///   exits.
    /// - panics: none.
    ///
    /// # Errors
    /// The loop's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a loop at a body's end and one bound as a statement
    ///   each lower to the fixpoint the module docs state and are accepted; one
    ///   in a call's operand is refused.
    /// - witness: `lower::loops::tests::a_loop_lowers_to_a_partial_fixpoint_over_its_body`
    /// - witness: `lower::loops::tests::a_loop_off_every_path_is_refused`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || (self.exitable.contains(&site.at.node)
                    && matches!(self.plans.get(site.at.node), Some(&Plan::Loop(body))
                        if self.looping.contains(&body.last)))
        },
    )]
    pub(super) fn looped(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::Computation)?;
        if !self.exitable.contains(&site.at.node) {
            return Err(site.out(FragmentBoundary::NotInTail));
        }
        let _keyword = cursor.tile(TileName::LOOP);
        let own = self.scope.extend(
            frame,
            iteration(),
            Maybe::Absent(binder_site::Absent::Unwritten),
        );
        let (passes, carries) = self.passes(site, own);
        let body = self.block(site, &mut cursor, passes)?;
        self.carry(body, carries);
        self.iterate(site, body)?;
        self.plan(site, Plan::Loop(body));

        Ok(())
    }

    /// Classify a conditional loop, `while c { … }`.
    ///
    /// # Specification
    /// - requires: `site` is a `while` in term position.
    /// - ensures: a `while` standing as a computation where a path through a
    ///   body passes binds itself in a frame extending its own, then the slots
    ///   it threads, reads its condition as a tested computation under that
    ///   frame, reads its block as a loop's body under two more, nameless
    ///   binders, the bound condition and the case's payload, and is planned
    ///   over both.
    /// - provides: the conditional loop.
    /// - fails: as [`Self::looped`], and the condition's own refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The loop's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a `while` at a body's end and one bound as a
    ///   statement each lower to the fixpoint over the case of the condition
    ///   and are accepted.
    /// - witness: `lower::loops::tests::a_while_tests_its_condition_on_every_pass`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || (self.exitable.contains(&site.at.node)
                    && matches!(self.plans.get(site.at.node), Some(&Plan::While(condition, body))
                        if self.looping.contains(&body.last)
                            && self.tested.contains(&condition)
                            && matches!(self.reading(condition), Reading::Computation(Frame::Inner(_)))))
        },
    )]
    pub(super) fn repeated(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::Computation)?;
        if !self.exitable.contains(&site.at.node) {
            return Err(site.out(FragmentBoundary::NotInTail));
        }
        let _keyword = cursor.tile(TileName::WHILE);
        let condition = site.one(cursor.operands())?;
        let own = self.scope.extend(
            frame,
            iteration(),
            Maybe::Absent(binder_site::Absent::Unwritten),
        );
        let (passes, carries) = self.passes(site, own);
        let _tested = self.tested.insert(condition.node);
        self.read(condition.node, Reading::Computation(passes));
        let mut held = passes;
        for _binder in 0_u8 .. 2_u8 {
            held = Frame::Inner(self.scope.extend(
                held,
                SurfaceName::from(""),
                Maybe::Absent(binder_site::Absent::Unwritten),
            ));
        }
        let body = self.block(site, &mut cursor, held)?;
        self.carry(body, carries);
        self.iterate(site, body)?;
        self.plan(site, Plan::While(condition.node, body));

        Ok(())
    }

    /// The frame what follows the computation `written` reads under, a
    /// statement or the last computation of the block `site` reads, standing
    /// under `frame`: `after` extended by the slots the computation threads,
    /// when it is a `loop` or a `while` that threads any. What follows the
    /// loop runs inside its passes, so a slot named there is threaded too.
    ///
    /// # Specification
    /// - requires: `written` is a computation of the block `site` reads, read
    ///   under `frame`; `after` is the frame what follows it reads under when
    ///   it threads nothing.
    /// - ensures: for a `loop` or a `while` in a block whose ends continue no
    ///   other's, each held slot an identifier of the block from the loop on
    ///   resolves to at `frame`, once, is recorded for the loop with its linear
    ///   index there and its name, outermost first, and `after` is extended by
    ///   one linear binder per slot under the slot's name, each recorded as
    ///   held; anything else threads nothing and answers `after`.
    /// - fails: [`LoweringRefusal::BudgetExceeded`] from a name's walk.
    /// - panics: none.
    ///
    /// # Errors
    /// The walk's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a `while` naming one slot in its condition and its
    ///   body threads it, one naming two threads both, a slot named only after
    ///   the loop is threaded, and one naming none threads nothing.
    /// - witness: `lower::loops::tests::a_loop_threads_the_slots_it_names_through_its_passes`
    #[spec(ensures: |ret| match ret {
        | Ok(rest) => rest == after || self.threading.contains_key(&written),
        | Err(LoweringRefusal::BudgetExceeded { .. }) => true,
        | Err(_) => false,
    })]
    pub(super) fn threads(
        &mut self,
        site: Site,
        written: NodeIndex,
        (frame, after): (Frame, Frame),
    ) -> Result<Frame, LoweringRefusal<'source>>
    {
        let Some(from) = self.tree.node(written).map(|node| node.span().start())
        else {
            return Ok(after);
        };
        let looping = self.tree.node(written).is_some_and(|node| {
            matches!(
                shape_of(self.pbg, node),
                Ok(Shape::Form {
                    former: Former::Loop | Former::While,
                    ..
                })
            )
        });
        if !looping
            || self.joined.contains(&site.at.node)
            || !self
                .scope
                .chain(frame)
                .any(|binder| self.held.contains(&binder))
        {
            return Ok(after);
        }
        // Keyed outermost first: distinct slots on one chain stand at distinct
        // linear indices.
        let mut slots: BTreeMap<Reverse<DeBruijnIndex>, SurfaceName<'source>> = BTreeMap::new();
        let mut pending = Vec::from([site.at.node]);
        while let Some(position) = pending.pop() {
            let Some(node) = self.tree.node(position)
            else {
                continue;
            };
            if node.span().end() <= from {
                continue;
            }
            pending.extend(self.tree.children(position));
            if node.span().start() < from
                || tile_label(self.pbg, node) != Maybe::Present(TileName::IDENTIFIER)
            {
                continue;
            }
            let name = self.name_at(Placed::of(position, node));
            if let Maybe::Present(bound) = self.scope.resolve(frame, name, &mut self.fuel)?
                && self.held.contains(&bound.binder)
            {
                let _first = slots.entry(Reverse(bound.index)).or_insert(name);
            }
        }
        if slots.is_empty() {
            return Ok(after);
        }
        let mut rest = after;
        for &name in slots.values() {
            let again =
                self.scope
                    .extend_linear(rest, name, Maybe::Absent(binder_site::Absent::Unwritten));
            let _held = self.held.insert(again);
            rest = Frame::Inner(again);
        }
        let _first = self.threading.insert(
            written,
            slots
                .into_iter()
                .map(|(Reverse(index), name)| (index, name))
                .collect(),
        );

        Ok(rest)
    }

    /// The frame the passes of the loop at `site` read under, past its own
    /// binder `own`, and the slots its first pass takes.
    ///
    /// # Specification
    /// - requires: `own` is the loop's own binder.
    /// - ensures: for a loop [`Self::threads`] recorded, the pass's argument —
    ///   one binder, or one for the tuple and one per slot it splits into —
    ///   then each slot held again under its own name, recorded as held and as
    ///   the loop's, with the linear indices the slots have where the loop
    ///   stands, outermost first; `own` and nothing otherwise.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::threads`].
    /// - witness: `lower::loops::tests::a_loop_threads_the_slots_it_names_through_its_passes`
    #[spec(ensures: |ret| ret.1.is_empty() != self.reheld.contains_key(&own))]
    fn passes(
        &mut self,
        site: Site,
        own: ScopeId,
    ) -> (Frame, Vec<DeBruijnIndex>)
    {
        let Some(slots) = self.threading.remove(&site.at.node)
        else {
            return (Frame::Inner(own), Vec::new());
        };
        let unwritten = || Maybe::Absent(binder_site::Absent::Unwritten);
        let mut pass = Frame::Inner(self.scope.extend(
            Frame::Inner(own),
            SurfaceName::from(""),
            unwritten(),
        ));
        if slots.len() > 1 {
            for _component in &slots {
                pass = Frame::Inner(self.scope.extend(pass, SurfaceName::from(""), unwritten()));
            }
        }
        let mut reheld = Vec::with_capacity(slots.len());
        let mut carries = Vec::with_capacity(slots.len());
        for (index, name) in slots {
            let again = self.scope.extend_linear(pass, name, unwritten());
            let _held = self.held.insert(again);
            reheld.push(again);
            carries.push(index);
            pass = Frame::Inner(again);
        }
        let _first = self.reheld.insert(own, reheld);

        (pass, carries)
    }

    /// Record `carries` as the slots the first pass of the loop over `body`
    /// takes.
    ///
    /// # Specification
    /// - requires: `carries` is what [`Self::passes`] answered for the loop.
    /// - ensures: recorded under the body's last computation unless empty.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::threads`].
    /// - witness: `lower::loops::tests::a_loop_threads_the_slots_it_names_through_its_passes`
    #[spec(
        captures: empty = carries.is_empty(),
        ensures: empty || self.carries.contains_key(&body.last),
    )]
    fn carry(
        &mut self,
        body: Block,
        carries: Vec<DeBruijnIndex>,
    )
    {
        if !carries.is_empty() {
            let _first = self.carries.insert(body.last, carries);
        }
    }

    /// Classify a list loop, `for x in xs { … }`.
    ///
    /// # Specification
    /// - requires: `site` is a `for` in term position.
    /// - ensures: a `for` standing as a computation where a path through a body
    ///   passes reads its list as a value in its own frame, binds itself in a
    ///   frame extending its own, reads its block as a loop's body under three
    ///   more binders — the remaining list, the element its written name binds
    ///   and the remaining tail — and is planned over both.
    /// - provides: the loop over a native list.
    /// - fails: as [`Self::looped`], a misplaced-tile fault for a `for` that
    ///   names no element, and the list's own refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The loop's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a `for` at a body's end and one bound as a statement
    ///   each lower to the structural fixpoint over the list case and are
    ///   accepted; a `continue` in it runs the loop again on the tail.
    /// - witness: `lower::loops::tests::a_for_steps_through_its_list`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || (self.exitable.contains(&site.at.node)
                    && matches!(self.plans.get(site.at.node), Some(&Plan::For(list, body))
                        if self.looping.contains(&body.last)
                            && matches!(self.reading(list), Reading::Value(_))))
        },
    )]
    pub(super) fn stepped(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::Computation)?;
        if !self.exitable.contains(&site.at.node) {
            return Err(site.out(FragmentBoundary::NotInTail));
        }
        let _keyword = cursor.tile(TileName::FOR);
        let Maybe::Present(binder) = cursor.tile(TileName::IDENTIFIER)
        else {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        };
        let _in = cursor.tile(TileName::IN);
        let list = site.one(cursor.operands())?;
        self.read(list.node, Reading::Value(frame));
        let unwritten = Maybe::Absent(binder_site::Absent::Unwritten);
        let own = Frame::Inner(self.scope.extend(frame, iteration(), unwritten));
        let listed = Frame::Inner(self.scope.extend(own, SurfaceName::from(""), unwritten));
        let name = self.name_at(binder);
        self.note_binder(binder, name)?;
        let element = Frame::Inner(self.scope.extend(listed, name, Maybe::Present(binder.span)));
        let held = Frame::Inner(self.scope.extend(element, remaining(), unwritten));
        let body = self.block(site, &mut cursor, held)?;
        self.iterate(site, body)?;
        self.plan(site, Plan::For(list.node, body));

        Ok(())
    }

    /// Run the paths through `body`, the block of the loop at `site`, as a
    /// loop's body.
    ///
    /// # Specification
    /// - requires: `body` is the block just read for the loop at `site`.
    /// - ensures: the block's last computation is where a path through a loop's
    ///   body ends and where a `break` or a `continue` may stand, and answers
    ///   what the loop answers; it carries the loop's frame and body, and no
    ///   loop past a frame, the loop being the nearest; the block's statements
    ///   as [`Self::paths_through`] marks them.
    /// - provides: the one opening of a body every loop shares.
    /// - fails: [`LoweringRefusal::Unreachable`], as [`Self::paths_through`].
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::Unreachable`] for statements no path reaches.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::looped`].
    /// - witness: `lower::loops::tests::a_loop_body_ends_by_its_exits_or_runs_again`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || (self.iterated.contains(&body.last)
                    && self.looping.contains(&body.last)
                    && self.exitable.contains(&body.last)
                    && self.framed.contains(&body.last) == self.framed.contains(&site.at.node)
                    && !self.looped_past.contains(&body.last))
        },
    )]
    fn iterate(
        &mut self,
        site: Site,
        body: Block,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let _end = self.iterated.insert(body.last);
        let _iteration = self.looping.insert(body.last);
        if self.framed.contains(&site.at.node) {
            let _framed = self.framed.insert(body.last);
        }
        if let Some(&owner) = self.bodies.get(&site.at.node) {
            let _owner = self.bodies.insert(body.last, owner);
        }
        let answer = match self.answers.get(&site.at.node) {
            Some(&answer) => {
                let _passed = self.answers.insert(body.last, answer);
                Maybe::Present(answer)
            },
            None => Maybe::Absent(answered::Absent::Unstated),
        };
        self.paths_through(site, body, answer)
    }

    /// Classify a loop exit, `break` or `break(v)`.
    ///
    /// # Specification
    /// - requires: `site` is a `break` in term position.
    /// - ensures: a `break` standing as a computation on a path through a
    ///   loop's body reads its parenthesised operand, when written, as a value
    ///   in its own frame, is recorded as a break and is planned as the
    ///   returner of the operand, or of unit without one.
    /// - provides: the exit that leaves the nearest loop.
    /// - fails: yields the wrong-sort refusal outside computation position, the
    ///   not-in-tail refusal where no path passes,
    ///   [`LoweringRefusal::OutsideLoop`] on a path through no loop's body, and
    ///   the operand's own refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The exit's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a `break` with and without a value continues what
    ///   follows its loop; one in a thunk inside a loop, and one in no loop,
    ///   are refused by name.
    /// - witness: `lower::loops::tests::a_break_continues_what_follows_its_loop`
    /// - witness: `lower::loops::tests::a_loop_exit_off_every_loop_body_is_refused_by_name`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || (self.looping.contains(&site.at.node)
                    && self.breaking.contains(&site.at.node)
                    && matches!(self.plans.get(site.at.node), Some(&(Plan::Break | Plan::Return(_)))))
        },
    )]
    pub(super) fn broken(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::Computation)?;
        self.on_loop_path(site, LoopExit::Break)?;
        let _keyword = cursor.tile(TileName::BREAK);
        let plan = match cursor.tile(TileName::PAREN_OPEN) {
            Maybe::Present(_) => {
                let operand = site.one(cursor.operands())?;
                closed(site, &mut cursor, TileName::PAREN_CLOSE)?;
                self.read(operand.node, Reading::Value(frame));
                Plan::Return(operand.node)
            },
            Maybe::Absent(_) => Plan::Break,
        };
        exhausted(site, &cursor)?;
        let _first = self.breaking.insert(site.at.node);
        self.plan(site, plan);

        Ok(())
    }

    /// Classify a loop exit, `continue`.
    ///
    /// # Specification
    /// - requires: `site` is a `continue` in term position.
    /// - ensures: a `continue` standing as a computation on a path through a
    ///   loop's body is recorded as an exit and planned as the force of the
    ///   nearest loop's own binder, at the index it has in the frame of `site`.
    /// - provides: the exit that runs the nearest loop again.
    /// - fails: as [`Self::broken`], and propagates
    ///   [`LoweringRefusal::BudgetExceeded`] from the binder walk.
    /// - panics: none.
    ///
    /// # Errors
    /// The exit's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a `continue` under a statement's binder and an arm's
    ///   payload forces the loop at the index past them; one in no loop is
    ///   refused by name.
    /// - witness: `lower::loops::tests::a_continue_runs_its_own_loop_again`
    /// - witness: `lower::loops::tests::a_loop_exit_off_every_loop_body_is_refused_by_name`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || (self.looping.contains(&site.at.node)
                    && self.leaving.contains(&site.at.node)
                    && matches!(self.plans.get(site.at.node), Some(&Plan::Reenter(_))))
        },
    )]
    pub(super) fn continued(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::Computation)?;
        self.on_loop_path(site, LoopExit::Continue)?;
        let _keyword = cursor.tile(TileName::CONTINUE);
        exhausted(site, &cursor)?;
        let reentry = self.reentry(frame, site)?;
        let _exit = self.leaving.insert(site.at.node);
        self.plan(site, Plan::Reenter(reentry));

        Ok(())
    }

    /// Where a pass through the nearest loop's body at `frame` runs the loop
    /// again from.
    ///
    /// # Specification
    /// - requires: `site` is the node the pass is read at, under `frame`.
    /// - ensures: the index the nearest loop's own binder has at `frame`, the
    ///   index of its remaining tail when that loop is a `for`, whose tail
    ///   stands inside the loop's own binder, and where the slots it holds
    ///   again stand at `frame` when that loop threads any.
    /// - fails: [`LoweringRefusal::OutsideLoop`] where no loop's binder is in
    ///   scope; [`LoweringRefusal::BudgetExceeded`] from the binder walk.
    /// - panics: none.
    ///
    /// # Errors
    /// The re-entry's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a `continue` in a `for` passes its tail, and one in a
    ///   `while` inside a `for` passes nothing; a pass of a threading `while`
    ///   passes its slots.
    /// - witness: `lower::loops::tests::a_for_steps_through_its_list`
    /// - witness: `lower::loops::tests::a_loop_threads_the_slots_it_names_through_its_passes`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |reentry| match reentry.tail {
        | Maybe::Present(tail) => u32::from(tail) < u32::from(reentry.own),
        | Maybe::Absent(_) => true,
    }))]
    fn reentry(
        &mut self,
        frame: Frame,
        site: Site,
    ) -> Result<Reentry, LoweringRefusal<'source>>
    {
        let Maybe::Present(own) = self.scope.resolve(frame, iteration(), &mut self.fuel)?
        else {
            return Err(LoweringRefusal::OutsideLoop {
                span: site.at.span,
                exit: LoopExit::Continue,
            });
        };
        let tail = match self.scope.index_of(frame, remaining(), &mut self.fuel)? {
            Maybe::Present(tail) if u32::from(tail) < u32::from(own.index) => Maybe::Present(tail),
            Maybe::Present(_) | Maybe::Absent(_) => Maybe::Absent(passed::Absent::Unlisted),
        };
        let carried = self.reheld.get(&own.binder).map_or(
            Maybe::Absent(carried::Absent::Unthreaded),
            |held| match held
                .last()
                .map(|&innermost| self.scope.linear_index(frame, innermost))
            {
                Some(Maybe::Present(innermost)) => Maybe::Present(Carried {
                    innermost,
                    count: ComponentCount::from(held.len()),
                }),
                Some(Maybe::Absent(_)) | None => Maybe::Absent(carried::Absent::Unthreaded),
            },
        );

        Ok(Reentry {
            own: own.index,
            tail,
            carried,
        })
    }

    /// Admit the loop exit `exit` at `site` only on a path through a loop's
    /// body.
    ///
    /// # Specification
    /// - requires: `site` is the exit's own node.
    /// - ensures: `Ok` exactly when a path through a loop's body passes `site`.
    /// - provides: the one admission `break` and `continue` share.
    /// - fails: the not-in-tail refusal where no path passes at all;
    ///   [`LoweringRefusal::AcrossHandler`] where the nearest loop's body holds
    ///   a handled subject `site` stands in, since the exit would run code in
    ///   place of the live handler's frame; [`LoweringRefusal::OutsideLoop`]
    ///   where a path passes and no loop's body is on it.
    /// - panics: none.
    ///
    /// # Errors
    /// The exit's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::broken`], and a `break` and a `continue`
    ///   in a subject of a scope a loop holds, each refused by name.
    /// - witness: `lower::loops::tests::a_loop_exit_off_every_loop_body_is_refused_by_name`
    /// - witness: `lower::capability::tests::an_exit_that_would_run_in_a_live_frame_is_refused`
    #[spec(
        ensures: |ret| match ret {
            | Ok(()) => self.exitable.contains(&site.at.node) && self.looping.contains(&site.at.node),
            | Err(LoweringRefusal::OutsideLoop { span, exit: refused }) => {
                span == site.at.span && refused == exit && !self.looping.contains(&site.at.node)
                    && !self.looped_past.contains(&site.at.node)
            },
            | Err(LoweringRefusal::AcrossHandler { span, .. }) => {
                span == site.at.span && !self.looping.contains(&site.at.node)
                    && self.looped_past.contains(&site.at.node)
            },
            | Err(_) => !self.exitable.contains(&site.at.node),
        },
    )]
    fn on_loop_path(
        &self,
        site: Site,
        exit: LoopExit,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        if !self.exitable.contains(&site.at.node) {
            return Err(site.out(FragmentBoundary::NotInTail));
        }
        if !self.looping.contains(&site.at.node) {
            if self.looped_past.contains(&site.at.node) {
                return Err(LoweringRefusal::AcrossHandler {
                    span: site.at.span,
                    exit: match exit {
                        LoopExit::Break => CrossedExit::Break,
                        LoopExit::Continue => CrossedExit::Continue,
                    },
                });
            }
            return Err(LoweringRefusal::OutsideLoop {
                span: site.at.span,
                exit,
            });
        }

        Ok(())
    }

    /// Record that the form at `site`, ending a path through a loop's body
    /// without an exit, runs the loop again.
    ///
    /// # Specification
    /// - requires: `site` is a form where a path through a loop's body ends,
    ///   written as a statement or taking the inferred re-entry.
    /// - ensures: `site` ends no path; a form whose every path leaves is left
    ///   as it is; any other records the index its loop's binder has under the
    ///   binder of the result it discards, and either joins the body, when a
    ///   path through it leaves, so its local ends run the loop again, or
    ///   answers nothing, since its result is discarded.
    /// - provides: the inferred `continue` at a loop's end.
    /// - fails: [`LoweringRefusal::OutsideLoop`] for a form on no loop's path,
    ///   which a loop's reader never marks; [`LoweringRefusal::BudgetExceeded`]
    ///   from the binder walk, and for an index past the width.
    /// - panics: none.
    ///
    /// # Errors
    /// The re-entry's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a call, a statement-written match, a match whose arms
    ///   are stated and a nested loop at a loop's end each run the loop again;
    ///   a nested loop with no `break` is left as it is.
    /// - witness: `lower::loops::tests::a_loop_body_ends_by_its_exits_or_runs_again`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || (!self.iterated.contains(&site.at.node)
                    && (self.leaves_at(site.at.node) == Leaves::Always)
                        != self.reentered.contains_key(&site.at.node))
        },
    )]
    pub(super) fn reenter(
        &mut self,
        site: Site,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let _ended = self.iterated.remove(&site.at.node);
        let leaves = self.leaves_at(site.at.node);
        if leaves == Leaves::Always {
            return Ok(());
        }
        let reentry = self.reentry(site.reading.frame(), site)?;
        let budget = self.fuel.budget;
        let past = |index: DeBruijnIndex| {
            u32::from(index)
                .checked_add(1_u32)
                .map(DeBruijnIndex::from)
                .ok_or(LoweringRefusal::BudgetExceeded { budget })
        };
        let under = Reentry {
            own: past(reentry.own)?,
            tail: match reentry.tail {
                Maybe::Present(tail) => Maybe::Present(past(tail)?),
                Maybe::Absent(reason) => Maybe::Absent(reason),
            },
            carried: reentry.carried,
        };
        let _first = self.reentered.insert(site.at.node, under);
        if leaves == Leaves::Never {
            let _discarded = self.answers.remove(&site.at.node);
        }
        else {
            let _joined = self.joined.insert(site.at.node);
        }

        Ok(())
    }

    /// `end`, minted at `position` where a path through a loop's body ends,
    /// with the loop run again after it.
    ///
    /// # Specification
    /// - requires: `reentry` is where the loop runs again from under one more
    ///   binder at `position`; `end` is the node's bridged computation.
    /// - ensures: `x ← end; split x (); force own`, or `…; (force own) t` in a
    ///   `for`, every inserted node at `origin` marked as the loop's insertion,
    ///   the pass recorded as an exit, and the bind recorded as distributed
    ///   when a path through `end` leaves.
    /// - provides: the minting half of [`Self::reenter`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a loop ending in a call lowers to the body written
    ///   with the re-entry by hand. L3 — the checker accepts it.
    /// - witness: `lower::loops::tests::a_loop_body_ends_by_its_exits_or_runs_again`
    #[spec(ensures: |ret| sink.arena.computation(ret).is_some())]
    pub(super) fn rerun(
        &self,
        position: NodeIndex,
        end: ComputationId,
        reentry: Reentry,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> ComputationId
    {
        let inserted = origin.inserted(Insertion::Loop);
        let discarded = sink
            .arena
            .value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        sink.origins.record_value(discarded, inserted);
        let pass = again(reentry, sink, inserted);
        sink.origins.record_computation(pass, inserted);
        let _exit = sink.exits.insert(pass);
        let split = sink
            .arena
            .computation_split(discarded, ComponentCount::default(), pass);
        sink.origins.record_computation(split, inserted);
        let bound = sink.arena.computation_bind(end, split);
        sink.origins.record_computation(bound, inserted);
        if self.leaves_at(position) != Leaves::Never {
            let _first = sink.distributed.insert(bound, inserted);
        }

        bound
    }

    /// Mint a loop over `body`.
    ///
    /// # Specification
    /// - requires: every node of `body` is already minted or absent.
    /// - ensures: `fix k. b`, partial, at `origin`, recorded as a loop, and
    ///   threading its slots as [`Self::passing`] does; nothing when the body
    ///   did not lower.
    /// - provides: the minting half of [`Self::looped`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::looped`].
    /// - witness: `lower::loops::tests::a_loop_lowers_to_a_partial_fixpoint_over_its_body`
    #[spec(ensures: |ret| match ret {
        | Maybe::Present(Lowered::Computation(id)) => sink.loops.contains(&id)
            || matches!(sink.arena.computation(id), Some(&Computation::Application(head, _)) if sink.loops.contains(&head)),
        | Maybe::Present(_) => false,
        | Maybe::Absent(_) => true,
    })]
    pub(super) fn mint_loop(
        &self,
        body: Block,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let under = match self.mint_block(body, sink) {
            Maybe::Present(under) => under,
            Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        let id = self.passing(body, under, sink, origin);

        Maybe::Present(sink.computation(id, origin))
    }

    /// Mint a conditional loop testing `condition` over `body`.
    ///
    /// # Specification
    /// - requires: the condition and every node of `body` are already minted or
    ///   absent.
    /// - ensures: `fix k. x ← c; case x { inl _ => b, inr _ => return () }`,
    ///   partial, the fixpoint at `origin` and recorded as a loop, the bind,
    ///   the case and the false branch at `origin` marked as the loop's
    ///   insertion, the false branch recorded as a break; a condition that is a
    ///   returner `return v` takes the beta step instead, the case instantiated
    ///   at `v` with every copy it makes marked as its source is; the slots
    ///   threaded as [`Self::passing`] does; nothing when the condition or the
    ///   body did not lower.
    /// - provides: the minting half of [`Self::repeated`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::repeated`].
    /// - witness: `lower::loops::tests::a_while_tests_its_condition_on_every_pass`
    #[spec(ensures: |ret| match ret {
        | Maybe::Present(Lowered::Computation(id)) => sink.loops.contains(&id)
            || matches!(sink.arena.computation(id), Some(&Computation::Application(head, _)) if sink.loops.contains(&head)),
        | Maybe::Present(_) => false,
        | Maybe::Absent(_) => true,
    })]
    pub(super) fn mint_while(
        &self,
        condition: NodeIndex,
        body: Block,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let tested = match self.computation_at(condition) {
            Maybe::Present(tested) => tested,
            Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        let under = match self.mint_block(body, sink) {
            Maybe::Present(under) => under,
            Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        let inserted = origin.inserted(Insertion::Loop);
        let unit = sink.arena.value_unit();
        sink.origins.record_value(unit, inserted);
        let left = sink.arena.computation_return(unit);
        sink.origins.record_computation(left, inserted);
        let _break = sink.breaks.insert(left);
        let bound = sink
            .arena
            .value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        sink.origins.record_value(bound, inserted);
        let tests = sink.arena.computation_case(bound, &[under, left]);
        sink.origins.record_computation(tests, inserted);
        let tested = if let Some(&Computation::Return(value)) = sink.arena.computation(tested) {
            let mark = sink.arena.watermark();
            let mut carried = Vec::new();
            let instantiated =
                instantiate_computation_traced(sink.arena, tests, value, &mut carried);
            record_copies(sink, mark, &carried, inserted);
            mark_copies(sink, &carried);
            instantiated
        }
        else {
            let bound = sink.arena.computation_bind(tested, tests);
            sink.origins.record_computation(bound, inserted);
            bound
        };
        let id = self.passing(body, tested, sink, origin);

        Maybe::Present(sink.computation(id, origin))
    }

    /// The loop whose passes run `under`, the body of the loop whose block is
    /// `body`: `fix k. under` when the loop threads no slot; when it threads
    /// one, `(fix k. λ s. hold c = s; under) c`, and when it threads several,
    /// `(fix k. λ p. split p (s₁, …, sₙ); hold c₁ = s₁; …; hold cₙ = sₙ;
    /// under) (c₁, …, cₙ)`.
    ///
    /// # Specification
    /// - requires: `under` is minted under the frames [`Self::passes`] built
    ///   for the loop.
    /// - ensures: the fixpoint, partial and recorded as a loop, alone, or
    ///   applied to the slots recorded for `body`'s last computation, read
    ///   where the loop stands; the fixpoint at `origin` and every node the
    ///   threading adds marked as the loop's insertion; the caller records the
    ///   answer at `origin`.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a `while` threading one slot and one threading two.
    /// - witness: `lower::loops::tests::a_loop_threads_the_slots_it_names_through_its_passes`
    #[spec(ensures: |ret| sink.loops.contains(&ret)
        || matches!(sink.arena.computation(ret), Some(&Computation::Application(head, _)) if sink.loops.contains(&head)))]
    fn passing(
        &self,
        body: Block,
        under: ComputationId,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> ComputationId
    {
        let Some(carries) = self.carries.get(&body.last)
        else {
            let id = sink
                .arena
                .computation_fixpoint(under, FixpointEvidence::Partial);
            let _first = sink.loops.insert(id);
            return id;
        };
        let inserted = origin.inserted(Insertion::Loop);
        let count = carries.len();
        let mut held = under;
        for component in (0 .. count).rev() {
            let index = count.saturating_sub(1).saturating_sub(component);
            let content = sink.arena.value_variable(
                Zone::Intuitionistic,
                DeBruijnIndex::from(u32::try_from(index).unwrap_or(u32::MAX)),
            );
            sink.origins.record_value(content, inserted);
            held = sink.arena.computation_memory(MemoryForm::Hold {
                value: content,
                body: held,
                grade: gandr_core_term::memory::HoldGrade::Many,
            });
            sink.origins.record_computation(held, inserted);
        }
        if count > 1 {
            let passed = sink
                .arena
                .value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
            sink.origins.record_value(passed, inserted);
            held = sink
                .arena
                .computation_split(passed, ComponentCount::from(count), held);
            sink.origins.record_computation(held, inserted);
        }
        let each = sink.arena.computation_lambda(held);
        sink.origins.record_computation(each, inserted);
        let id = sink
            .arena
            .computation_fixpoint(each, FixpointEvidence::Partial);
        sink.origins.record_computation(id, origin);
        let _first = sink.loops.insert(id);
        let first = slots(carries.iter().copied(), sink, inserted);
        sink.arena.computation_application(id, first)
    }

    /// Mint a list loop stepping through `list` over `body`.
    ///
    /// # Specification
    /// - requires: the list and every node of `body` are already minted or
    ///   absent.
    /// - ensures: `(fix k. λ r. case r { nil => return (), cons(x, t) => b })
    ///   xs`, the fixpoint structural on `r`, at `origin` and recorded as a
    ///   loop, the application at `origin`, the lambda, the case and the empty
    ///   branch marked as the loop's insertion and the empty branch recorded as
    ///   a break; nothing when the list or the body did not lower.
    /// - provides: the minting half of [`Self::stepped`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::stepped`].
    /// - witness: `lower::loops::tests::a_for_steps_through_its_list`
    #[spec(ensures: |ret| match ret {
        | Maybe::Present(Lowered::Computation(id)) => matches!(sink.arena.computation(id),
            Some(&Computation::Application(head, _)) if sink.loops.contains(&head)),
        | Maybe::Present(_) => false,
        | Maybe::Absent(_) => true,
    })]
    pub(super) fn mint_for(
        &self,
        list: NodeIndex,
        body: Block,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let listed = match self.value_at(list) {
            Maybe::Present(listed) => listed,
            Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        let under = match self.mint_block(body, sink) {
            Maybe::Present(under) => under,
            Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        let inserted = origin.inserted(Insertion::Loop);
        let unit = sink.arena.value_unit();
        sink.origins.record_value(unit, inserted);
        let left = sink.arena.computation_return(unit);
        sink.origins.record_computation(left, inserted);
        let _break = sink.breaks.insert(left);
        let remaining = sink
            .arena
            .value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        sink.origins.record_value(remaining, inserted);
        let steps = sink.arena.computation_list_case(remaining, left, under);
        sink.origins.record_computation(steps, inserted);
        let each = sink.arena.computation_lambda(steps);
        sink.origins.record_computation(each, inserted);
        let id = sink
            .arena
            .computation_fixpoint(each, FixpointEvidence::StructuralDescent);
        sink.origins.record_computation(id, origin);
        let _first = sink.loops.insert(id);
        let applied = sink.arena.computation_application(id, listed);

        Maybe::Present(sink.computation(applied, origin))
    }
}
