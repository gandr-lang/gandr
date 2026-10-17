//! Loops: `loop`, `while`, `break` and `continue`, lowered into the fixpoint
//! former, whose body runs in the continuation the loop was entered with.
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
//! - In `b'`, every place a path through the body ends without an exit runs the
//!   loop again: `e` becomes `x ← e; split x (); force k`, the result discarded
//!   as a block's statement discards it, so it must be unit. `continue` is
//!   `force k` where it stands.
//! - `break(v)` is `return v` and a bare `break` is `return ()`, each a local
//!   end of the loop's own position: the commuting continues it with what
//!   follows the loop, or leaves it where the loop ends the body.
//!
//! The loop's own binder carries a name no identifier spells, so a written
//! name never resolves to it and `continue` finds the nearest one.
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
//! The fragment has no mutation: a loop's body sees the binders around the
//! loop, unchanged on every pass. State a loop carries is a recursive
//! function's parameter, or an effect's.
//!
//! # `for`
//!
//! - choice: `for x in xs { b }` is refused as
//!   [`LoweringRefusal::ForNeedsListCase`].
//! - alternatives: lowering through the native list's fold, which runs every
//!   element and so cannot leave at a `break`; or recursion over a list data
//!   declaration, which the native list the loop names is not.
//! - reversal: a case former on the native list, in the kernel and the core,
//!   lowers `for` as a `while` over the list's remaining tail (#283).

use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::ComponentCount;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::Zone;
use gandr_core_term::instantiate_computation_traced;
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
use crate::error::FragmentBoundary;
use crate::error::LoopExit;
use crate::error::LoweringRefusal;
use crate::form::Cursor;
use crate::form::TileName;
use crate::origin::Insertion;
use crate::origin::Origin;
use crate::resolve::Frame;
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

impl<'source> Lowerer<'_, 'source>
{
    /// Classify a loop, `loop { … }`.
    ///
    /// # Specification
    /// - requires: `site` is a `loop` in term position.
    /// - ensures: a loop standing as a computation where a path through a body
    ///   passes binds itself in a frame extending its own, reads its block
    ///   under that frame as a loop's body, and is planned over it.
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
                    && matches!(self.plans.get(usize::from(site.at.node)), Some(&Plan::Loop(body))
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
        let own = Frame::Inner(self.scope.extend(
            frame,
            iteration(),
            Maybe::Absent(binder_site::Absent::Unwritten),
        ));
        let body = self.block(site, &mut cursor, own)?;
        self.iterate(site, body)?;
        self.plan(site, Plan::Loop(body));

        Ok(())
    }

    /// Classify a conditional loop, `while c { … }`.
    ///
    /// # Specification
    /// - requires: `site` is a `while` in term position.
    /// - ensures: a `while` standing as a computation where a path through a
    ///   body passes binds itself in a frame extending its own, reads its
    ///   condition as a tested computation under that frame, reads its block as
    ///   a loop's body under two more, nameless binders, the bound condition
    ///   and the case's payload, and is planned over both.
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
                    && matches!(self.plans.get(usize::from(site.at.node)), Some(&Plan::While(condition, body))
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
        let own = Frame::Inner(self.scope.extend(
            frame,
            iteration(),
            Maybe::Absent(binder_site::Absent::Unwritten),
        ));
        let _tested = self.tested.insert(condition.node);
        self.read(condition.node, Reading::Computation(own));
        let mut held = own;
        for _binder in 0_u8 .. 2_u8 {
            held = Frame::Inner(self.scope.extend(
                held,
                SurfaceName::from(""),
                Maybe::Absent(binder_site::Absent::Unwritten),
            ));
        }
        let body = self.block(site, &mut cursor, held)?;
        self.iterate(site, body)?;
        self.plan(site, Plan::While(condition.node, body));

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
                    && matches!(self.plans.get(usize::from(site.at.node)), Some(&(Plan::Break | Plan::Return(_)))))
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
                    && matches!(self.plans.get(usize::from(site.at.node)), Some(&Plan::Reenter(_))))
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
        let Maybe::Present(own) = self.scope.index_of(frame, iteration(), &mut self.fuel)?
        else {
            return Err(LoweringRefusal::OutsideLoop {
                span: site.at.span,
                exit: LoopExit::Continue,
            });
        };
        let _exit = self.leaving.insert(site.at.node);
        self.plan(site, Plan::Reenter(own));

        Ok(())
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
    /// - ensures: `site` no longer ends a path; a form whose every path leaves
    ///   is left as it is; any other records the index its loop's binder has
    ///   under the binder of the result it discards, and either joins the body,
    ///   when a path through it leaves, so its local ends run the loop again,
    ///   or answers nothing, since its result is discarded.
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
        let Maybe::Present(own) =
            self.scope
                .index_of(site.reading.frame(), iteration(), &mut self.fuel)?
        else {
            return Err(LoweringRefusal::OutsideLoop {
                span: site.at.span,
                exit: LoopExit::Continue,
            });
        };
        let under = u32::from(own)
            .checked_add(1_u32)
            .map(DeBruijnIndex::from)
            .ok_or(LoweringRefusal::BudgetExceeded {
                budget: self.fuel.budget,
            })?;
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
    /// - requires: `own` is the index the loop's binder has under one more
    ///   binder at `position`; `end` is the node's bridged computation.
    /// - ensures: `x ← end; split x (); force own`, every inserted node at
    ///   `origin` marked as the loop's insertion, the force recorded as an
    ///   exit, and the bind recorded as distributed when a path through `end`
    ///   leaves.
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
        own: DeBruijnIndex,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> ComputationId
    {
        let inserted = origin.inserted(Insertion::Loop);
        let discarded = sink
            .arena
            .value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        sink.origins.record_value(discarded, inserted);
        let itself = sink.arena.value_variable(Zone::Intuitionistic, own);
        sink.origins.record_value(itself, inserted);
        let again = sink.arena.computation_force(itself);
        sink.origins.record_computation(again, inserted);
        let _exit = sink.exits.insert(again);
        let split = sink
            .arena
            .computation_split(discarded, ComponentCount::default(), again);
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
    /// - ensures: `fix k. b`, partial, at `origin`, recorded as a loop; nothing
    ///   when the body did not lower.
    /// - provides: the minting half of [`Self::looped`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::looped`].
    /// - witness: `lower::loops::tests::a_loop_lowers_to_a_partial_fixpoint_over_its_body`
    #[spec(ensures: |ret| match ret {
        | Maybe::Present(Lowered::Computation(id)) => sink.loops.contains(&id),
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
        let id = sink
            .arena
            .computation_fixpoint(under, FixpointEvidence::Partial);
        let _first = sink.loops.insert(id);

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
    ///   at `v` with every copy it makes marked as its source is; nothing when
    ///   the condition or the body did not lower.
    /// - provides: the minting half of [`Self::repeated`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::repeated`].
    /// - witness: `lower::loops::tests::a_while_tests_its_condition_on_every_pass`
    #[spec(ensures: |ret| match ret {
        | Maybe::Present(Lowered::Computation(id)) => sink.loops.contains(&id),
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
        let id = sink
            .arena
            .computation_fixpoint(tested, FixpointEvidence::Partial);
        let _first = sink.loops.insert(id);

        Maybe::Present(sink.computation(id, origin))
    }
}
