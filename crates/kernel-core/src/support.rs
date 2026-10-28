//! The **support of one node check**: everything the checker's answer for a
//! single node depends on, and nothing else.
//!
//! # Why this is the whole soundness argument
//!
//! A memo is sound exactly when equal supports force equal answers. So a
//! support has to be the *complete* input to one goal expansion, and each
//! component below is here because dropping it would let two different
//! questions collide:
//!
//! - **the obligation's content** — not its arena id. Two structurally equal
//!   nodes are one question wherever they sit, which is what lets a re-minted
//!   spine reuse its untouched leaf, and it is what an identity key forfeits.
//! - **the direction, with the expected type** — checking a value against `A`
//!   and against `B` are different questions, and synthesis is a third.
//! - **the binder telescope's content** — variables are de Bruijn indices
//!   resolved against the machine's context, so the same node under two
//!   different contexts means two different things. Only the binders the goal's
//!   judgement read are folded in, each at its position, in telescope order so
//!   dependency order is part of the content.
//!
//! The key is therefore `(obligation content, telescope content, direction)`,
//! and it is **arena-free**: no arena id, no allocation order, and no binder
//! the judgement did not read reaches it. Content is named by the canonical
//! numbering [`SupportContext`] holds, so two structurally equal nodes key
//! alike however many arena positions spell them.
//!
//! The declaration's level parameters and the environment's admission log are
//! *not* in the key. They are fixed for the whole of one declaration's check,
//! and a memo never outlives that — see
//! [`check_declaration_with_memo`](crate::check::check_declaration_with_memo).
//!
//! # The read binders are the judgement's own output
//!
//! A goal's binders are not read off its node: the checking judgement derives
//! them. A machine opens an accrual on the session when it expands a goal
//! ([`SupportContext::open`]), every read of a binder's type joins the
//! innermost one open, and a goal's accrual joins the goal above it when it
//! closes, lowered past the binders the goal stood under. A goal's support is
//! therefore what its own expansion read and what its subgoals' supports name.
//! Two joins stand for work done elsewhere:
//!
//! - **an owed obligation** joins the support its node carries
//!   ([`TermArena::value_support`] and its three siblings), since the driver
//!   checks it later under the context it was owed at. A type's level reads no
//!   binder itself; the codes and arguments it owes do, so a formation goal's
//!   support is theirs.
//! - **a recalled goal** joins the support its entry was recorded under, since
//!   its subgoals never ran.
//!
//! A machine that swaps its context for one that does not extend it — a closed
//! payload, a component's own telescope — opens a barrier, and what is read
//! beyond it is dropped. A refusal never reaches the memo, so a read that
//! decides only a refusal — the context's length, which bounds a variable and
//! a binder's escape — reads no binder. **The failure direction is more
//! context in the key, never less**: a node the arena cannot resolve, a stage
//! witness scanned across the context, and a read at a context shallower than
//! the goal's own read every binder, which takes the whole context into the
//! key, so a defect here costs collapse and cannot manufacture a hit.
//!
//! # Recall reads the recorded binders against the asking context
//!
//! The binders are known only once the judgement has run, so a goal is asked
//! by its [`Question`] — its direction, obligation and expected type — and
//! every entry filed under the question is a candidate. An entry serves when
//! the record the asking context forms over the entry's binders is the entry's
//! own: the asking context agrees with the recorded one at every binder the
//! judgement read there.
//!
//! # References
//!
//! - `vault:01a178aa-6917-7983-b5cd-86e2af86b3ec` — lineage: the kernel takes
//!   the bicontextual judgement, so the support it keys by is the one it
//!   derives (§ kernel-reassessment-design item 3).
//! - `vault:01a12317-453f-7980-9c86-68f75917f3a6` — lineage: the support is the
//!   judgement's output, the binders it read, returned rather than read beside
//!   the check (§ bicontextual-judgement, § footprint-from-support).
//! - `vault:01a05203-4468-7931-8246-761a8f853a27` — lineage: the judgement
//!   synthesizes the context it consulted as its output, and the memo records
//!   its entry by it (§ successor-synthesized-context); here for the binders.

use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_check_memo::CheckMemo as _;
use gandr_kernel_check_memo::ContentAgreement;
use gandr_kernel_check_memo::ContentDigest;
use gandr_kernel_check_memo::DigestWord;
use gandr_kernel_check_memo::MemoEntryCount;
use gandr_kernel_check_memo::MemoKey;
use gandr_kernel_strata::Level;
use gandr_kernel_term::Binders;
use gandr_kernel_term::CompTypeId;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::Reads;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::ValueTypeId;
use gandr_kernel_term::WIDEST;
use gandr_kernel_term::read_indices;
use quenchant_shape::shape::Maybe;

use crate::element_identity::BinderUse;
use crate::encoding::ContentId;
use crate::encoding::ContentTable;
use crate::encoding::SupportGoal;
use crate::encoding::Telescope;
use crate::encoding::support_key;
use crate::rewrite::BinderDepth;
use crate::rewrite::RewriteMemo;
use crate::rewrite::RewritePlane;

/// The state one checking session derives its memo keys against.
///
/// It holds the canonical content numbering, the buffer one goal's read
/// binders are gathered in, and the goals open on its machines with the
/// binders each has read.
///
/// **The session is the memo's lifetime, made structural.** A support is
/// meaningful against the session that built it and against no other, so a
/// caller who wants to hand a memo an entry must build that entry through the
/// same session it then hands to the check. There is no way to mint a key that
/// outlives its call by accident.
#[derive(Clone, Debug, Default)]
pub struct SupportContext
{
    /// The canonical content numbering, the key's records among it.
    table: ContentTable,
    /// The read binders of the goal being keyed, reused across goals.
    read: Vec<(DeBruijnIndex, ValueTypeId)>,
    /// The session's shifting and substitution memo.
    rewrites: RewriteMemo,
    /// The goals open on the session's machines, innermost last.
    open: Vec<Accrual>,
}

/// One open goal and the binders its judgement has read so far, or a barrier.
#[derive(Clone, Debug)]
enum Accrual
{
    /// A goal expanded in a context `depth` binders deep, and the binders of
    /// that context its judgement has read, index `i` the binder `i` places
    /// out from the goal.
    Goal
    {
        /// The depth of the context the goal was expanded in.
        depth: BinderDepth,
        /// The binders read so far.
        reads: Reads,
    },
    /// The machine swapped its context for one that does not extend the open
    /// goal's, so nothing read until the barrier closes is a binder of it.
    Barrier,
}

/// Where an open accrual sits on its session's stack.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct Opened(usize);

/// How many binders `context` holds, saturating at the ceiling.
///
/// # Specification
/// trivial.
#[inline]
fn depth_of(context: &[ValueTypeId]) -> BinderDepth
{
    BinderDepth::from(u32::try_from(context.len()).unwrap_or(u32::MAX))
}

/// Join `reads`, read in a context `depth` binders deep, into the innermost
/// goal `open` holds, lowered past the binders the read stood under beyond it.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the innermost goal, opened `d` binders deep, gains each index
///   `reads` holds lowered by the binders between `d` and `depth`. It gains
///   every binder when `depth` is below `d`, when `depth` is at the ceiling, or
///   when `reads` reads every binder. A barrier innermost, or nothing open,
///   gains nothing; no accrual opens or closes.
/// - provides: every join an accrual takes: a read, a closed subgoal, a hit's
///   recorded support and an owed obligation's carried one.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a read at the goal's own depth, one under further
///   binders, one past a barrier and one shallower than the goal distinguish an
///   unlowered join, a leaking barrier and a narrowing fallback.
/// - witness: `support::tests::a_subgoal_s_reads_join_its_goal_lowered_past_its_binders`
/// - witness: `support::tests::a_barrier_drops_what_is_read_beyond_it`
#[spec(captures: count = open.len(), ensures: open.len() == count)]
#[inline]
fn accrue(
    open: &mut [Accrual],
    reads: &Reads,
    depth: BinderDepth,
)
{
    let Some(&mut Accrual::Goal {
        depth: at,
        reads: ref mut held,
    }) = open.last_mut()
    else {
        return;
    };
    if *reads == Reads::closed() {
        return;
    }
    // A context shallower than the goal's own is not one its judgement
    // extended, and a depth at the ceiling may stand for a deeper one, so
    // either read is taken as reading every binder.
    let seen = u32::from(depth)
        .checked_sub(u32::from(at))
        .filter(|_beyond| u32::from(depth) < u32::MAX)
        .map_or_else(
            || WIDEST.clone(),
            |beyond| reads.under(Binders::from(beyond)),
        );
    *held = core::mem::replace(held, Reads::closed()).join(&seen);
}

impl SupportContext
{
    /// A session over nothing.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new() -> Self
    {
        Self::default()
    }

    /// Name the constants of `entries` in this session's keys, as
    /// [`ContentTable::name_constants`] does: each plain definition by its
    /// content, every other constant by its position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn name_constants(
        &mut self,
        entries: &crate::env::Entries,
    )
    {
        self.table.name_constants(entries);
    }

    /// The two halves a rewrite needs: the content numbering its key is derived
    /// from, and the memo it records into.
    ///
    /// Handed over together because a rewrite borrows both at once and they are
    /// disjoint fields of one session — which is also the statement that a
    /// rewrite's memo lives exactly as long as the check that opened it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) const fn rewrite_parts(&mut self) -> (&mut ContentTable, &mut RewriteMemo)
    {
        (&mut self.table, &mut self.rewrites)
    }

    /// How many rewrites of `plane` this session has recorded.
    ///
    /// The two rewrites account separately, so a suite can pin the shifting
    /// machine's reuse without the substitution machine's numbers standing in
    /// for it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `|ret| ret == self.rewrites.plane_entry_count(plane)` — the
    ///   number of entries this session's rewrite memo holds on `plane`, one
    ///   per distinct rewritten `(content, depth)` pair.
    /// - provides: the per-plane accounting an acceptance case pins the two
    ///   wiring sites through.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the surface is the plane projection, separated by a
    ///   check that reaches both wiring sites and finds both planes non-empty.
    /// - witness: `tests::acceptance::the_rewrite_planes_account_separately_through_a_real_check`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret == self.rewrites.plane_entry_count(plane))]
    pub fn rewrite_entry_count(
        &self,
        plane: RewritePlane,
    ) -> MemoEntryCount
    {
        self.rewrites.plane_entry_count(plane)
    }

    /// Open an accrual for a goal expanded in `context`: every binder its
    /// judgement reads joins it until it closes.
    ///
    /// # Specification
    /// - requires: `context` is the one the goal is expanded in.
    /// - ensures: the goal's accrual is the innermost open, holding no binder,
    ///   and the returned position names it.
    /// - provides: the accrual [`Self::read`] joins and [`Self::close`]
    ///   returns.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`accrue`].
    /// - witness: `support::tests::a_subgoal_s_reads_join_its_goal_lowered_past_its_binders`
    #[spec(
        captures: count = self.open.len(),
        ensures: |ret| ret.0 == count && self.open.len() == count.saturating_add(1),
    )]
    #[inline]
    pub(crate) fn open(
        &mut self,
        context: &[ValueTypeId],
    ) -> Opened
    {
        let at = Opened(self.open.len());
        self.open.push(Accrual::Goal {
            depth: depth_of(context),
            reads: Reads::closed(),
        });
        at
    }

    /// Open a barrier: the machine is about to swap its context for one that
    /// does not extend the open goal's.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: until it closes, nothing read joins a goal opened before it;
    ///   the returned position names it.
    /// - provides: the swap to a closed payload's or a component's context.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`accrue`].
    /// - witness: `support::tests::a_barrier_drops_what_is_read_beyond_it`
    #[spec(
        captures: count = self.open.len(),
        ensures: |ret| ret.0 == count && self.open.len() == count.saturating_add(1),
    )]
    #[inline]
    pub(crate) fn open_barrier(&mut self) -> Opened
    {
        let at = Opened(self.open.len());
        self.open.push(Accrual::Barrier);
        at
    }

    /// Join `reads`, read in `context`, into the innermost open goal.
    ///
    /// # Specification
    /// - requires: `reads` indexes `context`.
    /// - ensures: as [`accrue`].
    /// - provides: a read of a binder's type, an owed obligation's support and
    ///   a recalled entry's.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`accrue`].
    /// - witness: `support::tests::a_subgoal_s_reads_join_its_goal_lowered_past_its_binders`
    #[spec(captures: count = self.open.len(), ensures: self.open.len() == count)]
    #[inline]
    pub(crate) fn read(
        &mut self,
        reads: &Reads,
        context: &[ValueTypeId],
    )
    {
        accrue(&mut self.open, reads, depth_of(context));
    }

    /// Close the accrual `opened` names, join it into the goal open around it,
    /// and return the binders its goal read.
    ///
    /// # Specification
    /// - requires: `opened` was returned by [`Self::open`] or
    ///   [`Self::open_barrier`] on this session.
    /// - ensures: every accrual opened after it closes into it first, so a
    ///   judgement that did not finish still counts what it read; it then
    ///   leaves the stack, its reads join the goal around it as [`accrue`]
    ///   does, and they are returned. A barrier returns no binder and joins
    ///   nothing. An accrual the stack does not hold returns every binder.
    /// - provides: a goal's support, the moment its judgement answers.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a goal closing over a subgoal left open, a barrier
    ///   and an accrual already gone distinguish a close that drops an
    ///   unfinished read, one that leaks a barrier and one that narrows.
    /// - witness: `support::tests::a_subgoal_s_reads_join_its_goal_lowered_past_its_binders`
    /// - witness: `support::tests::an_unfinished_subgoal_still_counts_what_it_read`
    /// - witness: `support::tests::a_barrier_drops_what_is_read_beyond_it`
    #[spec(
        captures: count = self.open.len(),
        ensures: self.open.len() == core::cmp::min(count, opened.0),
    )]
    #[inline]
    pub(crate) fn close(
        &mut self,
        opened: Opened,
    ) -> Reads
    {
        if self.open.len() <= opened.0 {
            return WIDEST.clone();
        }
        while self.open.len() > opened.0.saturating_add(1) {
            let _inner = self.close_innermost();
        }
        self.close_innermost()
    }

    /// Close the innermost accrual into the one around it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn close_innermost(&mut self) -> Reads
    {
        match self.open.pop() {
            Some(Accrual::Goal { depth, reads }) => {
                accrue(&mut self.open, &reads, depth);
                reads
            },
            Some(Accrual::Barrier) | None => Reads::closed(),
        }
    }

    /// Close every accrual unjoined, so a declaration's check opens on an
    /// empty stack whatever an earlier refusal left on it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn reset_accruals(&mut self)
    {
        self.open.clear();
    }
}

/// Whether `reads` reads the innermost binder, index zero.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`BinderUse::Ignored`] exactly when the set lists its indices and
///   zero is not among them; a set reading every binder reads it.
/// - provides: the condition a discarded call's continuation meets, and a
///   fixpoint that never recurses.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — sets on both sides of the word's width, with and without
///   zero, and a set reading every binder, each asserted.
/// - witness: `support::tests::index_zero_decides_the_innermost_binder`
#[spec(ensures: |ret| (ret == BinderUse::Ignored) == match reads.indices() {
    Maybe::Present(mut indices) => !indices.any(|index| index == DeBruijnIndex::from(0_u32)),
    Maybe::Absent(read_indices::Absent::Widest) => false,
})]
#[inline]
pub(crate) fn innermost(reads: &Reads) -> BinderUse
{
    let Maybe::Present(mut indices) = reads.indices()
    else {
        return BinderUse::Read;
    };
    if indices.next() == Some(DeBruijnIndex::from(0_u32)) {
        BinderUse::Read
    }
    else {
        BinderUse::Ignored
    }
}

/// Which of the two machines a support belongs to.
///
/// Admitting one declaration runs two iterative machines over the shared graph
/// — the checker's goal loop over the body and the type-formation walk over the
/// declared type. Each gets its own plane so entry counts are asserted
/// separately and neither machine's collapse hides behind the other's numbers.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum SupportPlane
{
    /// The checker's goal loop, over terms.
    Term,
    /// The type-formation walk, over types.
    Type,
}

/// What one goal expansion produced, as the memo stores it.
///
/// The four variants are the two machines' answers: the checker's produced
/// register, and the type-formation walk's level. They share one memo because
/// they share one lifetime — a declaration's check — and separating them would
/// buy nothing but a second type parameter. **A support carrying the wrong
/// shape is declined and recomputed rather than trusted**, which is what makes
/// sharing the memo safe rather than merely convenient.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum NodeOutcome
{
    /// A check succeeded; no type is carried.
    Checked,
    /// A value type was synthesized.
    ValueType(
        /// The synthesized type.
        ValueTypeId,
    ),
    /// A computation type was synthesized.
    CompType(
        /// The synthesized type.
        CompTypeId,
    ),
    /// A type formed at this level.
    Formed(
        /// The universe level.
        Level,
    ),
}

/// The machine a goal belongs to.
///
/// # Specification
/// trivial.
#[inline]
const fn plane_of(goal: SupportGoal) -> SupportPlane
{
    match goal {
        SupportGoal::ValueTypeLevel(_) | SupportGoal::CompTypeLevel(_) => SupportPlane::Type,
        SupportGoal::SynthValue(_)
        | SupportGoal::CheckValue(..)
        | SupportGoal::SynthComp(_)
        | SupportGoal::CheckComp(..) => SupportPlane::Term,
    }
}

/// The name of `goal`'s record under `context`, over the binders `reads`
/// names: the whole context when `reads` reads every binder or names one past
/// the context.
///
/// # Specification
/// - requires: `session` is this check's own.
/// - ensures: two names are equal exactly when the goals ask the same question
///   of equal content and find types of equal content at the same read
///   positions, or under whole contexts of equal content.
/// - provides: a recorded support's name, and the name a recall compares it
///   against.
/// - fails: never.
/// - panics: none.
/// - executable: none — the name is the session table's interning of the
///   record, which a predicate could restate only by interning it again.
///
/// # Adequacy
/// - hypothesis: L3 — as [`support_key`] and [`read_binders`].
/// - witness: `support::tests::a_recorded_binder_decides_which_context_is_served`
#[inline]
fn goal_name(
    arena: &TermArena,
    session: &mut SupportContext,
    goal: SupportGoal,
    context: &[ValueTypeId],
    reads: &Reads,
) -> ContentId
{
    let telescope = match read_binders(context, reads, &mut session.read) {
        Maybe::Present(read) => Telescope::Read(read),
        Maybe::Absent(_) => Telescope::Whole(context),
    };
    support_key(&mut session.table, arena, goal, telescope)
}

/// A goal's question: what it asks of which content against which expected
/// type, before its judgement has read a binder.
///
/// Every entry recorded for the question is filed under its digest, so a
/// recall walks the entries recorded under contexts that differed and serves
/// one the asking context agrees with.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct Question
{
    /// Which machine asked.
    plane: SupportPlane,
    /// The goal: its direction, obligation and expected type.
    goal: SupportGoal,
    /// The goal's record over no binder, named in the session's table.
    asked: ContentId,
}

impl Question
{
    /// Ask `goal`'s question in `session`.
    ///
    /// # Specification
    /// - requires: `session` is this check's own.
    /// - ensures: two questions take one name exactly when they ask the same
    ///   direction of equal content against equal expected types; no binder
    ///   reaches the name.
    /// - provides: the digest every entry for the goal is filed under.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the name is the session table's interning of the
    ///   record, which a predicate could restate only by interning it again.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`support_key`] over the empty telescope.
    /// - witness: `support::tests::a_recorded_binder_decides_which_context_is_served`
    #[inline]
    #[must_use]
    pub(crate) fn ask(
        arena: &TermArena,
        session: &mut SupportContext,
        goal: SupportGoal,
    ) -> Self
    {
        Self {
            plane: plane_of(goal),
            goal,
            asked: support_key(&mut session.table, arena, goal, Telescope::Read(&[])),
        }
    }

    /// The digest every entry recorded for this question is filed under.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub(crate) fn digest(self) -> ContentDigest
    {
        ContentDigest::new(DigestWord::from(self.plane), DigestWord::from(self.asked))
    }

    /// Whether `recorded` answers this question under `context`: it was
    /// recorded for this question, and `context` agrees with the context it
    /// was recorded under at every binder its judgement read.
    ///
    /// # Specification
    /// - requires: `recorded` and this question were built against `session`;
    ///   `context` is the asking goal's.
    /// - ensures: `ContentAgreement::Agree` exactly when `recorded` carries
    ///   this question and the record `context` forms over its read binders is
    ///   its own.
    /// - provides: the deciding comparison every hit the checker adopts is
    ///   served on.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — agreement interns the asking context's record in
    ///   the session's table, which a predicate could restate only by interning
    ///   it again.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an entry reading index one asked under a context
    ///   differing from its own at zero and at one, an entry reading every
    ///   binder, and an entry of another question.
    /// - witness: `support::tests::a_recorded_binder_decides_which_context_is_served`
    /// - witness: `support::tests::an_entry_reading_every_binder_is_served_its_own_context_alone`
    #[inline]
    #[must_use]
    pub(crate) fn agreement(
        self,
        arena: &TermArena,
        session: &mut SupportContext,
        context: &[ValueTypeId],
        recorded: &NodeSupport,
    ) -> ContentAgreement
    {
        if recorded.plane == self.plane
            && recorded.asked == self.asked
            && goal_name(arena, session, self.goal, context, &recorded.reads) == recorded.goal
        {
            ContentAgreement::Agree
        }
        else {
            ContentAgreement::Differ
        }
    }

    /// The support this question's goal answered under `context`, its
    /// judgement having read `reads`.
    ///
    /// # Specification
    /// - requires: `context` is the goal's, `reads` the binders of it the
    ///   goal's judgement read.
    /// - ensures: the support carries this question, `reads`, and the record
    ///   `context` forms over `reads`.
    /// - provides: the entry a check records once its judgement answers.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the record's name is the session table's interning,
    ///   which a predicate could restate only by interning it again.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::agreement`].
    /// - witness: `support::tests::a_recorded_binder_decides_which_context_is_served`
    #[inline]
    #[must_use]
    pub(crate) fn answered(
        self,
        arena: &TermArena,
        session: &mut SupportContext,
        context: &[ValueTypeId],
        reads: Reads,
    ) -> NodeSupport
    {
        let goal = goal_name(arena, session, self.goal, context, &reads);
        NodeSupport {
            plane: self.plane,
            asked: self.asked,
            reads,
            goal,
        }
    }
}

/// The complete support of one goal expansion: its question, the binders its
/// judgement read, and the name of its goal record over them.
///
/// The support holds no arena id: it carries names the session's content table
/// gives — the goal's question, and its record with the binders read — so two
/// supports agree exactly when they name one record, and the table names one
/// record exactly when the content agrees. The digest is read off the
/// question, so every entry recorded for one question shares a bucket.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NodeSupport
{
    /// Which machine asked.
    plane: SupportPlane,
    /// The goal's record over no binder: its question.
    asked: ContentId,
    /// The binders the goal's judgement read.
    reads: Reads,
    /// The goal's record over the binders read.
    goal: ContentId,
}

impl NodeSupport
{
    /// The support `goal` answers under `context` when its judgement read the
    /// binders `reads` names: the entry a check records, or one a caller
    /// plants.
    ///
    /// # Specification
    /// - requires: `context` is the machine's typing context at the expansion,
    ///   outermost first; `session` is this check's own, and every support a
    ///   memo holds was built against the same one.
    /// - ensures: two supports are equal exactly when the goals ask the same
    ///   question of the same content under binders that agree at every
    ///   position `reads` names. A `reads` reading every binder, or naming a
    ///   position past the context, takes the whole context, so an
    ///   over-estimate can only split a support and never merge two.
    /// - provides: the memo key, with the goal's plane checked by the
    ///   type-level entry so a support never crosses machines.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the names are the session table's interning, which
    ///   a predicate could restate only by interning them again.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — closed, binder-reading and type-formation goals under
    ///   agreeing and differing contexts.
    /// - witness: `support::tests::a_closed_node_takes_no_telescope`
    /// - witness: `support::tests::a_binder_reading_node_splits_on_what_it_reads`
    /// - witness: `support::tests::a_binder_reading_node_collapses_where_its_reads_agree`
    /// - witness: `support::tests::an_unread_binder_is_not_in_the_key`
    /// - witness: `support::tests::a_code_carrying_type_reads_its_binder`
    /// - witness: `support::tests::a_closed_type_goal_reads_no_binder`
    #[inline]
    #[must_use]
    pub fn recorded(
        arena: &TermArena,
        session: &mut SupportContext,
        goal: SupportGoal,
        context: &[ValueTypeId],
        reads: &Reads,
    ) -> Self
    {
        Question::ask(arena, session, goal).answered(arena, session, context, reads.clone())
    }

    /// The binders the goal's judgement read.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub(crate) const fn reads(&self) -> &Reads
    {
        &self.reads
    }
}

impl MemoKey for NodeSupport
{
    type Plane = SupportPlane;

    /// The plane this support was built on.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn plane(&self) -> Self::Plane
    {
        self.plane
    }

    /// The digest of this support: its plane, and its question's name, so
    /// every entry recorded for one question shares a bucket.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn digest(&self) -> ContentDigest
    {
        ContentDigest::new(DigestWord::from(self.plane), DigestWord::from(self.asked))
    }

    /// The deciding comparison between two recorded supports: their planes
    /// and their goal records' names, which the session's table assigns
    /// exactly when the records' content agrees.
    ///
    /// A recall decides by [`Question::agreement`] instead, against the
    /// asking context; this comparison is what a record replaces under.
    ///
    /// **The plane comparison is redundant and kept deliberately.** Deleting it
    /// is an inert mutation: the goal record carries the goal's direction, and
    /// the two type-formation directions draw from a disjoint part of that
    /// alphabet, so the names already separate the planes. The redundancy is
    /// defence in depth against a future direction tag that does not, and the
    /// plane field is load-bearing for *accounting* rather than for agreement.
    ///
    /// # Specification
    /// - requires: both supports were built against one session.
    /// - ensures: `ContentAgreement::Agree` exactly when the two supports carry
    ///   the same plane and name the same goal record.
    /// - provides: the comparison a record replaces an entry under.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 on equal and differing read binders, an unread binder
    ///   and disjoint planes; agreement observes the goal's content through its
    ///   name.
    /// - witness: `support::tests::a_binder_reading_node_splits_on_what_it_reads`
    /// - witness: `support::tests::a_binder_reading_node_collapses_where_its_reads_agree`
    /// - witness: `support::tests::an_unread_binder_is_not_in_the_key`
    /// - witness: `support::tests::a_term_support_never_agrees_with_a_type_support`
    #[spec(ensures: |ret| matches!(ret, ContentAgreement::Agree)
        == (self.plane == other.plane && self.goal == other.goal))]
    #[inline]
    fn agreement(
        &self,
        other: &Self,
    ) -> ContentAgreement
    {
        if self.plane == other.plane && self.goal == other.goal {
            ContentAgreement::Agree
        }
        else {
            ContentAgreement::Differ
        }
    }
}

impl From<SupportPlane> for DigestWord
{
    /// A plane as one digest word, so the two machines' supports fall in
    /// separate buckets.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(plane: SupportPlane) -> Self
    {
        Self::from(match plane {
            SupportPlane::Term => 0_u64,
            SupportPlane::Type => 1_u64,
        })
    }
}

quenchant_shape::reason_enum! {
    /// Why a support takes the whole context rather than the binders read.
    mod read_telescope {
        /// The node's reads do not place every binder it reads.
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        pub enum Absent {
            /// The node's support reads every binder.
            Unread,
            /// The node reads an index past the context.
            PastTheContext,
        }
    }
}

/// The binders `reads` names in `context`, gathered in `read`: each read index
/// beside the type of the binder it names, the indices ascending.
///
/// # Specification
/// - requires: nothing; `read`'s prior contents are discarded.
/// - ensures: for every index `i` that `reads` holds, `(i, context[len - 1 -
///   i])`, ascending; absent when `reads` is the widest reach or holds an index
///   at or past the context's length.
/// - provides: the telescope a support folds in, borrowed from `read`, which a
///   session reuses so that gathering allocates only when a goal reads more
///   binders than any before it.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 on reads inside, at and past the context's length and the
///   widest reach, gathered into a buffer holding an earlier read; exact
///   selections distinguish a reversed position, an off-by-one, a dropped index
///   and a stale member.
/// - witness: `support::tests::the_read_binders_are_placed_by_index`
#[spec(ensures: |ret| match (reads.indices(), &ret) {
    (Maybe::Present(indices), &Maybe::Present(gathered)) => indices.collect::<Vec<_>>()
        == gathered.iter().map(|&(index, _)| index).collect::<Vec<_>>()
        && gathered.iter().all(|&(index, entry)| usize::try_from(u32::from(index)).ok()
            .and_then(|index| context.len().checked_sub(index)?.checked_sub(1))
            .and_then(|position| context.get(position)) == Some(&entry)),
    (Maybe::Present(mut indices), &Maybe::Absent(read_telescope::Absent::PastTheContext)) => indices
        .any(|index| usize::try_from(u32::from(index)).map_or(true, |index| index >= context.len())),
    (Maybe::Absent(read_indices::Absent::Widest), &Maybe::Absent(read_telescope::Absent::Unread)) => true,
    _ => false,
})]
#[inline]
fn read_binders<'buffer>(
    context: &[ValueTypeId],
    reads: &Reads,
    read: &'buffer mut Vec<(DeBruijnIndex, ValueTypeId)>,
) -> Maybe<&'buffer [(DeBruijnIndex, ValueTypeId)], read_telescope::Absent>
{
    read.clear();
    let Maybe::Present(indices) = reads.indices()
    else {
        return Maybe::Absent(read_telescope::Absent::Unread);
    };
    for index in indices {
        let Some(&entry) = usize::try_from(u32::from(index))
            .ok()
            .and_then(|index| context.len().checked_sub(index)?.checked_sub(1))
            .and_then(|position| context.get(position))
        else {
            return Maybe::Absent(read_telescope::Absent::PastTheContext);
        };
        read.push((index, entry));
    }
    Maybe::Present(read.as_slice())
}

#[cfg(test)]
mod tests
{
    use gandr_kernel_check_memo::ContentAgreement;
    use gandr_kernel_check_memo::MemoKey as _;
    use gandr_kernel_strata::Level;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::Reads;
    use gandr_kernel_term::TermArena;
    use gandr_kernel_term::WIDEST;
    use quenchant_shape::shape::Maybe;

    use super::NodeSupport;
    use super::Question;
    use super::SupportContext;
    use super::SupportPlane;
    use super::innermost;
    use super::read_telescope;
    use crate::element_identity::BinderUse;
    use crate::encoding::SupportGoal;

    /// The set of the indices `indices`.
    ///
    /// # Specification
    /// trivial.
    fn reading<Index>(indices: &[Index]) -> Reads
    where
        Index: Copy,
        DeBruijnIndex: From<Index>,
    {
        indices.iter().fold(Reads::closed(), |reads, &index| {
            reads.join(&Reads::variable(DeBruijnIndex::from(index)))
        })
    }

    #[test]
    fn index_zero_decides_the_innermost_binder()
    {
        let mut arena = TermArena::new();
        let at =
            |arena: &mut TermArena, index: u32| arena.value_variable(DeBruijnIndex::from(index));
        let leaves = [0_u32, 3, 63, 64, 70].map(|index| at(&mut arena, index));
        let tuple = arena.value_tuple(&leaves);
        let body = arena.computation_return(tuple);
        let lambda = arena.computation_lambda(body);
        let [one, sixty_four] = [1_u32, 64].map(|index| at(&mut arena, index));
        let spilled = arena.value_tuple(&[one, sixty_four]);
        let zero = at(&mut arena, 0);
        let spilled_with_zero = arena.value_tuple(&[zero, sixty_four]);
        let floor = arena.watermark();
        let gone = arena.value_unit();
        arena.truncate_to(floor);
        for (reads, expected) in [
            (arena.value_support(tuple), BinderUse::Read),
            (arena.computation_support(lambda), BinderUse::Ignored),
            (arena.value_support(spilled), BinderUse::Ignored),
            (arena.value_support(spilled_with_zero), BinderUse::Read),
            (arena.value_support(gone), BinderUse::Read),
        ] {
            assert_eq!(
                expected,
                innermost(reads),
                "index zero decides the innermost binder in either form, and a set reading every \
                 binder reads it: {reads:?}"
            );
        }
    }

    #[test]
    fn a_closed_node_takes_no_telescope()
    {
        let mut arena = TermArena::new();
        let unit = arena.value_unit();
        let unit_type = arena.value_type_unit();
        let base = arena.value_type_base(BaseType::Integer);
        let mut session = SupportContext::new();
        let goal = SupportGoal::SynthValue(unit);
        let bare = NodeSupport::recorded(&arena, &mut session, goal, &[], &Reads::closed());
        let under = NodeSupport::recorded(
            &arena,
            &mut session,
            goal,
            &[unit_type, base],
            &Reads::closed(),
        );
        assert_eq!(
            ContentAgreement::Agree,
            bare.agreement(&under),
            "a goal that read no binder means the same thing under every context"
        );
        assert_eq!(SupportPlane::Term, bare.plane(), "and it is a term goal");
    }

    #[test]
    fn a_binder_reading_node_splits_on_what_it_reads()
    {
        let mut arena = TermArena::new();
        let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
        let unit_type = arena.value_type_unit();
        let base = arena.value_type_base(BaseType::Integer);
        let mut session = SupportContext::new();
        let goal = SupportGoal::SynthValue(variable);
        let under_unit =
            NodeSupport::recorded(&arena, &mut session, goal, &[unit_type], &reading(&[0]));
        let under_base = NodeSupport::recorded(&arena, &mut session, goal, &[base], &reading(&[0]));
        assert_eq!(
            ContentAgreement::Differ,
            under_unit.agreement(&under_base),
            "the same goal reading binders of different types is two entries"
        );
        assert_eq!(
            under_unit.digest(),
            under_base.digest(),
            "filed under its one question, where a recall finds both"
        );
    }

    #[test]
    fn a_binder_reading_node_collapses_where_its_reads_agree()
    {
        let mut arena = TermArena::new();
        let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
        let unit_type = arena.value_type_unit();
        let base = arena.value_type_base(BaseType::Integer);
        let mut session = SupportContext::new();
        let goal = SupportGoal::SynthValue(variable);
        let shallow =
            NodeSupport::recorded(&arena, &mut session, goal, &[unit_type], &reading(&[0]));
        let deep = NodeSupport::recorded(
            &arena,
            &mut session,
            goal,
            &[base, unit_type],
            &reading(&[0]),
        );
        assert_eq!(
            ContentAgreement::Agree,
            shallow.agreement(&deep),
            "only the binders read are in the key, so contexts agreeing where the judgement looked \
             are one entry"
        );
    }

    #[test]
    fn an_unread_binder_is_not_in_the_key()
    {
        let mut arena = TermArena::new();
        let variable = arena.value_variable(DeBruijnIndex::from(1_u32));
        let unit_type = arena.value_type_unit();
        let integer = arena.value_type_base(BaseType::Integer);
        let text = arena.value_type_base(BaseType::String);
        let mut session = SupportContext::new();
        let mut under = |context: &[_]| {
            NodeSupport::recorded(
                &arena,
                &mut session,
                SupportGoal::SynthValue(variable),
                context,
                &reading(&[1]),
            )
        };
        let over_unit = under(&[integer, unit_type]);
        let over_text = under(&[integer, text]);
        let elsewhere = under(&[text, unit_type]);
        assert_eq!(
            ContentAgreement::Agree,
            over_unit.agreement(&over_text),
            "a goal that read index one and not zero is one entry under contexts differing only \
             at zero"
        );
        assert_eq!(
            ContentAgreement::Differ,
            over_unit.agreement(&elsewhere),
            "and two where they differ at the index it read"
        );
    }

    /// A type-formation goal reads the binders the codes it owes read, as a
    /// term goal reads its own — so one type formed under two different
    /// binders is two entries rather than one.
    #[test]
    fn a_code_carrying_type_reads_its_binder()
    {
        let mut arena = TermArena::new();
        let code = arena.value_variable(DeBruijnIndex::from(0_u32));
        let element = arena.value_type_element(code, Level::zero());
        let unit_type = arena.value_type_unit();
        let base = arena.value_type_base(BaseType::Integer);
        let mut session = SupportContext::new();
        let goal = SupportGoal::ValueTypeLevel(element);
        let owed = arena.value_support(code).clone();
        let under_unit = NodeSupport::recorded(&arena, &mut session, goal, &[unit_type], &owed);
        let under_base = NodeSupport::recorded(&arena, &mut session, goal, &[base], &owed);
        assert_eq!(
            ContentAgreement::Differ,
            under_unit.agreement(&under_base),
            "the same code-carrying type under binders of different types is two entries"
        );
        assert_eq!(
            SupportPlane::Type,
            under_unit.plane(),
            "and both are accounted to the type-formation plane"
        );
    }

    #[test]
    fn a_closed_type_goal_reads_no_binder()
    {
        let mut arena = TermArena::new();
        let unit_type = arena.value_type_unit();
        let base = arena.value_type_base(BaseType::Integer);
        let mut session = SupportContext::new();
        let goal = SupportGoal::ValueTypeLevel(unit_type);
        let bare = NodeSupport::recorded(&arena, &mut session, goal, &[], &Reads::closed());
        let under = NodeSupport::recorded(
            &arena,
            &mut session,
            goal,
            &[base, unit_type],
            &Reads::closed(),
        );
        assert_eq!(
            ContentAgreement::Agree,
            bare.agreement(&under),
            "a type owing no code means the same thing under every context"
        );
        assert_eq!(
            SupportPlane::Type,
            bare.plane(),
            "and the type-formation walk accounts to its own plane"
        );
    }

    #[test]
    fn the_read_binders_are_placed_by_index()
    {
        let mut arena = TermArena::new();
        let unit = arena.value_type_unit();
        let base = arena.value_type_base(BaseType::Integer);
        let context = [unit, base];
        let at = |index: u32| DeBruijnIndex::from(index);
        let closed = arena.value_unit();
        let [zero, one, two] = [0_u32, 1, 2].map(|index| arena.value_variable(at(index)));
        let both = arena.value_tuple(&[one, zero]);
        let floor = arena.watermark();
        let gone = arena.value_unit();
        arena.truncate_to(floor);
        // The buffer holds an earlier goal's read, which gathering discards.
        let mut buffer = alloc::vec![(at(5), unit)];
        let mut read = |node| {
            super::read_binders(&context, arena.value_support(node), &mut buffer).map(<[_]>::to_vec)
        };
        assert_eq!(Maybe::Present(alloc::vec![]), read(closed));
        assert_eq!(
            Maybe::Present(alloc::vec![(at(0), base)]),
            read(zero),
            "index zero names the innermost binder"
        );
        assert_eq!(
            Maybe::Present(alloc::vec![(at(1), unit)]),
            read(one),
            "and the last index the outermost"
        );
        assert_eq!(
            Maybe::Present(alloc::vec![(at(0), base), (at(1), unit)]),
            read(both),
            "ascending by index"
        );
        assert_eq!(
            Maybe::Absent(read_telescope::Absent::PastTheContext),
            read(two),
            "an index past the context takes the whole context"
        );
        assert_eq!(
            Maybe::Absent(read_telescope::Absent::Unread),
            read(gone),
            "and so does a node whose support reads every binder"
        );
    }

    #[test]
    fn a_term_support_never_agrees_with_a_type_support()
    {
        let mut arena = TermArena::new();
        let unit = arena.value_unit();
        let unit_type = arena.value_type_unit();
        let mut session = SupportContext::new();
        let term = NodeSupport::recorded(
            &arena,
            &mut session,
            SupportGoal::SynthValue(unit),
            &[],
            &Reads::closed(),
        );
        let formation = NodeSupport::recorded(
            &arena,
            &mut session,
            SupportGoal::ValueTypeLevel(unit_type),
            &[],
            &Reads::closed(),
        );
        assert_eq!(
            ContentAgreement::Differ,
            term.agreement(&formation),
            "the two machines never answer for one another"
        );
    }

    #[test]
    fn a_subgoal_s_reads_join_its_goal_lowered_past_its_binders()
    {
        let binders = [TermArena::new().value_type_unit(); 4];
        let mut session = SupportContext::new();
        let goal = session.open(&binders[.. 2]);
        session.read(&reading(&[0]), &binders[.. 2]);
        let subgoal = session.open(&binders);
        // Index three under four binders is the goal's index one; index one is
        // a binder the goal's own expansion pushed, which the goal does not
        // read.
        session.read(&reading(&[1, 3]), &binders);
        assert_eq!(
            reading(&[1, 3]),
            session.close(subgoal),
            "the subgoal's own support is what it read"
        );
        assert_eq!(
            reading(&[0, 1]),
            session.close(goal),
            "and the goal's is its own read beside the subgoal's, lowered past the two binders \
             between them"
        );

        let shallow = session.open(&binders[.. 2]);
        session.read(&reading(&[0]), &binders[.. 1]);
        assert_eq!(
            WIDEST.clone(),
            session.close(shallow),
            "a read in a context shorter than the goal's is not one the goal extended, so it reads \
             every binder"
        );
        let gone = session.open(&binders[.. 1]);
        session.reset_accruals();
        assert_eq!(
            WIDEST.clone(),
            session.close(gone),
            "and an accrual the stack does not hold reads every binder rather than none"
        );
    }

    #[test]
    fn a_barrier_drops_what_is_read_beyond_it()
    {
        let binders = [TermArena::new().value_type_unit(); 3];
        let mut session = SupportContext::new();
        let goal = session.open(&binders[.. 1]);
        let barrier = session.open_barrier();
        let payload = session.open(&binders);
        session.read(&reading(&[0, 2]), &binders);
        assert_eq!(
            reading(&[0, 2]),
            session.close(payload),
            "a goal inside the swapped context still has its own support"
        );
        session.read(&reading(&[0]), &binders[.. 1]);
        assert_eq!(
            Reads::closed(),
            session.close(barrier),
            "the barrier itself reads nothing"
        );
        assert_eq!(
            Reads::closed(),
            session.close(goal),
            "and nothing read past it reaches the goal it was opened under"
        );
    }

    #[test]
    fn an_unfinished_subgoal_still_counts_what_it_read()
    {
        let binders = [TermArena::new().value_type_unit(); 2];
        let mut session = SupportContext::new();
        let goal = session.open(&binders[.. 1]);
        let _unfinished = session.open(&binders);
        session.read(&reading(&[1]), &binders);
        assert_eq!(
            reading(&[0]),
            session.close(goal),
            "a subgoal left open closes into its goal, so what it read still counts"
        );
    }

    #[test]
    fn a_recorded_binder_decides_which_context_is_served()
    {
        let mut arena = TermArena::new();
        let outer = arena.value_variable(DeBruijnIndex::from(1_u32));
        let inner = arena.value_variable(DeBruijnIndex::from(0_u32));
        let unit_type = arena.value_type_unit();
        let integer = arena.value_type_base(BaseType::Integer);
        let text = arena.value_type_base(BaseType::String);
        let mut session = SupportContext::new();
        let goal = SupportGoal::SynthValue(outer);
        let question = Question::ask(&arena, &mut session, goal);
        let recorded =
            question.answered(&arena, &mut session, &[integer, unit_type], reading(&[1]));
        assert_eq!(
            question.digest(),
            recorded.digest(),
            "the entry is filed under its question"
        );
        assert_eq!(
            ContentAgreement::Agree,
            question.agreement(&arena, &mut session, &[integer, text], &recorded),
            "a context agreeing at the binder the judgement read is served"
        );
        assert_eq!(
            ContentAgreement::Differ,
            question.agreement(&arena, &mut session, &[text, unit_type], &recorded),
            "one differing there is not"
        );
        assert_eq!(
            ContentAgreement::Differ,
            question.agreement(&arena, &mut session, &[unit_type], &recorded),
            "nor one too short to hold the binder"
        );
        let other = Question::ask(&arena, &mut session, SupportGoal::SynthValue(inner));
        assert_eq!(
            ContentAgreement::Differ,
            other.agreement(&arena, &mut session, &[integer, unit_type], &recorded),
            "and an entry for another question never answers"
        );
    }

    #[test]
    fn an_entry_reading_every_binder_is_served_its_own_context_alone()
    {
        let mut arena = TermArena::new();
        let unit = arena.value_unit();
        let unit_type = arena.value_type_unit();
        let integer = arena.value_type_base(BaseType::Integer);
        let text = arena.value_type_base(BaseType::String);
        let mut session = SupportContext::new();
        let question = Question::ask(&arena, &mut session, SupportGoal::SynthValue(unit));
        let recorded =
            question.answered(&arena, &mut session, &[integer, unit_type], WIDEST.clone());
        assert_eq!(
            ContentAgreement::Agree,
            question.agreement(&arena, &mut session, &[integer, unit_type], &recorded),
            "the context it was recorded under is served"
        );
        for context in [[integer, text], [text, unit_type]] {
            assert_eq!(
                ContentAgreement::Differ,
                question.agreement(&arena, &mut session, &context, &recorded),
                "and a context differing at any binder is not, though the node reads none"
            );
        }
    }
}
