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
//! `check::check_declaration_with_memo`.
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

use alloc::collections::BTreeSet;
use alloc::sync::Arc;
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

use crate::encoding::ContentTable;
use crate::encoding::RecordName;
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
///
/// **An environment keeps one session for its life.** It lends each
/// admission's check a job's session: an overlay of its own, forked from the
/// session at the check's release ([`SupportContext::fork`]) and folded back at
/// its commit ([`SupportContext::join`]). The session's content table keeps the
/// names of the environment's nodes across admissions. So a later declaration
/// reads an earlier one's nodes by their existing names. A truncation of the
/// arena retires the names of the nodes that it drops. The session's kept memo
/// holds the content outcomes of earlier admissions. Each outcome is kept
/// under the parameters of its judgement, by names that read no content id, so
/// an outcome folds from a job's overlay unchanged. The declaration's memo,
/// the rewrite memo and the open accruals belong to each admission.
/// [`SupportContext::begin_admission`] starts them empty.
#[derive(Clone, Debug)]
pub struct SupportContext
{
    /// The canonical content numbering, the key's records among it. It names
    /// each record it admits fresh, so a definition's naming reads two names.
    table: ContentTable,
    /// The read binders of the goal being keyed, reused across goals.
    read: Vec<(DeBruijnIndex, ValueTypeId)>,
    /// The session's shifting and substitution memo.
    rewrites: RewriteMemo,
    /// The goals open on the session's machines, innermost last.
    open: Vec<Accrual>,
    /// The content outcomes the environment's earlier admissions answered.
    kept: KeptMemo,
    /// The names of the keys of the obligations this declaration's check owes.
    /// Its drain checks each of them before the declaration is admitted.
    owing: BTreeSet<(RecordName, RecordName)>,
}

impl Default for SupportContext
{
    /// A session over nothing, whose table names each record it admits.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self {
            table: ContentTable::named(),
            read: Vec::new(),
            rewrites: RewriteMemo::default(),
            open: Vec::new(),
            kept: KeptMemo::default(),
            owing: BTreeSet::new(),
        }
    }
}

/// One open goal, the binders its judgement has read so far and the keys of
/// the obligations it owes, or a barrier.
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
        /// The keys of the obligations owed so far, each one time.
        owed: Vec<NodeSupport>,
    },
    /// The machine swapped its context for one that does not extend the open
    /// goal's, so nothing read until the barrier closes is a binder of it.
    Barrier,
}

/// Where an open accrual sits on its session's stack.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Opened(usize);

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
        ..
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

/// Join `keys` into the innermost goal `open` holds, past every barrier above
/// it.
///
/// An obligation's key names its inputs by their content, so it holds in
/// every context. A barrier stops a read, but it does not stop a key. The
/// goal keeps each key one time when it closes, as
/// [`SupportContext::close_owing`] states.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the innermost goal gains each key of `keys`. Nothing open, or
///   only barriers, gains nothing. No accrual opens or closes.
/// - provides: every key a goal owes: its own obligations, a closed subgoal's
///   and a recalled entry's.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a key owed under a barrier and a key owed two times
///   distinguish a barrier that drops a key and a close that repeats one.
/// - witness: `support::tests::an_owed_key_passes_a_barrier_and_joins_one_time`
#[spec(captures: count = open.len(), ensures: open.len() == count)]
#[inline]
fn owe_into(
    open: &mut [Accrual],
    keys: &[NodeSupport],
)
{
    if let Some(held) = open.iter_mut().rev().find_map(|accrual| match *accrual {
        Accrual::Goal { ref mut owed, .. } => Some(owed),
        Accrual::Barrier => None,
    }) {
        held.extend_from_slice(keys);
    }
}

/// Whether the obligation a key names lets a recall serve: its verdict holds,
/// or the check that recalls owes it already.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Discharge
{
    /// The key holds a checked verdict, or this declaration's check owes it,
    /// so its drain checks it before the declaration is admitted.
    Held,
    /// The key holds no such verdict, so a recall that owes it declines.
    Open,
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
    pub fn name_constants(
        &mut self,
        entries: &crate::env::Entries,
    )
    {
        self.table.name_constants(entries);
    }

    /// The session's table, to name a definition or to lend a fold that names
    /// each image at mint.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn table_mut(&mut self) -> &mut ContentTable
    {
        &mut self.table
    }

    /// Open an admission's check on this session: its rewrite memo, its open
    /// accruals, the obligations it owes and its read buffer start empty, and
    /// the table keeps the names it holds.
    ///
    /// The rewrite memo answers with arena ids, which the previous admission's
    /// truncation may have dropped, so it is each admission's own.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn begin_admission(&mut self)
    {
        self.rewrites = RewriteMemo::new();
        self.open.clear();
        self.owing.clear();
        self.read.clear();
    }

    /// This session for an environment that continues this one's arena: the
    /// same content table and kept memo, and an empty rewrite memo, open
    /// accruals and read buffer, as [`Self::begin_admission`] leaves them.
    ///
    /// The copy's arena holds the nodes that this session names, so each name
    /// and each kept outcome holds there as here.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn carried(&self) -> Self
    {
        Self {
            table: self.table.clone(),
            kept: self.kept.clone(),
            ..Self::default()
        }
    }

    /// Open a job's session at this fork point: an overlay of this session's
    /// table and kept memo, read by reference, and the job's own rewrite memo,
    /// accruals and owed keys, empty.
    ///
    /// # Specification
    /// - requires: `arena` is the arena this session names nodes of, and the
    ///   job names nodes of it or of a clone of it.
    /// - ensures: the job gives each node and record the name this session
    ///   gives it, and recalls each kept outcome this session recalls.
    /// - provides: the session a forked job checks in.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the names and recalls are those of the table and
    ///   the kept memo, whose own specifications check them.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::join`].
    /// - witness: `support::tests::two_jobs_folded_in_either_order_recall_what_a_serial_session_recalls`
    #[must_use]
    #[inline]
    pub fn fork(
        &mut self,
        arena: &TermArena,
    ) -> Self
    {
        Self {
            table: self.table.fork(arena),
            read: Vec::new(),
            rewrites: RewriteMemo::new(),
            open: Vec::new(),
            kept: self.kept.fork(),
            owing: BTreeSet::new(),
        }
    }

    /// Merge the frozen layers of this session's table and kept memo, as
    /// [`ContentTable::compact`] and the memo's compaction merge them. A
    /// session that forks a job at each release, while jobs stay open,
    /// keeps its layers to the open jobs and a logarithm of its records and
    /// outcomes, so each join and each recall reads as many.
    ///
    /// # Specification
    /// - requires: `arena` is the arena this session names nodes of.
    /// - ensures: the session gives each node and record the name it gave them,
    ///   recalls each kept outcome it recalled, and each open job joins as it
    ///   joined before.
    /// - provides: the bound on the layers of the environment's session.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — as the table's and the memo's compactions.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the table's and the memo's compactions.
    /// - witness: `encoding::tests::a_table_that_forks_without_a_break_keeps_its_layers_to_a_logarithm_7335`
    /// - witness: `gandr-kernel-core::environment::tests::each_commit_order_of_a_released_source_folds_as_the_serial_run_3476`
    #[inline]
    pub fn compact(
        &mut self,
        arena: &TermArena,
    )
    {
        self.table.compact(arena);
        self.kept.compact();
    }

    /// Fold `job`, a session forked from this one, into it: the records it
    /// named and the outcomes it kept, in the order it named and kept them.
    /// Its rewrite memo, accruals and owed keys belong to the job and go.
    ///
    /// # Specification
    /// - requires: `job` was forked from this session, or from one it overlays;
    ///   `arena` is this session's arena. The caller folds the jobs of one fork
    ///   point in their order.
    /// - ensures: as [`ContentTable::join`] and the kept memo's join, each of
    ///   which settles first.
    /// - provides: the fold of a job's session at its commit.
    /// - fails: the job kept an outcome under a key that this session kept with
    ///   another outcome since the job's fork.
    /// - panics: none.
    /// - executable: none — as [`ContentTable::join`], the job's records and
    ///   outcomes leave with the fold.
    ///
    /// # Errors
    /// [`crate::KernelError::KeptOutcomesDisagree`], naming the key by its
    /// content digest and both outcomes. The session then holds the job's
    /// records and none of its outcomes.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two jobs forked at one point, each keeping an outcome
    ///   over a record the other names, folded in either order; the session
    ///   recalls each outcome under the name a serial session gives it.
    /// - witness: `support::tests::two_jobs_folded_in_either_order_recall_what_a_serial_session_recalls`
    /// - witness: `support::tests::two_jobs_that_keep_two_outcomes_under_one_key_do_not_glue`
    #[inline]
    pub fn join(
        &mut self,
        arena: &TermArena,
        job: Self,
    ) -> Result<(), crate::KernelError>
    {
        let Self { table, kept, .. } = job;
        self.table.join(arena, table);
        self.kept.join(kept, |_, _| true).map_err(|disagreement| {
            let (key, held, offered) = disagreement.into_parts();
            crate::KernelError::KeptOutcomesDisagree(alloc::boxed::Box::new(
                crate::error::KeptOutcomes::new(key.digest(), held, offered),
            ))
        })
    }

    /// Name `parameters` in this session's table, as
    /// [`ContentTable::parameters`] does, and read the record's name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn name_parameters(
        &mut self,
        arena: &TermArena,
        parameters: &crate::encoding::Parameters<'_>,
    ) -> RecordName
    {
        let id = self.table.parameters(arena, parameters);
        self.table.key_name(id)
    }

    /// Recall `question` from the kept memo under `parameters`, asked in
    /// `context`. The result is the outcome of an earlier admission. Its
    /// binders are read here as if its walk had run.
    ///
    /// # Specification
    /// - requires: `question` was asked in this session. `parameters` names the
    ///   asking judgement's parameters in it.
    /// - ensures: an outcome kept for this question under these parameters,
    ///   whose recorded binders agree with `context`. Its reads join the
    ///   innermost open goal. None when no such entry is kept.
    /// - provides: the recall a walk takes on a miss of its declaration's memo.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — agreement interns the asking context's record. A
    ///   predicate could restate it only by interning it again.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Question::agreement`], over entries that earlier
    ///   admissions of generated environments keep. The environments reuse
    ///   refused positions. The reference checks each declaration on an empty
    ///   session.
    /// - witness: `gandr-kernel-core::environment::tests::kept_outcomes_leave_every_verdict_as_fresh_sessions_give`
    /// - witness: `gandr-kernel-core::environment::tests::a_refused_data_declaration_s_outcomes_do_not_answer_its_successor`
    #[inline]
    pub fn recall_kept(
        &mut self,
        arena: &TermArena,
        question: Question,
        context: &[ValueTypeId],
        parameters: RecordName,
    ) -> Option<NodeOutcome>
    {
        let kept = core::mem::take(&mut self.kept);
        let recalled = kept
            .filed(kept_digest(question.asked, parameters))
            .find(|hit| {
                hit.support().parameters == parameters
                    && matches!(
                        question.agreement(arena, self, context, &hit.support().support),
                        ContentAgreement::Agree
                    )
            })
            .map(|hit| {
                self.read(&hit.support().support.reads, context);
                hit.outcome().clone()
            });
        self.kept = kept;
        recalled
    }

    /// Whether an earlier admission kept `key` as checked under `parameters`.
    ///
    /// # Specification
    /// - requires: `key` was built in this session. `parameters` names the
    ///   asking judgement's parameters in it.
    /// - ensures: [`Discharge::Held`] exactly when the kept memo holds `key`
    ///   under `parameters` with a checked outcome.
    /// - provides: the probe a recalled formation takes of each obligation it
    ///   owes.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the answer is a probe of the kept memo. A predicate
    ///   could restate it only by probing the memo again.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a formation kept by a refused admission and recalled
    ///   by a later one, whose obligation the later one refuses.
    /// - witness: `gandr-kernel-core::tests::memo_order::a_refused_obligation_does_not_answer_a_later_declaration_6869`
    #[inline]
    #[must_use]
    pub fn kept_checked(
        &self,
        key: &NodeSupport,
        parameters: RecordName,
    ) -> Discharge
    {
        let held = self
            .kept
            .filed(kept_digest(key.asked, parameters))
            .any(|hit| {
                hit.support().parameters == parameters
                    && hit.support().support == *key
                    && *hit.outcome() == NodeOutcome::Checked
            });
        if held {
            Discharge::Held
        }
        else {
            Discharge::Open
        }
    }

    /// Keep `outcome` as `support`'s answer under `parameters` when it is
    /// content. Content is a check that succeeded or a level that a type
    /// formed at.
    ///
    /// # Specification
    /// - requires: `support` was answered in this session under the parameters
    ///   `parameters` names.
    /// - ensures: a checked or formed outcome is kept unless the kept memo is
    ///   at its ceiling. It replaces an entry that agrees with it. A
    ///   synthesized type names arena nodes. It is not kept.
    /// - provides: what a later admission recalls.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the kept memo's ceiling decides. A predicate could
    ///   restate it only by reading its accounting.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::recall_kept`].
    /// - witness: `gandr-kernel-core::environment::tests::kept_outcomes_leave_every_verdict_as_fresh_sessions_give`
    #[inline]
    pub fn keep(
        &mut self,
        support: &NodeSupport,
        parameters: RecordName,
        outcome: &NodeOutcome,
    )
    {
        if matches!(*outcome, NodeOutcome::Checked | NodeOutcome::Formed(..)) {
            let _recorded = self.kept.remember(
                KeptSupport {
                    support: support.clone(),
                    parameters,
                },
                outcome.clone(),
            );
        }
    }

    /// How this session's table names the constant at `index`, as
    /// [`ContentTable::constant_name`] reads it.
    ///
    /// # Specification
    /// trivial.
    #[cfg(any(test, feature = "fixture"))]
    pub(crate) fn constant_name(
        &self,
        index: gandr_kernel_term::ConstantIndex,
    ) -> Option<crate::encoding::ConstantName>
    {
        self.table.constant_name(index)
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
    pub const fn rewrite_parts(&mut self) -> (&mut ContentTable, &mut RewriteMemo)
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
    /// - witness: `gandr-kernel-core::tests::acceptance::the_rewrite_planes_account_separately_through_a_real_check`
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
    pub fn open(
        &mut self,
        context: &[ValueTypeId],
    ) -> Opened
    {
        let at = Opened(self.open.len());
        self.open.push(Accrual::Goal {
            depth: depth_of(context),
            reads: Reads::closed(),
            owed: Vec::new(),
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
    pub fn open_barrier(&mut self) -> Opened
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
    pub fn read(
        &mut self,
        reads: &Reads,
        context: &[ValueTypeId],
    )
    {
        accrue(&mut self.open, reads, depth_of(context));
    }

    /// Join `keys` into the innermost open goal, past every barrier.
    ///
    /// # Specification
    /// - requires: each key was built in this session.
    /// - ensures: as [`owe_into`].
    /// - provides: a recalled formation's keys.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`owe_into`].
    /// - witness: `support::tests::an_owed_key_passes_a_barrier_and_joins_one_time`
    #[spec(captures: count = self.open.len(), ensures: self.open.len() == count)]
    #[inline]
    pub fn owe(
        &mut self,
        keys: &[NodeSupport],
    )
    {
        owe_into(&mut self.open, keys);
    }

    /// Owe the obligation `key` names: join it into the innermost open goal,
    /// past every barrier, and hold it as owed by this declaration's check.
    ///
    /// # Specification
    /// - requires: `key` was built in this session, and the obligation it names
    ///   joins the worklist that this declaration's drain checks.
    /// - ensures: as [`owe_into`], and [`Self::owes`] holds for `key` until the
    ///   next declaration's check opens.
    /// - provides: the formation walk's key of each obligation it owes.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a formation recalled twice in one declaration whose
    ///   drain refuses the obligation, and the same formation in a later
    ///   declaration.
    /// - witness: `gandr-kernel-core::tests::memo_order::a_refused_obligation_does_not_answer_a_later_declaration_6869`
    #[spec(captures: count = self.open.len(), ensures: self.open.len() == count)]
    #[inline]
    pub fn owe_obligation(
        &mut self,
        key: &NodeSupport,
    )
    {
        let _new = self.owing.insert(key.names());
        owe_into(&mut self.open, core::slice::from_ref(key));
    }

    /// Whether this declaration's check owes the obligation `key` names, so
    /// that its drain checks it before the declaration is admitted.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn owes(
        &self,
        key: &NodeSupport,
    ) -> Discharge
    {
        if self.owing.contains(&key.names()) {
            Discharge::Held
        }
        else {
            Discharge::Open
        }
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
    pub fn close(
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
        self.close_innermost().0
    }

    /// Close the accrual `opened` names, as [`Self::close`] does, and return
    /// the binders its goal read with the keys of the obligations it owes.
    ///
    /// # Specification
    /// - requires: as [`Self::close`].
    /// - ensures: as [`Self::close`]. The keys join the goal around it as
    ///   [`owe_into`] does, and they are returned, each one time. An accrual
    ///   the stack does not hold returns none: its keys are lost, so no entry
    ///   may record it.
    /// - provides: a formation's support and the keys its entry carries.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`owe_into`].
    /// - witness: `support::tests::an_owed_key_passes_a_barrier_and_joins_one_time`
    #[spec(
        captures: count = self.open.len(),
        ensures: self.open.len() == core::cmp::min(count, opened.0),
    )]
    #[inline]
    pub fn close_owing(
        &mut self,
        opened: Opened,
    ) -> Option<(Reads, Owed)>
    {
        if self.open.len() <= opened.0 {
            return None;
        }
        while self.open.len() > opened.0.saturating_add(1) {
            let _inner = self.close_innermost();
        }
        let (reads, mut owed) = self.close_innermost();
        owed.sort_unstable_by_key(NodeSupport::names);
        owed.dedup_by_key(|key| key.names());
        Some((reads, Owed((!owed.is_empty()).then(|| owed.into()))))
    }

    /// Close the innermost accrual into the one around it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn close_innermost(&mut self) -> (Reads, Vec<NodeSupport>)
    {
        match self.open.pop() {
            Some(Accrual::Goal { depth, reads, owed }) => {
                accrue(&mut self.open, &reads, depth);
                owe_into(&mut self.open, &owed);
                (reads, owed)
            },
            Some(Accrual::Barrier) | None => (Reads::closed(), Vec::new()),
        }
    }

    /// Close every accrual unjoined and forget the obligations owed, so a
    /// declaration's check opens on an empty stack whatever an earlier refusal
    /// left on it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn reset_accruals(&mut self)
    {
        self.open.clear();
        self.owing.clear();
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
#[must_use]
pub fn innermost(reads: &Reads) -> BinderUse
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
    /// A type formed at this level, and its formation owes these
    /// obligations.
    Formed(
        /// The universe level.
        Level,
        /// The keys of the obligations the formation owes.
        Owed,
    ),
}

/// The keys of the obligations that a formation owes the checker, each one
/// time.
///
/// A recall of the formation serves its level only when each key holds a
/// checked outcome. A key with no checked outcome makes the recall decline,
/// and the formation expands and owes its obligations again. A formation
/// that owes nothing holds no allocation.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Owed(Option<Arc<[NodeSupport]>>);

impl Owed
{
    /// A formation that owes nothing.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn none() -> Self
    {
        Self(None)
    }

    /// The keys, each one time.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn keys(&self) -> &[NodeSupport]
    {
        self.0.as_deref().unwrap_or(&[])
    }
}

/// The machine a goal belongs to.
///
/// An obligation's verdict is the checking machine's answer, so its key is a
/// term-plane key.
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
        | SupportGoal::CheckComp(..)
        | SupportGoal::Obligation(_) => SupportPlane::Term,
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
///   positions, or under whole contexts of equal content. The name reads no
///   content id, so it is the same in each table that holds the record.
/// - provides: a recorded support's name, and the name a recall compares it
///   against.
/// - fails: never.
/// - panics: none.
/// - executable: none — the name is the session table's naming of the record,
///   which a predicate could restate only by interning it again.
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
) -> RecordName
{
    let telescope = match read_binders(context, reads, &mut session.read) {
        Maybe::Present(read) => Telescope::Read(read),
        Maybe::Absent(_) => Telescope::Whole(context),
    };
    let id = support_key(&mut session.table, arena, goal, telescope);
    session.table.key_name(id)
}

/// A goal's question: what it asks of which content against which expected
/// type, before its judgement has read a binder.
///
/// Every entry recorded for the question is filed under its digest, so a
/// recall walks the entries recorded under contexts that differed and serves
/// one the asking context agrees with.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Question
{
    /// Which machine asked.
    plane: SupportPlane,
    /// The goal: its direction, obligation and expected type.
    goal: SupportGoal,
    /// The name of the goal's record over no binder.
    asked: RecordName,
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
    pub fn ask(
        arena: &TermArena,
        session: &mut SupportContext,
        goal: SupportGoal,
    ) -> Self
    {
        let id = support_key(&mut session.table, arena, goal, Telescope::Read(&[]));
        Self {
            plane: plane_of(goal),
            goal,
            asked: session.table.key_name(id),
        }
    }

    /// The digest every entry recorded for this question is filed under.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn digest(self) -> ContentDigest
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
    pub fn agreement(
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
    pub fn answered(
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
/// The support holds no arena id and no content id: it carries the names the
/// session's content table gives — the goal's question, and its record with the
/// binders read. Two supports agree exactly when they carry one name, and two
/// records take one name, up to a BLAKE3 collision, exactly when their content
/// agrees. So a support folds from one table into another unchanged. The digest
/// is read off the question, so every entry recorded for one question shares a
/// bucket.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NodeSupport
{
    /// Which machine asked.
    plane: SupportPlane,
    /// The name of the goal's record over no binder: its question.
    asked: RecordName,
    /// The binders the goal's judgement read.
    reads: Reads,
    /// The name of the goal's record over the binders read.
    goal: RecordName,
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
    pub const fn reads(&self) -> &Reads
    {
        &self.reads
    }

    /// The two names that identify this support among the supports of one
    /// plane: its question and its goal record over the binders read.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn names(&self) -> (RecordName, RecordName)
    {
        (self.asked, self.goal)
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

/// A support that the kept memo files. It is the goal's support and the name
/// of the judgement's parameters.
///
/// The goal's support carries the question and the binders read. The
/// parameters carry what the judgement holds beside them. They are its level
/// context, manifest, laws, block, fixpoints and partiality. They can differ
/// between declarations. They never differ within one walk.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct KeptSupport
{
    /// The goal's support.
    support: NodeSupport,
    /// The name of the judgement's parameters in the session's table.
    parameters: RecordName,
}

impl MemoKey for KeptSupport
{
    type Plane = SupportPlane;

    /// The plane the goal's support was built on.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn plane(&self) -> Self::Plane
    {
        self.support.plane
    }

    /// The digest of the question and the parameters. Every entry kept for one
    /// question under one parameter set shares a bucket.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn digest(&self) -> ContentDigest
    {
        kept_digest(self.support.asked, self.parameters)
    }

    /// The deciding comparison between two kept supports. Their goals'
    /// supports must agree. They must name one parameter set.
    ///
    /// # Specification
    /// - requires: both supports were built against one session.
    /// - ensures: `ContentAgreement::Agree` exactly when the goals' supports
    ///   agree and the parameters' names are one.
    /// - provides: the comparison that a kept record replaces an entry under.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`ContentTable::parameters`]. One goal kept under
    ///   two parameter sets takes two entries.
    /// - witness: `gandr-kernel-core::environment::tests::a_refused_data_declaration_s_outcomes_do_not_answer_its_successor`
    #[spec(ensures: |ret| matches!(ret, ContentAgreement::Agree)
        == (matches!(self.support.agreement(&other.support), ContentAgreement::Agree)
            && self.parameters == other.parameters))]
    #[inline]
    fn agreement(
        &self,
        other: &Self,
    ) -> ContentAgreement
    {
        if self.parameters == other.parameters {
            self.support.agreement(&other.support)
        }
        else {
            ContentAgreement::Differ
        }
    }
}

/// The digest every entry kept for the question named `asked` under the
/// parameters named `parameters` is filed under.
///
/// # Specification
/// trivial.
#[inline]
fn kept_digest(
    asked: RecordName,
    parameters: RecordName,
) -> ContentDigest
{
    ContentDigest::new(DigestWord::from(asked), DigestWord::from(parameters))
}

/// The memo that an environment keeps across its declarations. It holds only
/// content outcomes. Each is kept under the parameters of its judgement. A
/// job keeps into an overlay of it, which its commit folds.
pub(crate) type KeptMemo = gandr_kernel_check_memo::OverlaidMemo<KeptSupport, NodeOutcome>;

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

/// What a family does with its innermost binder.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BinderUse
{
    /// The family provably ignores variable zero.
    Ignored,
    /// The family may read variable zero.
    Read,
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
    use crate::encoding::SupportGoal;
    use crate::support::BinderUse;

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
    fn two_jobs_folded_in_either_order_recall_what_a_serial_session_recalls()
    {
        let mut arena = TermArena::new();
        let unit = arena.value_type_unit();
        let integer = arena.value_type_base(BaseType::Integer);
        let left = arena.value_type_product(&[unit, integer]);
        let right = arena.value_type_product(&[integer, unit]);
        let goals = [
            SupportGoal::ValueTypeLevel(left),
            SupportGoal::ValueTypeLevel(right),
        ];
        let mut serial = SupportContext::new();
        let keys = goals
            .map(|goal| NodeSupport::recorded(&arena, &mut serial, goal, &[], &Reads::closed()));
        for swapped in [false, true] {
            let mut session = SupportContext::new();
            let _before = NodeSupport::recorded(
                &arena,
                &mut session,
                SupportGoal::ValueTypeLevel(unit),
                &[],
                &Reads::closed(),
            );
            let mut jobs = [session.fork(&arena), session.fork(&arena)];
            for (job, goal) in jobs.iter_mut().zip(goals) {
                let key = NodeSupport::recorded(&arena, job, goal, &[], &Reads::closed());
                job.keep(&key, key.names().0, &super::NodeOutcome::Checked);
            }
            if swapped {
                jobs.reverse();
            }
            for job in jobs {
                session
                    .join(&arena, job)
                    .expect("two jobs that keep two keys glue");
            }
            for key in &keys {
                assert_eq!(
                    session.kept_checked(key, key.names().0),
                    super::Discharge::Held,
                    "the session recalls each job's outcome under the serial key, swapped: {swapped}"
                );
            }
            assert_eq!(
                goals.map(|goal| NodeSupport::recorded(
                    &arena,
                    &mut session,
                    goal,
                    &[],
                    &Reads::closed()
                )),
                keys,
                "the folded session names each goal as a serial session names it, swapped: {swapped}"
            );
        }
    }

    #[test]
    fn two_jobs_that_keep_two_outcomes_under_one_key_do_not_glue()
    {
        let mut arena = TermArena::new();
        let goal = SupportGoal::ValueTypeLevel(arena.value_type_unit());
        let outcomes = [
            super::NodeOutcome::Checked,
            super::NodeOutcome::Formed(Level::zero(), super::Owed::none()),
        ];
        let mut session = SupportContext::new();
        let mut jobs = [session.fork(&arena), session.fork(&arena)];
        let keys = [0, 1].map(|at| {
            let job = jobs.get_mut(at).expect("two jobs");
            let key = NodeSupport::recorded(&arena, job, goal, &[], &Reads::closed());
            job.keep(&key, key.names().0, outcomes.get(at).expect("two outcomes"));
            key
        });
        assert_eq!(keys[0], keys[1], "the two jobs record one key");
        let [first, second] = jobs;
        session.join(&arena, first).expect("the first job glues");
        let refused = session
            .join(&arena, second)
            .expect_err("two outcomes under one key do not glue");
        let crate::KernelError::KeptOutcomesDisagree(kept) = refused
        else {
            panic!("the refusal is the disagreement of two kept outcomes: {refused:?}");
        };
        assert_eq!(
            (kept.key(), kept.held(), kept.offered()),
            (
                &gandr_kernel_check_memo::MemoKey::digest(&super::KeptSupport {
                    support: keys[0].clone(),
                    parameters: keys[0].names().0,
                }),
                &outcomes[0],
                &outcomes[1]
            ),
            "the refusal names the key, the outcome kept first and the outcome offered"
        );
        assert_eq!(
            session.kept_checked(&keys[0], keys[0].names().0),
            super::Discharge::Held,
            "the session keeps the outcome of the first job alone"
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
    fn an_owed_key_passes_a_barrier_and_joins_one_time()
    {
        let mut arena = TermArena::new();
        let unit_type = arena.value_type_unit();
        let mut session = SupportContext::new();
        let key = NodeSupport::recorded(
            &arena,
            &mut session,
            SupportGoal::Obligation(crate::encoding::ObligationGoal::Data(unit_type)),
            &[],
            &Reads::closed(),
        );
        let goal = session.open(&[]);
        let barrier = session.open_barrier();
        let inner = session.open(&[]);
        session.owe(core::slice::from_ref(&key));
        session.owe(core::slice::from_ref(&key));
        let (_, owed) = session.close_owing(inner).expect("the inner goal is open");
        assert_eq!(
            core::slice::from_ref(&key),
            owed.keys(),
            "a key owed two times is held one time"
        );
        let _barrier = session.close(barrier);
        let (_, owed) = session.close_owing(goal).expect("the goal is open");
        assert_eq!(
            core::slice::from_ref(&key),
            owed.keys(),
            "a key names content, so it passes the barrier to the goal around it"
        );
        assert!(
            session.close_owing(goal).is_none(),
            "a goal already closed gives no keys, so no entry records it"
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
