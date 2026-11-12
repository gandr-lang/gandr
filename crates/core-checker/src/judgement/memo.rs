//! The goal memo of one run of the machine: the answer of each value
//! judgement and of each value type's formation, kept for the rest of the run.
//!
//! The lowering and the bridge keep a shared term shared, so one node can stand
//! at many places of the tree it roots. Without a memo the machine judges such
//! a node once for each place, and an iterated pair of depth `d` costs `2^d`
//! goals. With the memo the machine judges each distinct goal once. A goal it
//! meets again costs the one step that starts it, and the memo hands its
//! recorded answer to the frame that waits for it.
//!
//! # The key
//!
//! The key of a goal is the goal, the world it is judged at, and each binder it
//! reads with the type that the binder was opened at. The goal names its node
//! by the node's arena id. The arena only grows while a run lives, so the id
//! names the node's content for the life of the memo. Two equal nodes at two
//! ids are two keys: that costs a miss, never a wrong answer. The binders read
//! are the node's support and the support of the type it is checked at. The
//! supports of the slot types they name close the set.
//!
//! # Where the memo answers
//!
//! The memo answers and records only where an answer is all that a goal
//! leaves behind:
//! - no thunk's image forms, so no image misses a read;
//! - no structural fixpoint waits for its case;
//! - the run holds no linear slot, keeps no region and reaches none, so no
//!   fence and no linear use is skipped;
//! - the goal reads no linear binder.
//!
//! A finished goal is recorded only when its run marked nothing, recorded no
//! code use, and left the session scope and the staged motives as it found
//! them. The output emission reads one code use for each occurrence of a code,
//! so an answer that skips a use gives a later occurrence no lift.
//!
//! A typed run keeps the typings of a goal's first judgement. An answer keeps
//! no typing again. Each node under the goal holds its typing from that first
//! judgement, at the same type, under binders of the same types. A table and
//! the concurrent schedule read each node's typing, so they read the same.
//!
//! # References
//!
//! - `core-kernel-reassessment.md` § kernel-reassessment-memo (vault reference
//!   `vault:01a178aa-6917-7983-b5cd-86e2af86b3ec`): the check memo and its key
//!   on the binders a judgement reads.
//! - `sharing-as-descent.md` (vault reference
//!   `vault:01a16be2-3ad1-73e2-9e54-d28a053edcaa`): a judgement served wherever
//!   its dependency set recurs, as one gluing.

use alloc::boxed::Box;
use alloc::vec::Vec;

use gandr_core_nbe::ContentHash;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::support::ThinningRef;
use gandr_core_term::world::World;
use gandr_kernel_check_memo::CheckMemo as _;
use gandr_kernel_check_memo::ContentAgreement;
use gandr_kernel_check_memo::ContentDigest;
use gandr_kernel_check_memo::DigestWord;
use gandr_kernel_check_memo::HashedMemo;
use gandr_kernel_check_memo::MemoActivity;
use gandr_kernel_check_memo::MemoKey;
use gandr_kernel_term::DeBruijnIndex;
use quenchant_shape::shape::Maybe;

use super::Goal;
use super::Machine;
use super::Produced;
use super::session::Scope;
use crate::judge::Direction;
use crate::judge::unanswered;
use crate::refusal::TypeNode;
use crate::solution::Migrating;

/// The most answers one run's memo holds. Past it the memo records nothing
/// more, and each goal it does not hold runs as it does without a memo.
const ENTRIES: usize = 1_usize << 16_u32;

/// The accounting partition: the goal loop over terms, and the formation walk
/// over types.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Plane
{
    /// Value judgements, in either direction.
    Terms,
    /// Value type formations.
    Types,
}

/// The complete input of one goal that the memo answers.
#[derive(Clone, Debug, Eq, PartialEq)]
struct GoalKey
{
    /// The goal, its node named by the node's arena id.
    goal: Goal,
    /// The world the goal is judged at.
    world: World,
    /// Each binder the goal reads, ascending by index, with its slot's type.
    reads: Box<[(DeBruijnIndex, ValueTypeId)]>,
}

impl MemoKey for GoalKey
{
    type Plane = Plane;

    /// The plane of the goal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn plane(&self) -> Plane
    {
        plane_of(self.goal)
    }

    /// The digest of the goal and its world.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn digest(&self) -> ContentDigest
    {
        digest_of(self.goal, self.world)
    }

    /// Agree exactly when the two keys hold the same goal, world and reads.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn agreement(
        &self,
        other: &Self,
    ) -> ContentAgreement
    {
        if self == other {
            ContentAgreement::Agree
        }
        else {
            ContentAgreement::Differ
        }
    }
}

/// The plane `goal` is accounted to.
///
/// # Specification
/// trivial.
const fn plane_of(goal: Goal) -> Plane
{
    match goal {
        Goal::Form(_) => Plane::Types,
        Goal::Value { .. } | Goal::Computation { .. } | Goal::Stack { .. } => Plane::Terms,
    }
}

/// The digest of `goal` judged at `world`: the bucket a key is filed under.
/// The reads stay out of it, so every key of one goal shares a bucket, and the
/// comparison of the reads decides.
///
/// # Specification
/// trivial.
fn digest_of(
    goal: Goal,
    world: World,
) -> ContentDigest
{
    ContentDigest::new(
        DigestWord::from(u64::from(ContentHash::of(&goal))),
        DigestWord::from(u64::from(ContentHash::of(&world))),
    )
}

/// What a run leaves beside an answer, compared where a goal starts and where
/// it finishes.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Effects
{
    /// The refusals the run marked.
    marks: usize,
    /// The staged motives waiting for their branches.
    staged: usize,
    /// The linear state's scope.
    sessions: Scope,
    /// The code uses the elaboration recorded.
    uses: crate::elaboration::CodeUses,
}

/// A goal under way whose answer the memo may record.
#[derive(Clone, Copy, Debug)]
struct Pending
{
    /// The goal.
    goal: Goal,
    /// The world it started at.
    world: World,
    /// How many frames waited as it started: it finishes on the ascent that
    /// reaches this height.
    frames: usize,
    /// What the run had left as it started.
    effects: Effects,
}

/// Whether the memo answers and records where the run stands.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Answering
{
    /// It does.
    Open,
    /// It does not.
    Closed,
}

/// Whether a goal has a key where the run stands.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Keyed
{
    /// It has: the memo's scratch holds the binders it reads.
    Keyed,
    /// It has none.
    Unkeyed,
}

/// What one consult of the memo found.
#[cfg(feature = "instrument")]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Consult
{
    /// The memo answered the goal.
    Hit,
    /// The memo keyed the goal and held no answer for it.
    Miss,
}

/// The memo one run of the machine keeps: its answers, the goals under way it
/// may record, and the scratch a key is gathered in.
pub(super) struct GoalMemo
{
    /// Whether the memo answers at all.
    activity: MemoActivity,
    /// The answers recorded, by key.
    answers: HashedMemo<GoalKey, Produced>,
    /// The goals under way whose answers it may record, innermost last.
    pending: Vec<Pending>,
    /// The binders still to read for the goal keyed last, ascending.
    unread: Vec<DeBruijnIndex>,
    /// The binders the goal keyed last reads, ascending, with their types.
    reads: Vec<(DeBruijnIndex, ValueTypeId)>,
}

impl GoalMemo
{
    /// An empty memo that answers as `activity` says.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(super) const fn new(activity: MemoActivity) -> Self
    {
        Self {
            activity,
            answers: HashedMemo::new(),
            pending: Vec::new(),
            unread: Vec::new(),
            reads: Vec::new(),
        }
    }
}

impl Machine<'_, '_>
{
    /// The answer the memo holds for `goal`. On a miss the goal is under way,
    /// and its answer is recorded where it finishes.
    ///
    /// # Specification
    /// - requires: `goal` is the goal the machine is about to start.
    /// - ensures: [`Maybe::Present`] only with the answer recorded for a key
    ///   that agrees with the goal's key where the run stands; on
    ///   [`unanswered::Absent::Missed`], one goal more is under way.
    /// - panics: none.
    /// - executable: none — agreement is the key's own content comparison, and
    ///   a predicate could state it only by gathering the key again.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a shared pair answers its repeated goals from the
    ///   memo; one node read under two binder types answers neither from the
    ///   other; a run without the memo spends the unshared work.
    /// - witness: `judgement::memo::tests::a_shared_pair_spends_a_step_for_each_distinct_goal`
    /// - witness: `judgement::memo::tests::a_node_read_under_two_binder_types_is_judged_under_each`
    pub(super) fn consulted(
        &mut self,
        goal: Goal,
    ) -> Maybe<Produced, unanswered::Absent>
    {
        if self.answering() == Answering::Closed {
            return Maybe::Absent(unanswered::Absent::Closed);
        }
        if self.keyed(goal) == Keyed::Unkeyed {
            return Maybe::Absent(unanswered::Absent::Unkeyed);
        }
        let world = self.context.world();
        let reads = self.memo.reads.as_slice();
        let answered = self
            .memo
            .answers
            .filed(digest_of(goal, world))
            .find(|hit| {
                let key = hit.support();
                key.goal == goal && key.world == world && *key.reads == *reads
            })
            .map(|hit| *hit.outcome());
        if let Some(answer) = answered {
            #[cfg(feature = "instrument")]
            self.tallied(goal, Consult::Hit);
            return Maybe::Present(answer);
        }
        let effects = self.effects();
        self.memo.pending.push(Pending {
            goal,
            world,
            frames: self.frames.len(),
            effects,
        });
        #[cfg(feature = "instrument")]
        self.tallied(goal, Consult::Miss);
        Maybe::Absent(unanswered::Absent::Missed)
    }

    /// Count `consult` of `goal` on its plane in the context's tally.
    ///
    /// # Specification
    /// trivial.
    #[cfg(feature = "instrument")]
    fn tallied(
        &mut self,
        goal: Goal,
        consult: Consult,
    )
    {
        let tally = self.context.tally_mut();
        match (plane_of(goal), consult) {
            (Plane::Terms, Consult::Hit) => tally.term_hit(),
            (Plane::Terms, Consult::Miss) => tally.term_miss(),
            (Plane::Types, Consult::Hit) => tally.type_hit(),
            (Plane::Types, Consult::Miss) => tally.type_miss(),
        }
    }

    /// The binders that the memo key of the goal keyed last reads.
    ///
    /// # Specification
    /// trivial.
    #[cfg(feature = "instrument")]
    pub(super) fn cover(&self) -> crate::trace::Cover
    {
        crate::trace::Cover::from(self.memo.reads.len())
    }

    /// Record `produced` as the answer of every goal under way that the ascent
    /// handing it finishes.
    ///
    /// # Specification
    /// - requires: `produced` is the result the ascent hands on, before the
    ///   frame awaiting it is popped.
    /// - ensures: no goal under way started at or above the frames' height;
    ///   each finished goal whose run left only its answer is recorded, while
    ///   the memo holds fewer than its bound.
    /// - panics: none.
    /// - executable: none — what a run left is the comparison of two effect
    ///   snapshots, which a predicate could restate only by taking them again.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::consulted`]; the corpus sweep compares
    ///   every declaration's settlement with and without the memo.
    /// - witness: `judgement::memo::tests::a_shared_pair_spends_a_step_for_each_distinct_goal`
    pub(super) fn remembered(
        &mut self,
        produced: Produced,
    )
    {
        let height = self.frames.len();
        while let Some(&pending) = self
            .memo
            .pending
            .last()
            .filter(|pending| pending.frames >= height)
        {
            let _finished = self.memo.pending.pop();
            self.record(pending, produced);
        }
    }

    /// Record `produced` as `pending`'s answer, when its run left only that.
    ///
    /// # Specification
    /// trivial.
    fn record(
        &mut self,
        pending: Pending,
        produced: Produced,
    )
    {
        if pending.effects != self.effects()
            || pending.world != self.context.world()
            || self.answering() == Answering::Closed
            || usize::from(self.memo.answers.entry_count()) >= ENTRIES
            || self.keyed(pending.goal) == Keyed::Unkeyed
        {
            return;
        }
        let key = GoalKey {
            goal: pending.goal,
            world: pending.world,
            reads: self.memo.reads.as_slice().into(),
        };
        // `ENTRIES` bounds the memo's memory. A memo at the bound records
        // nothing more, and a goal that it does not hold runs, so the bound
        // costs reuse and never an answer.
        let _recorded = self.memo.answers.remember(key, produced);
    }

    /// Whether the memo answers and records where the run stands.
    ///
    /// # Specification
    /// trivial.
    fn answering(&self) -> Answering
    {
        let open = matches!(self.memo.activity, MemoActivity::Active)
            && self.images.forming() == Migrating::Not
            && matches!(self.root, Maybe::Absent(_))
            && self.context.depth(Zone::Linear) <= self.sessions.base
            && self.sessions.abstracted == crate::capability::Reach::Clear
            && self.sessions.regions.is_empty();
        if open {
            Answering::Open
        }
        else {
            Answering::Closed
        }
    }

    /// What the run has left beside its answers so far.
    ///
    /// # Specification
    /// trivial.
    fn effects(&self) -> Effects
    {
        Effects {
            marks: self.marks.len(),
            staged: self.staged_motives.len(),
            sessions: self.session_scope(),
            uses: self.context.code_uses(),
        }
    }

    /// Gather the binders `goal` reads where the run stands into the memo's
    /// scratch, each with its slot's type: the node's support and the support
    /// of the type it is checked at, closed under the supports of the slot
    /// types they name.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Keyed::Keyed`] exactly when `goal` is a value judgement or
    ///   a value type's formation that reads no linear binder and only binders
    ///   the context holds; the scratch then holds each binder read once,
    ///   ascending, beside the type it was opened at.
    /// - panics: none.
    /// - executable: none — the closure is a walk over slot types that a
    ///   predicate could state only by walking them again.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one node read under two binder types keys apart.
    /// - witness: `judgement::memo::tests::a_node_read_under_two_binder_types_is_judged_under_each`
    fn keyed(
        &mut self,
        goal: Goal,
    ) -> Keyed
    {
        let arena = self.context.arena();
        let (node, at) = match goal {
            Goal::Value { term, direction } => (arena.value_support(term), match direction {
                Direction::Check(expected) => arena.value_type_support(expected),
                Direction::Synthesise => Some(ThinningRef::empty()),
            }),
            Goal::Form(TypeNode::Value(formed)) => {
                (arena.value_type_support(formed), Some(ThinningRef::empty()))
            },
            Goal::Form(TypeNode::Computation(_))
            | Goal::Computation { .. }
            | Goal::Stack { .. } => return Keyed::Unkeyed,
        };
        let (Some(node), Some(at)) = (node, at)
        else {
            return Keyed::Unkeyed;
        };
        if node.indices(Zone::Linear).next().is_some() || at.indices(Zone::Linear).next().is_some()
        {
            return Keyed::Unkeyed;
        }
        let unread = &mut self.memo.unread;
        unread.clear();
        for index in node
            .indices(Zone::Intuitionistic)
            .chain(at.indices(Zone::Intuitionistic))
        {
            insert_ascending(unread, index);
        }
        self.memo.reads.clear();
        let mut cursor = 0_usize;
        while let Some(&index) = self.memo.unread.get(cursor) {
            let Ok(slot) = self.context.binders().declared(Zone::Intuitionistic, index)
            else {
                return Keyed::Unkeyed;
            };
            self.memo.reads.push((index, slot));
            let Some(support) = self.context.arena().value_type_support(slot)
            else {
                return Keyed::Unkeyed;
            };
            // The slot's type stands under the binders outside the slot, so
            // its index `read` names the binder `index + 1 + read` here.
            for read in support.indices(Zone::Intuitionistic) {
                let Some(outer) = u32::from(index)
                    .checked_add(1_u32)
                    .and_then(|past| past.checked_add(u32::from(read)))
                else {
                    return Keyed::Unkeyed;
                };
                insert_ascending(&mut self.memo.unread, DeBruijnIndex::from(outer));
            }
            cursor = cursor.saturating_add(1_usize);
        }
        Keyed::Keyed
    }
}

/// Insert `index` into the ascending `indices`, unless it is there already.
///
/// # Specification
/// trivial.
fn insert_ascending(
    indices: &mut Vec<DeBruijnIndex>,
    index: DeBruijnIndex,
)
{
    if let Err(at) = indices.binary_search(&index) {
        indices.insert(at, index);
    }
}

#[cfg(test)]
mod tests;
