//! The synthesis stream: ordered, resumable events over one validated resume.
//!
//! # Items first, then liveness by origin
//!
//! A stream opens with the item count, carries one event per item in source
//! order — its handle, its typing and whether it was adopted — then the match
//! liveness its producer computed, and closes. Liveness follows the items
//! rather than interleaving with them: an item is addressed by core position,
//! a match by the source coordinates its producer gives it, and one source
//! item may lower to several core items, so there is no item a match belongs
//! beside. A submission whose source records the producer has dropped is
//! named by an event of its own rather than left silent, because silence
//! would read as a submission with no matches. The stream reads its inputs
//! and computes nothing, so a run that adopted and a run that judged publish
//! the same events but for the adoption marks.
//!
//! # The stream's shape
//!
//! A stream opens with the item count, carries one event per item in source
//! order — its handle, typing and adoption — then the match liveness its
//! producer computed, by origin, and closes. Liveness follows the items because
//! a match is addressed by source coordinates and one source item may lower to
//! several core items. A submission whose source records are gone is named by
//! an event of its own, because silence would read as a submission without
//! matches. The stream is a function of its inputs: a run that adopted and one
//! that judged publish the same events but for the adoption marks.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::pattern::BranchStatus;
use quenchant_shape::shape::Maybe;

use crate::boundary::ItemCount;
use crate::boundary::ItemOrdinal;
use crate::boundary::LivenessEmpty;
use crate::boundary::MatchOrdinal;
use crate::boundary::SourceItemOrdinal;
use crate::boundary::SubmissionOrdinal;
use crate::checkpoint::Adoption;
use crate::checkpoint::Resume;
use crate::order::ItemHandle;
use crate::typing::Typing;

quenchant_shape::reason_enum! {
    /// Why recording a match displaced nothing.
    pub mod displaced {
        /// The reason nothing was displaced.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The origin carried no entry before.
            Fresh,
        }
    }
}

/// Where one analysed match came from, in its producer's own coordinates.
///
/// No core position appears here: a match is a fact about source the
/// programmer wrote, and the stream never interprets the coordinates beyond
/// identifying and ordering matches by them.
///
/// # Specification
/// - requires: the producer interprets the coordinates in its source records.
/// - ensures: origins are identified and ordered lexicographically by
///   submission, source item and match index, not by a core item position.
/// - executable: none — this declaration has no call boundary; comparison is
///   derived from its ordered fields and source ownership is external.
///
/// # Adequacy
/// - hypothesis: L3 — reversed insertion order separates source-item priority
///   from match-index priority; an extreme retained origin beside an unretained
///   submission witnesses submission order without a core-item membership test.
///   The cases do not certify the producer's source-coordinate assignment.
/// - witness: `stream::tests::liveness_follows_the_items_in_origin_order`
/// - witness: `stream::tests::unretained_marks_dominate_stored_matches`
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct MatchOrigin
{
    /// The submission the match was written in.
    pub submission: SubmissionOrdinal,
    /// The source item of that submission owning the match.
    pub source_item: SourceItemOrdinal,
    /// Which match of the source item this is.
    pub match_index: MatchOrdinal,
}

/// The match liveness a stream publishes, keyed by origin.
///
/// # Specification
/// - requires: recorded statuses and source-retention marks come from a
///   producer; they may name no item of a particular core resume.
/// - ensures: one latest branch vector is held per origin, including an empty
///   vector; a marked submission publishes one missing-source event instead of
///   any stored matches from that submission.
/// - executable: none — this declaration has no call boundary. Mutation and
///   stream-construction predicates check its state and publication relations;
///   the producer's classification and retention facts are external.
///
/// # Adequacy
/// - hypothesis: L3 — replacement, a zero-branch match, idempotent marking and
///   insertion on both sides of a retention mark separate latest-value storage
///   from publication. Semantic classification remains a producer obligation.
/// - witness: `stream::tests::an_origin_carries_exactly_one_liveness_entry`
/// - witness: `stream::tests::an_empty_branch_vector_remains_a_match`
/// - witness: `stream::tests::unretained_marks_dominate_stored_matches`
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Liveness
{
    /// One entry per analysed match.
    matches: BTreeMap<MatchOrigin, Vec<BranchStatus>>,
    /// The submissions whose source records were not retained.
    unretained: BTreeSet<SubmissionOrdinal>,
}

impl Liveness
{
    /// An empty map: nothing analysed, nothing missing.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new() -> Self
    {
        Self::default()
    }

    /// Record one match's per-branch statuses at its origin.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the map holds exactly one entry for `origin`, `branches`.
    /// - provides: the entry this call displaced, so a producer publishing a
    ///   match twice is caught; `displaced::Absent::Fresh` when there was none.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — insertion, displacement and exact latest publication
    ///   distinguish replacement from accidental duplicate or stale entries. A
    ///   zero-branch vector remains an entry rather than being dropped. These
    ///   cases do not establish whether the supplied statuses are true.
    /// - witness: `stream::tests::an_origin_carries_exactly_one_liveness_entry`
    /// - witness: `stream::tests::an_empty_branch_vector_remains_a_match`
    #[spec(
        captures: [before_length = self.matches.len(), previous_length = self.matches.get(&origin).map(Vec::len), incoming_length = branches.len()],
        ensures: |ret| self.matches.get(&origin).is_some_and(|stored| stored.len() == incoming_length)
            && before_length.checked_add(usize::from(previous_length.is_none())) == Some(self.matches.len())
            && match ret {
                Maybe::Present(ref displaced) => Some(displaced.len()) == previous_length,
                Maybe::Absent(displaced::Absent::Fresh) => previous_length.is_none(),
            }
    )]
    #[inline]
    pub fn insert(
        &mut self,
        origin: MatchOrigin,
        branches: Vec<BranchStatus>,
    ) -> Maybe<Vec<BranchStatus>, displaced::Absent>
    {
        self.matches
            .insert(origin, branches)
            .map_or(Maybe::Absent(displaced::Absent::Fresh), Maybe::Present)
    }

    /// Name a submission whose source records were not retained.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the stream names the submission in an event of its own and
    ///   publishes none of its matches.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a submission with no stored matches still publishes
    ///   its mark; repeated marking and insertions before and after a mark
    ///   retain one missing-source event and suppress that submission's
    ///   matches.
    /// - witness: `stream::tests::an_unretained_submission_is_published_not_omitted`
    /// - witness: `stream::tests::unretained_marks_dominate_stored_matches`
    #[spec(
        captures: [before = self.unretained.len(), present = self.unretained.contains(&submission)],
        ensures: self.unretained.contains(&submission)
            && before.checked_add(usize::from(!present)) == Some(self.unretained.len())
    )]
    #[inline]
    pub fn mark_unretained(
        &mut self,
        submission: SubmissionOrdinal,
    )
    {
        let _fresh = self.unretained.insert(submission);
    }

    /// Whether the map publishes nothing.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: true exactly when neither a match entry nor a missing-source
    ///   mark is held; an entry with zero branches still publishes a match.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty, match-only, mark-only and combined states
    ///   distinguish the two independent ways liveness can be nonempty.
    /// - witness: `stream::tests::an_empty_branch_vector_remains_a_match`
    /// - witness: `stream::tests::an_unretained_submission_is_published_not_omitted`
    #[spec(ensures: |ret| bool::from(ret) == (self.matches.is_empty() && self.unretained.is_empty()))]
    #[inline]
    #[must_use]
    pub fn is_empty(&self) -> LivenessEmpty
    {
        LivenessEmpty::from(self.matches.is_empty() && self.unretained.is_empty())
    }
}

/// One event of the synthesis stream.
///
/// # Specification
/// - requires: an event is interpreted as part of its stream and against the
///   resume or producer coordinates its payload names.
/// - ensures: streams frame ordered item events and then ordered liveness
///   events; a missing-source marker is not an empty set of matches.
/// - executable: none — this declaration has no call boundary; sequence
///   position and the source of its payload are external to an isolated event.
///
/// # Adequacy
/// - hypothesis: L3 — item-prefix ordering, exact branch vectors,
///   missing-source dominance and an empty framed stream distinguish the
///   observable event classes. The witnesses cover generated streams, not
///   arbitrary event lists.
/// - witness: `stream::tests::liveness_follows_the_items_in_origin_order`
/// - witness: `stream::tests::unretained_marks_dominate_stored_matches`
/// - witness: `stream::tests::an_empty_stream_finishes_once_and_remains_exhausted`
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SynthesisEvent
{
    /// The stream opens over this many items.
    Started
    {
        /// The number of items.
        item_count: ItemCount,
    },
    /// One item's typing.
    Item
    {
        /// The item's source ordinal.
        index: ItemOrdinal,
        /// The item's identity across revisions.
        handle: ItemHandle,
        /// The item's typing.
        typing: Typing,
        /// Whether its checkpoint was adopted.
        adoption: Adoption,
    },
    /// One match's per-branch liveness.
    Match
    {
        /// The match, in its producer's coordinates.
        origin: MatchOrigin,
        /// One status per branch, in source order.
        branches: Vec<BranchStatus>,
    },
    /// A submission whose source records are gone, so no liveness can be
    /// computed for it.
    SourceNotRetained
    {
        /// The submission.
        submission: SubmissionOrdinal,
    },
    /// The stream closes after every item and match.
    Completed,
}

/// A deterministic, resumable sequence of synthesis events.
///
/// # Specification
/// - requires: constructed from a validated resume and optional liveness.
/// - ensures: its cursor begins before Started, advances once per yielded event
///   and stays exhausted after Completed; events retain their specified source
///   order and payload interpretation.
/// - executable: none — this declaration has no requires/ensures call boundary;
///   constructor and iterator predicates check framing and cursor transitions,
///   while resume and producer provenance are external.
///
/// # Adequacy
/// - hypothesis: L3 — nonempty item and liveness streams distinguish section
///   order; the empty resume distinguishes framing from item presence and
///   repeated terminal reads from a restarted iterator. The observed streams do
///   not establish producer provenance or an unbounded work estimate.
/// - witness: `stream::tests::liveness_follows_the_items_in_origin_order`
/// - witness: `stream::tests::unretained_marks_dominate_stored_matches`
/// - witness: `stream::tests::an_empty_stream_finishes_once_and_remains_exhausted`
#[derive(Clone, Debug)]
pub struct SynthesisStream
{
    /// The events, in order.
    events: Vec<SynthesisEvent>,
    /// The next event to hand out.
    cursor: usize,
}

impl SynthesisStream
{
    /// The stream of `resume` with no liveness.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the stream [`Self::from_resume_with_liveness`] gives with an
    ///   empty map.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty and two-item resumes separate framing from item
    ///   presence. The repeated key retains distinct source occurrences, and
    ///   three terminal reads distinguish exhaustion from a restarted iterator.
    ///   Other item counts and typing variants remain outside these finite
    ///   cases.
    /// - witness: `stream::tests::an_empty_stream_finishes_once_and_remains_exhausted`
    /// - witness: `stream::tests::a_plain_stream_addresses_each_source_item_once`
    #[spec(ensures: |ret| {
        let count = resume.checkpoints().items().len();
        ret.events.len().checked_sub(2) == Some(count)
            && ret.cursor == 0
            && matches!(ret.events.first(), Some(&SynthesisEvent::Started { item_count }) if usize::from(item_count) == count)
            && ret.events.last() == Some(&SynthesisEvent::Completed)
            && ret
                .events
                .get(1 .. count.saturating_add(1))
                .is_some_and(|events| {
                    events
                        .iter()
                        .enumerate()
                        .all(|(ordinal, event)| match *event {
                            | SynthesisEvent::Item {
                                index,
                                handle,
                                ref typing,
                                adoption,
                            } => {
                                usize::from(index) == ordinal
                                    && resume.handles().get(ordinal) == Some(&handle)
                                    && resume.adoptions().get(ordinal) == Some(&adoption)
                                    && resume
                                        .checkpoints()
                                        .items()
                                        .get(ordinal)
                                        .is_some_and(|checkpoint| checkpoint.typing() == typing)
                            },
                            | _ => false,
                        })
                })
    })]
    #[inline]
    #[must_use]
    pub fn from_resume(resume: &Resume) -> Self
    {
        Self::from_resume_with_liveness(resume, &Liveness::new())
    }

    /// The stream of `resume` and the liveness its producer computed.
    ///
    /// # Specification
    /// - requires: nothing of `liveness` beyond its type: an origin naming no
    ///   item of `resume` is published unchanged, because the stream is not the
    ///   authority on which matches exist.
    /// - ensures: `Started`, then one `Item` per item in source order, then per
    ///   submission ascending either its `SourceNotRetained` or its `Match`
    ///   events in origin order, then `Completed`.
    /// - provides: a stream that is a function of its inputs alone.
    /// - panics: none.
    /// - intension: one pass over the items and one range walk per submission
    ///   over the matches.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — reversed origin insertion, replacement, empty branch
    ///   vectors, missing-source marks without matches and marks that suppress
    ///   stored matches distinguish section order, origin order and precedence.
    ///   An extreme source origin remains independent of core item membership.
    ///   These finite cases do not establish an unbounded work estimate.
    /// - witness: `stream::tests::liveness_follows_the_items_in_origin_order`
    /// - witness: `stream::tests::an_origin_carries_exactly_one_liveness_entry`
    /// - witness: `stream::tests::an_unretained_submission_is_published_not_omitted`
    /// - witness: `stream::tests::unretained_marks_dominate_stored_matches`
    /// - witness: `stream::tests::an_empty_branch_vector_remains_a_match`
    #[spec(ensures: |ret| {
        let count = resume.checkpoints().items().len();
        let retained = liveness
            .matches
            .keys()
            .filter(|origin| !liveness.unretained.contains(&origin.submission))
            .count();
        let tail_count = liveness.unretained.len().checked_add(retained);
        ret.events.len().checked_sub(2) == tail_count.and_then(|tail| count.checked_add(tail))
            && ret.cursor == 0
            && matches!(ret.events.first(), Some(&SynthesisEvent::Started { item_count }) if usize::from(item_count) == count)
            && ret.events.last() == Some(&SynthesisEvent::Completed)
            && ret
                .events
                .get(1 .. count.saturating_add(1))
                .is_some_and(|events| {
                    events
                        .iter()
                        .enumerate()
                        .all(|(ordinal, event)| match *event {
                            | SynthesisEvent::Item {
                                index,
                                handle,
                                ref typing,
                                adoption,
                            } => {
                                usize::from(index) == ordinal
                                    && resume.handles().get(ordinal) == Some(&handle)
                                    && resume.adoptions().get(ordinal) == Some(&adoption)
                                    && resume
                                        .checkpoints()
                                        .items()
                                        .get(ordinal)
                                        .is_some_and(|checkpoint| checkpoint.typing() == typing)
                            },
                            | _ => false,
                        })
                })
            && ret
                .events
                .iter()
                .skip(count.saturating_add(1))
                .take(ret.events.len().saturating_sub(count).saturating_sub(2))
                .all(|event| match *event {
                    | SynthesisEvent::Match {
                        origin,
                        ref branches,
                    } => {
                        !liveness.unretained.contains(&origin.submission)
                            && liveness.matches.get(&origin) == Some(branches)
                    },
                    | SynthesisEvent::SourceNotRetained { submission } => {
                        liveness.unretained.contains(&submission)
                    },
                    | _ => false,
                })
            && ret
                .events
                .iter()
                .skip(count.saturating_add(1))
                .zip(ret.events.iter().skip(count.saturating_add(2)))
                .all(|(left, right)| match (left, right) {
                    | (
                        &SynthesisEvent::Match { origin: left, .. },
                        &SynthesisEvent::Match { origin: right, .. },
                    ) => left < right,
                    | (
                        &SynthesisEvent::Match { origin, .. },
                        &SynthesisEvent::SourceNotRetained { submission },
                    ) => origin.submission < submission,
                    | (
                        &SynthesisEvent::SourceNotRetained { submission },
                        &SynthesisEvent::Match { origin, .. },
                    ) => submission < origin.submission,
                    | (
                        &SynthesisEvent::SourceNotRetained { submission: left },
                        &SynthesisEvent::SourceNotRetained { submission: right },
                    ) => left < right,
                    | (_, &SynthesisEvent::Completed) => true,
                    | _ => false,
                })
    })]
    #[inline]
    #[must_use]
    pub fn from_resume_with_liveness(
        resume: &Resume,
        liveness: &Liveness,
    ) -> Self
    {
        let items = resume.checkpoints().items();
        let mut events = Vec::with_capacity(items.len().saturating_add(2));
        events.push(SynthesisEvent::Started {
            item_count: ItemCount::from(items.len()),
        });
        for (index, ((checkpoint, &adoption), &handle)) in items
            .iter()
            .zip(resume.adoptions())
            .zip(resume.handles())
            .enumerate()
        {
            events.push(SynthesisEvent::Item {
                index: ItemOrdinal::from(index),
                handle,
                typing: checkpoint.typing().clone(),
                adoption,
            });
        }
        let mut submissions: BTreeSet<SubmissionOrdinal> = liveness.unretained.clone();
        submissions.extend(liveness.matches.keys().map(|origin| origin.submission));
        for submission in submissions {
            if liveness.unretained.contains(&submission) {
                events.push(SynthesisEvent::SourceNotRetained { submission });
                continue;
            }
            let first = MatchOrigin {
                submission,
                source_item: SourceItemOrdinal::from(0_usize),
                match_index: MatchOrdinal::from(0_usize),
            };
            let last = MatchOrigin {
                submission,
                source_item: SourceItemOrdinal::from(usize::MAX),
                match_index: MatchOrdinal::from(usize::MAX),
            };
            for (&origin, branches) in liveness.matches.range(first ..= last) {
                events.push(SynthesisEvent::Match {
                    origin,
                    branches: branches.clone(),
                });
            }
        }
        events.push(SynthesisEvent::Completed);
        Self { events, cursor: 0 }
    }
}

impl Iterator for SynthesisStream
{
    type Item = SynthesisEvent;

    /// The next event, or the end of the stream.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the next stored event is yielded and the cursor advances
    ///   once; when no event remains, None is returned and the cursor stays
    ///   fixed, including on repeated calls after completion.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — complete nonempty streams witness ordered
    ///   advancement; an empty resume yields Started then Completed, followed
    ///   by three terminal reads. This finite boundary distinguishes early
    ///   stopping and restart.
    /// - witness: `stream::tests::liveness_follows_the_items_in_origin_order`
    /// - witness: `stream::tests::an_empty_stream_finishes_once_and_remains_exhausted`
    #[spec(
        captures: [before = self.cursor],
        ensures: |ret| ret.as_ref() == self.events.get(before)
            && self.cursor == if ret.is_some() { before.saturating_add(1) } else { before }
    )]
    #[inline]
    fn next(&mut self) -> Option<Self::Item>
    {
        let event = self.events.get(self.cursor).cloned();
        if event.is_some() {
            self.cursor = self.cursor.saturating_add(1);
        }
        event
    }
}

#[cfg(test)]
mod tests;
