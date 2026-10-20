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
//!   different contexts means two different things. Only the binders the node
//!   actually reads are folded in — its exact support, the free indices it
//!   mentions — each at its position, in telescope order so dependency order is
//!   part of the content.
//!
//! The key is therefore `(obligation content, telescope content, direction)`,
//! and it is **arena-free**: no arena id, no allocation order, and no binder
//! the node does not read reaches it. Content is named by the canonical
//! numbering [`SupportContext`] holds, so two structurally equal nodes key
//! alike however many arena positions spell them.
//!
//! The declaration's level parameters and the environment's admission log are
//! *not* in the key. They are fixed for the whole of one declaration's check,
//! and a memo never outlives that — see
//! [`check_declaration_with_memo`](crate::check::check_declaration_with_memo).
//!
//! # A type reaches binders too
//!
//! The universe-decoding former carries a value, so a type can mention a bound
//! variable and a type-formation goal's answer depends on the same reached
//! telescope a term goal's does. The reach pass therefore runs over all four
//! families rather than over the two term ones, which is what keeps a type
//! formed under two different binders from collapsing onto one entry.
//!
//! # The read binders are computed, not guessed
//!
//! [`Reaches`] computes each node's reach bottom-up over the graph,
//! iteratively, cached per node — so the computation is itself sharing-aware
//! and costs one pass per *distinct* node rather than per occurrence. The key
//! reads [`Reads`], the exact set of free indices; [`LooseDepths`] keeps one
//! more than the largest, for the checks that ask only how far a node reaches.
//! Where the walk cannot answer it returns the widest reach, which takes the
//! whole context into the key: **the failure direction is always more context
//! in the key, never less**, so a defect here costs collapse and cannot
//! manufacture a hit.

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_check_memo::CheckMemo as _;
use gandr_kernel_check_memo::ContentAgreement;
use gandr_kernel_check_memo::ContentDigest;
use gandr_kernel_check_memo::DigestWord;
use gandr_kernel_check_memo::MemoEntryCount;
use gandr_kernel_check_memo::MemoKey;
use gandr_kernel_strata::Level;
use gandr_kernel_term::CompType;
use gandr_kernel_term::CompTypeId;
use gandr_kernel_term::Computation;
use gandr_kernel_term::ComputationId;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueType;
use gandr_kernel_term::ValueTypeId;
use quenchant_arith::arith;
use quenchant_shape::shape::Maybe;

use crate::encoding::ContentId;
use crate::encoding::ContentTable;
use crate::encoding::SupportGoal;
use crate::encoding::Telescope;
use crate::encoding::support_key;
use crate::rewrite::RewriteMemo;
use crate::rewrite::RewritePlane;

/// The state one checking session derives its memo keys against: the canonical
/// content numbering, the per-node read binders, and the buffer one goal's
/// read binders are gathered in.
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
    /// The per-node read binders.
    reads: Reaches<Reads>,
    /// The read binders of the goal being keyed, reused across goals.
    read: Vec<(DeBruijnIndex, ValueTypeId)>,
    /// The session's shifting and substitution memo.
    rewrites: RewriteMemo,
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

    /// The binder reach of a computation-type node, read off its binders as
    /// cached for the session.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn comp_type_reach(
        &mut self,
        arena: &TermArena,
        root: CompTypeId,
    ) -> LooseDepth
    {
        self.reads.comp_type_reach(arena, root).depth()
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
}

/// One more than the largest free de Bruijn index a node mentions; zero for a
/// closed node.
///
/// This is the number of enclosing binders the node can reach, which is what
/// the checks that ask only how far a node reaches read.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct LooseDepth(u32);

impl From<u32> for LooseDepth
{
    /// The reach of `value` binders.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: u32) -> Self
    {
        Self(value)
    }
}

impl From<LooseDepth> for u32
{
    /// How many binders `depth` reaches.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(depth: LooseDepth) -> Self
    {
        depth.0
    }
}

impl LooseDepth
{
    /// The saturated maximum — the conservative answer, a reach past every
    /// binder.
    const WIDEST: Self = Self(u32::MAX);
}

/// What the reach walk computes for a node from its children's: the lattice
/// [`Reaches`] runs over.
///
/// # Specification
/// - requires: `join` is a least upper bound, with [`Reach::closed`] its unit
///   and [`Reach::widest`] absorbing; `under_binder` keeps the widest reach
///   widest. The walk relies on these laws and checks none of them.
/// - executable: none — laws over an implementor's values; each implementor's
///   witnesses observe them on the values the walk builds.
///
/// # Adequacy
/// - hypothesis: L3 — each implementor's join, binder step and widest
///   absorption are asserted exactly on closed, open and unreadable nodes.
/// - witness: `support::tests::a_variable_reaches_one_more_than_its_index`
/// - witness: `support::tests::reads_are_exactly_the_free_indices`
pub trait Reach: Clone + Eq
{
    /// A closed node's reach: no binder.
    ///
    /// # Specification
    /// trivial.
    fn closed() -> Self;

    /// The conservative reach of a node the walk could not read: every
    /// binder.
    ///
    /// # Specification
    /// trivial.
    fn widest() -> Self;

    /// The reach of a variable at `index`.
    ///
    /// # Specification
    /// trivial.
    fn variable(index: DeBruijnIndex) -> Self;

    /// The reach of a node whose children reach `self` and `other`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Clause cost
    /// - bound: every implementation keeps it to one word operation, or, for a
    ///   set holding an index past the word's width, one merge pass over the
    ///   two sets' indices; no node is read.
    #[must_use]
    fn join(
        self,
        other: Self,
    ) -> Self;

    /// The reach seen from outside one binder.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Clause cost
    /// - bound: every implementation keeps it to one word operation, or, for a
    ///   set holding an index past the word's width, one pass over its indices;
    ///   no node is read.
    #[must_use]
    fn under_binder(self) -> Self;
}

impl Reach for LooseDepth
{
    /// Zero binders.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn closed() -> Self
    {
        Self(0)
    }

    /// The saturated maximum.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn widest() -> Self
    {
        Self::WIDEST
    }

    /// One more than `index`, saturating to the widest reach.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn variable(index: DeBruijnIndex) -> Self
    {
        // reason: an unrepresentable reach conservatively uses the whole context.
        Self(u32::from(arith::saturating_add(
            arith::Int::from(u32::from(index)),
            arith::Int::from(1_u32),
        )))
    }

    /// The larger of two reaches.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn join(
        self,
        other: Self,
    ) -> Self
    {
        if self.0 >= other.0 { self } else { other }
    }

    /// The reach seen from outside one binder.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a finite, unsaturated reach loses one binder, stopping at
    ///   zero; the widest sentinel stays widest because its excess is unknown.
    /// - provides: conservative reach through a binding position, including
    ///   saturated variables and unreadable children.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 on a body reading its own binder and on the largest
    ///   variable index; exact external reaches separate closing a binder from
    ///   unsoundly narrowing an overflowed reach.
    /// - witness: `support::tests::a_binder_closes_its_body`
    /// - witness: `support::tests::saturated_reach_remains_conservative_beneath_a_binder`
    #[spec(ensures: |ret| ret.0 == if self.0 == u32::MAX {
        u32::MAX
    } else {
        self.0.saturating_sub(1)
    })]
    #[inline]
    fn under_binder(self) -> Self
    {
        if self == Self::WIDEST {
            return Self::WIDEST;
        }
        // reason: crossing a binder leaves a closed body's reach at zero.
        Self(u32::from(arith::saturating_sub(
            arith::Int::from(self.0),
            arith::Int::from(1_u32),
        )))
    }
}

/// How many indices a word of [`Reads`] holds.
const WORD_INDICES: u32 = u64::BITS;

/// The binders a node reads: exactly the free de Bruijn indices it mentions.
///
/// A set of indices all below 64 is one word, bit `i` for index `i`; a set
/// holding a larger index keeps its indices ascending behind one pointer. The
/// form is canonical, so equality compares sets.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct Reads(ReadSet);

/// The forms of [`Reads`].
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum ReadSet
{
    /// Every index is below 64: bit `i` set for index `i`.
    Word(u64),
    /// Some index is 64 or more: the indices, ascending, none repeated.
    Spilled(Box<[DeBruijnIndex]>),
    /// A node the walk could not read, which reads every binder.
    Widest,
}

quenchant_shape::reason_enum! {
    /// Why a read set lists no indices.
    mod read_indices {
        /// The set is not a list of indices.
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        pub enum Absent {
            /// The walk could not read the node, which reads every binder.
            Widest,
        }
    }
}

impl Reads
{
    /// The set of `indices`, in canonical form.
    ///
    /// # Specification
    /// - requires: `indices` ascend strictly.
    /// - ensures: [`Self::indices`] yields `indices`.
    /// - provides: the one constructor of a spilled set, which keeps the form
    ///   canonical.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the witness reads back every set it builds.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — sets on both sides of the word's width, joined and
    ///   stepped out across it, read back and compared.
    /// - witness: `support::tests::reads_are_exactly_the_free_indices`
    #[inline]
    fn of(indices: Vec<DeBruijnIndex>) -> Self
    {
        match indices.last() {
            Some(&last) if u32::from(last) >= WORD_INDICES => {
                Self(ReadSet::Spilled(indices.into_boxed_slice()))
            },
            Some(_) | None => Self(ReadSet::Word(indices.iter().fold(0_u64, |word, &index| {
                word | 1_u64.unbounded_shl(u32::from(index))
            }))),
        }
    }

    /// The indices read, ascending, or the widest reach's reason for a node the
    /// walk could not read.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn indices(&self) -> Maybe<ReadIndices<'_>, read_indices::Absent>
    {
        match self.0 {
            ReadSet::Word(word) => Maybe::Present(ReadIndices::Word(word)),
            ReadSet::Spilled(ref indices) => Maybe::Present(ReadIndices::Spilled(indices.iter())),
            ReadSet::Widest => Maybe::Absent(read_indices::Absent::Widest),
        }
    }

    /// One more than the largest index read, zero for none, and the widest
    /// reach for a node the walk could not read.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn depth(&self) -> LooseDepth
    {
        match self.0 {
            ReadSet::Word(word) => LooseDepth(WORD_INDICES.saturating_sub(word.leading_zeros())),
            ReadSet::Spilled(ref indices) => LooseDepth(
                indices
                    .last()
                    .map_or(0, |&last| u32::from(last).saturating_add(1)),
            ),
            ReadSet::Widest => LooseDepth::WIDEST,
        }
    }
}

impl Reach for Reads
{
    /// No index.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn closed() -> Self
    {
        Self(ReadSet::Word(0))
    }

    /// Every binder.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn widest() -> Self
    {
        Self(ReadSet::Widest)
    }

    /// The one index `index`: one bit of a word below the word's width, so a
    /// variable's set allocates nothing there.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn variable(index: DeBruijnIndex) -> Self
    {
        let position = u32::from(index);
        if position < WORD_INDICES {
            Self(ReadSet::Word(1_u64.unbounded_shl(position)))
        }
        else {
            Self(ReadSet::Spilled(Box::new([index])))
        }
    }

    /// The union of two sets.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the indices either set reads; the widest reach when either
    ///   is.
    /// - provides: a former's reads as its children's.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the witness reads back unions inside and across the
    ///   word's width.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Reads::of`].
    /// - witness: `support::tests::reads_are_exactly_the_free_indices`
    #[inline]
    fn join(
        self,
        other: Self,
    ) -> Self
    {
        match (self.0, other.0) {
            (ReadSet::Word(left), ReadSet::Word(right)) => Self(ReadSet::Word(left | right)),
            (ReadSet::Widest, _) | (_, ReadSet::Widest) => Self(ReadSet::Widest),
            (left, right) => {
                let (left, right) = (Self(left), Self(right));
                let (Maybe::Present(mut first), Maybe::Present(mut second)) =
                    (left.indices(), right.indices())
                else {
                    return Self(ReadSet::Widest);
                };
                let mut merged = Vec::new();
                let (mut next_first, mut next_second) = (first.next(), second.next());
                loop {
                    match (next_first, next_second) {
                        (Some(one), Some(two)) if one < two => {
                            merged.push(one);
                            next_first = first.next();
                        },
                        (Some(one), Some(two)) if two < one => {
                            merged.push(two);
                            next_second = second.next();
                        },
                        (Some(one), Some(_)) => {
                            merged.push(one);
                            next_first = first.next();
                            next_second = second.next();
                        },
                        (Some(one), None) => {
                            merged.push(one);
                            next_first = first.next();
                        },
                        (None, Some(two)) => {
                            merged.push(two);
                            next_second = second.next();
                        },
                        (None, None) => return Self::of(merged),
                    }
                }
            },
        }
    }

    /// The set seen from outside one binder: index zero dropped, every other
    /// one lower.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `i` for every `i + 1` the set reads; the widest reach stays
    ///   widest.
    /// - provides: a binding former's reads of its body.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the witness steps sets out across the word's width
    ///   and reads them back.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Reads::of`].
    /// - witness: `support::tests::reads_are_exactly_the_free_indices`
    #[inline]
    fn under_binder(self) -> Self
    {
        match self.0 {
            ReadSet::Word(word) => Self(ReadSet::Word(word.unbounded_shr(1))),
            ReadSet::Spilled(indices) => Self::of(
                indices
                    .iter()
                    .filter_map(|&index| u32::from(index).checked_sub(1).map(DeBruijnIndex::from))
                    .collect(),
            ),
            ReadSet::Widest => Self(ReadSet::Widest),
        }
    }
}

/// The indices a [`Reads`] holds, ascending.
#[derive(Clone, Debug)]
pub enum ReadIndices<'reads>
{
    /// The indices still to come of a word: its set bits.
    Word(u64),
    /// The indices still to come of a spilled set.
    Spilled(core::slice::Iter<'reads, DeBruijnIndex>),
}

impl Iterator for ReadIndices<'_>
{
    type Item = DeBruijnIndex;

    /// The next index, the lowest bit or entry not yet yielded.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn next(&mut self) -> Option<DeBruijnIndex>
    {
        match *self {
            Self::Word(ref mut word) => {
                if *word == 0 {
                    return None;
                }
                let index = word.trailing_zeros();
                *word &= word.wrapping_sub(1);
                Some(DeBruijnIndex::from(index))
            },
            Self::Spilled(ref mut indices) => indices.next().copied(),
        }
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

/// The complete support of one goal expansion, as the name of its goal record.
///
/// The support holds no arena id: it carries the name the session's content
/// table gives the goal's record — its direction, obligation, expected type and
/// the binders it reads — so two supports agree exactly when they name one
/// record, and the table names one record exactly when the content agrees. The
/// digest is read off that name: a bucket selector that narrows and never
/// decides.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct NodeSupport
{
    /// Which machine asked.
    plane: SupportPlane,
    /// The goal record's name in the session's table.
    goal: ContentId,
}

impl NodeSupport
{
    /// Build the support of `goal` under `context`, taking only the binders
    /// the goal's node reads.
    ///
    /// A type-formation goal reads binders exactly as a term goal does, because
    /// a type can carry a code and a code can be a variable. A type that
    /// carries none reads nothing and takes the empty telescope, which is what
    /// keeps the closed-type case free.
    ///
    /// # Specification
    /// - requires: `context` is the machine's typing context at the expansion,
    ///   outermost first; `session` is this check's own, and every support a
    ///   memo holds was built against the same one.
    /// - ensures: two supports are equal exactly when the goals ask the same
    ///   question of the same content under binders that agree at every
    ///   position the node reads. A node whose reads are unknown, or name a
    ///   position past the context, takes the whole context, so an
    ///   over-estimate can only split a support and never merge two.
    /// - provides: the memo key, with the goal's plane checked by the
    ///   predicate. Provenance and agreement across independent goals need a
    ///   second goal and remain obligations of the paired witnesses below.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decision surfaces are the plane split, the reads
    ///   lookup, and the positions read, separated by a closed node under a
    ///   non-empty context (empty telescope), a binder-reading node under two
    ///   differing contexts (two supports), a binder-reading node under two
    ///   contexts agreeing where it looks (one support), a node reading index
    ///   one and not zero under contexts differing only at zero (one support),
    ///   and a type goal under a non-empty context (empty telescope), each
    ///   asserted exactly.
    /// - witness: `support::tests::a_closed_node_takes_no_telescope`
    /// - witness: `support::tests::a_binder_reading_node_splits_on_what_it_reads`
    /// - witness: `support::tests::a_binder_reading_node_collapses_where_its_reads_agree`
    /// - witness: `support::tests::an_unread_binder_is_not_in_the_key`
    /// - witness: `support::tests::a_closed_type_goal_reads_no_binder`
    /// - witness: `support::tests::a_code_carrying_type_reads_its_binder`
    #[spec(ensures: |ret| ret.plane == match goal {
        SupportGoal::ValueTypeLevel(_) | SupportGoal::CompTypeLevel(_) => SupportPlane::Type,
        SupportGoal::SynthValue(_) | SupportGoal::CheckValue(_, _)
        | SupportGoal::SynthComp(_) | SupportGoal::CheckComp(_, _) => SupportPlane::Term,
    })]
    #[inline]
    #[must_use]
    pub fn build(
        arena: &TermArena,
        session: &mut SupportContext,
        goal: SupportGoal,
        context: &[ValueTypeId],
    ) -> Self
    {
        let (plane, reads) = match goal {
            SupportGoal::ValueTypeLevel(id) => (
                SupportPlane::Type,
                session.reads.value_type_reach(arena, id),
            ),
            SupportGoal::CompTypeLevel(id) => {
                (SupportPlane::Type, session.reads.comp_type_reach(arena, id))
            },
            SupportGoal::SynthValue(id) | SupportGoal::CheckValue(id, _) => {
                (SupportPlane::Term, session.reads.value_reach(arena, id))
            },
            SupportGoal::SynthComp(id) | SupportGoal::CheckComp(id, _) => {
                (SupportPlane::Term, session.reads.comp_reach(arena, id))
            },
        };
        let telescope = match read_binders(context, &reads, &mut session.read) {
            Maybe::Present(read) => Telescope::Read(read),
            Maybe::Absent(_) => Telescope::Whole(context),
        };
        let named = support_key(&mut session.table, arena, goal, telescope);
        Self { plane, goal: named }
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

    /// The digest of this support: its plane, and its goal record's name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn digest(&self) -> ContentDigest
    {
        ContentDigest::new(DigestWord::from(self.plane), DigestWord::from(self.goal))
    }

    /// The deciding comparison: the goal records' names, which the session's
    /// table assigns exactly when the records' content agrees.
    ///
    /// The digest is never consulted here. It is read off the same name, so a
    /// bucket holds one support, and this comparison is what serves a hit.
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
    /// - provides: the deciding comparison every hit the checker adopts is
    ///   served on.
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
            /// The walk could not read the node.
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

/// The per-node binder reach in the lattice `R`, computed once per distinct
/// node and cached.
#[derive(Clone, Debug)]
pub struct Reaches<R>
{
    /// Reaches already computed for value nodes.
    values: BTreeMap<ValueId, R>,
    /// Reaches already computed for computation nodes.
    computations: BTreeMap<ComputationId, R>,
    /// Reaches already computed for value-type nodes.
    value_types: BTreeMap<ValueTypeId, R>,
    /// Reaches already computed for computation-type nodes.
    comp_types: BTreeMap<CompTypeId, R>,
    /// The walk's task stack, reused across walks.
    tasks: Vec<ReachTask>,
}

/// How far each node reaches: one more than its largest free index.
pub type LooseDepths = Reaches<LooseDepth>;

impl<R> Default for Reaches<R>
{
    /// Nothing computed.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self {
            values: BTreeMap::new(),
            computations: BTreeMap::new(),
            value_types: BTreeMap::new(),
            comp_types: BTreeMap::new(),
            tasks: Vec::new(),
        }
    }
}

/// One step of the iterative bottom-up reach walk.
#[derive(Clone, Copy, Debug)]
enum ReachTask
{
    /// Ensure this value node's children are computed, then finish it.
    OpenValue(ValueId),
    /// Combine this value node's children's reaches into its own.
    CloseValue(ValueId),
    /// Ensure this computation node's children are computed, then finish it.
    OpenComp(ComputationId),
    /// Combine this computation node's children's reaches into its own.
    CloseComp(ComputationId),
    /// Ensure this value-type node's children are computed, then finish it.
    OpenValueType(ValueTypeId),
    /// Combine this value-type node's children's reaches into its own.
    CloseValueType(ValueTypeId),
    /// Ensure this computation-type node's children are computed, then finish
    /// it.
    OpenCompType(CompTypeId),
    /// Combine this computation-type node's children's reaches into its own.
    CloseCompType(CompTypeId),
}

impl<R: Reach> Reaches<R>
{
    /// An empty cache.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new() -> Self
    {
        Self::default()
    }

    /// The binder reach of a value node.
    ///
    /// # Specification
    /// - requires: cached positions still denote the same nodes in this arena;
    ///   unreadable roots are allowed and answered conservatively.
    /// - ensures: the node's reach in `R` — for [`LooseDepth`] one more than
    ///   the largest free de Bruijn index, for [`Reads`] exactly the free
    ///   indices; an unreadable node reaches widest, and stays widest through
    ///   enclosing binders. The walk is iterative and combines each distinct
    ///   node at most once.
    /// - provides: the reads of a value goal's support. The predicate checks
    ///   the recorded answer and unreadable-root boundary; binder recurrence
    ///   and sharing are witnessed without a second walk.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decision surfaces are the per-former join and the
    ///   binder step, separated by a closed leaf (zero), a bare variable at
    ///   index `i` (`i + 1`), a lambda over a variable (closed from outside),
    ///   and an unreadable id (widest), each asserted exactly.
    /// - witness: `support::tests::a_closed_value_reaches_no_binder`
    /// - witness: `support::tests::a_variable_reaches_one_more_than_its_index`
    /// - witness: `support::tests::a_binder_closes_its_body`
    /// - witness: `support::tests::an_unreadable_node_reaches_widest`
    /// - witness: `support::tests::reads_are_exactly_the_free_indices`
    #[spec(ensures: |ret| self.values.get(&root) == Some(&ret)
        && (arena.value(root).is_some() || ret == R::widest()))]
    #[inline]
    pub fn value_reach(
        &mut self,
        arena: &TermArena,
        root: ValueId,
    ) -> R
    {
        self.run(arena, ReachTask::OpenValue(root));
        self.cached_value(root)
    }

    /// The binder reach of a computation node; see [`Self::value_reach`].
    ///
    /// # Specification
    /// - requires: cached positions still denote the same nodes in this arena.
    /// - ensures: as [`Self::value_reach`], over the computation families.
    /// - provides: the reads of a computation goal's support; the predicate
    ///   checks cache agreement and the unreadable-root boundary.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::value_reach`]; the residues are the three
    ///   binding formers, whose bound positions each step out by one.
    /// - witness: `support::tests::a_binder_closes_its_body`
    /// - witness: `support::tests::a_bind_closes_only_its_body`
    #[spec(ensures: |ret| self.computations.get(&root) == Some(&ret)
        && (arena.computation(root).is_some() || ret == R::widest()))]
    #[inline]
    pub fn comp_reach(
        &mut self,
        arena: &TermArena,
        root: ComputationId,
    ) -> R
    {
        self.run(arena, ReachTask::OpenComp(root));
        self.cached_comp(root)
    }

    /// The binder reach of a value-type node; see [`Self::value_reach`].
    ///
    /// # Specification
    /// - requires: cached positions still denote the same nodes in this arena.
    /// - ensures: as [`Self::value_reach`], over the value-type family, where
    ///   the reach comes entirely from the codes the type carries.
    /// - provides: the reads of a value-type formation goal's support, with
    ///   cache agreement and unreadable roots checked directly.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the surfaces are the code edge and the dependent
    ///   arrow's binder step, separated by a closed type (zero), a type over a
    ///   variable code (`i + 1`), and a dependent arrow whose codomain reads
    ///   only its own binder (closed from outside).
    /// - witness: `support::tests::a_type_reaches_through_its_codes`
    #[spec(ensures: |ret| self.value_types.get(&root) == Some(&ret)
        && (arena.value_type(root).is_some() || ret == R::widest()))]
    #[inline]
    pub fn value_type_reach(
        &mut self,
        arena: &TermArena,
        root: ValueTypeId,
    ) -> R
    {
        self.run(arena, ReachTask::OpenValueType(root));
        self.cached_value_type(root)
    }

    /// The binder reach of a computation-type node; see
    /// [`Self::value_type_reach`].
    ///
    /// # Specification
    /// - requires: cached positions still denote the same nodes in this arena.
    /// - ensures: as [`Self::value_type_reach`], over the computation-type
    ///   family.
    /// - provides: the reads of a computation-type formation goal's support,
    ///   with cache agreement and unreadable roots checked directly.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::value_type_reach`]; the residue is the
    ///   dependent arrow, whose codomain steps out by one and whose domain does
    ///   not.
    /// - witness: `support::tests::a_type_reaches_through_its_codes`
    #[spec(ensures: |ret| self.comp_types.get(&root) == Some(&ret)
        && (arena.comp_type(root).is_some() || ret == R::widest()))]
    #[inline]
    pub fn comp_type_reach(
        &mut self,
        arena: &TermArena,
        root: CompTypeId,
    ) -> R
    {
        self.run(arena, ReachTask::OpenCompType(root));
        self.cached_comp_type(root)
    }

    /// Drive the reach walk to completion from one root task.
    ///
    /// # Specification
    /// - requires: the root is an open task and cached arena positions are
    ///   unchanged.
    /// - ensures: every node reachable from the root has a cached reach.
    /// - provides: the shared engine of the four reach families. The predicate
    ///   checks root completion; the witnesses observe child joins and binder
    ///   scope without repeating the entire traversal.
    /// - fails: never — an unreadable node caches the widest reach.
    /// - panics: none.
    ///
    /// # Termination
    /// - reason: the walk is a loop over an explicit task stack, not recursion.
    /// - measure: the number of reachable nodes without a cached reach, which
    ///   strictly falls at every close step and never rises, since an open on a
    ///   cached node pushes nothing.
    /// - boundedness: the arena is finite and children have strictly smaller
    ///   ids, so the reachable set is finite and acyclic.
    /// - input recursion: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 on closed leaves, open variables, joined children,
    ///   binding bodies, type codes and unreadable roots on all four planes;
    ///   exact resulting reaches separate missing child work and wrong binder
    ///   scope.
    /// - witness: `support::tests::a_variable_reaches_one_more_than_its_index`
    /// - witness: `support::tests::a_bind_closes_only_its_body`
    /// - witness: `support::tests::a_type_reaches_through_its_codes`
    /// - witness: `support::tests::an_unreadable_node_reaches_widest`
    #[spec(
        requires: matches!(root, ReachTask::OpenValue(_) | ReachTask::OpenComp(_)
            | ReachTask::OpenValueType(_) | ReachTask::OpenCompType(_)),
        ensures: match root {
            ReachTask::OpenValue(id) | ReachTask::CloseValue(id) => self.values.contains_key(&id),
            ReachTask::OpenComp(id) | ReachTask::CloseComp(id) => self.computations.contains_key(&id),
            ReachTask::OpenValueType(id) | ReachTask::CloseValueType(id) => self.value_types.contains_key(&id),
            ReachTask::OpenCompType(id) | ReachTask::CloseCompType(id) => self.comp_types.contains_key(&id),
        },
    )]
    fn run(
        &mut self,
        arena: &TermArena,
        root: ReachTask,
    )
    {
        let mut tasks = core::mem::take(&mut self.tasks);
        tasks.clear();
        tasks.push(root);
        while let Some(task) = tasks.pop() {
            match task {
                ReachTask::OpenValue(id) => {
                    if self.values.contains_key(&id) {
                        continue;
                    }
                    let Some(node) = arena.value(id)
                    else {
                        let _prior = self.values.insert(id, R::widest());
                        continue;
                    };
                    tasks.push(ReachTask::CloseValue(id));
                    match *node {
                        Value::Constructor {
                            datatype,
                            ref fields,
                            ..
                        } => {
                            tasks.push(ReachTask::OpenValueType(datatype));
                            tasks.extend(fields.iter().copied().map(ReachTask::OpenValue));
                        },
                        Value::Record(ref fields) => {
                            tasks.extend(fields.values().copied().map(ReachTask::OpenValue));
                        },
                        Value::Variable(_)
                        | Value::Constant(_)
                        | Value::ListNil
                        | Value::Literal(_) => {},
                        Value::PathEquiv {
                            path_type,
                            forward,
                            backward,
                            ..
                        } => {
                            tasks.push(ReachTask::OpenValueType(path_type));
                            tasks.push(ReachTask::OpenValue(forward));
                            tasks.push(ReachTask::OpenValue(backward));
                        },
                        Value::SessionPath {
                            path_type,
                            payload_paths,
                            ..
                        }
                        | Value::SessionFlow {
                            flow_type: path_type,
                            payload_paths,
                            ..
                        } => {
                            tasks.push(ReachTask::OpenValueType(path_type));
                            tasks.push(ReachTask::OpenValue(payload_paths));
                        },
                        Value::PathRefl(code)
                        | Value::Univalence(code)
                        | Value::Here { point: code, .. }
                        | Value::Stay { point: code, .. } => {
                            tasks.push(ReachTask::OpenValue(code));
                        },
                        Value::Higher {
                            evidence: ref values,
                            ..
                        }
                        | Value::QuantifiedEvaluation {
                            children: ref values,
                            ..
                        } => {
                            tasks.extend(values.iter().copied().map(ReachTask::OpenValue));
                        },
                        Value::HigherEvaluation { ref components, .. } => tasks.extend(
                            components
                                .iter()
                                .flat_map(|component| {
                                    [component.left, component.right, component.evidence]
                                })
                                .map(ReachTask::OpenValue),
                        ),
                        Value::ForwardFlow {
                            flow_type,
                            translator,
                            ref outputs,
                            ..
                        } => {
                            tasks.push(ReachTask::OpenValueType(flow_type));
                            tasks.push(ReachTask::OpenValue(translator));
                            tasks.extend(outputs.iter().copied().map(ReachTask::OpenValue));
                        },
                        Value::FunctionFlow {
                            flow_type,
                            domain,
                            codomain,
                        } => {
                            tasks.push(ReachTask::OpenValueType(flow_type));
                            tasks.push(ReachTask::OpenValue(domain));
                            tasks.push(ReachTask::OpenValue(codomain));
                        },
                        Value::PathProduct(first, second)
                        | Value::FlowProduct(first, second)
                        | Value::ListCons(first, second)
                        | Value::StaticApplication(first, second)
                        | Value::Then { first, second, .. } => {
                            tasks.push(ReachTask::OpenValue(first));
                            tasks.push(ReachTask::OpenValue(second));
                        },
                        Value::Tuple(ref components) => {
                            tasks.extend(components.iter().copied().map(ReachTask::OpenValue));
                        },
                        Value::Injection(_, body) | Value::Lift { body, .. } => {
                            tasks.push(ReachTask::OpenValue(body));
                        },
                        Value::Thunk(body) | Value::Returned(body) => {
                            tasks.push(ReachTask::OpenComp(body));
                        },
                        Value::Quote(quoted) => tasks.push(ReachTask::OpenValueType(quoted)),
                        Value::QuoteComputation(quoted) => {
                            tasks.push(ReachTask::OpenCompType(quoted));
                        },
                    }
                },
                ReachTask::CloseValue(id) => {
                    let reach = self.combine_value(arena, id);
                    let _prior = self.values.insert(id, reach);
                },
                ReachTask::OpenComp(id) => {
                    if self.computations.contains_key(&id) {
                        continue;
                    }
                    let Some(node) = arena.computation(id)
                    else {
                        let _prior = self.computations.insert(id, R::widest());
                        continue;
                    };
                    tasks.push(ReachTask::CloseComp(id));
                    match *node {
                        Computation::DataCase {
                            scrutinee,
                            motive,
                            ref branches,
                        } => {
                            tasks.push(ReachTask::OpenValue(scrutinee));
                            tasks.push(ReachTask::OpenCompType(motive));
                            tasks.extend(branches.iter().copied().map(ReachTask::OpenComp));
                        },
                        Computation::SigmaSplit {
                            scrutinee,
                            motive,
                            body,
                        } => {
                            tasks.extend([
                                ReachTask::OpenValue(scrutinee),
                                ReachTask::OpenCompType(motive),
                                ReachTask::OpenComp(body),
                            ]);
                        },
                        Computation::RecordProjection(record, _)
                        | Computation::TupleProjection(record, _) => {
                            tasks.push(ReachTask::OpenValue(record));
                        },
                        Computation::ListFold {
                            element,
                            result,
                            list,
                            on_nil,
                            on_cons,
                        } => {
                            tasks.extend([
                                ReachTask::OpenValueType(element),
                                ReachTask::OpenValueType(result),
                                ReachTask::OpenValue(list),
                                ReachTask::OpenComp(on_nil),
                                ReachTask::OpenComp(on_cons),
                            ]);
                        },
                        Computation::Transport(path, value) => {
                            tasks.push(ReachTask::OpenValue(path));
                            tasks.push(ReachTask::OpenValue(value));
                        },
                        Computation::PathTransport {
                            motive,
                            path,
                            value,
                        }
                        | Computation::Ride {
                            motive,
                            flow: path,
                            value,
                        } => {
                            tasks.push(ReachTask::OpenValueType(motive));
                            tasks.push(ReachTask::OpenValue(path));
                            tasks.push(ReachTask::OpenValue(value));
                        },
                        Computation::TelescopeTransport {
                            motive,
                            path,
                            start,
                            over,
                            value,
                        }
                        | Computation::TelescopeRide {
                            motive,
                            flow: path,
                            start,
                            over,
                            value,
                        } => {
                            tasks.extend([
                                ReachTask::OpenCompType(motive),
                                ReachTask::OpenValue(path),
                                ReachTask::OpenValue(start),
                                ReachTask::OpenValue(over),
                                ReachTask::OpenValue(value),
                            ]);
                        },
                        Computation::RelatedApplication {
                            path,
                            left,
                            right,
                            evidence,
                            body,
                        } => {
                            tasks.extend([
                                ReachTask::OpenValue(path),
                                ReachTask::OpenValue(left),
                                ReachTask::OpenValue(right),
                                ReachTask::OpenValue(evidence),
                                ReachTask::OpenComp(body),
                            ]);
                        },
                        Computation::Lambda(body)
                        | Computation::Fixpoint { body, .. }
                        | Computation::Project(_, body) => {
                            tasks.push(ReachTask::OpenComp(body));
                        },
                        Computation::Application(head, argument) => {
                            tasks.push(ReachTask::OpenComp(head));
                            tasks.push(ReachTask::OpenValue(argument));
                        },
                        Computation::Return(value) | Computation::Force(value) => {
                            tasks.push(ReachTask::OpenValue(value));
                        },
                        Computation::Bind(bound, body) | Computation::With(bound, body) => {
                            tasks.push(ReachTask::OpenComp(bound));
                            tasks.push(ReachTask::OpenComp(body));
                        },
                        Computation::Case {
                            scrutinee,
                            ref branches,
                        } => {
                            tasks.push(ReachTask::OpenValue(scrutinee));
                            tasks.extend(branches.iter().copied().map(ReachTask::OpenComp));
                        },
                    }
                },
                ReachTask::CloseComp(id) => {
                    let reach = self.combine_comp(arena, id);
                    let _prior = self.computations.insert(id, reach);
                },
                ReachTask::OpenValueType(id) => {
                    if self.value_types.contains_key(&id) {
                        continue;
                    }
                    let Some(node) = arena.value_type(id)
                    else {
                        let _prior = self.value_types.insert(id, R::widest());
                        continue;
                    };
                    tasks.push(ReachTask::CloseValueType(id));
                    match *node {
                        ValueType::Data { ref arguments, .. } => {
                            tasks.extend(arguments.iter().copied().map(ReachTask::OpenValue));
                        },
                        ValueType::Record(ref fields) => {
                            tasks.extend(fields.values().copied().map(ReachTask::OpenValueType));
                        },
                        ValueType::Base(_)
                        | ValueType::Universe { .. }
                        | ValueType::Abstract(_) => {},
                        ValueType::Product(ref parts) | ValueType::Sum(ref parts) => {
                            tasks.extend(parts.iter().copied().map(ReachTask::OpenValueType));
                        },
                        ValueType::StaticPi {
                            domain: first,
                            codomain: second,
                        }
                        | ValueType::Sigma { first, second } => {
                            tasks.push(ReachTask::OpenValueType(first));
                            tasks.push(ReachTask::OpenValueType(second));
                        },
                        ValueType::PathUniverse(source, target)
                        | ValueType::FlowUniverse(source, target) => {
                            tasks.push(ReachTask::OpenValue(source));
                            tasks.push(ReachTask::OpenValue(target));
                        },
                        ValueType::Path {
                            domain,
                            left,
                            right,
                        }
                        | ValueType::Flow {
                            domain,
                            source: left,
                            target: right,
                        }
                        | ValueType::Bridge {
                            domain,
                            left,
                            right,
                        } => {
                            tasks.push(ReachTask::OpenValueType(domain));
                            tasks.push(ReachTask::OpenValue(left));
                            tasks.push(ReachTask::OpenValue(right));
                        },
                        ValueType::Session {
                            payloads: inner, ..
                        }
                        | ValueType::Lift { inner, .. }
                        | ValueType::List(inner)
                        | ValueType::Staged { base: inner, .. } => {
                            tasks.push(ReachTask::OpenValueType(inner));
                        },
                        ValueType::Thunk(body) => tasks.push(ReachTask::OpenCompType(body)),
                        ValueType::Element { code, .. } => {
                            tasks.push(ReachTask::OpenValue(code));
                        },
                    }
                },
                ReachTask::CloseValueType(id) => {
                    let reach = self.combine_value_type(arena, id);
                    let _prior = self.value_types.insert(id, reach);
                },
                ReachTask::OpenCompType(id) => {
                    if self.comp_types.contains_key(&id) {
                        continue;
                    }
                    let Some(node) = arena.comp_type(id)
                    else {
                        let _prior = self.comp_types.insert(id, R::widest());
                        continue;
                    };
                    tasks.push(ReachTask::CloseCompType(id));
                    match *node {
                        CompType::Returner(result) => {
                            tasks.push(ReachTask::OpenValueType(result));
                        },
                        CompType::Arrow { domain, codomain }
                        | CompType::Pi { domain, codomain } => {
                            tasks.push(ReachTask::OpenValueType(domain));
                            tasks.push(ReachTask::OpenCompType(codomain));
                        },
                        CompType::Element { code, .. } => {
                            tasks.push(ReachTask::OpenValue(code));
                        },
                        CompType::With(left, right) => {
                            tasks.push(ReachTask::OpenCompType(left));
                            tasks.push(ReachTask::OpenCompType(right));
                        },
                        CompType::Codata { ref arguments, .. } => {
                            tasks.extend(arguments.iter().copied().map(ReachTask::OpenValue));
                        },
                    }
                },
                ReachTask::CloseCompType(id) => {
                    let reach = self.combine_comp_type(arena, id);
                    let _prior = self.comp_types.insert(id, reach);
                },
            }
        }
        self.tasks = tasks;
    }

    /// A cached value reach, conservatively widest when absent.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the reach already computed for `id`, and the widest reach
    ///   where none is cached.
    /// - provides: the conservative read the combine steps compose, so a gap in
    ///   the cache widens the key's telescope rather than narrowing it.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 on zero, a nonzero variable reach and an unreadable
    ///   value; exact observations distinguish a missing conservative fallback
    ///   from a valid closed answer.
    /// - witness: `support::tests::a_closed_value_reaches_no_binder`
    /// - witness: `support::tests::a_variable_reaches_one_more_than_its_index`
    /// - witness: `support::tests::an_unreadable_node_reaches_widest`
    #[spec(ensures: |ret| ret == self.values.get(&id).cloned().unwrap_or_else(R::widest))]
    #[inline]
    fn cached_value(
        &self,
        id: ValueId,
    ) -> R
    {
        self.values.get(&id).cloned().unwrap_or_else(R::widest)
    }

    /// A cached computation reach, conservatively widest when absent.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as `cached_value`, on the computation plane.
    /// - provides: the conservative read the combine steps compose.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 on an open return, its binding lambda and an unreadable
    ///   computation; exact reaches distinguish closing the body from narrowing
    ///   a missing answer.
    /// - witness: `support::tests::a_binder_closes_its_body`
    /// - witness: `support::tests::an_unreadable_node_reaches_widest`
    #[spec(ensures: |ret| ret == self.computations.get(&id).cloned().unwrap_or_else(R::widest))]
    #[inline]
    fn cached_comp(
        &self,
        id: ComputationId,
    ) -> R
    {
        self.computations
            .get(&id)
            .cloned()
            .unwrap_or_else(R::widest)
    }

    /// A cached value-type reach, conservatively widest when absent.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as `cached_value`, on the value-type plane.
    /// - provides: the conservative read the combine steps compose.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 on a closed type, a variable code and an unreadable
    ///   value type; the zero, nonzero and widest answers separate cache-plane
    ///   and fallback faults.
    /// - witness: `support::tests::a_type_reaches_through_its_codes`
    /// - witness: `support::tests::an_unreadable_node_reaches_widest`
    #[spec(ensures: |ret| ret == self.value_types.get(&id).cloned().unwrap_or_else(R::widest))]
    #[inline]
    fn cached_value_type(
        &self,
        id: ValueTypeId,
    ) -> R
    {
        self.value_types.get(&id).cloned().unwrap_or_else(R::widest)
    }

    /// A cached computation-type reach, conservatively widest when absent.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as `cached_value`, on the computation-type plane.
    /// - provides: the conservative read the combine steps compose.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 on a dependent codomain and an unreadable computation
    ///   type; exact external reach separates binder adjustment and
    ///   conservative fallback.
    /// - witness: `support::tests::a_type_reaches_through_its_codes`
    /// - witness: `support::tests::an_unreadable_node_reaches_widest`
    #[spec(ensures: |ret| ret == self.comp_types.get(&id).cloned().unwrap_or_else(R::widest))]
    #[inline]
    fn cached_comp_type(
        &self,
        id: CompTypeId,
    ) -> R
    {
        self.comp_types.get(&id).cloned().unwrap_or_else(R::widest)
    }

    /// Combine one value-type node's children's reaches into its own.
    ///
    /// A type's reach comes from the codes it carries, and the dependent pair
    /// is the one binding former on the positive side: its second factor is
    /// read one binder further out than it computed, and its first is not.
    ///
    /// # Specification
    /// - requires: this node's children already have their reaches cached,
    ///   which the task order establishes.
    /// - ensures: zero for a former carrying no code, the join of the
    ///   children's reaches for a former carrying several, with the dependent
    ///   pair's second factor read one binder further out than it computed, the
    ///   code's own reach for a universe-decoding former, and the widest reach
    ///   where the node could not be read.
    /// - provides: the value-type arm of the bottom-up reach recurrence.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 on closed types, variable codes and unreadable roots;
    ///   exact reaches separate code traversal, leaf closure and conservative
    ///   refusal. Composite joins are local predicate obligations, not an
    ///   exhaustive graph proof.
    /// - witness: `support::tests::a_type_reaches_through_its_codes`
    /// - witness: `support::tests::an_unreadable_node_reaches_widest`
    /// - witness: `support::tests::a_closed_type_goal_reads_no_binder`
    #[spec(ensures: |ret| ret == arena.value_type(id).map_or_else(R::widest, |matched_native_node| match *matched_native_node {
ValueType::Data { ref arguments, .. } => arguments.iter().fold(R::closed(), |depth, id| depth.join(self.cached_value(*id))),
ValueType::Record(ref fields) => fields.values().fold(R::closed(), |depth, id| depth.join(self.cached_value_type(*id))),
ValueType::Base(_) | ValueType::Universe { .. } | ValueType::Abstract(_) => R::closed(),
ValueType::PathUniverse(a, b) | ValueType::FlowUniverse(a, b) => self.cached_value(a).join(self.cached_value(b)),
ValueType::Path { domain, left, right } | ValueType::Flow { domain, source: left, target: right } | ValueType::Bridge { domain, left, right } => self.cached_value_type(domain).join(self.cached_value(left)).join(self.cached_value(right)),
ValueType::Product(ref parts) | ValueType::Sum(ref parts) => parts.iter().fold(R::closed(), |depth, id| depth.join(self.cached_value_type(*id))),
ValueType::StaticPi { domain: a, codomain: b } => self.cached_value_type(a).join(self.cached_value_type(b)),
ValueType::Sigma { first, second } => self.cached_value_type(first).join(self.cached_value_type(second).under_binder()),
ValueType::Session { payloads: inner, .. } | ValueType::Lift { inner, .. } | ValueType::List(inner) | ValueType::Staged { base: inner, .. } => self.cached_value_type(inner),
ValueType::Thunk(body) => self.cached_comp_type(body),
ValueType::Element { code, .. } => self.cached_value(code),
}))]
    fn combine_value_type(
        &self,
        arena: &TermArena,
        id: ValueTypeId,
    ) -> R
    {
        let Some(node) = arena.value_type(id)
        else {
            return R::widest();
        };
        match *node {
            ValueType::Data { ref arguments, .. } => arguments
                .iter()
                .fold(R::closed(), |depth, id| depth.join(self.cached_value(*id))),
            ValueType::Record(ref fields) => fields.values().fold(R::closed(), |depth, id| {
                depth.join(self.cached_value_type(*id))
            }),
            ValueType::PathUniverse(source, target) | ValueType::FlowUniverse(source, target) => {
                self.cached_value(source).join(self.cached_value(target))
            },
            ValueType::Path {
                domain,
                left,
                right,
            }
            | ValueType::Flow {
                domain,
                source: left,
                target: right,
            }
            | ValueType::Bridge {
                domain,
                left,
                right,
            } => self
                .cached_value_type(domain)
                .join(self.cached_value(left))
                .join(self.cached_value(right)),
            ValueType::Base(_) | ValueType::Universe { .. } | ValueType::Abstract(_) => R::closed(),
            ValueType::Product(ref parts) | ValueType::Sum(ref parts) => {
                parts.iter().fold(R::closed(), |depth, id| {
                    depth.join(self.cached_value_type(*id))
                })
            },
            ValueType::StaticPi {
                domain: first,
                codomain: second,
            } => self
                .cached_value_type(first)
                .join(self.cached_value_type(second)),
            ValueType::Sigma { first, second } => self
                .cached_value_type(first)
                .join(self.cached_value_type(second).under_binder()),
            ValueType::Session {
                payloads: inner, ..
            }
            | ValueType::Lift { inner, .. }
            | ValueType::List(inner)
            | ValueType::Staged { base: inner, .. } => self.cached_value_type(inner),
            ValueType::Thunk(body) => self.cached_comp_type(body),
            ValueType::Element { code, .. } => self.cached_value(code),
        }
    }

    /// Combine one computation-type node's children's reaches into its own.
    ///
    /// The dependent arrow is the one binding former on the negative side: its
    /// codomain is read one binder further out than it computed, and its domain
    /// is not.
    ///
    /// # Specification
    /// - requires: this node's children already have their reaches cached.
    /// - ensures: the join of domain and codomain reaches, with the dependent
    ///   arrow's codomain read one binder further out than it computed, the
    ///   code's own reach for a computation decode, and the widest reach where
    ///   the node could not be read.
    /// - provides: the computation-type arm of the recurrence, and the one
    ///   binding former on the negative side.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 on a returner carrying a variable code, a dependent
    ///   arrow and an unreadable root; exact reaches distinguish the codomain
    ///   binder from an unbound domain and conservative refusal.
    /// - witness: `support::tests::a_type_reaches_through_its_codes`
    /// - witness: `support::tests::an_unreadable_node_reaches_widest`
    #[spec(ensures: |ret| ret == arena.comp_type(id).map_or_else(R::widest, |node| match *node {
        CompType::Returner(result) => self.cached_value_type(result),
        CompType::Arrow { domain, codomain } => self.cached_value_type(domain).join(self.cached_comp_type(codomain)),
        CompType::Pi { domain, codomain } => self.cached_value_type(domain).join(self.cached_comp_type(codomain).under_binder()),
        CompType::Element { code, .. } => self.cached_value(code),
        CompType::With(left, right) => self.cached_comp_type(left).join(self.cached_comp_type(right)),
        CompType::Codata { ref arguments, .. } => arguments.iter().fold(R::closed(), |depth, id| depth.join(self.cached_value(*id))),
    }))]
    fn combine_comp_type(
        &self,
        arena: &TermArena,
        id: CompTypeId,
    ) -> R
    {
        let Some(node) = arena.comp_type(id)
        else {
            return R::widest();
        };
        match *node {
            CompType::Returner(result) => self.cached_value_type(result),
            CompType::Arrow { domain, codomain } => self
                .cached_value_type(domain)
                .join(self.cached_comp_type(codomain)),
            CompType::Pi { domain, codomain } => self
                .cached_value_type(domain)
                .join(self.cached_comp_type(codomain).under_binder()),
            CompType::Element { code, .. } => self.cached_value(code),
            CompType::With(left, right) => self
                .cached_comp_type(left)
                .join(self.cached_comp_type(right)),
            CompType::Codata { ref arguments, .. } => arguments
                .iter()
                .fold(R::closed(), |depth, id| depth.join(self.cached_value(*id))),
        }
    }

    /// Combine one value node's children's reaches into its own.
    ///
    /// A variable at index `i` reaches that index: `i + 1` binders as a depth,
    /// `{i}` as a read — index zero names the innermost slot. No value former
    /// binds, so every other case is the join of its children.
    ///
    /// # Specification
    /// - requires: this node's children already have their reaches cached.
    /// - ensures: a variable's own index's reach, the closed reach for a closed
    ///   former, the quoted type's reach for a quote, and the join of the
    ///   children's reaches otherwise; the widest reach where the node could
    ///   not be read. No value former binds.
    /// - provides: the value arm of the recurrence, and the base case that
    ///   makes an index a reach.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 on closed and joined values, ordinary and maximal
    ///   variable indices, and unreadable roots; exact reaches separate omitted
    ///   children, index offsets and overflow narrowing.
    /// - witness: `support::tests::a_closed_value_reaches_no_binder`
    /// - witness: `support::tests::a_variable_reaches_one_more_than_its_index`
    /// - witness: `support::tests::saturated_reach_remains_conservative_beneath_a_binder`
    /// - witness: `support::tests::an_unreadable_node_reaches_widest`
    /// - witness: `support::tests::a_binder_reading_node_splits_on_what_it_reads`
    /// - witness: `support::tests::reads_are_exactly_the_free_indices`
    #[spec(ensures: |ret| ret == arena.value(id).map_or_else(R::widest, |matched_native_node| match *matched_native_node {
Value::Constructor { datatype, ref fields, .. } => fields.iter().fold(self.cached_value_type(datatype), |depth, id| depth.join(self.cached_value(*id))),
Value::Record(ref fields) => fields.values().fold(R::closed(), |depth, id| depth.join(self.cached_value(*id))),
Value::Variable(index) => R::variable(index),
Value::ListNil | Value::Constant(_) | Value::Literal(_) => R::closed(),
Value::Tuple(ref components) => components.iter().fold(R::closed(), |depth, id| depth.join(self.cached_value(*id))),
Value::PathEquiv { path_type, forward, backward, .. } => self.cached_value_type(path_type).join(self.cached_value(forward)).join(self.cached_value(backward)),
Value::SessionPath { path_type: classifier, payload_paths, .. } | Value::SessionFlow { flow_type: classifier, payload_paths, .. } => self.cached_value_type(classifier).join(self.cached_value(payload_paths)),
Value::PathRefl(body) | Value::Univalence(body) | Value::Here { point: body, .. } | Value::Stay { point: body, .. } | Value::Injection(_, body) | Value::Lift { body, .. } => self.cached_value(body),
Value::ForwardFlow { flow_type, translator, ref outputs, .. } => outputs.iter().fold(self.cached_value_type(flow_type).join(self.cached_value(translator)), |depth, id| depth.join(self.cached_value(*id))),
Value::FunctionFlow { flow_type, domain, codomain } => self.cached_value_type(flow_type).join(self.cached_value(domain)).join(self.cached_value(codomain)),
Value::Higher { evidence: ref values, .. } | Value::QuantifiedEvaluation { children: ref values, .. } => values.iter().fold(R::closed(), |depth, id| depth.join(self.cached_value(*id))),
Value::HigherEvaluation { ref components, .. } => components.iter().fold(R::closed(), |depth, component| depth.join(self.cached_value(component.left)).join(self.cached_value(component.right)).join(self.cached_value(component.evidence))),
Value::ListCons(a, b) | Value::PathProduct(a, b) | Value::FlowProduct(a, b) | Value::StaticApplication(a, b) | Value::Then { first: a, second: b, .. } => self.cached_value(a).join(self.cached_value(b)),
Value::Thunk(body) | Value::Returned(body) => self.cached_comp(body),
Value::Quote(ty) => self.cached_value_type(ty),
Value::QuoteComputation(ty) => self.cached_comp_type(ty),
}))]
    fn combine_value(
        &self,
        arena: &TermArena,
        id: ValueId,
    ) -> R
    {
        let Some(node) = arena.value(id)
        else {
            return R::widest();
        };
        match *node {
            Value::Constructor {
                datatype,
                ref fields,
                ..
            } => fields
                .iter()
                .fold(self.cached_value_type(datatype), |depth, id| {
                    depth.join(self.cached_value(*id))
                }),
            Value::Record(ref fields) => fields
                .values()
                .fold(R::closed(), |depth, id| depth.join(self.cached_value(*id))),
            Value::Variable(index) => R::variable(index),
            Value::ListNil | Value::Constant(_) | Value::Literal(_) => R::closed(),
            Value::Tuple(ref components) => components
                .iter()
                .fold(R::closed(), |depth, id| depth.join(self.cached_value(*id))),
            Value::PathEquiv {
                path_type,
                forward,
                backward,
                ..
            } => self
                .cached_value_type(path_type)
                .join(self.cached_value(forward))
                .join(self.cached_value(backward)),
            Value::SessionPath {
                path_type,
                payload_paths,
                ..
            }
            | Value::SessionFlow {
                flow_type: path_type,
                payload_paths,
                ..
            } => self
                .cached_value_type(path_type)
                .join(self.cached_value(payload_paths)),
            Value::PathRefl(code)
            | Value::Univalence(code)
            | Value::Here { point: code, .. }
            | Value::Stay { point: code, .. } => self.cached_value(code),
            Value::ForwardFlow {
                flow_type,
                translator,
                ref outputs,
                ..
            } => outputs.iter().fold(
                self.cached_value_type(flow_type)
                    .join(self.cached_value(translator)),
                |depth, id| depth.join(self.cached_value(*id)),
            ),
            Value::FunctionFlow {
                flow_type,
                domain,
                codomain,
            } => self
                .cached_value_type(flow_type)
                .join(self.cached_value(domain))
                .join(self.cached_value(codomain)),
            Value::Higher {
                evidence: ref values,
                ..
            }
            | Value::QuantifiedEvaluation {
                children: ref values,
                ..
            } => values
                .iter()
                .fold(R::closed(), |depth, id| depth.join(self.cached_value(*id))),
            Value::HigherEvaluation { ref components, .. } => {
                components.iter().fold(R::closed(), |depth, component| {
                    depth
                        .join(self.cached_value(component.left))
                        .join(self.cached_value(component.right))
                        .join(self.cached_value(component.evidence))
                })
            },
            Value::PathProduct(first, second)
            | Value::FlowProduct(first, second)
            | Value::ListCons(first, second)
            | Value::StaticApplication(first, second)
            | Value::Then { first, second, .. } => {
                self.cached_value(first).join(self.cached_value(second))
            },
            Value::Injection(_, body) | Value::Lift { body, .. } => self.cached_value(body),
            Value::Thunk(body) | Value::Returned(body) => self.cached_comp(body),
            Value::Quote(quoted) => self.cached_value_type(quoted),
            Value::QuoteComputation(quoted) => self.cached_comp_type(quoted),
        }
    }

    /// Combine one computation node's children's reaches into its own.
    ///
    /// Every binding former is read here: a lambda binds its argument for the
    /// body, a bind binds its payload for the body only (not for the bound
    /// computation), a case binds each summand for its own branch only (not
    /// for the scrutinee), and a dependent split binds the scrutinee for its
    /// motive and both components for its body. Each bound position is
    /// therefore read as many binders further out as its child stands under.
    ///
    /// # Specification
    /// - requires: this node's children already have their reaches cached.
    /// - ensures: the join of the children's reaches, with each bound position
    ///   read one binder further out per binder it stands under — a lambda's
    ///   body, a bind's body but not its bound computation, each case branch
    ///   but not the scrutinee, and a dependent split's motive and body but not
    ///   its scrutinee; the widest reach where the node could not be read.
    /// - provides: the computation arm of the recurrence, where every binder of
    ///   the term language is accounted for.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 on a lambda, the two positions of a bind, saturated
    ///   variable reach and unreadable roots; exact reaches separate closing
    ///   the wrong child and losing the widest sentinel. The case recurrence is
    ///   checked locally, not exhaustively enumerated.
    /// - witness: `support::tests::a_binder_closes_its_body`
    /// - witness: `support::tests::a_bind_closes_only_its_body`
    /// - witness: `support::tests::saturated_reach_remains_conservative_beneath_a_binder`
    /// - witness: `support::tests::an_unreadable_node_reaches_widest`
    #[spec(ensures: |ret| ret == match arena.computation(id) {
        Some(&Computation::DataCase { scrutinee, motive, ref branches }) => branches.iter().fold(self.cached_value(scrutinee).join(self.cached_comp_type(motive).under_binder()), |depth, id| depth.join(self.cached_comp(*id))),
        Some(&Computation::SigmaSplit { scrutinee, motive, body }) => self.cached_value(scrutinee).join(self.cached_comp_type(motive).under_binder()).join(self.cached_comp(body).under_binder().under_binder()),
        Some(&(Computation::RecordProjection(record, _) | Computation::TupleProjection(record, _))) => self.cached_value(record),
        None => R::widest(),
        Some(&Computation::ListFold { element, result, list, on_nil, on_cons }) => self.cached_value_type(element).join(self.cached_value_type(result)).join(self.cached_value(list)).join(self.cached_comp(on_nil)).join(self.cached_comp(on_cons).under_binder().under_binder()),
        Some(&Computation::Transport(path, value)) => self.cached_value(path).join(self.cached_value(value)),
        Some(&(Computation::PathTransport { motive, path, value } | Computation::Ride { motive, flow: path, value })) => self.cached_value_type(motive).under_binder().join(self.cached_value(path)).join(self.cached_value(value)),
        Some(&(Computation::TelescopeTransport { motive, path, start, over, value } | Computation::TelescopeRide { motive, flow: path, start, over, value })) => self.cached_comp_type(motive).join(self.cached_value(path)).join(self.cached_value(start)).join(self.cached_value(over)).join(self.cached_value(value)),
        Some(&Computation::RelatedApplication { path, left, right, evidence, body }) => self.cached_value(path).join(self.cached_value(left)).join(self.cached_value(right)).join(self.cached_value(evidence)).join(self.cached_comp(body).under_binder().under_binder().under_binder()),
        Some(&Computation::Lambda(body) | &Computation::Fixpoint { body, .. }) => self.cached_comp(body).under_binder(),
        Some(&Computation::Application(head, argument)) => self.cached_comp(head).join(self.cached_value(argument)),
        Some(&Computation::Return(value) | &Computation::Force(value)) => self.cached_value(value),
        Some(&Computation::Project(_, pair)) => self.cached_comp(pair),
        Some(&Computation::Bind(bound, body)) => self.cached_comp(bound).join(self.cached_comp(body).under_binder()),
        Some(&Computation::With(left, right)) => self.cached_comp(left).join(self.cached_comp(right)),
        Some(&Computation::Case { scrutinee, ref branches }) => branches.iter().fold(self.cached_value(scrutinee), |depth, id| depth.join(self.cached_comp(*id).under_binder())),
    })]
    fn combine_comp(
        &self,
        arena: &TermArena,
        id: ComputationId,
    ) -> R
    {
        let Some(node) = arena.computation(id)
        else {
            return R::widest();
        };
        match *node {
            Computation::DataCase {
                scrutinee,
                motive,
                ref branches,
            } => branches.iter().fold(
                self.cached_value(scrutinee)
                    .join(self.cached_comp_type(motive).under_binder()),
                |depth, id| depth.join(self.cached_comp(*id)),
            ),
            Computation::SigmaSplit {
                scrutinee,
                motive,
                body,
            } => self
                .cached_value(scrutinee)
                .join(self.cached_comp_type(motive).under_binder())
                .join(self.cached_comp(body).under_binder().under_binder()),
            Computation::RecordProjection(record, _) | Computation::TupleProjection(record, _) => {
                self.cached_value(record)
            },
            Computation::ListFold {
                element,
                result,
                list,
                on_nil,
                on_cons,
            } => self
                .cached_value_type(element)
                .join(self.cached_value_type(result))
                .join(self.cached_value(list))
                .join(self.cached_comp(on_nil))
                .join(self.cached_comp(on_cons).under_binder().under_binder()),
            Computation::Transport(path, value) => {
                self.cached_value(path).join(self.cached_value(value))
            },
            Computation::PathTransport {
                motive,
                path,
                value,
            }
            | Computation::Ride {
                motive,
                flow: path,
                value,
            } => self
                .cached_value_type(motive)
                .under_binder()
                .join(self.cached_value(path))
                .join(self.cached_value(value)),
            Computation::TelescopeRide {
                motive,
                flow: path,
                start,
                over,
                value,
            }
            | Computation::TelescopeTransport {
                motive,
                path,
                start,
                over,
                value,
            } => self
                .cached_comp_type(motive)
                .join(self.cached_value(path))
                .join(self.cached_value(start))
                .join(self.cached_value(over))
                .join(self.cached_value(value)),
            Computation::RelatedApplication {
                path,
                left,
                right,
                evidence,
                body,
            } => self
                .cached_value(path)
                .join(self.cached_value(left))
                .join(self.cached_value(right))
                .join(self.cached_value(evidence))
                .join(
                    self.cached_comp(body)
                        .under_binder()
                        .under_binder()
                        .under_binder(),
                ),
            Computation::Lambda(body) | Computation::Fixpoint { body, .. } => {
                self.cached_comp(body).under_binder()
            },
            Computation::Application(head, argument) => {
                self.cached_comp(head).join(self.cached_value(argument))
            },
            Computation::Return(value) | Computation::Force(value) => self.cached_value(value),
            Computation::Project(_, pair) => self.cached_comp(pair),
            Computation::Bind(bound, body) => self
                .cached_comp(bound)
                .join(self.cached_comp(body).under_binder()),
            Computation::With(left, right) => self.cached_comp(left).join(self.cached_comp(right)),
            Computation::Case {
                scrutinee,
                ref branches,
            } => branches
                .iter()
                .fold(self.cached_value(scrutinee), |depth, id| {
                    depth.join(self.cached_comp(*id).under_binder())
                }),
        }
    }
}

#[cfg(test)]
mod tests
{
    use gandr_kernel_check_memo::ContentAgreement;
    use gandr_kernel_check_memo::MemoKey as _;
    use gandr_kernel_strata::Level;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::GroundSort;
    use gandr_kernel_term::TermArena;
    use quenchant_shape::shape::Maybe;

    use super::LooseDepth;
    use super::LooseDepths;
    use super::NodeSupport;
    use super::Reach as _;
    use super::Reaches;
    use super::Reads;
    use super::SupportContext;
    use super::SupportPlane;
    use super::read_telescope;
    use crate::encoding::SupportGoal;

    #[test]
    fn reads_are_exactly_the_free_indices()
    {
        let mut arena = TermArena::new();
        let at =
            |arena: &mut TermArena, index: u32| arena.value_variable(DeBruijnIndex::from(index));
        let listed = |reads: &Reads| match reads.indices() {
            Maybe::Present(read) => Maybe::Present(read.collect::<alloc::vec::Vec<_>>()),
            Maybe::Absent(absent) => Maybe::Absent(absent),
        };
        let set = |indices: &[u32]| {
            Maybe::Present(indices.iter().copied().map(DeBruijnIndex::from).collect())
        };
        let leaves = [0_u32, 3, 63, 64, 70].map(|index| at(&mut arena, index));
        let tuple = arena.value_tuple(&leaves);
        let body = arena.computation_return(tuple);
        let lambda = arena.computation_lambda(body);
        let far = at(&mut arena, 64);
        let returned = arena.computation_return(far);
        let stepped = arena.computation_lambda(returned);
        let mut reads: Reaches<Reads> = Reaches::default();
        let mut depths = LooseDepths::new();
        assert_eq!(
            set(&[0, 3, 63, 64, 70]),
            listed(&reads.value_reach(&arena, tuple)),
            "a former reads every index its children read, on both sides of the word"
        );
        assert_eq!(
            set(&[2, 62, 63, 69]),
            listed(&reads.comp_reach(&arena, lambda)),
            "a binder drops index zero and lowers the rest"
        );
        assert_eq!(
            Reads::variable(DeBruijnIndex::from(63_u32)),
            reads.comp_reach(&arena, stepped),
            "a spilled set stepped back inside the word takes the word's form"
        );
        assert_eq!(
            set(&[1, 63, 64]),
            listed(
                &Reads::variable(DeBruijnIndex::from(64_u32))
                    .join(Reads::variable(DeBruijnIndex::from(1_u32)))
                    .join(Reads::variable(DeBruijnIndex::from(63_u32)))
            ),
            "a union of a word and a spilled set is ascending and repeats nothing"
        );
        assert_eq!(
            depths.value_reach(&arena, tuple),
            reads.value_reach(&arena, tuple).depth(),
            "the depth is one more than the largest index read"
        );
        for node in [lambda, stepped] {
            assert_eq!(
                depths.comp_reach(&arena, node),
                reads.comp_reach(&arena, node).depth()
            );
        }
        let floor = arena.watermark();
        let gone = arena.value_unit();
        arena.truncate_to(floor);
        let unread = reads.value_reach(&arena, gone);
        assert_eq!(
            Maybe::Absent(super::read_indices::Absent::Widest),
            listed(&unread),
            "an unreadable node reads every binder"
        );
        assert_eq!(LooseDepth::WIDEST, unread.depth());
        assert_eq!(
            unread,
            Reads::variable(DeBruijnIndex::from(0_u32)).join(Reads::widest()),
            "and absorbs a join"
        );
        assert_eq!(
            unread,
            Reads::widest().under_binder(),
            "and survives a binder"
        );
    }

    #[test]
    fn saturated_reach_remains_conservative_beneath_a_binder()
    {
        let mut arena = TermArena::new();
        let variable = arena.value_variable(DeBruijnIndex::from(u32::MAX));
        let body = arena.computation_return(variable);
        let lambda = arena.computation_lambda(body);
        let mut reaches = LooseDepths::new();
        assert_eq!(reaches.comp_reach(&arena, lambda), LooseDepth::WIDEST);
    }

    #[test]
    fn a_closed_value_reaches_no_binder()
    {
        let mut arena = TermArena::new();
        let unit = arena.value_unit();
        let pair = arena.value_tuple(&[unit, unit]);
        let mut reaches = LooseDepths::new();
        assert_eq!(
            LooseDepth::from(0_u32),
            reaches.value_reach(&arena, pair),
            "a closed composite reaches no binder"
        );
    }

    #[test]
    fn a_variable_reaches_one_more_than_its_index()
    {
        let mut arena = TermArena::new();
        let zero = arena.value_variable(DeBruijnIndex::from(0_u32));
        let three = arena.value_variable(DeBruijnIndex::from(3_u32));
        let pair = arena.value_tuple(&[zero, three]);
        let mut reaches = LooseDepths::new();
        assert_eq!(
            LooseDepth::from(1_u32),
            reaches.value_reach(&arena, zero),
            "index zero names the innermost slot"
        );
        assert_eq!(
            LooseDepth::from(4_u32),
            reaches.value_reach(&arena, pair),
            "a join takes the wider of the two"
        );
    }

    #[test]
    fn a_binder_closes_its_body()
    {
        let mut arena = TermArena::new();
        let zero = arena.value_variable(DeBruijnIndex::from(0_u32));
        let body = arena.computation_return(zero);
        let lambda = arena.computation_lambda(body);
        let mut reaches = LooseDepths::new();
        assert_eq!(
            LooseDepth::from(1_u32),
            reaches.comp_reach(&arena, body),
            "the body reads its own binder"
        );
        assert_eq!(
            LooseDepth::from(0_u32),
            reaches.comp_reach(&arena, lambda),
            "and from outside the lambda that binder is gone"
        );
    }

    #[test]
    fn a_bind_closes_only_its_body()
    {
        let mut arena = TermArena::new();
        let zero = arena.value_variable(DeBruijnIndex::from(0_u32));
        let bound = arena.computation_return(zero);
        let body = arena.computation_return(zero);
        let sequence = arena.computation_bind(bound, body);
        let mut reaches = LooseDepths::new();
        assert_eq!(
            LooseDepth::from(1_u32),
            reaches.comp_reach(&arena, sequence),
            "the bound computation keeps its reach while the body loses one, so the join is one"
        );
    }

    #[test]
    fn an_unreadable_node_reaches_widest()
    {
        let mut arena = TermArena::new();
        let floor = arena.watermark();
        let unit = arena.value_unit();
        let computation = arena.computation_return(unit);
        let value_type = arena.value_type_unit();
        let comp_type = arena.comp_type_returner(value_type);
        arena.truncate_to(floor);
        let mut reaches = LooseDepths::new();
        assert_eq!(reaches.cached_value(unit), LooseDepth::WIDEST);
        assert_eq!(reaches.cached_comp(computation), LooseDepth::WIDEST);
        assert_eq!(reaches.cached_value_type(value_type), LooseDepth::WIDEST);
        assert_eq!(reaches.cached_comp_type(comp_type), LooseDepth::WIDEST);
        assert_eq!(reaches.comp_reach(&arena, computation), LooseDepth::WIDEST);
        assert_eq!(
            reaches.value_type_reach(&arena, value_type),
            LooseDepth::WIDEST
        );
        assert_eq!(
            reaches.comp_type_reach(&arena, comp_type),
            LooseDepth::WIDEST
        );
        assert_eq!(
            LooseDepth::from(u32::MAX),
            reaches.value_reach(&arena, unit),
            "an unreadable node widens the reach to the whole context rather than narrowing it"
        );
    }

    #[test]
    fn a_closed_node_takes_no_telescope()
    {
        let mut arena = TermArena::new();
        let unit = arena.value_unit();
        let unit_type = arena.value_type_unit();
        let base = arena.value_type_base(BaseType::Integer);
        let mut session = SupportContext::new();
        let bare = NodeSupport::build(&arena, &mut session, SupportGoal::SynthValue(unit), &[]);
        let under = NodeSupport::build(&arena, &mut session, SupportGoal::SynthValue(unit), &[
            unit_type, base,
        ]);
        assert_eq!(
            ContentAgreement::Agree,
            bare.agreement(&under),
            "a closed node means the same thing under every context"
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
        let under_unit =
            NodeSupport::build(&arena, &mut session, SupportGoal::SynthValue(variable), &[
                unit_type,
            ]);
        let under_base =
            NodeSupport::build(&arena, &mut session, SupportGoal::SynthValue(variable), &[
                base,
            ]);
        assert_eq!(
            ContentAgreement::Differ,
            under_unit.agreement(&under_base),
            "the same node under binders of different types is two questions"
        );
        assert_ne!(
            gandr_kernel_check_memo::MemoKey::digest(&under_unit),
            gandr_kernel_check_memo::MemoKey::digest(&under_base),
            "and the memo files the two under different buckets"
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
        let shallow =
            NodeSupport::build(&arena, &mut session, SupportGoal::SynthValue(variable), &[
                unit_type,
            ]);
        let deep = NodeSupport::build(&arena, &mut session, SupportGoal::SynthValue(variable), &[
            base, unit_type,
        ]);
        assert_eq!(
            ContentAgreement::Agree,
            shallow.agreement(&deep),
            "only the binders read are in the key, so contexts agreeing where the node looks are \
             one question"
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
            NodeSupport::build(
                &arena,
                &mut session,
                SupportGoal::SynthValue(variable),
                context,
            )
        };
        let over_unit = under(&[integer, unit_type]);
        let over_text = under(&[integer, text]);
        let elsewhere = under(&[text, unit_type]);
        assert_eq!(
            ContentAgreement::Agree,
            over_unit.agreement(&over_text),
            "a node reading index one and not zero is one question under contexts differing only \
             at zero"
        );
        assert_eq!(
            ContentAgreement::Differ,
            over_unit.agreement(&elsewhere),
            "and two where they differ at the index it reads"
        );
    }

    /// A type reaches binders exactly through the codes it carries, and the
    /// dependent arrow's codomain steps out by one like every other binder.
    #[test]
    fn a_type_reaches_through_its_codes()
    {
        let mut arena = TermArena::new();
        let zero = Level::zero();
        let closed = arena.value_type_unit();
        let code = arena.value_variable(DeBruijnIndex::from(2_u32));
        let element = arena.value_type_element(code, zero.clone());
        let returner = arena.comp_type_returner(element);
        let universe = arena.value_type_universe(GroundSort::Value, zero);
        let dependent = arena.comp_type_pi(universe, returner);
        let mut reaches = LooseDepths::new();
        assert_eq!(
            LooseDepth::from(0_u32),
            reaches.value_type_reach(&arena, closed),
            "a type carrying no code reaches no binder"
        );
        assert_eq!(
            LooseDepth::from(3_u32),
            reaches.value_type_reach(&arena, element),
            "a type read off a variable code reaches one more than its index"
        );
        assert_eq!(
            LooseDepth::from(2_u32),
            reaches.comp_type_reach(&arena, dependent),
            "and from outside the dependent arrow that binder is gone"
        );
    }

    /// A type-formation goal splits on the binders its codes read, the
    /// same way a term goal does — so one type formed under two different
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
        let under_unit = NodeSupport::build(
            &arena,
            &mut session,
            SupportGoal::ValueTypeLevel(element),
            &[unit_type],
        );
        let under_base = NodeSupport::build(
            &arena,
            &mut session,
            SupportGoal::ValueTypeLevel(element),
            &[base],
        );
        assert_eq!(
            ContentAgreement::Differ,
            under_unit.agreement(&under_base),
            "the same code-carrying type under binders of different types is two questions"
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
        let bare = NodeSupport::build(
            &arena,
            &mut session,
            SupportGoal::ValueTypeLevel(unit_type),
            &[],
        );
        let under = NodeSupport::build(
            &arena,
            &mut session,
            SupportGoal::ValueTypeLevel(unit_type),
            &[base, unit_type],
        );
        assert_eq!(
            ContentAgreement::Agree,
            bare.agreement(&under),
            "a type carrying no code means the same thing under every context"
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
        // The buffer holds an earlier goal's read, which gathering discards.
        let mut buffer = alloc::vec![(at(5), unit)];
        let mut read =
            |reads: Reads| super::read_binders(&context, &reads, &mut buffer).map(<[_]>::to_vec);
        assert_eq!(Maybe::Present(alloc::vec![]), read(Reads::closed()));
        assert_eq!(
            Maybe::Present(alloc::vec![(at(0), base)]),
            read(Reads::variable(at(0))),
            "index zero names the innermost binder"
        );
        assert_eq!(
            Maybe::Present(alloc::vec![(at(1), unit)]),
            read(Reads::variable(at(1))),
            "and the last index the outermost"
        );
        assert_eq!(
            Maybe::Present(alloc::vec![(at(0), base), (at(1), unit)]),
            read(Reads::variable(at(1)).join(Reads::variable(at(0)))),
            "ascending by index"
        );
        assert_eq!(
            Maybe::Absent(read_telescope::Absent::PastTheContext),
            read(Reads::variable(at(2))),
            "an index past the context takes the whole context"
        );
        assert_eq!(
            Maybe::Absent(read_telescope::Absent::Unread),
            read(Reads::widest()),
            "and so does a node the walk could not read"
        );
    }

    #[test]
    fn a_term_support_never_agrees_with_a_type_support()
    {
        let mut arena = TermArena::new();
        let unit = arena.value_unit();
        let unit_type = arena.value_type_unit();
        let mut session = SupportContext::new();
        let term = NodeSupport::build(&arena, &mut session, SupportGoal::SynthValue(unit), &[]);
        let formation = NodeSupport::build(
            &arena,
            &mut session,
            SupportGoal::ValueTypeLevel(unit_type),
            &[],
        );
        assert_eq!(
            ContentAgreement::Differ,
            term.agreement(&formation),
            "the two machines never answer for one another"
        );
    }
}
