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
//! telescope a term goal's does. Supports are therefore carried on all four
//! families rather than on the two term ones, which is what keeps a type
//! formed under two different binders from collapsing onto one entry.
//!
//! # The read binders are carried, not walked
//!
//! Every node of the arena carries its support from the moment it is minted
//! ([`TermArena::value_support`] and its three siblings): exactly the free
//! indices it mentions, gathered from its children's. The key reads that set
//! off the goal's node, so building a key walks nothing below it, and the
//! checks that ask only how far a node reaches read the set's depth. A node
//! whose child the arena cannot resolve reads every binder, which takes the
//! whole context into the key: **the failure direction is always more context
//! in the key, never less**, so a defect here costs collapse and cannot
//! manufacture a hit.
//!
//! # References
//!
//! - `vault:01a178aa-6917-7983-b5cd-86e2af86b3ec` — lineage: the key reads the
//!   binders a goal reads off the support its node carries, a support the
//!   kernel derives from its own nodes (§ kernel-reassessment-design items 1
//!   and 3).
//! - `vault:01a12317-453f-7980-9c86-68f75917f3a6` — lineage: what a node
//!   mentions is the syntactic layer of a goal's demanded context, carried on
//!   the node and read off it (§ codebruijn-carrier, § footprint-from-support).

use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_check_memo::CheckMemo as _;
use gandr_kernel_check_memo::ContentAgreement;
use gandr_kernel_check_memo::ContentDigest;
use gandr_kernel_check_memo::DigestWord;
use gandr_kernel_check_memo::MemoEntryCount;
use gandr_kernel_check_memo::MemoKey;
use gandr_kernel_strata::Level;
use gandr_kernel_term::CompTypeId;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::Reads;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::ValueTypeId;
use gandr_kernel_term::read_indices;
use quenchant_shape::shape::Maybe;

use crate::element_identity::BinderUse;
use crate::encoding::ContentId;
use crate::encoding::ContentTable;
use crate::encoding::SupportGoal;
use crate::encoding::Telescope;
use crate::encoding::support_key;
use crate::rewrite::RewriteMemo;
use crate::rewrite::RewritePlane;

/// The state one checking session derives its memo keys against: the canonical
/// content numbering, and the buffer one goal's read binders are gathered in.
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
    /// the goal's node reads, as the node's carried support names them.
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
    ///   position the node reads. A node whose support reads every binder, or
    ///   names a position past the context, takes the whole context, so an
    ///   over-estimate can only split a support and never merge two.
    /// - provides: the memo key, with the goal's plane checked by the
    ///   predicate. Provenance and agreement across independent goals need a
    ///   second goal and remain obligations of the paired witnesses below.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decision surfaces are the plane split, the
    ///   support read, and the positions read, separated by a closed node under
    ///   a non-empty context (empty telescope), a binder-reading node under two
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
            SupportGoal::ValueTypeLevel(id) => (SupportPlane::Type, arena.value_type_support(id)),
            SupportGoal::CompTypeLevel(id) => (SupportPlane::Type, arena.comp_type_support(id)),
            SupportGoal::SynthValue(id) | SupportGoal::CheckValue(id, _) => {
                (SupportPlane::Term, arena.value_support(id))
            },
            SupportGoal::SynthComp(id) | SupportGoal::CheckComp(id, _) => {
                (SupportPlane::Term, arena.computation_support(id))
            },
        };
        let telescope = match read_binders(context, reads, &mut session.read) {
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
    use gandr_kernel_term::TermArena;
    use quenchant_shape::shape::Maybe;

    use super::NodeSupport;
    use super::SupportContext;
    use super::SupportPlane;
    use super::innermost;
    use super::read_telescope;
    use crate::element_identity::BinderUse;
    use crate::encoding::SupportGoal;

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
