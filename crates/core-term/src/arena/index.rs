//! The content index of one arena family: the position of each interned node,
//! filed by the hash of the node.
//!
//! A constructor mints an occurrence, which the index never files. An interned
//! mint, which a canonical import makes, probes the index first: it answers
//! the filed node of an equal record, or appends its node and files it. So
//! the index files one node for each content, its canonical node.
//!
//! [`Index::freeze`] moves the entries filed so far to a frozen segment that
//! every clone shares, as [`gandr_kernel_term::Family`] shares its frozen rows.
//! A clone then copies only the entries filed after the freeze. A probe reads
//! the entries filed after the last freeze first, then each frozen segment,
//! newest first.
//!
//! # References
//!
//! - `vault:01a178aa-6917-7983-b5cd-86e2af86b3ec` — anchor: identity never
//!   decides validity, and a node is named when it is minted (§
//!   kernel-reassessment-design item 10): the index files the canonical node of
//!   each content, and no verdict reads which node it is.

use alloc::sync::Arc;

use anodized::spec;
use gandr_kernel_check_memo::HashIndex;
use gandr_kernel_check_memo::Probe;
use gandr_kernel_check_memo::TableHash;
use gandr_kernel_check_memo::TablePosition;
use gandr_kernel_check_memo::TableSlot;

/// Where a probe of one family's index ends.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Interned
{
    /// An equal node stands at this position.
    Found(TablePosition),
    /// No equal node is filed. An insertion of the new node fills this slot of
    /// the entries filed after the last freeze.
    Vacant(TableSlot),
}

/// The positions of the interned nodes of one family, filed by the hash of
/// each node.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Default)]
pub(super) struct Index
{
    /// The segments frozen before [`Self::own`], oldest first. Each clone
    /// shares the list and each segment.
    frozen: Option<Arc<[Arc<HashIndex>]>>,
    /// The entries filed after the last freeze.
    own: HashIndex,
}

impl PartialEq for Index
{
    /// Always equal: the index names which rows are canonical, and two arenas
    /// compare by their rows alone.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn eq(
        &self,
        _other: &Self,
    ) -> bool
    {
        true
    }
}

impl Eq for Index
{
}

impl Index
{
    /// Probe for a node whose hash is `hash`, accepting a filed position that
    /// `accepts` answers for.
    ///
    /// # Specification
    /// - requires: every filed position was filed under the hash of its node,
    ///   and `accepts` answers for at most one filed position.
    /// - ensures: `Found(position)` names a filed position that `accepts`
    ///   answers for. Otherwise `Vacant(slot)` names the slot of the entries
    ///   filed after the last freeze that an insertion under `hash` fills.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an equal node minted before a freeze and one minted
    ///   after it, each probed from a clone, distinguish a probe that reads the
    ///   own entries alone and one that misses a frozen segment.
    /// - witness: `arena::tests::equal_content_mints_occurrences_of_one_canonical_node`
    /// - witness: `arena::tests::a_frozen_arena_answers_as_it_did_and_clones_its_own_rows_alone`
    #[spec(ensures: |ret| match ret {
        Interned::Found(position) => accepts(position),
        Interned::Vacant(_) => true,
    })]
    #[inline]
    pub(super) fn probe<Accepts>(
        &self,
        hash: TableHash,
        accepts: Accepts,
    ) -> Interned
    where
        Accepts: Fn(TablePosition) -> bool,
    {
        let slot = match self.own.probe(hash, &accepts) {
            Probe::Found(position) => return Interned::Found(position),
            Probe::Vacant(slot) => slot,
        };
        self.frozen
            .iter()
            .flat_map(|segments| segments.iter().rev())
            .find_map(|segment| match segment.probe(hash, &accepts) {
                Probe::Found(position) => Some(position),
                Probe::Vacant(_) => None,
            })
            .map_or(Interned::Vacant(slot), Interned::Found)
    }

    /// File `position` under `hash` at `slot`, which the last probe for `hash`
    /// answered.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(super) fn insert(
        &mut self,
        slot: TableSlot,
        hash: TableHash,
        position: TablePosition,
    )
    {
        self.own.insert(slot, hash, position);
    }

    /// Take `position` out of the index, where it is filed under `hash`. A
    /// position that the index does not file is left as it is.
    ///
    /// # Specification
    /// - requires: `hash` is the hash of the node at `position`.
    /// - ensures: no probe finds `position` after the call. Every other filed
    ///   position stays filed. A frozen segment that another clone shares is
    ///   copied before the removal, so that clone keeps its entries.
    /// - panics: none.
    /// - executable: none — the clause reads each frozen segment, and a
    ///   predicate over them walks state that the index accumulates.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a truncation into frozen nodes that a clone taken
    ///   before shares, then a canonical probe in that clone, distinguish a
    ///   removal that copies the shared segment from one that would unfile the
    ///   clone's nodes.
    /// - witness: `arena::tests::a_frozen_arena_answers_as_it_did_and_clones_its_own_rows_alone`
    #[inline]
    pub(super) fn remove(
        &mut self,
        hash: TableHash,
        position: TablePosition,
    )
    {
        if self.own.filed(hash).any(|filed| filed == position) {
            self.own.remove(hash, position);
            return;
        }
        let Some(segments) = self.frozen.as_mut()
        else {
            return;
        };
        let Some(at) = segments
            .iter()
            .position(|segment| segment.filed(hash).any(|filed| filed == position))
        else {
            return;
        };
        if let Some(segment) = Arc::make_mut(segments).get_mut(at) {
            Arc::make_mut(segment).remove(hash, position);
        }
    }

    /// Move the entries filed after the last freeze to a frozen segment, which
    /// every clone made after shares.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: every probe answers as it did before the call.
    /// - panics: none.
    /// - executable: none — the clause holds for every probe, and a predicate
    ///   that reads each filed entry walks state that the index accumulates.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::probe`].
    /// - witness: `arena::tests::a_frozen_arena_answers_as_it_did_and_clones_its_own_rows_alone`
    #[inline]
    pub(super) fn freeze(&mut self)
    {
        if self.own.entries().next().is_none() {
            return;
        }
        let own = Arc::new(core::mem::take(&mut self.own));
        self.frozen = Some(
            self.frozen
                .iter()
                .flat_map(|segments| segments.iter().cloned())
                .chain(core::iter::once(own))
                .collect(),
        );
    }
}
