//! The amplification defence: the quantities a decode measures, the four
//! constants that bound them, and the metrics one forward scan yields.
//!
//! # Why a reader needs a budget at all
//!
//! Decode retains sharing, which is the whole point of the format — and it
//! moves the billion-laughs attack from memory to checker time. A shared graph
//! walked as a tree re-checks each shared subterm once per reference, so a
//! small artifact can name a DAG whose *expanded* size is astronomical. **A
//! depth bound does not bound width, and width is what sharing buys an
//! attacker.**
//!
//! The budgets below bound that work **without touching the checker**, which is
//! what keeps them outside the trusted base: an import boundary refuses an
//! artifact whose declared shape is absurd, whatever a checker could afford,
//! and the refusal stays cheap and independent of any checker's internals.
//!
//! # The four budgets, and where each is enforced
//!
//! | budget | axis | enforced |
//! | ------ | ---- | -------- |
//! | [`MAX_TABLE_ENTRIES`] | distinct graph nodes, input-linear | as entries accrue, so truncation is cheap |
//! | [`MAX_EXPANDED_TERM_WORK`] | per-declaration-root tree work | on the forward scan, before any consumer |
//! | [`MAX_ARTIFACT_EXPANDED_WORK`] | artifact-total tree work | on the same forward scan, one extra accumulator |
//! | [`MAX_DECODED_LEVEL_OFFSET`] | a level atom's successor offset | at the level decoder, per atom |
//!
//! The expanded size of an entry is one plus the saturating sum over its
//! children's expanded sizes. Because a child index is always strictly earlier
//! than its entry's own, **a single forward scan computes the whole vector in
//! linear time**, memoized per entry — there is no second descent, and the same
//! scan yields the deterministic metrics a caller can record as telemetry.
//!
//! # The artifact total closes a hole the per-declaration cap cannot see
//!
//! The shape is worth remembering: `N` declaration segments of about ten wire
//! bytes each, all referencing one near-cap root, force `N` times the
//! per-declaration budget in work while every individual declaration passes.
//! The artifact-total cap rides the same scan as one accumulator and one
//! compare. It is reader acceptance policy only, with no effect on the wire
//! format and none on canonicality.
//!
//! # What the constants are set against
//!
//! The binding floor is not a corpus of ordinary declarations, whose expanded
//! work is a handful of nodes. It is **the deepest artifact the kernel itself
//! round-trips**, because a reader must accept every artifact the kernel
//! legitimately admits: the adversarial-depth witness decodes a declaration of
//! roughly two hundred thousand entries and four hundred thousand expanded
//! work. Each constant clears that floor with headroom while rejecting an
//! obvious billion-laughs by orders of magnitude — and `MAX_TABLE_ENTRIES`
//! carries the thinnest headroom of the three, so it is the first to want
//! raising.

/// The global index of one entry in the artifact's subterm table.
///
/// It is not an arena id and not an admission position. The table's index space
/// runs across declaration segments, which is where cross-declaration sharing
/// lives, and an entry's children are always strictly earlier in it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct GlobalIndex(pub u32);

impl From<u32> for GlobalIndex
{
    #[inline]
    fn from(index: u32) -> Self
    {
        Self(index)
    }
}

impl From<GlobalIndex> for u32
{
    #[inline]
    fn from(index: GlobalIndex) -> Self
    {
        index.0
    }
}

/// The offset a global index reads at within one of the decoder's per-entry
/// vectors.
///
/// It is not a byte offset and not an arena id, and the wrapper is what keeps
/// the three from being interchangeable at a signature.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct EntryOffset(pub usize);

impl GlobalIndex
{
    /// The offset this index reads at, saturating at the offset ceiling so a
    /// checked read rejects it rather than wrapping into a live entry.
    #[inline]
    pub(crate) fn offset(self) -> EntryOffset
    {
        EntryOffset(usize::try_from(self.0).unwrap_or(usize::MAX))
    }

    /// The next free index after this one, saturating at the ceiling.
    #[inline]
    pub(crate) const fn next(self) -> Self
    {
        Self(self.0.saturating_add(1))
    }
}

/// The number of entries in a decoded subterm table.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TableEntryCount(pub usize);

impl From<usize> for TableEntryCount
{
    #[inline]
    fn from(count: usize) -> Self
    {
        Self(count)
    }
}

impl From<TableEntryCount> for usize
{
    #[inline]
    fn from(count: TableEntryCount) -> Self
    {
        count.0
    }
}

impl core::fmt::Display for TableEntryCount
{
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        self.0.fmt(f)
    }
}

/// Saturating expanded — that is, tree — work measured over a shared graph.
///
/// Saturation is the point rather than a convenience: the quantity being
/// measured is exactly the one an attacker wants to make astronomical, so a
/// wrapping sum would report a small number for the largest input.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ExpandedWork(pub u64);

impl From<u64> for ExpandedWork
{
    #[inline]
    fn from(work: u64) -> Self
    {
        Self(work)
    }
}

impl From<ExpandedWork> for u64
{
    #[inline]
    fn from(work: ExpandedWork) -> Self
    {
        work.0
    }
}

impl core::fmt::Display for ExpandedWork
{
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        self.0.fmt(f)
    }
}

impl ExpandedWork
{
    /// One node's own contribution to expanded work.
    pub(crate) const ONE: Self = Self(1);

    /// The saturating sum of two expanded-work quantities.
    #[inline]
    pub(crate) const fn saturating_add(
        self,
        other: Self,
    ) -> Self
    {
        Self(self.0.saturating_add(other.0))
    }
}

/// A level atom's successor offset, as it arrives on the wire.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct LevelAtomOffset(pub u64);

impl From<u64> for LevelAtomOffset
{
    #[inline]
    fn from(offset: u64) -> Self
    {
        Self(offset)
    }
}

impl From<LevelAtomOffset> for u64
{
    #[inline]
    fn from(offset: LevelAtomOffset) -> Self
    {
        offset.0
    }
}

/// The cap on the expanded tree size of one declaration root.
///
/// It rejects a repeated-diamond graph whose expanded size is astronomical
/// while its wire image is a few dozen bytes. It sits above the deepest
/// artifact the kernel round-trips with headroom, and above twice
/// [`MAX_TABLE_ENTRIES`], so a maximal flat table stays under it.
pub const MAX_EXPANDED_TERM_WORK: ExpandedWork = ExpandedWork(1 << 20);

/// The cap on the number of subterm-table entries in an artifact, enforced as
/// entries accrue so that a rejection truncates early.
///
/// This is the distinct-node axis, naturally below [`MAX_EXPANDED_TERM_WORK`]
/// since sharing makes expanded work exceed the distinct-entry count, and it is
/// input-linear — each entry costs at least one wire byte — so it carries no
/// amplification of its own.
pub const MAX_TABLE_ENTRIES: TableEntryCount = TableEntryCount(1 << 18);

/// The cap on the artifact-total expanded tree work: the saturating sum over
/// every declaration root.
///
/// It closes the residual no per-declaration bound can see — many cheap
/// segments all referencing one near-cap root — and is reader acceptance policy
/// only, with no wire-format or canonicality consequence.
pub const MAX_ARTIFACT_EXPANDED_WORK: ExpandedWork = ExpandedWork(1 << 24);

/// The cap on a level atom's successor offset.
///
/// A canonical level is rebuilt through the level oracle's smart constructors,
/// and the only way to raise a variable atom to a given offset is that many
/// applications of successor. A small adversarial varint could otherwise demand
/// unbounded reconstruction work, so an offset at or above this cap is rejected
/// at decode. Real universe levels carry variable offsets of zero or one; a
/// level beyond the cap is a documented non-round-tripping case, liftable when
/// the oracle exposes a constant-time offset constructor.
pub const MAX_DECODED_LEVEL_OFFSET: LevelAtomOffset = LevelAtomOffset(4096);

/// The deterministic decode-budget metrics of an artifact.
///
/// Every field is a function of the canonical bytes alone, so recording one per
/// corpus item pins the size and work profile the day it moves. They come off
/// the same memoized forward scan the budget check rides — a read from an
/// already-computed vector, never a second descent — so exposing them costs
/// nothing beyond the check already paid.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct DecodeMetrics
{
    /// The number of subterm-table entries.
    table_entries: TableEntryCount,
    /// The maximum expanded tree size over every declaration root.
    max_declaration_expanded_work: ExpandedWork,
    /// The saturating sum of expanded tree size over every declaration root.
    artifact_expanded_work: ExpandedWork,
}

impl DecodeMetrics
{
    /// Pair the three deterministic decode-budget quantities.
    #[inline]
    #[must_use]
    pub(crate) const fn new(
        table_entries: TableEntryCount,
        max_declaration_expanded_work: ExpandedWork,
        artifact_expanded_work: ExpandedWork,
    ) -> Self
    {
        Self {
            table_entries,
            max_declaration_expanded_work,
            artifact_expanded_work,
        }
    }

    /// The number of subterm-table entries.
    #[inline]
    #[must_use]
    pub const fn table_entries(&self) -> TableEntryCount
    {
        self.table_entries
    }

    /// The maximum per-declaration-root expanded tree size.
    #[inline]
    #[must_use]
    pub const fn max_declaration_expanded_work(&self) -> ExpandedWork
    {
        self.max_declaration_expanded_work
    }

    /// The artifact-total expanded tree size: the saturating sum over every
    /// declaration root.
    #[inline]
    #[must_use]
    pub const fn artifact_expanded_work(&self) -> ExpandedWork
    {
        self.artifact_expanded_work
    }
}

#[cfg(test)]
mod tests
{
    use alloc::format;
    use alloc::string::String;

    use super::ExpandedWork;
    use super::MAX_ARTIFACT_EXPANDED_WORK;
    use super::MAX_EXPANDED_TERM_WORK;
    use super::MAX_TABLE_ENTRIES;
    use super::TableEntryCount;

    #[test]
    fn expanded_work_saturates_rather_than_wrapping()
    {
        let ceiling = ExpandedWork::from(u64::MAX);
        assert_eq!(
            ceiling,
            ceiling.saturating_add(ExpandedWork::ONE),
            "the quantity an attacker inflates must not wrap to a small number"
        );
    }

    #[test]
    fn the_budget_constants_stand_in_their_recorded_order()
    {
        assert!(
            u64::from(MAX_EXPANDED_TERM_WORK)
                > 2_u64.saturating_mul(u64::try_from(usize::from(MAX_TABLE_ENTRIES)).unwrap_or(0)),
            "a maximal flat table stays under the per-declaration work cap"
        );
        assert!(
            u64::from(MAX_ARTIFACT_EXPANDED_WORK) > u64::from(MAX_EXPANDED_TERM_WORK),
            "the artifact total admits more than one near-cap declaration"
        );
    }

    #[test]
    fn the_metric_wrappers_render_their_quantities()
    {
        assert_eq!(String::from("17"), format!("{}", TableEntryCount::from(17)));
        assert_eq!(String::from("23"), format!("{}", ExpandedWork::from(23)));
    }
}
