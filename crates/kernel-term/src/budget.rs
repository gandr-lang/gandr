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

use anodized::spec;

/// The global index of one entry in the artifact's subterm table.
///
/// It is not an arena id and not an admission position. The table's index space
/// runs across declaration segments, which is where cross-declaration sharing
/// lives, and an entry's children are always strictly earlier in it.
///
/// # Specification
/// - requires: the quantity is interpreted in its named coordinate or work
///   domain.
/// - ensures: carries that quantity without proving that an index exists or a
///   budget is admitted; the decoder performs those checks.
/// - panics: none.
/// - executable: none — this quantity or report is a data declaration;
///   arithmetic and decoder admission are its executable boundaries.
///
/// # Adequacy
/// - hypothesis: L3 observes index and sum ceilings; L2 compares decoded table
///   counts and expanded work with independent graph expectations. Named
///   cap-adjacent artifacts distinguish field confusion and inclusive/exclusive
///   boundary changes. Nominal type separation is L0, not a runtime kill claim.
/// - witness: `budget::tests::index_and_work_boundaries_match_widened_arithmetic`
/// - witness: `sharing_format::sharing_format::sharing_round_trips_with_sharing_at_the_shared_nodes`
/// - witness: `sharing_format::sharing_format::the_declaration_work_boundary_accepts_under_and_refuses_over`
/// - witness: `sharing_format::sharing_format::many_cheap_segments_sharing_one_root_are_refused`
/// - witness: `sharing_format::sharing_format::the_level_offset_boundary_accepts_under_and_refuses_over`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct GlobalIndex(pub u32);

impl From<u32> for GlobalIndex
{
    /// The global index for a table position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: u32) -> Self
    {
        Self(index)
    }
}

impl From<GlobalIndex> for u32
{
    /// The table position the index carries.
    ///
    /// # Specification
    /// trivial.
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
///
/// # Specification
/// - requires: the quantity is interpreted in its named coordinate or work
///   domain.
/// - ensures: carries that quantity without proving that an index exists or a
///   budget is admitted; the decoder performs those checks.
/// - panics: none.
/// - executable: none — this quantity or report is a data declaration;
///   arithmetic and decoder admission are its executable boundaries.
///
/// # Adequacy
/// - hypothesis: L3 observes index and sum ceilings; L2 compares decoded table
///   counts and expanded work with independent graph expectations. Named
///   cap-adjacent artifacts distinguish field confusion and inclusive/exclusive
///   boundary changes. Nominal type separation is L0, not a runtime kill claim.
/// - witness: `budget::tests::index_and_work_boundaries_match_widened_arithmetic`
/// - witness: `sharing_format::sharing_format::sharing_round_trips_with_sharing_at_the_shared_nodes`
/// - witness: `sharing_format::sharing_format::the_declaration_work_boundary_accepts_under_and_refuses_over`
/// - witness: `sharing_format::sharing_format::many_cheap_segments_sharing_one_root_are_refused`
/// - witness: `sharing_format::sharing_format::the_level_offset_boundary_accepts_under_and_refuses_over`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct EntryOffset(pub usize);

impl GlobalIndex
{
    /// The offset this index reads at, saturating at the offset ceiling so a
    /// checked read rejects it rather than wrapping into a live entry.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the equal offset, or the offset ceiling on a target
    ///   whose pointer width cannot hold this index.
    /// - provides: the total, panic-free index-to-offset widening; the
    ///   saturated offset lies past every vector the decoder builds, so a
    ///   checked read rejects it rather than wrapping into a live entry.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 observes exact widening, the successor at zero and both
    ///   sides of the u32 ceiling, and sums around the u64 ceiling against a
    ///   widened reference. The cases separate wraparound, premature saturation
    ///   and shifted indices; target-width refusal is conditional on the
    ///   executing platform.
    /// - witness: `budget::tests::index_and_work_boundaries_match_widened_arithmetic`
    #[spec(
        ensures: |ret| ret.0 == usize::try_from(self.0).unwrap_or(usize::MAX),
    )]
    #[inline]
    pub(crate) fn offset(self) -> EntryOffset
    {
        EntryOffset(usize::try_from(self.0).unwrap_or(usize::MAX))
    }

    /// The next free index after this one, saturating at the ceiling.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the index one above this one, or the `u32` ceiling
    ///   when this index is already there.
    /// - provides: the total successor the table walk takes; the saturated
    ///   index repeats rather than wrapping to zero, so an exhausted table
    ///   cannot alias entry zero.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 observes exact widening, the successor at zero and both
    ///   sides of the u32 ceiling, and sums around the u64 ceiling against a
    ///   widened reference. The cases separate wraparound, premature saturation
    ///   and shifted indices; target-width refusal is conditional on the
    ///   executing platform.
    /// - witness: `budget::tests::index_and_work_boundaries_match_widened_arithmetic`
    #[spec(
        ensures: |ret| ret.0 >= self.0
                && if self.0 == u32::MAX { ret.0 == u32::MAX }
            else { ret.0.saturating_sub(self.0) == 1 },
    )]
    #[inline]
    pub(crate) const fn next(self) -> Self
    {
        Self(self.0.saturating_add(1))
    }
}

/// The number of entries in a decoded subterm table.
///
/// # Specification
/// - requires: the quantity is interpreted in its named coordinate or work
///   domain.
/// - ensures: carries that quantity without proving that an index exists or a
///   budget is admitted; the decoder performs those checks.
/// - panics: none.
/// - executable: none — this quantity or report is a data declaration;
///   arithmetic and decoder admission are its executable boundaries.
///
/// # Adequacy
/// - hypothesis: L3 observes index and sum ceilings; L2 compares decoded table
///   counts and expanded work with independent graph expectations. Named
///   cap-adjacent artifacts distinguish field confusion and inclusive/exclusive
///   boundary changes. Nominal type separation is L0, not a runtime kill claim.
/// - witness: `budget::tests::index_and_work_boundaries_match_widened_arithmetic`
/// - witness: `sharing_format::sharing_format::sharing_round_trips_with_sharing_at_the_shared_nodes`
/// - witness: `sharing_format::sharing_format::the_declaration_work_boundary_accepts_under_and_refuses_over`
/// - witness: `sharing_format::sharing_format::many_cheap_segments_sharing_one_root_are_refused`
/// - witness: `sharing_format::sharing_format::the_level_offset_boundary_accepts_under_and_refuses_over`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TableEntryCount(pub usize);

impl From<usize> for TableEntryCount
{
    /// The count for a number of table entries.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: usize) -> Self
    {
        Self(count)
    }
}

impl From<TableEntryCount> for usize
{
    /// The number of entries the count carries.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: TableEntryCount) -> Self
    {
        count.0
    }
}

impl core::fmt::Display for TableEntryCount
{
    /// Writes the count as a decimal number.
    ///
    /// # Specification
    /// - requires: a formatter accepting or refusing writes.
    /// - ensures: writes the carried quantity in decimal form.
    /// - provides: a numeric observation without changing the quantity.
    /// - fails: propagates refusal by the destination formatter.
    /// - panics: none.
    /// - executable: none — Formatter exposes no readable output or
    ///   sink-refusal state; checking either here would require wrapping or
    ///   replaying the write.
    ///
    /// # Adequacy
    /// - hypothesis: L3 observes decimal representations at zero, ordinary
    ///   values and numeric ceilings, plus refusal by a real exhausted byte
    ///   sink. It separates truncation, alternate-radix formatting and
    ///   swallowed sink errors without pinning incidental diagnostic wording.
    /// - witness: `budget::tests::the_metric_wrappers_render_their_quantities`
    /// - witness: `error::tests::diagnostics_preserve_semantic_distinctions_and_sink_refusal`
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
///
/// # Specification
/// - requires: the quantity is interpreted in its named coordinate or work
///   domain.
/// - ensures: carries that quantity without proving that an index exists or a
///   budget is admitted; the decoder performs those checks.
/// - panics: none.
/// - executable: none — this quantity or report is a data declaration;
///   arithmetic and decoder admission are its executable boundaries.
///
/// # Adequacy
/// - hypothesis: L3 observes index and sum ceilings; L2 compares decoded table
///   counts and expanded work with independent graph expectations. Named
///   cap-adjacent artifacts distinguish field confusion and inclusive/exclusive
///   boundary changes. Nominal type separation is L0, not a runtime kill claim.
/// - witness: `budget::tests::index_and_work_boundaries_match_widened_arithmetic`
/// - witness: `sharing_format::sharing_format::sharing_round_trips_with_sharing_at_the_shared_nodes`
/// - witness: `sharing_format::sharing_format::the_declaration_work_boundary_accepts_under_and_refuses_over`
/// - witness: `sharing_format::sharing_format::many_cheap_segments_sharing_one_root_are_refused`
/// - witness: `sharing_format::sharing_format::the_level_offset_boundary_accepts_under_and_refuses_over`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ExpandedWork(pub u64);

impl From<u64> for ExpandedWork
{
    /// The quantity for a measured amount of expanded work.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(work: u64) -> Self
    {
        Self(work)
    }
}

impl From<ExpandedWork> for u64
{
    /// The amount the quantity carries.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(work: ExpandedWork) -> Self
    {
        work.0
    }
}

impl core::fmt::Display for ExpandedWork
{
    /// Writes the quantity as a decimal number.
    ///
    /// # Specification
    /// - requires: a formatter accepting or refusing writes.
    /// - ensures: writes the carried quantity in decimal form.
    /// - provides: a numeric observation without changing the quantity.
    /// - fails: propagates refusal by the destination formatter.
    /// - panics: none.
    /// - executable: none — Formatter exposes no readable output or
    ///   sink-refusal state; checking either here would require wrapping or
    ///   replaying the write.
    ///
    /// # Adequacy
    /// - hypothesis: L3 observes decimal representations at zero, ordinary
    ///   values and numeric ceilings, plus refusal by a real exhausted byte
    ///   sink. It separates truncation, alternate-radix formatting and
    ///   swallowed sink errors without pinning incidental diagnostic wording.
    /// - witness: `budget::tests::the_metric_wrappers_render_their_quantities`
    /// - witness: `error::tests::diagnostics_preserve_semantic_distinctions_and_sink_refusal`
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
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the sum of the two quantities, or the `u64` ceiling
    ///   when the sum is not representable.
    /// - provides: the accumulation the forward scan performs. Saturation is
    ///   the specification rather than a fallback: the quantity is exactly the
    ///   one an attacker wants to make astronomical, and a wrapping sum would
    ///   report a small number for the largest input.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 observes exact widening, the successor at zero and both
    ///   sides of the u32 ceiling, and sums around the u64 ceiling against a
    ///   widened reference. The cases separate wraparound, premature saturation
    ///   and shifted indices; target-width refusal is conditional on the
    ///   executing platform.
    /// - witness: `budget::tests::index_and_work_boundaries_match_widened_arithmetic`
    #[spec(
        ensures: |ret| match self.0.checked_add(other.0) { Some(sum) => ret.0 == sum, None => ret.0 == u64::MAX },
    )]
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
///
/// # Specification
/// - requires: the quantity is interpreted in its named coordinate or work
///   domain.
/// - ensures: carries that quantity without proving that an index exists or a
///   budget is admitted; the decoder performs those checks.
/// - panics: none.
/// - executable: none — this quantity or report is a data declaration;
///   arithmetic and decoder admission are its executable boundaries.
///
/// # Adequacy
/// - hypothesis: L3 observes index and sum ceilings; L2 compares decoded table
///   counts and expanded work with independent graph expectations. Named
///   cap-adjacent artifacts distinguish field confusion and inclusive/exclusive
///   boundary changes. Nominal type separation is L0, not a runtime kill claim.
/// - witness: `budget::tests::index_and_work_boundaries_match_widened_arithmetic`
/// - witness: `sharing_format::sharing_format::sharing_round_trips_with_sharing_at_the_shared_nodes`
/// - witness: `sharing_format::sharing_format::the_declaration_work_boundary_accepts_under_and_refuses_over`
/// - witness: `sharing_format::sharing_format::many_cheap_segments_sharing_one_root_are_refused`
/// - witness: `sharing_format::sharing_format::the_level_offset_boundary_accepts_under_and_refuses_over`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct LevelAtomOffset(pub u64);

impl From<u64> for LevelAtomOffset
{
    /// The offset for a successor distance read off the wire.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(offset: u64) -> Self
    {
        Self(offset)
    }
}

impl From<LevelAtomOffset> for u64
{
    /// The successor distance the offset carries.
    ///
    /// # Specification
    /// trivial.
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
///
/// # Specification
/// - requires: the decoder uses the matching resource axis.
/// - ensures: bounds expanded work per declaration root and exceeds twice the
///   distinct-entry cap.
/// - panics: none.
/// - executable: none — this policy constant is not callable; the decoder
///   compares the observed quantity against it.
///
/// # Adequacy
/// - hypothesis: L3 derives accepted and refused artifacts from the policy
///   bound and observes exact admission or the named resource refusal. Changing
///   the bound is permitted; reversing the comparison, changing strictness or
///   using the wrong axis is distinguished. The deepest small-stack round trip
///   witnesses retained headroom.
/// - witness: `sharing_format::sharing_format::the_declaration_work_boundary_accepts_under_and_refuses_over`
/// - witness: `adversarial_depth::adversarial_depth::a_deep_artifact_round_trips_byte_identically`
pub const MAX_EXPANDED_TERM_WORK: ExpandedWork = ExpandedWork(1 << 20);

/// The cap on the number of subterm-table entries in an artifact, enforced as
/// entries accrue so that a rejection truncates early.
///
/// This is the distinct-node axis, naturally below [`MAX_EXPANDED_TERM_WORK`]
/// since sharing makes expanded work exceed the distinct-entry count, and it is
/// input-linear — each entry costs at least one wire byte — so it carries no
/// amplification of its own.
///
/// # Specification
/// - requires: the decoder uses the matching resource axis.
/// - ensures: bounds the number of distinct table entries as the table grows.
/// - panics: none.
/// - executable: none — this policy constant is not callable; the decoder
///   compares the observed quantity against it.
///
/// # Adequacy
/// - hypothesis: L3 derives accepted and refused artifacts from the policy
///   bound and observes exact admission or the named resource refusal. Changing
///   the bound is permitted; reversing the comparison, changing strictness or
///   using the wrong axis is distinguished. The deepest small-stack round trip
///   witnesses retained headroom.
/// - witness: `sharing_format::sharing_format::the_table_entry_boundary_accepts_under_and_refuses_over`
/// - witness: `adversarial_depth::adversarial_depth::a_deep_artifact_round_trips_byte_identically`
pub const MAX_TABLE_ENTRIES: TableEntryCount = TableEntryCount(1 << 18);

/// The cap on the artifact-total expanded tree work: the saturating sum over
/// every declaration root.
///
/// It closes the residual no per-declaration bound can see — many cheap
/// segments all referencing one near-cap root — and is reader acceptance policy
/// only, with no wire-format or canonicality consequence.
///
/// # Specification
/// - requires: the decoder uses the matching resource axis.
/// - ensures: bounds total declaration work, including repeated references to a
///   shared root.
/// - panics: none.
/// - executable: none — this policy constant is not callable; the decoder
///   compares the observed quantity against it.
///
/// # Adequacy
/// - hypothesis: L3 derives accepted and refused artifacts from the policy
///   bound and observes exact admission or the named resource refusal. Changing
///   the bound is permitted; reversing the comparison, changing strictness or
///   using the wrong axis is distinguished. The deepest small-stack round trip
///   witnesses retained headroom.
/// - witness: `sharing_format::sharing_format::many_cheap_segments_sharing_one_root_are_refused`
/// - witness: `adversarial_depth::adversarial_depth::a_deep_artifact_round_trips_byte_identically`
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
///
/// # Specification
/// - requires: the decoder uses the matching resource axis.
/// - ensures: excludes variable-atom successor offsets at or above this
///   ceiling.
/// - panics: none.
/// - executable: none — this policy constant is not callable; the decoder
///   compares the observed quantity against it.
///
/// # Adequacy
/// - hypothesis: L3 derives accepted and refused artifacts from the policy
///   bound and observes exact admission or the named resource refusal. Changing
///   the bound is permitted; reversing the comparison, changing strictness or
///   using the wrong axis is distinguished. The deepest small-stack round trip
///   witnesses retained headroom.
/// - witness: `sharing_format::sharing_format::the_level_offset_boundary_accepts_under_and_refuses_over`
/// - witness: `adversarial_depth::adversarial_depth::a_deep_artifact_round_trips_byte_identically`
pub const MAX_DECODED_LEVEL_OFFSET: LevelAtomOffset = LevelAtomOffset(4096);

/// The deterministic decode-budget metrics of an artifact.
///
/// Every field is a function of the canonical bytes alone, so recording one per
/// corpus item pins the size and work profile the day it moves. They come off
/// the same memoized forward scan the budget check rides — a read from an
/// already-computed vector, never a second descent — so exposing them costs
/// nothing beyond the check already paid.
///
/// # Specification
/// - requires: the quantity is interpreted in its named coordinate or work
///   domain.
/// - ensures: carries that quantity without proving that an index exists or a
///   budget is admitted; the decoder performs those checks.
/// - panics: none.
/// - executable: none — this quantity or report is a data declaration;
///   arithmetic and decoder admission are its executable boundaries.
///
/// # Adequacy
/// - hypothesis: L3 observes index and sum ceilings; L2 compares decoded table
///   counts and expanded work with independent graph expectations. Named
///   cap-adjacent artifacts distinguish field confusion and inclusive/exclusive
///   boundary changes. Nominal type separation is L0, not a runtime kill claim.
/// - witness: `budget::tests::index_and_work_boundaries_match_widened_arithmetic`
/// - witness: `sharing_format::sharing_format::sharing_round_trips_with_sharing_at_the_shared_nodes`
/// - witness: `sharing_format::sharing_format::the_declaration_work_boundary_accepts_under_and_refuses_over`
/// - witness: `sharing_format::sharing_format::many_cheap_segments_sharing_one_root_are_refused`
/// - witness: `sharing_format::sharing_format::the_level_offset_boundary_accepts_under_and_refuses_over`
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
    ///
    /// # Specification
    /// - requires: the three quantities describe the same artifact.
    /// - ensures: returns the metrics carrying the three quantities unchanged.
    /// - provides: the deterministic budget report the subsequent admission
    ///   check and the telemetry a caller keeps both read.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 compares decoded shared-graph metrics with closed-form
    ///   expanded-work expectations, including repeated roots across
    ///   declaration segments. L3 cap-adjacent artifacts distinguish swapped
    ///   quantities and omitted declaration contributions; the tests do not
    ///   validate arbitrary graphs exhaustively.
    /// - witness: `sharing_format::sharing_format::sharing_round_trips_with_sharing_at_the_shared_nodes`
    /// - witness: `sharing_format::sharing_format::the_declaration_work_boundary_accepts_under_and_refuses_over`
    /// - witness: `sharing_format::sharing_format::many_cheap_segments_sharing_one_root_are_refused`
    #[spec(
        ensures: |ret| ret.table_entries.0 == table_entries.0
                && ret.max_declaration_expanded_work.0 == max_declaration_expanded_work.0
                && ret.artifact_expanded_work.0 == artifact_expanded_work.0,
    )]
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
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn table_entries(&self) -> TableEntryCount
    {
        self.table_entries
    }

    /// The maximum per-declaration-root expanded tree size.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn max_declaration_expanded_work(&self) -> ExpandedWork
    {
        self.max_declaration_expanded_work
    }

    /// The artifact-total expanded tree size: the saturating sum over every
    /// declaration root.
    ///
    /// # Specification
    /// trivial.
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

    #[test]
    fn index_and_work_boundaries_match_widened_arithmetic()
    {
        for (index, next) in [
            (0u32, 1u32),
            (1, 2),
            (u32::MAX.saturating_sub(1), u32::MAX),
            (u32::MAX, u32::MAX),
        ] {
            let global = super::GlobalIndex(index);
            assert_eq!(next, global.next().0);
            let expected =
                u128::from(index).min(u128::try_from(usize::MAX).expect("pointer width fits u128"));
            assert_eq!(
                expected,
                u128::try_from(global.offset().0).expect("pointer width fits u128")
            );
        }
        for left in [
            0u64,
            1,
            u64::MAX.div_euclid(2),
            u64::MAX.saturating_sub(1),
            u64::MAX,
        ] {
            for right in [
                0u64,
                1,
                u64::MAX.div_euclid(2),
                u64::MAX.saturating_sub(1),
                u64::MAX,
            ] {
                let expected = u128::from(left)
                    .saturating_add(u128::from(right))
                    .min(u128::from(u64::MAX));
                let actual = ExpandedWork(left).saturating_add(ExpandedWork(right));
                assert_eq!(expected, u128::from(actual.0));
            }
        }
    }
}
