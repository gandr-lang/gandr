//! The expected chunk-locality bound and edit measurements.
//!
//! # The locality bound
//!
//! [`expected_chunk_bound`] computes `2 + ceil(2d / kappa) + ceil(d / cap)`
//! for edit depth `d` under the committed profile. It rounds each quotient
//! up to whole chunks. See the
//! [locality bound and its source](https://github.com/gandr-lang/gandr/blob/main/crates/storage-values/README.md#the-locality-bound).
//!
//! # Edit measurement
//!
//! [`measure_edit`] counts chunks added by an edit and chunks left shared,
//! comparing the closures the closure walk finds for the two roots. The bound
//! is an expectation over residues, not a per-edit ceiling; the locality suite
//! compares corpus means against it. A finite corpus supplies evidence only
//! for the edits and codecs it exercises.

use anodized::spec;
use gandr_storage_chunker::TypedChunkerParams;

use crate::chunk::ChunkStore;
use crate::closure::walk_closure;
use crate::error::ValueError;
use crate::error::ValueQuantity;
use crate::ptr::ContentPtr;
use crate::units::ChunkBound;
use crate::units::ChunkCount;
use crate::units::EditDepth;

/// One edit's observed locality.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the affected and shared counts sum without overflow to at least
///   one chunk, since the edited value's closure contains its root.
/// - provides: a representable partition count for the edited closure.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 on identical and disjoint one-chunk values observes the
///   exact two partitions. Forged empty and overflowing totals are rejected,
///   separating impossible measurements without assuming a locality theorem for
///   arbitrary edits.
/// - witness: `locality::tests::measurements_partition_identical_and_disjoint_closures`
#[spec(maintains: usize::from(self.chunks_affected)
    .checked_add(usize::from(self.chunks_shared)).is_some_and(|total| total > 0_usize))]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct LocalityMeasurement
{
    /// The constructor depth of the edited node.
    pub edit_depth: EditDepth,
    /// Chunks reachable from the edited value and not from the original: the
    /// chunks the edit added.
    pub chunks_affected: ChunkCount,
    /// Chunks reachable from both: the chunks the edit left shared.
    pub chunks_shared: ChunkCount,
}

/// The expected number of chunks an edit at `depth` affects under `params`.
///
/// # Specification
/// - requires: `params` is the profile the value was committed under.
/// - ensures: on success exactly `2 + ceil(2d / kappa) + ceil(d / cap)`, where
///   `d` is `depth`. A representable bound is admitted even when the numerator
///   `2d` needs more than sixty-four bits.
/// - provides: the number a measured mean is read against.
/// - fails: [`ValueError::ArithmeticOverflow`] exactly when the resulting bound
///   exceeds sixty-four bits, never by wrapping or saturation.
/// - panics: none.
///
/// # Errors
/// [`ValueError::ArithmeticOverflow`] — the bound passes sixty-four bits.
///
/// # Adequacy
/// - hypothesis: L2 on depths 0, 5, 8 and 64 under profiles (4, 64) and (1, 1)
///   observes hand-calculated bounds. L3 at the depth ceiling under (4, 64) and
///   the widest profile separates numerator width from result width; the tight
///   profile's last admitted and next depths distinguish quotient, sum and
///   final-addition overflow. This finite domain does not establish the
///   probabilistic locality theorem.
/// - witness: `locality::tests::the_bound_matches_the_formula_by_hand`
/// - witness: `locality::tests::large_depths_refuse_only_unrepresentable_bounds`
#[inline]
#[spec(ensures: |ret| {
    let wide_depth = u128::from(u64::from(depth));
    let expected = wide_depth.saturating_mul(2_u128)
        .div_ceil(u128::from(u64::from(params.kappa())))
        .saturating_add(wide_depth.div_ceil(u128::from(u64::from(params.cap()))))
        .saturating_add(2_u128);
    ret.as_ref().is_ok_and(|bound| u128::from(u64::from(*bound)) == expected)
        || (expected > u128::from(u64::MAX)
            && ret == Err(ValueError::ArithmeticOverflow { quantity: ValueQuantity::LocalityBound }))
})]
pub fn expected_chunk_bound(
    depth: EditDepth,
    params: &TypedChunkerParams,
) -> Result<ChunkBound, ValueError>
{
    let overflow = ValueError::ArithmeticOverflow {
        quantity: ValueQuantity::LocalityBound,
    };
    let depth = u64::from(depth);
    let kappa = u64::from(params.kappa());
    let cap = u64::from(params.cap());

    // Twice any input fits in u128; narrowing before division rejects valid bounds.
    let twice = u128::from(depth).saturating_mul(2_u128);
    let Ok(path) = u64::try_from(twice.div_ceil(u128::from(kappa)))
    else {
        return Err(overflow);
    };
    let spill = depth.div_ceil(cap);

    path.checked_add(spill)
        .and_then(|sum| sum.checked_add(2_u64))
        .map(ChunkBound::from)
        .ok_or(overflow)
}

/// Measures one edit: the chunks reachable from `after` and not from
/// `before`, and the chunks reachable from both.
///
/// # Specification
/// - requires: both pointers were committed into `store`.
/// - ensures: on success `chunks_affected` counts the distinct chunks in the
///   closure of `after` that are not in the closure of `before`, and
///   `chunks_shared` those in both, each closure the chunks a reader of its
///   pointer loads.
/// - provides: the observation a corpus of edits reads against
///   [`expected_chunk_bound`].
/// - fails: the closure walk's refusals: a chunk the store cannot answer for, a
///   malformed subtree, or a spent decode budget.
/// - panics: none.
///
/// # Errors
/// [`ValueError`] — as listed above.
///
/// # Adequacy
/// - hypothesis: L2 on balanced corpora of depths two through eight observes
///   mean affected counts below the stated bound. L3 on a fixed distinct-
///   subtree value at kappa one and caps 1, 2, 3, 64 and `u64::MAX` observes
///   exactly the edited path affected and all other chunks shared. Identical
///   and disjoint roots separate both partition extremes; committed mutation
///   preserves the old value and grows the store by the affected count. These
///   finite corpora do not prove a bound for each edit or arbitrary codecs.
/// - witness: `tests::laws::an_edit_under_every_cut_affects_exactly_its_path`
/// - witness: `tests::laws::a_value_mutated_after_commit_commits_anew_and_the_old_pointer_still_reads_the_old_value`
/// - witness: `tests::values::measured_chunk_counts_sit_inside_the_locality_bound`
/// - witness: `tests::values::an_early_edit_moves_only_its_own_chunk_under_chunk_local_bases`
/// - witness: `locality::tests::measurements_partition_identical_and_disjoint_closures`
#[inline]
#[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|measured| {
    measured.edit_depth == edit_depth
        && anodized::types::Spec::predicate(measured)
}))]
pub fn measure_edit(
    store: &dyn ChunkStore,
    before: ContentPtr,
    after: ContentPtr,
    edit_depth: EditDepth,
) -> Result<LocalityMeasurement, ValueError>
{
    let original = walk_closure(store, before)?;
    let edited = walk_closure(store, after)?;
    let original = original.closure().digests();
    let edited = edited.closure().digests();
    let shared = edited.intersection(original).count();
    let affected = edited.len().saturating_sub(shared);

    Ok(LocalityMeasurement {
        edit_depth,
        chunks_affected: ChunkCount::from(affected),
        chunks_shared: ChunkCount::from(shared),
    })
}

#[cfg(test)]
mod tests
{
    use gandr_storage_chunker::Kappa;
    use gandr_storage_chunker::TokenCap;
    use gandr_storage_chunker::TypedChunkerParams;

    use super::LocalityMeasurement;
    use super::expected_chunk_bound;
    use super::measure_edit;
    use crate::ChunkStore as _;
    use crate::ContentPtr;
    use crate::InMemoryChunkStore;
    use crate::TokenBody;
    use crate::TokenOffset;
    use crate::error::ValueError;
    use crate::error::ValueQuantity;
    use crate::frame_chunk;
    use crate::units::ChunkBound;
    use crate::units::ChunkCount;
    use crate::units::EditDepth;

    #[test]
    fn the_bound_matches_the_formula_by_hand()
    {
        let params = TypedChunkerParams::new(
            Kappa::try_from(4_u64).expect("kappa is nonzero"),
            TokenCap::try_from(64_u64).expect("the cap is nonzero"),
        );

        // d = 0: 2 + 0 + 0.
        assert_eq!(
            expected_chunk_bound(EditDepth::from(0_u64), &params),
            Ok(ChunkBound::from(2_u64))
        );
        // d = 5: 2 + ceil(10 / 4) + ceil(5 / 64) = 2 + 3 + 1.
        assert_eq!(
            expected_chunk_bound(EditDepth::from(5_u64), &params),
            Ok(ChunkBound::from(6_u64))
        );
        // d = 8: 2 + ceil(16 / 4) + ceil(8 / 64) = 2 + 4 + 1.
        assert_eq!(
            expected_chunk_bound(EditDepth::from(8_u64), &params),
            Ok(ChunkBound::from(7_u64))
        );
        // d = 64 at kappa 1, cap 1: 2 + 128 + 64.
        let tight = TypedChunkerParams::new(
            Kappa::try_from(1_u64).expect("kappa is nonzero"),
            TokenCap::try_from(1_u64).expect("the cap is nonzero"),
        );
        assert_eq!(
            expected_chunk_bound(EditDepth::from(64_u64), &tight),
            Ok(ChunkBound::from(194_u64))
        );
    }

    #[test]
    fn large_depths_refuse_only_unrepresentable_bounds()
    {
        let wide = TypedChunkerParams::new(
            Kappa::try_from(u64::MAX).expect("nonzero kappa"),
            TokenCap::try_from(u64::MAX).expect("nonzero cap"),
        );
        assert_eq!(
            expected_chunk_bound(EditDepth::from(u64::MAX), &wide),
            Ok(ChunkBound::from(5_u64))
        );
        let ordinary = TypedChunkerParams::new(
            Kappa::try_from(4_u64).expect("nonzero kappa"),
            TokenCap::try_from(64_u64).expect("nonzero cap"),
        );
        // 2 + 2^63 + 2^58, although the numerator 2d needs 65 bits.
        assert_eq!(
            expected_chunk_bound(EditDepth::from(u64::MAX), &ordinary),
            Ok(ChunkBound::from(0x8400_0000_0000_0002_u64))
        );
        let tight = TypedChunkerParams::new(
            Kappa::try_from(1_u64).expect("nonzero kappa"),
            TokenCap::try_from(1_u64).expect("nonzero cap"),
        );
        assert_eq!(
            expected_chunk_bound(EditDepth::from(6_148_914_691_236_517_204_u64), &tight),
            Ok(ChunkBound::from(u64::MAX - 1_u64))
        );
        for depth in [
            6_148_914_691_236_517_205_u64,
            6_148_914_691_236_517_206_u64,
            u64::MAX,
        ] {
            assert_eq!(
                expected_chunk_bound(EditDepth::from(depth), &tight),
                Err(ValueError::ArithmeticOverflow {
                    quantity: ValueQuantity::LocalityBound
                })
            );
        }
    }

    #[test]
    fn measurements_partition_identical_and_disjoint_closures()
    {
        let before =
            frame_chunk(TokenBody::from(&[1_u8, 42, 5][..])).expect("the first leaf frames");
        let after =
            frame_chunk(TokenBody::from(&[1_u8, 43, 5][..])).expect("the second leaf frames");
        let mut store = InMemoryChunkStore::new();
        store
            .insert(before.as_verified())
            .expect("the first leaf stores");
        store
            .insert(after.as_verified())
            .expect("the second leaf stores");
        let before = ContentPtr::new(before.digest(), TokenOffset::ZERO);
        let after = ContentPtr::new(after.digest(), TokenOffset::ZERO);
        let unchanged = measure_edit(&store, before, before, EditDepth::from(0_u64))
            .expect("the unchanged root measures");
        assert_eq!(unchanged, LocalityMeasurement {
            edit_depth: EditDepth::from(0_u64),
            chunks_affected: ChunkCount::from(0_usize),
            chunks_shared: ChunkCount::from(1_usize),
        });
        let changed = measure_edit(&store, before, after, EditDepth::from(0_u64))
            .expect("the disjoint roots measure");
        assert_eq!(changed, LocalityMeasurement {
            edit_depth: EditDepth::from(0_u64),
            chunks_affected: ChunkCount::from(1_usize),
            chunks_shared: ChunkCount::from(0_usize),
        });
        assert!(anodized::types::Spec::predicate(&unchanged));
        assert!(anodized::types::Spec::predicate(&changed));
        let mut forged = unchanged;
        forged.chunks_shared = ChunkCount::from(0_usize);
        assert!(!anodized::types::Spec::predicate(&forged));
        forged.chunks_affected = ChunkCount::from(usize::MAX);
        forged.chunks_shared = ChunkCount::from(1_usize);
        assert!(!anodized::types::Spec::predicate(&forged));
    }
}
