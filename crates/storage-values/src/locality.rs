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
/// - ensures: `|ret| ret.as_ref().ok().is_none_or(|bound| (2_u128 ..=
///   u128::from(u64::from(depth)).saturating_mul(3_u128).
///   saturating_add(2_u128)) .contains(&u128::from(u64::from(*bound))))` — on
///   success `2 + ceil(2d / kappa) + ceil(d / cap)`, which lies between two and
///   `2 + 3d` because kappa and the cap are at least one.
/// - provides: the number a measured mean is read against.
/// - fails: [`ValueError::ArithmeticOverflow`] when the arithmetic passes the
///   width — never a wrapped or saturated bound, which would make every
///   comparison against it meaningless.
/// - panics: none.
///
/// # Errors
/// [`ValueError::ArithmeticOverflow`] — the bound passes sixty-four bits.
///
/// # Adequacy
/// - hypothesis: L2 agreement — the bound at fixed depths and profiles equals
///   the formula worked by hand — plus L3 for the overflow refusal at the
///   width.
/// - witness: `locality::tests::the_bound_matches_the_formula_by_hand`
#[inline]
#[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|bound| (2_u128
    ..= u128::from(u64::from(depth))
        .saturating_mul(3_u128)
        .saturating_add(2_u128))
    .contains(&u128::from(u64::from(*bound)))))]
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

    let Some(twice) = depth.checked_mul(2_u64)
    else {
        return Err(overflow);
    };
    let path = twice.div_ceil(kappa);
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
/// - hypothesis: L2 agreement — the mean measured over every leaf edit of a
///   corpus sits inside the bound, and an early edit shares most chunks — plus
///   L3 at kappa one, where every constructor is its own chunk and each leaf
///   edit of a value with no repeated subtree measures exactly its root path
///   affected and every other chunk shared, and for a value mutated after its
///   commit, whose affected count equals the store's growth.
/// - witness: `tests::laws::an_edit_under_every_cut_affects_exactly_its_path`
/// - witness: `tests::laws::a_value_mutated_after_commit_commits_anew_and_the_old_pointer_still_reads_the_old_value`
/// - witness: `tests::values::measured_chunk_counts_sit_inside_the_locality_bound`
/// - witness: `tests::values::an_early_edit_moves_only_its_own_chunk_under_chunk_local_bases`
#[inline]
#[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|measured| {
    measured.edit_depth == edit_depth
        && usize::from(measured.chunks_affected).saturating_add(usize::from(measured.chunks_shared)) >= 1_usize
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

    use super::expected_chunk_bound;
    use crate::error::ValueError;
    use crate::error::ValueQuantity;
    use crate::units::ChunkBound;
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

        assert_eq!(
            expected_chunk_bound(EditDepth::from(u64::MAX), &params),
            Err(ValueError::ArithmeticOverflow {
                quantity: ValueQuantity::LocalityBound,
            })
        );
    }
}
