//! The bundle of a checkpoint set over its sources: each source's run of
//! checkpoints under the source's key. So the set of a closure restricts to
//! the set of each closure inside it by keys alone.
//!
//! A check of a closure gives one checkpoint for each item. Each checkpoint
//! is a function of its own source and of the sources that this source
//! reaches. So the set is a section over the closure, and the section over
//! the closure of a source that it reaches is a part of it. A [`SourceKey`]
//! names that part: it digests the content keys of the source's items and the
//! keys of the sources that the source imports. Two sources with one key have
//! one closure, so they have one run of checkpoints. [`Bundle::restrict`]
//! gives the set of a closure from the runs that its keys name. It judges no
//! item and encodes no item.
//!
//! # Boundaries
//!
//! A front end states the sources of a program as [`SourceRun`]s, because the
//! front end alone knows them. [`SourceKeys::of`] encodes each item of a
//! program once. [`Bundle::of`] reads the content keys that the checkpoints of
//! a set hold, and encodes nothing. A source with an opaque item has no key.
//! A source that imports a source with no key has no key. The bundle gives no
//! set for a closure that holds such a source, and the caller walks the set
//! instead.
//!
//! The restriction takes the key of each source of the smaller closure, in the
//! order that this closure lays them. A closure lays its sources by a walk
//! from its own root, so two closures can lay one source in two orders.
//!
//! # References
//!
//! - `vault:01a1aa2d-a69c-7030-91e0-337d68d88151` — newest: §
//!   presented-spaces-quasi-coherence — a stored result is a section of a
//!   weakly quasi-coherent bundle over its support, so its restriction to a
//!   sub-support is an operation on its key, and no walk.
//! - Felix Cherubini, Thierry Coquand and Matthias Hutzler. "A Foundation for
//!   Synthetic Algebraic Geometry." _Mathematical Structures in Computer
//!   Science_ 34, 9 (2024), pages 1008–1053. `arXiv:2307.00073` — Definition
//!   7.1.5 and Lemma 7.1.8: a bundle over a space is weakly quasi-coherent when
//!   its restriction to an open `D(f)` is its localisation at `f`, so the
//!   restriction equals the section over the smaller space.

use alloc::collections::BTreeMap;
use alloc::sync::Arc;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_core_checker::CheckBudget;
use quenchant_shape::shape::Maybe;

use crate::boundary::ItemCount;
use crate::boundary::ItemOrdinal;
use crate::boundary::SourceOrdinal;
use crate::checkpoint::Checkpoints;
use crate::checkpoint::ContentKey;
use crate::checkpoint::ItemCheckpoint;
use crate::checkpoint::content_key;
use crate::checkpoint::recall;
use crate::region::Program;

#[cfg(test)]
mod tests;

quenchant_shape::reason_enum! {
    /// Why a source has no key.
    pub mod unkeyed {
        /// The reason the source has no key.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// An item of the source is opaque, so no content key names it.
            Opaque,
            /// The source imports a source that has no key.
            Reaches,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a bundle gives no set for a closure.
    pub mod unheld {
        /// The reason the bundle gives no set.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// A source of the closure has no key.
            Unkeyed,
            /// The bundle holds no run under a key of the closure.
            Unheld,
        }
    }
}

/// How many bytes of a digest a source key keeps.
const KEY_DIGEST: usize = 16;

/// The key of a source's run of checkpoints: the first sixteen bytes of the
/// BLAKE3 digest of the source's item count, its items' content keys, its
/// import count and its imports' keys, each in order.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SourceKey([u8; KEY_DIGEST]);

/// One source of a program as its front end lays it: how many items the
/// source declares after the items of the sources before it, and the sources
/// that it imports.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SourceRun
{
    /// How many items the source declares.
    items: ItemCount,
    /// The sources it imports, in the order it writes them.
    imports: Vec<SourceOrdinal>,
}

impl SourceRun
{
    /// The source that declares `items` items and imports `imports`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        items: ItemCount,
        imports: Vec<SourceOrdinal>,
    ) -> Self
    {
        Self { items, imports }
    }

    /// How many items the source declares.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn items(&self) -> ItemCount
    {
        self.items
    }
}

/// Why the sources that a front end states do not lay out a program.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum SourcesError
{
    /// A source imports a source that does not come before it.
    Forward
    {
        /// The importing source.
        source: SourceOrdinal,
        /// The source it imports.
        import: SourceOrdinal,
    },
    /// The runs of the sources count other items than the program holds.
    Uncovered
    {
        /// The items the runs count.
        runs: ItemCount,
        /// The items the program holds.
        items: ItemCount,
    },
}

impl fmt::Display for SourcesError
{
    /// Writes the failure's message.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Forward { source, import } => write!(
                f,
                "source {} imports source {}, which does not come before it",
                usize::from(source),
                usize::from(import)
            ),
            Self::Uncovered { runs, items } => write!(
                f,
                "the sources lay out {} items, and the program holds {}",
                usize::from(runs),
                usize::from(items)
            ),
        }
    }
}

impl core::error::Error for SourcesError
{
}

/// The key of each source of a program, in the program's order of sources.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SourceKeys(Vec<Maybe<SourceKey, unkeyed::Absent>>);

impl SourceKeys
{
    /// The key of each source of `program`, as `sources` lay it out. The
    /// function encodes each item of `program` once.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one key for each source, as [`Bundle::of`] reads it off the
    ///   checkpoints of `program`; a source with an opaque item, or a source
    ///   that imports a source with no key, has none.
    /// - fails: [`SourcesError::Forward`] for an import that does not come
    ///   before its source; [`SourcesError::Uncovered`] when the runs count
    ///   other items than `program` holds.
    /// - panics: none.
    ///
    /// # Errors
    /// [`SourcesError`] — `sources` do not lay out `program`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a source under two imports that differ, a forward
    ///   import, runs short of the program and a source beside an opaque item.
    /// - witness: `bundle::tests::a_source_s_key_moves_with_what_it_imports_6512`
    /// - witness: `bundle::tests::a_closure_with_an_opaque_source_restricts_to_nothing_6512`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |keys| keys.0.len() == sources.len()))]
    #[inline]
    pub fn of(
        program: &Program,
        sources: &[SourceRun],
    ) -> Result<Self, SourcesError>
    {
        keyed(sources, ItemCount::from(program.items().len()), |ordinal| {
            content_key(program, ordinal)
        })
        .map(Self)
    }

    /// Each source's key, in the program's order of sources.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn keys(&self) -> &[Maybe<SourceKey, unkeyed::Absent>]
    {
        &self.0
    }
}

/// A checkpoint set cut at its sources: the run of checkpoints of each source
/// with a key, under that key. A run is shared, not copied, by each set that
/// the bundle restricts to.
#[derive(Clone, Debug)]
pub struct Bundle
{
    /// The allowance every judgement of the set ran under.
    budget: CheckBudget,
    /// Each keyed source's run of checkpoints.
    runs: BTreeMap<SourceKey, Arc<[ItemCheckpoint]>>,
}

impl Bundle
{
    /// The bundle of `checkpoints`, the set that a check of the program
    /// `sources` lay out gives. Each key comes from the content keys that the
    /// checkpoints hold, so the function encodes no item.
    ///
    /// # Specification
    /// - requires: `checkpoints` is the set of the program that `sources` lay
    ///   out.
    /// - ensures: the run of each source with a key, under the key that
    ///   [`SourceKeys::of`] gives that source, at the set's budget.
    /// - fails: as [`SourceKeys::of`], with the set's item count in place of
    ///   the program's.
    /// - panics: none.
    ///
    /// # Errors
    /// [`SourcesError`] — `sources` do not lay out the set.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Bundle::restrict`].
    /// - witness: `bundle::tests::a_set_restricts_to_the_fresh_set_of_a_closure_inside_it_6512`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |bundle| {
        bundle.budget == checkpoints.budget() && bundle.runs.len() <= sources.len()
    }))]
    #[inline]
    pub fn of(
        checkpoints: &Checkpoints,
        sources: &[SourceRun],
    ) -> Result<Self, SourcesError>
    {
        let items = checkpoints.items();
        let keys = keyed(sources, ItemCount::from(items.len()), |ordinal| {
            items
                .get(usize::from(ordinal))
                .map_or(Maybe::Absent(recall::Absent::Opaque), ItemCheckpoint::key)
        })?;
        let mut runs = BTreeMap::new();
        let mut start = 0_usize;
        for (run, key) in sources.iter().zip(keys) {
            let end = start.saturating_add(usize::from(run.items));
            if let Maybe::Present(key) = key {
                let _held = runs
                    .entry(key)
                    .or_insert_with(|| Arc::from(items.get(start .. end).unwrap_or_default()));
            }
            start = end;
        }
        Ok(Self {
            budget: checkpoints.budget(),
            runs,
        })
    }

    /// The set of the closure whose sources have the keys `keys`: each
    /// source's run, in the order of `keys`. The bundle shares each run, so
    /// the set copies one pointer for each item and no checkpoint.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the runs under `keys`, in their order, at the bundle's
    ///   budget; [`unheld::Absent::Unkeyed`] when a source has no key, and
    ///   [`unheld::Absent::Unheld`] when the bundle holds no run under a key.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a closure inside the checked one, a closure whose
    ///   first source differs and a closure that holds an opaque item.
    /// - witness: `bundle::tests::a_set_restricts_to_the_fresh_set_of_a_closure_inside_it_6512`
    /// - witness: `bundle::tests::a_source_s_key_moves_with_what_it_imports_6512`
    /// - witness: `bundle::tests::a_closure_with_an_opaque_source_restricts_to_nothing_6512`
    #[spec(ensures: |ret| match ret {
        Maybe::Present(ref set) => set.budget() == self.budget,
        Maybe::Absent(_) => true,
    })]
    #[inline]
    pub fn restrict(
        &self,
        keys: &SourceKeys,
    ) -> Maybe<Checkpoints, unheld::Absent>
    {
        let mut found: Vec<&Arc<[ItemCheckpoint]>> = Vec::with_capacity(keys.0.len());
        let mut count = 0_usize;
        for key in &keys.0 {
            let Maybe::Present(key) = *key
            else {
                return Maybe::Absent(unheld::Absent::Unkeyed);
            };
            let Some(run) = self.runs.get(&key)
            else {
                return Maybe::Absent(unheld::Absent::Unheld);
            };
            count = count.saturating_add(run.len());
            found.push(run);
        }
        let mut items = Vec::with_capacity(count);
        for run in found {
            items.extend_from_slice(run);
        }
        Maybe::Present(Checkpoints::new(self.budget, items))
    }
}

/// The key of each run of `sources` over `items` items, each item's content
/// key as `key` reads it.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one key for each run, the digest of the run's item count, the
///   content keys of its items, its import count and its imports' keys; an
///   opaque item, or an import with no key, leaves the run with none.
/// - fails: [`SourcesError::Uncovered`] when the runs count other than `items`;
///   [`SourcesError::Forward`] at the first import that does not come before
///   its source.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`SourceKeys::of`].
/// - witness: `bundle::tests::a_source_s_key_moves_with_what_it_imports_6512`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |keys| keys.len() == sources.len()))]
fn keyed<Key>(
    sources: &[SourceRun],
    items: ItemCount,
    mut key: Key,
) -> Result<Vec<Maybe<SourceKey, unkeyed::Absent>>, SourcesError>
where
    Key: FnMut(ItemOrdinal) -> Maybe<ContentKey, recall::Absent>,
{
    let runs = sources.iter().fold(0_usize, |total, run| {
        total.saturating_add(usize::from(run.items))
    });
    if runs != usize::from(items) {
        return Err(SourcesError::Uncovered {
            runs: ItemCount::from(runs),
            items,
        });
    }
    let count = |of: usize| u64::try_from(of).unwrap_or(u64::MAX).to_le_bytes();
    let mut keys: Vec<Maybe<SourceKey, unkeyed::Absent>> = Vec::with_capacity(sources.len());
    let mut start = 0_usize;
    for (source, run) in sources.iter().enumerate() {
        let end = start.saturating_add(usize::from(run.items));
        let mut hasher = blake3::Hasher::new();
        let _counted = hasher.update(&count(usize::from(run.items)));
        // The first reason the run has no key, once one shows.
        let mut missing: Option<unkeyed::Absent> = None;
        for ordinal in start .. end {
            if let Maybe::Present(content) = key(ItemOrdinal::from(ordinal)) {
                content.digest_into(&mut hasher);
            }
            else {
                missing = Some(unkeyed::Absent::Opaque);
                break;
            }
        }
        start = end;
        let _counted = hasher.update(&count(run.imports.len()));
        for &import in &run.imports {
            match keys.get(usize::from(import)) {
                Some(&Maybe::Present(SourceKey(ref imported))) => {
                    let _digested = hasher.update(imported);
                },
                Some(&Maybe::Absent(_)) => {
                    missing = missing.or(Some(unkeyed::Absent::Reaches));
                },
                None => {
                    return Err(SourcesError::Forward {
                        source: SourceOrdinal::from(source),
                        import,
                    });
                },
            }
        }
        keys.push(missing.map_or_else(
            || {
                let mut digest = [0_u8; KEY_DIGEST];
                for (byte, digested) in digest.iter_mut().zip(hasher.finalize().as_bytes()) {
                    *byte = *digested;
                }
                Maybe::Present(SourceKey(digest))
            },
            Maybe::Absent,
        ));
    }
    Ok(keys)
}
