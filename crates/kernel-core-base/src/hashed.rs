//! A map whose entries sit in recording order, filed by hash in the kernel's
//! one open-addressing index.
//!
//! The kernel's per-session caches keyed by more than a content name — a
//! node's binder reach, a rewrite's answer at a depth — share this one shape
//! with the content table's interning and the check memo: dense entries, one
//! [`HashIndex`] over them, and the key's own equality deciding. The index
//! narrows; it never answers for a key that is not equal.

use alloc::vec::Vec;
use core::hash::Hash;

use anodized::spec;
use gandr_kernel_check_memo::HashIndex;
use gandr_kernel_check_memo::Probe;
use gandr_kernel_check_memo::TableHash;
use gandr_kernel_check_memo::TablePosition;
use quenchant_shape::shape::Maybe;

quenchant_shape::reason_enum! {
    /// Why a map holds no value for a key.
    pub mod hashed_entry {
        /// The map has not been told the key.
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        pub enum Absent {
            /// No entry's key equals it.
            Unrecorded,
        }
    }
}

/// A map from `Key` to `Value`, filed by the key's hash.
///
/// # Specification
/// - requires: `Key`'s `Hash` agrees with its equality.
/// - ensures: at most one entry per key, holding the value last inserted for
///   it.
/// - provides: an unordered map without an ordered search or a hasher
///   dependency.
/// - panics: none.
/// - executable: none — a data declaration; its operations carry the
///   predicates.
///
/// # Adequacy
/// - hypothesis: L3 — keys inserted, re-inserted and never inserted are read
///   back exactly, separating a lost entry, a duplicated one and a stale value.
/// - witness: `hashed::tests::a_map_reads_back_what_it_was_told_last`
#[derive(Clone, Debug)]
pub struct HashedMap<Key, Value>
{
    /// The entries, in first-insertion order.
    entries: Vec<(Key, Value)>,
    /// Each entry's position, filed under its key's hash.
    index: HashIndex,
}

impl<Key, Value> Default for HashedMap<Key, Value>
{
    /// An empty map.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self {
            entries: Vec::new(),
            index: HashIndex::new(),
        }
    }
}

impl<Key, Value> HashedMap<Key, Value>
where
    Key: Hash + Eq,
{
    /// The probe for the entry whose key equals `key`, hashed `hash`.
    ///
    /// # Specification
    /// - requires: `hash` is `key`'s hash.
    /// - ensures: [`Probe::Found`] the position of the entry whose key equals
    ///   `key`, or [`Probe::Vacant`] the slot it would be filed at.
    /// - provides: the one probe reads and writes decide over.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the type.
    /// - witness: `hashed::tests::a_map_reads_back_what_it_was_told_last`
    #[inline]
    #[spec(ensures: |ret| match ret {
        Probe::Found(position) => self.entries.get(usize::from(position))
            .is_some_and(|entry| entry.0 == *key),
        Probe::Vacant(_) => true,
    })]
    fn probe(
        &self,
        key: &Key,
        hash: TableHash,
    ) -> Probe
    {
        self.index.probe(hash, |position| {
            self.entries
                .get(usize::from(position))
                .is_some_and(|entry| entry.0 == *key)
        })
    }

    /// The value held for `key`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the value last inserted for a key equal to `key`, or
    ///   [`hashed_entry::Absent::Unrecorded`] when none was held.
    /// - provides: the cache read.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the type.
    /// - witness: `hashed::tests::a_map_reads_back_what_it_was_told_last`
    #[inline]
    #[spec(ensures: |ret| match ret {
        Maybe::Present(value) => matches!(self.probe(key, TableHash::of(key)),
            Probe::Found(position) if self.entries.get(usize::from(position))
                .is_some_and(|entry| core::ptr::eq(&raw const entry.1, &raw const *value))),
        Maybe::Absent(hashed_entry::Absent::Unrecorded) => true,
    })]
    pub fn get(
        &self,
        key: &Key,
    ) -> Maybe<&Value, hashed_entry::Absent>
    {
        match self.probe(key, TableHash::of(key)) {
            Probe::Found(position) => self
                .entries
                .get(usize::from(position))
                .map_or(Maybe::Absent(hashed_entry::Absent::Unrecorded), |entry| {
                    Maybe::Present(&entry.1)
                }),
            Probe::Vacant(_) => Maybe::Absent(hashed_entry::Absent::Unrecorded),
        }
    }

    /// Hold `value` for `key`, replacing a value already held for it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`HashedMap::get`] answers `value` for `key`; every other
    ///   key's value is unchanged. A map already holding `u32::MAX` keys
    ///   declines a fresh one, which a later read misses.
    /// - provides: the cache write.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — `key` and `value` move into the map, so the
    ///   post-state cannot be compared against them without a `Clone` bound the
    ///   map does not take.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the type.
    /// - witness: `hashed::tests::a_map_reads_back_what_it_was_told_last`
    #[inline]
    pub fn insert(
        &mut self,
        key: Key,
        value: Value,
    )
    {
        let hash = TableHash::of(&key);
        match self.probe(&key, hash) {
            Probe::Found(position) => {
                if let Some(entry) = self.entries.get_mut(usize::from(position)) {
                    entry.1 = value;
                }
            },
            Probe::Vacant(slot) => {
                if let Ok(position) = TablePosition::try_from(self.entries.len()) {
                    self.index.insert(slot, hash, position);
                    self.entries.push((key, value));
                }
            },
        }
    }
}

#[cfg(test)]
mod tests
{
    use quenchant_shape::shape::Maybe;

    use super::HashedMap;
    use super::hashed_entry;

    #[test]
    fn a_map_reads_back_what_it_was_told_last()
    {
        let mut map: HashedMap<(u32, u8), u64> = HashedMap::default();
        for key in 0_u32 .. 100 {
            map.insert((key, 1), u64::from(key));
        }
        map.insert((7, 1), 700);
        for key in 0_u32 .. 100 {
            let expected = if key == 7 { 700 } else { u64::from(key) };
            assert_eq!(map.get(&(key, 1)), Maybe::Present(&expected), "key {key}");
            assert_eq!(
                map.get(&(key, 2)),
                Maybe::Absent(hashed_entry::Absent::Unrecorded),
                "a key differing in its last component is another key"
            );
        }
    }
}
