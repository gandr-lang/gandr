//! **Chunked maps**: an ordered map whose clones share their entries in
//! chunks of at most [`CHUNK`] entries.
//!
//! A clone takes the list of chunks by reference. A write to one entry copies
//! the list and the one chunk that holds the entry while a clone shares them,
//! and no other entry. A read finds the chunk by a binary search over the
//! first key of each chunk, then the entry by a binary search in the chunk.
//! The kernel keeps the indexes of an environment so, and a readmission that
//! keeps an environment of its record copies only the chunks that it writes.

use alloc::sync::Arc;
use alloc::vec::Vec;
use core::ops::Bound;
use core::ops::RangeBounds;

use anodized::spec;

/// How many entries a chunk holds at most: a write to one entry copies at most
/// this many entries.
const CHUNK: usize = 64;

/// How few entries a chunk holds before a removal merges it with the next
/// chunk, so that the list of chunks stays short.
const SPARSE: usize = CHUNK >> 2;

/// How many entries a [`ChunkedMap`] holds.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct EntryCount(usize);

impl From<usize> for EntryCount
{
    /// The count of `entries`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(entries: usize) -> Self
    {
        Self(entries)
    }
}

impl From<EntryCount> for usize
{
    /// The number of entries.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: EntryCount) -> Self
    {
        count.0
    }
}

/// The place of an entry in a map's list of chunks: its chunk, and its offset
/// in the chunk.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Place
{
    /// The offset of the chunk in the list.
    chunk: usize,
    /// The offset of the entry in the chunk.
    within: usize,
}

/// The offset of a chunk in a map's list of chunks.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct ChunkAt(usize);

/// An ordered map whose clones share their entries in chunks.
///
/// # Specification
/// - executable: none — a data declaration; [`Self::get`], [`Self::insert`],
///   [`Self::remove`] and [`Self::range`] state what a read and a write see.
///
/// # Adequacy
/// - hypothesis: L3 — a chunked map written and read beside a clone answers as
///   an ordered map does, and the clone answers as it did.
/// - witness: `chunked::tests::a_chunked_map_answers_as_an_ordered_map_beside_its_clone`
/// - witness: `chunked::tests::a_write_to_one_entry_copies_its_chunk_alone`
#[derive(Clone, Debug)]
pub struct ChunkedMap<Key, Value>
{
    /// The chunks in key order, shared with each clone by reference.
    #[expect(
        clippy::rc_buffer,
        reason = "a write inserts and removes chunks in place while no clone shares the list"
    )]
    chunks: Option<Arc<Vec<Chunk<Key, Value>>>>,
    /// How many entries the chunks hold.
    len: usize,
}

/// One chunk of a [`ChunkedMap`]: its least key, and its entries in key order,
/// shared with each clone by reference.
#[derive(Clone, Debug)]
struct Chunk<Key, Value>
{
    /// The least key of the chunk's entries.
    first: Key,
    /// The entries, at least one and at most [`CHUNK`], in key order.
    #[expect(
        clippy::rc_buffer,
        reason = "a write inserts and removes entries in place while no clone shares the chunk"
    )]
    entries: Arc<Vec<(Key, Value)>>,
}

impl<Key, Value> Default for ChunkedMap<Key, Value>
{
    /// The empty map.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self::new()
    }
}

impl<Key: PartialEq, Value: PartialEq> PartialEq for ChunkedMap<Key, Value>
{
    /// Whether the two maps hold the same entries.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn eq(
        &self,
        other: &Self,
    ) -> bool
    {
        self.len == other.len
            && (self.chunks.as_ref().map(Arc::as_ptr) == other.chunks.as_ref().map(Arc::as_ptr)
                || self
                    .entries()
                    .zip(other.entries())
                    .all(|(mine, theirs)| mine == theirs))
    }
}

impl<Key: Eq, Value: Eq> Eq for ChunkedMap<Key, Value>
{
}

impl<Key, Value> ChunkedMap<Key, Value>
{
    /// The empty map, for a constant or a static.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new() -> Self
    {
        Self {
            chunks: None,
            len: 0,
        }
    }

    /// How many entries the map holds.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn len(&self) -> EntryCount
    {
        EntryCount(self.len)
    }

    /// The chunks, in key order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn chunks(&self) -> &[Chunk<Key, Value>]
    {
        self.chunks.as_deref().map_or(&[], Vec::as_slice)
    }

    /// Every entry, in key order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn entries(&self) -> impl DoubleEndedIterator<Item = &(Key, Value)>
    {
        self.chunks().iter().flat_map(|chunk| chunk.entries.iter())
    }

    /// Every entry, in key order, read from either end.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn iter(&self) -> impl DoubleEndedIterator<Item = (&Key, &Value)>
    {
        self.entries().map(|&(ref key, ref value)| (key, value))
    }

    /// Every key, in order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn keys(&self) -> impl DoubleEndedIterator<Item = &Key>
    {
        self.entries().map(|&(ref key, _)| key)
    }

    /// Every value, in the order of its key.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn values(&self) -> impl DoubleEndedIterator<Item = &Value>
    {
        self.entries().map(|&(_, ref value)| value)
    }

    /// The entry of the least key, or `None` for an empty map.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn first_key_value(&self) -> Option<(&Key, &Value)>
    {
        self.iter().next()
    }

    /// The entry of the greatest key, or `None` for an empty map.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn last_key_value(&self) -> Option<(&Key, &Value)>
    {
        let &(ref key, ref value) = self.chunks().last()?.entries.last()?;
        Some((key, value))
    }
}

impl<Key: Ord, Value> ChunkedMap<Key, Value>
{
    /// The chunk that holds `key` when the map holds it: the last chunk whose
    /// first key is at or below `key`, or the first chunk when every first
    /// key is above it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn chunk_of(
        chunks: &[Chunk<Key, Value>],
        key: &Key,
    ) -> ChunkAt
    {
        ChunkAt(
            chunks
                .partition_point(|chunk| chunk.first <= *key)
                .saturating_sub(1),
        )
    }

    /// The place of the entry of `key`, or `None` when the map does not hold
    /// it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn held(
        &self,
        key: &Key,
    ) -> Option<Place>
    {
        let chunks = self.chunks();
        let ChunkAt(chunk) = Self::chunk_of(chunks, key);
        let within = chunks
            .get(chunk)?
            .entries
            .binary_search_by(|&(ref held, _)| held.cmp(key))
            .ok()?;
        Some(Place { chunk, within })
    }

    /// The place of the first entry whose key is past `bound` from below: at
    /// or above an included key, above an excluded key. A place past the
    /// last entry of its chunk is the start of the next chunk.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn lower(
        &self,
        bound: Bound<&Key>,
    ) -> Place
    {
        let start = Place {
            chunk: 0,
            within: 0,
        };
        let chunks = self.chunks();
        let (key, above) = match bound {
            Bound::Unbounded => return start,
            Bound::Included(key) => (key, false),
            Bound::Excluded(key) => (key, true),
        };
        let ChunkAt(at) = Self::chunk_of(chunks, key);
        let Some(chunk) = chunks.get(at)
        else {
            return start;
        };
        let within = chunk
            .entries
            .partition_point(|&(ref held, _)| if above { held <= key } else { held < key });
        if within >= chunk.entries.len() {
            Place {
                chunk: at.saturating_add(1),
                within: 0,
            }
        }
        else {
            Place { chunk: at, within }
        }
    }

    /// The value of `key`, or `None` when the map does not hold it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn get(
        &self,
        key: &Key,
    ) -> Option<&Value>
    {
        let Place { chunk, within } = self.held(key)?;
        self.chunks()
            .get(chunk)?
            .entries
            .get(within)
            .map(|&(_, ref value)| value)
    }

    /// The entries whose keys `range` holds, in key order, read from either
    /// end.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn range<Range>(
        &self,
        range: Range,
    ) -> impl DoubleEndedIterator<Item = (&Key, &Value)>
    where
        Range: RangeBounds<Key>,
    {
        let start = self.lower(range.start_bound());
        // The end is the first place past the range: past an included key,
        // at or past an excluded one.
        let end = match range.end_bound() {
            Bound::Unbounded => Place {
                chunk: self.chunks().len(),
                within: 0,
            },
            Bound::Included(key) => self.lower(Bound::Excluded(key)),
            Bound::Excluded(key) => self.lower(Bound::Included(key)),
        };
        let end = end.max(start);
        let last = if end.within == 0 {
            end.chunk
        }
        else {
            end.chunk.saturating_add(1)
        };
        self.chunks()
            .get(start.chunk .. last)
            .unwrap_or_default()
            .iter()
            .enumerate()
            .flat_map(move |(offset, chunk)| {
                let at = start.chunk.saturating_add(offset);
                let from = if at == start.chunk { start.within } else { 0 };
                let to = if at == end.chunk {
                    end.within
                }
                else {
                    chunk.entries.len()
                };
                chunk.entries.get(from .. to).unwrap_or_default()
            })
            .map(|&(ref key, ref value)| (key, value))
    }
}

/// The list of chunks of a map, to change: shared with no clone after. A
/// function of the field alone, so a write keeps the map's count at hand.
///
/// # Specification
/// trivial.
#[inline]
#[expect(
    clippy::rc_buffer,
    reason = "a write inserts and removes chunks in place while no clone shares the list"
)]
fn owned<Key, Value>(
    chunks: &mut Option<Arc<Vec<Chunk<Key, Value>>>>
) -> &mut Vec<Chunk<Key, Value>>
where
    Key: Clone,
    Value: Clone,
{
    Arc::make_mut(chunks.get_or_insert_with(Arc::default))
}

impl<Key: Ord + Clone, Value: Clone> ChunkedMap<Key, Value>
{
    /// The value of `key`, to change, or `None` when the map does not hold
    /// it. A write copies the list and the chunk that holds `key` while a
    /// clone shares them, and no other entry; a key the map does not hold
    /// copies nothing.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn get_mut(
        &mut self,
        key: &Key,
    ) -> Option<&mut Value>
    {
        let Place { chunk, within } = self.held(key)?;
        let chunk = owned(&mut self.chunks).get_mut(chunk)?;
        Arc::make_mut(&mut chunk.entries)
            .get_mut(within)
            .map(|&mut (_, ref mut value)| value)
    }

    /// Change the value of `key` by `change`, after the default value enters
    /// at `key` when the map does not hold it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn update_or_default<Change>(
        &mut self,
        key: Key,
        change: Change,
    ) where
        Value: Default,
        Change: FnOnce(&mut Value),
    {
        if let Some(value) = self.get_mut(&key) {
            change(value);
            return;
        }
        let mut value = Value::default();
        change(&mut value);
        let _absent = self.insert(key, value);
    }

    /// Hold `value` at `key`: the value it held before, or `None`. A chunk
    /// that the entry fills past [`CHUNK`] splits in two.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the map holds `value` at `key`, and every other entry as it
    ///   was; one more entry when it did not hold `key`.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`ChunkedMap`].
    /// - witness: `chunked::tests::a_chunked_map_answers_as_an_ordered_map_beside_its_clone`
    #[spec(
        captures: count = usize::from(self.len()),
        ensures: |previous| usize::from(self.len()) == count.saturating_add(usize::from(previous.is_none())),
    )]
    #[inline]
    pub fn insert(
        &mut self,
        key: Key,
        value: Value,
    ) -> Option<Value>
    {
        let chunks = owned(&mut self.chunks);
        let ChunkAt(at) = Self::chunk_of(chunks, &key);
        let Some(chunk) = chunks.get_mut(at)
        else {
            let mut entries = Vec::with_capacity(CHUNK);
            let first = key.clone();
            entries.push((key, value));
            chunks.push(Chunk {
                first,
                entries: Arc::new(entries),
            });
            self.len = 1;
            return None;
        };
        let entries = Arc::make_mut(&mut chunk.entries);
        let within = match entries.binary_search_by(|&(ref held, _)| held.cmp(&key)) {
            Ok(within) => {
                return entries
                    .get_mut(within)
                    .map(|entry| core::mem::replace(&mut entry.1, value));
            },
            Err(within) => within,
        };
        if within == 0 {
            chunk.first = key.clone();
        }
        entries.insert(within, (key, value));
        let upper = (entries.len() > CHUNK).then(|| entries.split_off(CHUNK >> 1));
        if let Some(upper) = upper
            && let Some(&(ref first, _)) = upper.first()
        {
            let first = first.clone();
            chunks.insert(at.saturating_add(1), Chunk {
                first,
                entries: Arc::new(upper),
            });
        }
        self.len = self.len.saturating_add(1);
        None
    }

    /// Take the entry of `key` out: its value, or `None` when the map does
    /// not hold it. A chunk left with fewer than [`SPARSE`] entries merges
    /// with the next chunk when the two fit one chunk.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the map holds no entry at `key`, and every other entry as it
    ///   was; one entry fewer when it held `key`.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`ChunkedMap`].
    /// - witness: `chunked::tests::a_chunked_map_answers_as_an_ordered_map_beside_its_clone`
    #[spec(
        captures: count = usize::from(self.len()),
        ensures: |taken| self.get(key).is_none()
            && usize::from(self.len()) == count.saturating_sub(usize::from(taken.is_some())),
    )]
    #[inline]
    pub fn remove(
        &mut self,
        key: &Key,
    ) -> Option<Value>
    {
        let Place { chunk: at, within } = self.held(key)?;
        let chunks = owned(&mut self.chunks);
        let chunk = chunks.get_mut(at)?;
        let entries = Arc::make_mut(&mut chunk.entries);
        let (_, value) = entries.remove(within);
        let left = entries.len();
        if let Some(&(ref first, _)) = entries.first() {
            chunk.first = first.clone();
        }
        if left == 0 {
            let _empty = chunks.remove(at);
        }
        else if left < SPARSE {
            Self::merge(chunks, ChunkAt(at));
        }
        self.len = self.len.saturating_sub(1);
        Some(value)
    }

    /// Merge the chunk at `at` with the next chunk when the two fit one chunk.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn merge(
        chunks: &mut Vec<Chunk<Key, Value>>,
        ChunkAt(at): ChunkAt,
    )
    {
        let next = at.saturating_add(1);
        let fits = match (chunks.get(at), chunks.get(next)) {
            (Some(chunk), Some(after)) => {
                chunk.entries.len().saturating_add(after.entries.len()) <= CHUNK
            },
            _ => false,
        };
        if !fits {
            return;
        }
        let after = chunks.remove(next);
        if let Some(chunk) = chunks.get_mut(at) {
            Arc::make_mut(&mut chunk.entries).extend(after.entries.iter().cloned());
        }
    }

    /// Keep the entries that `keep` holds, in their order. A chunk whose
    /// entries `keep` holds each stays shared, and a chunk that loses an
    /// entry is copied.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the map holds exactly its entries that `keep` holds.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`ChunkedMap`].
    /// - witness: `chunked::tests::a_chunked_map_answers_as_an_ordered_map_beside_its_clone`
    #[spec(
        captures: count = usize::from(self.len()),
        ensures: usize::from(self.len()) <= count,
    )]
    #[inline]
    pub fn retain<Keep>(
        &mut self,
        mut keep: Keep,
    ) where
        Keep: FnMut(&Key, &Value) -> bool,
    {
        let losing: Vec<usize> = self
            .chunks()
            .iter()
            .enumerate()
            .filter(|&(_, chunk)| {
                chunk
                    .entries
                    .iter()
                    .any(|&(ref key, ref value)| !keep(key, value))
            })
            .map(|(at, _)| at)
            .collect();
        if losing.is_empty() {
            return;
        }
        let chunks = owned(&mut self.chunks);
        // From the last, so a removed chunk moves no chunk still to read.
        for &at in losing.iter().rev() {
            let Some(chunk) = chunks.get_mut(at)
            else {
                continue;
            };
            let entries = Arc::make_mut(&mut chunk.entries);
            let before = entries.len();
            entries.retain(|&(ref key, ref value)| keep(key, value));
            self.len = self
                .len
                .saturating_sub(before.saturating_sub(entries.len()));
            if let Some(&(ref first, _)) = entries.first() {
                chunk.first = first.clone();
            }
            else {
                let _empty = chunks.remove(at);
            }
        }
    }

    /// Split the map at `key`: the entries at or above `key` leave it, and
    /// the map they make is the result. The chunks on either side of `key`
    /// stay shared; the chunk that `key` cuts is copied.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the map holds its entries below `key`, and the result those
    ///   at or above it.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`ChunkedMap`].
    /// - witness: `chunked::tests::a_chunked_map_answers_as_an_ordered_map_beside_its_clone`
    #[spec(
        captures: count = usize::from(self.len()),
        ensures: |upper| self.last_key_value().is_none_or(|(last, _)| last < key)
            && upper.first_key_value().is_none_or(|(first, _)| first >= key)
            && usize::from(self.len()).saturating_add(usize::from(upper.len())) == count,
    )]
    #[inline]
    #[must_use]
    pub fn split_off(
        &mut self,
        key: &Key,
    ) -> Self
    {
        let Place { chunk: at, within } = self.lower(Bound::Included(key));
        if at >= self.chunks().len() {
            return Self::new();
        }
        let chunks = owned(&mut self.chunks);
        let mut upper = chunks.split_off(at);
        if within > 0
            && let Some(cut) = upper.first_mut()
        {
            let entries = Arc::make_mut(&mut cut.entries);
            let above = entries.split_off(within);
            chunks.push(Chunk {
                first: cut.first.clone(),
                entries: Arc::new(core::mem::take(entries)),
            });
            if let Some(&(ref first, _)) = above.first() {
                cut.first = first.clone();
            }
            cut.entries = Arc::new(above);
        }
        let moved: usize = upper.iter().map(|chunk| chunk.entries.len()).sum();
        self.len = self.len.saturating_sub(moved);
        Self {
            chunks: Some(Arc::new(upper)),
            len: moved,
        }
    }
}

impl<Key: Ord + Clone, Item: Clone> ChunkedMap<Key, Vec<Item>>
{
    /// Keep the items of each value that `keep` holds, in their order, and
    /// the keys whose values keep an item. A chunk whose values `keep` holds
    /// whole stays shared.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each value holds exactly its items that `keep` holds, and the
    ///   map holds exactly the keys whose values hold an item after.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`ChunkedMap`].
    /// - witness: `chunked::tests::kept_items_answer_as_an_ordered_map_beside_its_clone`
    #[spec(
        captures: count = usize::from(self.len()),
        ensures: usize::from(self.len()) <= count,
    )]
    #[inline]
    pub fn retain_items<Keep>(
        &mut self,
        mut keep: Keep,
    ) where
        Keep: FnMut(&Item) -> bool,
    {
        let losing: Vec<Key> = self
            .iter()
            .filter(|&(_, items)| items.iter().any(|item| !keep(item)))
            .map(|(key, _)| key.clone())
            .collect();
        for key in losing {
            let emptied = self.get_mut(&key).is_some_and(|items| {
                items.retain(|item| keep(item));
                items.is_empty()
            });
            if emptied {
                let _empty = self.remove(&key);
            }
        }
    }
}

impl<Key: Ord + Clone, Value: Clone> FromIterator<(Key, Value)> for ChunkedMap<Key, Value>
{
    /// The map of `entries`: a later entry of one key replaces an earlier one.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from_iter<Entries>(iter: Entries) -> Self
    where
        Entries: IntoIterator<Item = (Key, Value)>,
    {
        let mut map = Self::new();
        for (key, value) in iter {
            let _previous = map.insert(key, value);
        }
        map
    }
}

#[cfg(test)]
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        primitive_signature,
        reason = "the tests key the map by small integers, as its ordered map oracle does"
    )
)]
mod tests
{
    use alloc::collections::BTreeMap;
    use alloc::vec::Vec;

    use proptest::prelude::*;
    use proptest::test_runner::TestCaseError;

    use super::CHUNK;
    use super::ChunkedMap;

    /// The keys a write reads lie below this.
    const KEYS: u16 = 400;

    /// One write of the map under test.
    #[derive(Clone, Debug)]
    enum Write
    {
        /// Hold a value at a key.
        Insert(u16, u32),
        /// Take a key out.
        Remove(u16),
        /// Keep the keys that a modulus leaves no remainder of.
        Retain(u16),
        /// Split at a key and keep the lower part.
        Split(u16),
    }

    /// A write over keys below [`KEYS`].
    ///
    /// # Specification
    /// trivial.
    fn write() -> impl Strategy<Value = Write>
    {
        prop_oneof![
            8 => (0 .. KEYS, any::<u32>()).prop_map(|(key, value)| Write::Insert(key, value)),
            4 => (0 .. KEYS).prop_map(Write::Remove),
            1 => (2_u16 .. 5).prop_map(Write::Retain),
            1 => (0 .. KEYS).prop_map(Write::Split),
        ]
    }

    /// Apply `write` to the map and to the ordered map it should answer as.
    ///
    /// # Specification
    /// trivial.
    fn apply(
        write: &Write,
        map: &mut ChunkedMap<u16, u32>,
        oracle: &mut BTreeMap<u16, u32>,
    )
    {
        match *write {
            Write::Insert(key, value) => {
                assert_eq!(map.insert(key, value), oracle.insert(key, value));
            },
            Write::Remove(key) => assert_eq!(map.remove(&key), oracle.remove(&key)),
            Write::Retain(modulus) => {
                map.retain(|&key, _| key.checked_rem(modulus) == Some(0));
                oracle.retain(|&key, _| key.checked_rem(modulus) == Some(0));
            },
            Write::Split(key) => {
                let upper = map.split_off(&key);
                let oracle_upper = oracle.split_off(&key);
                assert!(
                    upper
                        .iter()
                        .map(|(&key, &value)| (key, value))
                        .eq(oracle_upper)
                );
            },
        }
    }

    /// Refuse the case unless `map` answers each read as `oracle` does.
    ///
    /// # Specification
    /// trivial.
    fn agrees(
        map: &ChunkedMap<u16, u32>,
        oracle: &BTreeMap<u16, u32>,
    ) -> Result<(), TestCaseError>
    {
        prop_assert_eq!(usize::from(map.len()), oracle.len());
        prop_assert!(
            map.iter()
                .map(|(&key, &value)| (key, value))
                .eq(oracle.iter().map(|(&key, &value)| (key, value)))
        );
        prop_assert!(
            map.iter()
                .rev()
                .map(|(&key, _)| key)
                .eq(oracle.keys().rev().copied())
        );
        prop_assert_eq!(map.last_key_value(), oracle.last_key_value());
        for key in 0 .. KEYS {
            prop_assert_eq!(map.get(&key), oracle.get(&key));
            prop_assert!(
                map.range(key ..)
                    .map(|(&key, _)| key)
                    .eq(oracle.range(key ..).map(|(&key, _)| key))
            );
            prop_assert!(
                map.range(.. key)
                    .rev()
                    .map(|(&key, _)| key)
                    .eq(oracle.range(.. key).rev().map(|(&key, _)| key))
            );
            prop_assert!(
                map.range(key ..= key.saturating_add(70))
                    .map(|(&key, _)| key)
                    .eq(oracle
                        .range(key ..= key.saturating_add(70))
                        .map(|(&key, _)| key))
            );
        }
        Ok(())
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(64))]

        /// A chunked map answers each read as an ordered map does after each
        /// write, and a clone taken between writes answers as it did.
        #[test]
        fn a_chunked_map_answers_as_an_ordered_map_beside_its_clone(
            writes in proptest::collection::vec(write(), 0 .. 600),
            cut in 0_usize .. 600,
        )
        {
            let mut map = ChunkedMap::new();
            let mut oracle = BTreeMap::new();
            let mut clone = None;
            for (at, write) in writes.iter().enumerate() {
                if at == cut {
                    clone = Some((map.clone(), oracle.clone()));
                }
                apply(write, &mut map, &mut oracle);
            }
            agrees(&map, &oracle)?;
            if let Some((clone, oracle)) = clone {
                agrees(&clone, &oracle)?;
            }
        }
    }

    /// A write to one entry of a map that a clone shares copies the chunk that
    /// holds the entry, and every other chunk stays shared.
    #[test]
    fn a_write_to_one_entry_copies_its_chunk_alone()
    {
        let length = u32::try_from(CHUNK * 8).unwrap_or(u32::MAX);
        let mut map: ChunkedMap<u32, u32> = (0 .. length).map(|key| (key, key)).collect();
        let clone = map.clone();
        if let Some(value) = map.get_mut(&3) {
            *value = 7;
        }
        let _absent = map.remove(&(length + 1));
        let shared: Vec<bool> = map
            .chunks()
            .iter()
            .zip(clone.chunks())
            .map(|(mine, theirs)| alloc::sync::Arc::ptr_eq(&mine.entries, &theirs.entries))
            .collect();
        assert_eq!(shared.iter().filter(|&&shared| !shared).count(), 1);
        assert_eq!(shared.first(), Some(&false));
        assert_eq!(clone.get(&3), Some(&3));
        assert_eq!(map.get(&3), Some(&7));
    }

    /// Keeping the items of each value drops the items that the test refuses
    /// and the keys left with none, as an ordered map does, and a clone taken
    /// before answers as it did.
    #[test]
    fn kept_items_answer_as_an_ordered_map_beside_its_clone()
    {
        let items = |key: u32| alloc::vec![key, key.saturating_add(1), key.saturating_mul(3)];
        let mut map: ChunkedMap<u32, Vec<u32>> = (0 .. 600).map(|key| (key, items(key))).collect();
        let mut oracle: BTreeMap<u32, Vec<u32>> = (0 .. 600).map(|key| (key, items(key))).collect();
        let clone = map.clone();
        let keep = |item: &u32| item.checked_rem(4) != Some(0) || *item > 1_000;
        map.retain_items(keep);
        oracle.retain(|_, held| {
            held.retain(keep);
            !held.is_empty()
        });
        assert!(map.iter().eq(oracle.iter()));
        assert_eq!(usize::from(map.len()), oracle.len());
        assert!(
            clone
                .iter()
                .map(|(&key, held)| (key, held.clone()))
                .eq((0 .. 600).map(|key| (key, items(key))))
        );
    }
}
