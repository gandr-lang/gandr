//! The kernel's one hash index: an open-addressed, linearly probed table from
//! a key's hash to its position in a dense vector the consumer owns, kept at
//! most half full.
//!
//! The table stores positions and 32-bit hashes, never keys: the consumer's
//! vector owns them, and the consumer's own comparison decides. A hash match
//! is confirmed by that comparison, so a collision costs a comparison and
//! never an identity, and a clone of the table is one slice copy. The hash is
//! an unkeyed fold of the key's derived `Hash`, a function of the key alone,
//! so a run files and probes alike on every host.
//!
//! The check memo, the content table's interning, the binder-reach caches,
//! the rewrite walk's local answers and the staging arena's descriptor lookup
//! all file on this one index.
//!
//! A producer that chooses colliding keys can lengthen probe sequences toward
//! linear time, though it cannot merge two keys.

use alloc::vec::Vec;
use core::hash::Hash;
use core::hash::Hasher;

use anodized::spec;

/// The capacity a first insertion allocates.
const MINIMUM: usize = 16;

/// Odd multiplier of the word fold: the 64-bit golden-ratio constant.
const FOLD: u64 = 0x9e37_79b9_7f4a_7c15;

/// A key's 32-bit table hash.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct TableHash(u32);

impl From<u32> for TableHash
{
    /// The hash `hash`, chosen rather than computed: a fixture forcing keys
    /// under one hash.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(hash: u32) -> Self
    {
        Self(hash)
    }
}

impl TableHash
{
    /// The table hash of `key`: both halves of its folded hash, a function of
    /// the key's derived hash alone.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn of<Key>(key: &Key) -> Self
    where
        Key: Hash + ?Sized,
    {
        let mut fold = Fold::default();
        key.hash(&mut fold);
        let bytes = fold.finish().to_le_bytes();
        let low = bytes.first_chunk::<4>().copied().unwrap_or_default();
        let high = bytes.last_chunk::<4>().copied().unwrap_or_default();
        Self(u32::from_le_bytes(low) ^ u32::from_le_bytes(high))
    }
}

/// A slot coordinate of one table: where a probe found room.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct TableSlot(usize);

/// A dense position among the entries a table files, below `u32::MAX`, the
/// value a vacant slot carries instead.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TablePosition(u32);

/// The position a vacant slot carries; no entry sits there.
const VACANT: TablePosition = TablePosition(u32::MAX);

impl TryFrom<usize> for TablePosition
{
    type Error = TableFull;

    /// The position `position`, or [`TableFull`] at or past `u32::MAX`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn try_from(position: usize) -> Result<Self, TableFull>
    {
        u32::try_from(position)
            .ok()
            .filter(|&position| position != VACANT.0)
            .map_or(Err(TableFull), |position| Ok(Self(position)))
    }
}

impl From<TablePosition> for usize
{
    /// The vector index `position` names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(position: TablePosition) -> Self
    {
        Self::try_from(position.0).unwrap_or(Self::MAX)
    }
}

/// A position no slot can record: at least `u32::MAX`.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct TableFull;

/// One slot: a dense position and the hash of the key filed there.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Slot
{
    /// The key's hash; meaningless while vacant.
    hash: TableHash,
    /// The key's position, or [`VACANT`].
    position: TablePosition,
}

impl Slot
{
    /// The slot holding nothing.
    const EMPTY: Self = Self {
        hash: TableHash(0),
        position: VACANT,
    };
}

/// An unkeyed word-folding hasher over a key's derived [`Hash`].
#[repr(transparent)]
#[derive(Debug, Default)]
struct Fold(u64);

impl Hasher for Fold
{
    /// The folded state through a full-avalanche finalizer.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn finish(&self) -> u64
    {
        let mut state = self.0;
        state ^= state.wrapping_shr(33);
        state = state.wrapping_mul(0xff51_afd7_ed55_8ccd);
        state ^= state.wrapping_shr(33);
        state = state.wrapping_mul(0xc4ce_b9fe_1a85_ec53);
        state ^ state.wrapping_shr(33)
    }

    /// Fold bytes eight at a time, the last word zero-padded.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn write(
        &mut self,
        bytes: &[u8],
    )
    {
        let mut chunks = bytes.chunks_exact(8);
        for chunk in &mut chunks {
            let mut word = [0_u8; 8];
            word.copy_from_slice(chunk);
            self.write_u64(u64::from_le_bytes(word));
        }
        let rest = chunks.remainder();
        if !rest.is_empty() {
            let mut word = [0_u8; 8];
            for (target, byte) in word.iter_mut().zip(rest) {
                *target = *byte;
            }
            self.write_u64(u64::from_le_bytes(word));
        }
    }

    /// Fold one byte.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn write_u8(
        &mut self,
        i: u8,
    )
    {
        self.write_u64(u64::from(i));
    }

    /// Fold one 32-bit word.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn write_u32(
        &mut self,
        i: u32,
    )
    {
        self.write_u64(u64::from(i));
    }

    /// Fold one 64-bit word into the state.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn write_u64(
        &mut self,
        i: u64,
    )
    {
        self.0 = (self.0.rotate_left(5) ^ i).wrapping_mul(FOLD);
    }

    /// Fold one pointer-sized word; a host wider than 64 bits folds the
    /// saturated value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn write_usize(
        &mut self,
        i: usize,
    )
    {
        self.write_u64(u64::try_from(i).unwrap_or(u64::MAX));
    }

    /// Fold one signed pointer-sized word, as a derived enum hash writes its
    /// discriminant.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn write_isize(
        &mut self,
        i: isize,
    )
    {
        self.write_usize(i.cast_unsigned());
    }
}

/// Where a probe for one key ended.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Probe
{
    /// An entry the consumer's comparison accepts is filed at this position.
    Found(TablePosition),
    /// No accepted entry is filed; this vacant slot is the one an insertion
    /// would fill.
    Vacant(TableSlot),
}

/// Open-addressed, linearly probed index from a key's hash to the dense
/// positions filed under it.
///
/// # Specification
/// - ensures: the capacity is zero or a power of two, and at most half the
///   slots are occupied, so every probe sequence reaches a vacant slot.
/// - panics: none.
/// - executable: none — this data declaration has no callable boundary; probing
///   and insertion carry the laws.
///
/// # Adequacy
/// - hypothesis: L3 — growth across several doublings, colliding hashes and the
///   position bound distinguish a lost entry, a hash taken for identity and a
///   truncated position.
/// - witness: `table::tests::growth_keeps_every_position`
/// - witness: `table::tests::colliding_hashes_compare_keys`
/// - witness: `table::tests::the_last_position_is_refused`
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct HashIndex
{
    /// The slots, vacant where the position is [`VACANT`].
    slots: Vec<Slot>,
    /// The number of occupied slots.
    len: usize,
}

impl HashIndex
{
    /// An empty index; it allocates on its first insertion.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new() -> Self
    {
        Self {
            slots: Vec::new(),
            len: 0,
        }
    }

    /// The home slot of `hash`; slot zero of the empty table.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn home(
        &self,
        hash: TableHash,
    ) -> TableSlot
    {
        let mask = self.slots.len().saturating_sub(1);
        TableSlot(usize::try_from(hash.0).unwrap_or(usize::MAX) & mask)
    }

    /// The slot after `slot`, wrapping at the capacity.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn next(
        &self,
        slot: TableSlot,
    ) -> TableSlot
    {
        TableSlot(slot.0.wrapping_add(1) & self.slots.len().saturating_sub(1))
    }

    /// Probe for a key whose hash is `hash`, accepting the first position
    /// filed under that hash that `accepts` answers for.
    ///
    /// # Specification
    /// - requires: every filed position was filed under its key's hash, and
    ///   `accepts` answers for at most one position filed under `hash`.
    /// - ensures: `Found(position)` names a position filed under `hash` that
    ///   `accepts` answers for; otherwise `Vacant(slot)` names the first vacant
    ///   slot of `hash`'s probe sequence, or slot zero of the empty table.
    ///   `accepts` is asked only about positions filed under `hash`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — colliding hashes over distinct keys and lookups after
    ///   growth distinguish a probe that trusts the hash and one that stops
    ///   early.
    /// - witness: `table::tests::colliding_hashes_compare_keys`
    /// - witness: `table::tests::growth_keeps_every_position`
    #[inline]
    #[spec(ensures: |ret| match ret {
        Probe::Found(position) => accepts(position),
        Probe::Vacant(slot) => self.slots.get(slot.0).is_none_or(|stored| stored.position == VACANT),
    })]
    pub fn probe<Accepts>(
        &self,
        hash: TableHash,
        accepts: Accepts,
    ) -> Probe
    where
        Accepts: Fn(TablePosition) -> bool,
    {
        let mut slot = self.home(hash);
        while let Some(stored) = self.slots.get(slot.0) {
            if stored.position == VACANT {
                return Probe::Vacant(slot);
            }
            if stored.hash == hash && accepts(stored.position) {
                return Probe::Found(stored.position);
            }
            slot = self.next(slot);
        }
        Probe::Vacant(slot)
    }

    /// Every position filed under `hash`, in the order a probe for `hash`
    /// meets them.
    ///
    /// # Specification
    /// - requires: every filed position was filed under its key's hash.
    /// - ensures: each position filed under `hash` once, and none filed under
    ///   another hash; the walk stops at the first vacant slot, which every
    ///   probe sequence reaches, and never passes the capacity.
    /// - provides: the candidates a consumer decides among when more than one
    ///   key filed under one hash may answer it.
    /// - panics: none.
    /// - executable: none — the result is a lazy iterator borrowing the index,
    ///   which a predicate could only check by consuming it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — keys colliding on one hash beside a key under
    ///   another, walked after growth, distinguish a walk that stops at the
    ///   first match, one that trusts the home slot alone and one that leaks a
    ///   neighbour.
    /// - witness: `table::tests::filed_walks_every_position_under_one_hash`
    #[inline]
    pub fn filed(
        &self,
        hash: TableHash,
    ) -> impl Iterator<Item = TablePosition>
    {
        let mut slot = self.home(hash);
        let mut remaining = self.slots.len();
        core::iter::from_fn(move || {
            while remaining > 0 {
                remaining = remaining.saturating_sub(1);
                let stored = self.slots.get(slot.0)?;
                if stored.position == VACANT {
                    remaining = 0;
                    return None;
                }
                slot = self.next(slot);
                if stored.hash == hash {
                    return Some(stored.position);
                }
            }
            None
        })
    }

    /// File `position` under `hash` at `slot`, which a preceding
    /// [`probe`](Self::probe) for `hash` found vacant.
    ///
    /// # Specification
    /// - requires: no filed position's key equals the one `position` holds;
    ///   `slot` is the vacant slot that probe returned with no insertion since.
    /// - ensures: one more position is filed, and a probe under `hash` whose
    ///   comparison accepts `position` finds it; at most half the slots stay
    ///   occupied.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — growth across several doublings distinguishes a lost
    ///   entry and an overfull table.
    /// - witness: `table::tests::growth_keeps_every_position`
    #[inline]
    #[spec(captures: before = self.len, ensures: self.len == before.saturating_add(1)
        && self.len.saturating_mul(2) <= self.slots.len())]
    pub fn insert(
        &mut self,
        slot: TableSlot,
        hash: TableHash,
        position: TablePosition,
    )
    {
        let len = self.len.saturating_add(1);
        let entry = Slot { hash, position };
        if len.saturating_mul(2) > self.slots.len() {
            self.grow();
            self.place(entry);
        }
        else if let Some(target) = self.slots.get_mut(slot.0) {
            *target = entry;
        }
        self.len = len;
    }

    /// Store `entry` in the first vacant slot of its probe sequence.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn place(
        &mut self,
        entry: Slot,
    )
    {
        let mut slot = self.home(entry.hash);
        loop {
            let next = self.next(slot);
            let Some(target) = self.slots.get_mut(slot.0)
            else {
                return;
            };
            if target.position == VACANT {
                *target = entry;
                return;
            }
            slot = next;
        }
    }

    /// Double the table, rehashing from the stored hashes alone.
    ///
    /// # Specification
    /// trivial.
    #[inline(never)]
    fn grow(&mut self)
    {
        let capacity = self.slots.len().saturating_mul(2).max(MINIMUM);
        let old = core::mem::replace(&mut self.slots, alloc::vec![Slot::EMPTY; capacity]);
        for entry in old {
            if entry.position != VACANT {
                self.place(entry);
            }
        }
    }

    /// Forget `position`, filed under `hash`, closing its probe gap by
    /// shifting later entries of the same run backward.
    ///
    /// # Specification
    /// - requires: when filed, `position` was filed under `hash`.
    /// - ensures: no slot records `position`; one fewer entry is counted when
    ///   one did; every other filed position stays where its probe sequence
    ///   reaches it, so a probe for its key still finds it.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — removing the head, the middle and the wrapped tail of
    ///   one colliding run, then probing every survivor, distinguishes a hole
    ///   left open, an entry shifted past its home and a removal that forgets
    ///   the wrong position. Linear probing keeps every record in the run from
    ///   its hash's home slot to the first vacant slot, so under the
    ///   requirement the predicate reads that run alone, before and after.
    /// - witness: `table::tests::removal_keeps_every_other_position`
    #[inline]
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "the check walks only the probe run from `hash`'s home slot to its first vacant slot, the run the body searches and shifts"
        )
    )]
    #[spec(captures: [before = self.len, recorded = self.slots.iter().chain(&self.slots).skip(self.home(hash).0)
            .take_while(|slot| slot.position != VACANT)
            .any(|slot| slot.position == position)],
        ensures: !self.slots.iter().chain(&self.slots).skip(self.home(hash).0)
                .take_while(|slot| slot.position != VACANT)
                .any(|slot| slot.position == position)
            && self.len == if recorded { before.saturating_sub(1) } else { before })]
    pub fn remove(
        &mut self,
        hash: TableHash,
        position: TablePosition,
    )
    {
        let mask = self.slots.len().saturating_sub(1);
        let mut hole = self.home(hash);
        loop {
            match self.slots.get(hole.0) {
                Some(stored) if stored.position == position => break,
                Some(stored) if stored.position != VACANT => hole = self.next(hole),
                Some(_) | None => return,
            }
        }
        let mut next = self.next(hole);
        while let Some(stored) = self.slots.get(next.0).copied() {
            if stored.position == VACANT {
                break;
            }
            // `stored` may fill the hole only if the hole lies on its probe
            // path: no farther from its home than its current slot.
            let home = self.home(stored.hash);
            if next.0.wrapping_sub(home.0) & mask >= next.0.wrapping_sub(hole.0) & mask {
                if let Some(target) = self.slots.get_mut(hole.0) {
                    *target = stored;
                }
                hole = next;
            }
            next = self.next(next);
        }
        if let Some(target) = self.slots.get_mut(hole.0) {
            *target = Slot::EMPTY;
        }
        self.len = self.len.saturating_sub(1);
    }
}

#[cfg(test)]
mod tests
{
    use alloc::vec::Vec;

    use super::HashIndex;
    use super::MINIMUM;
    use super::Probe;
    use super::TableFull;
    use super::TableHash;
    use super::TablePosition;
    use super::VACANT;

    /// A test key.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
    struct Key(u64);

    /// Find `key` among `entries`, or file it at the next position.
    ///
    /// # Specification
    /// trivial.
    fn intern(
        index: &mut HashIndex,
        entries: &mut Vec<Key>,
        hash: TableHash,
        key: Key,
    ) -> Probe
    {
        match index.probe(hash, |position| {
            entries.get(usize::from(position)) == Some(&key)
        }) {
            Probe::Found(position) => Probe::Found(position),
            Probe::Vacant(slot) => {
                let position = TablePosition::try_from(entries.len()).unwrap();
                index.insert(slot, hash, position);
                entries.push(key);
                Probe::Found(position)
            },
        }
    }

    /// The probe for `key` under `hash`.
    ///
    /// # Specification
    /// trivial.
    fn find(
        index: &HashIndex,
        entries: &[Key],
        hash: TableHash,
        key: Key,
    ) -> Probe
    {
        index.probe(hash, |position| {
            entries.get(usize::from(position)) == Some(&key)
        })
    }

    /// The position of the `ordinal`th entry, however the test counts it.
    ///
    /// # Specification
    /// trivial.
    fn at<Ordinal>(ordinal: Ordinal) -> Probe
    where
        TablePosition: TryFrom<Ordinal, Error = TableFull>,
    {
        Probe::Found(TablePosition::try_from(ordinal).unwrap())
    }

    #[test]
    fn growth_keeps_every_position()
    {
        let mut index = HashIndex::new();
        let mut entries = Vec::new();
        for key in (0 .. 5_000).map(Key) {
            let expected = at(entries.len());
            assert_eq!(
                intern(&mut index, &mut entries, TableHash::of(&key), key),
                expected
            );
        }
        assert_eq!(index.len, 5_000);
        assert!(
            index.slots.len().is_power_of_two(),
            "the capacity stays a power of two"
        );
        assert!(
            index.len.checked_mul(2).unwrap() <= index.slots.len(),
            "the table stays at most half full"
        );
        let cloned = index.clone();
        for (position, key) in entries.iter().enumerate() {
            assert_eq!(
                find(&index, &entries, TableHash::of(key), *key),
                at(position)
            );
            assert_eq!(
                find(&cloned, &entries, TableHash::of(key), *key),
                at(position)
            );
        }
        let absent = Key(5_000);
        assert!(matches!(
            find(&index, &entries, TableHash::of(&absent), absent),
            Probe::Vacant(_)
        ));
    }

    #[test]
    fn colliding_hashes_compare_keys()
    {
        let mut index = HashIndex::new();
        let mut entries = Vec::new();
        let shared = TableHash::from(7_u32);
        let found: Vec<Probe> = (0 .. 40)
            .map(|key| intern(&mut index, &mut entries, shared, Key(key)))
            .collect();
        assert_eq!(found, (0 .. 40).map(at).collect::<Vec<_>>());
        for (position, key) in entries.iter().enumerate() {
            assert_eq!(find(&index, &entries, shared, *key), at(position));
        }
        assert!(matches!(
            find(&index, &entries, shared, Key(40)),
            Probe::Vacant(_)
        ));
    }

    #[test]
    fn filed_walks_every_position_under_one_hash()
    {
        let mut index = HashIndex::new();
        let mut entries = Vec::new();
        let shared = TableHash::from(7_u32);
        let neighbour = TableHash::from(8_u32);
        let mut under_shared = Vec::new();
        for key in 0 .. 40 {
            let hash = if key % 4 == 3 { neighbour } else { shared };
            let Probe::Found(position) = intern(&mut index, &mut entries, hash, Key(key))
            else {
                panic!("interning files every key");
            };
            if hash == shared {
                under_shared.push(position);
            }
        }
        let mut walked: Vec<TablePosition> = index.filed(shared).collect();
        walked.sort_unstable();
        assert_eq!(
            walked, under_shared,
            "every position filed under the shared hash, each once, across growth, and none of its \
             neighbour's interleaved run"
        );
        assert_eq!(
            index.filed(TableHash::from(9_u32)).count(),
            0,
            "a hash nothing was filed under walks nothing"
        );
        assert_eq!(
            HashIndex::new().filed(shared).count(),
            0,
            "nor does the empty table"
        );
    }

    #[test]
    fn the_last_position_is_refused()
    {
        let last = usize::try_from(VACANT.0).unwrap();
        assert_eq!(TablePosition::try_from(last), Err(TableFull));
        assert_eq!(TablePosition::try_from(usize::MAX), Err(TableFull));
        let below = TablePosition::try_from(last.checked_sub(1).unwrap()).unwrap();
        assert_eq!(usize::from(below), last.checked_sub(1).unwrap());
        let mut index = HashIndex::new();
        let hash = TableHash::from(3_u32);
        let Probe::Vacant(slot) = index.probe(hash, |_position| false)
        else {
            panic!("an empty table files nothing");
        };
        index.insert(slot, hash, below);
        assert_eq!(index.len, 1);
        assert_eq!(
            index.probe(hash, |position| position == below),
            Probe::Found(below)
        );
    }

    #[test]
    fn removal_keeps_every_other_position()
    {
        let mut index = HashIndex::new();
        let mut entries = Vec::new();
        // One run of colliding entries homed in the table's last slot, so the
        // run wraps past slot zero, then a few entries of their own.
        let last = TableHash::from(u32::try_from(MINIMUM).unwrap().checked_sub(1).unwrap());
        let hashes: Vec<TableHash> = core::iter::repeat_n(last, 6)
            .chain((0 .. 2_u32).map(TableHash::from))
            .collect();
        for (key, hash) in hashes.iter().enumerate() {
            let key = Key(u64::try_from(key).unwrap());
            intern(&mut index, &mut entries, *hash, key);
        }
        assert_eq!(index.slots.len(), MINIMUM);
        let mut live: Vec<usize> = (0 .. hashes.len()).collect();
        for removed in [0_usize, 3, 5, 6] {
            index.remove(hashes[removed], TablePosition::try_from(removed).unwrap());
            live.retain(|position| *position != removed);
            assert_eq!(index.len, live.len());
            for &position in &live {
                assert_eq!(
                    find(&index, &entries, hashes[position], entries[position]),
                    at(position),
                    "position {position} survives the removal of {removed}"
                );
            }
            assert!(matches!(
                find(&index, &entries, hashes[removed], entries[removed]),
                Probe::Vacant(_)
            ));
        }
        index.remove(hashes[3], TablePosition::try_from(3_usize).unwrap());
        assert_eq!(
            index.len,
            live.len(),
            "removing a forgotten position is a no-op"
        );
    }
}
