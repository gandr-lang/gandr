//! The stage arena's descriptor lookup: an open-addressed, linearly probed
//! table from a descriptor's hash to its position in the arena's dense
//! vector.
//!
//! The table stores positions and 32-bit hashes, never descriptors: the dense
//! vector owns them. A hash match is confirmed by comparing the descriptor
//! itself, so a collision costs a comparison and never an identity, and a
//! clone of the table is one slice copy.

use alloc::vec::Vec;
use core::hash::Hash;
use core::hash::Hasher;

use anodized::spec;

/// The position a vacant slot carries; no descriptor sits there.
const VACANT: u32 = u32::MAX;

/// The capacity a first insertion allocates.
const MINIMUM: usize = 16;

/// Odd multiplier of the word fold: the 64-bit golden-ratio constant.
const FOLD: u64 = 0x9e37_79b9_7f4a_7c15;

/// A descriptor's 32-bit lookup hash.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct DescriptorHash(u32);

/// A slot coordinate of one table.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SlotIndex(usize);

/// One slot: a dense position and the hash of the descriptor stored there.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Slot
{
    /// The descriptor's hash; meaningless while vacant.
    hash: DescriptorHash,
    /// The descriptor's position, or [`VACANT`].
    position: u32,
}

impl Slot
{
    /// The slot holding nothing.
    const EMPTY: Self = Self {
        hash: DescriptorHash(0),
        position: VACANT,
    };
}

/// An unkeyed word-folding hasher over a descriptor's derived [`Hash`].
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

/// The lookup hash of a descriptor: both halves of its folded hash, a
/// function of the descriptor's derived hash alone.
///
/// # Specification
/// trivial.
#[inline]
pub(super) fn hash_of<T>(value: &T) -> DescriptorHash
where
    T: Hash,
{
    let mut fold = Fold::default();
    value.hash(&mut fold);
    let bytes = fold.finish().to_le_bytes();
    let low = bytes.first_chunk::<4>().copied().unwrap_or_default();
    let high = bytes.last_chunk::<4>().copied().unwrap_or_default();
    DescriptorHash(u32::from_le_bytes(low) ^ u32::from_le_bytes(high))
}

/// Where a probe for one descriptor ended.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Probe
{
    /// An equal descriptor is stored at this dense position.
    Found(usize),
    /// No equal descriptor is recorded; this vacant slot is the one an
    /// insertion would fill.
    Vacant(SlotIndex),
}

/// The position a slot cannot record: at least `u32::MAX`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct Full;

/// Open-addressed, linearly probed lookup from a descriptor to its dense
/// position.
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
/// - witness: `stage::lookup::tests::growth_keeps_every_position`
/// - witness: `stage::lookup::tests::colliding_hashes_compare_descriptors`
/// - witness: `stage::lookup::tests::the_last_position_is_refused`
#[derive(Clone, Debug, Default)]
pub(super) struct Lookup
{
    /// The slots, vacant where the position is [`VACANT`].
    slots: Vec<Slot>,
    /// The number of occupied slots.
    len: usize,
}

impl Lookup
{
    /// The home slot of `hash`; slot zero of the empty table.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn home(
        &self,
        hash: DescriptorHash,
    ) -> SlotIndex
    {
        let mask = self.slots.len().saturating_sub(1);
        SlotIndex(usize::try_from(hash.0).unwrap_or(usize::MAX) & mask)
    }

    /// The slot after `slot`, wrapping at the capacity.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn next(
        &self,
        slot: SlotIndex,
    ) -> SlotIndex
    {
        SlotIndex(slot.0.wrapping_add(1) & self.slots.len().saturating_sub(1))
    }

    /// Probe for `key`, whose hash is `hash`, among `entries`.
    ///
    /// # Specification
    /// - requires: every recorded position indexes `entries`, recorded under
    ///   its entry's hash.
    /// - ensures: `Found(position)` exactly when `entries[position] == *key` is
    ///   recorded; otherwise `Vacant(slot)` names the first vacant slot of
    ///   `key`'s probe sequence, or slot zero of the empty table.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — colliding hashes over distinct descriptors and
    ///   lookups after growth distinguish a probe that trusts the hash and one
    ///   that stops early.
    /// - witness: `stage::lookup::tests::colliding_hashes_compare_descriptors`
    /// - witness: `stage::lookup::tests::growth_keeps_every_position`
    #[inline]
    #[spec(ensures: |ret| match ret {
        Probe::Found(position) => entries.get(position) == Some(key),
        Probe::Vacant(slot) => self.slots.get(slot.0).is_none_or(|stored| stored.position == VACANT),
    })]
    pub(super) fn probe<T>(
        &self,
        hash: DescriptorHash,
        entries: &[T],
        key: &T,
    ) -> Probe
    where
        T: Eq,
    {
        let mut slot = self.home(hash);
        while let Some(stored) = self.slots.get(slot.0) {
            if stored.position == VACANT {
                return Probe::Vacant(slot);
            }
            if stored.hash == hash {
                let position = usize::try_from(stored.position).unwrap_or(usize::MAX);
                if entries.get(position) == Some(key) {
                    return Probe::Found(position);
                }
            }
            slot = self.next(slot);
        }
        Probe::Vacant(slot)
    }

    /// Record the next position of `entries`, `entries.len()`, for a
    /// descriptor of hash `hash` that a preceding [`probe`](Self::probe)
    /// found vacant at `slot`.
    ///
    /// # Specification
    /// - requires: no slot records an equal descriptor; `slot` is the vacant
    ///   slot that probe returned with no insertion since; the caller pushes
    ///   the descriptor onto `entries` next.
    /// - ensures: one more position is recorded, and once the descriptor is
    ///   pushed a probe for it returns `Found(entries.len())` as it stood here;
    ///   at most half the slots stay occupied.
    /// - fails: [`Full`] when that position does not fit a slot, leaving the
    ///   table unchanged.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`Full`] at the 32-bit position bound.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — growth across several doublings and the position
    ///   bound distinguish a lost entry, an overfull table and a truncated
    ///   position.
    /// - witness: `stage::lookup::tests::growth_keeps_every_position`
    /// - witness: `stage::lookup::tests::the_last_position_is_refused`
    #[inline]
    #[spec(captures: before = self.len, ensures: |ret| match ret {
        Ok(()) => self.len == before.saturating_add(1)
            && self.len.saturating_mul(2) <= self.slots.len(),
        Err(Full) => self.len == before,
    })]
    pub(super) fn insert<T>(
        &mut self,
        slot: SlotIndex,
        hash: DescriptorHash,
        entries: &[T],
    ) -> Result<(), Full>
    {
        let position = u32::try_from(entries.len()).map_err(|_overflow| Full)?;
        if position == VACANT {
            return Err(Full);
        }
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
        Ok(())
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
}

#[cfg(test)]
mod tests
{
    use super::*;

    /// A test descriptor.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
    struct Key(u64);

    /// Find `key` among `entries`, or record it at the next position.
    ///
    /// # Specification
    /// trivial.
    fn intern(
        lookup: &mut Lookup,
        entries: &mut Vec<Key>,
        hash: DescriptorHash,
        key: Key,
    ) -> Probe
    {
        match lookup.probe(hash, entries, &key) {
            | Probe::Found(position) => Probe::Found(position),
            | Probe::Vacant(slot) => {
                let position = entries.len();
                lookup.insert(slot, hash, entries).unwrap();
                entries.push(key);
                Probe::Found(position)
            },
        }
    }

    #[test]
    fn growth_keeps_every_position()
    {
        let mut lookup = Lookup::default();
        let mut entries = Vec::new();
        for key in (0 .. 5_000).map(Key) {
            let expected = Probe::Found(entries.len());
            assert_eq!(
                intern(&mut lookup, &mut entries, hash_of(&key), key),
                expected
            );
        }
        assert_eq!(lookup.len, 5_000);
        assert!(
            lookup.slots.len().is_power_of_two(),
            "the capacity stays a power of two"
        );
        assert!(
            lookup.len.checked_mul(2).unwrap() <= lookup.slots.len(),
            "the table stays at most half full"
        );
        let cloned = lookup.clone();
        for (position, key) in entries.iter().enumerate() {
            assert_eq!(
                lookup.probe(hash_of(key), &entries, key),
                Probe::Found(position)
            );
            assert_eq!(
                cloned.probe(hash_of(key), &entries, key),
                Probe::Found(position)
            );
        }
        let absent = Key(5_000);
        assert!(matches!(
            lookup.probe(hash_of(&absent), &entries, &absent),
            Probe::Vacant(_)
        ));
    }

    #[test]
    fn colliding_hashes_compare_descriptors()
    {
        let mut lookup = Lookup::default();
        let mut entries = Vec::new();
        let shared = DescriptorHash(7);
        let found: Vec<Probe> = (0 .. 40)
            .map(|key| intern(&mut lookup, &mut entries, shared, Key(key)))
            .collect();
        assert_eq!(found, (0 .. 40).map(Probe::Found).collect::<Vec<_>>());
        for (position, key) in entries.iter().enumerate() {
            assert_eq!(lookup.probe(shared, &entries, key), Probe::Found(position));
        }
        let stranger = Key(40);
        assert!(matches!(
            lookup.probe(shared, &entries, &stranger),
            Probe::Vacant(_)
        ));
    }

    #[test]
    fn the_last_position_is_refused()
    {
        let mut lookup = Lookup::default();
        let hash = DescriptorHash(3);
        let full = alloc::vec![(); usize::try_from(VACANT).unwrap()];
        let Probe::Vacant(slot) = lookup.probe(hash, &full, &())
        else {
            panic!("an empty table records nothing");
        };
        assert_eq!(lookup.insert(slot, hash, &full), Err(Full));
        assert_eq!(lookup.len, 0);
        assert_eq!(lookup.insert(slot, hash, &full[1 ..]), Ok(()));
        assert_eq!(lookup.len, 1);
    }
}
