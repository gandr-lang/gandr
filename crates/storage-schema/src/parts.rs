//! Parts: stable keys minted by a monotone counter, live parts as a bit set.
//!
//! A [`PartKey`] is minted once per table by a counter that only grows, and a
//! key is never reused, renumbered or moved: deleting a part clears its bit
//! and leaves every other key where it was. This is the marked-as-deleted part
//! model, and it is what lets a part's key be a record-plane key whose
//! identity survives every edit that does not touch that part.

use alloc::vec::Vec;
use core::fmt;

use anodized::spec;

/// The width of one bit-set word, as a shift.
const WORD_SHIFT: u32 = 6_u32;

/// The mask selecting a bit within one word.
const BIT_MASK: u64 = 0x3f_u64;

/// A part's stable key within its table.
///
/// Keys are minted in increasing order from [`PartKey::FIRST`]; the counter's
/// next value is committed with the table, so a reopened store never mints a
/// key it has minted before.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct PartKey(u64);

impl PartKey
{
    /// The first key a table mints.
    pub const FIRST: Self = Self(0_u64);

    /// The key after this one.
    ///
    /// # Specification
    /// - ensures: on success the key is exactly one greater.
    /// - fails: [`Exhausted`] at the largest key.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Exhausted`]: no key follows the largest.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — successive mints observe consecutive keys from zero,
    ///   and a set whose counter stands at the largest key refuses the next
    ///   mint.
    /// - witness: `parts::tests::mints_are_consecutive_and_the_last_key_is_refused`
    #[inline]
    #[spec(ensures: |ret| ret.map_or(self.0 == u64::MAX, |next| next.0.checked_sub(1_u64) == Some(self.0)))]
    pub(crate) fn next(self) -> Result<Self, Exhausted>
    {
        self.0.checked_add(1_u64).map(Self).ok_or(Exhausted)
    }

    /// The bit-set word and bit this key occupies, when addressable.
    ///
    /// # Specification
    /// - ensures: on success the word is the key over 64 and the mask has the
    ///   bit of the key modulo 64.
    /// - fails: [`Unaddressable`] when the word does not fit a `usize`.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Unaddressable`]: the key is beyond what this target can index.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — keys 63, 64 and 65 occupy the last bit of word zero
    ///   and the first two of word one, observed through liveness after minting
    ///   66 parts and removing 64.
    /// - witness: `parts::tests::removal_clears_one_bit_across_a_word_boundary`
    #[inline]
    #[spec(ensures: |ret| ret.map_or(true, |(_word, mask)| mask.0.is_power_of_two()))]
    fn position(self) -> Result<(Slot, BitMask), Unaddressable>
    {
        let word = self.0.checked_shr(WORD_SHIFT).ok_or(Unaddressable)?;
        let word = usize::try_from(word).map_err(|_overflow| Unaddressable)?;
        let bit = u32::try_from(self.0 & BIT_MASK).map_err(|_overflow| Unaddressable)?;
        let mask = 1_u64.checked_shl(bit).ok_or(Unaddressable)?;
        Ok((Slot(word), BitMask(mask)))
    }

    /// The column slot this key's cells occupy, when addressable.
    ///
    /// # Specification
    /// - ensures: on success the slot is the key's value.
    /// - fails: [`Unaddressable`] when the key does not fit a `usize`.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Unaddressable`]: the key is beyond what this target can index.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every column read in the defect and keyed fixtures
    ///   reads the cell of its own key; a shifted slot reads a neighbour's.
    /// - witness: `tests::keyed::the_fixture_round_trips_through_the_block_store`
    #[inline]
    #[spec(ensures: |ret| ret.map_or(true, |slot| u64::try_from(slot.0) == Ok(self.0)))]
    pub(crate) fn slot(self) -> Result<Slot, Unaddressable>
    {
        usize::try_from(self.0)
            .map(Slot)
            .map_err(|_overflow| Unaddressable)
    }
}

impl From<u64> for PartKey
{
    /// Reads a counter value as a key; whether a part holds it is the
    /// store's question.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(key: u64) -> Self
    {
        Self(key)
    }
}

impl From<PartKey> for u64
{
    /// Reads the key's counter value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(key: PartKey) -> Self
    {
        key.0
    }
}

impl fmt::Display for PartKey
{
    /// Writes the key in decimal.
    ///
    /// # Specification
    /// - ensures: writes the counter value in decimal.
    /// - fails: propagates the formatter's write failure unchanged.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Errors
    /// Propagates the formatter's write failure.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the defect witness renders the referring edge's and
    ///   the vertex's keys in the refusal message.
    /// - witness: `tests::defect::deleting_the_middle_vertex_refuses_by_name`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        fmt::Display::fmt(&self.0, f)
    }
}

/// A position in a column or a bit set.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(crate) struct Slot(usize);

impl From<Slot> for usize
{
    /// Reads the position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(slot: Slot) -> Self
    {
        slot.0
    }
}

impl Slot
{
    /// The key at a bit of this bit-set word.
    ///
    /// # Specification
    /// - ensures: on success the key is the word times 64 plus the bit.
    /// - fails: [`Unaddressable`] when the key does not fit a `u64`.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Unaddressable`]: the key overflows.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — iteration across the word boundary yields keys 63 and
    ///   65, so a lost word offset or bit shows.
    /// - witness: `parts::tests::removal_clears_one_bit_across_a_word_boundary`
    #[inline]
    #[spec(ensures: |ret| ret.map_or(true, |key| key.0 & BIT_MASK == u64::from(bit.0)))]
    fn key(
        self,
        bit: BitIndex,
    ) -> Result<PartKey, Unaddressable>
    {
        let word = u64::try_from(self.0).map_err(|_overflow| Unaddressable)?;
        let base = word.checked_shl(WORD_SHIFT).ok_or(Unaddressable)?;
        base.checked_add(u64::from(bit.0))
            .map(PartKey)
            .ok_or(Unaddressable)
    }
}

/// A bit's position within one bit-set word.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct BitIndex(u32);

/// One bit within a bit-set word.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct BitMask(u64);

/// The counter has minted its largest key.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(crate) struct Exhausted;

/// A key beyond what this target can index.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(crate) struct Unaddressable;

/// Whether a key names a live part.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Liveness
{
    /// No live part holds the key: never minted, or deleted.
    Dead,
    /// A live part holds the key.
    Live,
}

/// How many parts a table holds or has minted.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct PartCount(u64);

impl From<PartCount> for u64
{
    /// Reads the count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: PartCount) -> Self
    {
        count.0
    }
}

/// One table's parts: a bit set of live keys and the counter that mints them.
///
/// # Specification
/// - requires: construction through [`PartSet::new`] or [`PartSet::reserved`].
/// - ensures: every set bit is below the counter; the live count is the number
///   of set bits; the counter never decreases.
/// - provides: minting, removal, restoration and ascending iteration.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — consecutive mints, a removal across a word boundary and a
///   restore observe exact liveness, counts and iteration order; an abandoned
///   edit leaves the counter advanced.
/// - witness: `parts::tests::mints_are_consecutive_and_the_last_key_is_refused`
/// - witness: `parts::tests::removal_clears_one_bit_across_a_word_boundary`
/// - witness: `tests::equations::an_abandoned_edit_leaves_no_part_and_no_reused_key`
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct PartSet
{
    /// The live bits, 64 keys per word.
    words: Vec<u64>,
    /// How many bits are set.
    live: u64,
    /// The next key to mint.
    next: PartKey,
}

impl PartSet
{
    /// An empty set whose counter stands at [`PartKey::FIRST`].
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) const fn new() -> Self
    {
        Self {
            words: Vec::new(),
            live: 0_u64,
            next: PartKey::FIRST,
        }
    }

    /// An empty set whose counter stands at `next`, for a reopened table.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) const fn reserved(next: PartKey) -> Self
    {
        Self {
            words: Vec::new(),
            live: 0_u64,
            next,
        }
    }

    /// Mints the next key and marks it live.
    ///
    /// # Specification
    /// - ensures: on success the key is the counter's previous value, it is
    ///   live, the counter is one greater and the live count one greater.
    /// - fails: [`Exhausted`] at the largest key, changing nothing.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Exhausted`]: the counter cannot advance.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — three mints observe keys zero, one and two, all live;
    ///   a counter at the largest key refuses.
    /// - witness: `parts::tests::mints_are_consecutive_and_the_last_key_is_refused`
    #[inline]
    #[spec(
        captures: before = self.next,
        ensures: |ret| ret.map_or(self.next == before, |key| key == before && self.next > before),
    )]
    pub(crate) fn mint(&mut self) -> Result<PartKey, Exhausted>
    {
        let key = self.next;
        let next = key.next()?;
        let (word, mask) = key.position().map_err(|_unaddressable| Exhausted)?;
        if self.words.len() <= word.0 {
            self.words.resize(word.0.saturating_add(1_usize), 0_u64);
        }
        let Some(bits) = self.words.get_mut(word.0)
        else {
            return Err(Exhausted);
        };
        *bits |= mask.0;
        self.live = self.live.saturating_add(1_u64);
        self.next = next;
        Ok(key)
    }

    /// Whether the key is live.
    ///
    /// # Specification
    /// - ensures: [`Liveness::Live`] exactly when the key's bit is set.
    /// - panics: none.
    /// - executable: none — the answer is the bit itself; the mint, remove and
    ///   restore witnesses observe it through every transition.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — liveness after mints, a removal and a restore.
    /// - witness: `parts::tests::removal_clears_one_bit_across_a_word_boundary`
    #[inline]
    #[must_use]
    pub(crate) fn liveness(
        &self,
        key: PartKey,
    ) -> Liveness
    {
        let Ok((word, mask)) = key.position()
        else {
            return Liveness::Dead;
        };
        match self.words.get(word.0) {
            Some(bits) if bits & mask.0 != 0_u64 => Liveness::Live,
            Some(_) | None => Liveness::Dead,
        }
    }

    /// Clears a live key's bit; the counter does not move.
    ///
    /// # Specification
    /// - requires: nothing; a key that is not live is left as it is.
    /// - ensures: the key is dead; the live count is one smaller when it was
    ///   live and unchanged otherwise; every other key's liveness and the
    ///   counter are unchanged.
    /// - panics: none.
    /// - executable: none — a predicate over every other key would walk the
    ///   set; the boundary witness observes the neighbours.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — removing key 64 of 66 leaves 63 and 65 live, and
    ///   removing it again counts nothing.
    /// - witness: `parts::tests::removal_clears_one_bit_across_a_word_boundary`
    #[inline]
    pub(crate) fn remove(
        &mut self,
        key: PartKey,
    )
    {
        let Ok((word, mask)) = key.position()
        else {
            return;
        };
        if let Some(bits) = self.words.get_mut(word.0)
            && *bits & mask.0 != 0_u64
        {
            *bits &= !mask.0;
            self.live = self.live.saturating_sub(1_u64);
        }
    }

    /// Sets the bit of a key already minted, undoing a removal or confirming
    /// a mint.
    ///
    /// # Specification
    /// - requires: the key is below the counter.
    /// - ensures: the key is live; the live count grows by one when it was
    ///   dead.
    /// - panics: none.
    /// - executable: none — the transition is observed through liveness and the
    ///   live count in the witness.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — restoring a removed key makes it live and restores
    ///   the count; a refused delete's rollback restores the part.
    /// - witness: `parts::tests::removal_clears_one_bit_across_a_word_boundary`
    /// - witness: `tests::equations::an_abandoned_edit_leaves_no_part_and_no_reused_key`
    #[inline]
    pub(crate) fn restore(
        &mut self,
        key: PartKey,
    )
    {
        let Ok((word, mask)) = key.position()
        else {
            return;
        };
        if self.words.len() <= word.0 {
            self.words.resize(word.0.saturating_add(1_usize), 0_u64);
        }
        if let Some(bits) = self.words.get_mut(word.0)
            && *bits & mask.0 == 0_u64
        {
            *bits |= mask.0;
            self.live = self.live.saturating_add(1_u64);
        }
    }

    /// How many parts are live.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) const fn live(&self) -> PartCount
    {
        PartCount(self.live)
    }

    /// The next key the counter mints.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) const fn next_key(&self) -> PartKey
    {
        self.next
    }

    /// The live keys in ascending order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn iter(&self) -> LiveParts<'_>
    {
        LiveParts {
            words: &self.words,
            word: Slot(0_usize),
            remaining: self.words.first().copied().unwrap_or(0_u64),
        }
    }
}

/// The live keys of one table, ascending.
#[derive(Clone, Debug)]
pub struct LiveParts<'parts>
{
    /// The bit set.
    words: &'parts [u64],
    /// The word being read.
    word: Slot,
    /// The word's bits not yet yielded.
    remaining: u64,
}

impl Iterator for LiveParts<'_>
{
    type Item = PartKey;

    /// Yields the next live key.
    ///
    /// # Specification
    /// - ensures: yields each set bit's key exactly once, in ascending order,
    ///   then `None`.
    /// - panics: none.
    /// - executable: none — the sequence is observed whole by the iteration
    ///   witness; a per-call predicate sees one key.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — iteration over 66 mints with key 64 removed yields
    ///   every other key once, ascending, across the word boundary.
    /// - witness: `parts::tests::removal_clears_one_bit_across_a_word_boundary`
    #[inline]
    fn next(&mut self) -> Option<PartKey>
    {
        loop {
            if self.remaining != 0_u64 {
                let bit = self.remaining.trailing_zeros();
                self.remaining &= self.remaining.saturating_sub(1_u64);
                return self.word.key(BitIndex(bit)).ok();
            }
            let next = self.word.0.checked_add(1_usize)?;
            let bits = self.words.get(next)?;
            self.remaining = *bits;
            self.word = Slot(next);
        }
    }
}

#[cfg(test)]
mod tests
{
    use alloc::vec::Vec;

    use super::Liveness;
    use super::PartKey;
    use super::PartSet;

    #[test]
    fn mints_are_consecutive_and_the_last_key_is_refused()
    {
        let mut set = PartSet::new();
        let keys: Vec<u64> =
            core::iter::repeat_with(|| u64::from(set.mint().expect("a fresh set mints")))
                .take(3)
                .collect();
        assert_eq!(keys, [0_u64, 1, 2], "mints are consecutive from zero");
        assert_eq!(u64::from(set.live()), 3_u64, "three parts are live");
        assert_eq!(
            u64::from(set.next_key()),
            3_u64,
            "the counter stands at three"
        );

        let mut last = PartSet::reserved(PartKey::from(u64::MAX));
        assert!(
            last.mint().is_err(),
            "the largest key has no successor to stand at"
        );
        assert_eq!(
            last.next_key(),
            PartKey::from(u64::MAX),
            "a refused mint leaves the counter"
        );
    }

    #[test]
    fn removal_clears_one_bit_across_a_word_boundary()
    {
        let mut set = PartSet::new();
        for _mint in 0_u8 .. 66_u8 {
            set.mint().expect("the set mints");
        }
        set.remove(PartKey::from(64_u64));
        assert_eq!(
            set.liveness(PartKey::from(63_u64)),
            Liveness::Live,
            "the last bit of word zero"
        );
        assert_eq!(
            set.liveness(PartKey::from(64_u64)),
            Liveness::Dead,
            "the removed key"
        );
        assert_eq!(
            set.liveness(PartKey::from(65_u64)),
            Liveness::Live,
            "its neighbour in word one"
        );
        assert_eq!(
            set.liveness(PartKey::from(66_u64)),
            Liveness::Dead,
            "never minted"
        );
        assert_eq!(u64::from(set.live()), 65_u64, "one fewer live part");
        assert_eq!(
            u64::from(set.next_key()),
            66_u64,
            "the counter does not move"
        );
        set.remove(PartKey::from(64_u64));
        assert_eq!(
            u64::from(set.live()),
            65_u64,
            "removing the dead key again counts nothing"
        );

        let keys: Vec<u64> = set.iter().map(u64::from).collect();
        let expected: Vec<u64> = (0_u64 .. 66_u64).filter(|key| *key != 64_u64).collect();
        assert_eq!(
            keys, expected,
            "iteration is ascending and skips the removed key"
        );

        set.restore(PartKey::from(64_u64));
        assert_eq!(
            set.liveness(PartKey::from(64_u64)),
            Liveness::Live,
            "the restored key"
        );
        assert_eq!(u64::from(set.live()), 66_u64, "the count is restored");
    }
}
