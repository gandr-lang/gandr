//! Parts: stable keys that each writer mints in its own region, live parts as
//! a bit set for each region.
//!
//! A [`PartKey`] is a [`Writer`]'s region and a [`PartOffset`] inside it. A
//! writer mints offsets in its region by a counter that only grows. A key is
//! never reused, renumbered or moved: deleting a part clears its bit and
//! leaves every other key where it was. This is the marked-as-deleted part
//! model, and it is what lets a part's key be a record-plane key whose
//! identity survives every edit that does not touch that part.
//!
//! The key reads no order of the mints of its table. Two writers mint into
//! two regions, so their keys never collide. Their tables then glue by a
//! union of their parts, with no renumbering.

use alloc::vec::Vec;
use core::cmp::Ordering;
use core::fmt;

use anodized::spec;

/// The width of one bit-set word, as a shift.
const WORD_SHIFT: u32 = 6_u32;

/// The mask selecting a bit within one word.
const BIT_MASK: u64 = 0x3f_u64;

/// The mask selecting a key's offset: its low forty-eight bits.
const OFFSET_MASK: u64 = 0xffff_ffff_ffff_u64;

/// The region of one writer: the producer that mints parts into a store.
///
/// # Specification
/// - provides: the high sixteen bits of a [`PartKey`]. Two writers mint into
///   two regions, so their keys never collide. A store glues at most 65,536
///   writers.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Writer(u16);

impl From<u16> for Writer
{
    /// Reads a region id as a writer.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(writer: u16) -> Self
    {
        Self(writer)
    }
}

impl From<Writer> for u16
{
    /// Reads the writer's region id.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(writer: Writer) -> Self
    {
        writer.0
    }
}

impl fmt::Display for Writer
{
    /// Writes the region id in decimal.
    ///
    /// # Specification
    /// - ensures: writes the region id in decimal.
    /// - fails: propagates the formatter's write failure unchanged.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Errors
    /// Propagates the formatter's write failure.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the glue witness renders the writer of a region that
    ///   two stores hold apart in the refusal.
    /// - witness: `tests::glue::two_stores_that_disagree_on_a_shared_region_do_not_glue`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        fmt::Display::fmt(&self.0, f)
    }
}

/// A part's place inside its writer's region.
///
/// # Specification
/// - provides: the low bits of a [`PartKey`]. A writer mints offsets in
///   increasing order from [`PartOffset::FIRST`], up to [`PartOffset::LAST`].
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct PartOffset(u64);

impl PartOffset
{
    /// The first offset that a writer mints in a table.
    pub const FIRST: Self = Self(0_u64);
    /// The largest offset that a key holds: `2^48 − 1`. A counter stands here
    /// once its region is spent.
    pub const LAST: Self = Self(OFFSET_MASK);

    /// The offset after this one.
    ///
    /// # Specification
    /// - ensures: on success the offset is exactly one greater, and at most
    ///   [`PartOffset::LAST`].
    /// - fails: [`Exhausted`] at or past [`PartOffset::LAST`].
    /// - panics: none.
    ///
    /// # Errors
    /// [`Exhausted`]: no offset of the region follows the last.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — successive mints observe consecutive offsets from
    ///   zero, and a region whose counter stands at the last offset refuses the
    ///   next mint.
    /// - witness: `parts::tests::mints_are_consecutive_and_the_last_key_is_refused`
    #[inline]
    #[spec(ensures: |ret| ret.map_or(self >= Self::LAST, |next| next <= Self::LAST && next.0.checked_sub(1_u64) == Some(self.0)))]
    fn next(self) -> Result<Self, Exhausted>
    {
        if self.0 < OFFSET_MASK {
            Ok(Self(self.0.saturating_add(1_u64)))
        }
        else {
            Err(Exhausted)
        }
    }

    /// The bit-set word and bit that this offset occupies, when addressable.
    ///
    /// # Specification
    /// - ensures: on success the word is the offset over 64 and the mask has
    ///   the bit of the offset modulo 64.
    /// - fails: [`Unaddressable`] when the word does not fit a `usize`.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Unaddressable`]: the offset is beyond what this target can index.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — offsets 63, 64 and 65 occupy the last bit of word
    ///   zero and the first two of word one, observed through liveness after
    ///   minting 66 parts and removing 64.
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
}

impl From<u64> for PartOffset
{
    /// Reads a counter value as an offset.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(offset: u64) -> Self
    {
        Self(offset)
    }
}

impl From<PartOffset> for u64
{
    /// Reads the offset's counter value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(offset: PartOffset) -> Self
    {
        offset.0
    }
}

/// A part's stable key: its writer's region and its offset inside it.
///
/// The key is one `u64`: the writer's sixteen bits above the offset's
/// forty-eight. So keys order by writer, then by offset, and a key costs
/// what a counter costs to copy, compare and hash. A writer mints its offsets
/// in increasing order, and its counter's next value is committed with the
/// table. So a reopened store never mints a key that it has minted before.
///
/// # Specification
/// - provides: the name of a part, for the store's whole life. No order of the
///   mints of the table enters it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct PartKey(u64);

/// A key takes the eight bytes of a counter, its writer included.
const _: () = assert!(size_of::<PartKey>() == 8_usize, "a key is one word");

impl PartKey
{
    /// The key of a writer's region and an offset inside it, when the offset
    /// fits a key; whether a part holds it is the store's question.
    ///
    /// # Specification
    /// - ensures: `Some` exactly when `offset` is at most [`PartOffset::LAST`],
    ///   and then the key's writer and offset are `writer` and `offset`.
    /// - panics: none.
    /// - executable: none — the answer is one comparison and a packing; the
    ///   parts witness reads the widest writer and offset back and refuses an
    ///   offset past the last.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the widest writer and the last offset read back from
    ///   one key, and an offset past the last makes no key.
    /// - witness: `parts::tests::mints_are_consecutive_and_the_last_key_is_refused`
    #[inline]
    #[must_use]
    pub const fn new(
        writer: Writer,
        offset: PartOffset,
    ) -> Option<Self>
    {
        if offset.0 > OFFSET_MASK {
            return None;
        }
        let [o0, o1, o2, o3, o4, o5, _, _] = offset.0.to_le_bytes();
        let [w0, w1] = writer.0.to_le_bytes();
        Some(Self(u64::from_le_bytes([o0, o1, o2, o3, o4, o5, w0, w1])))
    }

    /// The writer that minted the part.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn writer(self) -> Writer
    {
        let [_, _, _, _, _, _, w0, w1] = self.0.to_le_bytes();
        Writer(u16::from_le_bytes([w0, w1]))
    }

    /// The part's place in its writer's region.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn offset(self) -> PartOffset
    {
        PartOffset(self.0 & OFFSET_MASK)
    }

    /// The place of this key's cells in its writer's run of a column, when
    /// addressable.
    ///
    /// # Specification
    /// - ensures: on success the slot is the key's offset.
    /// - fails: [`Unaddressable`] when the offset does not fit a `usize`.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Unaddressable`]: the offset is beyond what this target can index.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every column read in the defect and keyed fixtures
    ///   reads the cell of its own key; a shifted slot reads a neighbour's.
    /// - witness: `tests::keyed::the_fixture_round_trips_through_the_block_store`
    #[inline]
    #[spec(ensures: |ret| ret.map_or(true, |slot| u64::try_from(slot.0) == Ok(self.offset().0)))]
    fn slot(self) -> Result<Slot, Unaddressable>
    {
        usize::try_from(self.offset().0)
            .map(Slot)
            .map_err(|_overflow| Unaddressable)
    }
}

impl fmt::Display for PartKey
{
    /// Writes the key as its writer and its offset, `writer:offset`.
    ///
    /// # Specification
    /// - ensures: writes the writer and the offset in decimal, with a colon
    ///   between them.
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
        write!(f, "{}:{}", self.writer(), self.offset().0)
    }
}

impl From<u64> for PartKey
{
    /// Reads a key's bits, as a record key or an arrow cell holds them: the
    /// high sixteen name the writer, the low forty-eight the offset.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bits: u64) -> Self
    {
        Self(bits)
    }
}

impl From<PartKey> for u64
{
    /// Reads the key's bits, as a record key or an arrow cell holds them.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(key: PartKey) -> Self
    {
        key.0
    }
}

/// A position in a column's run or in a region's bit set.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Slot(usize);

impl Slot
{
    /// The offset at a bit of this bit-set word.
    ///
    /// # Specification
    /// - ensures: on success the offset is the word times 64 plus the bit.
    /// - fails: [`Unaddressable`] when the offset does not fit a `u64`.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Unaddressable`]: the offset overflows.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — iteration across the word boundary yields offsets 63
    ///   and 65, so a lost word offset or bit shows.
    /// - witness: `parts::tests::removal_clears_one_bit_across_a_word_boundary`
    #[inline]
    #[spec(ensures: |ret| ret.map_or(true, |offset| offset.0 & BIT_MASK == u64::from(bit.0)))]
    fn offset(
        self,
        bit: BitIndex,
    ) -> Result<PartOffset, Unaddressable>
    {
        let word = u64::try_from(self.0).map_err(|_overflow| Unaddressable)?;
        let base = word.checked_shl(WORD_SHIFT).ok_or(Unaddressable)?;
        base.checked_add(u64::from(bit.0))
            .map(PartOffset)
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

/// The counter has minted its largest offset.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(crate) struct Exhausted;

/// A key beyond what this target can index, or beyond what a column holds.
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

/// Whether a table's counters have reached a key.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(crate) enum Minting
{
    /// The key's writer has a region below whose counter the key stands.
    Minted,
    /// The key stands at or past its writer's counter.
    Unminted,
    /// The table holds no region of the key's writer.
    Unseen,
}

/// Whether two copies of one writer's region hold the same parts.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(crate) enum Agreement
{
    /// The same writer, the same counter and the same live parts.
    Agrees,
    /// The copies differ.
    Differs,
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

/// The next offset that one writer's counter mints in one table.
///
/// # Specification
/// - provides: what a manifest commits of each region of a table, so a reopened
///   store never mints a key that it has minted before.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Counter
{
    /// The writer whose region the counter mints in.
    writer: Writer,
    /// The next offset that the counter mints.
    next: PartOffset,
}

impl Counter
{
    /// The counter of a writer's region that stands at `next`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        writer: Writer,
        next: PartOffset,
    ) -> Self
    {
        Self { writer, next }
    }

    /// The writer whose region the counter mints in.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn writer(self) -> Writer
    {
        self.writer
    }

    /// The next offset that the counter mints.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn next(self) -> PartOffset
    {
        self.next
    }
}

/// The id that no writer has: one past the largest `u16`. A [`ByWriter`]
/// holds it as its lowest id while it holds no writer.
const NO_WRITER: u32 = 0x1_0000_u32;

/// The lowest writer with its value, and each further writer with its value.
type Split<'map, V> = (Option<(Writer, &'map V)>, &'map [(Writer, V)]);

/// One value for each writer, ascending by writer.
///
/// The lowest writer's value is held inline. So a table or a column of one
/// writer reaches its value through no indirection more than the value's own,
/// and only a further writer's value is behind the list. The lowest writer's
/// id is a `u32`, and [`NO_WRITER`] stands in it while no writer is held. Every
/// writer's id is below [`NO_WRITER`]. So one comparison of a writer's id with
/// the lowest tells a hit, a further writer and a miss apart.
///
/// # Specification
/// - ensures: `lowest` is the lowest writer's id whenever any writer is held,
///   and [`NO_WRITER`] otherwise; `first` is that writer's value, or the empty
///   value; `rest` ascends by writer, each writer above the lowest and each
///   once.
/// - provides: the value of a writer, read, written and held in order.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — two writers mint in either order, the lower one second,
///   and the iteration still takes the lower writer first.
/// - witness: `parts::tests::two_writers_mint_apart_and_iterate_by_writer`
#[derive(Clone, Debug, Eq, PartialEq)]
struct ByWriter<V>
{
    /// The lowest writer's id, or [`NO_WRITER`].
    lowest: u32,
    /// The lowest writer's value, or the empty value.
    first: V,
    /// Each further writer and its value, ascending by writer.
    rest: Vec<(Writer, V)>,
}

impl<V> ByWriter<V>
{
    /// No writer, with `empty` held in place of the lowest writer's value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    const fn new(empty: V) -> Self
    {
        Self {
            lowest: NO_WRITER,
            first: empty,
            rest: Vec::new(),
        }
    }

    /// The value of `writer`, when held.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn get(
        &self,
        writer: Writer,
    ) -> Option<&V>
    {
        match u32::from(writer.0).cmp(&self.lowest) {
            Ordering::Equal => Some(&self.first),
            Ordering::Greater => further(&self.rest, writer)
                .and_then(|at| self.rest.get(at.0))
                .map(|entry| &entry.1),
            Ordering::Less => None,
        }
    }

    /// The value of `writer` to write, when held.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn get_mut(
        &mut self,
        writer: Writer,
    ) -> Option<&mut V>
    {
        match u32::from(writer.0).cmp(&self.lowest) {
            Ordering::Equal => Some(&mut self.first),
            Ordering::Greater => further(&self.rest, writer)
                .and_then(|at| self.rest.get_mut(at.0))
                .map(|entry| &mut entry.1),
            Ordering::Less => None,
        }
    }

    /// The value of `writer` to write, made by `make` and held when absent.
    ///
    /// A held writer costs one lookup, so a mint or a grown cell of a known
    /// writer reads the map once.
    ///
    /// # Specification
    /// - ensures: on return [`ByWriter::get`] of `writer` is held; a held value
    ///   is unchanged, and an absent one is `make`'s; every other writer keeps
    ///   its value, and the writers still ascend, the lowest inline. `Some` on
    ///   every path.
    /// - panics: none.
    /// - executable: none — the order is the map's invariant, observed whole by
    ///   the iteration witness.
    ///
    /// # Cost
    /// - allocation: the list's slot of a new writer, growth within the writers
    ///   held
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two writers mint in either order, the lower one
    ///   second, and each mints from zero in its own region.
    /// - witness: `parts::tests::two_writers_mint_apart_and_iterate_by_writer`
    #[inline]
    fn entry<F>(
        &mut self,
        writer: Writer,
        make: F,
    ) -> Option<&mut V>
    where
        F: FnOnce() -> V,
    {
        let id = u32::from(writer.0);
        match id.cmp(&self.lowest) {
            Ordering::Equal => Some(&mut self.first),
            Ordering::Greater => match self.rest.binary_search_by_key(&writer, |entry| entry.0) {
                Ok(at) => self.rest.get_mut(at).map(|entry| &mut entry.1),
                Err(at) => {
                    self.rest.insert(at, (writer, make()));
                    self.rest.get_mut(at).map(|entry| &mut entry.1)
                },
            },
            Ordering::Less => {
                let held = core::mem::replace(&mut self.first, make());
                if let Ok(lowest) = u16::try_from(self.lowest) {
                    self.rest.insert(0_usize, (Writer(lowest), held));
                }
                self.lowest = id;
                Some(&mut self.first)
            },
        }
    }

    /// The lowest writer with its value, and the further writers.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn split(&self) -> Split<'_, V>
    {
        let first = u16::try_from(self.lowest)
            .ok()
            .map(|lowest| (Writer(lowest), &self.first));
        (first, &self.rest)
    }

    /// Each writer with its value, ascending by writer.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn iter(&self) -> impl Iterator<Item = (Writer, &V)>
    {
        let (first, rest) = self.split();
        first
            .into_iter()
            .chain(rest.iter().map(|&(writer, ref value)| (writer, value)))
    }
}

/// The place of `writer` among the further writers, when held.
///
/// The search stays out of line. So a lookup of the lowest writer, which is
/// the only writer of a one-writer table, inlines into its caller as one
/// comparison.
///
/// # Specification
/// trivial.
#[inline(never)]
fn further<V>(
    rest: &[(Writer, V)],
    writer: Writer,
) -> Option<Slot>
{
    rest.binary_search_by_key(&writer, |entry| entry.0)
        .ok()
        .map(Slot)
}

/// One writer's parts of one table: a bit set of live offsets and the counter
/// that mints them. The table holds the writer beside the region.
///
/// # Specification
/// - ensures: every set bit is below the counter; the live count is the number
///   of set bits; the counter never decreases.
/// - provides: minting, removal and restoration inside one region.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — consecutive mints, a removal across a word boundary and a
///   restore observe exact liveness, counts and iteration order.
/// - witness: `parts::tests::removal_clears_one_bit_across_a_word_boundary`
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Region
{
    /// The live bits, 64 offsets per word.
    words: Vec<u64>,
    /// How many bits are set.
    live: u64,
    /// The next offset to mint.
    next: PartOffset,
}

impl Region
{
    /// An empty region whose counter stands at `next`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    const fn new(next: PartOffset) -> Self
    {
        Self {
            words: Vec::new(),
            live: 0_u64,
            next,
        }
    }

    /// The live keys of the region, which `writer` mints, ascending.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn parts(
        &self,
        writer: Writer,
    ) -> LiveParts<'_>
    {
        LiveParts::over(Some((writer, self)), &[])
    }

    /// Whether this copy and `other`, two copies of one writer's region, hold
    /// the same parts: the same counter and the same live offsets.
    ///
    /// # Specification
    /// - ensures: [`Agreement::Agrees`] exactly when the counters and the live
    ///   offsets are equal. A word of zeros past the last set bit counts as
    ///   absent, since a reopened region grows only to its last live offset.
    /// - panics: none.
    /// - executable: none — the answer is the comparison itself; the glue
    ///   witnesses observe it on a reopened and a live copy of one region.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a region shared by two stores agrees with itself, and
    ///   an edit of one copy makes the glue refuse.
    /// - witness: `tests::glue::two_writers_that_share_a_base_glue_over_it`
    /// - witness: `tests::glue::two_stores_that_disagree_on_a_shared_region_do_not_glue`
    #[inline]
    pub(crate) fn agreement(
        &self,
        other: &Self,
    ) -> Agreement
    {
        let live_words = |words: &[u64]| -> usize {
            words
                .iter()
                .rposition(|word| *word != 0_u64)
                .map_or(0_usize, |last| last.saturating_add(1_usize))
        };
        let ours = self.words.get(.. live_words(&self.words));
        let theirs = other.words.get(.. live_words(&other.words));
        let same = self.next == other.next && self.live == other.live && ours == theirs;
        if same {
            Agreement::Agrees
        }
        else {
            Agreement::Differs
        }
    }

    /// Mints the next offset and marks it live.
    ///
    /// # Specification
    /// - ensures: on success the offset is the counter's previous value, it is
    ///   live, the counter is one greater and the live count one greater.
    /// - fails: [`Exhausted`] at the largest offset, changing nothing.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Exhausted`]: the counter cannot advance.
    ///
    /// # Cost
    /// - allocation: the bit-set word of a new run of 64 offsets, growth within
    ///   the region's offsets
    ///
    /// # Adequacy
    /// - hypothesis: L3 — three mints observe offsets zero, one and two, all
    ///   live; a counter at the largest offset refuses.
    /// - witness: `parts::tests::mints_are_consecutive_and_the_last_key_is_refused`
    #[inline]
    #[spec(
        captures: before = self.next,
        ensures: |ret| ret.map_or(self.next == before, |offset| offset == before && self.next > before),
    )]
    fn mint(&mut self) -> Result<PartOffset, Exhausted>
    {
        let offset = self.next;
        let next = offset.next()?;
        let (word, mask) = offset.position().map_err(|_unaddressable| Exhausted)?;
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
        Ok(offset)
    }
}

/// What a table holds of one writer's region.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Holding<'set>
{
    /// The table holds the region.
    Held(&'set Region),
    /// The table holds no region of the writer.
    Unseen,
}

/// One table's parts: one region for each writer that has minted in it,
/// ordered by writer.
///
/// # Specification
/// - requires: construction through [`PartSet::new`] or [`PartSet::reserved`].
/// - ensures: the regions ascend by writer, each writer once; in each region
///   every set bit is below its counter and the counter never decreases; the
///   live count is the number of set bits of every region.
/// - provides: minting, removal, restoration, ascending iteration and the
///   adoption of another table's region.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — consecutive mints, a removal across a word boundary and a
///   restore observe exact liveness, counts and iteration order; two writers
///   mint apart, and the iteration takes the first writer's keys first; an
///   abandoned edit leaves the counter advanced.
/// - witness: `parts::tests::mints_are_consecutive_and_the_last_key_is_refused`
/// - witness: `parts::tests::removal_clears_one_bit_across_a_word_boundary`
/// - witness: `parts::tests::two_writers_mint_apart_and_iterate_by_writer`
/// - witness: `tests::equations::an_abandoned_edit_leaves_no_part_and_no_reused_key`
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct PartSet
{
    /// Each writer's region, ascending by writer.
    regions: ByWriter<Region>,
    /// How many bits of every region are set.
    live: u64,
}

impl PartSet
{
    /// An empty set with no region.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) const fn new() -> Self
    {
        Self {
            regions: ByWriter::new(Region::new(PartOffset::FIRST)),
            live: 0_u64,
        }
    }

    /// An empty set whose regions' counters stand at `counters`, for a
    /// reopened table.
    ///
    /// # Specification
    /// - requires: `counters` ascend by writer, each writer once.
    /// - ensures: one empty region for each counter, in its order.
    /// - panics: none.
    /// - executable: none — the result holds no part to compare; the reopening
    ///   witness reads every part back below its counter.
    ///
    /// # Cost
    /// - allocation: one region for each counter past the first, setup
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a reopened keyed fixture mints its next key after its
    ///   last, never a reused one.
    /// - witness: `tests::keyed::the_fixture_round_trips_through_the_block_store`
    #[inline]
    pub(crate) fn reserved<Counters>(counters: Counters) -> Self
    where
        Counters: IntoIterator<Item = Counter>,
    {
        let mut regions = ByWriter::new(Region::new(PartOffset::FIRST));
        for counter in counters {
            if let Some(region) = regions.entry(counter.writer, || Region::new(counter.next)) {
                region.next = counter.next;
            }
        }
        Self {
            regions,
            live: 0_u64,
        }
    }

    /// Mints `writer`'s next key and marks it live.
    ///
    /// # Specification
    /// - ensures: on success the key's offset is the writer's counter's
    ///   previous value, or [`PartOffset::FIRST`] for a writer the table has
    ///   not seen; the key is live, the counter is one greater and the live
    ///   count one greater.
    /// - fails: [`Exhausted`] at the largest offset, changing no part.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Exhausted`]: the writer's counter cannot advance.
    ///
    /// # Cost
    /// - allocation: the region of a writer the table has not seen and the
    ///   bit-set word of a new run of 64 offsets, growth within the table's
    ///   writers and offsets
    ///
    /// # Adequacy
    /// - hypothesis: L3 — three mints observe offsets zero, one and two, all
    ///   live; a counter at the largest offset refuses; two writers each mint
    ///   from zero.
    /// - witness: `parts::tests::mints_are_consecutive_and_the_last_key_is_refused`
    /// - witness: `parts::tests::two_writers_mint_apart_and_iterate_by_writer`
    #[inline]
    #[spec(
        captures: before = self.live,
        ensures: |ret| ret.map_or(self.live == before, |key| key.writer() == writer && self.live > before),
    )]
    pub(crate) fn mint(
        &mut self,
        writer: Writer,
    ) -> Result<PartKey, Exhausted>
    {
        let region = self
            .regions
            .entry(writer, || Region::new(PartOffset::FIRST))
            .ok_or(Exhausted)?;
        let offset = region.mint()?;
        let key = PartKey::new(writer, offset).ok_or(Exhausted)?;
        self.live = self.live.saturating_add(1_u64);
        Ok(key)
    }

    /// The region of `writer`, when the table holds one.
    ///
    /// # Specification
    /// - ensures: [`Holding::Held`] with the region of `writer` exactly when
    ///   the table holds one.
    /// - panics: none.
    /// - executable: none — the answer borrows the region; the glue witnesses
    ///   observe both arms.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the glue reads a shared region as held and a writer's
    ///   own region as unseen by the other store.
    /// - witness: `tests::glue::two_writers_that_share_a_base_glue_over_it`
    #[inline]
    pub(crate) fn holding(
        &self,
        writer: Writer,
    ) -> Holding<'_>
    {
        self.regions
            .get(writer)
            .map_or(Holding::Unseen, Holding::Held)
    }

    /// Each region of the table with its writer, ascending by writer.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn regions(&self) -> impl Iterator<Item = (Writer, &Region)>
    {
        self.regions.iter()
    }

    /// Takes a copy of another table's region of a writer that this table has
    /// not seen.
    ///
    /// # Specification
    /// - requires: the table holds no region of `writer`.
    /// - ensures: the table holds the region as `writer`'s, its regions still
    ///   ascend by writer, and the live count grows by the region's.
    /// - panics: none.
    /// - executable: none — the regions' order is the set's invariant, observed
    ///   whole by the glue witness's iteration.
    ///
    /// # Cost
    /// - allocation: the copy of the region's bit set, growth within the
    ///   writers of the glued tables
    ///
    /// # Adequacy
    /// - hypothesis: L2 — two writers' tables glue to the union of their parts,
    ///   ascending.
    /// - witness: `tests::glue::two_writers_glue_to_the_union_of_their_parts`
    #[inline]
    pub(crate) fn adopt(
        &mut self,
        writer: Writer,
        region: &Region,
    )
    {
        if self.regions.get(writer).is_none()
            && self.regions.entry(writer, || region.clone()).is_some()
        {
            self.live = self.live.saturating_add(region.live);
        }
    }

    /// Whether the key is live.
    ///
    /// # Specification
    /// - ensures: [`Liveness::Live`] exactly when the key's writer has a region
    ///   whose bit of the key's offset is set.
    /// - panics: none.
    /// - executable: none — the answer is the bit itself; the mint, remove and
    ///   restore witnesses observe it through every transition.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — liveness after mints, a removal and a restore, and of
    ///   a key whose writer the table has not seen.
    /// - witness: `parts::tests::removal_clears_one_bit_across_a_word_boundary`
    /// - witness: `parts::tests::two_writers_mint_apart_and_iterate_by_writer`
    #[inline]
    #[must_use]
    pub(crate) fn liveness(
        &self,
        key: PartKey,
    ) -> Liveness
    {
        let Some(region) = self.regions.get(key.writer())
        else {
            return Liveness::Dead;
        };
        let Ok((word, mask)) = key.offset().position()
        else {
            return Liveness::Dead;
        };
        match region.words.get(word.0) {
            Some(bits) if bits & mask.0 != 0_u64 => Liveness::Live,
            Some(_) | None => Liveness::Dead,
        }
    }

    /// Whether the key's writer's counter has passed the key.
    ///
    /// # Specification
    /// - ensures: [`Minting::Minted`] exactly when the table holds a region of
    ///   the key's writer whose counter stands past the key's offset;
    ///   [`Minting::Unseen`] exactly when it holds no region of the writer.
    /// - panics: none.
    /// - executable: none — the answer is one comparison; the reopening witness
    ///   refuses a record past the counter and one of a writer the manifest
    ///   does not name.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a doctored record past its writer's counter and one
    ///   of an unseen writer are refused on reopening, each by its own fault.
    /// - witness: `tests::keyed::a_doctored_table_is_refused_on_reopening`
    #[inline]
    pub(crate) fn minting(
        &self,
        key: PartKey,
    ) -> Minting
    {
        match self.regions.get(key.writer()) {
            Some(region) if key.offset() < region.next => Minting::Minted,
            Some(_) => Minting::Unminted,
            None => Minting::Unseen,
        }
    }

    /// Clears a live key's bit; the counter does not move.
    ///
    /// # Specification
    /// - requires: nothing; a key that is not live is left as it is.
    /// - ensures: the key is dead; the live count is one smaller when it was
    ///   live and unchanged otherwise; every other key's liveness and every
    ///   counter are unchanged.
    /// - panics: none.
    /// - executable: none — a predicate over every other key would walk the
    ///   set; the boundary witness observes the neighbours.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — removing offset 64 of 66 leaves 63 and 65 live, and
    ///   removing it again counts nothing.
    /// - witness: `parts::tests::removal_clears_one_bit_across_a_word_boundary`
    #[inline]
    pub(crate) fn remove(
        &mut self,
        key: PartKey,
    )
    {
        let Ok((word, mask)) = key.offset().position()
        else {
            return;
        };
        if let Some(region) = self.regions.get_mut(key.writer())
            && let Some(bits) = region.words.get_mut(word.0)
            && *bits & mask.0 != 0_u64
        {
            *bits &= !mask.0;
            region.live = region.live.saturating_sub(1_u64);
            self.live = self.live.saturating_sub(1_u64);
        }
    }

    /// Sets the bit of a key already minted, undoing a removal or confirming
    /// a mint.
    ///
    /// # Specification
    /// - requires: the table holds a region of the key's writer, and the key's
    ///   offset is below its counter.
    /// - ensures: the key is live; the live count grows by one when it was
    ///   dead.
    /// - panics: none.
    /// - executable: none — the transition is observed through liveness and the
    ///   live count in the witness.
    ///
    /// # Cost
    /// - allocation: the bit-set words up to the key's offset, growth within
    ///   the region's offsets
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
        let Ok((word, mask)) = key.offset().position()
        else {
            return;
        };
        let Some(region) = self.regions.get_mut(key.writer())
        else {
            return;
        };
        if region.words.len() <= word.0 {
            region.words.resize(word.0.saturating_add(1_usize), 0_u64);
        }
        if let Some(bits) = region.words.get_mut(word.0)
            && *bits & mask.0 == 0_u64
        {
            *bits |= mask.0;
            region.live = region.live.saturating_add(1_u64);
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

    /// Each region's counter, ascending by writer.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn counters(&self) -> impl Iterator<Item = Counter> + '_
    {
        self.regions
            .iter()
            .map(|(writer, region)| Counter::new(writer, region.next))
    }

    /// The live keys in ascending order: by writer, then by offset.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn iter(&self) -> LiveParts<'_>
    {
        let (first, rest) = self.regions.split();
        LiveParts::over(first, rest)
    }
}

/// The live keys of one table, ascending.
#[derive(Clone, Debug)]
pub struct LiveParts<'parts>
{
    /// The region being read, with its writer.
    region: Option<(Writer, &'parts Region)>,
    /// The regions after it, with their writers.
    rest: &'parts [(Writer, Region)],
    /// The word being read.
    word: Slot,
    /// The word's bits not yet yielded.
    remaining: u64,
}

impl<'parts> LiveParts<'parts>
{
    /// The live keys of `region`, then of `rest`, in their order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn over(
        region: Option<(Writer, &'parts Region)>,
        rest: &'parts [(Writer, Region)],
    ) -> Self
    {
        Self {
            region,
            rest,
            word: Slot(0_usize),
            remaining: region
                .and_then(|(_, read)| read.words.first())
                .copied()
                .unwrap_or(0_u64),
        }
    }
}

impl Iterator for LiveParts<'_>
{
    type Item = PartKey;

    /// Yields the next live key.
    ///
    /// # Specification
    /// - ensures: yields each set bit's key exactly once, in ascending order of
    ///   writer then offset, then `None`.
    /// - panics: none.
    /// - executable: none — the sequence is observed whole by the iteration
    ///   witness; a per-call predicate sees one key.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — iteration over 66 mints with offset 64 removed yields
    ///   every other key once, ascending, across the word boundary; two
    ///   writers' keys come writer by writer.
    /// - witness: `parts::tests::removal_clears_one_bit_across_a_word_boundary`
    /// - witness: `parts::tests::two_writers_mint_apart_and_iterate_by_writer`
    #[inline]
    fn next(&mut self) -> Option<PartKey>
    {
        loop {
            let (writer, region) = self.region?;
            if self.remaining != 0_u64 {
                let bit = self.remaining.trailing_zeros();
                self.remaining &= self.remaining.saturating_sub(1_u64);
                let offset = self.word.offset(BitIndex(bit)).ok()?;
                return PartKey::new(writer, offset);
            }
            let next = self.word.0.checked_add(1_usize)?;
            if let Some(bits) = region.words.get(next) {
                self.remaining = *bits;
                self.word = Slot(next);
            }
            else {
                *self = match self.rest.split_first() {
                    Some((&(after, ref read), rest)) => Self::over(Some((after, read)), rest),
                    None => Self::over(None, &[]),
                };
            }
        }
    }
}

/// A column's cells: one dense run for each writer, ascending by writer, each
/// run indexed by the offsets of its writer's parts.
///
/// # Specification
/// - ensures: the runs ascend by writer, each writer once.
/// - provides: the cell of a key, read and written through its writer's run. A
///   column of one writer holds its run inline, so a cell read is one
///   comparison and one index.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — every column read of the fixtures reads the cell of its
///   own key, and two writers' columns glue to the union of their cells.
/// - witness: `tests::keyed::the_fixture_round_trips_through_the_block_store`
/// - witness: `tests::glue::two_writers_glue_to_the_union_of_their_parts`
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Segments<T>
{
    /// Each writer's run of cells, indexed by offset.
    runs: ByWriter<Vec<T>>,
}

impl<T> Segments<T>
{
    /// A column with no cell.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) const fn new() -> Self
    {
        Self {
            runs: ByWriter::new(Vec::new()),
        }
    }

    /// The cell of `key`, when the column holds one.
    ///
    /// # Specification
    /// - ensures: on success the cell at the key's offset in the run of the
    ///   key's writer.
    /// - fails: [`Unaddressable`] when the column holds no run of the writer,
    ///   or no cell at the offset.
    /// - panics: none.
    /// - executable: none — the answer is the cell itself; the fixtures read
    ///   every cell back against what they wrote.
    ///
    /// # Errors
    /// [`Unaddressable`]: the column holds no cell of the key.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every column read of the keyed round trip reads the
    ///   cell of its own key.
    /// - witness: `tests::keyed::the_fixture_round_trips_through_the_block_store`
    #[inline]
    pub(crate) fn cell(
        &self,
        key: PartKey,
    ) -> Result<&T, Unaddressable>
    {
        let slot = key.slot()?;
        self.runs
            .get(key.writer())
            .and_then(|run| run.get(slot.0))
            .ok_or(Unaddressable)
    }

    /// The cell of `key` to write, when the column holds one.
    ///
    /// # Specification
    /// - ensures: on success the cell at the key's offset in the run of the
    ///   key's writer.
    /// - fails: [`Unaddressable`] when the column holds no run of the writer,
    ///   or no cell at the offset.
    /// - panics: none.
    /// - executable: none — the answer is the cell itself; the undo witnesses
    ///   read every restored cell back.
    ///
    /// # Errors
    /// [`Unaddressable`]: the column holds no cell of the key.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a refused close restores every cell it wrote.
    /// - witness: `tests::equations::a_refused_close_restores_the_store`
    #[inline]
    pub(crate) fn cell_mut(
        &mut self,
        key: PartKey,
    ) -> Result<&mut T, Unaddressable>
    {
        let slot = key.slot()?;
        self.runs
            .get_mut(key.writer())
            .and_then(|run| run.get_mut(slot.0))
            .ok_or(Unaddressable)
    }
}

impl<T> Segments<T>
where
    T: Default + Clone,
{
    /// The cell of `key` to write, the column grown to hold it.
    ///
    /// # Specification
    /// - ensures: on success the column holds a run of the key's writer with a
    ///   cell at the key's offset; existing cells are unchanged, and a new cell
    ///   holds the default.
    /// - fails: [`Unaddressable`] when the offset does not fit a `usize`.
    /// - panics: none.
    /// - executable: none — `T` carries no bound a predicate could compare
    ///   with.
    ///
    /// # Errors
    /// [`Unaddressable`]: the offset is beyond what this target can index.
    ///
    /// # Cost
    /// - allocation: the run of a new writer and the cells up to the key's
    ///   offset, growth within the column's writers and offsets
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every add in the fixtures writes through a cell this
    ///   grows, and the round trip reads each back.
    /// - witness: `tests::keyed::the_fixture_round_trips_through_the_block_store`
    #[inline]
    pub(crate) fn ensure(
        &mut self,
        key: PartKey,
    ) -> Result<&mut T, Unaddressable>
    {
        let slot = key.slot()?;
        let run = self
            .runs
            .entry(key.writer(), Vec::new)
            .ok_or(Unaddressable)?;
        let wanted = slot.0.saturating_add(1_usize);
        if run.len() < wanted {
            run.resize(wanted, T::default());
        }
        run.get_mut(slot.0).ok_or(Unaddressable)
    }

    /// Takes a copy of `other`'s run of `writer`, in place of any run of
    /// `writer` that this column holds.
    ///
    /// # Specification
    /// - ensures: the column's run of `writer` is `other`'s, or the column
    ///   holds no new run when `other` holds none; the runs still ascend by
    ///   writer.
    /// - panics: none.
    /// - executable: none — the runs' order is the column's invariant, observed
    ///   through every cell read of the glue witness.
    ///
    /// # Cost
    /// - allocation: the copy of the run's cells, growth within the writers of
    ///   the glued columns
    ///
    /// # Adequacy
    /// - hypothesis: L2 — two writers' columns glue to the union of their
    ///   cells.
    /// - witness: `tests::glue::two_writers_glue_to_the_union_of_their_parts`
    #[inline]
    pub(crate) fn adopt(
        &mut self,
        other: &Self,
        writer: Writer,
    )
    {
        if let Some(run) = other.runs.get(writer)
            && let Some(ours) = self.runs.entry(writer, Vec::new)
        {
            ours.clone_from(run);
        }
    }
}

#[cfg(test)]
mod tests
{
    use alloc::vec::Vec;

    use super::Counter;
    use super::Liveness;
    use super::PartKey;
    use super::PartOffset;
    use super::PartSet;
    use super::Writer;

    #[test]
    fn mints_are_consecutive_and_the_last_key_is_refused()
    {
        let writer = Writer::from(7_u16);
        let key = |writer: Writer, value: u64| {
            PartKey::new(writer, PartOffset::from(value)).expect("the offset fits a key")
        };
        let mut set = PartSet::new();
        let offsets: Vec<u64> = core::iter::repeat_with(|| {
            u64::from(set.mint(writer).expect("a fresh set mints").offset())
        })
        .take(3)
        .collect();
        assert_eq!(offsets, [0_u64, 1, 2], "mints are consecutive from zero");
        assert_eq!(u64::from(set.live()), 3_u64, "three parts are live");
        assert_eq!(
            set.counters().collect::<Vec<_>>(),
            [Counter::new(writer, PartOffset::from(3_u64))],
            "the counter stands at three"
        );

        let mut spent = PartSet::reserved([Counter::new(writer, PartOffset::LAST)]);
        assert!(
            spent.mint(writer).is_err(),
            "the last offset has no successor to stand at"
        );
        assert_eq!(
            spent.counters().collect::<Vec<_>>(),
            [Counter::new(writer, PartOffset::LAST)],
            "a refused mint leaves the counter"
        );
        let past = PartOffset::from(u64::from(PartOffset::LAST).saturating_add(1));
        assert_eq!(
            PartKey::new(writer, past),
            None,
            "no key holds an offset past the last"
        );

        let high = Writer::from(u16::MAX);
        let last = PartKey::new(high, PartOffset::LAST).expect("the last offset fits a key");
        assert_eq!(
            (last.writer(), last.offset()),
            (high, PartOffset::LAST),
            "the widest writer and offset read back from one key"
        );
        assert!(
            key(Writer::from(1_u16), 0) > key(Writer::from(0_u16), u64::from(PartOffset::LAST)),
            "every key of a writer orders after every key of a lower writer"
        );
    }

    #[test]
    fn removal_clears_one_bit_across_a_word_boundary()
    {
        let writer = Writer::from(0_u16);
        let at = |value: u64| {
            PartKey::new(writer, PartOffset::from(value)).expect("the offset fits a key")
        };
        let mut set = PartSet::new();
        for _mint in 0_u8 .. 66_u8 {
            set.mint(writer).expect("the set mints");
        }
        set.remove(at(64));
        assert_eq!(
            set.liveness(at(63)),
            Liveness::Live,
            "the last bit of word zero"
        );
        assert_eq!(set.liveness(at(64)), Liveness::Dead, "the removed key");
        assert_eq!(
            set.liveness(at(65)),
            Liveness::Live,
            "its neighbour in word one"
        );
        assert_eq!(set.liveness(at(66)), Liveness::Dead, "never minted");
        assert_eq!(u64::from(set.live()), 65_u64, "one fewer live part");
        assert_eq!(
            set.counters().collect::<Vec<_>>(),
            [Counter::new(writer, PartOffset::from(66_u64))],
            "the counter does not move"
        );
        set.remove(at(64));
        assert_eq!(
            u64::from(set.live()),
            65_u64,
            "removing the dead key again counts nothing"
        );

        let offsets: Vec<u64> = set.iter().map(|live| u64::from(live.offset())).collect();
        let expected: Vec<u64> = (0_u64 .. 66_u64).filter(|value| *value != 64_u64).collect();
        assert_eq!(
            offsets, expected,
            "iteration is ascending and skips the removed key"
        );

        set.restore(at(64));
        assert_eq!(set.liveness(at(64)), Liveness::Live, "the restored key");
        assert_eq!(u64::from(set.live()), 66_u64, "the count is restored");
    }

    #[test]
    fn two_writers_mint_apart_and_iterate_by_writer()
    {
        let (first, second) = (Writer::from(3_u16), Writer::from(9_u16));
        let mut set = PartSet::new();
        let key = |writer: Writer, value: u64| {
            PartKey::new(writer, PartOffset::from(value)).expect("the offset fits a key")
        };
        let minted = [second, first, second, first, second]
            .map(|writer| set.mint(writer).expect("each writer mints"));
        assert_eq!(
            minted,
            [
                key(second, 0),
                key(first, 0),
                key(second, 1),
                key(first, 1),
                key(second, 2),
            ],
            "each writer mints from zero in its own region, so no key collides"
        );
        assert_eq!(
            set.iter().collect::<Vec<_>>(),
            [
                key(first, 0),
                key(first, 1),
                key(second, 0),
                key(second, 1),
                key(second, 2),
            ],
            "the iteration takes the writers in order, each writer's offsets ascending"
        );
        assert_eq!(u64::from(set.live()), 5_u64, "five parts are live");
        assert_eq!(
            set.liveness(key(Writer::from(4_u16), 0)),
            Liveness::Dead,
            "a writer the table has not seen holds no live part"
        );
        assert_eq!(
            set.counters().collect::<Vec<_>>(),
            [
                Counter::new(first, PartOffset::from(2_u64)),
                Counter::new(second, PartOffset::from(3_u64)),
            ],
            "one counter for each writer, ascending by writer"
        );
    }
}
