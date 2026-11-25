//! The tiered code a selection is written in: one self-describing code per
//! zone it selects from, each a whole number of 64-bit words.
//!
//! # The header
//!
//! Word 0 of a zone's code carries a header in its low eight bits: the form
//! (bits 0–1: dense, sparse, run, or a handle that only a store writes), the
//! zone (bit 2) and the code's length in words less one (bits 3–7). The
//! payload starts at bit 8, so index `i` of a one-word dense code is bit
//! `8 + i` and the word holds the 56 innermost binders. A length field of 31
//! is the long form: bits 8–63 of word 0 hold the length and the payload
//! starts at word 1, so a code of any length is written with its length up
//! front.
//!
//! # The forms
//!
//! - **dense** — bit `i` of the payload selects index `i`; the last word is
//!   never zero unless the code is one word.
//! - **sparse** — the selected indices as an Elias–Fano sequence: the count
//!   less one (24 bits), the lower width `ℓ` (6 bits), each index's low `ℓ`
//!   bits in order, then the upper bits in unary — index `k`'s high part `h`
//!   sets bit `h + k` — so membership and rank count set and clear bits a word
//!   at a time.
//! - **run** — a contiguous selection as its first index (32 bits) and its
//!   length less one (24 bits), in one word.
//!
//! The encoder sizes every form a selection admits and writes the smallest,
//! dense on a tie and run before sparse, so each selection has one code.
//!
//! # The two zones
//!
//! A selection writes the intuitionistic zone's code, then the linear
//! zone's, each only when the zone selects something; the empty selection is
//! the one-word dense intuitionistic code of nothing, the zero word. A reader
//! finds a zone's code by its header's zone bit, and a second code by the
//! first one's length.

use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::DeBruijnIndex;
use quenchant_shape::shape::Maybe;

use crate::context::BinderDepth;
use crate::syntax::Zone;

/// The bits of word 0 a code's header takes.
const HEADER_BITS: u64 = 8;

/// Word 0's header bits, all zero in a one-word dense intuitionistic code.
const HEADER_MASK: u64 = 0xFF;

/// The header's form field.
const FORM_MASK: u64 = 0b11;

/// The header's zone bit: set for the linear zone.
const ZONE_BIT: u64 = 0b100;

/// Where the header's length field starts.
const LENGTH_SHIFT: u32 = 3;

/// The header's length field, after its shift.
const LENGTH_MASK: u64 = 0b1_1111;

/// The header bits that are zero exactly in a one-word dense code: the form
/// and the length fields.
const ONE_DENSE_MASK: u64 = FORM_MASK | (LENGTH_MASK << LENGTH_SHIFT);

/// The length field of the long form.
const LONG: u64 = 31;

/// The most words a code with its length in the header spans.
const SHORT_WORDS: u64 = 31;

/// The bits of a word.
const WORD_BITS: u64 = 64;

/// The innermost binders a one-word dense code holds.
const INLINE_WIDTH: u64 = 56;

/// The width of a run's first index.
const RUN_START_BITS: u32 = 32;

/// The width of a run's length less one.
const RUN_LENGTH_BITS: u32 = 24;

/// The width of a sparse code's count less one.
const SPARSE_COUNT_BITS: u32 = 24;

/// The width of a sparse code's lower width.
const SPARSE_WIDTH_BITS: u32 = 6;

/// The bits a sparse code's two fields take before its lower bits.
const SPARSE_FIELDS: u64 = 30;

/// The most indices a run or a sparse code holds.
const COUNT_CEILING: u64 = 1 << 24;

/// The dense form's field value.
const DENSE: u64 = 0;

/// The sparse form's field value.
const SPARSE: u64 = 1;

/// The run form's field value.
const RUN: u64 = 2;

/// The handle form's field value: written only by a store.
const HANDLE: u64 = 3;

/// One word of a code.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(super) struct Word(pub u64);

/// A code's words after its first, or a store's whole word arena.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(super) struct Buffer(pub Vec<u64>);

/// A bit position, counted from bit 0 of a sequence's first word.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct Bit(u64);

/// An unsigned value a code holds: a field, an index widened past `u32`, or
/// a distance in bits.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct Raw(pub u64);

/// How many: indices, set or clear bits, or a rank.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct Tally(pub u64);

/// A field's width in bits, or a bit's place in its word.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct Width(u32);

/// A word's place in a sequence.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct WordAt(pub usize);

/// How many words a code or a sequence spans.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct WordCount(usize);

/// Whether a bit is set.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Held
{
    /// The bit is set.
    Set,
    /// The bit is clear.
    Clear,
}

/// Where a code keeps its length.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Layout
{
    /// In the header's length field.
    Short,
    /// In bits 8–63 of word 0, the payload starting at word 1.
    Long,
}

/// Why no code stands for a zone.
pub(super) mod omitted
{
    /// The single reason a selection writes no code for a zone, or a code
    /// holds no rank for an index.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub enum Absent
    {
        /// Nothing stands there.
        Omitted,
    }
}

/// Why a bit search found nothing.
mod searched
{
    /// The single reason a bit search answers no position.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub enum Absent
    {
        /// No bit of the kind sought stands in the range.
        Exhausted,
    }
}

/// Why a walk yields no index.
pub(super) mod walked
{
    /// The single reason a walk over a code answers no index.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub enum Absent
    {
        /// Every index has been read.
        Exhausted,
    }
}

/// The form a zone's code takes, as a reader observes it.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Coding
{
    /// The zone selects nothing, and the selection writes no code for it.
    Omitted,
    /// A bitset over the zone's indices.
    Dense,
    /// The indices as an Elias–Fano sequence.
    Sparse,
    /// A contiguous run of indices.
    Run,
}

/// The form field of a code's header.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Form
{
    /// A bitset.
    Dense,
    /// An Elias–Fano sequence.
    Sparse,
    /// A run.
    Run,
}

/// What a stored word is: a one-word code or a store's handle.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Stored
{
    /// The word is a whole code.
    Code,
    /// The word is a handle; its payload is where the words stand.
    Handle(Raw),
}

/// A code's words: its first word by value and the rest by reference.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct Seq<'words>
{
    /// Word 0.
    pub head: Word,
    /// Words 1 onwards.
    pub tail: &'words [u64],
}

/// A zone's code located in a sequence.
#[derive(Clone, Copy, Debug)]
pub(super) struct Code<'words>
{
    /// The sequence the code stands in.
    seq: Seq<'words>,
    /// The code's form.
    form: Form,
    /// Its first payload bit.
    body: Bit,
    /// The bit after its last word.
    end: Bit,
}

/// A sparse code's fields.
#[derive(Clone, Copy, Debug)]
pub(super) struct Sparse
{
    /// How many indices it holds.
    count: Tally,
    /// The lower width.
    width: Width,
    /// The first lower bit.
    lower: Bit,
    /// The first upper bit.
    upper: Bit,
}

/// The state of a walk over one zone's selected indices.
#[derive(Clone, Debug)]
pub(super) enum Walk<'words>
{
    /// Nothing is left.
    Empty,
    /// The unread bits of a one-word dense code, index 0 at bit 0.
    Inline(u64),
    /// The unread positions of a wider dense code.
    Dense
    {
        /// The sequence read.
        seq: Seq<'words>,
        /// The payload's first bit: index 0.
        base: Bit,
        /// The first unread bit.
        front: Bit,
        /// The bit after the last unread one.
        back: Bit,
        /// How many indices are left.
        left: Tally,
    },
    /// The unread part of a run.
    Run
    {
        /// The next index.
        next: u64,
        /// The index after the last.
        end: u64,
    },
    /// The unread part of an Elias–Fano sequence.
    Sparse
    {
        /// The sequence read.
        seq: Seq<'words>,
        /// The code's fields.
        fields: Sparse,
        /// The first unread upper bit.
        front: Bit,
        /// The bit after the last unread upper bit.
        back: Bit,
        /// The rank of the next index from the front.
        first: Tally,
        /// The rank after the next index from the back.
        last: Tally,
    },
}

impl From<WordCount> for usize
{
    /// The number of words.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: WordCount) -> Self
    {
        count.0
    }
}

impl Width
{
    /// The width of `bits` bits.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn of(bits: Raw) -> Self
    {
        Self(u32::try_from(bits.0.min(64)).unwrap_or(64))
    }

    /// The mask of this many low bits.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    const fn mask(self) -> Raw
    {
        if self.0 >= 64 {
            Raw(u64::MAX)
        }
        else {
            Raw(1_u64.unbounded_shl(self.0).wrapping_sub(1))
        }
    }
}

impl Bit
{
    /// The bit `by` past this one.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    const fn past(
        self,
        by: Raw,
    ) -> Self
    {
        Self(self.0.saturating_add(by.0))
    }

    /// Bit 0 of word `word`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn of_word(word: WordAt) -> Self
    {
        Self(
            u64::try_from(word.0)
                .unwrap_or(u64::MAX)
                .saturating_mul(WORD_BITS),
        )
    }

    /// The word this bit stands in.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn word(self) -> WordAt
    {
        WordAt(usize::try_from(self.0.wrapping_shr(6)).unwrap_or(usize::MAX))
    }

    /// The bit's place in its word.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn place(self) -> Width
    {
        Width::of(Raw(self.0 & 63))
    }

    /// The distance from `from` to this bit.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    const fn since(
        self,
        from: Self,
    ) -> Raw
    {
        Raw(self.0.saturating_sub(from.0))
    }
}

impl Word
{
    /// The one-word dense intuitionistic code selecting `index` alone, when
    /// the index is inside the word.
    ///
    /// # Specification
    /// - ensures: a word whose header is zero and whose only set bit is the
    ///   payload's bit `index`, eight bits past the header, for an index below
    ///   the inline width; otherwise [`omitted::Absent::Omitted`].
    /// - panics: none.
    /// - executable: none — this runs once per name on the mint and check
    ///   paths, where the instrumented body is a closure the test profile does
    ///   not inline; the witness compares the word with the encoder's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the last inline index and the first past it.
    /// - witness: `support::tests::the_mode_switches_at_its_boundaries`
    #[inline]
    pub(super) fn inline_bit(index: DeBruijnIndex) -> Maybe<Self, omitted::Absent>
    {
        let index = u64::from(u32::from(index));
        if index < INLINE_WIDTH {
            Maybe::Present(Self(1_u64.unbounded_shl(
                u32::try_from(index).unwrap_or(u32::MAX).saturating_add(8),
            )))
        }
        else {
            Maybe::Absent(omitted::Absent::Omitted)
        }
    }

    /// This word, when it is a whole one-word dense intuitionistic code: a
    /// zero header.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(super) const fn inline_dense(self) -> Maybe<Self, omitted::Absent>
    {
        if self.0 & HEADER_MASK == 0 {
            Maybe::Present(self)
        }
        else {
            Maybe::Absent(omitted::Absent::Omitted)
        }
    }

    /// A one-word dense intuitionistic code read past `crossed` binders:
    /// every index inside the crossing dropped, every other lowered by it.
    ///
    /// # Specification
    /// - requires: the word is a one-word dense intuitionistic code.
    /// - ensures: the code of the outer indices, each lowered by `crossed`.
    /// - panics: none.
    /// - executable: none — this runs once per child on the mint and check
    ///   paths, as [`Self::inline_bit`]; the witnesses compare every lowered
    ///   union with an independent reference union.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — crossings of none, some and every inline binder.
    /// - witness: `support::tests::a_cover_unions_its_children`
    /// - witness: `support::tests::union_is_canonical`
    #[inline]
    pub(super) fn lowered(
        self,
        crossed: BinderDepth,
    ) -> Self
    {
        let crossed = u64::try_from(usize::from(crossed)).unwrap_or(u64::MAX);
        if crossed >= WORD_BITS {
            return Self(0);
        }
        // reason: `crossed` is below the word's width, so it fits a `u32`,
        // and a zero header keeps the uncrossed word whole under the mask.
        Self(
            self.0
                .wrapping_shr(u32::try_from(crossed).unwrap_or(u32::MAX))
                & !HEADER_MASK,
        )
    }

    /// The payload of a one-word dense code, index 0 at bit 0.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    const fn payload(self) -> Raw
    {
        Raw(self.0.wrapping_shr(8))
    }

    /// This header with its zone bit naming `zone`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(super) const fn in_zone(
        self,
        zone: Zone,
    ) -> Self
    {
        match zone {
            Zone::Intuitionistic => Self(self.0 & !ZONE_BIT),
            Zone::Linear => Self(self.0 | ZONE_BIT),
        }
    }

    /// What this stored word is: a code, or a handle carrying a payload.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(super) const fn stored(self) -> Stored
    {
        if self.0 & FORM_MASK == HANDLE {
            Stored::Handle(Raw(self.0.wrapping_shr(8)))
        }
        else {
            Stored::Code
        }
    }

    /// The handle word whose payload is `at`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(super) const fn handle(at: Raw) -> Self
    {
        Self(HANDLE | at.0.unbounded_shl(8))
    }

    /// The zone the header names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    const fn zone(self) -> Zone
    {
        if self.0 & ZONE_BIT == 0 {
            Zone::Intuitionistic
        }
        else {
            Zone::Linear
        }
    }
}

impl<'words> Seq<'words>
{
    /// Word `at`, or the zero word past the end.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn word(
        self,
        at: WordAt,
    ) -> Word
    {
        at.0.checked_sub(1).map_or(self.head, |rest| {
            Word(self.tail.get(rest).copied().unwrap_or(0))
        })
    }

    /// How many words the sequence spans.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(super) const fn len(self) -> WordCount
    {
        WordCount(self.tail.len().saturating_add(1))
    }

    /// Whether bit `at` is set.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn held(
        self,
        at: Bit,
    ) -> Held
    {
        if self.word(at.word()).0.unbounded_shr(at.place().0) & 1 == 1 {
            Held::Set
        }
        else {
            Held::Clear
        }
    }

    /// The `width`-bit field starting at bit `at`, which may span two words.
    ///
    /// # Specification
    /// - requires: `width` is at most 64.
    /// - ensures: bit `j` of the answer is bit `at + j` of the sequence, for
    ///   every `j` below `width`; every higher bit is clear.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — fields inside one word and across a word boundary,
    ///   read back from every sparse and run code the witnesses build.
    /// - witness: `support::tests::one_encoding_per_selection`
    #[spec(ensures: |ret| width.0 >= 64 || ret.0.unbounded_shr(width.0) == 0)]
    #[inline]
    fn field(
        self,
        at: Bit,
        width: Width,
    ) -> Raw
    {
        if width.0 == 0 {
            return Raw(0);
        }
        let place = at.place().0;
        let low = self.word(at.word()).0.unbounded_shr(place);
        let taken = 64_u32.wrapping_sub(place);
        let joined = if taken < width.0 {
            low | self
                .word(WordAt(at.word().0.saturating_add(1)))
                .0
                .unbounded_shl(taken)
        }
        else {
            low
        };
        Raw(joined & width.mask().0)
    }

    /// How many bits are set in `[from, to)`.
    ///
    /// # Specification
    /// - ensures: the number of set bits at positions in the range.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — ranges inside one word, across words and empty,
    ///   through every rank the witnesses read.
    /// - witness: `support::tests::rank_and_select_are_inverse`
    /// - witness: `support::tests::the_mode_switches_at_its_boundaries`
    #[spec(ensures: |ret| ret.0 <= to.0.saturating_sub(from.0))]
    fn ones(
        self,
        from: Bit,
        to: Bit,
    ) -> Tally
    {
        let mut count = 0_u64;
        let mut at = from;
        while at < to {
            let word = at.word();
            let next = Bit::of_word(WordAt(word.0.saturating_add(1))).min(to);
            let span = Width::of(next.since(at));
            let bits = self.word(word).0.unbounded_shr(at.place().0) & span.mask().0;
            count = count.saturating_add(u64::from(bits.count_ones()));
            at = next;
        }
        Tally(count)
    }

    /// The first set bit in `[from, to)`.
    ///
    /// # Specification
    /// - ensures: the least set position in the range, or
    ///   [`searched::Absent::Exhausted`] when none is set.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every dense and sparse walk the witnesses run reads
    ///   its next index through it.
    /// - witness: `support::tests::one_encoding_per_selection`
    #[spec(ensures: |ret| match ret {
        Maybe::Present(found) => found >= from && found < to && self.held(found) == Held::Set,
        Maybe::Absent(searched::Absent::Exhausted) => true,
    })]
    fn next_one(
        self,
        from: Bit,
        to: Bit,
    ) -> Maybe<Bit, searched::Absent>
    {
        let mut at = from;
        while at < to {
            let word = at.word();
            let bits = self.word(word).0.unbounded_shr(at.place().0);
            if bits != 0 {
                let found = at.past(Raw(u64::from(bits.trailing_zeros())));
                return if found < to {
                    Maybe::Present(found)
                }
                else {
                    Maybe::Absent(searched::Absent::Exhausted)
                };
            }
            at = Bit::of_word(WordAt(word.0.saturating_add(1)));
        }
        Maybe::Absent(searched::Absent::Exhausted)
    }

    /// The last set bit in `[from, to)`.
    ///
    /// # Specification
    /// - ensures: the greatest set position in the range, or
    ///   [`searched::Absent::Exhausted`] when none is set.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every walk the witnesses run from the back.
    /// - witness: `support::tests::one_encoding_per_selection`
    #[spec(ensures: |ret| match ret {
        Maybe::Present(found) => found >= from && found < to && self.held(found) == Held::Set,
        Maybe::Absent(searched::Absent::Exhausted) => true,
    })]
    fn last_one(
        self,
        from: Bit,
        to: Bit,
    ) -> Maybe<Bit, searched::Absent>
    {
        let mut end = to;
        while end > from {
            let word = Bit(end.0.saturating_sub(1)).word();
            let base = Bit::of_word(word);
            let bits = self.word(word).0 & Width::of(end.since(base)).mask().0;
            if bits != 0 {
                let found = base.past(Raw(u64::from(63_u32.wrapping_sub(bits.leading_zeros()))));
                return if found >= from {
                    Maybe::Present(found)
                }
                else {
                    Maybe::Absent(searched::Absent::Exhausted)
                };
            }
            end = base;
        }
        Maybe::Absent(searched::Absent::Exhausted)
    }

    /// The bit after the `nth` clear bit at or past `from`, counting from
    /// one: where the upper bits of a sparse code's indices with high part
    /// `nth` start.
    ///
    /// # Specification
    /// - requires: `nth` is at least one.
    /// - ensures: the position after the `nth` clear bit in `[from, to)`, or
    ///   [`searched::Absent::Exhausted`] when fewer stand there.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every sparse rank and cut the witnesses read, with
    ///   high parts in the first word and past it.
    /// - witness: `support::tests::rank_and_select_are_inverse`
    /// - witness: `support::tests::outside_cuts_at_the_crossing`
    #[spec(ensures: |ret| match ret {
        Maybe::Present(after) => after > from && after <= to,
        Maybe::Absent(searched::Absent::Exhausted) => true,
    })]
    fn after_zero(
        self,
        from: Bit,
        to: Bit,
        nth: Tally,
    ) -> Maybe<Bit, searched::Absent>
    {
        let mut left = nth.0;
        let mut at = from;
        while at < to {
            let word = at.word();
            let next = Bit::of_word(WordAt(word.0.saturating_add(1))).min(to);
            let span = Width::of(next.since(at));
            let mut zeros = !self.word(word).0.unbounded_shr(at.place().0) & span.mask().0;
            let here = u64::from(zeros.count_ones());
            if here >= left {
                for _ in 1 .. left {
                    zeros &= zeros.wrapping_sub(1);
                }
                return Maybe::Present(
                    at.past(Raw(u64::from(zeros.trailing_zeros()).saturating_add(1))),
                );
            }
            left = left.saturating_sub(here);
            at = next;
        }
        Maybe::Absent(searched::Absent::Exhausted)
    }

    /// The code that starts at word `at`, and the zone its header names.
    ///
    /// # Specification
    /// - ensures: the code's form, its first payload bit and the bit after its
    ///   last word, read off its header.
    /// - panics: none.
    /// - executable: none — this runs on every read past a one-word dense code,
    ///   as [`Word::inline_bit`]; the witnesses decode every form.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — short and long headers of every form in either zone.
    /// - witness: `support::tests::the_mode_switches_at_its_boundaries`
    #[inline]
    fn code_at(
        self,
        at: WordAt,
    ) -> (Zone, Code<'words>)
    {
        let header = self.word(at);
        let start = Bit::of_word(at);
        let form = match header.0 & FORM_MASK {
            SPARSE => Form::Sparse,
            RUN => Form::Run,
            _ => Form::Dense,
        };
        let length = header.0.wrapping_shr(LENGTH_SHIFT) & LENGTH_MASK;
        let (words, body) = if length == LONG {
            (header.0.wrapping_shr(8), start.past(Raw(WORD_BITS)))
        }
        else {
            (length.saturating_add(1), start.past(Raw(HEADER_BITS)))
        };
        let end = start.past(Raw(words.saturating_mul(WORD_BITS))).max(body);
        (header.zone(), Code {
            seq: self,
            form,
            body,
            end,
        })
    }

    /// The code of `zone`.
    ///
    /// # Specification
    /// - ensures: the code whose header names `zone`: the first code, or the
    ///   linear code standing after an intuitionistic one;
    ///   [`omitted::Absent::Omitted`] when the sequence writes none.
    /// - panics: none.
    /// - executable: none — as [`Self::code_at`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — selections in either zone alone, in both and in
    ///   neither.
    /// - witness: `support::tests::one_encoding_per_selection`
    #[inline]
    pub(super) fn zone(
        self,
        zone: Zone,
    ) -> Maybe<Code<'words>, omitted::Absent>
    {
        let (first, code) = self.code_at(WordAt(0));
        if first == zone {
            return Maybe::Present(code);
        }
        if first == Zone::Intuitionistic && zone == Zone::Linear {
            let at = code.end.word();
            if at.0 < self.len().0 {
                let (second, code) = self.code_at(at);
                if second == Zone::Linear {
                    return Maybe::Present(code);
                }
            }
        }
        Maybe::Absent(omitted::Absent::Omitted)
    }

    /// A walk over the indices of `zone` at or past `from`.
    ///
    /// # Specification
    /// - ensures: exactly the indices the code of `zone` selects not below
    ///   `from`, ascending; none when the sequence writes no code for `zone`.
    /// - panics: none.
    /// - intension: a one-word dense code is read off its word without locating
    ///   it.
    /// - executable: none — this runs on every read of a support, as
    ///   [`Word::inline_bit`]; the witnesses compare every walk with the
    ///   selection it was written from.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Code::walk_from`], through one-word codes of
    ///   either zone and wider sequences of both.
    /// - witness: `support::tests::outside_cuts_at_the_crossing`
    /// - witness: `support::tests::one_encoding_per_selection`
    #[inline]
    pub(super) fn walk(
        self,
        zone: Zone,
        from: Raw,
    ) -> Walk<'words>
    {
        if self.tail.is_empty() && self.head.0 & ONE_DENSE_MASK == 0 {
            return if self.head.zone() == zone {
                Walk::Inline(self.head.payload().0 & !Width::of(from).mask().0)
            }
            else {
                Walk::Empty
            };
        }
        match self.zone(zone) {
            Maybe::Present(code) => code.walk_from(from),
            Maybe::Absent(omitted::Absent::Omitted) => Walk::Empty,
        }
    }

    /// The rank of `index` among the indices of `zone`, when it is selected.
    ///
    /// # Specification
    /// - ensures: as [`Code::rank`] over the code of `zone`;
    ///   [`omitted::Absent::Omitted`] when the sequence writes none.
    /// - panics: none.
    /// - intension: a one-word dense code ranks by one population count.
    /// - executable: none — this runs once per child index on the cover path,
    ///   as [`Word::inline_bit`]; the witnesses rank every selected index.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Code::rank`].
    /// - witness: `support::tests::rank_and_select_are_inverse`
    #[inline]
    pub(super) fn rank(
        self,
        zone: Zone,
        index: DeBruijnIndex,
    ) -> Maybe<Tally, omitted::Absent>
    {
        if self.tail.is_empty() && self.head.0 & ONE_DENSE_MASK == 0 {
            let payload = self.head.payload().0;
            let at = u32::from(index);
            return if self.head.zone() == zone
                && u64::from(at) < INLINE_WIDTH
                && payload.unbounded_shr(at) & 1 == 1
            {
                Maybe::Present(Tally(u64::from(
                    (payload & 1_u64.unbounded_shl(at).wrapping_sub(1)).count_ones(),
                )))
            }
            else {
                Maybe::Absent(omitted::Absent::Omitted)
            };
        }
        match self.zone(zone) {
            Maybe::Present(code) => code.rank(index),
            Maybe::Absent(omitted::Absent::Omitted) => Maybe::Absent(omitted::Absent::Omitted),
        }
    }
}

impl<'words> Code<'words>
{
    /// The code's form, as a reader observes it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(super) const fn coding(self) -> Coding
    {
        match self.form {
            Form::Dense => Coding::Dense,
            Form::Sparse => Coding::Sparse,
            Form::Run => Coding::Run,
        }
    }

    /// A sparse code's fields.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn sparse(self) -> Sparse
    {
        let count = Tally(
            self.seq
                .field(self.body, Width(SPARSE_COUNT_BITS))
                .0
                .saturating_add(1),
        );
        let width = Width::of(self.seq.field(
            self.body.past(Raw(u64::from(SPARSE_COUNT_BITS))),
            Width(SPARSE_WIDTH_BITS),
        ));
        let lower = self.body.past(Raw(SPARSE_FIELDS));
        let upper = lower.past(Raw(count.0.saturating_mul(u64::from(width.0))));
        Sparse {
            count,
            width,
            lower,
            upper,
        }
    }

    /// A run's first index and its length.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn run(self) -> (Raw, Tally)
    {
        let start = self.seq.field(self.body, Width(RUN_START_BITS));
        let length = self.seq.field(
            self.body.past(Raw(u64::from(RUN_START_BITS))),
            Width(RUN_LENGTH_BITS),
        );
        (start, Tally(length.0.saturating_add(1)))
    }

    /// A walk over every index the code selects.
    ///
    /// # Specification
    /// - ensures: the walk yields the code's indices, ascending from the front
    ///   and descending from the back.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — codes of every form, decoded and compared with the
    ///   selection they were written from.
    /// - witness: `support::tests::one_encoding_per_selection`
    #[spec(ensures: |ret| match ret {
        Walk::Empty => false,
        Walk::Inline(_) | Walk::Dense { .. } | Walk::Run { .. } | Walk::Sparse { .. } => true,
    })]
    #[inline]
    pub(super) fn walk(self) -> Walk<'words>
    {
        match self.form {
            Form::Dense => {
                if self.end.since(self.body).0 <= INLINE_WIDTH {
                    Walk::Inline(self.seq.word(self.body.word()).payload().0)
                }
                else {
                    Walk::Dense {
                        seq: self.seq,
                        base: self.body,
                        front: self.body,
                        back: self.end,
                        left: self.seq.ones(self.body, self.end),
                    }
                }
            },
            Form::Run => {
                let (start, length) = self.run();
                Walk::Run {
                    next: start.0,
                    end: start.0.saturating_add(length.0),
                }
            },
            Form::Sparse => {
                let fields = self.sparse();
                Walk::Sparse {
                    seq: self.seq,
                    fields,
                    front: fields.upper,
                    back: self.end,
                    first: Tally(0),
                    last: fields.count,
                }
            },
        }
    }

    /// A walk over the indices the code selects at or past `from`.
    ///
    /// # Specification
    /// - ensures: exactly the code's indices not below `from`, ascending.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — cuts below, at and past selections of every form.
    /// - witness: `support::tests::outside_cuts_at_the_crossing`
    #[spec(ensures: |ret| matches!(ret.clone().first_below(from), Maybe::Absent(_)))]
    #[inline]
    pub(super) fn walk_from(
        self,
        from: Raw,
    ) -> Walk<'words>
    {
        if from.0 == 0 {
            return self.walk();
        }
        match self.walk() {
            Walk::Inline(bits) => Walk::Inline(bits & !Width::of(from).mask().0),
            Walk::Dense {
                seq, base, back, ..
            } => {
                let front = base.past(from).min(back);
                Walk::Dense {
                    seq,
                    base,
                    front,
                    back,
                    left: seq.ones(front, back),
                }
            },
            Walk::Run { next, end } => Walk::Run {
                next: next.max(from.0),
                end,
            },
            Walk::Sparse {
                seq,
                fields,
                back,
                last,
                ..
            } => {
                let high = from.0.unbounded_shr(fields.width.0);
                let front = if high == 0 {
                    fields.upper
                }
                else {
                    match seq.after_zero(fields.upper, back, Tally(high)) {
                        Maybe::Present(after) => after,
                        Maybe::Absent(searched::Absent::Exhausted) => back,
                    }
                };
                let mut walk = Walk::Sparse {
                    seq,
                    fields,
                    front,
                    back,
                    first: seq.ones(fields.upper, front),
                    last,
                };
                loop {
                    let before = walk.clone();
                    match walk.front() {
                        Maybe::Present(index) if u64::from(u32::from(index)) < from.0 => {},
                        Maybe::Present(_) => return before,
                        Maybe::Absent(walked::Absent::Exhausted) => return walk,
                    }
                }
            },
            Walk::Empty => Walk::Empty,
        }
    }

    /// The rank of `index` among the code's indices, when it selects it.
    ///
    /// # Specification
    /// - ensures: how many selected indices lie below `index` when the code
    ///   selects it; [`omitted::Absent::Omitted`] otherwise.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every index of exhaustive small selections and of
    ///   wide selections of every form.
    /// - witness: `support::tests::rank_and_select_are_inverse`
    #[spec(ensures: |ret| match ret {
        Maybe::Present(rank) => self.walk().nth_index(rank) == Maybe::Present(index),
        Maybe::Absent(omitted::Absent::Omitted) => true,
    })]
    #[inline]
    pub(super) fn rank(
        self,
        index: DeBruijnIndex,
    ) -> Maybe<Tally, omitted::Absent>
    {
        let wide = u64::from(u32::from(index));
        match self.form {
            Form::Dense => {
                let at = self.body.past(Raw(wide));
                if at < self.end && self.seq.held(at) == Held::Set {
                    Maybe::Present(self.seq.ones(self.body, at))
                }
                else {
                    Maybe::Absent(omitted::Absent::Omitted)
                }
            },
            Form::Run => {
                let (start, length) = self.run();
                match wide.checked_sub(start.0) {
                    Some(rank) if rank < length.0 => Maybe::Present(Tally(rank)),
                    Some(_) | None => Maybe::Absent(omitted::Absent::Omitted),
                }
            },
            Form::Sparse => {
                let mut walk = self.walk_from(Raw(wide));
                let rank = match walk {
                    Walk::Sparse { first, .. } => first,
                    Walk::Empty | Walk::Inline(_) | Walk::Dense { .. } | Walk::Run { .. } => {
                        Tally(0)
                    },
                };
                match walk.front() {
                    Maybe::Present(found) if found == index => Maybe::Present(rank),
                    Maybe::Present(_) | Maybe::Absent(walked::Absent::Exhausted) => {
                        Maybe::Absent(omitted::Absent::Omitted)
                    },
                }
            },
        }
    }
}

impl Walk<'_>
{
    /// The next index from the front.
    ///
    /// # Specification
    /// - ensures: the least unread index, which leaves the walk;
    ///   [`walked::Absent::Exhausted`] when none is left.
    /// - panics: none.
    /// - executable: none — the walk is read through itself; the witnesses
    ///   compare every walk with the selection it was written from.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Code::walk`].
    /// - witness: `support::tests::one_encoding_per_selection`
    #[inline]
    pub(super) fn front(&mut self) -> Maybe<DeBruijnIndex, walked::Absent>
    {
        match *self {
            Self::Empty => Maybe::Absent(walked::Absent::Exhausted),
            Self::Inline(ref mut bits) => {
                if *bits == 0 {
                    return Maybe::Absent(walked::Absent::Exhausted);
                }
                let at = bits.trailing_zeros();
                *bits &= bits.wrapping_sub(1);
                Maybe::Present(DeBruijnIndex::from(at))
            },
            Self::Dense {
                seq,
                base,
                ref mut front,
                back,
                ref mut left,
            } => {
                if left.0 == 0 {
                    return Maybe::Absent(walked::Absent::Exhausted);
                }
                match seq.next_one(*front, back) {
                    Maybe::Present(found) => {
                        *front = found.past(Raw(1));
                        left.0 = left.0.saturating_sub(1);
                        Maybe::Present(index_of(found.since(base)))
                    },
                    Maybe::Absent(searched::Absent::Exhausted) => {
                        left.0 = 0;
                        Maybe::Absent(walked::Absent::Exhausted)
                    },
                }
            },
            Self::Run { ref mut next, end } => {
                if *next >= end {
                    return Maybe::Absent(walked::Absent::Exhausted);
                }
                let at = *next;
                *next = next.saturating_add(1);
                Maybe::Present(index_of(Raw(at)))
            },
            Self::Sparse {
                seq,
                fields,
                ref mut front,
                back,
                ref mut first,
                last,
            } => {
                if first.0 >= last.0 {
                    return Maybe::Absent(walked::Absent::Exhausted);
                }
                match seq.next_one(*front, back) {
                    Maybe::Present(found) => {
                        let rank = *first;
                        *front = found.past(Raw(1));
                        first.0 = first.0.saturating_add(1);
                        Maybe::Present(sparse_index(seq, fields, found, rank))
                    },
                    Maybe::Absent(searched::Absent::Exhausted) => {
                        *first = last;
                        Maybe::Absent(walked::Absent::Exhausted)
                    },
                }
            },
        }
    }

    /// The next index from the back.
    ///
    /// # Specification
    /// - ensures: the greatest unread index, which leaves the walk;
    ///   [`walked::Absent::Exhausted`] when none is left.
    /// - panics: none.
    /// - executable: none — as [`Self::front`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Code::walk`], read from the back.
    /// - witness: `support::tests::one_encoding_per_selection`
    #[inline]
    pub(super) fn back(&mut self) -> Maybe<DeBruijnIndex, walked::Absent>
    {
        match *self {
            Self::Empty => Maybe::Absent(walked::Absent::Exhausted),
            Self::Inline(ref mut bits) => {
                if *bits == 0 {
                    return Maybe::Absent(walked::Absent::Exhausted);
                }
                let at = 63_u32.wrapping_sub(bits.leading_zeros());
                *bits &= !1_u64.unbounded_shl(at);
                Maybe::Present(DeBruijnIndex::from(at))
            },
            Self::Dense {
                seq,
                base,
                front,
                ref mut back,
                ref mut left,
            } => {
                if left.0 == 0 {
                    return Maybe::Absent(walked::Absent::Exhausted);
                }
                match seq.last_one(front, *back) {
                    Maybe::Present(found) => {
                        *back = found;
                        left.0 = left.0.saturating_sub(1);
                        Maybe::Present(index_of(found.since(base)))
                    },
                    Maybe::Absent(searched::Absent::Exhausted) => {
                        left.0 = 0;
                        Maybe::Absent(walked::Absent::Exhausted)
                    },
                }
            },
            Self::Run { next, ref mut end } => {
                if next >= *end {
                    return Maybe::Absent(walked::Absent::Exhausted);
                }
                *end = end.saturating_sub(1);
                Maybe::Present(index_of(Raw(*end)))
            },
            Self::Sparse {
                seq,
                fields,
                front,
                ref mut back,
                first,
                ref mut last,
            } => {
                if first.0 >= last.0 {
                    return Maybe::Absent(walked::Absent::Exhausted);
                }
                match seq.last_one(front, *back) {
                    Maybe::Present(found) => {
                        *back = found;
                        last.0 = last.0.saturating_sub(1);
                        Maybe::Present(sparse_index(seq, fields, found, *last))
                    },
                    Maybe::Absent(searched::Absent::Exhausted) => {
                        *last = first;
                        Maybe::Absent(walked::Absent::Exhausted)
                    },
                }
            },
        }
    }

    /// How many indices are left.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(super) fn left(&self) -> Tally
    {
        Tally(match *self {
            Self::Empty => 0,
            Self::Inline(bits) => u64::from(bits.count_ones()),
            Self::Dense { left, .. } => left.0,
            Self::Run { next, end } => end.saturating_sub(next),
            Self::Sparse { first, last, .. } => last.0.saturating_sub(first.0),
        })
    }

    /// The first index a walk yields below `from`, if any: the predicate the
    /// cut's specification reads.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn first_below(
        mut self,
        from: Raw,
    ) -> Maybe<DeBruijnIndex, walked::Absent>
    {
        loop {
            match self.front() {
                Maybe::Present(index) if u64::from(u32::from(index)) < from.0 => {
                    return Maybe::Present(index);
                },
                Maybe::Present(_) => {},
                Maybe::Absent(walked::Absent::Exhausted) => {
                    return Maybe::Absent(walked::Absent::Exhausted);
                },
            }
        }
    }

    /// The walk's `rank`-th index: the predicate a rank's specification reads.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn nth_index(
        mut self,
        rank: Tally,
    ) -> Maybe<DeBruijnIndex, walked::Absent>
    {
        for _ in 0 .. rank.0 {
            if let Maybe::Absent(absent) = self.front() {
                return Maybe::Absent(absent);
            }
        }
        self.front()
    }
}

/// `at` as an index, clamped to the index space.
///
/// # Specification
/// trivial.
#[inline]
fn index_of(at: Raw) -> DeBruijnIndex
{
    DeBruijnIndex::from(u32::try_from(at.0).unwrap_or(u32::MAX))
}

/// The index a sparse code's upper bit `found` stands for, the code's
/// `rank`-th.
///
/// # Specification
/// trivial.
#[inline]
fn sparse_index(
    seq: Seq<'_>,
    fields: Sparse,
    found: Bit,
    rank: Tally,
) -> DeBruijnIndex
{
    let high = found.since(fields.upper).0.saturating_sub(rank.0);
    let low = seq.field(
        fields
            .lower
            .past(Raw(rank.0.saturating_mul(u64::from(fields.width.0)))),
        fields.width,
    );
    index_of(Raw(high.unbounded_shl(fields.width.0) | low.0))
}

/// The words a code spans when its payload is `payload` bits, and where it
/// keeps its length: in the header while that fits, and in the long form
/// past it.
///
/// # Specification
/// trivial.
#[inline]
fn words_for(payload: Raw) -> (Tally, Layout)
{
    let short = payload
        .0
        .saturating_add(HEADER_BITS)
        .saturating_add(WORD_BITS.wrapping_sub(1))
        .wrapping_shr(6);
    if short <= SHORT_WORDS {
        (Tally(short), Layout::Short)
    }
    else {
        let long = payload
            .0
            .saturating_add(WORD_BITS.wrapping_sub(1))
            .wrapping_shr(6)
            .saturating_add(1);
        (Tally(long), Layout::Long)
    }
}

/// The lower width an Elias–Fano sequence of `count` indices below
/// `universe` takes: the floor of `log2(universe / count)`, or zero.
///
/// # Specification
/// trivial.
#[inline]
fn lower_width(
    count: Tally,
    universe: Raw,
) -> Width
{
    if count.0 == 0 || universe.0 <= count.0 {
        return Width(0);
    }
    let ratio = universe.0.checked_div(count.0).unwrap_or(1);
    Width(63_u32.wrapping_sub(ratio.leading_zeros()))
}

/// A selection's form and length, as the encoder chooses them.
#[derive(Clone, Copy, Debug)]
struct Choice
{
    /// The form written.
    form: Form,
    /// Its length in words.
    words: Tally,
    /// Where it keeps its length.
    layout: Layout,
}

/// The form the encoder writes `indices` in: the shortest, dense on a tie and
/// run before sparse.
///
/// # Specification
/// - requires: `indices` strictly ascends.
/// - ensures: the dense form when no other is shorter; the run form when the
///   indices are contiguous and its one word is shorter than the dense code;
///   the sparse form when it is shorter than both.
/// - panics: none.
/// - executable: none — the clause is the rule the body states; the witnesses
///   hold the choice to an independent sizing of every form.
///
/// # Adequacy
/// - hypothesis: L3 — selections at either side of each switch: the inline
///   width, a run's start past it, and densities at which sparse and dense
///   cross.
/// - witness: `support::tests::the_mode_switches_at_its_boundaries`
fn choose(indices: &[DeBruijnIndex]) -> Choice
{
    let (Some(&first), Some(&last)) = (indices.first(), indices.last())
    else {
        return Choice {
            form: Form::Dense,
            words: Tally(1),
            layout: Layout::Short,
        };
    };
    let count = u64::try_from(indices.len()).unwrap_or(u64::MAX);
    let first = u64::from(u32::from(first));
    let last = u64::from(u32::from(last));
    let (dense, layout) = words_for(Raw(last.saturating_add(1)));
    let mut chosen = Choice {
        form: Form::Dense,
        words: dense,
        layout,
    };
    let contiguous = last.saturating_sub(first).saturating_add(1) == count;
    if count <= COUNT_CEILING && contiguous && chosen.words.0 > 1 {
        chosen = Choice {
            form: Form::Run,
            words: Tally(1),
            layout: Layout::Short,
        };
    }
    if count <= COUNT_CEILING {
        let width = lower_width(Tally(count), Raw(last.saturating_add(1)));
        let payload = SPARSE_FIELDS
            .saturating_add(count.saturating_mul(u64::from(width.0)))
            .saturating_add(count)
            .saturating_add(last.unbounded_shr(width.0));
        let (sparse, layout) = words_for(Raw(payload));
        if sparse < chosen.words {
            chosen = Choice {
                form: Form::Sparse,
                words: sparse,
                layout,
            };
        }
    }
    chosen
}

/// A code under construction: words appended to a buffer.
#[repr(transparent)]
struct Writer<'out>
{
    /// The buffer being written.
    words: &'out mut Vec<u64>,
}

impl Writer<'_>
{
    /// Set bit `at`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn set(
        &mut self,
        at: Bit,
    )
    {
        if let Some(word) = self.words.get_mut(at.word().0) {
            *word |= 1_u64.unbounded_shl(at.place().0);
        }
    }

    /// Write the low `width` bits of `value` from bit `at`, which may span
    /// two words.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn put(
        &mut self,
        at: Bit,
        width: Width,
        value: Raw,
    )
    {
        if width.0 == 0 {
            return;
        }
        let value = value.0 & width.mask().0;
        let place = at.place().0;
        if let Some(word) = self.words.get_mut(at.word().0) {
            *word |= value.unbounded_shl(place);
        }
        let taken = 64_u32.wrapping_sub(place);
        if taken < width.0
            && let Some(word) = self.words.get_mut(at.word().0.saturating_add(1))
        {
            *word |= value.unbounded_shr(taken);
        }
    }
}

/// Append the code of `zone`'s selection `indices` to `out`.
///
/// # Specification
/// - requires: `indices` strictly ascends.
/// - ensures: `out` gains the one code the encoder writes for the selection:
///   the form [`choose`] picks, a header naming the form, the zone and the
///   length, and a payload the readers decode back to `indices`.
/// - panics: none.
/// - executable: none — the code is observed by decoding it; the witnesses
///   decode every code they build and re-encode it to the same words.
///
/// # Adequacy
/// - hypothesis: L3 — every selection the witnesses generate, of every form,
///   decoded back and re-encoded to the same words.
/// - witness: `support::tests::one_encoding_per_selection`
/// - witness: `support::tests::the_mode_switches_at_its_boundaries`
pub(super) fn encode(
    zone: Zone,
    indices: &[DeBruijnIndex],
    out: &mut Buffer,
)
{
    let choice = choose(indices);
    let start = out.0.len();
    out.0.resize(
        start.saturating_add(usize::try_from(choice.words.0).unwrap_or(usize::MAX)),
        0,
    );
    let form = match choice.form {
        Form::Dense => DENSE,
        Form::Sparse => SPARSE,
        Form::Run => RUN,
    };
    let zone_bit = match zone {
        Zone::Intuitionistic => 0,
        Zone::Linear => ZONE_BIT,
    };
    let base = Bit::of_word(WordAt(start));
    let (length, body) = match choice.layout {
        Layout::Long => (LONG, base.past(Raw(WORD_BITS))),
        Layout::Short => (
            choice.words.0.saturating_sub(1),
            base.past(Raw(HEADER_BITS)),
        ),
    };
    let mut writer = Writer { words: &mut out.0 };
    writer.put(
        base,
        Width(8),
        Raw(form | zone_bit | length.unbounded_shl(LENGTH_SHIFT)),
    );
    if choice.layout == Layout::Long {
        writer.put(base.past(Raw(HEADER_BITS)), Width(56), Raw(choice.words.0));
    }
    let count = u64::try_from(indices.len()).unwrap_or(u64::MAX);
    match choice.form {
        Form::Dense => {
            for &index in indices {
                writer.set(body.past(Raw(u64::from(u32::from(index)))));
            }
        },
        Form::Run => {
            let first = indices
                .first()
                .map_or(0, |&index| u64::from(u32::from(index)));
            writer.put(body, Width(RUN_START_BITS), Raw(first));
            writer.put(
                body.past(Raw(u64::from(RUN_START_BITS))),
                Width(RUN_LENGTH_BITS),
                Raw(count.saturating_sub(1)),
            );
        },
        Form::Sparse => {
            let last = indices
                .last()
                .map_or(0, |&index| u64::from(u32::from(index)));
            let width = lower_width(Tally(count), Raw(last.saturating_add(1)));
            writer.put(body, Width(SPARSE_COUNT_BITS), Raw(count.saturating_sub(1)));
            writer.put(
                body.past(Raw(u64::from(SPARSE_COUNT_BITS))),
                Width(SPARSE_WIDTH_BITS),
                Raw(u64::from(width.0)),
            );
            let lower = body.past(Raw(SPARSE_FIELDS));
            let upper = lower.past(Raw(count.saturating_mul(u64::from(width.0))));
            for (rank, &index) in (0_u64 ..).zip(indices) {
                let index = u64::from(u32::from(index));
                writer.put(
                    lower.past(Raw(rank.saturating_mul(u64::from(width.0)))),
                    width,
                    Raw(index),
                );
                writer.set(upper.past(Raw(index.unbounded_shr(width.0).saturating_add(rank))));
            }
        },
    }
}

/// The one-word code selecting `index` alone in `zone`: dense inside the
/// inline width, a run of one past it.
///
/// # Specification
/// - ensures: the word [`encode`] writes for the selection `[index]`.
/// - panics: none.
/// - executable: none — the witness compares it with the encoder's word.
///
/// # Adequacy
/// - hypothesis: L3 — the last inline index and the first past it, in either
///   zone.
/// - witness: `support::tests::the_mode_switches_at_its_boundaries`
#[inline]
pub(super) fn single(
    zone: Zone,
    index: DeBruijnIndex,
) -> Word
{
    match Word::inline_bit(index) {
        Maybe::Present(bit) => bit.in_zone(zone),
        Maybe::Absent(omitted::Absent::Omitted) => {
            Word(RUN | u64::from(u32::from(index)).unbounded_shl(8)).in_zone(zone)
        },
    }
}
