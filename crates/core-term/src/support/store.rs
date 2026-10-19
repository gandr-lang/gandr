//! Where a table keeps supports: a one-word slot per node, the codes wider
//! than a word in a word arena behind it.

use alloc::vec::Vec;

use quenchant_shape::shape::Maybe;

use super::Thinning;
use super::ThinningRef;
use super::Union;
use super::code::Buffer;
use super::code::Raw;
use super::code::Seq;
use super::code::Stored;
use super::code::Word;
use crate::syntax::Zone;

/// Why a word arena reads no code for a slot.
pub mod unstored
{
    /// The single reason a slot's handle reaches no code.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub enum Absent
    {
        /// The handle points past the arena's words.
        Unstored,
    }
}

/// A support as a table row keeps it: a one-word code itself, or a handle to
/// a wider code's words in a [`WordArena`].
///
/// # Specification
/// - executable: none — a data declaration; only [`WordArena::store`] and
///   [`WordArena::store_union`] make one, so a handle names words that arena
///   wrote.
///
/// # Adequacy
/// - hypothesis: L3 — supports of one word and of several are stored and read
///   back as the thinnings they were.
/// - witness: `support::tests::a_stored_support_reads_back`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct Slot(Word);

/// The words of every support wider than one word, each entry its length
/// and then its code.
///
/// # Specification
/// - executable: none — a data declaration; every entry is written by
///   [`Self::store`] and read back whole by [`Self::read`].
///
/// # Adequacy
/// - hypothesis: L3 — as [`Slot`], and a truncation to a mark keeps exactly the
///   entries stored before it.
/// - witness: `support::tests::a_stored_support_reads_back`
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct WordArena
{
    /// The entries, back to back.
    words: Buffer,
}

/// A word arena's length, to truncate it back to.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct WordMark(usize);

impl From<WordMark> for usize
{
    /// The mark, counted in words.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(mark: WordMark) -> Self
    {
        mark.0
    }
}

impl WordArena
{
    /// The empty arena.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new() -> Self
    {
        Self {
            words: Buffer(Vec::new()),
        }
    }

    /// Keep `thinning`: its one word in the slot, or its words in the arena
    /// behind a handle.
    ///
    /// # Specification
    /// - ensures: [`Self::read`] of the slot is the thinning's view; the arena
    ///   grows only when the code spans more than one word.
    /// - panics: none.
    /// - executable: none — the slot is observed through [`Self::read`]; the
    ///   witness reads every slot it stores.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one-word and wider supports, stored in turn.
    /// - witness: `support::tests::a_stored_support_reads_back`
    #[inline]
    pub fn store(
        &mut self,
        thinning: &Thinning,
    ) -> Slot
    {
        thinning
            .tail
            .as_deref()
            .map_or(Slot(thinning.head), |tail| {
                self.store_words(Seq {
                    head: thinning.head,
                    tail,
                })
            })
    }

    /// Keep the support `union` finishes, without an owned thinning when it
    /// is one word.
    ///
    /// # Specification
    /// - ensures: as [`Self::store`] of `union.finish()`.
    /// - panics: none.
    /// - executable: none — as [`Self::store`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — inline and gathered unions, stored in turn.
    /// - witness: `support::tests::a_stored_support_reads_back`
    #[inline]
    pub fn store_union(
        &mut self,
        union: Union,
    ) -> Slot
    {
        match union.listed {
            None => Slot(union.inline),
            Some(lists) => self.store(&Union::finish_listed(*lists)),
        }
    }

    /// Append a wide code's words and answer the handle to them.
    ///
    /// # Specification
    /// trivial.
    #[cold]
    fn store_words(
        &mut self,
        code: Seq<'_>,
    ) -> Slot
    {
        let at = self.words.0.len();
        let count = u64::try_from(code.tail.len().saturating_add(1)).unwrap_or(u64::MAX);
        self.words.0.reserve(code.tail.len().saturating_add(2));
        self.words.0.push(count);
        self.words.0.push(code.head.0);
        self.words.0.extend_from_slice(code.tail);
        Slot(Word::handle(Raw(u64::try_from(at).unwrap_or(u64::MAX))))
    }

    /// The support `slot` keeps, read in place.
    ///
    /// # Specification
    /// - ensures: the view of the thinning [`Self::store`] kept in the slot;
    ///   [`unstored::Absent::Unstored`] for a handle past the arena, which only
    ///   a slot of another arena or a truncated entry can be.
    /// - panics: none.
    /// - executable: none — as [`Self::store`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::store`], and a slot read after its entry
    ///   was truncated away.
    /// - witness: `support::tests::a_stored_support_reads_back`
    #[inline]
    pub fn read(
        &self,
        slot: Slot,
    ) -> Maybe<ThinningRef<'_>, unstored::Absent>
    {
        match slot.0.stored() {
            Stored::Code => Maybe::Present(ThinningRef::of_seq(Seq {
                head: slot.0,
                tail: &[],
            })),
            Stored::Handle(at) => self.read_words(at),
        }
    }

    /// The entry a handle names.
    ///
    /// # Specification
    /// trivial.
    #[cold]
    fn read_words(
        &self,
        at: Raw,
    ) -> Maybe<ThinningRef<'_>, unstored::Absent>
    {
        let entry = usize::try_from(at.0)
            .ok()
            .and_then(|at| self.words.0.get(at ..))
            .and_then(|entry| {
                let (&count, rest) = entry.split_first()?;
                let count = usize::try_from(count).ok()?;
                let code = rest.get(.. count)?;
                let (&head, tail) = code.split_first()?;
                Some(ThinningRef::of_seq(Seq {
                    head: Word(head),
                    tail,
                }))
            });
        entry.map_or(Maybe::Absent(unstored::Absent::Unstored), Maybe::Present)
    }

    /// The arena's length now, to truncate back to.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn mark(&self) -> WordMark
    {
        WordMark(self.words.0.len())
    }

    /// Drop every entry stored since `mark`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn truncate(
        &mut self,
        mark: WordMark,
    )
    {
        self.words.0.truncate(mark.0);
    }
}

impl Union
{
    /// Add every index the support `slot` keeps selects past `crossing`: as
    /// [`Union::child`] of the slot's view in `words`, without reading it
    /// when the slot holds a one-word dense intuitionistic code.
    ///
    /// # Specification
    /// - ensures: as [`Union::child`] of the support [`WordArena::read`]
    ///   answers for `slot`; nothing for a handle past `words`.
    /// - panics: none.
    /// - executable: none — this runs once per child on the mint and check
    ///   paths, as [`Union::child`]; the witness holds it to that union.
    /// - intension: a shift, a mask and a disjunction while the union and the
    ///   slot are one-word dense intuitionistic codes.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Union::child`], over slots of one word and
    ///   handles, crossings in either zone and unions inline and gathered.
    /// - witness: `support::tests::a_slot_unions_and_compares_as_its_support`
    #[inline]
    pub fn stored_child(
        &mut self,
        slot: Slot,
        words: &WordArena,
        crossing: super::Crossing,
    )
    {
        if self.listed.is_none()
            && let Maybe::Present(word) = slot.0.inline_dense()
        {
            self.inline.0 |= word.lowered(crossing.depth(Zone::Intuitionistic)).0;
            return;
        }
        self.stored_child_read(slot, words, crossing);
    }

    /// Add the slot's view in `words`, past `crossing`: the path
    /// [`Self::stored_child`] keeps off its one-word path.
    ///
    /// # Specification
    /// trivial.
    #[cold]
    fn stored_child_read(
        &mut self,
        slot: Slot,
        words: &WordArena,
        crossing: super::Crossing,
    )
    {
        if let Maybe::Present(support) = words.read(slot) {
            self.child(support, crossing);
        }
    }

    /// Whether the union, finished, is the support `slot` keeps in `words`.
    ///
    /// # Specification
    /// - ensures: as [`Union::equals`] of the support [`WordArena::read`]
    ///   answers for `slot`; [`super::Agreement::Different`] for a handle past
    ///   `words`.
    /// - panics: none.
    /// - executable: none — this runs once per carrier on the check path, as
    ///   [`Union::equals`]; the witness holds it to that comparison.
    /// - intension: one comparison of two words while the union is inline: a
    ///   one-word union finishes to its own word, which a slot keeps itself.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Union::equals`], over slots of one word and
    ///   handles, a union that holds the support and one that holds more.
    /// - witness: `support::tests::a_slot_unions_and_compares_as_its_support`
    #[inline]
    #[must_use]
    pub fn equals_stored(
        &self,
        slot: Slot,
        words: &WordArena,
    ) -> super::Agreement
    {
        match self.listed {
            None if slot.0 == self.inline => super::Agreement::Same,
            None => super::Agreement::Different,
            Some(_) => self.equals_stored_read(slot, words),
        }
    }

    /// Whether gathered lists, finished, are the slot's view in `words`: the
    /// comparison [`Self::equals_stored`] keeps off its inline path.
    ///
    /// # Specification
    /// trivial.
    #[cold]
    fn equals_stored_read(
        &self,
        slot: Slot,
        words: &WordArena,
    ) -> super::Agreement
    {
        match words.read(slot) {
            Maybe::Present(support) => self.equals(support),
            Maybe::Absent(unstored::Absent::Unstored) => super::Agreement::Different,
        }
    }
}
