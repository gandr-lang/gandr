//! The heap object header, the closure flavours, the exit statuses and the
//! fuel the stencils and the emitter share.
//!
//! # The heap object
//!
//! A heap object is a header word followed by its fields. The header packs,
//! from the least significant bit:
//!
//! | bits | field | holds |
//! | ---- | ----- | ----- |
//! | 0–3 | kind | [`Kind`] |
//! | 4–15 | tag | a summand position, a constructor ordinal, a closure's [`Flavour`] |
//! | 16–31 | arity | the field count, or a closure's capture count |
//! | 32–63 | family | a data constructor's family declaration, a head's or a literal's entry in its table, or an opaque constant, each plus one; zero when none is named |
//!
//! A case arm compares the low 32 bits against one immediate operand and the
//! family against the other, so a header a stencil tests is two operands
//! below 2³²; a nominal match compares the kind and the tag alone, as the
//! machine matches by ordinal. A closure is `[header, code, capture…]`: the
//! code word is the entry its observation jumps to, the captures the words
//! its support names, which its body's entry copies into a fresh window.
//!
//! Three kinds only the host reads, as the host makes them. A capability is
//! compared by its address alone. A stack is `[header, base, top, frame…,
//! window…]`, the arity its frame count: the frames a capture took from the
//! region `[base, top)`, each window a frame resumes in copied after them. A
//! cell is a held binding's or a view's mutable words, which a linear
//! variable reads its first field of.
//!
//! # The count
//!
//! Every object is preceded by its count word, so a value addresses its
//! header and every field offset is the same whether or not a count is read.
//! A fresh object's count is one; a constant the function lays out in its
//! data carries [`COUNT_IMMORTAL`], zero, which `dup` and `drop` leave alone.
//! A `drop` that finds a count of one calls the host's [`RELEASE`] entry,
//! which frees the object's block and drops what it holds through a
//! worklist. A freed block joins the runtime record's free list for its size
//! ([`Header::block`]), its count word holding the next block, and the next
//! allocation of that size takes it before the bump pointer moves. A block of
//! [`FREE_CLASSES`] words or more, and a stack, whose size its header does
//! not hold, are never reused; a window is allocated by the bump pointer
//! alone and holds no count. The alternative, a count inside the header,
//! needs bits the header has none of: its four fields fill the word.

use crate::Word;

/// What a heap object is.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Kind
{
    /// A machine integer literal: one field, its two's-complement bits.
    Integer,
    /// A tuple: its fields, left to right; the unit is the tuple of none.
    Tuple,
    /// A sum injection: one field, the summand position in the tag.
    Injection,
    /// A nominal datatype's constructor: its fields, the ordinal in the tag.
    Data,
    /// A closure: a code word and its captures.
    Closure,
    /// A constructor head the stencils compare only by identity — a record
    /// with its labels, a native list's nil or cell, a lift, a recorded run —
    /// whose family names its entry in the function's head table.
    Head,
    /// A literal no machine word holds — text, a numeric, an integer past 64
    /// bits — whose family names its entry in the run's literal table.
    Literal,
    /// A constant with no body, carried as itself; its family names it.
    Opaque,
    /// A capability a handler introduced, compared by its address.
    Capability,
    /// A captured stack: its frames and the windows they resume in.
    Stack,
    /// A linear binding's mutable words: the value held first.
    Cell,
    /// A code a run passes as a type argument and never observes, whose
    /// family names its entry in the function's code table.
    Code,
}

/// The header bits of [`Kind::Integer`].
const KIND_INTEGER: usize = 0;
/// The header bits of [`Kind::Tuple`].
pub const KIND_TUPLE: usize = 1;
/// The header bits of [`Kind::Injection`].
const KIND_INJECTION: usize = 2;
/// The header bits of [`Kind::Data`].
pub const KIND_DATA: usize = 3;
/// The header bits of [`Kind::Closure`].
pub const KIND_CLOSURE: usize = 4;
/// The header bits of [`Kind::Head`].
const KIND_HEAD: usize = 5;
/// The header bits of [`Kind::Literal`].
const KIND_LITERAL: usize = 6;
/// The header bits of [`Kind::Opaque`].
const KIND_OPAQUE: usize = 7;
/// The header bits of [`Kind::Capability`].
const KIND_CAPABILITY: usize = 8;
/// The header bits of [`Kind::Stack`].
const KIND_STACK: usize = 9;
/// The header bits of [`Kind::Cell`].
const KIND_CELL: usize = 10;
/// The header bits of [`Kind::Code`].
const KIND_CODE: usize = 11;
/// The kind's bits in a header.
pub const KIND_MASK: usize = 0xF;
/// Where the tag starts in a header.
pub const TAG_SHIFT: u32 = 4;
/// The tag's bits, shifted down.
const TAG_MASK: usize = 0xFFF;
/// Where the arity starts in a header.
pub const ARITY_SHIFT: u32 = 16;
/// The arity's bits, shifted down.
pub const ARITY_MASK: usize = 0xFFFF;
/// Where the family starts in a header.
pub const FAMILY_SHIFT: u32 = 32;
/// The bits an observation checks: kind and tag.
pub const OBSERVED_MASK: usize = 0xFFFF;
/// The kind and tag of an application arm's closure, which only an
/// application observes.
pub const APPLY_CLOSURE: usize = KIND_CLOSURE | 2_usize.wrapping_shl(TAG_SHIFT);
/// The kind and tag of a copattern object entered through its dispatch, which
/// reads the observed word every observation writes before entering it.
pub const OBJECT_CLOSURE: usize = KIND_CLOSURE | 4_usize.wrapping_shl(TAG_SHIFT);
/// The kind and tag of a suspended capture, which no observation enters: only
/// a cut delivering it runs its body against the consumer it meets.
pub const CAPTURE_CLOSURE: usize = KIND_CLOSURE | 5_usize.wrapping_shl(TAG_SHIFT);
/// The bits a case arm compares against operand A: kind, tag and arity.
pub const MATCHED_MASK: usize = 0xFFFF_FFFF;
/// The bits a nominal match compares: kind and tag.
pub const ORDINAL_MASK: usize = 0xFFFF;

/// How a closure answers its observation, carried in its header's tag.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Flavour
{
    /// A thunk: a force enters it.
    Thunk,
    /// A recursive thunk: a force enters it bound to itself.
    Fixpoint,
    /// A one-arm copattern object answering `apply`.
    Apply,
    /// A one-arm copattern object answering `force`.
    Force,
    /// A copattern object of any other arms: its code dispatches on the
    /// observed word to the arm's entry.
    Object,
    /// A suspended capture `μα. c`: its code runs `c` with `α` the frame on
    /// top.
    Capture,
}

/// The flavours, by their tag.
const FLAVOURS: [Flavour; 6] = [
    Flavour::Thunk,
    Flavour::Fixpoint,
    Flavour::Apply,
    Flavour::Force,
    Flavour::Object,
    Flavour::Capture,
];

/// A header's tag field: a summand position, a constructor ordinal or a
/// closure's flavour.
///
/// # Specification
/// - ensures: the value is below 2¹², the tag field's width.
/// - executable: none — the bound is the type's construction invariant,
///   established by its `TryFrom` refusal.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Tag(u16);

/// Why a value does not fit its header field.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum FieldOverflow
{
    /// The tag is 2¹² or more.
    Tag,
    /// The arity is 2¹⁶ or more.
    Arity,
    /// The family's position plus one is 2³² or more.
    Family,
}

impl TryFrom<usize> for Tag
{
    type Error = FieldOverflow;

    /// The tag `value`, when it fits the tag field.
    ///
    /// # Specification
    /// - ensures: `Ok` exactly when `value` is below 2¹².
    /// - fails: [`FieldOverflow::Tag`] at or past 2¹².
    /// - panics: none.
    /// - executable: none — the bound is the type's construction invariant.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the boundary pair 2¹² − 1 and 2¹² separates the
    ///   accepted tags from the refused.
    /// - witness: `tests::layout::the_header_fields_refuse_values_past_their_width`
    #[inline]
    fn try_from(value: usize) -> Result<Self, FieldOverflow>
    {
        if value > TAG_MASK {
            return Err(FieldOverflow::Tag);
        }
        u16::try_from(value)
            .map(Self)
            .map_err(|_overflow| FieldOverflow::Tag)
    }
}

impl From<Flavour> for Tag
{
    /// The tag of a closure's flavour.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(flavour: Flavour) -> Self
    {
        Self(match flavour {
            Flavour::Thunk => 0,
            Flavour::Fixpoint => 1,
            Flavour::Apply => 2,
            Flavour::Force => 3,
            Flavour::Object => 4,
            Flavour::Capture => 5,
        })
    }
}

impl TryFrom<Tag> for Flavour
{
    type Error = Tag;

    /// The flavour a closure's tag names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn try_from(tag: Tag) -> Result<Self, Tag>
    {
        FLAVOURS.get(usize::from(tag.0)).copied().ok_or(tag)
    }
}

impl From<Tag> for usize
{
    /// The tag's value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(tag: Tag) -> Self
    {
        Self::from(tag.0)
    }
}

/// A header's arity field: a field count or a capture count.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Arity(u16);

impl TryFrom<usize> for Arity
{
    type Error = FieldOverflow;

    /// The arity `value`, when it fits the arity field.
    ///
    /// # Specification
    /// - ensures: `Ok` exactly when `value` is below 2¹⁶.
    /// - fails: [`FieldOverflow::Arity`] at or past 2¹⁶.
    /// - panics: none.
    /// - executable: none — the bound is the type's construction invariant.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the boundary pair 2¹⁶ − 1 and 2¹⁶ separates the
    ///   accepted arities from the refused.
    /// - witness: `tests::layout::the_header_fields_refuse_values_past_their_width`
    #[inline]
    fn try_from(value: usize) -> Result<Self, FieldOverflow>
    {
        u16::try_from(value)
            .map(Self)
            .map_err(|_overflow| FieldOverflow::Arity)
    }
}

impl From<Arity> for usize
{
    /// The arity's value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(arity: Arity) -> Self
    {
        Self::from(arity.0)
    }
}

/// A header's family field: a data constructor's family declaration plus
/// one, or zero for a constructor whose family the core does not name.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Family(u32);

impl Family
{
    /// No family named.
    pub const UNNAMED: Self = Self(0);
}

impl TryFrom<usize> for Family
{
    type Error = FieldOverflow;

    /// The family declared at admission position `position`, stored plus one.
    ///
    /// # Specification
    /// - ensures: `Ok` exactly when `position + 1` fits 32 bits, and
    ///   `usize::try_from` of the result is `position` again.
    /// - fails: [`FieldOverflow::Family`] otherwise.
    /// - panics: none.
    /// - executable: none — the bound is the type's construction invariant.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — position 0 and the largest representable position
    ///   round-trip, and the next is refused.
    /// - witness: `tests::layout::the_header_fields_refuse_values_past_their_width`
    #[inline]
    fn try_from(position: usize) -> Result<Self, FieldOverflow>
    {
        let biased = position.checked_add(1).ok_or(FieldOverflow::Family)?;
        u32::try_from(biased)
            .map(Self)
            .map_err(|_overflow| FieldOverflow::Family)
    }
}

impl TryFrom<Family> for usize
{
    type Error = Unnamed;

    /// The admission position the family names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn try_from(family: Family) -> Result<Self, Unnamed>
    {
        let position = family.0.checked_sub(1).ok_or(Unnamed)?;
        Self::try_from(position).map_err(|_overflow| Unnamed)
    }
}

impl From<Family> for u32
{
    /// The field's bits.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(family: Family) -> Self
    {
        family.0
    }
}

/// A header names no family.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Unnamed;

/// A heap object's header word.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Header(Word);

/// A header word whose kind bits name no [`Kind`].
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct UnknownKind(pub Word);

impl Header
{
    /// The header of an object of `kind`, `tag` and `arity`, naming `family`.
    ///
    /// # Specification
    /// - ensures: [`Self::kind`], [`Self::tag`], [`Self::arity`] and
    ///   [`Self::family`] read back the four arguments.
    /// - panics: none.
    /// - executable: none — the round trip is the adequacy witness's to show.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a header built from the widest value of each field
    ///   reads every field back unchanged, so no field overlaps another.
    /// - witness: `tests::layout::a_header_reads_back_every_field`
    #[inline]
    #[must_use]
    pub fn new(
        kind: Kind,
        tag: Tag,
        arity: Arity,
        family: Family,
    ) -> Self
    {
        let kind = match kind {
            Kind::Integer => KIND_INTEGER,
            Kind::Tuple => KIND_TUPLE,
            Kind::Injection => KIND_INJECTION,
            Kind::Data => KIND_DATA,
            Kind::Closure => KIND_CLOSURE,
            Kind::Head => KIND_HEAD,
            Kind::Literal => KIND_LITERAL,
            Kind::Opaque => KIND_OPAQUE,
            Kind::Capability => KIND_CAPABILITY,
            Kind::Stack => KIND_STACK,
            Kind::Cell => KIND_CELL,
            Kind::Code => KIND_CODE,
        };
        let family = usize::try_from(family.0).unwrap_or(0);
        Self(Word(
            kind | usize::from(tag).wrapping_shl(TAG_SHIFT)
                | usize::from(arity).wrapping_shl(ARITY_SHIFT)
                | family.wrapping_shl(FAMILY_SHIFT),
        ))
    }

    /// The header an object starts with.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn from_word(word: Word) -> Self
    {
        Self(word)
    }

    /// The header's word.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn word(self) -> Word
    {
        self.0
    }

    /// The bits a case arm compares against operand A: kind, tag and arity.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn matched(self) -> Word
    {
        Word(self.0.0 & MATCHED_MASK)
    }

    /// The family field.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn family(self) -> Family
    {
        Family(u32::try_from(self.0.0.wrapping_shr(FAMILY_SHIFT)).unwrap_or(0))
    }

    /// The object's kind.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`UnknownKind`] when the kind bits name no kind.
    #[inline]
    pub const fn kind(self) -> Result<Kind, UnknownKind>
    {
        match self.0.0 & KIND_MASK {
            KIND_INTEGER => Ok(Kind::Integer),
            KIND_TUPLE => Ok(Kind::Tuple),
            KIND_INJECTION => Ok(Kind::Injection),
            KIND_DATA => Ok(Kind::Data),
            KIND_CLOSURE => Ok(Kind::Closure),
            KIND_HEAD => Ok(Kind::Head),
            KIND_LITERAL => Ok(Kind::Literal),
            KIND_OPAQUE => Ok(Kind::Opaque),
            KIND_CAPABILITY => Ok(Kind::Capability),
            KIND_STACK => Ok(Kind::Stack),
            KIND_CELL => Ok(Kind::Cell),
            KIND_CODE => Ok(Kind::Code),
            _ => Err(UnknownKind(self.0)),
        }
    }

    /// The object's tag.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn tag(self) -> Tag
    {
        Tag(u16::try_from(self.0.0.wrapping_shr(TAG_SHIFT) & TAG_MASK).unwrap_or(0))
    }

    /// The object's field or capture count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn arity(self) -> Arity
    {
        Arity(u16::try_from(self.0.0.wrapping_shr(ARITY_SHIFT) & ARITY_MASK).unwrap_or(0))
    }

    /// The words the object's block spans, its count word included, when the
    /// header alone says: a closure's code word and captures, every other
    /// kind's fields, and none for a stack, whose window copies its arity
    /// does not count.
    ///
    /// # Specification
    /// - ensures: `ret` is `None` exactly for a stack or an unknown kind, and
    ///   otherwise two words past the arity, three for a closure.
    /// - executable: none — the arithmetic is the body.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a freed tuple's block is the one the next tuple of
    ///   its arity reuses, and a freed closure's the next closure's.
    /// - witness: `tests::count::a_freed_block_is_the_next_of_its_size`
    #[inline]
    #[must_use]
    pub fn block(self) -> Option<Words>
    {
        let fields = usize::from(self.arity());
        match self.kind() {
            Ok(Kind::Closure) => Some(Words(fields.wrapping_add(3))),
            Ok(Kind::Stack) | Err(_) => None,
            Ok(
                Kind::Integer
                | Kind::Tuple
                | Kind::Injection
                | Kind::Data
                | Kind::Head
                | Kind::Literal
                | Kind::Opaque
                | Kind::Capability
                | Kind::Cell
                | Kind::Code,
            ) => Some(Words(fields.wrapping_add(2))),
        }
    }
}

/// A count of heap words.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Words(pub usize);

/// The count word of an object no drop frees: a constant laid out in the
/// function's data.
pub const COUNT_IMMORTAL: Word = Word(0);
/// The count word of a fresh object: its one owner.
pub const COUNT_ONE: Word = Word(1);
/// The free lists the runtime record keeps, by block size in words: a block
/// of this many words or more is never reused.
pub const FREE_CLASSES: usize = 16;
/// The host entry a drop calls with the object whose count it found at one:
/// no callee table numbers an entry this high.
pub const RELEASE: Word = Word(usize::MAX);

/// Why a run returned to its entry.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Status
{
    /// The run has not exited.
    Running,
    /// The run delivered its answer to the terminal consumer.
    Halted,
    /// A case met a constructor none of its arms answers.
    Unmatched,
    /// An allocation would have passed the heap region's limit.
    HeapExhausted,
    /// A push would have passed the frame region's limit.
    FramesExhausted,
    /// The run spent its fuel: as many code-word jumps as its budget allows.
    FuelExhausted,
    /// An observation met a value it does not observe — the record's observed
    /// word names the destructor — or a host call refused its operands, the
    /// observed word zero and the refusal the host's to name.
    Stuck,
}

/// The destructor an observation applied when it took the stuck exit, as the
/// runtime record's observed word names it.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Observed
{
    /// An application.
    Apply,
    /// A force.
    Force,
    /// A lazy product's projection of the component the word counts, from
    /// zero.
    Project(Word),
}

/// The observed word of [`Observed::Apply`].
pub const OBSERVED_APPLY: Word = Word(1);
/// The observed word of [`Observed::Force`].
pub const OBSERVED_FORCE: Word = Word(2);
/// The observed word of [`Observed::Project`] of the first component; each
/// later component's is one more.
pub const OBSERVED_PROJECT: Word = Word(3);

/// The observed word of the projection of `component`.
///
/// # Specification
/// trivial.
#[inline]
#[must_use]
pub const fn observed_projection(component: Word) -> Word
{
    Word(OBSERVED_PROJECT.0.wrapping_add(component.0))
}

impl TryFrom<Word> for Observed
{
    type Error = UnknownStatus;

    /// The destructor an observed word names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn try_from(word: Word) -> Result<Self, UnknownStatus>
    {
        match word {
            OBSERVED_APPLY => Ok(Self::Apply),
            OBSERVED_FORCE => Ok(Self::Force),
            Word(other) => other
                .checked_sub(OBSERVED_PROJECT.0)
                .map(|component| Self::Project(Word(component)))
                .ok_or(UnknownStatus(Word(other))),
        }
    }
}

impl From<Observed> for Word
{
    /// The observed word naming `observed`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(observed: Observed) -> Self
    {
        match observed {
            Observed::Apply => OBSERVED_APPLY,
            Observed::Force => OBSERVED_FORCE,
            Observed::Project(component) => observed_projection(component),
        }
    }
}

/// The status word of [`Status::Running`].
pub const STATUS_RUNNING: Word = Word(0);
/// The status word of [`Status::Halted`].
pub const STATUS_HALTED: Word = Word(1);
/// The status word of [`Status::Unmatched`].
pub const STATUS_UNMATCHED: Word = Word(2);
/// The status word of [`Status::HeapExhausted`].
pub const STATUS_HEAP_EXHAUSTED: Word = Word(3);
/// The status word of [`Status::FramesExhausted`].
pub const STATUS_FRAMES_EXHAUSTED: Word = Word(4);
/// The status word of [`Status::FuelExhausted`].
pub const STATUS_FUEL_EXHAUSTED: Word = Word(5);
/// The status word of [`Status::Stuck`].
pub const STATUS_STUCK: Word = Word(6);

/// A status word no exit writes.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct UnknownStatus(pub Word);

impl TryFrom<Word> for Status
{
    type Error = UnknownStatus;

    /// The status an exit wrote.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn try_from(word: Word) -> Result<Self, UnknownStatus>
    {
        match word {
            STATUS_RUNNING => Ok(Self::Running),
            STATUS_HALTED => Ok(Self::Halted),
            STATUS_UNMATCHED => Ok(Self::Unmatched),
            STATUS_HEAP_EXHAUSTED => Ok(Self::HeapExhausted),
            STATUS_FRAMES_EXHAUSTED => Ok(Self::FramesExhausted),
            STATUS_FUEL_EXHAUSTED => Ok(Self::FuelExhausted),
            STATUS_STUCK => Ok(Self::Stuck),
            other => Err(UnknownStatus(other)),
        }
    }
}

/// A count of code-word jumps a run may take before it exits with
/// [`Status::FuelExhausted`].
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Fuel(usize);

impl Fuel
{
    /// The fuel a runtime record's word holds.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn from_word(word: Word) -> Self
    {
        Self(word.0)
    }
}

impl From<usize> for Fuel
{
    /// The fuel of this many jumps.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(jumps: usize) -> Self
    {
        Self(jumps)
    }
}

impl From<Fuel> for usize
{
    /// The jumps the fuel allows.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(fuel: Fuel) -> Self
    {
        fuel.0
    }
}
