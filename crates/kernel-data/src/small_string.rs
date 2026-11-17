//! A small string: a text of up to 23 bytes inline, a static text, or a
//! block of its allocator, in 24 bytes for the global allocator.
//!
//! The string is an enum of three forms. The inline form keeps the text's
//! length, from 0 to 23, as an enum of 24 values, so the other values of that
//! byte are a niche. The compiler keeps the form's tag in the niche, so the
//! string is 24 bytes and an `Option` of a string is 24 bytes too. A read of
//! the text or of its length takes one branch on that byte.
//!
//! The static form keeps a text that the string never frees. The heap form
//! keeps a block of the allocator of the text's exact length, as a boxed
//! `str` does, until the shared pointer of the crate takes the long case. A
//! long text can live in the caller's region, and a refused block is an `Err`
//! of the operation, never an abort.
//!
//! The string takes and gives its text as a [`Text`], and gives its length as
//! a [`ByteLength`]. A [`Fits`] is a text of at most 23 bytes, and a string
//! builds from it with no refusal to answer.
//!
//! # Safety
//!
//! - unsafe invariants: the bytes of the inline and the heap forms are valid
//!   UTF-8, since the string copies only whole texts into them, and a static
//!   text is a `str`. [`SmallString::as_str`] reads the bytes as a `str` with
//!   no check, and that read is the type's one `unsafe`.

use alloc::alloc::Global;
use alloc::boxed::Box;
use alloc::vec::Vec;
use core::alloc::Allocator;
use core::alloc::Layout;
use core::cmp::Ordering;
use core::fmt;
use core::hash::Hash;
use core::hash::Hasher;
use core::ops::Deref;

use anodized::spec;

use crate::small_vec::Refused;

/// The bytes of the inline form.
const INLINE: usize = 23;

/// A borrowed text: the form in which a small string takes and gives text.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Text<'text>(&'text str);

impl<'text> From<&'text str> for Text<'text>
{
    /// The text of `text`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(text: &'text str) -> Self
    {
        Self(text)
    }
}

impl Deref for Text<'_>
{
    type Target = str;

    /// The borrowed text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn deref(&self) -> &str
    {
        self.0
    }
}

impl AsRef<str> for Text<'_>
{
    /// The borrowed text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        self.0
    }
}

impl fmt::Display for Text<'_>
{
    /// Write the text as it is.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(self.0)
    }
}

/// The length of a small string's text, in bytes.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ByteLength(usize);

impl From<ByteLength> for usize
{
    /// The count of bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(length: ByteLength) -> Self
    {
        length.0
    }
}

/// Whether a small string holds any text.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Emptiness
{
    /// The string holds no text.
    Empty,
    /// The string holds at least one byte of text.
    Occupied,
}

/// The length of an inline text: 0 to 23 bytes. No variant holds a byte from
/// 24 up, so those bytes are a niche, which keeps the string's tag.
#[cfg_attr(
    not(test),
    expect(
        clippy::missing_docs_in_private_items,
        reason = "each variant is the length that its name states"
    )
)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(u8)]
enum Length
{
    L0,
    L1,
    L2,
    L3,
    L4,
    L5,
    L6,
    L7,
    L8,
    L9,
    L10,
    L11,
    L12,
    L13,
    L14,
    L15,
    L16,
    L17,
    L18,
    L19,
    L20,
    L21,
    L22,
    L23,
}

/// Each length of an inline text, at its own index.
const LENGTHS: [Length; INLINE + 1] = [
    Length::L0,
    Length::L1,
    Length::L2,
    Length::L3,
    Length::L4,
    Length::L5,
    Length::L6,
    Length::L7,
    Length::L8,
    Length::L9,
    Length::L10,
    Length::L11,
    Length::L12,
    Length::L13,
    Length::L14,
    Length::L15,
    Length::L16,
    Length::L17,
    Length::L18,
    Length::L19,
    Length::L20,
    Length::L21,
    Length::L22,
    Length::L23,
];

impl Length
{
    /// The count of bytes.
    ///
    /// # Specification
    /// - ensures: the count that the variant's name states, at most 23.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each length from 0 to 23 reads back from its inline
    ///   string, which a wrong count for any variant breaks.
    /// - witness: `tests::small_string::each_length_reads_back_its_text_in_each_form`
    #[spec(ensures: |ret| ret.0 <= INLINE)]
    #[expect(
        clippy::as_conversions,
        reason = "a fieldless `repr(u8)` enum converts to its discriminant, which is the count that it names"
    )]
    #[inline]
    const fn get(self) -> ByteLength
    {
        ByteLength(self as usize)
    }
}

/// A text that fits inline, so that its small string never allocates.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Fits
{
    /// The text's bytes, and zeros after them.
    bytes: [u8; INLINE],
    /// The text's length.
    length: Length,
}

impl Fits
{
    /// The text, when it fits in the inline bytes.
    ///
    /// # Specification
    /// - ensures: `Some` exactly when the text has at most 23 bytes.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a text of 23 bytes fits and builds with no refusal,
    ///   and a text of 24 bytes does not fit.
    /// - witness: `tests::small_string::a_text_that_fits_builds_inline_and_a_longer_one_does_not_fit`
    #[spec(ensures: |ret| ret.is_some() == (text.0.len() <= INLINE))]
    #[inline]
    #[must_use]
    pub fn new(text: Text<'_>) -> Option<Self>
    {
        joined(Text(""), text)
    }
}

/// The inline bytes of two texts one after the other, when they fit.
///
/// # Specification
/// - ensures: `Some` exactly when the two have at most 23 bytes together, with
///   `head` and then `tail` in the first bytes.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a push at each character boundary of each text up to 40
///   bytes reads back the whole text, across the edge at 23 bytes.
/// - witness: `tests::small_string::push_str_crosses_the_inline_edge_at_each_split`
#[spec(ensures: |ret| ret.is_some() == (head.0.len().saturating_add(tail.0.len()) <= INLINE))]
#[inline]
fn joined(
    head: Text<'_>,
    tail: Text<'_>,
) -> Option<Fits>
{
    let total = head.0.len().checked_add(tail.0.len())?;
    let length = LENGTHS.get(total).copied()?;
    let mut bytes = [0_u8; INLINE];
    bytes
        .get_mut(.. head.0.len())?
        .copy_from_slice(head.0.as_bytes());
    bytes
        .get_mut(head.0.len() .. total)?
        .copy_from_slice(tail.0.as_bytes());
    Some(Fits { bytes, length })
}

/// The heap form of two texts one after the other, in a block of
/// `allocator`.
///
/// # Specification
/// - ensures: on success the heap form, whose block holds `head` and then
///   `tail` and whose capacity is its length.
/// - fails: the allocator refuses the block, or the length passes the largest
///   layout.
/// - panics: none.
///
/// # Errors
/// Returns [`Refused::Overflow`] when the length passes `isize::MAX`, and
/// [`Refused::Allocator`] when the allocator refuses the block.
///
/// # Adequacy
/// - hypothesis: L3 — a long text reads back from its block, and a region past
///   its budget refuses the block.
/// - witness: `tests::small_string::a_string_in_a_region_lives_in_its_bytes_and_is_refused_past_its_budget`
#[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|repr| matches!(*repr, Repr::Heap(ref block) if block.len() == head.0.len().saturating_add(tail.0.len()))))]
#[inline]
fn spilled<A>(
    head: Text<'_>,
    tail: Text<'_>,
    allocator: A,
) -> Result<Repr<A>, Refused>
where
    A: Allocator,
{
    let total = head
        .0
        .len()
        .checked_add(tail.0.len())
        .ok_or(Refused::Overflow)?;
    let layout = Layout::array::<u8>(total).map_err(|_overflow| Refused::Overflow)?;
    let mut bytes = Vec::new_in(allocator);
    bytes
        .try_reserve_exact(total)
        .map_err(|_refusal| Refused::Allocator(layout))?;
    bytes.extend_from_slice(head.0.as_bytes());
    bytes.extend_from_slice(tail.0.as_bytes());
    Ok(Repr::Heap(bytes.into_boxed_slice()))
}

/// The three forms of a small string.
#[derive(Clone)]
enum Repr<A: Allocator>
{
    /// A text of at most 23 bytes, in the string itself.
    Inline
    {
        /// The text's bytes, and zeros or old bytes after them.
        bytes: [u8; INLINE],
        /// The text's length, whose spare values keep the tag.
        length: Length,
        /// The allocator of a block that a push takes.
        allocator: A,
    },
    /// A static text, which the string never frees.
    Static(&'static str, A),
    /// A block of the allocator, of the text's exact length.
    Heap(Box<[u8], A>),
}

impl<A: Allocator> Repr<A>
{
    /// The inline form of a text that fits.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    const fn inline(
        fits: Fits,
        allocator: A,
    ) -> Self
    {
        Self::Inline {
            bytes: fits.bytes,
            length: fits.length,
            allocator,
        }
    }
}

/// A string of up to 23 bytes inline, a static text, or a block of its
/// allocator.
///
/// The allocator is a parameter, so a long text can live in a region, and an
/// allocator that refuses a block makes the operation an `Err`, never an
/// abort. A copy of a heap text copies its block, as a boxed `str` does, and
/// [`SmallString::try_clone`] answers a refusal instead.
#[repr(transparent)]
#[derive(Clone)]
pub struct SmallString<A: Allocator>(Repr<A>);

impl SmallString<Global>
{
    /// The empty string in the global allocator.
    ///
    /// # Specification
    /// - ensures: the string holds no text.
    /// - panics: none.
    /// - executable: none — a const function's clause runs in const evaluation,
    ///   where the string's readers do not run.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the empty string reads back no text.
    /// - witness: `tests::small_string::each_length_reads_back_its_text_in_each_form`
    #[inline]
    #[must_use]
    pub const fn new() -> Self
    {
        Self::new_in(Global)
    }

    /// The string of a static text, which never allocates.
    ///
    /// # Specification
    /// - ensures: the string reads back `text`, and a push that leaves it
    ///   longer than 23 bytes takes a block of the global allocator.
    /// - panics: none.
    /// - executable: none — a const function's clause runs in const evaluation,
    ///   where the string's readers do not run.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a static text reads back and spills on a push, and a
    ///   copy of it keeps the static text.
    /// - witness: `tests::small_string::a_static_text_reads_back_and_spills_on_a_push`
    #[inline]
    #[must_use]
    pub const fn from_static(text: Text<'static>) -> Self
    {
        Self(Repr::Static(text.0, Global))
    }
}

impl<A: Allocator> SmallString<A>
{
    /// The empty string in `allocator`.
    ///
    /// # Specification
    /// - ensures: the string holds no text.
    /// - panics: none.
    /// - executable: none — a const function's clause runs in const evaluation,
    ///   where the string's readers do not run.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the empty string reads back no text.
    /// - witness: `tests::small_string::each_length_reads_back_its_text_in_each_form`
    #[inline]
    #[must_use]
    pub const fn new_in(allocator: A) -> Self
    {
        Self(Repr::Inline {
            bytes: [0; INLINE],
            length: Length::L0,
            allocator,
        })
    }

    /// The string of `text` in `allocator`.
    ///
    /// # Specification
    /// - ensures: on success the string reads back `text`; a text of at most 23
    ///   bytes takes no block.
    /// - fails: the allocator refuses the block of a longer text.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`Refused::Allocator`] when the allocator refuses the block.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each length from 0 to 64 bytes, with a last character
    ///   of 1 to 4 bytes, reads back; a region of no budget holds a text of 23
    ///   bytes and refuses one of 24.
    /// - witness: `tests::small_string::each_length_reads_back_its_text_in_each_form`
    /// - witness: `tests::small_string::a_string_in_a_region_lives_in_its_bytes_and_is_refused_past_its_budget`
    #[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|string| string.as_str() == text))]
    #[inline]
    pub fn from_in(
        text: Text<'_>,
        allocator: A,
    ) -> Result<Self, Refused>
    {
        Ok(Self(match Fits::new(text) {
            Some(fits) => Repr::inline(fits, allocator),
            None => spilled(Text(""), text, allocator)?,
        }))
    }

    /// A copy of the string in a copy of its allocator.
    ///
    /// # Specification
    /// - ensures: on success the copy has the string's length, and reads back
    ///   its text; a static text stays static and an inline text takes no
    ///   block.
    /// - fails: the allocator refuses the block of a heap text.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`Refused::Allocator`] when the allocator refuses the block.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a copy of a heap text reads back in a region, and a
    ///   region past its budget refuses a block.
    /// - witness: `tests::small_string::a_string_in_a_region_lives_in_its_bytes_and_is_refused_past_its_budget`
    #[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|copy| copy.len() == self.len()))]
    #[inline]
    pub fn try_clone(&self) -> Result<Self, Refused>
    where
        A: Clone,
    {
        Ok(Self(match self.0 {
            Repr::Heap(ref text) => spilled(Text(""), self.as_str(), Box::allocator(text).clone())?,
            Repr::Inline { .. } | Repr::Static(..) => self.0.clone(),
        }))
    }

    /// The string's allocator.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn allocator(&self) -> &A
    {
        match self.0 {
            Repr::Inline { ref allocator, .. } | Repr::Static(_, ref allocator) => allocator,
            Repr::Heap(ref text) => Box::allocator(text),
        }
    }

    /// The text.
    ///
    /// # Specification
    /// - ensures: an inline text has at most 23 bytes.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each form reads back its text, which a wrong form or
    ///   length breaks.
    /// - witness: `tests::small_string::each_length_reads_back_its_text_in_each_form`
    #[spec(ensures: |ret| ret.0.len() <= INLINE || !matches!(self.0, Repr::Inline { .. }))]
    #[inline]
    #[must_use]
    pub fn as_str(&self) -> Text<'_>
    {
        let bytes = match self.0 {
            Repr::Inline {
                ref bytes, length, ..
            } => bytes.get(.. length.get().0).unwrap_or_default(),
            Repr::Static(text, _) => text.as_bytes(),
            Repr::Heap(ref text) => text,
        };
        // SAFETY: the unsafe invariant of the module: the string copies only
        // whole texts into the inline bytes and into a block, and a static
        // text is a `str`.
        Text(unsafe { core::str::from_utf8_unchecked(bytes) })
    }

    /// The length of the text in bytes.
    ///
    /// # Specification
    /// - ensures: the count of the text's bytes, read with one branch on the
    ///   tag.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each length from 0 to 64 bytes reads back in each
    ///   form.
    /// - witness: `tests::small_string::each_length_reads_back_its_text_in_each_form`
    #[spec(ensures: |ret| ret.0 == self.as_str().0.len())]
    #[inline]
    #[must_use]
    pub fn len(&self) -> ByteLength
    {
        ByteLength(self.as_str().0.len())
    }

    /// Whether the string holds any text.
    ///
    /// # Specification
    /// - ensures: `Empty` exactly when the text has no bytes.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the empty string is empty, and a string of one byte
    ///   is not.
    /// - witness: `tests::small_string::each_length_reads_back_its_text_in_each_form`
    #[spec(ensures: |ret| (ret == Emptiness::Empty) == (self.len().0 == 0))]
    #[inline]
    #[must_use]
    pub fn is_empty(&self) -> Emptiness
    {
        if self.as_str().0.is_empty() {
            Emptiness::Empty
        }
        else {
            Emptiness::Occupied
        }
    }

    /// Append `text`; a refusal leaves the string as it was.
    ///
    /// # Specification
    /// - ensures: on success the string reads back its old text and then
    ///   `text`; a text that stays within 23 bytes is inline, and a longer one
    ///   takes a block of the exact length.
    /// - fails: the allocator refuses the block, or the length passes the
    ///   largest layout; the string is unchanged.
    /// - panics: none.
    /// - intension: one copy of the old text and of `text` when the result
    ///   leaves the inline form or grows past it, and the old block's release.
    ///
    /// # Errors
    /// Returns [`Refused::Overflow`] when the length passes `isize::MAX`, and
    /// [`Refused::Allocator`] when the allocator refuses the block.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a push at each character boundary of each text up to
    ///   40 bytes reads back the whole text, across the edge at 23 bytes in the
    ///   two directions; a region past its budget refuses the push and the
    ///   string keeps its text.
    /// - witness: `tests::small_string::push_str_crosses_the_inline_edge_at_each_split`
    /// - witness: `tests::small_string::a_string_in_a_region_lives_in_its_bytes_and_is_refused_past_its_budget`
    #[spec(
        captures: before = self.len().0,
        ensures: |ret| self.len().0 == if ret.is_ok() { before.saturating_add(text.0.len()) } else { before },
    )]
    #[inline]
    pub fn push_str(
        &mut self,
        text: Text<'_>,
    ) -> Result<(), Refused>
    where
        A: Clone,
    {
        if text.0.is_empty() {
            return Ok(());
        }
        let allocator = self.allocator().clone();
        self.0 = match joined(self.as_str(), text) {
            Some(fits) => Repr::inline(fits, allocator),
            None => spilled(self.as_str(), text, allocator)?,
        };
        Ok(())
    }
}

impl<A: Allocator + Default> From<Fits> for SmallString<A>
{
    /// The inline string of a text that fits, with no refusal to answer.
    ///
    /// # Specification
    /// - ensures: the string has the text's length and holds no block.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a text of 23 bytes builds and reads back.
    /// - witness: `tests::small_string::a_text_that_fits_builds_inline_and_a_longer_one_does_not_fit`
    #[spec(ensures: |ret| ret.len() == text.length.get())]
    #[inline]
    fn from(text: Fits) -> Self
    {
        Self(Repr::inline(text, A::default()))
    }
}

impl<'text, A: Allocator + Default> TryFrom<&'text str> for SmallString<A>
{
    type Error = Refused;

    /// The string of `text` in a default allocator.
    ///
    /// # Specification
    /// - ensures: on success the string reads back `text`.
    /// - fails: as [`SmallString::from_in`].
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`Refused::Allocator`] when the allocator refuses the block.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each length from 0 to 64 bytes reads back.
    /// - witness: `tests::small_string::each_length_reads_back_its_text_in_each_form`
    #[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|string| string.as_str().0 == text))]
    #[inline]
    fn try_from(text: &'text str) -> Result<Self, Refused>
    {
        Self::from_in(Text(text), A::default())
    }
}

impl<A: Allocator> Deref for SmallString<A>
{
    type Target = str;

    /// The text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn deref(&self) -> &str
    {
        self.as_str().0
    }
}

impl<A: Allocator + Default> Default for SmallString<A>
{
    /// The empty string in a default allocator.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self::new_in(A::default())
    }
}

impl<A: Allocator> fmt::Debug for SmallString<A>
{
    /// Write the text as `str` writes it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        fmt::Debug::fmt(self.as_str().0, f)
    }
}

impl<A: Allocator> fmt::Display for SmallString<A>
{
    /// Write the text as it is.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(self.as_str().0)
    }
}

impl<A: Allocator> PartialEq for SmallString<A>
{
    /// Whether the two texts are equal, whatever their forms.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn eq(
        &self,
        other: &Self,
    ) -> bool
    {
        self.as_str() == other.as_str()
    }
}

impl<A: Allocator> Eq for SmallString<A>
{
}

impl<A: Allocator> PartialOrd for SmallString<A>
{
    /// The order of the two texts.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn partial_cmp(
        &self,
        other: &Self,
    ) -> Option<Ordering>
    {
        Some(self.cmp(other))
    }
}

impl<A: Allocator> Ord for SmallString<A>
{
    /// The order of the two texts, as `str` orders them.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn cmp(
        &self,
        other: &Self,
    ) -> Ordering
    {
        self.as_str().0.cmp(other.as_str().0)
    }
}

impl<A: Allocator> Hash for SmallString<A>
{
    /// Hash the text as `str` hashes it, whatever form holds it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn hash<H>(
        &self,
        state: &mut H,
    ) where
        H: Hasher,
    {
        self.as_str().0.hash(state);
    }
}
