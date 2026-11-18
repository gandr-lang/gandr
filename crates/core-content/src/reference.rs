//! The name of a constant in content: the key of the item that it names and
//! that item's occurrence among the items of its key.
//!
//! An admission position is an artefact of one revision, so content never
//! states one. A [`Resolver`] reads a position as the [`Reference`] that it
//! resolves to, and reads a reference back as a position.

use alloc::boxed::Box;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::ConstantIndex;
use quenchant_shape::shape::Maybe;

use crate::boundary::Occurrence;
use crate::content::seating;

/// The two directions between an admission position and a [`Reference`].
///
/// # Specification
/// - requires: `place` is the inverse of `resolve` on each occupied position.
/// - executable: none — a trait states no call of its own.
pub trait Resolver
{
    /// The reference that `position` resolves to.
    ///
    /// # Specification
    /// trivial.
    fn resolve(
        &self,
        position: ConstantIndex,
    ) -> Reference;

    /// The admission position of the item that `reference` names.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`seating::Absent::Unplaced`] when no item carries `reference`.
    fn place(
        &self,
        reference: &Reference,
    ) -> Maybe<ConstantIndex, seating::Absent>;
}

/// A front end's stable identity for one item: its name, after the tag of the
/// source that declares it when the front end names that source.
///
/// The tag tells the source's items from another source's items of the same
/// name, so an item's reference counts its occurrence within its own source,
/// whatever other sources the program holds. The crate reads no more
/// of a key than its bytes, its tag and its name.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ItemKey(Box<[u8]>);

/// The byte that opens the key of an item of a tagged source. No UTF-8 text
/// opens with it, so a key of an untagged source never reads as a tagged one.
const TAGGED: u8 = 0xFF;

/// How many bytes of a source name's digest a tag keeps.
const TAG_DIGEST: usize = 8;

/// How many bytes open the key of an item of a tagged source: [`TAGGED`],
/// then the tag's digest.
const TAG_PREFIX: usize = 1 + TAG_DIGEST;

/// The tag of a source: the first eight bytes of the BLAKE3 digest of the name
/// a front end gives it. A digest keeps each key of the source short, whatever
/// the length of the name.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SourceTag([u8; TAG_DIGEST]);

impl From<&str> for SourceTag
{
    /// The tag of the source named `name`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the first eight bytes of the BLAKE3 digest of `name`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two names of one source and two sources of one name.
    /// - witness: `gandr-core-incremental::region::tests::a_tagged_key_keeps_its_name_and_tells_its_source_6522`
    #[spec(ensures: |ret| blake3::hash(name.as_bytes()).as_bytes().get(.. TAG_DIGEST) == Some(ret.0.as_slice()))]
    #[inline]
    fn from(name: &str) -> Self
    {
        let mut tag = [0_u8; TAG_DIGEST];
        for (byte, digested) in tag.iter_mut().zip(blake3::hash(name.as_bytes()).as_bytes()) {
            *byte = *digested;
        }
        Self(tag)
    }
}

/// The name an item key holds: its bytes after the tag of its source.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct KeyName<'key>(&'key [u8]);

impl AsRef<[u8]> for KeyName<'_>
{
    /// The name's bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        self.0
    }
}

impl<'key> From<KeyName<'key>> for &'key [u8]
{
    /// The name's bytes, borrowed from its key.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(name: KeyName<'key>) -> Self
    {
        name.0
    }
}

impl ItemKey
{
    /// The name the key holds: the bytes after its source's tag, or every
    /// byte of the key of an untagged source.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the bytes after the first [`TAG_PREFIX`] when the key opens
    ///   with [`TAGGED`] and holds a whole tag; else every byte. The predicate
    ///   checks the name's end and width, since comparing the bytes walks them.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a tagged key, an untagged key and an empty key.
    /// - witness: `gandr-core-incremental::region::tests::a_tagged_key_keeps_its_name_and_tells_its_source_6522`
    #[spec(ensures: |ret| ret.0.as_ptr_range().end == self.0.as_ptr_range().end
        && ret.0.len() == self.0.get(TAG_PREFIX ..)
            .filter(|_| self.0.first() == Some(&TAGGED))
            .map_or_else(|| self.0.len(), <[u8]>::len))]
    #[inline]
    #[must_use]
    pub fn name(&self) -> KeyName<'_>
    {
        let bytes: &[u8] = &self.0;
        KeyName(
            bytes
                .get(TAG_PREFIX ..)
                .filter(|_| bytes.first() == Some(&TAGGED))
                .unwrap_or(bytes),
        )
    }
}

impl From<(SourceTag, &str)> for ItemKey
{
    /// The key of the item named `name` in the source tagged `tag`:
    /// [`TAGGED`], the tag, then the name's bytes.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`TAGGED`], the tag's bytes, then `name`'s bytes; its
    ///   [`ItemKey::name`] is `name`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`ItemKey::name`].
    /// - witness: `gandr-core-incremental::region::tests::a_tagged_key_keeps_its_name_and_tells_its_source_6522`
    ///
    /// # Cost
    /// - allocation: the bytes of the key, growth within the key
    #[spec(ensures: |ret| ret.0.first() == Some(&TAGGED)
        && ret.0.get(1 .. TAG_PREFIX) == Some(tag.0.as_slice())
        && ret.name().0 == name.as_bytes())]
    #[inline]
    fn from((tag, name): (SourceTag, &str)) -> Self
    {
        let mut key = Vec::with_capacity(TAG_PREFIX.saturating_add(name.len()));
        key.push(TAGGED);
        key.extend_from_slice(&tag.0);
        key.extend_from_slice(name.as_bytes());
        Self(key.into_boxed_slice())
    }
}

impl From<&[u8]> for ItemKey
{
    /// The key of these bytes.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the bytes of the key, growth within the key
    #[inline]
    fn from(bytes: &[u8]) -> Self
    {
        Self(Box::from(bytes))
    }
}

impl From<&str> for ItemKey
{
    /// The key of this text's bytes: the key of an item of an untagged
    /// source.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the bytes of the key, growth within the key
    #[inline]
    fn from(text: &str) -> Self
    {
        Self(Box::from(text.as_bytes()))
    }
}

impl AsRef<[u8]> for ItemKey
{
    /// The key's bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        &self.0
    }
}

/// What a constant names, stated without admission positions.
///
/// # Specification
/// - requires: item keys and occurrence counts are interpreted in one program.
/// - ensures: an item reference names the occurrence of its key; an unoccupied
///   position names no item.
/// - panics: none.
/// - executable: none — the program assigning keys and occurrence counts is
///   external to a reference value.
///
/// # Adequacy
/// - hypothesis: L3 — empty, skipped and maximum positions, interleaved
///   repeated keys and unknown references distinguish missing names, wrong
///   occurrence counts and accidental naming by exact references and ordinals.
/// - witness: `gandr-core-incremental::region::tests::positions_must_ascend_and_may_skip`
/// - witness: `gandr-core-incremental::region::tests::a_repeated_key_counts_its_occurrences`
/// - witness: `gandr-core-incremental::region::tests::empty_and_extreme_programs_resolve_exactly`
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Reference
{
    /// The item of `key` that `occurrence` items of the same key precede.
    Item
    {
        /// The item's key.
        key: ItemKey,
        /// How many items of the same key precede it.
        occurrence: Occurrence,
    },
    /// A position no item of the program occupies.
    Unoccupied,
}
