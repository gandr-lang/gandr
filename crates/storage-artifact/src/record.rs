//! The declaration-record model: a kernel artifact as an index of two records
//! and one value leaf for each distinct declaration segment.
//!
//! # The records
//!
//! ```text
//! key        value
//! ""         header: magic, version, minted-atom table, count
//! 0x00       the order: the form, the record keys, then one slot per place
//! ```
//!
//! | Key | Value |
//! | --- | ----- |
//! | the empty key | the header: magic, version, minted-atom table, declaration count |
//! | [`ORDER_KEY`], one zero byte | the order: the set's form; the number of records, four bytes; each record's key, [`RECORD_KEY_LEN`] bytes, in the order of its first place; then for each declaration in admission order the slot of its record among the keys, four bytes, and in a named set its content name, [`CONTENT_NAME_LEN`] bytes |
//!
//! The two records make the index tree that the manifest names. Each
//! declaration record is a value leaf of its own: one node that holds the
//! segment under the empty key. The record's key is the identity of that node,
//! so no record stores a key beside its bytes. The store hashes a node once
//! when it loads it, and that hash is the key. One key names one byte string
//! in every artifact that holds it. Two artifacts that differ by one
//! declaration share each record whose bytes the edit leaves, at any position.
//! Two places with equal bytes share one record.
//!
//! The order is the one record that an insertion always rewrites. It holds
//! each key once, and four bytes for each place. It opens with the set's form,
//! [`Naming`]. In a named set, each place also holds the kernel's content key
//! of its entry. A set never mixes the two forms. An admission whose artifact
//! the store keeps names every place, and an export cut from bytes alone names
//! none.
//!
//! A declaration segment may reference subterm-table entries that an earlier
//! segment introduced, and constants by their admission index. So a record is
//! a content-addressing grain, never an independently decodable unit: a reader
//! reassembles the whole image in the order's sequence and decodes it once.
//! Those references move a record whose declaration does not change. A
//! reference by name, at an offset inside its piece, removes them, and the
//! key stays.
//!
//! Executable record refinements bind each key to the identity of its bytes'
//! value leaf, require distinct keys in the order of their first place,
//! require each place's slot to name a held record and each record to stand
//! at a place, and require a named
//! set to hold one name per place. Raw header and segment bytes remain
//! admissible; those refinements do not certify kernel validity.
//!
//! **Choice.** A record's key is the identity of the value leaf that holds its
//! bytes, and the order holds each key once and a slot for each place.
//! **Alternatives.** The admission index as the key moves every record past an
//! insertion. A probe of 2,000 declarations shares 28 of the 1,000 records
//! past one insertion under that key. The kernel's content key shares 600 of
//! them. But while references stay positional, one content key names several
//! byte strings: 16 keys held 816 segments. The digest of the bytes shares the
//! same 600, and it names one byte string. A key stored beside its bytes in a
//! record, and again at each place, costs 8% on the corpus's commit and read
//! against the admission index. **Reversal.** None planned: the references
//! part changes the bytes and not the key.
//!
//! # Where the cuts come from
//!
//! [`ArtifactRecordSet::from_artifact`] cuts an image where the kernel's
//! decoder reports its segments end, so a record boundary that is not a
//! segment boundary never reaches storage from this path.
//! [`ArtifactRecordSet::ensure_cut_at`] holds a stored set to the same
//! boundaries on the way back.
//!
//! `from_artifact` decodes the image before it cuts it, and cuts where
//! `DecodedArtifact::segments` reports each segment ends, so every set the
//! commit path builds was decoded, budget-checked and delimited by the kernel
//! first. On the way back, `ensure_cut_at` refuses a stored set whose bytes
//! decode but whose records straddle or split segments: the boundaries a reader
//! trusts are its own decoder's, never a writer's.
//!
//! **Alternatives.** A segmenting encoder that reports its own cuts makes the
//! writer the authority on where records end. A second parser of the format
//! here would drift from the kernel's. **Reversal.** None planned: the decoder
//! is the format's one reader.
//!
//! # The declaration is the record grain
//!
//! The record is the declaration segment, and nothing cuts inside one: no
//! scanner here reads `NODE_TAG_TABLE`'s storage columns, and each record is
//! one value leaf of the record plane. The declaration boundary
//! is the replay grain and the checkpoint grain as well, so one grain serves
//! all three. Were a codec to cut inside segments, the table's conservative
//! alias column governs which constructors are boundaries; the threshold column
//! stays recorded with no reader. **Alternatives.** A value-plane codec over
//! each segment, cut at the conservative column's boundary set, shares
//! structure below a declaration at the cost of a second chunk language for one
//! artifact. **Reversal.** A measured artifact whose single declarations
//! outgrow the record plane's node budget, or whose edits land inside large
//! declarations often enough that per-declaration records stop sharing.

use alloc::boxed::Box;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::ArtifactImage;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DecodedPrefix;
use gandr_kernel_term::SegmentLayout;
use gandr_kernel_term::decode;
use gandr_kernel_term::decode_after;
use gandr_kernel_term::decode_keeping;
use gandr_kernel_term::decoded_prefix;
use gandr_storage_records::BlockStore;
use gandr_storage_records::NamedValue;
use gandr_storage_records::NodeHash;
use gandr_storage_records::Record;
use gandr_storage_records::RecordIndex;
use gandr_storage_records::RecordRef;
use gandr_storage_records::RecordValue;
use gandr_storage_records::ValueLeafHasher;
use gandr_theory_spec_combinators::Holds;
use quenchant_shape::shape::Maybe;

use crate::error::ArtifactError;

mod value;

/// The byte width of a declaration record's key: one node identity.
pub const RECORD_KEY_LEN: usize = 0x20_usize;

/// The byte width of a count and of a slot in the order.
pub(crate) const SLOT_LEN: usize = 0x04_usize;

/// The byte width of a content name: the kernel's content key of an entry.
pub const CONTENT_NAME_LEN: usize = 0x20_usize;

/// The key the header record is stored under: the empty key, which sorts
/// first.
pub const HEADER_KEY: &[u8] = b"";

/// The key the order is stored under: one zero byte, which sorts after the
/// header's key and before every record key.
pub const ORDER_KEY: &[u8] = b"\x00";

/// The tag the order of a named set opens with: each place then holds its
/// record's key and the content name of its entry.
pub(crate) const NAMED: u8 = 0x01_u8;

/// The tag the order of a set cut from the artifact's bytes alone opens with:
/// each place then holds its record's key alone.
pub(crate) const FROM_BYTES: u8 = 0x02_u8;

quenchant_shape::reason_enum! {
    /// Why a place carries no content name.
    pub mod unnamed {
        /// The reason a place has no name.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The set was cut from the artifact's bytes alone, and no writer
            /// named its places.
            Bytes,
            /// The kernel computes no content key for the entry. A named set
            /// refuses such a place, so no stored artifact holds one.
            Unkeyed,
        }
    }
}

/// The form of an artifact's names. An artifact never mixes the two forms:
/// every place carries the kernel's content key of its entry, or none does.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Naming
{
    /// Each place carries the kernel's content key of its entry: the form of
    /// an admission whose artifact the store keeps.
    Named,
    /// No place carries a name: the form of an export cut from the
    /// artifact's bytes alone.
    Bytes,
}

impl From<Naming> for u8
{
    /// The tag that spells the form, in the order and in the manifest:
    /// [`NAMED`] or [`FROM_BYTES`].
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(naming: Naming) -> Self
    {
        match naming {
            Naming::Named => NAMED,
            Naming::Bytes => FROM_BYTES,
        }
    }
}

/// A declaration record's key: the identity of the value leaf that holds the
/// record's bytes.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RecordKey(NodeHash);

impl RecordKey
{
    /// The key of a declaration segment: the identity of its value leaf.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`ValueLeafHasher::hash`] of `segment`'s bytes, so equal
    ///   bytes give equal keys in every artifact.
    /// - provides: the one spelling of a declaration record's key, at one pass
    ///   over the bytes and with no copy of them.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the identity is its own definition; a postcondition
    ///   could only repeat it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two places with equal bytes share one record, and one
    ///   changed byte gives another key.
    /// - witness: `record::tests::equal_segments_share_one_record`
    #[inline]
    #[must_use]
    pub fn of(segment: SegmentBytes<'_>) -> Self
    {
        Self(ValueLeafHasher::new().hash(RecordValue::from(segment.0)))
    }
}

impl From<RecordKey> for NodeHash
{
    /// The identity of the value leaf the key names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(key: RecordKey) -> Self
    {
        key.0
    }
}

impl AsRef<[u8]> for RecordKey
{
    /// Borrows the key's bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        self.0.as_ref()
    }
}

/// The slot of each key among the distinct keys, which take their slots in
/// the order each first appears.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one slot per key; the first key of each distinct value takes the
///   next slot, and each later equal key takes that slot again.
/// - provides: the cut's and the read's dedup in one pass: an open-addressing
///   table whose probe starts at a key's leading bytes, which a digest spreads
///   evenly, so no sort and no search runs.
/// - fails: never.
/// - panics: none.
///
/// # Clause cost
/// - bound: one pass over the slots, and one sort of the distinct keys.
///
/// # Adequacy
/// - hypothesis: L2 — equal segments share one record and every set reads back;
///   L3 a key an order lists twice is refused at its second place.
/// - witness: `record::tests::equal_segments_share_one_record`
/// - witness: `tests::artifact_contract::a_stored_tree_with_misplaced_keys_is_refused`
#[spec(ensures: |ret| ret.len() == keys.len() && {
    let mut firsts: Vec<RecordKey> = Vec::new();
    ret.iter().zip(keys).all(|(&slot, &key)| match firsts.get(usize::from(slot)) {
        Some(&first) => first == key,
        None => usize::from(slot) == firsts.len() && {
            firsts.push(key);
            true
        },
    }) && {
        firsts.sort_unstable();
        firsts.is_sorted_by(|lower, higher| lower < higher)
    }
})]
fn slots_by_first_appearance(keys: &[RecordKey]) -> Vec<RecordIndex>
{
    // Twice the keys' room keeps the table at most half full, so each probe
    // meets an empty cell; a power of two lets a mask wrap the probe.
    let size = keys
        .len()
        .saturating_mul(2)
        .max(0x10_usize)
        .checked_next_power_of_two()
        .unwrap_or(1_usize << (usize::BITS - 1));
    let mask = size.saturating_sub(1);
    let wide_mask = u64::try_from(mask).unwrap_or(u64::MAX);
    let mut cells: Vec<Option<(RecordKey, RecordIndex)>> = alloc::vec![None; size];
    let mut slots = Vec::with_capacity(keys.len());
    let mut distinct = 0_usize;
    for &key in keys {
        let lead = key
            .0
            .as_ref()
            .first_chunk::<8>()
            .map_or(0_u64, |lead| u64::from_le_bytes(*lead));
        let mut cell = usize::try_from(lead & wide_mask).unwrap_or_default();
        let slot = loop {
            match cells.get_mut(cell) {
                Some(&mut Some((held, slot))) if held == key => break slot,
                Some(empty @ &mut None) => {
                    let slot = RecordIndex::from(distinct);
                    *empty = Some((key, slot));
                    distinct = distinct.saturating_add(1);
                    break slot;
                },
                _ => cell = cell.wrapping_add(1) & mask,
            }
        };
        slots.push(slot);
    }

    slots
}

/// The kernel's content key of an entry, as the order carries it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ContentName([u8; CONTENT_NAME_LEN]);

impl From<[u8; CONTENT_NAME_LEN]> for ContentName
{
    /// Reads the kernel's content key bytes as a name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: [u8; CONTENT_NAME_LEN]) -> Self
    {
        Self(bytes)
    }
}

impl AsRef<[u8]> for ContentName
{
    /// Borrows the name's bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        self.0.as_slice()
    }
}

/// One place of the order: the slot of the record that stands there.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Place
{
    /// The position of the place's record among the records of the set that
    /// holds the place, which stand in the order of their first place.
    slot: RecordIndex,
}

impl Place
{
    /// Returns the position of the place's record among the set's records.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn slot(&self) -> RecordIndex
    {
        self.slot
    }
}

/// The order of a record set as the one record it is stored as.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct OrderImage(Box<[u8]>);

impl AsRef<[u8]> for OrderImage
{
    /// Borrows the order's bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        &self.0
    }
}

/// Borrowed bytes of one artifact segment: the header, or one declaration's.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SegmentBytes<'segment>(&'segment [u8]);

impl<'segment> From<&'segment [u8]> for SegmentBytes<'segment>
{
    /// Reads a byte slice as segment bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: &'segment [u8]) -> Self
    {
        Self(bytes)
    }
}

impl AsRef<[u8]> for SegmentBytes<'_>
{
    /// Borrows the segment's bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        self.0
    }
}

/// The bytes a record set reassembles to: the header, then the segment at
/// each place of the order.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReassembledArtifact(Vec<u8>);

impl AsRef<[u8]> for ReassembledArtifact
{
    /// Borrows the reassembled bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        self.0.as_slice()
    }
}

impl ReassembledArtifact
{
    /// Borrows the reassembled bytes as an image for the kernel's decoder.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn as_image(&self) -> ArtifactImage<'_>
    {
        ArtifactImage::from(self.0.as_slice())
    }
}

/// One declaration record: its segment's bytes beside the identity of their
/// value leaf, which is the record's key.
///
/// # Specification
/// - requires: nothing; segment syntax belongs to kernel decoding.
/// - ensures: the key is [`RecordKey::of`] the segment.
/// - provides: the binding between a declaration segment and its key. The
///   record plane pairs the two ([`NamedValue`]), so no path makes a record
///   under another key, and a store admits its leaf with no second hash.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — each record a cut makes sits under the identity of its
///   bytes' value leaf.
/// - witness: `tests::artifact_contract::a_set_is_held_to_the_layout_s_segment_count`
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ArtifactRecord
{
    /// The segment's bytes under the identity of their value leaf.
    value: NamedValue,
}

impl ArtifactRecord
{
    /// Keys a declaration segment by the identity of its value leaf.
    ///
    /// # Specification
    /// - requires: nothing; whether the bytes are a segment is the decoder's
    ///   question when the set is read back.
    /// - ensures: the record carries [`RecordKey::of`] `segment` and a copy of
    ///   `segment`.
    /// - provides: the one constructor a declaration record has outside a cut
    ///   and a stored read.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 through reassembly and stored reads observes the key
    ///   and complete segment in a shared four-declaration artifact and 64
    ///   generated environments with at most 47 declarations of four kinds.
    /// - witness: `tests::artifact_contract::records_round_trip_to_a_byte_identical_artifact`
    /// - witness: `tests::artifact_contract::round_trip_over_generated_environments`
    #[spec(ensures: |ret| ret.key() == RecordKey::of(segment) && ret.segment().0 == segment.0)]
    #[inline]
    #[must_use]
    pub fn new(segment: SegmentBytes<'_>) -> Self
    {
        Self {
            value: ValueLeafHasher::new().named(RecordValue::from(segment.0)),
        }
    }

    /// Returns the record's key.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn key(&self) -> RecordKey
    {
        RecordKey(self.value.identity())
    }

    /// Returns the declaration segment's bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn segment(&self) -> SegmentBytes<'_>
    {
        SegmentBytes(<&[u8]>::from(self.value.value()))
    }
}

/// The record set a kernel artifact is.
///
/// It holds the header, the order of its places, the content name of each
/// place or why the set names none, and one record per distinct declaration
/// segment, unique by key, in the order of its first place.
///
/// # Specification
/// - requires: nothing; header and segment bytes need not decode as a kernel
///   artifact.
/// - ensures: keys are distinct and stand in the order of their first place,
///   each place's slot names a held record, each record stands at a place, and
///   a named set holds one name per place. Each record binds its key to its
///   bytes by construction.
/// - provides: canonical record ordering without certifying the payload.
/// - fails: the refinement rejects a place ahead of its turn, a duplicate, an
///   unheld and an unplaced record, and names that differ in number from the
///   places.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an empty set admits raw bytes; moving a place ahead of
///   its turn, repeating a record, dropping a placed record, adding an unplaced
///   one and dropping a name each violate a separate part of the refinement.
/// - witness: `record::tests::record_refinements_bind_keys_and_places`
#[spec(maintains: bool::from(self.well_formed()))]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ArtifactRecordSet
{
    /// The header preceding the first declaration segment.
    header: Box<[u8]>,
    /// One place per declaration, in admission order.
    places: Vec<Place>,
    /// The kernel's content key of the entry at each place, in the order of
    /// the places, or why the set names none.
    names: Maybe<Box<[ContentName]>, unnamed::Absent>,
    /// The declaration records, unique by key, in the order of their first
    /// place.
    records: Vec<ArtifactRecord>,
}

impl ArtifactRecordSet
{
    /// Whether the records are distinct by key and stand in the order of
    /// their first place, each bound to its bytes, each place's slot names a
    /// held record and each record stands at a place, and a named set holds
    /// one name per place.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: holds exactly when no two records share a key, each place's
    ///   slot is below the number of records and names either a record an
    ///   earlier place names or the next record no earlier place names, each
    ///   record stands at a place, and the names, when the set has them, are as
    ///   many as the places.
    /// - provides: the record set's invariant, which a clause reads through
    ///   this bound.
    /// - panics: none.
    /// - executable: none — this is the invariant's predicate; a postcondition
    ///   could only repeat its pass.
    ///
    /// # Clause cost
    /// - bound: one digest per record, one sort of the keys, and one step per
    ///   place. No function's clause reads the set's invariant; only its
    ///   witness does.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an empty set holds; a place ahead of its turn, a
    ///   repeated record, an unheld place, an unplaced record and a dropped
    ///   name each fail.
    /// - witness: `record::tests::record_refinements_bind_keys_and_places`
    fn well_formed(&self) -> Holds
    {
        let mut next = 0_usize;
        let in_turn = self.places.iter().all(|place| {
            let slot = usize::from(place.slot);
            if slot == next {
                next = next.saturating_add(1);
            }
            slot < next && slot < self.records.len()
        });
        let mut keys: Vec<RecordKey> = self.records.iter().map(ArtifactRecord::key).collect();
        keys.sort_unstable();
        let named = match self.names {
            Maybe::Present(ref names) => names.len() == self.places.len(),
            Maybe::Absent(_) => true,
        };
        Holds::from(
            keys.is_sorted_by(|lower, higher| lower < higher)
                && in_turn
                && next == self.records.len()
                && named,
        )
    }

    /// The set that `header` and `segments` make, one place per segment in
    /// the sequence given, the set unnamed for [`unnamed::Absent::Bytes`].
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one place per segment, in order, whose slot names the record
    ///   of its bytes; one record per distinct segment, in the order of its
    ///   first place.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — as [`from_artifact`](Self::from_artifact).
    /// - witness: `record::tests::equal_segments_share_one_record`
    #[spec(ensures: |ret| ret.header.as_ref() == header.0)]
    fn gathered<'segment, Segments>(
        header: SegmentBytes<'_>,
        segments: Segments,
    ) -> Self
    where
        Segments: IntoIterator<Item = SegmentBytes<'segment>>,
    {
        let hasher = ValueLeafHasher::new();
        let named: Vec<NamedValue> = segments
            .into_iter()
            .map(|segment| hasher.named(RecordValue::from(segment.0)))
            .collect();
        let keys: Vec<RecordKey> = named
            .iter()
            .map(|value| RecordKey(value.identity()))
            .collect();
        let slots = slots_by_first_appearance(&keys);
        let mut records = Vec::new();
        let mut places = Vec::with_capacity(slots.len());
        for (&slot, value) in slots.iter().zip(named) {
            // A slot past the records held is a segment's first appearance.
            if usize::from(slot) == records.len() {
                records.push(ArtifactRecord { value });
            }
            places.push(Place { slot });
        }

        Self {
            header: Box::from(header.0),
            places,
            names: Maybe::Absent(unnamed::Absent::Bytes),
            records,
        }
    }

    /// Cuts an artifact into its record set where the kernel's decoder finds
    /// its segments end.
    ///
    /// # Specification
    /// - requires: nothing; the bytes are arbitrary.
    /// - ensures: on success the header is the image up to the decoder's header
    ///   end, place `i` names the record of the bytes from the end before it to
    ///   its own, the set is unnamed for [`unnamed::Absent::Bytes`], and
    ///   [`ArtifactRecordSet::reassemble`] gives back exactly `image`.
    /// - provides: the commit path's only way in, so every set it builds was
    ///   decoded, budget-checked and delimited by the kernel first.
    /// - fails: [`ArtifactError::Kernel`] for any image the kernel's decoder
    ///   refuses; [`ArtifactError::SegmentBoundary`] for a reported end the
    ///   image does not hold, which a decode's own specification rules out.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ArtifactError::Kernel`] — the decoder refuses the image.
    /// - [`ArtifactError::SegmentBoundary`] — a reported end lies outside the
    ///   image.
    ///
    /// # Adequacy
    /// - hypothesis: L2 on a four-declaration environment sharing subterms and
    ///   64 generated environments of zero to 47 declarations, drawn from four
    ///   kinds, observes exact image reconstruction and declaration count. It
    ///   distinguishes dropped bytes, changed ordering and missing records.
    ///   Those valid-image witnesses do not establish every decoder refusal.
    /// - witness: `tests::artifact_contract::records_round_trip_to_a_byte_identical_artifact`
    /// - witness: `tests::artifact_contract::round_trip_over_generated_environments`
    #[spec(ensures: |ret| match ret {
        Ok(ref set) => bool::from(set.cuts(image)),
        Err(ArtifactError::Kernel { .. } | ArtifactError::SegmentBoundary { .. }) => true,
        Err(_) => false,
    })]
    #[inline]
    pub fn from_artifact(image: ArtifactImage<'_>) -> Result<Self, ArtifactError>
    {
        let decoded = decode(image)?;
        Self::cut(image, decoded.segments())
    }

    /// [`from_artifact`](Self::from_artifact), keeping what decoding the
    /// artifact's first `end` declarations left, for
    /// [`from_artifact_after`](Self::from_artifact_after) to resume.
    ///
    /// # Specification
    /// - requires: nothing; the bytes are arbitrary.
    /// - ensures: [`from_artifact`](Self::from_artifact)'s set or refusal, and
    ///   the prefix the kernel's `decode_keeping` keeps of its first `end`
    ///   declarations.
    /// - provides: the first commit of an editor's export, which decodes the
    ///   import closure's declarations once.
    /// - fails: as [`from_artifact`](Self::from_artifact).
    /// - panics: none.
    ///
    /// # Errors
    /// As [`from_artifact`](Self::from_artifact).
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a set cut after a kept prefix is the set cut whole.
    /// - witness: `tests::artifact_contract::a_set_cut_after_a_kept_prefix_is_the_whole_cut_776`
    #[spec(ensures: |ret| match ret {
        Ok((ref set, _)) => bool::from(set.cuts(image)),
        Err(ArtifactError::Kernel { .. } | ArtifactError::SegmentBoundary { .. }) => true,
        Err(_) => false,
    })]
    #[inline]
    pub fn from_artifact_keeping(
        image: ArtifactImage<'_>,
        end: ConstantIndex,
    ) -> Result<(Self, Maybe<DecodedPrefix, decoded_prefix::Absent>), ArtifactError>
    {
        let (decoded, prefix) = decode_keeping(image, end)?;
        Ok((Self::cut(image, decoded.segments())?, prefix))
    }

    /// [`from_artifact`](Self::from_artifact), decoding `image` after
    /// `prefix` when its segments lead with `prefix`'s.
    ///
    /// # Specification
    /// - requires: nothing; the bytes are arbitrary, and `prefix` was kept by
    ///   [`from_artifact_keeping`](Self::from_artifact_keeping).
    /// - ensures: [`from_artifact`](Self::from_artifact)'s set or refusal.
    /// - provides: each later commit of an editor's export, which decodes the
    ///   document's segments alone.
    /// - fails: as [`from_artifact`](Self::from_artifact).
    /// - panics: none.
    ///
    /// # Errors
    /// As [`from_artifact`](Self::from_artifact).
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a set cut after a kept prefix is the set cut whole.
    /// - witness: `tests::artifact_contract::a_set_cut_after_a_kept_prefix_is_the_whole_cut_776`
    #[spec(ensures: |ret| match ret {
        Ok(ref set) => bool::from(set.cuts(image)),
        Err(ArtifactError::Kernel { .. } | ArtifactError::SegmentBoundary { .. }) => true,
        Err(_) => false,
    })]
    #[inline]
    pub fn from_artifact_after(
        prefix: &DecodedPrefix,
        image: ArtifactImage<'_>,
    ) -> Result<Self, ArtifactError>
    {
        let decoded = decode_after(prefix, image)?;
        Self::cut(image, decoded.segments())
    }

    /// `image` cut at the boundaries `layout` reports.
    ///
    /// # Specification
    /// - requires: `layout` is a decode's of `image`.
    /// - ensures: the header is the image up to the header's end, and place `i`
    ///   names the record of [`SegmentLayout::declaration_segment`] at `i`.
    /// - fails: [`ArtifactError::SegmentBoundary`] for a reported end the image
    ///   does not hold, which a decode's own specification rules out.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — as [`from_artifact`](Self::from_artifact).
    /// - witness: `tests::artifact_contract::records_round_trip_to_a_byte_identical_artifact`
    /// - witness: `tests::artifact_contract::round_trip_over_generated_environments`
    #[spec(ensures: |ret| match ret {
        Ok(ref set) => set.places.len() == layout.declaration_ends().len(),
        Err(ArtifactError::SegmentBoundary { .. }) => true,
        Err(_) => false,
    })]
    fn cut(
        image: ArtifactImage<'_>,
        layout: &SegmentLayout,
    ) -> Result<Self, ArtifactError>
    {
        let bytes = image.as_ref();
        let header = bytes.get(.. usize::from(layout.header_end())).ok_or(
            ArtifactError::SegmentBoundary {
                position: RecordIndex::ZERO,
            },
        )?;
        let mut segments = Vec::with_capacity(layout.declaration_ends().len());
        for (offset, span) in layout.declaration_segments().enumerate() {
            segments.push(SegmentBytes(
                bytes
                    .get(usize::from(span.start) .. usize::from(span.end))
                    .ok_or_else(|| ArtifactError::SegmentBoundary {
                        position: RecordIndex::from(offset.saturating_add(1_usize)),
                    })?,
            ));
        }

        Ok(Self::gathered(SegmentBytes(header), segments))
    }

    /// Holds when the set is `image` cut at its segments: the header leads the
    /// image, the record at place `i` holds the bytes from the end before it
    /// to its own, and the last ends where the image does.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: holds exactly as stated.
    /// - provides: the postcondition every constructor that cuts an image
    ///   states.
    /// - panics: none.
    /// - executable: none — this is the postcondition's predicate; a
    ///   postcondition could only repeat its pass.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — as [`from_artifact`](Self::from_artifact).
    /// - witness: `tests::artifact_contract::records_round_trip_to_a_byte_identical_artifact`
    fn cuts(
        &self,
        image: ArtifactImage<'_>,
    ) -> Holds
    {
        let mut offset = self.header.len();
        let mut segments = self.segments();
        Holds::from(
            image.as_ref().starts_with(self.header.as_ref())
                && segments.all(|segment| {
                    let end = offset.saturating_add(segment.0.len());
                    let agrees = image.as_ref().get(offset .. end) == Some(segment.0);
                    offset = end;
                    agrees
                })
                && self.segments().len() == self.places.len()
                && offset == image.as_ref().len(),
        )
    }

    /// Builds a set from a header and the declaration segments in their
    /// order, the set unnamed for [`unnamed::Absent::Bytes`].
    ///
    /// # Specification
    /// - requires: nothing; neither the header nor the segments are checked
    ///   here, since a reader decodes what it reassembles.
    /// - ensures: one place per segment, in the order given; one record per
    ///   distinct segment, in the order of its first place.
    /// - provides: the general constructor, which a test forges a set through.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two equal segments make one record and two places,
    ///   and the set reassembles to both.
    /// - witness: `record::tests::equal_segments_share_one_record`
    #[spec(ensures: |ret| ret.header.as_ref() == header.0)]
    #[inline]
    #[must_use]
    pub fn from_segments<'segment, Segments>(
        header: SegmentBytes<'_>,
        segments: Segments,
    ) -> Self
    where
        Segments: IntoIterator<Item = SegmentBytes<'segment>>,
    {
        Self::gathered(header, segments)
    }

    /// The set with each place named as `names` names it, in order.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the set is [`Naming::Named`] with `names[i]` at
    ///   place `i`, and the header, the records and each place's record are as
    ///   they were.
    /// - provides: the writer's way to put the kernel's content key of each
    ///   entry beside its place. A kept artifact is named whole or not stored.
    /// - fails: [`ArtifactError::Misnamed`] naming the first place past the
    ///   names, the first name past the places, or the first place whose name
    ///   is absent.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ArtifactError::Misnamed`] — `names` and the places differ in number,
    /// or a place has no name.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a named set stored and read back holds each name at
    ///   its place; one name too few or too many is refused at the place where
    ///   the two counts part, and an absent name at its own place.
    /// - witness: `tests::artifact_contract::a_named_set_reads_back_with_its_names_7340`
    /// - witness: `record::tests::names_go_beside_their_places_in_order`
    #[spec(
        captures: count = self.places.len(),
        ensures: |ret| match ret {
            Ok(ref set) => match set.names {
                Maybe::Present(ref held) => held.iter().map(|&name| Maybe::Present(name)).eq(names.iter().copied()),
                Maybe::Absent(_) => false,
            },
            Err(ArtifactError::Misnamed { place }) => usize::from(place) == if names.len() == count {
                names.iter().position(|name| matches!(name, Maybe::Absent(_))).unwrap_or(count)
            } else {
                names.len().min(count)
            },
            Err(_) => false,
        },
    )]
    #[inline]
    pub fn named(
        mut self,
        names: &[Maybe<ContentName, unnamed::Absent>],
    ) -> Result<Self, ArtifactError>
    {
        if names.len() != self.places.len() {
            return Err(ArtifactError::Misnamed {
                place: RecordIndex::from(names.len().min(self.places.len())),
            });
        }
        let mut held = Vec::with_capacity(names.len());
        for (place, &name) in names.iter().enumerate() {
            match name {
                Maybe::Present(name) => held.push(name),
                Maybe::Absent(_) => {
                    return Err(ArtifactError::Misnamed {
                        place: RecordIndex::from(place),
                    });
                },
            }
        }
        self.names = Maybe::Present(held.into_boxed_slice());

        Ok(self)
    }

    /// Reads a stored artifact back into a set: the two records of its index
    /// tree, then the value leaf of each record the order names.
    ///
    /// # Specification
    /// - requires: `stored` is strictly ascending by key, as a record tree's
    ///   records are.
    /// - ensures: on success the first record is the header, under
    ///   [`HEADER_KEY`]; the second and last is the order, under [`ORDER_KEY`];
    ///   the order's keys are distinct and stand in the order of their first
    ///   place, each place's slot names one of them, each stands at a place,
    ///   and each names a value leaf that `store` holds, whose value is the
    ///   record's bytes.
    /// - provides: the read path's key check: the store's verified load hashes
    ///   each leaf once, and that hash is the record's key. The order is read
    ///   whole before any leaf is loaded.
    /// - fails: [`ArtifactError::MisplacedRecord`] naming the first stored
    ///   record whose key is not the one its position requires (the empty set
    ///   fails at position zero, and a record past the order at position two),
    ///   the first key of the order, counted from two, that repeats a key
    ///   before it, or the first key a place names before its turn;
    ///   [`ArtifactError::MalformedOrder`] naming place zero for an order that
    ///   opens with no form or holds fewer keys than it counts, and otherwise
    ///   the first place the order does not hold whole;
    ///   [`ArtifactError::UnheldRecord`] naming the first place whose slot is
    ///   past the keys; [`ArtifactError::UnplacedRecord`] naming the first key,
    ///   counted from two, that no place names; and [`ArtifactError::Records`]
    ///   for a leaf the store does not hold or cannot authenticate, or a node
    ///   that is not a value leaf.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ArtifactError::MisplacedRecord`] — a record's key is not the one its
    ///   position requires.
    /// - [`ArtifactError::MalformedOrder`] — the order holds bytes that are not
    ///   a place.
    /// - [`ArtifactError::UnheldRecord`] — a place names a record the order
    ///   does not hold.
    /// - [`ArtifactError::UnplacedRecord`] — a record stands at no place.
    /// - [`ArtifactError::Records`] — a leaf does not load as a value leaf.
    ///
    /// # Adequacy
    /// - hypothesis: L2 through stored reads observes complete reconstruction
    ///   for one- and 300-declaration artifacts. L3 supplies a missing header,
    ///   a missing order, a record past the order, keys out of order, an order
    ///   cut short, a slot past the keys, a key at no place and a leaf the
    ///   store does not hold, and observes each refusal at its exact position.
    /// - witness: `tests::artifact_contract::a_stored_tree_with_misplaced_keys_is_refused`
    /// - witness: `tests::artifact_contract::tree_nodes_store_and_reopen`
    #[inline]
    #[spec(ensures: |ret| match ret {
        Ok(ref set) => stored.len() == 2 && stored.first().is_some_and(|header| {
            header.key().as_ref() == HEADER_KEY && set.header.as_ref() == header.value().as_ref()
        }),
        Err(
            ArtifactError::MisplacedRecord { .. }
            | ArtifactError::MalformedOrder { .. }
            | ArtifactError::UnheldRecord { .. }
            | ArtifactError::UnplacedRecord { .. }
            | ArtifactError::Records { .. },
        ) => true,
        Err(_) => false,
    })]
    pub fn from_stored<S>(
        stored: &[Record],
        store: &S,
    ) -> Result<Self, ArtifactError>
    where
        S: BlockStore + ?Sized,
    {
        let misplaced = |position: usize| ArtifactError::MisplacedRecord {
            position: RecordIndex::from(position),
        };
        let header = stored
            .first()
            .filter(|header| header.key().as_ref() == HEADER_KEY)
            .ok_or_else(|| misplaced(0_usize))?;
        let order = stored
            .get(1_usize)
            .filter(|order| order.key().as_ref() == ORDER_KEY)
            .ok_or_else(|| misplaced(1_usize))?;
        if stored.len() > 2_usize {
            return Err(misplaced(2_usize));
        }
        // The order opens with its form and the number of keys, then holds
        // each key, then each place at the width the form gives: the slot of
        // its record, and the name when the set has names.
        let unformed = ArtifactError::MalformedOrder {
            place: RecordIndex::ZERO,
        };
        let order_value = order.value();
        let (naming, order) = match order_value.as_ref().split_first() {
            Some((&NAMED, rest)) => (Naming::Named, rest),
            Some((&FROM_BYTES, rest)) => (Naming::Bytes, rest),
            _ => return Err(unformed),
        };
        let (&count, order) = order
            .split_first_chunk::<SLOT_LEN>()
            .ok_or_else(|| unformed.clone())?;
        let count = usize::try_from(u32::from_le_bytes(count)).map_err(|_wide| unformed.clone())?;
        // The count is the order's claim, so it reserves nothing until the
        // order holds that many keys.
        let (keys, mut order) = order
            .split_at_checked(count.saturating_mul(RECORD_KEY_LEN))
            .ok_or(unformed)?;
        let keys = keys.as_chunks::<RECORD_KEY_LEN>().0;
        let keys: Vec<RecordKey> = keys
            .iter()
            .map(|&key| RecordKey(NodeHash::from(key)))
            .collect();
        if let Some(repeat) = slots_by_first_appearance(&keys)
            .iter()
            .enumerate()
            .position(|(position, &slot)| usize::from(slot) != position)
        {
            return Err(misplaced(repeat.saturating_add(2_usize)));
        }
        let width = match naming {
            Naming::Named => SLOT_LEN.saturating_add(CONTENT_NAME_LEN),
            Naming::Bytes => SLOT_LEN,
        };
        let places_held = order.len().checked_div(width).unwrap_or_default();
        let mut places = Vec::with_capacity(places_held);
        let mut names = Vec::with_capacity(match naming {
            Naming::Named => places_held,
            Naming::Bytes => 0_usize,
        });
        // Each key takes its turn at its first place: a place names a key an
        // earlier place names, or the next key no place has named.
        let mut next = 0_usize;
        while !order.is_empty() {
            let place = RecordIndex::from(places.len());
            let malformed = ArtifactError::MalformedOrder { place };
            let Some((&slot, rest)) = order.split_first_chunk::<SLOT_LEN>()
            else {
                return Err(malformed);
            };
            order = match naming {
                Naming::Named => {
                    let Some((&name, rest)) = rest.split_first_chunk::<CONTENT_NAME_LEN>()
                    else {
                        return Err(malformed);
                    };
                    names.push(ContentName(name));
                    rest
                },
                Naming::Bytes => rest,
            };
            let slot = usize::try_from(u32::from_le_bytes(slot))
                .ok()
                .filter(|&slot| slot < keys.len())
                .ok_or(ArtifactError::UnheldRecord { place })?;
            if slot == next {
                next = next.saturating_add(1);
            }
            else if slot > next {
                return Err(misplaced(slot.saturating_add(2_usize)));
            }
            places.push(Place {
                slot: RecordIndex::from(slot),
            });
        }
        if next < keys.len() {
            return Err(ArtifactError::UnplacedRecord {
                position: RecordIndex::from(next.saturating_add(2_usize)),
            });
        }
        let mut records = Vec::with_capacity(keys.len());
        for key in keys {
            records.push(ArtifactRecord {
                value: NamedValue::load(store, NodeHash::from(key))?,
            });
        }
        let set = Self {
            header: Box::from(header.value().as_ref()),
            places,
            names: match naming {
                Naming::Named => Maybe::Present(names.into_boxed_slice()),
                Naming::Bytes => Maybe::Absent(unnamed::Absent::Bytes),
            },
            records,
        };

        Ok(set)
    }

    /// Returns the header carried for reassembly.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn header(&self) -> SegmentBytes<'_>
    {
        SegmentBytes(&self.header)
    }

    /// Returns the declaration records, in the order of their first place.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn records(&self) -> &[ArtifactRecord]
    {
        self.records.as_slice()
    }

    /// Returns the places, in admission order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn places(&self) -> &[Place]
    {
        self.places.as_slice()
    }

    /// Returns the kernel's content key of the entry at each place, in
    /// admission order, or why the set names none.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn names(&self) -> Maybe<&[ContentName], unnamed::Absent>
    {
        match self.names {
            Maybe::Present(ref names) => Maybe::Present(names),
            Maybe::Absent(absent) => Maybe::Absent(absent),
        }
    }

    /// Returns the form of the set's names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn naming(&self) -> Naming
    {
        match self.names {
            Maybe::Present(_) => Naming::Named,
            Maybe::Absent(_) => Naming::Bytes,
        }
    }

    /// Returns the segment at each place, in admission order.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one segment per place whose record the set holds, which the
    ///   invariant makes every place.
    /// - provides: the walk that reassembly, the boundary check and the value
    ///   plane read.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the result is an iterator, which a postcondition
    ///   could not read without spending it.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — as [`reassemble`](Self::reassemble).
    /// - witness: `tests::artifact_contract::records_round_trip_to_a_byte_identical_artifact`
    #[inline]
    #[must_use]
    pub fn segments(&self) -> impl ExactSizeIterator<Item = SegmentBytes<'_>> + '_
    {
        self.places.iter().map(|place| {
            self.records
                .get(usize::from(place.slot))
                .map_or(SegmentBytes(&[]), ArtifactRecord::segment)
        })
    }

    /// Returns the order as the one record it is stored as.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the form's tag; the number of records, four bytes
    ///   little-endian; each record's [`RECORD_KEY_LEN`] bytes in the order of
    ///   its first place; then each place in admission order: its slot, four
    ///   bytes little-endian, and the [`CONTENT_NAME_LEN`] bytes of its name
    ///   when the set is [`Naming::Named`].
    /// - provides: the order's value for [`record_refs`](Self::record_refs).
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a set stored and read back is the set.
    /// - witness: `tests::artifact_contract::tree_nodes_store_and_reopen`
    /// - witness: `tests::artifact_contract::a_named_set_reads_back_with_its_names_7340`
    #[spec(ensures: |ret| ret.0.len() == self.places.len().saturating_mul(match self.names {
        Maybe::Present(_) => SLOT_LEN.saturating_add(CONTENT_NAME_LEN),
        Maybe::Absent(_) => SLOT_LEN,
    }).saturating_add(self.records.len().saturating_mul(RECORD_KEY_LEN))
        .saturating_add(SLOT_LEN.saturating_add(1)))]
    #[inline]
    #[must_use]
    pub fn order_image(&self) -> OrderImage
    {
        let width = match self.names {
            Maybe::Present(_) => SLOT_LEN.saturating_add(CONTENT_NAME_LEN),
            Maybe::Absent(_) => SLOT_LEN,
        };
        let mut order = Vec::with_capacity(
            self.places
                .len()
                .saturating_mul(width)
                .saturating_add(self.records.len().saturating_mul(RECORD_KEY_LEN))
                .saturating_add(SLOT_LEN.saturating_add(1_usize)),
        );
        // A set of more than `u32::MAX` records holds an order past the record
        // plane's node budget, which the tree refuses; so the ceiling here
        // names no stored order.
        let narrow = |count: usize| u32::try_from(count).unwrap_or(u32::MAX).to_le_bytes();
        order.push(u8::from(self.naming()));
        order.extend_from_slice(&narrow(self.records.len()));
        for record in &self.records {
            order.extend_from_slice(record.key().as_ref());
        }
        match self.names {
            Maybe::Present(ref names) => {
                for (place, name) in self.places.iter().zip(names.iter()) {
                    order.extend_from_slice(&narrow(usize::from(place.slot)));
                    order.extend_from_slice(&name.0);
                }
            },
            Maybe::Absent(_) => {
                for place in &self.places {
                    order.extend_from_slice(&narrow(usize::from(place.slot)));
                }
            },
        }

        OrderImage(order.into_boxed_slice())
    }

    /// Returns the set's index as record-plane records: the header under
    /// [`HEADER_KEY`], then the order under [`ORDER_KEY`].
    ///
    /// # Specification
    /// - requires: `order` is [`order_image`](Self::order_image)'s.
    /// - ensures: the two records, strictly ascending by key.
    /// - provides: the input the index tree is built from.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 through building, storing and reopening a one- and a
    ///   300-declaration artifact observes ordered keys and every record value.
    ///   Perturbing the header or a segment changes the stored identity.
    /// - witness: `tests::artifact_contract::tree_nodes_store_and_reopen`
    /// - witness: `tests::artifact_contract::any_perturbation_changes_the_identity`
    #[spec(ensures: |ret| ret.first().is_some_and(|header| header.key().as_ref() == HEADER_KEY)
        && ret.last().is_some_and(|order| order.key().as_ref() == ORDER_KEY))]
    #[inline]
    #[must_use]
    pub fn record_refs<'set>(
        &'set self,
        order: &'set OrderImage,
    ) -> [RecordRef<'set>; 2]
    {
        [
            RecordRef::new(HEADER_KEY, &*self.header),
            RecordRef::new(ORDER_KEY, &*order.0),
        ]
    }

    /// Admits the value leaf of each record into `store`, under the record's
    /// key.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success `store` holds the value leaf of each record, under
    ///   its key.
    /// - provides: the commit path's write of the records, beside the index
    ///   tree. Each record's leaf is admitted as a [`NamedValue`], so a store
    ///   that overrides [`BlockStore::admit_value`] hashes no record again.
    /// - fails: [`ArtifactError::Records`] for a leaf past the node budget, or
    ///   a leaf the store does not admit.
    /// - panics: none.
    /// - executable: none — a postcondition that loaded every leaf would walk
    ///   the set's records.
    ///
    /// # Errors
    /// [`ArtifactError::Records`] — the record plane refuses a leaf.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every stored read loads each leaf this writes.
    /// - witness: `tests::artifact_contract::tree_nodes_store_and_reopen`
    #[inline]
    pub(crate) fn write_leaves<S>(
        &self,
        store: &mut S,
    ) -> Result<(), ArtifactError>
    where
        S: BlockStore + ?Sized,
    {
        for record in &self.records {
            store.admit_value(&record.value)?;
        }

        Ok(())
    }

    /// Reassembles the artifact: the header, then the segment at each place.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the concatenation of the header and the segments in the
    ///   order's sequence; for a set [`ArtifactRecordSet::from_artifact`]
    ///   built, exactly that image.
    /// - provides: the bytes a reader hands the kernel's decoder.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 on the shared four-declaration artifact and 64
    ///   generated environments of zero to 47 declarations observes every
    ///   reassembled byte against the kernel encoder, distinguishing misplaced
    ///   headers, segment loss and reordered bytes.
    /// - witness: `tests::artifact_contract::records_round_trip_to_a_byte_identical_artifact`
    /// - witness: `tests::artifact_contract::round_trip_over_generated_environments`
    #[inline]
    #[spec(ensures: |ret| ret.0.starts_with(self.header.as_ref()))]
    #[must_use]
    pub fn reassemble(&self) -> ReassembledArtifact
    {
        let length = self.segments().fold(self.header.len(), |total, segment| {
            total.saturating_add(segment.0.len())
        });
        let mut bytes = Vec::with_capacity(length);
        bytes.extend_from_slice(&self.header);
        for segment in self.segments() {
            bytes.extend_from_slice(segment.0);
        }

        ReassembledArtifact(bytes)
    }

    /// Refuses a set whose places are not cut at the decoded artifact's
    /// segment boundaries.
    ///
    /// # Specification
    /// - requires: `layout` is the segment layout of a decode of
    ///   [`ArtifactRecordSet::reassemble`]'s image.
    /// - ensures: success exactly when the header ends at the layout's header
    ///   end, the set holds one place per declaration segment, and the record
    ///   at each place ends at its segment's end.
    /// - provides: the read path's guarantee that the stored cuts are the
    ///   reader's, not a writer's: bytes that decode are still refused when a
    ///   record straddles two segments or splits one.
    /// - fails: [`ArtifactError::SegmentBoundary`] naming the first place, from
    ///   one, whose record ends where no segment does, or the position past the
    ///   shorter of the two sequences when their lengths differ.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ArtifactError::SegmentBoundary`] — a record ends where the artifact
    /// has no segment boundary.
    ///
    /// # Adequacy
    /// - hypothesis: L3 on one four-declaration artifact shifts the header and
    ///   first declaration cuts separately while preserving all image bytes,
    ///   observing positions zero and one. The unshifted artifact is admitted.
    /// - witness: `tests::artifact_contract::records_cut_off_a_segment_boundary_are_refused`
    #[spec(ensures: |ret| match ret {
        Ok(()) => self.header.len() == usize::from(layout.header_end())
            && layout.declaration_ends().len() == self.places.len(),
        Err(ArtifactError::SegmentBoundary { .. }) => true,
        Err(_) => false,
    })]
    #[inline]
    pub fn ensure_cut_at(
        &self,
        layout: &SegmentLayout,
    ) -> Result<(), ArtifactError>
    {
        let mut end = self.header.len();
        if end != usize::from(layout.header_end()) {
            return Err(ArtifactError::SegmentBoundary {
                position: RecordIndex::ZERO,
            });
        }
        let ends = layout.declaration_ends();
        for (offset, segment) in self.segments().enumerate() {
            let position = RecordIndex::from(offset.saturating_add(1_usize));
            end = end.saturating_add(segment.0.len());
            let Some(&expected) = ends.get(offset)
            else {
                return Err(ArtifactError::SegmentBoundary { position });
            };
            if end != usize::from(expected) {
                return Err(ArtifactError::SegmentBoundary { position });
            }
        }
        if ends.len() != self.places.len() {
            return Err(ArtifactError::SegmentBoundary {
                position: RecordIndex::from(self.places.len().saturating_add(1_usize)),
            });
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests
{
    use alloc::boxed::Box;
    use alloc::vec;

    use gandr_storage_records::RecordIndex;
    use quenchant_shape::shape::Maybe;

    use super::ArtifactRecordSet;
    use super::ContentName;
    use super::Naming;
    use super::RecordKey;
    use super::SegmentBytes;
    use super::unnamed;
    use crate::error::ArtifactError;

    /// Two places with equal bytes share one record, reassemble to both, and
    /// one changed byte gives another key.
    #[test]
    fn equal_segments_share_one_record()
    {
        let header = SegmentBytes::from(b"header".as_slice());
        let set = ArtifactRecordSet::from_segments(
            header,
            [b"alpha".as_slice(), b"beta", b"alpha"].map(SegmentBytes::from),
        );
        assert_eq!(3, set.places().len(), "one place per segment");
        assert_eq!(2, set.records().len(), "one record per distinct segment");
        assert_eq!(
            set.places().first().map(super::Place::slot),
            set.places().last().map(super::Place::slot),
            "the two alphas name one record"
        );
        assert_eq!(
            b"headeralphabetaalpha".as_slice(),
            set.reassemble().as_ref()
        );
        assert_ne!(
            RecordKey::of(SegmentBytes::from(b"alpha".as_slice())),
            RecordKey::of(SegmentBytes::from(b"alphb".as_slice())),
            "one changed byte gives another key"
        );
    }

    /// Names stand beside their places in order; a count that differs is
    /// refused where the two counts part, and an absent name at its own place.
    #[test]
    fn names_go_beside_their_places_in_order()
    {
        let header = SegmentBytes::from(b"h".as_slice());
        let set = ArtifactRecordSet::from_segments(
            header,
            [b"a".as_slice(), b"b"].map(SegmentBytes::from),
        );
        assert_eq!(Naming::Bytes, set.naming());
        assert_eq!(Maybe::Absent(unnamed::Absent::Bytes), set.names());
        let first = ContentName::from([7; 32]);
        let second = ContentName::from([9; 32]);
        let names = [Maybe::Present(first), Maybe::Present(second)];
        let named = set.clone().named(&names).expect("one name per place");
        assert_eq!(Naming::Named, named.naming());
        assert_eq!(Maybe::Present([first, second].as_slice()), named.names());
        assert_eq!(set.reassemble(), named.reassemble(), "a name moves no byte");
        assert_eq!(
            Err(ArtifactError::Misnamed {
                place: RecordIndex::from(1_usize)
            }),
            set.clone().named(names.get(.. 1).expect("one name")),
        );
        assert_eq!(
            Err(ArtifactError::Misnamed {
                place: RecordIndex::from(2_usize)
            }),
            set.clone().named(&[names[0], names[1], names[0]]),
        );
        assert_eq!(
            Err(ArtifactError::Misnamed {
                place: RecordIndex::from(1_usize)
            }),
            set.named(&[names[0], Maybe::Absent(unnamed::Absent::Unkeyed)]),
            "a named set names every place"
        );
    }

    /// Refinement separates ordered identity from unvalidated payload bytes.
    #[test]
    fn record_refinements_bind_keys_and_places()
    {
        let empty =
            ArtifactRecordSet::from_segments(SegmentBytes::from(b"unvalidated".as_slice()), vec![]);
        assert!(anodized::types::Spec::predicate(&empty));
        assert!(gandr_kernel_term::decode(empty.reassemble().as_image()).is_err());

        let set = ArtifactRecordSet::from_segments(
            SegmentBytes::from(b"h".as_slice()),
            [b"zero".as_slice(), b"one", b"two", b"three"].map(SegmentBytes::from),
        );
        assert!(anodized::types::Spec::predicate(&set));

        let mut early = set.clone();
        early.places.swap(0, 1);
        assert!(!anodized::types::Spec::predicate(&early));
        let mut duplicate = set.clone();
        duplicate
            .records
            .insert(1, duplicate.records.first().expect("first record").clone());
        assert!(!anodized::types::Spec::predicate(&duplicate));
        let mut unheld = set.clone();
        let _dropped = unheld.records.pop();
        assert!(!anodized::types::Spec::predicate(&unheld));
        let mut short = set
            .clone()
            .named(&[Maybe::Present(ContentName::from([1; 32])); 4])
            .expect("one name per place");
        assert!(anodized::types::Spec::predicate(&short));
        short.names = Maybe::Present(Box::from([ContentName::from([1; 32])].as_slice()));
        assert!(!anodized::types::Spec::predicate(&short));
        let mut unplaced = set;
        let _dropped = unplaced.places.pop();
        assert!(!anodized::types::Spec::predicate(&unplaced));
    }
}
