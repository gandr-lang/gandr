//! The declaration-record model: a kernel artifact as a set of records, each
//! keyed by the digest of its own bytes, and the order the records stand in.
//!
//! # The records
//!
//! ```text
//! key                          value
//! ""                           header: magic, version, minted-atom table, count
//! 0x00                         the order: one place per declaration
//! BLAKE3(domain || segment)    one declaration segment, once per distinct segment
//! ```
//!
//! | Key | Value |
//! | --- | ----- |
//! | the empty key | the header: magic, version, minted-atom table, declaration count |
//! | [`ORDER_KEY`], one zero byte | the order: [`PLACE_LEN`] bytes per declaration, in admission order |
//! | the digest of a segment, [`RECORD_KEY_LEN`] bytes | that declaration segment |
//!
//! A record's key is the digest of its own bytes under [`RECORD_DOMAIN`]. So
//! one key names one byte string in every artifact that holds it. Two
//! artifacts that differ by one declaration share each record whose bytes the
//! edit leaves, at any position. Two places with equal bytes share one record.
//!
//! The order is the one record that an insertion always rewrites. Each place
//! holds a tag, the key of the record that stands there, and the kernel's
//! content key of the entry when the writer gives one. The tag tells why a
//! place has no name: the set was cut from bytes alone, or the kernel computes
//! no key for the entry. A place without a name holds zeros in its name.
//!
//! The empty key sorts first. A shorter key sorts before each longer key that
//! it leads, so the order's one byte sorts before every digest. The header and
//! the order are thus the first two records of every stored tree.
//!
//! A declaration segment may reference subterm-table entries that an earlier
//! segment introduced, and constants by their admission index. So a record is
//! a content-addressing grain, never an independently decodable unit: a reader
//! reassembles the whole image in the order's sequence and decodes it once.
//! Those references move a record whose declaration does not change. The
//! references part of #7340 removes them, and the key stays.
//!
//! Executable record refinements bind each key to the digest of its bytes,
//! require strictly increasing keys, and require each place to name a held
//! record and each record to stand at a place. Raw header and segment bytes
//! remain admissible; those refinements do not certify kernel validity.
//!
//! **Choice.** A record's key is the digest of its own bytes, and the order is
//! a record of its own. **Alternatives.** The admission index as the key moves
//! every record past an insertion. A probe of 2,000 declarations shares 28 of
//! the 1,000 records past one insertion under that key. The kernel's content
//! key shares 600 of them. But while references stay positional, one content
//! key names several byte strings: 16 keys held 816 segments. The digest
//! shares the same 600, and it names one byte string. **Reversal.** None
//! planned: the references part changes the bytes and not the key.
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
//! scanner here reads `NODE_TAG_TABLE`'s storage columns, and the record
//! plane's content-defined leaves group whole records. The declaration boundary
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
use gandr_storage_records::Record;
use gandr_storage_records::RecordIndex;
use gandr_storage_records::RecordRef;
use gandr_theory_spec_combinators::Holds;
use quenchant_shape::shape::Maybe;

use crate::error::ArtifactError;

mod value;

/// The byte width of a declaration record's key: one BLAKE3 output.
pub const RECORD_KEY_LEN: usize = 0x20_usize;

/// The domain a record's digest opens with, inside the hashed preimage.
pub const RECORD_DOMAIN: &[u8] = b"gandr:storage-artifact:record:v1";

/// The byte width of a content name: the kernel's content key of an entry.
pub const CONTENT_NAME_LEN: usize = 0x20_usize;

/// The byte width of one place of the order: a tag, a record key and a
/// content name.
pub const PLACE_LEN: usize = 0x41_usize;

/// The key the header record is stored under: the empty key, which sorts
/// first.
pub const HEADER_KEY: &[u8] = b"";

/// The key the order is stored under: one zero byte, which sorts after the
/// header's key and before every record key.
pub const ORDER_KEY: &[u8] = b"\x00";

/// The tag of a place that carries a content name.
const NAMED: u8 = 0x01_u8;

/// The tag of a place cut from the artifact's bytes alone.
const FROM_BYTES: u8 = 0x02_u8;

/// The tag of a place whose entry the kernel computes no key for.
const UNKEYED: u8 = 0x03_u8;

quenchant_shape::reason_enum! {
    /// Why a place of the order carries no content name.
    pub mod unnamed {
        /// The reason a place has no name.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The set was cut from the artifact's bytes alone, and no writer
            /// named its places.
            Bytes,
            /// The kernel computes no content key for the entry.
            Unkeyed,
        }
    }
}

/// A declaration record's key: the digest of the record's own bytes.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RecordKey([u8; RECORD_KEY_LEN]);

impl RecordKey
{
    /// The key of a declaration segment: BLAKE3 over [`RECORD_DOMAIN`] and
    /// the segment's bytes.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the digest of the domain followed by `segment`'s bytes, so
    ///   equal bytes give equal keys in every artifact.
    /// - provides: the one spelling of a declaration record's key.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two places with equal bytes share one record, and one
    ///   changed byte gives another key.
    /// - witness: `record::tests::equal_segments_share_one_record`
    #[inline]
    #[must_use]
    pub fn of(segment: SegmentBytes<'_>) -> Self
    {
        let mut hasher = blake3::Hasher::new();
        hasher.update(RECORD_DOMAIN);
        hasher.update(segment.0);

        Self(*hasher.finalize().as_bytes())
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
        self.0.as_slice()
    }
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

/// One place of the order: the key of the record that stands there, and the
/// kernel's name of the entry.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Place
{
    /// The key of the record that stands at the place.
    record: RecordKey,
    /// The kernel's content key of the entry, or why the place has none.
    name: Maybe<ContentName, unnamed::Absent>,
}

impl Place
{
    /// Returns the key of the record that stands at the place.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn record(&self) -> RecordKey
    {
        self.record
    }

    /// Returns the kernel's content key of the entry, or why the place has
    /// none.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn name(&self) -> Maybe<ContentName, unnamed::Absent>
    {
        self.name
    }

    /// Appends the place's [`PLACE_LEN`] bytes to `order`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `order` grows by [`PLACE_LEN`] bytes: the tag, the record
    ///   key, and the name or zeros.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a named set stored and read back holds each name at
    ///   its place.
    /// - witness: `tests::artifact_contract::a_named_set_reads_back_with_its_names_7340`
    fn write_to(
        &self,
        order: &mut Vec<u8>,
    )
    {
        let (tag, name) = match self.name {
            Maybe::Present(name) => (NAMED, name.0),
            Maybe::Absent(unnamed::Absent::Bytes) => (FROM_BYTES, [0_u8; CONTENT_NAME_LEN]),
            Maybe::Absent(unnamed::Absent::Unkeyed) => (UNKEYED, [0_u8; CONTENT_NAME_LEN]),
        };
        order.push(tag);
        order.extend_from_slice(&self.record.0);
        order.extend_from_slice(&name);
    }

    /// Reads one place from its [`PLACE_LEN`] bytes.
    ///
    /// # Specification
    /// - requires: nothing; the bytes are arbitrary.
    /// - ensures: on success the place [`Place::write_to`] wrote as `bytes`.
    /// - fails: [`ArtifactError::MalformedOrder`] naming `place` for a tag that
    ///   no place carries, a name beside a tag without one, or a width other
    ///   than [`PLACE_LEN`].
    /// - panics: none.
    ///
    /// # Errors
    /// [`ArtifactError::MalformedOrder`] — the bytes are not a place.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a stored order with a foreign tag is refused at its
    ///   place.
    /// - witness: `tests::artifact_contract::a_stored_tree_with_misplaced_keys_is_refused`
    fn read(
        bytes: &[u8],
        place: RecordIndex,
    ) -> Result<Self, ArtifactError>
    {
        let malformed = ArtifactError::MalformedOrder { place };
        let Some((&tag, rest)) = bytes.split_first()
        else {
            return Err(malformed);
        };
        let Some((record, name)) = rest.split_first_chunk::<RECORD_KEY_LEN>()
        else {
            return Err(malformed);
        };
        let Ok(&name) = <&[u8; CONTENT_NAME_LEN]>::try_from(name)
        else {
            return Err(malformed);
        };
        let unnamed = name == [0_u8; CONTENT_NAME_LEN];
        let name = match tag {
            NAMED => Maybe::Present(ContentName(name)),
            FROM_BYTES if unnamed => Maybe::Absent(unnamed::Absent::Bytes),
            UNKEYED if unnamed => Maybe::Absent(unnamed::Absent::Unkeyed),
            _ => return Err(malformed),
        };

        Ok(Self {
            record: RecordKey(*record),
            name,
        })
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

/// One declaration record: the digest of its bytes, and its segment's bytes.
///
/// # Specification
/// - requires: nothing; segment syntax belongs to kernel decoding.
/// - ensures: the key is [`RecordKey::of`] the segment.
/// - provides: the binding between a declaration segment and its key.
/// - fails: the refinement rejects a key that is not the digest of the bytes.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a record whose key is changed fails the refinement, and
///   raw segments remain admissible.
/// - witness: `record::tests::record_refinements_bind_keys_and_places`
#[spec(maintains: self.key == RecordKey::of(SegmentBytes(&self.segment)))]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ArtifactRecord
{
    /// The digest of the segment's bytes.
    key: RecordKey,
    /// The declaration segment's bytes.
    segment: Box<[u8]>,
}

impl ArtifactRecord
{
    /// Keys a declaration segment by the digest of its bytes.
    ///
    /// # Specification
    /// - requires: nothing; whether the bytes are a segment is the decoder's
    ///   question when the set is read back.
    /// - ensures: the record carries [`RecordKey::of`] `segment` and a copy of
    ///   `segment`.
    /// - provides: the one constructor a declaration record has.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 through reassembly and stored reads observes the key
    ///   and complete segment in a shared four-declaration artifact and 64
    ///   generated environments with at most 47 declarations of four kinds.
    /// - witness: `tests::artifact_contract::records_round_trip_to_a_byte_identical_artifact`
    /// - witness: `tests::artifact_contract::round_trip_over_generated_environments`
    #[spec(ensures: |ret| ret.key == RecordKey::of(segment) && ret.segment.as_ref() == segment.0)]
    #[inline]
    #[must_use]
    pub fn new(segment: SegmentBytes<'_>) -> Self
    {
        Self {
            key: RecordKey::of(segment),
            segment: Box::from(segment.0),
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
        self.key
    }

    /// Returns the declaration segment's bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn segment(&self) -> SegmentBytes<'_>
    {
        SegmentBytes(&self.segment)
    }
}

/// The record set a kernel artifact is: its header, the order of its places,
/// and one record per distinct declaration segment, strictly ascending and
/// unique by key.
///
/// # Specification
/// - requires: nothing; header and segment bytes need not decode as a kernel
///   artifact.
/// - ensures: each record binds its key to its bytes, keys are strictly
///   increasing, each place names a held record, and each record stands at a
///   place.
/// - provides: canonical record ordering without certifying the payload.
/// - fails: the refinement rejects miskeyed, reversed, duplicate, unheld and
///   unplaced records.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an empty set admits raw bytes; reversing two records,
///   repeating one, changing a key, dropping a placed record and adding an
///   unplaced one each violate a separate part of the refinement.
/// - witness: `record::tests::record_refinements_bind_keys_and_places`
#[spec(maintains: bool::from(self.well_formed()))]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ArtifactRecordSet
{
    /// The header preceding the first declaration segment.
    header: Box<[u8]>,
    /// One place per declaration, in admission order.
    places: Vec<Place>,
    /// The declaration records, strictly ascending and unique by key.
    records: Vec<ArtifactRecord>,
}

impl ArtifactRecordSet
{
    /// Whether the records strictly ascend by key, each bound to its bytes,
    /// and the places and the records name each other.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: holds exactly when each record's key sorts strictly before
    ///   the next record's, each record satisfies its own invariant, each place
    ///   names a held record, and each record stands at a place.
    /// - provides: the record set's invariant, which a clause reads through
    ///   this bound.
    /// - panics: none.
    /// - executable: none — this is the invariant's predicate; a postcondition
    ///   could only repeat its pass.
    ///
    /// # Clause cost
    /// - bound: one key comparison and one digest per record, and one search
    ///   per place. No function's clause reads the set's invariant; only its
    ///   witness does.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an empty set holds; a reversed set, a repeated
    ///   record, a miskeyed record, an unheld place and an unplaced record each
    ///   fail.
    /// - witness: `record::tests::record_refinements_bind_keys_and_places`
    fn well_formed(&self) -> Holds
    {
        let mut placed = Vec::new();
        placed.resize(self.records.len(), false);
        let held = self.places.iter().all(|place| {
            self.slot(place.record).is_ok_and(|slot| {
                if let Some(seen) = placed.get_mut(slot) {
                    *seen = true;
                }
                true
            })
        });
        Holds::from(
            self.records
                .is_sorted_by(|lower, higher| lower.key < higher.key)
                && self.records.iter().all(anodized::types::Spec::predicate)
                && held
                && placed.iter().all(|&seen| seen),
        )
    }

    /// The position in key order of the record keyed `key`.
    ///
    /// # Specification
    /// - requires: the records ascend strictly by key.
    /// - ensures: `Ok` with the position of the record keyed `key`, or `Err`
    ///   with the position a record keyed `key` would take.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every reassembly reads each place's record through
    ///   this search.
    /// - witness: `tests::artifact_contract::records_round_trip_to_a_byte_identical_artifact`
    fn slot(
        &self,
        key: RecordKey,
    ) -> Result<usize, usize>
    {
        self.records.binary_search_by_key(&key, |record| record.key)
    }

    /// The set that `header` and `segments` make, one place per segment in
    /// the sequence given, each place unnamed for `name`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one place per segment, in order, naming the record of its
    ///   bytes; the records strictly ascending and unique by key.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — as [`from_artifact`](Self::from_artifact).
    /// - witness: `record::tests::equal_segments_share_one_record`
    fn gathered<'segment>(
        header: SegmentBytes<'_>,
        segments: impl IntoIterator<Item = SegmentBytes<'segment>>,
    ) -> Self
    {
        let segments = segments.into_iter();
        let mut places = Vec::with_capacity(segments.size_hint().0);
        let mut records = Vec::with_capacity(segments.size_hint().0);
        for segment in segments {
            let record = ArtifactRecord::new(segment);
            places.push(Place {
                record: record.key,
                name: Maybe::Absent(unnamed::Absent::Bytes),
            });
            records.push(record);
        }
        records.sort_unstable_by_key(|record| record.key);
        records.dedup_by_key(|record| record.key);

        Self {
            header: Box::from(header.0),
            places,
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
    ///   its own, every place is unnamed for [`unnamed::Absent::Bytes`], and
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
    /// order, each place unnamed for [`unnamed::Absent::Bytes`].
    ///
    /// # Specification
    /// - requires: nothing; neither the header nor the segments are checked
    ///   here, since a reader decodes what it reassembles.
    /// - ensures: one place per segment, in the order given; one record per
    ///   distinct segment, strictly ascending by key.
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
    pub fn from_segments<'segment>(
        header: SegmentBytes<'_>,
        segments: impl IntoIterator<Item = SegmentBytes<'segment>>,
    ) -> Self
    {
        Self::gathered(header, segments)
    }

    /// The set with each place named as `names` names it, in order.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success place `i` carries `names[i]`, and the header, the
    ///   records and each place's record are as they were.
    /// - provides: the writer's way to put the kernel's content key of each
    ///   entry beside its place.
    /// - fails: [`ArtifactError::Misnamed`] naming the first place without a
    ///   name, or the first name past the last place.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ArtifactError::Misnamed`] — `names` and the places differ in number.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a named set stored and read back holds each name at
    ///   its place, and one name too few or too many is refused at the place
    ///   where the two counts part.
    /// - witness: `tests::artifact_contract::a_named_set_reads_back_with_its_names_7340`
    #[spec(
        captures: count = self.places.len(),
        ensures: |ret| match ret {
            Ok(ref set) => set.places.iter().map(Place::name).eq(names.iter().copied()),
            Err(ArtifactError::Misnamed { place }) => usize::from(place) == names.len().min(count),
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
        for (place, &name) in self.places.iter_mut().zip(names) {
            place.name = name;
        }

        Ok(self)
    }

    /// Reads the records a stored artifact tree holds back into a set.
    ///
    /// # Specification
    /// - requires: `stored` is strictly ascending by key, as a record tree's
    ///   records are.
    /// - ensures: on success the first record is the header, under
    ///   [`HEADER_KEY`]; the second is the order, under [`ORDER_KEY`]; and each
    ///   record after them sits under the digest of its own bytes, stands at a
    ///   place of the order, and every place names one of them.
    /// - provides: the read path's key check, made before any byte is
    ///   reassembled or decoded.
    /// - fails: [`ArtifactError::MisplacedRecord`] naming the first record, in
    ///   key order, whose key is not the one its position or its bytes require
    ///   (the empty set fails at position zero);
    ///   [`ArtifactError::MalformedOrder`] naming the first place the order
    ///   does not hold whole; [`ArtifactError::UnheldRecord`] naming the first
    ///   place whose record the tree does not hold; and
    ///   [`ArtifactError::UnplacedRecord`] naming the first record no place
    ///   names.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ArtifactError::MisplacedRecord`] — a record's key is not the one its
    ///   position or its bytes require.
    /// - [`ArtifactError::MalformedOrder`] — the order holds bytes that are not
    ///   a place.
    /// - [`ArtifactError::UnheldRecord`] — a place names a record the tree does
    ///   not hold.
    /// - [`ArtifactError::UnplacedRecord`] — a record stands at no place.
    ///
    /// # Adequacy
    /// - hypothesis: L2 through stored reads observes complete reconstruction
    ///   for one- and 300-declaration artifacts. L3 supplies a missing header,
    ///   a missing order, a record under a foreign key, an order cut short, a
    ///   place naming no record and a record at no place, and observes each
    ///   refusal at its exact position.
    /// - witness: `tests::artifact_contract::a_stored_tree_with_misplaced_keys_is_refused`
    /// - witness: `tests::artifact_contract::tree_nodes_store_and_reopen`
    #[inline]
    pub fn from_stored(stored: &[Record]) -> Result<Self, ArtifactError>
    {
        let mut stored = stored.iter();
        let header = stored
            .next()
            .filter(|header| header.key().as_ref() == HEADER_KEY)
            .ok_or(ArtifactError::MisplacedRecord {
                position: RecordIndex::ZERO,
            })?;
        let order = stored
            .next()
            .filter(|order| order.key().as_ref() == ORDER_KEY)
            .ok_or(ArtifactError::MisplacedRecord {
                position: RecordIndex::from(1_usize),
            })?;
        let mut records = Vec::with_capacity(stored.len());
        for (offset, record) in stored.enumerate() {
            let kept = ArtifactRecord::new(SegmentBytes(record.value().as_ref()));
            if record.key().as_ref() != kept.key.as_ref() {
                return Err(ArtifactError::MisplacedRecord {
                    position: RecordIndex::from(offset.saturating_add(2_usize)),
                });
            }
            records.push(kept);
        }
        let order_value = order.value();
        let order = order_value.as_ref();
        let whole = order.len().checked_div(PLACE_LEN).unwrap_or_default();
        if order.len() % PLACE_LEN != 0 {
            return Err(ArtifactError::MalformedOrder {
                place: RecordIndex::from(whole),
            });
        }
        let mut places = Vec::with_capacity(whole);
        for (index, bytes) in order.chunks_exact(PLACE_LEN).enumerate() {
            places.push(Place::read(bytes, RecordIndex::from(index))?);
        }
        let set = Self {
            header: Box::from(header.value().as_ref()),
            places,
            records,
        };
        let mut placed = Vec::new();
        placed.resize(set.records.len(), false);
        for (index, place) in set.places.iter().enumerate() {
            let Ok(slot) = set.slot(place.record)
            else {
                return Err(ArtifactError::UnheldRecord {
                    place: RecordIndex::from(index),
                });
            };
            if let Some(seen) = placed.get_mut(slot) {
                *seen = true;
            }
        }
        if let Some(unplaced) = placed.iter().position(|&seen| !seen) {
            return Err(ArtifactError::UnplacedRecord {
                position: RecordIndex::from(unplaced.saturating_add(2_usize)),
            });
        }

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

    /// Returns the declaration records, strictly ascending by key.
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
    ///
    /// # Adequacy
    /// - hypothesis: L2 — as [`reassemble`](Self::reassemble).
    /// - witness: `tests::artifact_contract::records_round_trip_to_a_byte_identical_artifact`
    #[inline]
    pub fn segments(&self) -> impl ExactSizeIterator<Item = SegmentBytes<'_>> + '_
    {
        self.places.iter().map(|place| {
            self.slot(place.record)
                .ok()
                .and_then(|slot| self.records.get(slot))
                .map_or(SegmentBytes(&[]), ArtifactRecord::segment)
        })
    }

    /// Returns the order as the one record it is stored as.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`PLACE_LEN`] bytes per place, in admission order.
    /// - provides: the order's value for [`record_refs`](Self::record_refs).
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a set stored and read back is the set.
    /// - witness: `tests::artifact_contract::tree_nodes_store_and_reopen`
    #[spec(ensures: |ret| ret.0.len() == self.places.len().saturating_mul(PLACE_LEN))]
    #[inline]
    #[must_use]
    pub fn order_image(&self) -> OrderImage
    {
        let mut order = Vec::with_capacity(self.places.len().saturating_mul(PLACE_LEN));
        for place in &self.places {
            place.write_to(&mut order);
        }

        OrderImage(order.into_boxed_slice())
    }

    /// Returns the set as record-plane records: the header under
    /// [`HEADER_KEY`], the order under [`ORDER_KEY`], then every declaration
    /// record in key order.
    ///
    /// # Specification
    /// - requires: `order` is [`order_image`](Self::order_image)'s.
    /// - ensures: two records more than [`ArtifactRecordSet::records`] holds,
    ///   strictly ascending by key.
    /// - provides: the input a record tree is built from.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 through building, storing and reopening a one- and a
    ///   300-declaration artifact observes ordered keys and every record value.
    ///   Perturbing the header or a segment changes the stored identity.
    /// - witness: `tests::artifact_contract::tree_nodes_store_and_reopen`
    /// - witness: `tests::artifact_contract::any_perturbation_changes_the_identity`
    #[spec(ensures: |ret| ret.len() == self.records.len().saturating_add(2)
        && ret.first().is_some_and(|header| header.key().as_ref() == HEADER_KEY
            && header.value().as_ref() == self.header.as_ref()))]
    #[inline]
    #[must_use]
    pub fn record_refs<'set>(
        &'set self,
        order: &'set OrderImage,
    ) -> Vec<RecordRef<'set>>
    {
        let mut refs = Vec::with_capacity(self.records.len().saturating_add(2_usize));
        refs.push(RecordRef::new(HEADER_KEY, &*self.header));
        refs.push(RecordRef::new(ORDER_KEY, &*order.0));
        for record in &self.records {
            refs.push(RecordRef::new(record.key.as_ref(), &*record.segment));
        }

        refs
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
    use alloc::vec;
    use alloc::vec::Vec;

    use gandr_storage_records::RecordIndex;
    use quenchant_shape::shape::Maybe;

    use super::ArtifactRecordSet;
    use super::ContentName;
    use super::RecordKey;
    use super::SegmentBytes;
    use super::unnamed;
    use crate::error::ArtifactError;

    /// The segments `bytes` names, borrowed.
    ///
    /// # Specification
    /// trivial.
    fn segments<'bytes>(bytes: &[&'bytes [u8]]) -> Vec<SegmentBytes<'bytes>>
    {
        bytes
            .iter()
            .map(|&segment| SegmentBytes::from(segment))
            .collect()
    }

    /// Two places with equal bytes share one record, reassemble to both, and
    /// one changed byte gives another key.
    #[test]
    fn equal_segments_share_one_record()
    {
        let header = SegmentBytes::from(b"header".as_slice());
        let set =
            ArtifactRecordSet::from_segments(header, segments(&[b"alpha", b"beta", b"alpha"]));
        assert_eq!(3, set.places().len(), "one place per segment");
        assert_eq!(2, set.records().len(), "one record per distinct segment");
        assert_eq!(
            set.places().first().map(super::Place::record),
            set.places().last().map(super::Place::record),
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

    /// Names replace each place's reason, and a count that differs is refused
    /// where the two counts part.
    #[test]
    fn names_go_beside_their_places_in_order()
    {
        let header = SegmentBytes::from(b"h".as_slice());
        let set = ArtifactRecordSet::from_segments(header, segments(&[b"a", b"b"]));
        assert!(
            set.places()
                .iter()
                .all(|place| place.name() == Maybe::Absent(unnamed::Absent::Bytes))
        );
        let names = [
            Maybe::Present(ContentName::from([7; 32])),
            Maybe::Absent(unnamed::Absent::Unkeyed),
        ];
        let named = set.clone().named(&names).expect("one name per place");
        assert!(named.places().iter().map(super::Place::name).eq(names));
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
            set.named(&[names[0], names[1], names[0]]),
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
            segments(&[b"zero", b"one", b"two", b"three"]),
        );
        assert!(anodized::types::Spec::predicate(&set));
        let mut record = set.records().first().expect("first record").clone();
        assert!(anodized::types::Spec::predicate(&record));
        record.key = RecordKey([0; 32]);
        assert!(!anodized::types::Spec::predicate(&record));

        let mut reversed = set.clone();
        reversed.records.reverse();
        assert!(!anodized::types::Spec::predicate(&reversed));
        let mut duplicate = set.clone();
        duplicate
            .records
            .insert(1, duplicate.records.first().expect("first record").clone());
        assert!(!anodized::types::Spec::predicate(&duplicate));
        let mut miskeyed = set.clone();
        miskeyed.records.first_mut().expect("first record").key = RecordKey([0; 32]);
        assert!(!anodized::types::Spec::predicate(&miskeyed));
        let mut unheld = set.clone();
        let _dropped = unheld.records.pop();
        assert!(!anodized::types::Spec::predicate(&unheld));
        let mut unplaced = set;
        let _dropped = unplaced.places.pop();
        assert!(!anodized::types::Spec::predicate(&unplaced));
    }
}
