//! The declaration-record model: a kernel artifact as a sorted, unique, keyed
//! record set.
//!
//! # The records
//!
//! ```text
//! key                        value
//! ""                         header: magic, version, minted-atom table, count
//! u64be admission index 0    declaration segment 0
//! u64be admission index 1    declaration segment 1
//! …
//! ```
//!
//! The header sits under the empty key, which sorts before every admission
//! key, so the artifact image is the concatenation of the record values in
//! key order and the record plane's root binds every byte of it. An admission
//! key is big-endian at a fixed width, so byte order is numeric order.
//!
//! A declaration segment may reference subterm-table entries an earlier
//! segment introduced, so a record is a content-addressing grain, never an
//! independently decodable unit: a reader reassembles the whole image and
//! decodes it once.
//!
//! # Where the cuts come from
//!
//! [`ArtifactRecordSet::from_artifact`] cuts an image where the kernel's
//! decoder reports its segments end, so a record boundary that is not a
//! segment boundary never reaches storage from this path.
//! [`ArtifactRecordSet::ensure_cut_at`] holds a stored set to the same
//! boundaries on the way back.

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use gandr_kernel_term::ArtifactImage;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::SegmentLayout;
use gandr_kernel_term::decode;
use gandr_storage_records::Record;
use gandr_storage_records::RecordIndex;
use gandr_storage_records::RecordRef;

use crate::error::ArtifactError;

/// The byte width of a declaration record's key.
pub const ADMISSION_KEY_LEN: usize = 0x08_usize;

/// The key the header record is stored under: the empty key, which sorts
/// before every admission key.
pub const HEADER_KEY: &[u8] = b"";

/// A declaration record's key: its admission index, big-endian at a fixed
/// width, so byte order is numeric order.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct AdmissionKey([u8; ADMISSION_KEY_LEN]);

impl From<ConstantIndex> for AdmissionKey
{
    /// Writes an admission index as its key.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the eight big-endian bytes of the index, so two indices
    ///   compare as their keys compare bytewise.
    /// - provides: the one spelling of a declaration record's key.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 on zero, all byte carries representable by the target,
    ///   and the usize ceiling observes eight-byte big-endian encodings and
    ///   numeric/lexicographic agreement. It distinguishes reversed bytes,
    ///   shortened keys and narrowed indices, without exhausting index pairs.
    /// - witness: `record::tests::admission_keys_preserve_numeric_order_across_byte_carries`
    #[anodized::spec(ensures: |ret| ret.0.iter().fold(0_u64, |value, &byte|
        value.wrapping_shl(8) | u64::from(byte))
        == u64::try_from(usize::from(index)).unwrap_or(u64::MAX))]
    #[inline]
    fn from(index: ConstantIndex) -> Self
    {
        // An admission index counts declarations held in memory, so it fits
        // sixty-four bits on every target Rust supports.
        let wide = u64::try_from(usize::from(index)).unwrap_or(u64::MAX);
        // The most significant byte first, so bytewise order is numeric order:
        // the one place in the tier a key is not little-endian, because a key
        // is compared as bytes and never read back as a number.
        let mut bytes = wide.to_le_bytes();
        bytes.reverse();

        Self(bytes)
    }
}

impl AsRef<[u8]> for AdmissionKey
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

/// The bytes a record set reassembles to: the header, then every declaration
/// segment in key order.
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

/// One declaration record: its admission index, its key, and its segment's
/// bytes.
///
/// # Specification
/// - requires: nothing; segment syntax belongs to kernel decoding.
/// - ensures: the admitted key is the stored admission index in eight-byte
///   big-endian form, independent of the segment contents.
/// - provides: the binding between a declaration's numeric and ordered keys.
/// - fails: the refinement rejects a key/index disagreement.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 zero, 255, 256 and the native-word maximum distinguish
///   miskeyed records; raw segments remain admissible. Carry goldens
///   distinguish byte order from the constructor's own implementation.
/// - witness: `record::tests::record_refinements_bind_keys_and_sorted_unique_sets`
/// - witness: `record::tests::admission_keys_preserve_numeric_order_across_byte_carries`
#[anodized::spec(maintains: self.key.0.iter().rev().copied().eq(
    u64::try_from(usize::from(self.index)).unwrap_or(u64::MAX).to_le_bytes()))]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ArtifactRecord
{
    /// The admission index the record is keyed by.
    index: ConstantIndex,
    /// The index's key.
    key: AdmissionKey,
    /// The declaration segment's bytes.
    segment: Box<[u8]>,
}

impl ArtifactRecord
{
    /// Keys a declaration segment by its admission index.
    ///
    /// # Specification
    /// - requires: nothing; whether the bytes are a segment is the decoder's
    ///   question when the set is read back.
    /// - ensures: the record carries `index`, its [`AdmissionKey`], and a copy
    ///   of `segment`.
    /// - provides: the one constructor a declaration record has.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 through reassembly and stored reads observes the index,
    ///   key and complete segment in a shared four-declaration artifact and 64
    ///   generated environments with at most 47 declarations of four kinds. It
    ///   distinguishes lost segment bytes and miskeyed declarations; it does
    ///   not exhaust arbitrary malformed segment contents.
    /// - witness: `artifact_contract::artifact_contract::records_round_trip_to_a_byte_identical_artifact`
    /// - witness: `artifact_contract::artifact_contract::round_trip_over_generated_environments`
    #[anodized::spec(ensures: |ret| ret.index == index
        && ret.key == AdmissionKey::from(index)
        && ret.segment.as_ref() == segment.0)]
    #[inline]
    #[must_use]
    pub fn new(
        index: ConstantIndex,
        segment: SegmentBytes<'_>,
    ) -> Self
    {
        Self {
            index,
            key: AdmissionKey::from(index),
            segment: Box::from(segment.0),
        }
    }

    /// Returns the admission index the record is keyed by.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn admission_index(&self) -> ConstantIndex
    {
        self.index
    }

    /// Returns the record's key.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn key(&self) -> AdmissionKey
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

/// The record set a kernel artifact is: its header, and one record per
/// declaration, strictly ascending and unique by admission key.
///
/// # Specification
/// - requires: nothing; header and segment bytes need not decode as a kernel
///   artifact, and admission indices need not be contiguous.
/// - ensures: each record binds its index to its key, and keys are strictly
///   increasing, so duplicate keys are absent.
/// - provides: canonical record ordering without certifying the payload.
/// - fails: the refinement rejects miskeyed, reversed or duplicate records.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 empty and noncontiguous sets admit raw bytes; reversing a
///   byte-carry pair, repeating a key and changing a stored key each violate a
///   separate part of the refinement. Public construction also refuses named
///   duplicate positions before sorting.
/// - witness: `record::tests::record_refinements_bind_keys_and_sorted_unique_sets`
/// - witness: `record::tests::a_duplicate_admission_key_is_rejected`
#[anodized::spec(maintains: {
    let mut previous = None;
    self.records.iter().all(|record| {
        let ordered = previous.is_none_or(|key| key < record.key);
        previous = Some(record.key);
        ordered && anodized::types::Spec::predicate(record)
    })
})]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ArtifactRecordSet
{
    /// The header preceding the first declaration segment.
    header: Box<[u8]>,
    /// The declaration records, strictly ascending and unique by key.
    records: Vec<ArtifactRecord>,
}

impl ArtifactRecordSet
{
    /// Cuts an artifact into its record set where the kernel's decoder finds
    /// its segments end.
    ///
    /// # Specification
    /// - requires: nothing; the bytes are arbitrary.
    /// - ensures: on success the header is the image up to the decoder's header
    ///   end, record `i` is keyed by admission index `i` and holds the bytes
    ///   from the end before it to its own, and
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
    /// - witness: `artifact_contract::artifact_contract::records_round_trip_to_a_byte_identical_artifact`
    /// - witness: `artifact_contract::artifact_contract::round_trip_over_generated_environments`
    #[anodized::spec(ensures: |ret| match ret {
        Ok(ref set) => {
            let mut offset = set.header.len();
            image.as_ref().starts_with(set.header.as_ref())
                && set.records.iter().enumerate().all(|(index, record)| {
                    let end = offset.saturating_add(record.segment.len());
                    let agrees = record.index == ConstantIndex::from(index)
                        && record.key == AdmissionKey::from(record.index)
                        && image.as_ref().get(offset .. end) == Some(record.segment.as_ref());
                    offset = end;
                    agrees
                })
                && offset == image.as_ref().len()
        },
        Err(ArtifactError::Kernel { .. } | ArtifactError::SegmentBoundary { .. }) => true,
        Err(_) => false,
    })]
    #[inline]
    pub fn from_artifact(image: ArtifactImage<'_>) -> Result<Self, ArtifactError>
    {
        let decoded = decode(image)?;
        let layout = decoded.segments();
        let bytes = image.as_ref();
        let mut start = usize::from(layout.header_end());
        let header = bytes.get(.. start).ok_or(ArtifactError::SegmentBoundary {
            position: RecordIndex::ZERO,
        })?;
        let mut records = Vec::with_capacity(layout.declaration_ends().len());
        for (offset, &end) in layout.declaration_ends().iter().enumerate() {
            let end = usize::from(end);
            let segment =
                bytes
                    .get(start .. end)
                    .ok_or_else(|| ArtifactError::SegmentBoundary {
                        position: RecordIndex::from(offset.saturating_add(1_usize)),
                    })?;
            records.push(ArtifactRecord::new(
                ConstantIndex::from(offset),
                SegmentBytes(segment),
            ));
            start = end;
        }

        Ok(Self {
            header: Box::from(header),
            records,
        })
    }

    /// Builds a set from a header and declaration records in any order.
    ///
    /// # Specification
    /// - requires: nothing; neither the header nor the segments are checked
    ///   here, since a reader decodes what it reassembles.
    /// - ensures: on success the records are sorted strictly ascending by key,
    ///   so any two orders of one record collection build equal sets.
    /// - provides: the general constructor, and the entry the
    ///   history-independence differential builds through.
    /// - fails: [`ArtifactError::DuplicateAdmissionKey`] naming the first
    ///   repeated index and the input positions of its first two records.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ArtifactError::DuplicateAdmissionKey`] — two records carry one
    /// admission index.
    ///
    /// # Adequacy
    /// - hypothesis: L2 on forward and reverse orders across the 255/256 carry
    ///   observes canonical ordering and unchanged payloads, with a downstream
    ///   identity comparison for a four-declaration artifact. L3 distinguishes
    ///   first-repetition order from key order and later duplicate positions in
    ///   three duplicate layouts. It does not exhaust permutations; the
    ///   predicate retains only the moved collection's count.
    /// - witness: `record::tests::from_records_sorts_any_permutation_canonically`
    /// - witness: `record::tests::a_duplicate_admission_key_is_rejected`
    /// - witness: `artifact_contract::artifact_contract::a_permuted_build_order_yields_the_same_identity`
    #[anodized::spec(
        captures: count = records.len(),
        ensures: |ret| match ret {
            Ok(ref set) => set.header.as_ref() == header.0
                && set.records.len() == count
                && set.records.iter().zip(set.records.iter().skip(1))
                    .all(|(previous, next)| previous.key < next.key),
            Err(ArtifactError::DuplicateAdmissionKey { first, second, .. }) =>
                first < second && usize::from(second) < count,
            Err(_) => false,
        },
    )]
    #[inline]
    pub fn from_records(
        header: SegmentBytes<'_>,
        records: Vec<ArtifactRecord>,
    ) -> Result<Self, ArtifactError>
    {
        let mut first_seen: BTreeMap<ConstantIndex, RecordIndex> = BTreeMap::new();
        for (position, record) in records.iter().enumerate() {
            let position = RecordIndex::from(position);
            if let Some(&first) = first_seen.get(&record.index) {
                return Err(ArtifactError::DuplicateAdmissionKey {
                    key: record.index,
                    first,
                    second: position,
                });
            }
            let _absent = first_seen.insert(record.index, position);
        }
        let mut sorted = records;
        sorted.sort_by_key(|record| record.key);

        Ok(Self {
            header: Box::from(header.0),
            records: sorted,
        })
    }

    /// Reads the records a stored artifact tree holds back into a set.
    ///
    /// # Specification
    /// - requires: `stored` is strictly ascending by key, as a record tree's
    ///   records are.
    /// - ensures: on success the first record is the header, under
    ///   [`HEADER_KEY`], and the records after it are keyed by the admission
    ///   indices from zero up, one each, in order.
    /// - provides: the read path's key check, made before any byte is
    ///   reassembled or decoded.
    /// - fails: [`ArtifactError::MisplacedRecord`] naming the first record, in
    ///   key order, whose key is not the one its position requires — the empty
    ///   set fails at position zero.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ArtifactError::MisplacedRecord`] — a record's key is not the one its
    /// position requires.
    ///
    /// # Adequacy
    /// - hypothesis: L2 through stored reads observes complete reconstruction
    ///   for one- and 300-declaration artifacts. L3 supplies a missing header
    ///   and a skipped initial index, observing the exact refused position. It
    ///   distinguishes shifted keys and omitted values without exhausting
    ///   malformed key lengths or all later failure positions.
    /// - witness: `artifact_contract::artifact_contract::a_stored_tree_with_misplaced_keys_is_refused`
    /// - witness: `artifact_contract::artifact_contract::tree_nodes_store_and_reopen`
    #[anodized::spec(
        requires: stored.iter().zip(stored.iter().skip(1))
            .all(|(previous, next)| previous.key() < next.key()),
        ensures: |ret| match ret {
            Ok(ref set) => stored.first().is_some_and(|header|
                header.key().as_ref() == HEADER_KEY
                    && set.header.as_ref() == header.value().as_ref())
                && set.records.len().checked_add(1) == Some(stored.len())
                && set.records.iter().zip(stored.iter().skip(1)).enumerate()
                    .all(|(index, (record, original))| {
                        record.index == ConstantIndex::from(index)
                            && record.key == AdmissionKey::from(record.index)
                            && original.key().as_ref() == record.key.as_ref()
                            && original.value().as_ref() == record.segment.as_ref()
                    }),
            Err(ArtifactError::MisplacedRecord { position }) => {
                let first = if stored.is_empty() {
                    Some(0)
                } else {
                    stored.iter().enumerate().position(|(index, record)| {
                        if index == 0 {
                            record.key().as_ref() != HEADER_KEY
                        } else {
                            record.key().as_ref() != AdmissionKey::from(ConstantIndex::from(index.saturating_sub(1))).as_ref()
                        }
                    })
                };
                first == Some(usize::from(position))
            },
            Err(_) => false,
        },
    )]
    #[inline]
    pub fn from_stored(stored: &[Record]) -> Result<Self, ArtifactError>
    {
        let Some((header, declarations)) = stored.split_first()
        else {
            return Err(ArtifactError::MisplacedRecord {
                position: RecordIndex::ZERO,
            });
        };
        if header.key().as_ref() != HEADER_KEY {
            return Err(ArtifactError::MisplacedRecord {
                position: RecordIndex::ZERO,
            });
        }
        let mut records = Vec::with_capacity(declarations.len());
        for (offset, record) in declarations.iter().enumerate() {
            let index = ConstantIndex::from(offset);
            if record.key().as_ref() != AdmissionKey::from(index).as_ref() {
                return Err(ArtifactError::MisplacedRecord {
                    position: RecordIndex::from(offset.saturating_add(1_usize)),
                });
            }
            records.push(ArtifactRecord::new(
                index,
                SegmentBytes(record.value().as_ref()),
            ));
        }

        Ok(Self {
            header: Box::from(header.value().as_ref()),
            records,
        })
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

    /// Returns the set as record-plane records: the header under
    /// [`HEADER_KEY`], then every declaration record in key order.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one record more than [`ArtifactRecordSet::records`] holds,
    ///   strictly ascending by key.
    /// - provides: the input a record tree is built from.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 through building, storing and reopening a one- and a
    ///   300-declaration artifact observes ordered keys and every record value.
    ///   Perturbing the header or a segment changes the stored identity. These
    ///   witnesses distinguish omitted, reordered and misassociated records;
    ///   they do not exhaust record-tree shapes or allocation behaviour.
    /// - witness: `artifact_contract::artifact_contract::tree_nodes_store_and_reopen`
    /// - witness: `artifact_contract::artifact_contract::any_perturbation_changes_the_identity`
    #[anodized::spec(ensures: |ret| ret.len() == self.records.len().saturating_add(1)
        && ret.first().is_some_and(|header| header.key().as_ref() == HEADER_KEY
            && header.value().as_ref() == self.header.as_ref())
        && ret.iter().skip(1).zip(&self.records).all(|(view, record)|
            (view.key().as_ref(), view.value().as_ref())
                == (record.key.as_ref(), record.segment.as_ref())))]
    #[inline]
    #[must_use]
    pub fn record_refs(&self) -> Vec<RecordRef<'_>>
    {
        let mut refs = Vec::with_capacity(self.records.len().saturating_add(1_usize));
        refs.push(RecordRef::new(HEADER_KEY, &*self.header));
        for record in &self.records {
            refs.push(RecordRef::new(record.key.as_ref(), &*record.segment));
        }

        refs
    }

    /// Reassembles the artifact: the header, then every declaration segment
    /// in key order.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the concatenation of the header and the segments; for a set
    ///   [`ArtifactRecordSet::from_artifact`] built, exactly that image.
    /// - provides: the bytes a reader hands the kernel's decoder.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 on the shared four-declaration artifact and 64
    ///   generated environments of zero to 47 declarations observes every
    ///   reassembled byte against the kernel encoder, distinguishing misplaced
    ///   headers, segment loss and reordered bytes. These witnesses do not
    ///   validate arbitrary bytes admitted by the unchecked record constructor.
    /// - witness: `artifact_contract::artifact_contract::records_round_trip_to_a_byte_identical_artifact`
    /// - witness: `artifact_contract::artifact_contract::round_trip_over_generated_environments`
    #[anodized::spec(ensures: |ret| {
        let mut offset = self.header.len();
        ret.0.starts_with(self.header.as_ref())
            && self.records.iter().all(|record| {
                let end = offset.saturating_add(record.segment.len());
                let agrees = ret.0.get(offset .. end) == Some(record.segment.as_ref());
                offset = end;
                agrees
            })
            && offset == ret.0.len()
    })]
    #[inline]
    #[must_use]
    pub fn reassemble(&self) -> ReassembledArtifact
    {
        let length = self
            .records
            .iter()
            .fold(self.header.len(), |total, record| {
                total.saturating_add(record.segment.len())
            });
        let mut bytes = Vec::with_capacity(length);
        bytes.extend_from_slice(&self.header);
        for record in &self.records {
            bytes.extend_from_slice(&record.segment);
        }

        ReassembledArtifact(bytes)
    }

    /// Refuses a set whose records are not cut at the decoded artifact's
    /// segment boundaries.
    ///
    /// # Specification
    /// - requires: `layout` is the segment layout of a decode of
    ///   [`ArtifactRecordSet::reassemble`]'s image.
    /// - ensures: success exactly when the header ends at the layout's header
    ///   end, the set holds one record per declaration segment, and each record
    ///   ends at its segment's end.
    /// - provides: the read path's guarantee that the stored cuts are the
    ///   reader's, not a writer's: bytes that decode are still refused when a
    ///   record straddles two segments or splits one.
    /// - fails: [`ArtifactError::SegmentBoundary`] naming the first record, in
    ///   key order, that ends where no segment does, or the position past the
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
    ///   It distinguishes conflating valid bytes with valid cuts; later cuts
    ///   and differing record/layout counts are not sampled by this witness.
    /// - witness: `artifact_contract::artifact_contract::records_cut_off_a_segment_boundary_are_refused`
    #[anodized::spec(ensures: |ret| {
        let ends = layout.declaration_ends();
        let first = if self.header.len() == usize::from(layout.header_end()) {
            let mut end = self.header.len();
            self.records.iter().zip(ends).position(|(record, expected)| {
                end = end.saturating_add(record.segment.len());
                end != usize::from(*expected)
            }).map(|index| index.saturating_add(1)).or_else(||
                (self.records.len() != ends.len())
                    .then_some(self.records.len().min(ends.len()).saturating_add(1)))
        } else {
            Some(0)
        };
        match ret {
            Ok(()) => first.is_none(),
            Err(ArtifactError::SegmentBoundary { position }) => first == Some(usize::from(position)),
            Err(_) => false,
        }
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
        for (offset, record) in self.records.iter().enumerate() {
            let position = RecordIndex::from(offset.saturating_add(1_usize));
            end = end.saturating_add(record.segment.len());
            let Some(&expected) = ends.get(offset)
            else {
                return Err(ArtifactError::SegmentBoundary { position });
            };
            if end != usize::from(expected) {
                return Err(ArtifactError::SegmentBoundary { position });
            }
        }
        if ends.len() != self.records.len() {
            return Err(ArtifactError::SegmentBoundary {
                position: RecordIndex::from(self.records.len().saturating_add(1_usize)),
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

    use gandr_kernel_term::ConstantIndex;
    use gandr_storage_records::RecordIndex;

    use super::AdmissionKey;
    use super::ArtifactRecord;
    use super::ArtifactRecordSet;
    use super::SegmentBytes;
    use crate::error::ArtifactError;

    #[test]
    fn from_records_sorts_any_permutation_canonically()
    {
        let record = |index: usize, segment: &'static [u8]| {
            ArtifactRecord::new(ConstantIndex::from(index), SegmentBytes::from(segment))
        };
        let forward = vec![
            record(0, b"zero"),
            record(1, b"one"),
            record(255, b"two hundred fifty-five"),
            record(256, b"two hundred fifty-six"),
        ];
        let reversed = forward.iter().rev().cloned().collect();
        let header = SegmentBytes::from(b"header".as_slice());
        let from_forward = ArtifactRecordSet::from_records(header, forward).expect("unique");
        let from_reversed = ArtifactRecordSet::from_records(header, reversed).expect("unique");
        assert_eq!(
            from_forward, from_reversed,
            "a permuted input builds the same set"
        );
        // Index 256 past 255 is where a little-endian key would sort wrongly.
        let indices: Vec<usize> = from_forward
            .records()
            .iter()
            .map(|record| usize::from(record.admission_index()))
            .collect();
        assert_eq!(
            vec![0, 1, 255, 256],
            indices,
            "the records ascend by admission index"
        );
    }

    #[test]
    fn a_duplicate_admission_key_is_rejected()
    {
        for (indices, key, first, second) in [
            ([5, 3, 3, 5], 3, 1, 2),
            ([5, 3, 5, 3], 5, 0, 2),
            ([usize::MAX, 0, usize::MAX, 0], usize::MAX, 0, 2),
        ] {
            let records = indices
                .into_iter()
                .map(|index| {
                    ArtifactRecord::new(
                        ConstantIndex::from(index),
                        SegmentBytes::from(b"segment".as_slice()),
                    )
                })
                .collect();
            assert_eq!(
                Err(ArtifactError::DuplicateAdmissionKey {
                    key: ConstantIndex::from(key),
                    first: RecordIndex::from(first),
                    second: RecordIndex::from(second),
                }),
                ArtifactRecordSet::from_records(SegmentBytes::from(b"header".as_slice()), records),
            );
        }
    }

    /// The wire key preserves numeric order at every native-word byte carry.
    #[test]
    fn admission_keys_preserve_numeric_order_across_byte_carries()
    {
        assert_eq!([0; 8], AdmissionKey::from(ConstantIndex::from(0_usize)).0);
        for byte in 1 .. size_of::<usize>() {
            let after = 1_usize << (byte * 8);
            let before = after - 1;
            let mut lower = [0; 8];
            lower[8 - byte ..].fill(u8::MAX);
            let mut upper = [0; 8];
            upper[7 - byte] = 1;
            let lower_key = AdmissionKey::from(ConstantIndex::from(before));
            let upper_key = AdmissionKey::from(ConstantIndex::from(after));
            assert_eq!(lower, lower_key.0);
            assert_eq!(upper, upper_key.0);
            assert!(lower_key < upper_key);
        }
        let mut maximum = [0; 8];
        maximum[8 - size_of::<usize>() ..].fill(u8::MAX);
        assert_eq!(
            maximum,
            AdmissionKey::from(ConstantIndex::from(usize::MAX)).0
        );
    }

    /// Refinement separates ordered identity from unvalidated payload bytes.
    #[test]
    fn record_refinements_bind_keys_and_sorted_unique_sets()
    {
        for index in [0_usize, 255, 256, usize::MAX] {
            let mut record = ArtifactRecord::new(
                ConstantIndex::from(index),
                SegmentBytes::from(b"not a kernel segment".as_slice()),
            );
            assert!(anodized::types::Spec::predicate(&record));
            record.key = AdmissionKey::from(ConstantIndex::from(index ^ 1));
            assert!(!anodized::types::Spec::predicate(&record));
        }

        let empty =
            ArtifactRecordSet::from_records(SegmentBytes::from(b"unvalidated".as_slice()), vec![])
                .expect("an empty record set admits raw header bytes");
        assert!(anodized::types::Spec::predicate(&empty));
        assert!(gandr_kernel_term::decode(empty.reassemble().as_image()).is_err());

        let records = [usize::MAX, 256, 255, 0]
            .into_iter()
            .map(|index| {
                ArtifactRecord::new(
                    ConstantIndex::from(index),
                    SegmentBytes::from(b"".as_slice()),
                )
            })
            .collect();
        let set = ArtifactRecordSet::from_records(SegmentBytes::from(b"h".as_slice()), records)
            .expect("unique noncontiguous indices");
        assert!(anodized::types::Spec::predicate(&set));
        let mut reversed = set.clone();
        reversed.records.reverse();
        assert!(!anodized::types::Spec::predicate(&reversed));
        let mut duplicate = set.clone();
        duplicate
            .records
            .insert(1, duplicate.records.first().expect("first record").clone());
        assert!(!anodized::types::Spec::predicate(&duplicate));
        let mut miskeyed = set;
        miskeyed.records.first_mut().expect("first record").key =
            AdmissionKey::from(ConstantIndex::from(1_usize));
        assert!(!anodized::types::Spec::predicate(&miskeyed));
    }
}
