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
    /// - hypothesis: L2 agreement — the reassembled set is byte-identical to
    ///   the encoder's image for a fixed environment sharing subterms across
    ///   declarations and for generated environments, with one record per
    ///   declaration plus the header.
    /// - witness: `artifact_contract::artifact_contract::records_round_trip_to_a_byte_identical_artifact`
    /// - witness: `artifact_contract::artifact_contract::round_trip_over_generated_environments`
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
    /// - hypothesis: L2 agreement for the sort — two permutations of one
    ///   collection build equal sets in ascending key order — and L3 for the
    ///   refusal, one repeated index with both positions asserted.
    /// - witness: `record::tests::from_records_sorts_any_permutation_canonically`
    /// - witness: `record::tests::a_duplicate_admission_key_is_rejected`
    /// - witness: `artifact_contract::artifact_contract::a_permuted_build_order_yields_the_same_identity`
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
    /// - hypothesis: L3 only — a stored tree missing its header record, and one
    ///   whose declaration keys skip an index, each refused naming the
    ///   position.
    /// - witness: `artifact_contract::artifact_contract::a_stored_tree_with_misplaced_keys_is_refused`
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
    /// - hypothesis: L3 only — a stored set whose bytes decode but whose first
    ///   record carries one byte of the first declaration is refused at that
    ///   record, and the committed set of the same artifact is admitted.
    /// - witness: `artifact_contract::artifact_contract::records_cut_off_a_segment_boundary_are_refused`
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
            record(2, b"two"),
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
        // Index 256 past 2 is where a little-endian key would sort wrongly.
        let indices: Vec<usize> = from_forward
            .records()
            .iter()
            .map(|record| usize::from(record.admission_index()))
            .collect();
        assert_eq!(
            vec![0, 1, 2, 256],
            indices,
            "the records ascend by admission index"
        );
    }

    #[test]
    fn a_duplicate_admission_key_is_rejected()
    {
        let record = |index: usize, segment: &'static [u8]| {
            ArtifactRecord::new(ConstantIndex::from(index), SegmentBytes::from(segment))
        };
        let records = vec![record(5, b"a"), record(3, b"b"), record(3, b"c")];
        assert_eq!(
            Err(ArtifactError::DuplicateAdmissionKey {
                key: ConstantIndex::from(3_usize),
                first: RecordIndex::from(1_usize),
                second: RecordIndex::from(2_usize),
            }),
            ArtifactRecordSet::from_records(SegmentBytes::from(b"header".as_slice()), records),
            "the repeated index and both positions are named"
        );
    }
}
