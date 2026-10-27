//! A kernel artifact on the value plane: an [`ArtifactRecordSet`] as one
//! canonical value, so a value store chunks it and a content pointer names it.
//!
//! # The tokens
//!
//! ```text
//! open 0x01                 the artifact
//!   bytes                   the header
//!   word                    the number of records, n
//!   open 0x02 or 0x03       n opens: record k's constructor holds record k − 1's
//!     …
//!     word                  0x03 only: record 1's hole, less one
//!     bytes                 record 1's declaration segment
//!   close
//!   [word,] bytes, close    records 2 to n, each closing the constructor its
//!   …                       open began
//! close
//! ```
//!
//! The least index a record could carry is zero for the first and one past its
//! predecessor's for each after. A record at that least index opens `0x02` and
//! carries no index at all; a record past it opens `0x03`, and its word is the
//! width of the hole before it less one. Any stream therefore reads back as
//! indices strictly ascending and unique, and as the one stream its set
//! emits: the set's invariant and the codec's canonicity hold by construction,
//! with nothing to refuse but an index past the word's range. A set cut from an
//! artifact numbers its declarations from zero without a hole, so it opens
//! `0x02` throughout and spends no word on an index.
//!
//! Each declaration segment closes a constructor of its own, and a value store
//! cuts chunks only where a constructor closes, so a chunk boundary falls
//! between two declarations, never inside one. No node of the kernel's term
//! graph is a token. A cut frames the constructor that closes, which holds
//! every record before it the store has not already cut away, so a chunk is a
//! run of consecutive declarations pointing at the run before it.
//!
//! A segment names its children by their index in the whole artifact's subterm
//! table, so an edit that adds or drops one entry renumbers the references of
//! every segment after it. What such an edit leaves is the declarations before
//! it, and the nesting keeps exactly that: every chunk wholly before the edited
//! declaration is shared.
//!
//! **Choice.** The declaration segment is the token grain, the record plane's
//! grain; each record's constructor nests its predecessor's; a record names
//! its index only past a hole. **Alternatives.** The subterm table's nodes as
//! constructors would read the kernel's node tags into the token stream, which
//! the store's grain rules out. The whole image as one bytes token would make
//! every artifact one chunk. The records side by side under the artifact's
//! constructor would leave every record the store does not cut inline in the
//! root chunk, so any edit would rewrite most of the artifact. Nesting each
//! record's constructor in its successor's would make every chunk point toward
//! the end, so an edit would rewrite every chunk before it. A gap word on every
//! record would spend nine bytes on each declaration segment, which averages 65
//! bytes across the corpus, to write zero; the index in place of a gap would
//! write a duplicate or a descent for the decoder to refuse. **Reversal.** A
//! kernel format whose segments name children relative to themselves makes a
//! later segment survive an earlier edit, and a shape sharing both sides of an
//! edit worth its depth.
//!
//! A pointer names bytes, never an artifact. Decoding checks the token
//! stream's shape and nothing of the header's or the segments' bytes; a reader
//! reassembles the set it reads back and hands the image to the kernel's
//! decoder, as it does a set read off the record plane.
//!
//! # References
//!
//! - `vault:01a178aa-ce14-7610-bcad-5aab5f9c0b0f` — background: § two walls — a
//!   pointer proves which bytes these are, so the codec checks the stream's
//!   shape alone and the kernel's decoder decides the bytes.

use alloc::boxed::Box;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::ConstantIndex;
use gandr_storage_values::CanonicalValue;
use gandr_storage_values::CanonicalWord;
use gandr_storage_values::ConstructorTag;
use gandr_storage_values::TokenBytes;
use gandr_storage_values::TokenReader;
use gandr_storage_values::TokenSink;
use gandr_storage_values::ValueError;
use gandr_storage_values::ValueQuantity;

use super::ArtifactRecord;
use super::ArtifactRecordSet;
use super::SegmentBytes;

/// The tag an artifact opens with on the value plane.
const ARTIFACT: u8 = 0x01_u8;

/// The tag a record at the least index it could carry opens with.
const NEXT: u8 = 0x02_u8;

/// The tag a record past a hole opens with; its first payload is the hole's
/// width less one.
const AFTER_HOLE: u8 = 0x03_u8;

impl CanonicalValue for ArtifactRecordSet
{
    /// The set as the module's tokens: the header, the record count, one open
    /// per record, then each record's segment in key order, after its hole's
    /// width less one where it has a hole, each closing its constructor.
    ///
    /// # Specification
    /// - requires: nothing; the keys ascend strictly, as every set's do.
    /// - ensures: one balanced value whose segments are the records' bytes in
    ///   key order, each record's constructor holding its predecessor's; a
    ///   record at the least index it could carry opens [`NEXT`] with no word,
    ///   and one past it opens [`AFTER_HOLE`] with the hole's width less one.
    /// - provides: the producer half of the artifact's value-plane codec.
    /// - fails: the sink's refusals, propagated.
    /// - panics: none.
    /// - executable: none — the sink's record is the committing store's.
    ///
    /// # Errors
    /// [`ValueError`], the sink's.
    ///
    /// # Adequacy
    /// - hypothesis: L2 artifacts of four and of forty declarations, and a set
    ///   with holes in its indices, read back equal under several cuts, which a
    ///   lost segment, a reordered one or a miswritten hole would not; the set
    ///   read back commits to the pointer it was read from. L3 at every record
    ///   its own chunk, an edit to the thirty-first of forty shares exactly the
    ///   thirty chunks before it, which records side by side or nested the
    ///   other way would not.
    /// - witness: `tests::artifact_contract::an_artifact_commits_and_reads_back_to_the_image_the_kernel_decodes`
    /// - witness: `tests::artifact_contract::a_set_with_holes_reads_back_off_the_value_plane`
    /// - witness: `tests::artifact_contract::an_edit_shares_every_chunk_before_it_on_the_value_plane`
    #[inline]
    fn emit_tokens<Sink>(
        &self,
        sink: &mut Sink,
    ) -> Result<(), ValueError>
    where
        Sink: TokenSink + ?Sized,
    {
        sink.open(ConstructorTag::from(ARTIFACT))?;
        sink.bytes(TokenBytes::from(&*self.header))?;
        // A count or a hole widens to the word whole on every host whose
        // addresses are sixty-four bits or fewer; past that, the word's ceiling.
        sink.word(CanonicalWord::from(
            u64::try_from(self.records.len()).unwrap_or(u64::MAX),
        ))?;
        let mut least = 0_usize;
        for record in &self.records {
            let index = usize::from(record.index);
            let tag = if index == least { NEXT } else { AFTER_HOLE };
            sink.open(ConstructorTag::from(tag))?;
            least = index.saturating_add(1_usize);
        }
        let mut least = 0_usize;
        for record in &self.records {
            let index = usize::from(record.index);
            if index != least {
                let hole = index.saturating_sub(least).saturating_sub(1_usize);
                sink.word(CanonicalWord::from(u64::try_from(hole).unwrap_or(u64::MAX)))?;
            }
            sink.bytes(TokenBytes::from(&*record.segment))?;
            sink.close()?;
            least = index.saturating_add(1_usize);
        }
        sink.close()
    }

    /// The set [`ArtifactRecordSet::emit_tokens`] wrote.
    ///
    /// # Specification
    /// - requires: `reader` stands at an artifact's constructor.
    /// - ensures: on success the header and the records the stream spells, each
    ///   record keyed by the least index it could carry, or past it by its
    ///   hole, the keys strictly ascending.
    /// - provides: the consumer half of the artifact's value-plane codec; a
    ///   reader reassembles what it returns and decodes the image.
    /// - fails: [`ValueError::UnexpectedConstructor`] for a constructor other
    ///   than the artifact's or a record's where one stands;
    ///   [`ValueError::ArithmeticOverflow`] naming
    ///   [`ValueQuantity::PayloadIndex`] for a hole that carries an index past
    ///   the host's addresses; and the reader's refusals.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError`], as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 a stream opening with a record's tag, and one whose
    ///   second hole runs past the word's range, are each refused by name,
    ///   which a decoder trusting its stream would not.
    /// - witness: `tests::artifact_contract::a_stream_that_is_no_artifact_is_refused_off_the_value_plane`
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|set| set.records.iter()
        .zip(set.records.iter().skip(1))
        .all(|(previous, next)| previous.key < next.key)))]
    fn decode_tokens(reader: &mut TokenReader<'_>) -> Result<Self, ValueError>
    {
        let overflow = ValueError::ArithmeticOverflow {
            quantity: ValueQuantity::PayloadIndex,
        };
        let position = reader.position();
        let found = reader.read_tag()?;
        if found != ConstructorTag::from(ARTIFACT) {
            return Err(ValueError::UnexpectedConstructor { found, position });
        }
        let header = Box::from(<&[u8]>::from(reader.read_bytes()?));
        let count = u64::from(reader.read_word()?);
        // The count is the stream's claim, so it bounds the loop and never
        // reserves memory: a short stream is refused when it runs out.
        let mut holes = Vec::new();
        for _record in 0_u64 .. count {
            let position = reader.position();
            let found = reader.read_tag()?;
            holes.push(if found == ConstructorTag::from(NEXT) {
                false
            }
            else if found == ConstructorTag::from(AFTER_HOLE) {
                true
            }
            else {
                return Err(ValueError::UnexpectedConstructor { found, position });
            });
        }
        let mut records = Vec::with_capacity(holes.len());
        let mut least = Some(0_usize);
        for after_hole in holes {
            let at_least = least.ok_or(overflow)?;
            let index = if after_hole {
                let hole = usize::try_from(u64::from(reader.read_word()?))
                    .map_err(|_overflow| overflow)?;
                at_least
                    .checked_add(hole)
                    .and_then(|index| index.checked_add(1_usize))
                    .ok_or(overflow)?
            }
            else {
                at_least
            };
            let segment = <&[u8]>::from(reader.read_bytes()?);
            reader.read_close()?;
            records.push(ArtifactRecord::new(
                ConstantIndex::from(index),
                SegmentBytes(segment),
            ));
            least = index.checked_add(1_usize);
        }
        reader.read_close()?;
        Ok(Self { header, records })
    }
}
