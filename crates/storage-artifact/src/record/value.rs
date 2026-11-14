//! A kernel artifact on the value plane: an [`ArtifactRecordSet`] as one
//! canonical value, so a value store chunks it and a content pointer names it.
//!
//! # The tokens
//!
//! ```text
//! open 0x01 or 0x04         the artifact: 0x04 when its places carry names
//!   bytes                   the header
//!   word                    the number of places, n
//!   open 0x02               n opens: place k's constructor holds place k − 1's
//!     …
//!     word × 4              under 0x04 only: place 1's content name,
//!                           little-endian
//!     bytes                 the segment at place 1
//!   close
//!   [word × 4,] bytes,      places 2 to n, each closing the constructor its
//!   close …                 open began
//! close
//! ```
//!
//! The stream walks the order: one constructor per place, which holds the
//! segment at that place. The artifact's constructor gives the set's form once.
//! Under `0x04` every place writes its content name as four words before its
//! segment, and under `0x01` no place writes one. So no stream mixes the two
//! forms, and a set with no place keeps its form. The tag `0x03` once opened a
//! record past a hole in the admission indices. No stream writes it now, and a
//! reader refuses it.
//!
//! Two places with equal bytes each write their segment, and a reader folds
//! them into one record again. So any stream reads back as one set, and that
//! set emits the stream: the codec's canonicity holds by construction.
//!
//! Each declaration segment closes a constructor of its own, and a value store
//! cuts chunks only where a constructor closes, so a chunk boundary falls
//! between two declarations, never inside one. No node of the kernel's term
//! graph is a token. A cut frames the constructor that closes, which holds
//! every place before it the store has not already cut away, so a chunk is a
//! run of consecutive declarations pointing at the run before it.
//!
//! A segment names its children by their index in the whole artifact's subterm
//! table, so an edit that adds or drops one entry renumbers the references of
//! every segment after it. What such an edit leaves is the declarations before
//! it, and the nesting keeps exactly that: every chunk wholly before the edited
//! declaration is shared.
//!
//! **Choice.** The declaration segment is the token grain, the record plane's
//! grain; each place's constructor nests its predecessor's; a place carries its
//! name in words. **Alternatives.** The subterm table's nodes as constructors
//! would read the kernel's node tags into the token stream, which the store's
//! grain rules out. The whole image as one bytes token would make every
//! artifact one chunk. The places side by side under the artifact's
//! constructor would leave every place the store does not cut inline in the
//! root chunk, so any edit would rewrite most of the artifact. Nesting each
//! place's constructor in its successor's would make every chunk point toward
//! the end, so an edit would rewrite every chunk before it. The name as one
//! bytes token would need a length check that four words do not. **Reversal.**
//! A kernel format whose segments name children relative to themselves makes
//! a later segment survive an earlier edit, and a shape sharing both sides of
//! an edit worth its depth.
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

use alloc::vec::Vec;

use anodized::spec;
use gandr_storage_values::CanonicalValue;
use gandr_storage_values::CanonicalWord;
use gandr_storage_values::ConstructorTag;
use gandr_storage_values::TokenBytes;
use gandr_storage_values::TokenReader;
use gandr_storage_values::TokenSink;
use gandr_storage_values::ValueError;
use quenchant_shape::shape::Maybe;

use super::ArtifactRecordSet;
use super::CONTENT_NAME_LEN;
use super::ContentName;
use super::SegmentBytes;

/// The tag a set without names opens with on the value plane.
const ARTIFACT: u8 = 0x01_u8;

/// The tag each place opens with.
const PLACE: u8 = 0x02_u8;

/// The tag a named set opens with on the value plane: each place's first four
/// payloads are its name's words.
const NAMED_ARTIFACT: u8 = 0x04_u8;

/// The byte width of one word of a content name.
const NAME_WORD_LEN: usize = 0x08_usize;

impl CanonicalValue for ArtifactRecordSet
{
    /// The set as the module's tokens: the form's tag, the header, the place
    /// count, one open per place, then each place's name words when the set
    /// is named and its segment, each closing its constructor.
    ///
    /// # Specification
    /// - requires: nothing; each place names a held record, as every set's
    ///   does.
    /// - ensures: one balanced value whose segments are the places' bytes in
    ///   the order's sequence, each place's constructor holding its
    ///   predecessor's; a named set opens [`NAMED_ARTIFACT`], and each of its
    ///   places writes its name as four words.
    /// - provides: the producer half of the artifact's value-plane codec.
    /// - fails: the sink's refusals, propagated.
    /// - panics: none.
    /// - executable: none — the sink's record is the committing store's.
    ///
    /// # Errors
    /// [`ValueError`], the sink's.
    ///
    /// # Adequacy
    /// - hypothesis: L2 artifacts of four and of forty declarations, and a
    ///   named set, read back equal under several cuts, which a lost segment, a
    ///   reordered one or a lost name would not; the set read back commits to
    ///   the pointer it was read from. L3 at every place its own chunk, an edit
    ///   to the thirty-first of forty shares exactly the thirty chunks before
    ///   it, which places side by side or nested the other way would not.
    /// - witness: `tests::artifact_contract::an_artifact_commits_and_reads_back_to_the_image_the_kernel_decodes`
    /// - witness: `tests::artifact_contract::a_named_set_reads_back_off_the_value_plane_7340`
    /// - witness: `tests::artifact_contract::an_edit_shares_every_chunk_before_it_on_the_value_plane`
    #[inline]
    fn emit_tokens<Sink>(
        &self,
        sink: &mut Sink,
    ) -> Result<(), ValueError>
    where
        Sink: TokenSink + ?Sized,
    {
        sink.open(ConstructorTag::from(match self.names {
            Maybe::Present(_) => NAMED_ARTIFACT,
            Maybe::Absent(_) => ARTIFACT,
        }))?;
        sink.bytes(TokenBytes::from(&*self.header))?;
        // A count widens to the word whole on every host whose addresses are
        // sixty-four bits or fewer; past that, the word's ceiling.
        sink.word(CanonicalWord::from(
            u64::try_from(self.places.len()).unwrap_or(u64::MAX),
        ))?;
        for _place in &self.places {
            sink.open(ConstructorTag::from(PLACE))?;
        }
        let names = match self.names {
            Maybe::Present(ref names) => names.as_ref(),
            Maybe::Absent(_) => &[],
        };
        let mut names = names.iter();
        for segment in self.segments() {
            if let Some(name) = names.next() {
                for word in name.0.as_chunks::<NAME_WORD_LEN>().0 {
                    sink.word(CanonicalWord::from(u64::from_le_bytes(*word)))?;
                }
            }
            sink.bytes(TokenBytes::from(segment.as_ref()))?;
            sink.close()?;
        }
        sink.close()
    }

    /// The set [`ArtifactRecordSet::emit_tokens`] wrote.
    ///
    /// # Specification
    /// - requires: `reader` stands at an artifact's constructor.
    /// - ensures: on success the header, the form and the places the stream
    ///   spells, each place naming the record of its segment, and one record
    ///   per distinct segment, in the order of its first place.
    /// - provides: the consumer half of the artifact's value-plane codec; a
    ///   reader reassembles what it returns and decodes the image.
    /// - fails: [`ValueError::UnexpectedConstructor`] for a constructor other
    ///   than an artifact's or a place's where one stands, and the reader's
    ///   refusals.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError`], as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 a stream opening with a place's tag, and one whose
    ///   place opens the retired hole tag, are each refused by name, which a
    ///   decoder trusting its stream would not.
    /// - witness: `tests::artifact_contract::a_stream_that_is_no_artifact_is_refused_off_the_value_plane`
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|set| set.places.iter()
        .try_fold(0_usize, |next, place| match usize::from(place.slot) {
            slot if slot == next => Some(next.saturating_add(1)),
            slot if slot < next => Some(next),
            _ => None,
        }) == Some(set.records.len())))]
    fn decode_tokens(reader: &mut TokenReader<'_>) -> Result<Self, ValueError>
    {
        let position = reader.position();
        let found = reader.read_tag()?;
        let named = if found == ConstructorTag::from(NAMED_ARTIFACT) {
            true
        }
        else if found == ConstructorTag::from(ARTIFACT) {
            false
        }
        else {
            return Err(ValueError::UnexpectedConstructor { found, position });
        };
        let header = <&[u8]>::from(reader.read_bytes()?);
        let count = u64::from(reader.read_word()?);
        // The count is the stream's claim, so it bounds the loop and never
        // reserves memory: a short stream is refused when it runs out.
        let mut opened = 0_usize;
        for _place in 0_u64 .. count {
            let position = reader.position();
            let found = reader.read_tag()?;
            if found != ConstructorTag::from(PLACE) {
                return Err(ValueError::UnexpectedConstructor { found, position });
            }
            opened = opened.saturating_add(1);
        }
        let mut names = Vec::with_capacity(if named { opened } else { 0_usize });
        let mut segments = Vec::with_capacity(opened);
        for _place in 0 .. opened {
            if named {
                let mut name = [0_u8; CONTENT_NAME_LEN];
                for word in name.as_chunks_mut::<NAME_WORD_LEN>().0 {
                    *word = u64::from(reader.read_word()?).to_le_bytes();
                }
                names.push(ContentName(name));
            }
            segments.push(SegmentBytes(<&[u8]>::from(reader.read_bytes()?)));
            reader.read_close()?;
        }
        reader.read_close()?;
        let mut set = Self::gathered(SegmentBytes(header), segments);
        if named {
            set.names = Maybe::Present(names.into_boxed_slice());
        }

        Ok(set)
    }
}
