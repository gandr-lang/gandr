//! `cam_commit` — the typed chunking traversal, committing bottom-up.
//!
//! The traversal walks a value once, in preorder, appending its records to a
//! pending body. At every constructor exit but the outermost it raises a
//! boundary event and asks the committed typed profile whether to cut. A cut
//! frames the closed subtree as a chunk, stores it, and splices a child record
//! naming that chunk in its place. The root chunk is framed last, and its
//! digest at offset zero is the root pointer.
//!
//! # Bottom-up commitment
//!
//! A child's digest must be fixed before its parent's body can carry it.
//! Cutting at constructor exit makes the order available: by the time a
//! subtree closes, everything beneath it is decided.
//!
//! # Boundary residues
//!
//! An event carries the records appended to the body since the previous
//! event, so each record joins the scanner's pending count once. The residue
//! is the subtree's own content hash, taken Merkle-wise so it does not depend
//! on how the subtree's descendants were cut:
//!
//! ```text
//! preimage(c) := "gandr:storage-values:residue:v1"
//!             || the open record of c
//!             || item*
//!             || the close record
//! item        := a word, bytes or child record c emitted directly
//!              | 0x00 || subtree digest of a constructor nested in c
//! subtree digest(c) := BLAKE3(preimage(c))
//! residue(c)        := the first eight bytes of subtree digest(c), as u64le
//! ```
//!
//! The marker `0x00` is a kind byte no record uses, so a nested digest cannot
//! read as a record. Each emitted byte is hashed once, under the constructor
//! that emitted it, whatever the depth.
//!
//! # Root framing
//!
//! The outermost constructor is framed directly as the root chunk. Applying
//! a cut there would add a pointer-only root and an unnecessary seam.

use alloc::vec::Vec;

use anodized::spec;
use gandr_storage_chunker::BoundaryEvent;
use gandr_storage_chunker::BoundaryResidue;
use gandr_storage_chunker::CutDecision;
use gandr_storage_chunker::TokenCount;
use gandr_storage_chunker::TypedChunker;

use crate::chunk::ChunkStore;
use crate::chunk::frame_chunk;
use crate::error::EmissionFault;
use crate::error::ValueError;
use crate::error::ValueQuantity;
use crate::index_base::ChildIndexBase;
use crate::manifest::ValueManifest;
use crate::manifest::ValueProfile;
use crate::ptr::ContentPtr;
use crate::ptr::TokenOffset;
use crate::tokens::BodyFront;
use crate::tokens::BodyMark;
use crate::tokens::BodyWriter;
use crate::tokens::CanonicalValue;
use crate::tokens::Closing;
use crate::tokens::ConstructorTag;
use crate::tokens::EmissionShape;
use crate::tokens::Record;
use crate::tokens::TokenSink;
use crate::tokens::split_record;
use crate::units::CanonicalWord;
use crate::units::TokenBytes;

/// The domain every residue preimage opens with.
pub const RESIDUE_DOMAIN: &[u8] = b"gandr:storage-values:residue:v1";

/// The residue preimage's marker before a nested constructor's digest.
const NESTED_SUBTREE: u8 = 0x00_u8;

/// A byte position in the stack of open residue preimages.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct PreimageMark(usize);

/// One open constructor: where its subtree starts in the body, and where its
/// residue preimage starts.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct OpenFrame
{
    /// The body position of the constructor's open record.
    body_start: BodyMark,
    /// The preimage position of the constructor's residue domain.
    preimage_start: PreimageMark,
}

/// The committing traversal's sink.
///
/// Not public: a caller driving it directly could splice a child record the
/// traversal did not place, which is a claim about the store nothing checked.
/// A value embedding an already-committed value does so through
/// [`TokenSink::child_pointer`], whose pointer the reader verifies on use.
struct CommitSink<'store, Store>
where
    Store: ChunkStore + ?Sized,
{
    /// Where cut chunks are inserted, bottom-up.
    store: &'store mut Store,
    /// The scanner under the committed typed profile.
    chunker: TypedChunker,
    /// The records not yet framed.
    body: BodyWriter,
    /// The residue preimages of every open constructor, outermost first.
    preimage: Vec<u8>,
    /// One frame per open constructor, outermost first.
    open: Vec<OpenFrame>,
    /// Where the emission stands in the one-balanced-value shape.
    shape: EmissionShape,
    /// Records appended to the body since the previous boundary event.
    since_event: TokenCount,
    /// Records the value emitted, across every chunk.
    emitted: TokenCount,
}

impl<'store, Store> CommitSink<'store, Store>
where
    Store: ChunkStore + ?Sized,
{
    /// Opens a sink over a store under a committed profile.
    ///
    /// # Specification
    /// trivial.
    fn new(
        store: &'store mut Store,
        profile: &ValueProfile,
    ) -> Self
    {
        Self {
            store,
            chunker: TypedChunker::new(&profile.params()),
            body: BodyWriter::default(),
            preimage: Vec::new(),
            open: Vec::new(),
            shape: EmissionShape::Empty,
            since_event: TokenCount::ZERO,
            emitted: TokenCount::ZERO,
        }
    }

    /// Appends one record the value emitted, to the body and to the innermost
    /// residue preimage.
    ///
    /// # Specification
    /// - requires: the record's shape check has passed.
    /// - ensures: on success the record's bytes end both the body and the
    ///   preimage stack, and both counters are one higher.
    /// - provides: the one place an emitted record is accounted.
    /// - fails: the body writer's overflow refusal, and an overflow refusal at
    ///   a counter's width.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError::ArithmeticOverflow`] — a length or count passes its width.
    #[spec(captures: [entry_mark = self.body.mark(), entry_emitted = u64::from(self.emitted)],
        ensures: |ret| ret.is_err()
            || (self.body.mark() > entry_mark && u64::from(self.emitted) == entry_emitted.saturating_add(1_u64)))]
    fn emit(
        &mut self,
        record: Record<'_>,
    ) -> Result<(), ValueError>
    {
        let mark = self.body.mark();
        self.body.push(record)?;
        self.preimage
            .extend_from_slice(self.body.since(mark).as_ref());
        self.emitted = one_more(self.emitted)?;
        self.since_event = one_more(self.since_event)?;

        Ok(())
    }

    /// Frames the subtree from `start` to the end of the body as a chunk,
    /// stores it, and splices a child record naming it in its place.
    ///
    /// # Specification
    /// - requires: `start` is the open record of a subtree that just closed.
    /// - ensures: on success the store holds the subtree's chunk, and the body
    ///   ends with one child record addressing that chunk at offset zero
    ///   instead of the subtree.
    /// - provides: the cut, and so every seam the reader later crosses.
    /// - fails: [`frame_chunk`]'s and the store's refusals, and an overflow
    ///   refusal at the event counter's width.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError`] — as listed above.
    #[spec(ensures: |ret| ret.is_err()
        || matches!(
            split_record(self.body.since(start)),
            Ok(BodyFront::Record(Record::Child(pointer), rest))
                if rest.as_ref().is_empty() && pointer.offset() == TokenOffset::ZERO
        ))]
    fn cut(
        &mut self,
        start: BodyMark,
    ) -> Result<(), ValueError>
    {
        let chunk = frame_chunk(self.body.since(start))?;
        self.store.insert(chunk.as_verified())?;
        self.body.truncate(start);
        self.body.push(Record::Child(ContentPtr::new(
            chunk.digest(),
            TokenOffset::ZERO,
        )))?;
        self.since_event = one_more(self.since_event)?;

        Ok(())
    }

    /// Frames what remains as the root chunk and names the committed value.
    ///
    /// # Specification
    /// - requires: the emission is over.
    /// - ensures: on success the store holds the root chunk, and the pointer
    ///   addresses it at offset zero.
    /// - provides: the traversal's last step.
    /// - fails: [`ValueError::MalformedEmission`] when the emission was not one
    ///   closed value, and [`frame_chunk`]'s and the store's refusals.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError`] — as listed above.
    #[spec(ensures: |ret| ret
        .as_ref()
        .ok()
        .is_none_or(|&(root, _count)| root.offset() == TokenOffset::ZERO))]
    fn finish(self) -> Result<(ContentPtr, TokenCount), ValueError>
    {
        self.shape.finish()?;
        let chunk = frame_chunk(self.body.as_body())?;
        self.store.insert(chunk.as_verified())?;

        Ok((
            ContentPtr::new(chunk.digest(), TokenOffset::ZERO),
            self.emitted,
        ))
    }
}

impl<Store> TokenSink for CommitSink<'_, Store>
where
    Store: ChunkStore + ?Sized,
{
    /// Opens a constructor: a frame, a residue preimage, an open record.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success one frame deeper, its preimage opened with
    ///   [`RESIDUE_DOMAIN`], and the open record appended.
    /// - provides: the committing half of [`TokenSink::open`].
    /// - fails: the shape refusal for a second root, and [`CommitSink`]'s
    ///   overflow refusals.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError`] — as listed above.
    #[inline]
    #[spec(captures: [entry_depth = self.open.len()],
        ensures: |ret| ret.is_err() || self.open.len() == entry_depth.saturating_add(1_usize))]
    fn open(
        &mut self,
        tag: ConstructorTag,
    ) -> Result<(), ValueError>
    {
        self.shape.open()?;
        self.open.push(OpenFrame {
            body_start: self.body.mark(),
            preimage_start: PreimageMark(self.preimage.len()),
        });
        self.preimage.extend_from_slice(RESIDUE_DOMAIN);

        self.emit(Record::Open(tag))
    }

    /// Appends a word record.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the word record is appended.
    /// - provides: the committing half of [`TokenSink::word`].
    /// - fails: the shape refusal outside every constructor.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError`] — as listed above.
    #[inline]
    #[spec(captures: [entry_emitted = u64::from(self.emitted)],
        ensures: |ret| ret.is_err() || u64::from(self.emitted) == entry_emitted.saturating_add(1_u64))]
    fn word(
        &mut self,
        word: CanonicalWord,
    ) -> Result<(), ValueError>
    {
        self.shape.payload()?;

        self.emit(Record::Word(word))
    }

    /// Appends a bytes record.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the bytes record is appended.
    /// - provides: the committing half of [`TokenSink::bytes`].
    /// - fails: the shape refusal outside every constructor, and an overflow
    ///   refusal for a payload past sixty-four bits of length.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError`] — as listed above.
    #[inline]
    #[spec(captures: [entry_emitted = u64::from(self.emitted)],
        ensures: |ret| ret.is_err() || u64::from(self.emitted) == entry_emitted.saturating_add(1_u64))]
    fn bytes(
        &mut self,
        bytes: TokenBytes<'_>,
    ) -> Result<(), ValueError>
    {
        self.shape.payload()?;

        self.emit(Record::Bytes(bytes))
    }

    /// Appends a child record for an already-committed value.
    ///
    /// # Specification
    /// - requires: the pointer addresses a chunk the store holds.
    /// - ensures: on success the child record is appended unchanged.
    /// - provides: the committing half of [`TokenSink::child_pointer`].
    /// - fails: the shape refusal outside every constructor.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError`] — as listed above.
    #[inline]
    #[spec(captures: [entry_emitted = u64::from(self.emitted)],
        ensures: |ret| ret.is_err() || u64::from(self.emitted) == entry_emitted.saturating_add(1_u64))]
    fn child_pointer(
        &mut self,
        pointer: ContentPtr,
    ) -> Result<(), ValueError>
    {
        self.shape.payload()?;

        self.emit(Record::Child(pointer))
    }

    /// Closes a constructor, raising its boundary event and cutting when the
    /// scanner says so.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the close record is appended and the frame popped;
    ///   for an inner constructor the event carried the records since the
    ///   previous event and the subtree's residue, the parent's preimage holds
    ///   the subtree digest, and a cut decision replaced the subtree with a
    ///   child record; the outermost close raises no event.
    /// - provides: every cut the traversal makes.
    /// - fails: the shape refusal with nothing open, [`CommitSink`]'s refusals,
    ///   and the cut's.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError`] — as listed above.
    ///
    /// # Adequacy
    /// - hypothesis: L2 agreement — committing and dereferencing return the
    ///   value, deterministically, across seams the scanner placed — plus L3
    ///   for the outermost close, separated by a value whose root would cut.
    /// - witness: `tests::values::a_committed_value_derefs_back_equal`
    /// - witness: `tests::values::a_value_larger_than_one_chunk_is_read_across_seams`
    /// - witness: `tests::flat::flat_bytes_equal_the_single_chunk_body`
    #[inline]
    #[spec(captures: [entry_depth = self.open.len()],
        ensures: |ret| ret.is_err() || self.open.len().saturating_add(1_usize) == entry_depth)]
    fn close(&mut self) -> Result<(), ValueError>
    {
        let closing = self.shape.close()?;
        self.emit(Record::Close)?;

        let Some(frame) = self.open.pop()
        else {
            return Err(ValueError::MalformedEmission {
                fault: EmissionFault::CloseWithoutOpen,
            });
        };
        let subtree = blake3::hash(
            self.preimage
                .get(frame.preimage_start.0 ..)
                .unwrap_or_default(),
        );
        self.preimage.truncate(frame.preimage_start.0);

        if closing == Closing::Root {
            return Ok(());
        }

        self.preimage.push(NESTED_SUBTREE);
        self.preimage.extend_from_slice(subtree.as_bytes());

        let Some(head) = subtree.as_bytes().first_chunk::<8>()
        else {
            return Ok(());
        };
        let event = BoundaryEvent::new(
            self.since_event,
            BoundaryResidue::from(u64::from_le_bytes(*head)),
        );
        self.since_event = TokenCount::ZERO;

        match self.chunker.on_boundary(event) {
            | CutDecision::Cut(_reason) => self.cut(frame.body_start),
            | CutDecision::Continue => Ok(()),
        }
    }
}

/// Counts one more record, refusing a count past the width.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `|ret| ret.is_ok() == (u64::from(count) < u64::MAX)` — the
///   successor exactly when it fits.
/// - provides: the step both of the traversal's counters advance by.
/// - fails: [`ValueError::ArithmeticOverflow`] naming the token count.
/// - panics: none.
///
/// # Errors
/// [`ValueError::ArithmeticOverflow`] — the count is already `u64::MAX`.
#[spec(ensures: |ret| ret.is_ok() == (u64::from(count) < u64::MAX))]
fn one_more(count: TokenCount) -> Result<TokenCount, ValueError>
{
    u64::from(count)
        .checked_add(1_u64)
        .map(TokenCount::from)
        .ok_or(ValueError::ArithmeticOverflow {
            quantity: ValueQuantity::TokenCount,
        })
}

/// Commits a value into a store as a chunk DAG and names it.
///
/// # Specification
/// - requires: `profile` is the profile every reader of the value agrees on.
/// - ensures: on success every chunk the traversal cut is in `store` under its
///   own digest, and the manifest carries `profile`, the root chunk at offset
///   zero, and the number of records the value emitted. Committing is a
///   deterministic function of the value and the profile: the same value
///   commits to the same root, and two values sharing a subtree share the
///   chunks it was cut into wherever the scanner's pending count agrees.
/// - provides: the value plane's write path.
/// - fails: [`ValueError::UnsupportedIndexBase`] for a chunk-local profile,
///   before anything is written; [`ValueError::MalformedEmission`] for an
///   emission that is not one balanced value; the framing's and the store's
///   refusals.
/// - panics: none.
///
/// # Errors
/// [`ValueError`] — as listed above.
///
/// # Adequacy
/// - hypothesis: L2 agreement — the same value commits to the same root in two
///   stores, shared subtrees are stored once, and an early edit adds few chunks
///   — plus L3 for the chunk-local refusal and each emission fault.
/// - witness: `tests::values::the_same_value_commits_to_the_same_pointer`
/// - witness: `tests::values::a_shared_subtree_is_stored_once`
/// - witness: `tests::values::an_early_edit_moves_only_its_own_chunk_under_chunk_local_bases`
/// - witness: `tests::values::a_malformed_emission_is_refused_by_name`
#[inline]
#[spec(ensures: |ret| (ret.is_err() || profile.index_base() == ChildIndexBase::Absolute)
    && ret
        .as_ref()
        .ok()
        .is_none_or(|manifest| manifest.profile() == profile && manifest.root().offset() == TokenOffset::ZERO))]
pub fn cam_commit<Store, Value>(
    store: &mut Store,
    profile: &ValueProfile,
    value: &Value,
) -> Result<ValueManifest, ValueError>
where
    Store: ChunkStore + ?Sized,
    Value: CanonicalValue,
{
    let base = profile.index_base();
    if base == ChildIndexBase::ChunkLocal {
        return Err(ValueError::UnsupportedIndexBase { base });
    }

    let mut sink = CommitSink::new(store, profile);
    value.emit_tokens(&mut sink)?;
    let (root, token_count) = sink.finish()?;

    Ok(ValueManifest::new(*profile, root, token_count))
}
