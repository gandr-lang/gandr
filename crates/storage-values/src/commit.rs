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
use crate::closure::add_tokens;
use crate::closure::walk_closure;
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
///
/// # Specification
/// - requires: nothing.
/// - ensures: identifies one open constructor in a sink's body and residue
///   preimage buffers.
/// - provides: the two starts a close and possible cut consume.
/// - fails: never.
/// - panics: none.
/// - executable: none — the two buffers that give the marks meaning belong to
///   the sink, not to this pair of positions.
///
/// # Adequacy
/// - hypothesis: L3 on two nested constructors observes live marks before and
///   after a close; the owning sink rejects a mark at either buffer's end and a
///   damaged residue domain. This separates stale or unbound marks on that
///   path, not all emission histories.
/// - witness: `commit::tests::open_frames_bind_live_body_and_residue_marks`
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
///
/// # Specification
/// - requires: nothing.
/// - ensures: each live frame addresses an open record in the body and a
///   residue domain at the start of its preimage. Counter overflow or a store
///   refusal need not roll back other state.
/// - provides: the live positions needed to close and cut constructors.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 on two nested constructors observes exact committed bytes
///   and delivered count, and rejects displaced body/preimage marks and a
///   damaged domain. These separate unbound cached positions and lost records;
///   store correctness remains the store implementation's contract.
/// - witness: `commit::tests::open_frames_bind_live_body_and_residue_marks`
#[spec(maintains: self.open.iter().all(|frame|
    matches!(split_record(self.body.since(frame.body_start)),
        Ok(BodyFront::Record(Record::Open(_tag), _rest)))
    && self.preimage.get(frame.preimage_start.0 ..)
        .is_some_and(|suffix| suffix.starts_with(RESIDUE_DOMAIN))))]
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
    /// Records a reader of the value will deliver, across every chunk.
    delivered: TokenCount,
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
            delivered: TokenCount::ZERO,
        }
    }

    /// Appends one record the value emitted, to the body and to the innermost
    /// residue preimage, counting the records a reader delivers for it.
    ///
    /// # Specification
    /// - requires: the record's shape check has passed, and `delivers` is the
    ///   records a reader delivers in the record's place: one for a record of
    ///   the value's own, the embedded subtree's total for a child record.
    /// - ensures: on success the record's bytes end both the body and the
    ///   preimage stack, the event counter is one higher, and the delivered
    ///   count is `delivers` higher.
    /// - provides: the one place an emitted record is accounted.
    /// - fails: the body writer's overflow refusal, and an overflow refusal at
    ///   a counter's width.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError::ArithmeticOverflow`] — a length or count passes its width.
    ///
    /// # Adequacy
    /// - hypothesis: L3 on a literal nested value observes exact open, word,
    ///   binary payload and close records and a count of six. L2 compares the
    ///   cuts with an independent scanner over generated trees of at most 4096
    ///   records, separating changed residue preimages and record accounting on
    ///   that finite domain.
    /// - witness: `commit::tests::open_frames_bind_live_body_and_residue_marks`
    /// - witness: `tests::laws::the_cuts_agree_with_a_reference_scanner`
    #[spec(captures: [entry_mark = self.body.mark(), entry_delivered = u64::from(self.delivered),
        entry_event = u64::from(self.since_event)],
        ensures: |ret| ret.is_err()
            || (matches!(split_record(self.body.since(entry_mark)),
                    Ok(BodyFront::Record(found, rest)) if found == record && rest.as_ref().is_empty())
                && self.preimage.ends_with(self.body.since(entry_mark).as_ref())
                && entry_event.checked_add(1_u64) == Some(u64::from(self.since_event))
                && entry_delivered.checked_add(u64::from(delivers)) == Some(u64::from(self.delivered))))]
    fn emit(
        &mut self,
        record: Record<'_>,
        delivers: TokenCount,
    ) -> Result<(), ValueError>
    {
        let mark = self.body.mark();
        self.body.push(record)?;
        self.preimage
            .extend_from_slice(self.body.since(mark).as_ref());
        self.delivered = add_tokens(self.delivered, delivers)?;
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
    ///
    /// # Adequacy
    /// - hypothesis: L2 on generated trees of at most 4096 records compares
    ///   spliced flat bytes and exact cut positions with an independent
    ///   scanner. L3 at kappa one, for caps 1, 2, 3, 64 and `u64::MAX`,
    ///   observes every inner constructor cut. This separates missing cuts,
    ///   wrong subtrees and displaced replacement pointers.
    /// - witness: `tests::laws::the_cuts_agree_with_a_reference_scanner`
    /// - witness: `tests::laws::an_edit_under_every_cut_affects_exactly_its_path`
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 on a literal six-record nested value observes the exact
    ///   stored root body and delivered count. Named malformed emissions
    ///   exercise missing and unclosed roots. These distinguish changed root
    ///   bytes, wrong counts and acceptance of unfinished emission.
    /// - witness: `commit::tests::open_frames_bind_live_body_and_residue_marks`
    /// - witness: `tests::values::a_malformed_emission_is_refused_by_name`
    #[spec(captures: delivered = self.delivered, ensures: |ret| ret
        .as_ref()
        .ok()
        .is_none_or(|&(root, count)| root.offset() == TokenOffset::ZERO && count == delivered))]
    fn finish(self) -> Result<(ContentPtr, TokenCount), ValueError>
    {
        self.shape.finish()?;
        let chunk = frame_chunk(self.body.as_body())?;
        self.store.insert(chunk.as_verified())?;

        Ok((
            ContentPtr::new(chunk.digest(), TokenOffset::ZERO),
            self.delivered,
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 on two nested constructors observes their live body and
    ///   residue marks, exact final bytes and delivered count; malformed
    ///   emissions distinguish a second root. This separates missed pushes,
    ///   wrong domain starts and lost open records on these inputs.
    /// - witness: `commit::tests::open_frames_bind_live_body_and_residue_marks`
    /// - witness: `tests::values::a_malformed_emission_is_refused_by_name`
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

        self.emit(Record::Open(tag), TokenCount::from(1_u64))
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 on a literal word seven inside two constructors
    ///   observes exact stored bytes and the delivered count. A payload outside
    ///   any constructor is refused by name, separating payload replacement,
    ///   accounting errors and missing shape admission.
    /// - witness: `commit::tests::open_frames_bind_live_body_and_residue_marks`
    /// - witness: `tests::values::a_malformed_emission_is_refused_by_name`
    #[inline]
    #[spec(captures: [entry_delivered = u64::from(self.delivered)],
        ensures: |ret| ret.is_err() || u64::from(self.delivered) == entry_delivered.saturating_add(1_u64))]
    fn word(
        &mut self,
        word: CanonicalWord,
    ) -> Result<(), ValueError>
    {
        self.shape.payload()?;

        self.emit(Record::Word(word), TokenCount::from(1_u64))
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 on binary bytes zero and 255 inside two constructors
    ///   observes the exact length-prefixed stored image and delivered count.
    ///   This separates text coercion, byte replacement, wrong lengths and
    ///   counting payload bytes as records; oversized allocations are not
    ///   exercised.
    /// - witness: `commit::tests::open_frames_bind_live_body_and_residue_marks`
    #[inline]
    #[spec(captures: [entry_delivered = u64::from(self.delivered)],
        ensures: |ret| ret.is_err() || u64::from(self.delivered) == entry_delivered.saturating_add(1_u64))]
    fn bytes(
        &mut self,
        bytes: TokenBytes<'_>,
    ) -> Result<(), ValueError>
    {
        self.shape.payload()?;

        self.emit(Record::Bytes(bytes), TokenCount::from(1_u64))
    }

    /// Appends a child record for an already-committed value, counting the
    /// records its subtree delivers.
    ///
    /// # Specification
    /// - requires: nothing; a pointer whose closure the store cannot answer for
    ///   is refused.
    /// - ensures: on success the child record is appended unchanged, and the
    ///   delivered count grows by the records a reader of the pointer delivers,
    ///   so the manifest counts the value a reader reads back.
    /// - provides: the committing half of [`TokenSink::child_pointer`].
    /// - fails: the shape refusal outside every constructor, and the closure
    ///   walk's refusals for the pointer — [`ValueError::UnknownChunk`] naming
    ///   a chunk of its closure the store does not hold among them.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError`] — as listed above.
    ///
    /// # Adequacy
    /// - hypothesis: L2 on generated trees of at most 4096 records observes
    ///   that embedding adds exactly two delivered records and the closure is
    ///   the store's whole digest set. L3 on a depth-four fixture with a chunk
    ///   missing two seams down observes its exact refusal. These separate
    ///   shallow accounting, omitted descendants and acceptance of missing
    ///   data.
    /// - witness: `tests::closure::the_closure_is_every_chunk_the_commit_wrote`
    /// - witness: `tests::closure::a_missing_descendant_fails_the_closure_by_name`
    #[inline]
    #[spec(captures: [entry_delivered = u64::from(self.delivered)],
        ensures: |ret| ret.is_err() || u64::from(self.delivered) > entry_delivered)]
    fn child_pointer(
        &mut self,
        pointer: ContentPtr,
    ) -> Result<(), ValueError>
    {
        self.shape.payload()?;
        // economy: each embedding walks its pointer's closure afresh; a
        // per-commit memo of embedded pointers if embedding-heavy codecs show.
        let embedded = walk_closure(&*self.store, pointer)?;

        self.emit(Record::Child(pointer), embedded.token_count())
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
    /// - hypothesis: L2 agreement — the constructors cut, read off the stored
    ///   chunks, are the ones a reference scanner recomputes from the flat form
    ///   alone, over generated values of at most 4096 records and profiles
    ///   biased toward runs ending at the cap and one record past it. The exact
    ///   reconstructed values separate lost or changed payloads. L3 separates
    ///   the uncut root and every inner constructor cut at kappa one for caps
    ///   1, 2, 3, 64 and `u64::MAX`.
    /// - witness: `tests::laws::the_cuts_agree_with_a_reference_scanner`
    /// - witness: `tests::laws::an_edit_under_every_cut_affects_exactly_its_path`
    /// - witness: `tests::values::a_committed_value_derefs_back_equal`
    /// - witness: `tests::values::a_value_larger_than_one_chunk_is_read_across_seams`
    /// - witness: `tests::flat::flat_bytes_equal_the_single_chunk_body`
    #[inline]
    #[spec(captures: [entry_depth = self.open.len()],
        ensures: |ret| ret.is_err() || self.open.len().saturating_add(1_usize) == entry_depth)]
    fn close(&mut self) -> Result<(), ValueError>
    {
        let closing = self.shape.close()?;
        self.emit(Record::Close, TokenCount::from(1_u64))?;

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
///
/// # Adequacy
/// - hypothesis: L3 at zero, `u64::MAX` minus one and `u64::MAX` observes the
///   exact successor or token-count overflow, separating an off-by-one ceiling,
///   wrapping and a substituted successor.
/// - witness: `commit::tests::record_successors_refuse_width_overflow`
#[spec(ensures: |ret| ret.is_ok() == (u64::from(count) < u64::MAX)
    && ret.as_ref().ok().is_none_or(|next|
        u64::from(count).checked_add(1_u64) == Some(u64::from(*next))))]
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
///   zero, and the number of records a reader of the root delivers — every
///   record the value emitted, each embedded pointer counted as the records its
///   value delivers. Committing is a deterministic function of the value and
///   the profile: the same value commits to the same root, and two values
///   sharing a subtree share the chunks it was cut into wherever the scanner's
///   pending count agrees.
/// - provides: the value plane's write path.
/// - fails: [`ValueError::UnsupportedIndexBase`] for a chunk-local profile,
///   before anything is written; [`ValueError::MalformedEmission`] for an
///   emission that is not one balanced value; the closure walk's refusals for
///   an embedded pointer; the framing's and the store's refusals.
/// - panics: none.
///
/// # Errors
/// [`ValueError`] — as listed above.
///
/// # Adequacy
/// - hypothesis: L2 on generated values of at most 4096 records observes the
///   same manifest in an empty store and after at most six generated priors,
///   some sharing subtrees and some under other profiles, ending with exactly
///   the union of the two; shared subtrees are stored once, an early edit adds
///   few chunks, and a value embedding a committed one has a token count its
///   closure delivers — plus L3 for the chunk-local refusal, each emission
///   fault, an embedded value missing a chunk, and a value mutated after its
///   commit, which commits to a new root while the store grows by exactly the
///   chunks the edit affected.
/// - witness: `tests::laws::a_root_pointer_does_not_depend_on_what_the_store_holds`
/// - witness: `tests::laws::a_value_mutated_after_commit_commits_anew_and_the_old_pointer_still_reads_the_old_value`
/// - witness: `tests::values::the_same_value_commits_to_the_same_pointer`
/// - witness: `tests::values::a_shared_subtree_is_stored_once`
/// - witness: `tests::values::an_early_edit_moves_only_its_own_chunk_under_chunk_local_bases`
/// - witness: `tests::values::a_malformed_emission_is_refused_by_name`
/// - witness: `tests::closure::the_closure_is_every_chunk_the_commit_wrote`
/// - witness: `tests::closure::a_missing_descendant_fails_the_closure_by_name`
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

#[cfg(test)]
mod tests
{
    use gandr_storage_chunker::Kappa;
    use gandr_storage_chunker::TokenCap;
    use gandr_storage_chunker::TokenCount;
    use gandr_storage_chunker::TypedChunkerParams;

    use super::CommitSink;
    use super::PreimageMark;
    use super::one_more;
    use crate::CanonicalWord;
    use crate::ChildIndexBase;
    use crate::ChunkStore as _;
    use crate::CodecId;
    use crate::CodecIdentity;
    use crate::CodecVersion;
    use crate::ConstructorTag;
    use crate::InMemoryChunkStore;
    use crate::TokenBytes;
    use crate::TokenOffset;
    use crate::TokenSink as _;
    use crate::ValueError;
    use crate::ValueProfile;
    use crate::ValueQuantity;

    #[test]
    fn record_successors_refuse_width_overflow()
    {
        assert_eq!(one_more(TokenCount::ZERO), Ok(TokenCount::from(1_u64)));
        assert_eq!(
            one_more(TokenCount::from(u64::MAX - 1_u64)),
            Ok(TokenCount::from(u64::MAX))
        );
        assert_eq!(
            one_more(TokenCount::from(u64::MAX)),
            Err(ValueError::ArithmeticOverflow {
                quantity: ValueQuantity::TokenCount,
            })
        );
    }

    #[test]
    fn open_frames_bind_live_body_and_residue_marks()
    {
        let params = TypedChunkerParams::new(
            Kappa::try_from(u64::MAX).expect("nonzero kappa"),
            TokenCap::try_from(u64::MAX).expect("nonzero cap"),
        );
        let profile = ValueProfile::new(
            params,
            CodecIdentity::new(CodecId::from(1_u16), CodecVersion::from(1_u16)),
            ChildIndexBase::Absolute,
        );
        let mut store = InMemoryChunkStore::new();
        let mut sink = CommitSink::new(&mut store, &profile);
        assert!(anodized::types::Spec::predicate(&sink));
        sink.open(ConstructorTag::from(0_u8))
            .expect("the root opens");
        sink.open(ConstructorTag::from(1_u8))
            .expect("the child opens");
        sink.word(CanonicalWord::from(7_u64))
            .expect("the word emits");
        sink.bytes(TokenBytes::from(&[0_u8, 255][..]))
            .expect("the binary payload emits");
        assert_eq!(sink.open.len(), 2_usize);
        assert!(anodized::types::Spec::predicate(&sink));

        let frame = *sink.open.last().expect("an open child");
        let end = sink.body.mark();
        sink.open.last_mut().expect("an open child").body_start = end;
        assert!(!anodized::types::Spec::predicate(&sink));
        *sink.open.last_mut().expect("an open child") = frame;
        let end = PreimageMark(sink.preimage.len());
        sink.open.last_mut().expect("an open child").preimage_start = end;
        assert!(!anodized::types::Spec::predicate(&sink));
        *sink.open.last_mut().expect("an open child") = frame;
        let first = *sink
            .preimage
            .get(frame.preimage_start.0)
            .expect("a residue domain");
        *sink
            .preimage
            .get_mut(frame.preimage_start.0)
            .expect("a residue domain") = 0_u8;
        assert!(!anodized::types::Spec::predicate(&sink));
        *sink
            .preimage
            .get_mut(frame.preimage_start.0)
            .expect("a residue domain") = first;
        sink.close().expect("the child closes");
        assert_eq!(sink.open.len(), 1_usize);
        assert!(anodized::types::Spec::predicate(&sink));
        sink.close().expect("the root closes");
        assert!(sink.open.is_empty());
        assert!(anodized::types::Spec::predicate(&sink));
        let (root, delivered) = sink.finish().expect("the complete value commits");
        assert_eq!(root.offset(), TokenOffset::ZERO);
        assert_eq!(delivered, TokenCount::from(6_u64));
        let chunk = store.load(root.digest()).expect("the root was stored");
        assert_eq!(chunk.body().as_ref(), &[
            1_u8, 0, 1, 1, 2, 7, 0, 0, 0, 0, 0, 0, 0, 3, 2, 0, 0, 0, 0, 0, 0, 0, 0, 255, 5, 5,
        ]);
    }
}
