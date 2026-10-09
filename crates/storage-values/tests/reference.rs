//! The references the laws compare against, written from the README's byte
//! languages alone: a record reader, the cut rule recomputed over a flat form,
//! a chunk DAG read back into one record stream, and a store that lists what
//! it holds. None of it calls the crate's reader, scanner or traversal.

use alloc::collections::BTreeSet;

use gandr_storage_chunker::TypedChunkerParams;
use gandr_storage_values::ChunkDigest;
use gandr_storage_values::ChunkStore;
use gandr_storage_values::ContentPtr;
use gandr_storage_values::InMemoryChunkStore;
use gandr_storage_values::TokenBody;
use gandr_storage_values::TokenOffset;
use gandr_storage_values::ValueError;
use gandr_storage_values::VerifiedChunk;

/// The domain every residue preimage opens with, as the README writes it.
const RESIDUE_DOMAIN: &[u8] = b"gandr:storage-values:residue:v1";

/// The residue preimage's marker before a nested constructor's digest.
const NESTED_SUBTREE: u8 = 0x00_u8;

/// A record's index in a value's flat record stream.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct RecordIndex(pub usize);

/// What a record is.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Kind
{
    /// A constructor opens.
    Open,
    /// A word.
    Word,
    /// A byte string.
    Bytes,
    /// A pointer to a stored chunk.
    Child(ContentPtr),
    /// The innermost open constructor closes.
    Close,
}

/// One record of a body, with the bytes that encode it.
#[derive(Clone, Copy, Debug)]
pub struct Record<'body>
{
    /// What the record is.
    pub kind: Kind,
    /// The record's whole encoding, kind byte first.
    pub bytes: TokenBody<'body>,
}

/// The front of a body.
#[derive(Clone, Copy, Debug)]
enum Front<'body>
{
    /// The body is exhausted.
    Empty,
    /// One record, and the body after it.
    Record(Record<'body>, TokenBody<'body>),
}

/// Reads one record off the front of a body by the documented layout.
///
/// # Specification
/// - requires: `body` is a sequence of whole records.
/// - ensures: [`Front::Empty`] for an empty body, otherwise the first record
///   and the bytes after it.
/// - provides: the one record grammar every reference here reads by.
/// - panics: on an unknown kind byte or a body ending inside a record.
fn front(body: TokenBody<'_>) -> Front<'_>
{
    let bytes: &[u8] = body.into();
    let Some((&kind, after)) = bytes.split_first()
    else {
        return Front::Empty;
    };
    let (kind, payload) = match kind {
        | 0x01 => (Kind::Open, 1_usize),
        | 0x02 => (Kind::Word, 8_usize),
        | 0x03 => {
            let declared = after.first_chunk::<8>().expect("a bytes length");
            let length = usize::try_from(u64::from_le_bytes(*declared)).expect("a payload length");
            (
                Kind::Bytes,
                length.checked_add(8_usize).expect("a record length"),
            )
        },
        | 0x04 => {
            let digest = after.first_chunk::<32>().expect("a child digest");
            let offset = after
                .get(32_usize ..)
                .and_then(<[u8]>::first_chunk::<4>)
                .expect("a child offset");
            let pointer = ContentPtr::new(
                ChunkDigest::from(*digest),
                TokenOffset::from(u32::from_le_bytes(*offset)),
            );
            (Kind::Child(pointer), 36_usize)
        },
        | 0x05 => (Kind::Close, 0_usize),
        | other => panic!("no record has kind {other:#04x}"),
    };
    let (record, rest) = bytes
        .split_at_checked(payload.checked_add(1_usize).expect("a record length"))
        .expect("a body of whole records");

    Front::Record(
        Record {
            kind,
            bytes: TokenBody::from(record),
        },
        TokenBody::from(rest),
    )
}

/// Splits a body into its records.
///
/// # Specification
/// trivial.
pub fn records(body: TokenBody<'_>) -> Vec<Record<'_>>
{
    let mut records = Vec::new();
    let mut rest = body;
    while let Front::Record(record, after) = front(rest) {
        records.push(record);
        rest = after;
    }

    records
}

/// One constructor open during the reference scan.
#[derive(Clone, Debug)]
struct Frame
{
    /// The index of the constructor's open record.
    open: RecordIndex,
    /// The constructor's residue preimage so far.
    preimage: Vec<u8>,
}

/// Recomputes, from a flat form alone, which constructors the cut rule cuts.
///
/// # Specification
/// - requires: `flat` is a flat form: one balanced value, no child record.
/// - ensures: the open-record index of every cut constructor, in stream order.
///   A constructor's residue is the first eight bytes, little-endian, of BLAKE3
///   over the residue domain, its open record, each word or bytes record it
///   holds directly, `0x00` and the subtree digest of each constructor nested
///   in it, and its close record; its subtree digest is that hash. Every record
///   joins the pending count at the next constructor exit, and so does the one
///   child record that takes a cut subtree's place; at every exit but the
///   outermost the constructor is cut when the count has reached the cap, or
///   else when its residue is divisible by kappa, and a cut empties the count.
/// - provides: the cut rule as the README states it, sharing no code with the
///   committing traversal.
/// - panics: on a body that is not a flat form.
pub fn reference_cuts(
    flat: TokenBody<'_>,
    params: &TypedChunkerParams,
) -> Vec<RecordIndex>
{
    let kappa = u64::from(params.kappa());
    let cap = u64::from(params.cap());
    let mut open: Vec<Frame> = Vec::new();
    let mut cuts = Vec::new();
    let mut since_event = 0_u64;
    let mut pending = 0_u64;

    for (index, record) in records(flat).into_iter().enumerate() {
        since_event = since_event.checked_add(1_u64).expect("a record count");
        let bytes: &[u8] = record.bytes.into();
        match record.kind {
            | Kind::Open => {
                let mut preimage = RESIDUE_DOMAIN.to_vec();
                preimage.extend_from_slice(bytes);
                open.push(Frame {
                    open: RecordIndex(index),
                    preimage,
                });
            },
            | Kind::Word | Kind::Bytes => {
                open.last_mut()
                    .expect("a payload sits inside a constructor")
                    .preimage
                    .extend_from_slice(bytes);
            },
            | Kind::Child(_) => panic!("a flat form carries no child record"),
            | Kind::Close => {
                let mut frame = open.pop().expect("a close ends an open constructor");
                frame.preimage.extend_from_slice(bytes);
                let subtree = blake3::hash(&frame.preimage);
                let Some(parent) = open.last_mut()
                else {
                    continue;
                };
                parent.preimage.push(NESTED_SUBTREE);
                parent.preimage.extend_from_slice(subtree.as_bytes());

                let residue = u64::from_le_bytes(
                    *subtree
                        .as_bytes()
                        .first_chunk::<8>()
                        .expect("a digest is thirty-two bytes"),
                );
                pending = pending.saturating_add(since_event);
                since_event = 0_u64;
                if pending >= cap || residue.checked_rem(kappa) == Some(0_u64) {
                    cuts.push(frame.open);
                    pending = 0_u64;
                    // The child record that takes the cut subtree's place.
                    since_event = 1_u64;
                }
            },
        }
    }

    // A constructor's cut is decided at its close, after every cut beneath it;
    // stream order is the order of the open records.
    cuts.sort_unstable();
    cuts
}

/// A chunk DAG read back into the record stream it was cut from.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Spliced
{
    /// The records, each child record replaced by the body it names.
    pub flat: Vec<u8>,
    /// Where each chunk below the root begins: the index of its first record
    /// in the spliced stream, in stream order.
    pub chunk_starts: Vec<RecordIndex>,
}

/// Loads the body of the chunk a pointer names.
///
/// # Specification
/// - requires: the store holds the chunk.
/// - ensures: the verified chunk's body.
/// - provides: each step of [`splice`]'s descent.
/// - panics: when the store refuses the load, or the pointer is not at the
///   chunk's start, which no cut writes.
fn body_of(
    store: &dyn ChunkStore,
    pointer: ContentPtr,
) -> TokenBody<'_>
{
    assert_eq!(
        pointer.offset(),
        TokenOffset::ZERO,
        "a cut names its chunk from the start"
    );
    store
        .load(pointer.digest())
        .expect("every chunk a commit names is stored")
        .body()
}

/// Reads a committed value's chunk DAG back into one record stream, splicing
/// each child chunk's body where its child record stands.
///
/// # Specification
/// - requires: `root` was committed into `store` from a value with no embedded
///   pointer.
/// - ensures: the spliced records and where each chunk below the root begins.
/// - provides: the boundaries a commit chose, read off the stored chunks.
/// - panics: when the store refuses a load.
pub fn splice(
    store: &dyn ChunkStore,
    root: ContentPtr,
) -> Spliced
{
    let mut flat = Vec::new();
    let mut chunk_starts = Vec::new();
    let mut written = 0_usize;
    let mut pending = vec![body_of(store, root)];

    while let Some(body) = pending.pop() {
        let Front::Record(record, rest) = front(body)
        else {
            continue;
        };
        pending.push(rest);
        match record.kind {
            | Kind::Child(pointer) => {
                chunk_starts.push(RecordIndex(written));
                pending.push(body_of(store, pointer));
            },
            | Kind::Open | Kind::Word | Kind::Bytes | Kind::Close => {
                flat.extend_from_slice(record.bytes.into());
                written = written.checked_add(1_usize).expect("a record count");
            },
        }
    }

    Spliced { flat, chunk_starts }
}

/// An in-memory chunk store that also lists every digest it holds.
#[derive(Clone, Debug, Default)]
pub struct Ledger
{
    /// The chunks.
    store: InMemoryChunkStore,
    /// The digest of every chunk in `store`.
    held: BTreeSet<ChunkDigest>,
}

impl Ledger
{
    /// Returns the digests held.
    ///
    /// # Specification
    /// trivial.
    pub const fn held(&self) -> &BTreeSet<ChunkDigest>
    {
        &self.held
    }
}

impl ChunkStore for Ledger
{
    /// Inserts the chunk and lists its digest.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the chunk is held and its digest listed.
    /// - provides: the in-memory store's write, observed.
    /// - fails: the in-memory store's refusals, before anything is listed.
    /// - panics: none.
    fn insert(
        &mut self,
        chunk: VerifiedChunk<'_>,
    ) -> Result<(), ValueError>
    {
        self.store.insert(chunk)?;
        let _listed = self.held.insert(chunk.digest());

        Ok(())
    }

    /// Loads from the in-memory store.
    ///
    /// # Specification
    /// trivial.
    fn load(
        &self,
        digest: ChunkDigest,
    ) -> Result<VerifiedChunk<'_>, ValueError>
    {
        self.store.load(digest)
    }
}
