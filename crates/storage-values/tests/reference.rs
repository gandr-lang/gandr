//! The references the laws compare against, written from the README's byte
//! languages alone: a record reader, the cut rule recomputed over a flat form,
//! a chunk DAG read back into one record stream, and a store that lists what
//! it holds. None of it calls the crate's reader, scanner or traversal.

use alloc::collections::BTreeSet;

use anodized::spec;
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
///
/// # Specification
/// - requires: nothing.
/// - ensures: the kind agrees with the complete wire image, including a byte
///   payload's declared length and every child pointer field.
/// - provides: a borrowed record whose classification retains its evidence.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 covers all five record kinds, exact borrowed extents,
///   binary bytes and a multibyte child offset; forged kind, length and pointer
///   claims fail independently of the production parser.
/// - witness: `tests::reference::records_preserve_fields_and_borrowed_extents`
#[spec(maintains: {
    let bytes: &[u8] = self.bytes.into();
    match self.kind {
        Kind::Open => bytes.len() == 2_usize && bytes.first() == Some(&0x01_u8),
        Kind::Word => bytes.len() == 9_usize && bytes.first() == Some(&0x02_u8),
        Kind::Bytes => bytes.first() == Some(&0x03_u8)
            && bytes.get(1 ..).and_then(<[u8]>::split_first_chunk::<8>)
                .is_some_and(|(declared, payload)|
                    usize::try_from(u64::from_le_bytes(*declared)) == Ok(payload.len())),
        Kind::Child(pointer) => bytes.len() == 37_usize
            && bytes.first() == Some(&0x04_u8)
            && bytes.get(1 ..).and_then(<[u8]>::first_chunk::<32>)
                .is_some_and(|digest| pointer.digest() == ChunkDigest::from(*digest))
            && bytes.get(33 ..).and_then(<[u8]>::first_chunk::<4>)
                .is_some_and(|offset| pointer.offset()
                    == TokenOffset::from(u32::from_le_bytes(*offset))),
        Kind::Close => bytes == [0x05_u8],
    }
})]
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
/// - fails: never within the admitted byte language.
/// - panics: on an unknown kind byte or a body ending inside a record.
///
/// # Adequacy
/// - hypothesis: L3 literal records cover all wire kinds and exhaustion; exact
///   pointer equality checks both returned views, not just copied bytes.
/// - witness: `tests::reference::records_preserve_fields_and_borrowed_extents`
#[spec(ensures: |ret| match ret {
    Front::Empty => body.as_ref().is_empty(),
    Front::Record(record, rest) => anodized::types::Spec::predicate(&record)
        && body.as_ref().split_at_checked(record.bytes.as_ref().len())
            .is_some_and(|(prefix, suffix)| core::ptr::eq(core::ptr::from_ref(prefix), core::ptr::from_ref(record.bytes.as_ref()))
                && core::ptr::eq(core::ptr::from_ref(suffix), core::ptr::from_ref(rest.as_ref()))),
})]
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
/// - requires: the body consists of whole records in the documented layout.
/// - ensures: the refined records partition the body's borrowed bytes exactly
///   once, in order, with no gaps, overlap or copied backing storage.
/// - fails: never within the admitted byte language.
/// - panics: on an unknown kind, truncation or unrepresentable payload length.
///
/// # Adequacy
/// - hypothesis: L3 one literal body has every kind and asymmetric field
///   values; each record's exact slice address and extent are checked.
/// - witness: `tests::reference::records_preserve_fields_and_borrowed_extents`
#[spec(ensures: |ret| ret.iter().try_fold(<&[u8]>::from(body),
    |remaining, record| {
        let (prefix, suffix) = remaining.split_at_checked(record.bytes.as_ref().len())?;
        (anodized::types::Spec::predicate(record)
            && core::ptr::eq(core::ptr::from_ref(prefix), core::ptr::from_ref(record.bytes.as_ref()))).then_some(suffix)
    })
    .is_some_and(<[u8]>::is_empty))]
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
///
/// # Specification
/// - requires: nothing.
/// - ensures: the residue preimage begins with the residue domain and a whole
///   open record. Its source index is historical, not certified by this state.
/// - provides: the prefix every reference subtree hash extends.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 distinguishes a complete opening prefix from a bare domain
///   and a changed domain; L2 generated cuts compare the whole model.
/// - witness: `tests::reference::cuts_and_splices_keep_record_coordinates`
/// - witness: `tests::laws::the_cuts_agree_with_a_reference_scanner`
#[spec(maintains: self.preimage.starts_with(RESIDUE_DOMAIN)
    && self.preimage.get(RESIDUE_DOMAIN.len() ..).is_some_and(|record|
        record.len() >= 2_usize && record.first() == Some(&0x01_u8)))]
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
/// - fails: never within the admitted flat language.
/// - panics: on a body that is not a flat form.
///
/// # Adequacy
/// - hypothesis: L2 compares independently recomputed cuts with stored chunk
///   boundaries on generated values bounded by 4096 records; L3 kappa one and
///   cap one select exactly the nonroot constructors in a literal eight-record
///   value, separating byte coordinates and root cuts.
/// - witness: `tests::laws::the_cuts_agree_with_a_reference_scanner`
/// - witness: `tests::reference::cuts_and_splices_keep_record_coordinates`
#[spec(ensures: |ret| {
    let every = u64::from(params.kappa()) == 1_u64 || u64::from(params.cap()) == 1_u64;
    let mut cuts = ret.iter().peekable();
    let mut rest = flat;
    let mut index = 0_usize;
    let mut valid = true;
    while let Front::Record(record, after) = front(rest) {
        let cut = cuts.next_if(|cut| cut.0 == index).is_some();
        let eligible = index > 0_usize && record.kind == Kind::Open;
        valid &= (!cut || eligible) && (!every || !eligible || cut);
        rest = after;
        index = index.saturating_add(1_usize);
    }
    valid && cuts.next().is_none()
})]
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
///
/// # Specification
/// - requires: nothing.
/// - ensures: the flat image has an opening/closing envelope, and nonroot chunk
///   starts are positive, strictly increasing and below the byte extent. This
///   necessary extent bound does not itself certify record boundaries.
/// - provides: observable consistency conditions on splicing evidence.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 exact flat bytes and start indices one and four distinguish
///   byte coordinates, zero/root starts, duplicates and reversed ordering;
///   generated L2 comparisons cover the full reconstruction relation.
/// - witness: `tests::reference::cuts_and_splices_keep_record_coordinates`
/// - witness: `tests::laws::chunking_is_invisible_to_the_flat_form`
#[spec(maintains: self.flat.len() >= 3_usize
    && self.flat.first() == Some(&0x01_u8) && self.flat.last() == Some(&0x05_u8)
    && self.chunk_starts.iter().all(|start| start.0 > 0_usize && start.0 < self.flat.len())
    && self.chunk_starts.windows(2).all(|pair| pair.first() < pair.get(1)))]
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
/// - fails: never when the named chunk is held.
/// - panics: when the store refuses the load, or the pointer is not at the
///   chunk's start, which no cut writes.
///
/// # Adequacy
/// - hypothesis: L3 two distinct literal leaf chunks are loaded through a
///   committed root; splicing must restore their exact words and positions.
/// - witness: `tests::reference::cuts_and_splices_keep_record_coordinates`
#[spec(requires: pointer.offset() == TokenOffset::ZERO,
    ensures: |ret| !ret.as_ref().is_empty())]
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
/// - fails: never for a retained commit within the admitted domain.
/// - panics: when the store refuses a load.
///
/// # Adequacy
/// - hypothesis: L2 compares reconstructed bytes on generated values bounded by
///   4096 records; L3 a forced-cut pair gives exact bytes and record starts one
///   and four, independently of the two child records in its stored body.
/// - witness: `tests::laws::chunking_is_invisible_to_the_flat_form`
/// - witness: `tests::reference::cuts_and_splices_keep_record_coordinates`
#[spec(requires: root.offset() == TokenOffset::ZERO,
    ensures: |ret| anodized::types::Spec::predicate(&ret))]
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
///
/// # Specification
/// - requires: nothing.
/// - ensures: the listed identities are exactly the authenticated chunks in the
///   backing store: cardinalities agree and every listed chunk loads.
/// - provides: an observable store-content set for history comparisons.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 fresh and repeated inserts preserve exact membership;
///   forged missing and same-size wrong listings fail. L2 generated histories
///   add zero through six prior values before comparing the exact set union.
/// - witness: `tests::reference::cuts_and_splices_keep_record_coordinates`
/// - witness: `tests::laws::a_root_pointer_does_not_depend_on_what_the_store_holds`
#[spec(maintains: self.held.len() == usize::from(self.store.chunk_count())
    && self.held.iter().all(|digest| self.store.load(*digest).is_ok()))]
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
    ///
    /// # Errors
    /// Propagates a backing-store refusal before changing the listing.
    ///
    /// # Adequacy
    /// - hypothesis: L3 a fresh leaf, its repeated insertion and a forced-cut
    ///   parent yield the exact identity set without counting the leaf twice;
    ///   bounded generated histories additionally vary retained prior values.
    /// - witness: `tests::reference::cuts_and_splices_keep_record_coordinates`
    /// - witness: `tests::laws::a_root_pointer_does_not_depend_on_what_the_store_holds`
    #[spec(captures: [listed = self.held.contains(&chunk.digest()), count = self.held.len()],
        ensures: |ret| if ret.is_ok() {
            self.held.contains(&chunk.digest())
                && self.held.len() == count.saturating_add(usize::from(!listed))
                && self.held.len() == usize::from(self.store.chunk_count())
                && self.store.load(chunk.digest()).is_ok()
        } else {
            self.held.len() == count && self.held.contains(&chunk.digest()) == listed
        })]
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

/// Reference records retain their exact source slices and complete field
/// claims.
#[test]
fn records_preserve_fields_and_borrowed_extents()
{
    let mut bytes = vec![
        1_u8, 0x7F, 2, 7, 0, 0, 0, 0, 0, 0, 0, 3, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0xFF, 4,
    ];
    bytes.extend_from_slice(&[0xA5_u8; 32]);
    bytes.extend_from_slice(&[4_u8, 3, 2, 1, 5]);
    let pointer = ContentPtr::new(
        ChunkDigest::from([0xA5_u8; 32]),
        TokenOffset::from(0x0102_0304_u32),
    );
    let parsed = records(TokenBody::from(bytes.as_slice()));
    assert!(parsed.iter().map(|record| record.kind).eq([
        Kind::Open,
        Kind::Word,
        Kind::Bytes,
        Kind::Child(pointer),
        Kind::Close
    ]));
    for (record, (start, end)) in
        parsed
            .iter()
            .zip([(0_usize, 2_usize), (2, 11), (11, 22), (22, 59), (59, 60)])
    {
        let expected = bytes.get(start .. end).expect("a literal record extent");
        assert!(core::ptr::eq(
            core::ptr::from_ref(<&[u8]>::from(record.bytes)),
            core::ptr::from_ref(expected)
        ));
        assert!(anodized::types::Spec::predicate(record));
    }
    assert!(matches!(front(TokenBody::from(&[][..])), Front::Empty));
    let wrong_tag = [2_u8, 0x7F];
    assert!(!anodized::types::Spec::predicate(&Record {
        kind: Kind::Open,
        bytes: TokenBody::from(wrong_tag.as_slice())
    }));
    let wrong_length = [3_u8, 2, 0, 0, 0, 0, 0, 0, 0, 0];
    assert!(!anodized::types::Spec::predicate(&Record {
        kind: Kind::Bytes,
        bytes: TokenBody::from(wrong_length.as_slice())
    }));
    let child = *parsed.get(3_usize).expect("the child record");
    for wrong in [
        ContentPtr::new(ChunkDigest::from([0xA4_u8; 32]), pointer.offset()),
        ContentPtr::new(pointer.digest(), TokenOffset::from(0x0403_0201_u32)),
    ] {
        assert!(!anodized::types::Spec::predicate(&Record {
            kind: Kind::Child(wrong),
            ..child
        }));
    }
}

/// Cap transitions and splicing use logical record coordinates, not byte
/// offsets.
#[test]
fn cuts_and_splices_keep_record_coordinates()
{
    let left_body = [1_u8, 0x11, 2, 7, 0, 0, 0, 0, 0, 0, 0, 5];
    let right_body = [1_u8, 0x11, 2, 11, 0, 0, 0, 0, 0, 0, 0, 5];
    let left_chunk = gandr_storage_values::frame_chunk(TokenBody::from(left_body.as_slice()))
        .expect("the left leaf frames");
    let right_chunk = gandr_storage_values::frame_chunk(TokenBody::from(right_body.as_slice()))
        .expect("the right leaf frames");
    let mut listed = Ledger::default();
    listed
        .insert(left_chunk.as_verified())
        .expect("the first leaf stores");
    listed
        .insert(left_chunk.as_verified())
        .expect("repeated insertion succeeds");
    assert_eq!(listed.held(), &BTreeSet::from([left_chunk.digest()]));
    assert!(anodized::types::Spec::predicate(&listed));
    listed.held.clear();
    assert!(!anodized::types::Spec::predicate(&listed));
    let mut wrong_digest = *left_chunk
        .digest()
        .as_ref()
        .first_chunk::<32>()
        .expect("a 32-byte digest");
    *wrong_digest.first_mut().expect("a nonempty digest") ^= 1_u8;
    let _inserted = listed.held.insert(ChunkDigest::from(wrong_digest));
    assert!(!anodized::types::Spec::predicate(&listed));

    let value = crate::common::Fixture(vec![
        crate::common::Node::Pair,
        crate::common::Node::Leaf(gandr_storage_values::CanonicalWord::from(7_u64)),
        crate::common::Node::Leaf(gandr_storage_values::CanonicalWord::from(11_u64)),
    ]);
    let flat = [
        1_u8, 0x12, 1, 0x11, 2, 7, 0, 0, 0, 0, 0, 0, 0, 5, 1, 0x11, 2, 11, 0, 0, 0, 0, 0, 0, 0, 5,
        5,
    ];
    for (kappa, cap, expected) in [
        (1_u64, 64_u64, vec![
            RecordIndex(1_usize),
            RecordIndex(4_usize),
        ]),
        (u64::MAX, 1_u64, vec![
            RecordIndex(1_usize),
            RecordIndex(4_usize),
        ]),
        (u64::MAX, 4_u64, vec![
            RecordIndex(1_usize),
            RecordIndex(4_usize),
        ]),
        (u64::MAX, 5_u64, vec![RecordIndex(4_usize)]),
        (u64::MAX, 8_u64, vec![]),
    ] {
        let params = TypedChunkerParams::new(
            gandr_storage_chunker::Kappa::try_from(kappa).expect("nonzero kappa"),
            gandr_storage_chunker::TokenCap::try_from(cap).expect("a nonzero cap"),
        );
        assert_eq!(
            reference_cuts(TokenBody::from(flat.as_slice()), &params),
            expected
        );
        let profile = gandr_storage_values::ValueProfile::new(
            params,
            gandr_storage_values::CodecIdentity::new(
                gandr_storage_values::CodecId::from(1_u16),
                gandr_storage_values::CodecVersion::from(1_u16),
            ),
            gandr_storage_values::ChildIndexBase::Absolute,
        );
        let mut store = Ledger::default();
        let manifest = gandr_storage_values::cam_commit(&mut store, &profile, &value)
            .expect("the pair commits");
        let spliced = splice(&store, manifest.root());
        assert_eq!(spliced.flat, flat);
        assert_eq!(spliced.chunk_starts, expected);
        assert!(anodized::types::Spec::predicate(&spliced));
        let mut identities = BTreeSet::from([manifest.root().digest()]);
        if expected.contains(&RecordIndex(1_usize)) {
            let _inserted = identities.insert(left_chunk.digest());
        }
        if expected.contains(&RecordIndex(4_usize)) {
            let _inserted = identities.insert(right_chunk.digest());
        }
        assert_eq!(store.held(), &identities);
        assert!(anodized::types::Spec::predicate(&store));
    }
    for starts in [
        vec![RecordIndex(0_usize)],
        vec![RecordIndex(1_usize), RecordIndex(1_usize)],
        vec![RecordIndex(4_usize), RecordIndex(1_usize)],
        vec![RecordIndex(flat.len())],
    ] {
        assert!(!anodized::types::Spec::predicate(&Spliced {
            flat: flat.to_vec(),
            chunk_starts: starts
        }));
    }
    let mut frame = Frame {
        open: RecordIndex(1_usize),
        preimage: RESIDUE_DOMAIN.to_vec(),
    };
    assert!(!anodized::types::Spec::predicate(&frame));
    frame.preimage.extend_from_slice(&[1_u8, 0x11]);
    assert!(anodized::types::Spec::predicate(&frame));
    *frame.preimage.first_mut().expect("a residue domain") ^= 1_u8;
    assert!(!anodized::types::Spec::predicate(&frame));
}
