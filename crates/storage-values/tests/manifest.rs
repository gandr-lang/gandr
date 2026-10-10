//! The value manifest: its pinned image and identity, its binding, its round
//! trip, every refusal of its decoder, and the profile-checked read.

use alloc::collections::BTreeSet;
use core::cell::Cell;

use gandr_storage_chunker::Kappa;
use gandr_storage_chunker::TokenCap;
use gandr_storage_chunker::TokenCount;
use gandr_storage_chunker::TypedChunkerParams;
use gandr_storage_values::ChildIndexBase;
use gandr_storage_values::ChunkDigest;
use gandr_storage_values::ChunkFrameField;
use gandr_storage_values::ChunkImage;
use gandr_storage_values::ChunkStore;
use gandr_storage_values::CodecId;
use gandr_storage_values::CodecIdentity;
use gandr_storage_values::CodecVersion;
use gandr_storage_values::ContentPtr;
use gandr_storage_values::InMemoryChunkStore;
use gandr_storage_values::ManifestDigest;
use gandr_storage_values::ManifestField;
use gandr_storage_values::ManifestImage;
use gandr_storage_values::ProfileField;
use gandr_storage_values::StoredChunkRef;
use gandr_storage_values::TokenBody;
use gandr_storage_values::TokenOffset;
use gandr_storage_values::ValueError;
use gandr_storage_values::ValueManifest;
use gandr_storage_values::ValueProfile;
use gandr_storage_values::VerifiedChunk;
use gandr_storage_values::cam_commit;
use gandr_storage_values::frame_chunk;
use gandr_storage_values::verify_chunk_image;
use proptest::prelude::ProptestConfig;
use proptest::prop_assert_eq;
use proptest::proptest;

use crate::common::Depth;
use crate::common::Fixture;
use crate::common::Seed;
use crate::common::balanced;
use crate::generate::profile;
use crate::generate::tree;

/// The golden manifest: kappa four and cap sixty-four, codec `0x0a0b` at
/// version `0x0c0d`, absolute children, a root at digest bytes `0x00` to
/// `0x1f` and offset `0x01020304`, and forty-two tokens.
///
/// # Specification
/// trivial.
fn golden() -> ValueManifest
{
    let params = TypedChunkerParams::new(
        Kappa::try_from(4_u64).expect("kappa is nonzero"),
        TokenCap::try_from(64_u64).expect("the cap is nonzero"),
    );
    let codec = CodecIdentity::new(CodecId::from(0x0A0B_u16), CodecVersion::from(0x0C0D_u16));
    let digest: [u8; 32] = core::array::from_fn(|index| u8::try_from(index).expect("a byte index"));
    let root = ContentPtr::new(
        ChunkDigest::from(digest),
        TokenOffset::from(0x0102_0304_u32),
    );

    ValueManifest::new(
        ValueProfile::new(params, codec, ChildIndexBase::Absolute),
        root,
        TokenCount::from(42_u64),
    )
}

/// Where each field of the golden image begins, in image order, written out
/// from the documented widths rather than read off the encoder.
const LAYOUT: [(usize, ManifestField); 13] = [
    (0_usize, ManifestField::Domain),
    (32_usize, ManifestField::ManifestVersion),
    (34_usize, ManifestField::CommitmentLength),
    (42_usize, ManifestField::ChunkerCommitment),
    (91_usize, ManifestField::DigestFamily),
    (92_usize, ManifestField::CodecId),
    (94_usize, ManifestField::CodecVersion),
    (96_usize, ManifestField::ChildIndexBase),
    (97_usize, ManifestField::BoundaryClassification),
    (98_usize, ManifestField::ChunkFrameVersion),
    (100_usize, ManifestField::RootDigest),
    (132_usize, ManifestField::RootOffset),
    (136_usize, ManifestField::TokenCount),
];

/// The golden image's length: the token count's eight bytes past its start.
const GOLDEN_LEN: usize = 144_usize;

/// The golden manifest's bytes are a fixed image written out here field by
/// field, and its identity is a digest pasted here once.
///
/// The identity is a literal and never recomputed: recomputing it would be the
/// implementation agreeing with itself.
#[test]
fn the_manifest_bytes_are_pinned()
{
    // BLAKE3 of the hand-built image below, computed by `b3sum` over a file
    // holding exactly those bytes.
    const IDENTITY: [u8; 32] = [
        0xE1, 0xBE, 0x44, 0x59, 0x7E, 0x3C, 0x05, 0x16, 0x16, 0xF2, 0x5B, 0xF4, 0xEB, 0xE5, 0x4F,
        0x6A, 0xE9, 0xA2, 0xC0, 0xC3, 0x25, 0x96, 0xA8, 0x6A, 0xA5, 0x50, 0xE3, 0x79, 0xA9, 0x5B,
        0xFD, 0x72,
    ];

    let manifest = golden();
    let image = manifest.encode();
    let root: Vec<u8> = (0x00_u8 ..= 0x1F_u8).collect();
    let fields: [(&str, &[u8]); 16] = [
        ("domain", b"gandr:storage-values:manifest:v1"),
        ("manifest version", &[0x01, 0x00]),
        ("commitment length", &[0x31, 0, 0, 0, 0, 0, 0, 0]),
        ("commitment domain", b"gandr:storage-chunker:params:v1"),
        ("typed algorithm", &[0x02, 0x00]),
        ("kappa", &[0x04, 0, 0, 0, 0, 0, 0, 0]),
        ("cap", &[0x40, 0, 0, 0, 0, 0, 0, 0]),
        ("digest family", &[0x01]),
        ("codec identifier", &[0x0B, 0x0A]),
        ("codec version", &[0x0D, 0x0C]),
        ("child index base", &[0x01]),
        ("boundary classification", &[0x01]),
        ("chunk frame version", &[0x01, 0x00]),
        ("root digest", root.as_slice()),
        ("root offset", &[0x04, 0x03, 0x02, 0x01]),
        ("token count", &[0x2A, 0, 0, 0, 0, 0, 0, 0]),
    ];

    // Read back field by field, so a disagreement says which field moved.
    let mut rest: &[u8] = image.as_ref();
    for (name, field) in fields {
        let (head, tail) = rest.split_at(field.len());
        assert_eq!(head, field, "the image's {name}");
        rest = tail;
    }
    assert!(rest.is_empty(), "nothing follows the token count");
    assert_eq!(image.as_ref().len(), GOLDEN_LEN, "the layout table's end");

    assert_eq!(
        manifest.identity(),
        ManifestDigest::from(IDENTITY),
        "the image hashes to its golden identity"
    );
    assert_eq!(
        manifest.identity().to_string(),
        "e1be44597e3c051616f25bf4ebe54f6ae9a2c0c32596a86aa550e379a95bfd72",
        "the identity renders as the tool printed it"
    );
    assert_eq!(
        ValueManifest::decode(image.as_image()),
        Ok(manifest),
        "the pinned image decodes to the manifest that wrote it"
    );
}

/// Every bound field with more than one admissible value moves the identity,
/// and no two of the moved identities agree.
#[test]
fn each_manifest_field_moves_the_identity()
{
    let base = golden();
    let profile = *base.profile();
    let params = profile.params();
    let codec = profile.codec();
    let under = |params, codec, index_base| {
        ValueManifest::new(
            ValueProfile::new(params, codec, index_base),
            base.root(),
            base.token_count(),
        )
    };
    let at = |root| ValueManifest::new(profile, root, base.token_count());

    let mut digest: [u8; 32] =
        core::array::from_fn(|index| u8::try_from(index).expect("a byte index"));
    digest[31] ^= 0x01;
    let offset = u32::from(base.root().offset())
        .checked_add(1_u32)
        .expect("the golden offset has a successor");
    let tokens = u64::from(base.token_count())
        .checked_add(1_u64)
        .expect("the golden count has a successor");

    let cases = [
        (
            "kappa, through the chunker commitment",
            under(
                TypedChunkerParams::new(Kappa::try_from(8_u64).expect("nonzero"), params.cap()),
                codec,
                ChildIndexBase::Absolute,
            ),
        ),
        (
            "the cap, through the chunker commitment",
            under(
                TypedChunkerParams::new(
                    params.kappa(),
                    TokenCap::try_from(63_u64).expect("nonzero"),
                ),
                codec,
                ChildIndexBase::Absolute,
            ),
        ),
        (
            "the codec identifier",
            under(
                params,
                CodecIdentity::new(CodecId::from(0x0A0C_u16), codec.version()),
                ChildIndexBase::Absolute,
            ),
        ),
        (
            "the codec version",
            under(
                params,
                CodecIdentity::new(codec.codec(), CodecVersion::from(0x0C0E_u16)),
                ChildIndexBase::Absolute,
            ),
        ),
        (
            "the child index base",
            under(params, codec, ChildIndexBase::ChunkLocal),
        ),
        (
            "the root digest",
            at(ContentPtr::new(
                ChunkDigest::from(digest),
                base.root().offset(),
            )),
        ),
        (
            "the root offset",
            at(ContentPtr::new(
                base.root().digest(),
                TokenOffset::from(offset),
            )),
        ),
        (
            "the token count",
            ValueManifest::new(profile, base.root(), TokenCount::from(tokens)),
        ),
    ];

    let mut identities = BTreeSet::from([base.identity()]);
    for (field, moved) in cases {
        assert_ne!(
            moved.identity(),
            base.identity(),
            "{field} moves the identity"
        );
        assert!(
            identities.insert(moved.identity()),
            "{field} moves the identity somewhere no other field does"
        );
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    /// The manifest of every generated commit under every generated profile
    /// decodes from its image back to itself, re-encodes to the same bytes,
    /// and is named by those bytes' BLAKE3; so does the same manifest naming
    /// chunk-local children, which a commit refuses but an image admits.
    #[test]
    fn a_manifest_round_trips_through_its_bytes(value in tree(), profile in profile()) {
        let mut store = InMemoryChunkStore::new();
        let committed = cam_commit(&mut store, &profile, &value)
            .expect("a generated value commits");
        let chunk_local = ValueManifest::new(
            ValueProfile::new(profile.params(), profile.codec(), ChildIndexBase::ChunkLocal),
            committed.root(),
            committed.token_count(),
        );

        for manifest in [committed, chunk_local] {
            let image = manifest.encode();
            let decoded = ValueManifest::decode(image.as_image());
            prop_assert_eq!(decoded, Ok(manifest));
            prop_assert_eq!(manifest.encode(), image.clone());
            prop_assert_eq!(
                manifest.identity(),
                ManifestDigest::from(*blake3::hash(image.as_ref()).as_bytes())
            );
        }
    }
}

/// A foreign domain, an unknown manifest version, an unassigned value in each
/// tagged field, a commitment this build does not read, a truncation at every
/// prefix length and a trailing byte are each refused by name.
#[test]
fn each_malformed_manifest_is_refused_by_name()
{
    let good: Vec<u8> = golden().encode().as_ref().to_vec();
    assert_eq!(good.len(), GOLDEN_LEN, "the golden image's length");
    let decode = |image: &[u8]| ValueManifest::decode(ManifestImage::from(image));
    let malformed = |field| Err(ValueError::MalformedManifest { field });
    let with = |at: usize, byte: u8| {
        let mut image = good.clone();
        image[at] = byte;
        image
    };
    let with_word = |at: usize, word: u64| {
        let mut image = good.clone();
        let end = at.checked_add(8).expect("a field inside the image");
        image[at .. end].copy_from_slice(&word.to_le_bytes());
        image
    };
    let trailing = {
        let mut image = good.clone();
        image.push(0x00);
        image
    };

    let cases = [
        (with(0, b'G'), malformed(ManifestField::Domain)),
        (with(31, b'2'), malformed(ManifestField::Domain)),
        (with(32, 0x00), malformed(ManifestField::ManifestVersion)),
        (with(32, 0x02), malformed(ManifestField::ManifestVersion)),
        (
            with_word(34, u64::MAX),
            Err(ValueError::TruncatedManifest {
                field: ManifestField::ChunkerCommitment,
            }),
        ),
        // One byte short and one long: the cap is cut, or the digest family
        // joins the commitment.
        (
            with_word(34, 48),
            malformed(ManifestField::ChunkerCommitment),
        ),
        (
            with_word(34, 50),
            malformed(ManifestField::ChunkerCommitment),
        ),
        (with(42, b'G'), malformed(ManifestField::ChunkerCommitment)),
        // The record-safe algorithm's discriminator, then a zero kappa and a
        // zero cap.
        (with(73, 0x01), malformed(ManifestField::ChunkerCommitment)),
        (
            with_word(75, 0),
            malformed(ManifestField::ChunkerCommitment),
        ),
        (
            with_word(83, 0),
            malformed(ManifestField::ChunkerCommitment),
        ),
        (with(91, 0x00), malformed(ManifestField::DigestFamily)),
        (with(91, 0x02), malformed(ManifestField::DigestFamily)),
        (with(96, 0x00), malformed(ManifestField::ChildIndexBase)),
        (with(96, 0x03), malformed(ManifestField::ChildIndexBase)),
        (
            with(97, 0x00),
            malformed(ManifestField::BoundaryClassification),
        ),
        (
            with(97, 0x02),
            malformed(ManifestField::BoundaryClassification),
        ),
        (with(98, 0x00), malformed(ManifestField::ChunkFrameVersion)),
        (with(98, 0x02), malformed(ManifestField::ChunkFrameVersion)),
        (trailing, Err(ValueError::TrailingManifestBytes)),
    ];
    for (image, refusal) in cases {
        assert_eq!(decode(&image), refusal, "the image {image:02x?}");
    }

    for length in 0 .. GOLDEN_LEN {
        let field = LAYOUT
            .iter()
            .rev()
            .find_map(|&(start, field)| (start <= length).then_some(field))
            .expect("every prefix length lies in some field");
        assert_eq!(
            decode(&good[.. length]),
            Err(ValueError::TruncatedManifest { field }),
            "a prefix of {length} bytes ends inside {field}"
        );
    }
}

/// A manifest image, offered as a chunk under its own BLAKE3, is refused for
/// its domain, and a chunk image is refused as a manifest for its domain.
///
/// The manifest image passes the chunk verifier's digest check and fails
/// every later frame field too, so only a refusal naming the domain separates
/// a verifier that keeps the two byte languages apart from one that does not.
#[test]
fn a_manifest_image_is_refused_as_a_chunk()
{
    let manifest = golden();
    let image = manifest.encode();
    let claimed = ChunkDigest::from(*blake3::hash(image.as_ref()).as_bytes());
    assert_eq!(
        claimed.as_ref(),
        manifest.identity().as_ref(),
        "the identity is the image's own BLAKE3, so the digest check passes"
    );
    assert_eq!(
        verify_chunk_image(StoredChunkRef::new(
            claimed,
            ChunkImage::from(image.as_ref())
        )),
        Err(ValueError::MalformedChunk {
            field: ChunkFrameField::Domain,
        })
    );

    let body: [u8; 12] = [
        0x01, 0x2A, 0x02, 0x07, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x05,
    ];
    let chunk = frame_chunk(TokenBody::from(body.as_slice())).expect("the body frames");
    assert_eq!(
        ValueManifest::decode(ManifestImage::from(chunk.image().as_ref())),
        Err(ValueError::MalformedManifest {
            field: ManifestField::Domain,
        })
    );
}

/// A number of loads a store has answered.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
struct LoadCount(usize);

/// An in-memory chunk store that counts the loads asked of it.
#[derive(Debug, Default)]
struct Counted
{
    /// The chunks.
    store: InMemoryChunkStore,
    /// The loads asked so far, answered or not.
    loads: Cell<LoadCount>,
}

impl Counted
{
    /// Returns the loads asked so far.
    ///
    /// # Specification
    /// trivial.
    fn loads(&self) -> LoadCount
    {
        self.loads.get()
    }
}

impl ChunkStore for Counted
{
    /// Inserts into the in-memory store.
    ///
    /// # Specification
    /// trivial.
    fn insert(
        &mut self,
        chunk: VerifiedChunk<'_>,
    ) -> Result<(), ValueError>
    {
        self.store.insert(chunk)
    }

    /// Counts the load, then loads from the in-memory store.
    ///
    /// # Specification
    /// - requires: one more request fits the load counter.
    /// - ensures: increments the counter exactly once on success or refusal; a
    ///   successful load retains the requested authenticated digest.
    /// - fails: propagates the backing store's named refusal unchanged.
    /// - panics: when the request counter is exhausted.
    ///
    /// # Adequacy
    /// - hypothesis: L3 observes missing and successful loads and the final
    ///   representable increment; profile mismatch cases make no request.
    /// - witness: `tests::manifest::load_counts_include_refusals_and_successes`
    /// - witness: `tests::manifest::a_profile_mismatch_is_refused_before_any_chunk_is_read`
    #[anodized::spec(requires: self.loads.get().0 < usize::MAX,
        captures: before = self.loads.get().0,
        ensures: |ret| self.loads.get().0.checked_sub(before) == Some(1_usize)
            && ret.as_ref().ok().is_none_or(|chunk| chunk.digest() == digest))]
    fn load(
        &self,
        digest: ChunkDigest,
    ) -> Result<VerifiedChunk<'_>, ValueError>
    {
        let LoadCount(loads) = self.loads.get();
        self.loads
            .set(LoadCount(loads.checked_add(1).expect("a load count")));

        self.store.load(digest)
    }
}

/// The profile the read tests commit under, with its chunking constants and
/// codec as arguments.
///
/// # Specification
/// trivial.
fn committed_under(
    kappa: Kappa,
    cap: TokenCap,
    codec: CodecIdentity,
    index_base: ChildIndexBase,
) -> ValueProfile
{
    ValueProfile::new(TypedChunkerParams::new(kappa, cap), codec, index_base)
}

/// A reader expecting another profile is refused naming the first field that
/// differs, and the store is never asked for a chunk.
#[test]
fn a_profile_mismatch_is_refused_before_any_chunk_is_read()
{
    let kappa = Kappa::try_from(4_u64).expect("kappa is nonzero");
    let cap = TokenCap::try_from(64_u64).expect("the cap is nonzero");
    let codec = CodecIdentity::new(CodecId::from(1_u16), CodecVersion::from(1_u16));
    let committed = committed_under(kappa, cap, codec, ChildIndexBase::Absolute);
    let mut store = Counted::default();
    let manifest = cam_commit(&mut store, &committed, &balanced(Depth(4), Seed(5)))
        .expect("the fixture commits");
    assert_eq!(store.loads(), LoadCount(0), "a commit loads nothing");

    let other_codec = CodecIdentity::new(CodecId::from(2_u16), CodecVersion::from(1_u16));
    let other_version = CodecIdentity::new(CodecId::from(1_u16), CodecVersion::from(2_u16));
    let cases = [
        (
            committed_under(
                Kappa::try_from(8_u64).expect("nonzero"),
                cap,
                codec,
                ChildIndexBase::Absolute,
            ),
            ProfileField::ChunkerCommitment,
        ),
        (
            committed_under(
                kappa,
                TokenCap::try_from(63_u64).expect("nonzero"),
                codec,
                ChildIndexBase::Absolute,
            ),
            ProfileField::ChunkerCommitment,
        ),
        (
            committed_under(kappa, cap, other_codec, ChildIndexBase::Absolute),
            ProfileField::CodecId,
        ),
        (
            committed_under(kappa, cap, other_version, ChildIndexBase::Absolute),
            ProfileField::CodecVersion,
        ),
        (
            committed_under(kappa, cap, codec, ChildIndexBase::ChunkLocal),
            ProfileField::ChildIndexBase,
        ),
        // Two fields differ; the earlier in image order is named.
        (
            committed_under(kappa, cap, other_version, ChildIndexBase::ChunkLocal),
            ProfileField::CodecVersion,
        ),
    ];

    for (expected, field) in cases {
        assert_eq!(
            manifest.read_under::<Fixture>(&store, &expected),
            Err(ValueError::IncompatibleProfile { field }),
            "a reader expecting another {field} is refused by name"
        );
        assert_eq!(
            store.loads(),
            LoadCount(0),
            "refusing {field} asked the store for nothing"
        );
    }
}

/// A reader expecting the committed profile reads the committed value back,
/// from the manifest a commit returned and from its decoded image alike.
#[test]
fn a_matching_profile_reads_the_committed_value()
{
    let codec = CodecIdentity::new(CodecId::from(1_u16), CodecVersion::from(1_u16));
    let committed = committed_under(
        Kappa::try_from(4_u64).expect("kappa is nonzero"),
        TokenCap::try_from(64_u64).expect("the cap is nonzero"),
        codec,
        ChildIndexBase::Absolute,
    );
    let value = balanced(Depth(4), Seed(5));
    let mut store = Counted::default();
    let manifest = cam_commit(&mut store, &committed, &value).expect("the fixture commits");

    let back: Fixture = manifest
        .read_under(&store, &committed)
        .expect("the matching profile reads");
    assert_eq!(back, value);

    let decoded =
        ValueManifest::decode(manifest.encode().as_image()).expect("the manifest's image decodes");
    let again: Fixture = decoded
        .read_under(&store, &committed)
        .expect("the decoded manifest reads under the same profile");
    assert_eq!(again, value);
}

/// Failed requests count too, including the last representable counter step.
#[test]
fn load_counts_include_refusals_and_successes()
{
    let mut store = Counted::default();
    let missing = ChunkDigest::from([0xA5_u8; 32_usize]);
    assert_eq!(
        store.load(missing),
        Err(ValueError::UnknownChunk { digest: missing })
    );
    assert_eq!(store.loads(), LoadCount(1_usize));
    let body: [u8; 12] = [0x01, 0x2A, 0x02, 0x07, 0, 0, 0, 0, 0, 0, 0, 0x05];
    let frame = frame_chunk(TokenBody::from(body.as_slice())).expect("the body frames");
    store
        .insert(frame.as_verified())
        .expect("the frame inserts");
    let loaded = store.load(frame.digest()).expect("the held frame loads");
    assert_eq!(loaded.body().as_ref(), body.as_slice());
    assert_eq!(store.loads(), LoadCount(2_usize));
    store.loads.set(LoadCount(
        usize::MAX
            .checked_sub(1_usize)
            .expect("the final counter step"),
    ));
    assert_eq!(
        store.load(missing),
        Err(ValueError::UnknownChunk { digest: missing })
    );
    assert_eq!(store.loads(), LoadCount(usize::MAX));
}
