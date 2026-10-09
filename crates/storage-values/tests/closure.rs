//! The closure walk: every chunk a commit wrote, a missing descendant refused
//! by name, and a token count the chunks do not deliver refused.

use gandr_storage_chunker::Kappa;
use gandr_storage_chunker::TokenCap;
use gandr_storage_chunker::TokenCount;
use gandr_storage_values::ChunkDigest;
use gandr_storage_values::ChunkStore;
use gandr_storage_values::CodecId;
use gandr_storage_values::CodecIdentity;
use gandr_storage_values::CodecVersion;
use gandr_storage_values::ContentPtr;
use gandr_storage_values::InMemoryChunkStore;
use gandr_storage_values::ValueError;
use gandr_storage_values::ValueManifest;
use gandr_storage_values::ValueProfile;
use gandr_storage_values::cam_commit;
use proptest::prelude::ProptestConfig;
use proptest::prop_assert_eq;
use proptest::proptest;

use crate::common::Depth;
use crate::common::Embedding;
use crate::common::Inner;
use crate::common::Scanned;
use crate::common::Seed;
use crate::common::balanced;
use crate::common::scan;
use crate::generate::profile;
use crate::generate::profile_of;
use crate::generate::tree;
use crate::reference::Ledger;

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    /// The closure of a value committed into an empty store is exactly the
    /// set of digests that store holds; and once a value embedding the first
    /// one's root is committed beside it, that value's closure is the store's
    /// whole set, its token count the embedded value's plus its own two.
    #[test]
    fn the_closure_is_every_chunk_the_commit_wrote(value in tree(), profile in profile()) {
        let mut store = Ledger::default();
        let manifest = cam_commit(&mut store, &profile, &value)
            .expect("a generated value commits");
        let closure = manifest.closure(&store).expect("the closure is complete");
        prop_assert_eq!(closure.digests(), store.held());

        let embedding = cam_commit(&mut store, &profile, &Embedding(Inner::Pointer(manifest.root())))
            .expect("the embedding commits");
        let closure = embedding.closure(&store).expect("the embedding's closure is complete");
        prop_assert_eq!(closure.digests(), store.held());
        prop_assert_eq!(
            u64::from(embedding.token_count()),
            u64::from(manifest.token_count())
                .checked_add(2_u64)
                .expect("a generated count")
        );
    }
}

/// The profile the fixed witnesses commit under, at the given kappa.
///
/// # Specification
/// trivial.
fn fixed(kappa: Kappa) -> ValueProfile
{
    let codec = CodecIdentity::new(CodecId::from(1_u16), CodecVersion::from(1_u16));

    profile_of(
        kappa,
        TokenCap::try_from(64_u64).expect("the cap is nonzero"),
        codec,
    )
}

/// Every child pointer in the body of the chunk `digest` names.
///
/// # Specification
/// trivial.
fn children(
    store: &dyn ChunkStore,
    digest: ChunkDigest,
) -> Vec<ContentPtr>
{
    let body = store.load(digest).expect("the chunk is stored").body();

    scan(body)
        .into_iter()
        .filter_map(|record| match record {
            | Scanned::Child(pointer) => Some(pointer),
            | Scanned::Open | Scanned::Other => None,
        })
        .collect()
}

/// A store holding every chunk a commit wrote but one two seams below the
/// root refuses the closure naming that chunk, and refuses a commit that
/// embeds the value the same way.
#[test]
fn a_missing_descendant_fails_the_closure_by_name()
{
    // At kappa one every constructor below the root is its own chunk, so a
    // depth-four fixture has chunks two seams down.
    let profile = fixed(Kappa::try_from(1_u64).expect("kappa is nonzero"));
    let mut ledger = Ledger::default();
    let manifest = cam_commit(&mut ledger, &profile, &balanced(Depth(4), Seed(9)))
        .expect("the fixture commits");

    let below_root = children(&ledger, manifest.root().digest());
    let child = below_root.first().expect("the root chunk names a child");
    let missing = children(&ledger, child.digest())
        .first()
        .expect("the child chunk names a grandchild")
        .digest();
    assert!(
        below_root.iter().all(|pointer| pointer.digest() != missing),
        "the missing chunk is reachable only through its parent"
    );

    let mut partial = InMemoryChunkStore::new();
    for &digest in ledger.held() {
        if digest != missing {
            let chunk = ledger.load(digest).expect("the chunk is stored");
            partial.insert(chunk).expect("the chunk copies");
        }
    }
    assert_eq!(
        usize::from(partial.chunk_count()).checked_add(1),
        Some(ledger.held().len()),
        "the partial store lacks one chunk"
    );

    assert_eq!(
        manifest.closure(&partial),
        Err(ValueError::UnknownChunk { digest: missing })
    );
    assert_eq!(
        cam_commit(
            &mut partial,
            &profile,
            &Embedding(Inner::Pointer(manifest.root()))
        ),
        Err(ValueError::UnknownChunk { digest: missing }),
        "a commit embedding the value walks its closure and refuses the same chunk"
    );
}

/// A manifest declaring one token more than its chunks deliver is refused
/// with both counts, and so is one declaring one fewer.
#[test]
fn a_manifest_overstating_its_tokens_fails_the_closure()
{
    let mut store = InMemoryChunkStore::new();
    let manifest = cam_commit(
        &mut store,
        &fixed(Kappa::try_from(4_u64).expect("kappa is nonzero")),
        &balanced(Depth(5), Seed(2)),
    )
    .expect("the fixture commits");
    let spliced = manifest.token_count();
    let declaring = |count: u64| {
        ValueManifest::new(
            *manifest.profile(),
            manifest.root(),
            TokenCount::from(count),
        )
    };

    let over = u64::from(spliced)
        .checked_add(1_u64)
        .expect("a fixture count");
    assert_eq!(
        declaring(over).closure(&store),
        Err(ValueError::TokenCountMismatch {
            declared: TokenCount::from(over),
            spliced,
        })
    );

    let under = u64::from(spliced)
        .checked_sub(1_u64)
        .expect("a fixture count");
    assert_eq!(
        declaring(under).closure(&store),
        Err(ValueError::TokenCountMismatch {
            declared: TokenCount::from(under),
            spliced,
        }),
        "the count is checked for equality, not as a ceiling"
    );
}
