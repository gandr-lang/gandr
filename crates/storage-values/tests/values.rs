//! The value plane's contract: commit, deref, sharing, seams and locality.

use gandr_storage_values::ChildIndexBase;
use gandr_storage_values::ChunkStore as _;
use gandr_storage_values::ContentPtr;
use gandr_storage_values::EditDepth;
use gandr_storage_values::EmissionFault;
use gandr_storage_values::InMemoryChunkStore;
use gandr_storage_values::SeamDepth;
use gandr_storage_values::TokenBody;
use gandr_storage_values::TokenKind;
use gandr_storage_values::TokenOffset;
use gandr_storage_values::ValueError;
use gandr_storage_values::cam_commit;
use gandr_storage_values::cam_deref;
use gandr_storage_values::encode_flat;
use gandr_storage_values::expected_chunk_bound;
use gandr_storage_values::frame_chunk;
use gandr_storage_values::measure_edit;

use crate::common::Depth;
use crate::common::Embedding;
use crate::common::Fixture;
use crate::common::Inner;
use crate::common::LEAF;
use crate::common::LeafIndex;
use crate::common::Probed;
use crate::common::Scanned;
use crate::common::Script;
use crate::common::Seed;
use crate::common::Step;
use crate::common::balanced;
use crate::common::edit_leaf;
use crate::common::pair;
use crate::common::profile;
use crate::common::scan;

/// A committed value derefs back equal, and the manifest counts the records
/// it emitted.
#[test]
fn a_committed_value_derefs_back_equal()
{
    let value = balanced(Depth(3), Seed(1));
    let mut store = InMemoryChunkStore::new();
    let manifest = cam_commit(&mut store, &profile(ChildIndexBase::Absolute), &value)
        .expect("the fixture commits");

    let back: Fixture = cam_deref(&store, manifest.root()).expect("the root derefs");
    assert_eq!(back, value);

    let flat = encode_flat(&value).expect("the fixture encodes flat");
    assert_eq!(
        u64::from(manifest.token_count()),
        u64::try_from(scan(flat.as_body()).len()).expect("a fixture count"),
        "the manifest counts the value's records, whatever chunks it was cut into"
    );
}

/// The same value commits to the same root in two stores.
#[test]
fn the_same_value_commits_to_the_same_pointer()
{
    let value = balanced(Depth(5), Seed(3));
    let mut left = InMemoryChunkStore::new();
    let mut right = InMemoryChunkStore::new();

    let first = cam_commit(&mut left, &profile(ChildIndexBase::Absolute), &value)
        .expect("the first commit");
    let second = cam_commit(&mut right, &profile(ChildIndexBase::Absolute), &value)
        .expect("the second commit");

    assert_eq!(first, second);
    assert_eq!(left, right, "both stores hold the same chunks");
}

/// Two values sharing a subtree store its chunks once.
#[test]
fn a_shared_subtree_is_stored_once()
{
    let shared = balanced(Depth(6), Seed(7));
    let left = pair(&shared, &balanced(Depth(4), Seed(8)));
    let right = pair(&shared, &balanced(Depth(4), Seed(9)));
    let commit = |store: &mut InMemoryChunkStore, value: &Fixture| {
        cam_commit(store, &profile(ChildIndexBase::Absolute), value).expect("the value commits")
    };

    let mut together = InMemoryChunkStore::new();
    commit(&mut together, &left);
    commit(&mut together, &right);

    let mut alone_left = InMemoryChunkStore::new();
    commit(&mut alone_left, &left);
    let mut alone_right = InMemoryChunkStore::new();
    commit(&mut alone_right, &right);

    let apart = usize::from(alone_left.chunk_count()) + usize::from(alone_right.chunk_count());
    let shared_count = usize::from(together.chunk_count());
    assert!(
        shared_count < apart,
        "one store holding both values holds fewer chunks ({shared_count}) than two holding one each ({apart})"
    );
}

/// A word standing where a constructor tag belongs is refused naming both
/// kinds, even when its leading byte is a valid tag.
#[test]
fn a_word_is_never_read_as_a_tag()
{
    // The word's leading byte — its least significant, little-endian — is the
    // leaf tag, so a reader coercing the record would read a well-formed
    // constructor and fail later, with a truncation, for the wrong reason.
    let mut body = vec![0x02_u8];
    body.extend_from_slice(&u64::from(LEAF).to_le_bytes());
    let chunk = frame_chunk(TokenBody::from(body.as_slice())).expect("the body frames");
    let mut store = InMemoryChunkStore::new();
    store.insert(chunk.as_verified()).expect("the chunk stores");

    let refusal = cam_deref::<Fixture>(&store, ContentPtr::new(chunk.digest(), TokenOffset::ZERO))
        .expect_err("a word is not a tag");
    assert_eq!(refusal, ValueError::UnexpectedToken {
        expected: TokenKind::Open,
        found: TokenKind::Word,
        position: TokenOffset::ZERO,
    });
}

/// A pointer into a chunk derefs to the subtree at its offset, not to the
/// whole value and not to the chunk's start.
#[test]
fn an_interior_pointer_derefs_to_its_own_subtree()
{
    let value = balanced(Depth(6), Seed(3));
    let mut store = InMemoryChunkStore::new();
    let root = cam_commit(&mut store, &profile(ChildIndexBase::Absolute), &value)
        .expect("the fixture commits")
        .root();

    // A child record of the root chunk, followed: a proper subtree.
    let root_body = store
        .load(root.digest())
        .expect("the root chunk is stored")
        .body();
    let children: Vec<ContentPtr> = scan(root_body)
        .into_iter()
        .filter_map(|record| match record {
            | Scanned::Child(pointer) => Some(pointer),
            | Scanned::Open | Scanned::Other => None,
        })
        .collect();
    let first = *children
        .first()
        .expect("the root body carries a child record");
    let subtree: Fixture = cam_deref(&store, first).expect("the child pointer derefs");
    assert!(
        subtree.leaves() < value.leaves(),
        "a child names a proper subtree"
    );

    // A non-zero offset, built by hand because the traversal only ever writes
    // zero: the first cut chunk with an interior constructor, addressed there.
    let (digest, offset) = children
        .iter()
        .find_map(|child| {
            let body = store
                .load(child.digest())
                .expect("the cut chunk is stored")
                .body();
            scan(body)
                .iter()
                .skip(1)
                .position(|record| *record == Scanned::Open)
                .map(|index| (child.digest(), index + 1))
        })
        .expect("some cut chunk holds an interior constructor");
    let offset = TokenOffset::from(u32::try_from(offset).expect("a fixture offset"));

    let addressed: Fixture =
        cam_deref(&store, ContentPtr::new(digest, offset)).expect("the offset derefs");
    let from_start: Fixture = cam_deref(&store, ContentPtr::new(digest, TokenOffset::ZERO))
        .expect("the chunk derefs from its start");
    assert_ne!(
        addressed, from_start,
        "a non-zero offset addresses into the chunk rather than restarting it"
    );
    assert!(addressed.leaves() < from_start.leaves());
}

/// A value larger than one chunk is cut, and reading it back crosses seams.
#[test]
fn a_value_larger_than_one_chunk_is_read_across_seams()
{
    let value = balanced(Depth(7), Seed(3));
    let mut store = InMemoryChunkStore::new();
    let root = cam_commit(&mut store, &profile(ChildIndexBase::Absolute), &value)
        .expect("the deep fixture commits")
        .root();
    assert!(
        usize::from(store.chunk_count()) > 1,
        "the traversal cut at least once"
    );

    let back: Probed = cam_deref(&store, root).expect("the root derefs across seams");
    assert_eq!(
        back.value, value,
        "crossing a seam is invisible to the decoder"
    );
    assert!(
        back.deepest >= SeamDepth::from(2_usize),
        "the reader was inside nested seams, not one chunk: {}",
        back.deepest
    );
}

/// A value embedding a committed pointer reads back with the pointed-to value
/// inline.
#[test]
fn an_embedded_pointer_reads_as_the_value_it_names()
{
    let inner = balanced(Depth(5), Seed(11));
    let mut store = InMemoryChunkStore::new();
    let pointer = cam_commit(&mut store, &profile(ChildIndexBase::Absolute), &inner)
        .expect("the inner value commits")
        .root();

    let outer = Embedding(Inner::Pointer(pointer));
    let root = cam_commit(&mut store, &profile(ChildIndexBase::Absolute), &outer)
        .expect("the embedding commits")
        .root();

    let back: Embedding = cam_deref(&store, root).expect("the embedding derefs");
    assert_eq!(back, Embedding(Inner::Value(inner)));
}

/// An emission that is not one balanced value is refused by name.
#[test]
fn a_malformed_emission_is_refused_by_name()
{
    let cases = [
        (vec![], EmissionFault::EmptyValue),
        (vec![Step::Close], EmissionFault::CloseWithoutOpen),
        (vec![Step::Word], EmissionFault::PayloadOutsideConstructor),
        (
            vec![Step::Open, Step::Close, Step::Open],
            EmissionFault::SecondRoot,
        ),
        (
            vec![Step::Open, Step::Close, Step::Word],
            EmissionFault::PayloadOutsideConstructor,
        ),
        (
            vec![Step::Open, Step::Open, Step::Close],
            EmissionFault::UnclosedConstructor,
        ),
    ];

    for (steps, fault) in cases {
        let script = Script(steps);
        let mut store = InMemoryChunkStore::new();
        assert_eq!(
            cam_commit(&mut store, &profile(ChildIndexBase::Absolute), &script),
            Err(ValueError::MalformedEmission { fault }),
            "the commit refuses {script:?}"
        );
        assert_eq!(
            encode_flat(&script),
            Err(ValueError::MalformedEmission { fault }),
            "the flat encoder refuses {script:?}"
        );
    }
}

/// The mean chunks an edit affects, over every leaf edit of a corpus, sits
/// inside the expected bound for its depth.
#[test]
fn measured_chunk_counts_sit_inside_the_locality_bound()
{
    let profile = profile(ChildIndexBase::Absolute);

    for depth in 2_u32 ..= 8 {
        let value = balanced(Depth(depth), Seed(u64::from(depth)));
        let mut store = InMemoryChunkStore::new();
        let before = cam_commit(&mut store, &profile, &value)
            .expect("the original commits")
            .root();
        let edit_depth = EditDepth::from(u64::from(depth));
        let leaves = value.leaves().0;

        let affected: usize = (0 .. leaves)
            .map(|index| {
                let edited = edit_leaf(&value, LeafIndex(index));
                let after = cam_commit(&mut store, &profile, &edited)
                    .expect("the edit commits")
                    .root();
                let measured =
                    measure_edit(&store, before, after, edit_depth).expect("the edit measures");
                usize::from(measured.chunks_affected)
            })
            .sum();

        let bound = expected_chunk_bound(edit_depth, &profile.params()).expect("the bound fits");
        let ceiling = u64::from(bound) * u64::try_from(leaves).expect("a fixture count");
        let total = u64::try_from(affected).expect("a fixture count");
        assert!(
            total <= ceiling,
            "depth {depth}: mean affected {total}/{leaves} exceeds the bound {bound}"
        );
    }
}

/// A chunk-local base is refused, and the property it was proposed to recover
/// holds by construction: an early edit leaves most chunks shared.
#[test]
fn an_early_edit_moves_only_its_own_chunk_under_chunk_local_bases()
{
    let value = balanced(Depth(7), Seed(3));
    let mut refusing = InMemoryChunkStore::new();
    assert_eq!(
        cam_commit(&mut refusing, &profile(ChildIndexBase::ChunkLocal), &value),
        Err(ValueError::UnsupportedIndexBase {
            base: ChildIndexBase::ChunkLocal,
        })
    );
    assert_eq!(
        usize::from(refusing.chunk_count()),
        0,
        "nothing is written before the refusal"
    );

    let mut store = InMemoryChunkStore::new();
    let before = cam_commit(&mut store, &profile(ChildIndexBase::Absolute), &value)
        .expect("the original commits")
        .root();
    let held = usize::from(store.chunk_count());

    let edited = edit_leaf(&value, LeafIndex(0));
    let after = cam_commit(&mut store, &profile(ChildIndexBase::Absolute), &edited)
        .expect("the edited value commits")
        .root();
    let measured =
        measure_edit(&store, before, after, EditDepth::from(7_u64)).expect("the edit measures");

    assert_eq!(
        usize::from(store.chunk_count()) - held,
        usize::from(measured.chunks_affected),
        "the chunks the edit added are the chunks it affected"
    );
    assert!(
        measured.chunks_affected < measured.chunks_shared,
        "an early edit reuses most chunks: {} affected, {} shared",
        measured.chunks_affected,
        measured.chunks_shared
    );
}
