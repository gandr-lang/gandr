//! The flat form: its round trip, its identity with a single chunk's body, and
//! its refusals.

use gandr_storage_values::ChildIndexBase;
use gandr_storage_values::ChunkStore as _;
use gandr_storage_values::ContentPtr;
use gandr_storage_values::InMemoryChunkStore;
use gandr_storage_values::TokenBody;
use gandr_storage_values::TokenOffset;
use gandr_storage_values::ValueError;
use gandr_storage_values::cam_commit;
use gandr_storage_values::cam_deref;
use gandr_storage_values::decode_flat;
use gandr_storage_values::encode_flat;

use crate::common::Depth;
use crate::common::Embedding;
use crate::common::Fixture;
use crate::common::Inner;
use crate::common::PAIR;
use crate::common::Seed;
use crate::common::balanced;
use crate::common::profile;
use crate::common::scan;

/// Encoding then decoding a flat form is the identity.
#[test]
fn a_flat_form_round_trips()
{
    for depth in [0_u32, 1, 3, 7] {
        let value = balanced(Depth(depth), Seed(5));
        let flat = encode_flat(&value).expect("the fixture encodes");
        let back: Fixture = decode_flat(flat.as_body()).expect("the flat form decodes");
        assert_eq!(back, value, "depth {depth}");
    }
}

/// For a value that fits one chunk, the flat bytes are that chunk's body; for
/// one that is cut, the flat form still decodes to what the chunk DAG derefs
/// to.
#[test]
fn flat_bytes_equal_the_single_chunk_body()
{
    let small = balanced(Depth(1), Seed(5));
    let mut store = InMemoryChunkStore::new();
    let root = cam_commit(&mut store, &profile(ChildIndexBase::Absolute), &small)
        .expect("the small value commits")
        .root();
    assert_eq!(
        usize::from(store.chunk_count()),
        1,
        "the small value fits one chunk"
    );

    let flat = encode_flat(&small).expect("the small value encodes");
    let chunk = store
        .load(root.digest())
        .expect("the single chunk is stored");
    assert_eq!(
        flat.as_body(),
        chunk.body(),
        "the flat bytes are the chunk's body"
    );

    let large = balanced(Depth(7), Seed(5));
    let mut store = InMemoryChunkStore::new();
    let root = cam_commit(&mut store, &profile(ChildIndexBase::Absolute), &large)
        .expect("the large value commits")
        .root();
    assert!(
        usize::from(store.chunk_count()) > 1,
        "the large value is cut"
    );
    let flat = encode_flat(&large).expect("the large value encodes");
    let flat_value: Fixture = decode_flat(flat.as_body()).expect("the flat form decodes");
    let dag_value: Fixture = cam_deref(&store, root).expect("the chunk DAG derefs");
    assert_eq!(flat_value, dag_value);
}

/// A flat form that ends inside its value is refused as truncated.
#[test]
fn a_truncated_flat_form_is_refused()
{
    let flat = encode_flat(&balanced(Depth(2), Seed(5))).expect("the fixture encodes");
    let bytes: &[u8] = flat.as_ref();
    let records = u32::try_from(scan(flat.as_body()).len()).expect("a fixture count");

    // Without its final close record, one byte, the body ends after whole
    // records with the value still open.
    let short = bytes.split_last().expect("a non-empty form").1;
    assert_eq!(
        decode_flat::<Fixture>(TokenBody::from(short)),
        Err(ValueError::TruncatedStream {
            position: TokenOffset::from(records - 1),
        })
    );

    // Inside a record: two pair opens, a leaf open, then the first word record
    // loses its last byte.
    let word_end = 2 + 2 + 2 + 9;
    let inside = bytes.get(.. word_end - 1).expect("a prefix");
    assert_eq!(
        decode_flat::<Fixture>(TokenBody::from(inside)),
        Err(ValueError::TruncatedStream {
            position: TokenOffset::from(3_u32),
        })
    );
}

/// A flat form that continues past its value is refused naming where the
/// value ended.
#[test]
fn a_flat_form_with_trailing_tokens_is_refused()
{
    let flat = encode_flat(&balanced(Depth(2), Seed(5))).expect("the fixture encodes");
    let records = u32::try_from(scan(flat.as_body()).len()).expect("a fixture count");
    let mut trailing = flat.as_ref().to_vec();
    trailing.push(0x05);

    assert_eq!(
        decode_flat::<Fixture>(TokenBody::from(trailing.as_slice())),
        Err(ValueError::TrailingTokens {
            position: TokenOffset::from(records),
        })
    );
}

/// A flat form carries no child record: the encoder refuses to write one and
/// the decoder refuses to read one.
#[test]
fn a_child_record_is_refused_in_a_flat_form()
{
    let pointer = ContentPtr::new([0x5A_u8; 32].into(), TokenOffset::ZERO);
    assert_eq!(
        encode_flat(&Embedding(Inner::Pointer(pointer))),
        Err(ValueError::SeamInFlatForm {
            position: TokenOffset::from(1_u32),
        })
    );

    let mut body = vec![0x01_u8, PAIR, 0x04];
    body.extend_from_slice(&[0x5A_u8; 32]);
    body.extend_from_slice(&0_u32.to_le_bytes());
    body.push(0x05);
    assert_eq!(
        decode_flat::<Fixture>(TokenBody::from(body.as_slice())),
        Err(ValueError::SeamInFlatForm {
            position: TokenOffset::from(1_u32),
        })
    );
}
