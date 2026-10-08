//! The chunk frame: its golden digest, its domain, and every field's refusal.

use gandr_storage_records::RecordRef;
use gandr_storage_records::encode_leaf;
use gandr_storage_values::CHUNK_DOMAIN;
use gandr_storage_values::ChunkDigest;
use gandr_storage_values::ChunkFrameField;
use gandr_storage_values::ChunkImage;
use gandr_storage_values::StoredChunkRef;
use gandr_storage_values::TokenBody;
use gandr_storage_values::ValueError;
use gandr_storage_values::frame_chunk;
use gandr_storage_values::verify_chunk_image;

/// The digest of a fixed body's frame matches a golden pasted here once.
///
/// The golden is a literal and never recomputed: recomputing it would be the
/// implementation agreeing with itself. A digest path that encoded an integer
/// at the target's endianness or pointer width would pass on the machine that
/// minted it and fail on another.
#[test]
fn a_chunk_digest_matches_its_committed_golden()
{
    // Re-derived for the domain `gandr:storage-values:chunk:v1` and
    // little-endian fields, and checked against an independent BLAKE3 tool
    // over the hand-built image.
    const GOLDEN: [u8; 32] = [
        0xA4, 0x81, 0xE4, 0x96, 0xB6, 0x98, 0x5D, 0x1E, 0x82, 0x29, 0xDC, 0x91, 0xC5, 0xFA, 0xD1,
        0x53, 0xB7, 0x5D, 0x7E, 0x57, 0xF8, 0x9F, 0xC2, 0xE7, 0x77, 0xE5, 0xA8, 0xCD, 0x37, 0x42,
        0xC2, 0xC3,
    ];

    // One open record with tag 0x2a, one word record carrying 7, one close
    // record: three records, twelve bytes.
    let body: [u8; 12] = [
        0x01, 0x2A, 0x02, 0x07, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x05,
    ];
    let chunk = frame_chunk(TokenBody::from(body.as_slice())).expect("a twelve-byte body frames");

    // The frame, read back field by field, so a disagreement says which moved.
    let image: &[u8] = chunk.image().into();
    let (domain, header) = image.split_at(CHUNK_DOMAIN.len());
    assert_eq!(
        domain, CHUNK_DOMAIN,
        "the image opens with the chunk domain"
    );
    assert_eq!(
        header,
        [
            [0x01, 0x00].as_slice(),
            [0x03, 0, 0, 0, 0, 0, 0, 0].as_slice(),
            [0x0C, 0, 0, 0, 0, 0, 0, 0].as_slice(),
            body.as_slice(),
        ]
        .concat(),
        "version one, three records, twelve bytes, then the body, little-endian"
    );

    assert_eq!(
        chunk.digest(),
        ChunkDigest::from(GOLDEN),
        "the frame hashes to its golden"
    );

    verify_chunk_image(StoredChunkRef::new(chunk.digest(), chunk.image()))
        .expect("the framed image verifies against its own digest");
}

/// A record plane node image, offered under its own BLAKE3, is refused for
/// its domain.
///
/// Every node image also fails later fields, so a refusal that named any of
/// them would hold even for a verifier with no domain separation at all;
/// naming the domain is what separates.
#[test]
fn a_record_plane_node_image_is_refused_as_a_chunk()
{
    let key = 0_u64.to_le_bytes();
    let value = [1_u8, 2, 3];
    let node =
        encode_leaf(&[RecordRef::new(key.as_slice(), value.as_slice())]).expect("the leaf encodes");
    let bytes: &[u8] = node.as_borrowed().into();

    let claimed = ChunkDigest::from(*blake3::hash(bytes).as_bytes());
    assert_eq!(
        verify_chunk_image(StoredChunkRef::new(claimed, ChunkImage::from(bytes))),
        Err(ValueError::MalformedChunk {
            field: ChunkFrameField::Domain,
        })
    );
}

/// Each frame field, wrong alone, is refused by name, and a wrong digest
/// before any of them.
#[test]
fn each_frame_field_is_refused_by_name()
{
    let body: [u8; 12] = [
        0x01, 0x2A, 0x02, 0x07, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x05,
    ];
    let good = frame_chunk(TokenBody::from(body.as_slice())).expect("the body frames");
    let good: Vec<u8> = <&[u8]>::from(good.image()).to_vec();
    let at = CHUNK_DOMAIN.len();

    let mut domain = good.clone();
    domain[0] ^= 0x20;
    let header = good[.. at + 5].to_vec();
    let mut version = good.clone();
    version[at] = 0x02;
    let mut count = good.clone();
    count[at + 2] = 0x04;
    let mut length = good.clone();
    length[at + 10] = 0x0D;
    let mut records = good.clone();
    let last = records.len() - 1;
    records[last] = 0x06;

    let cases = [
        (domain, ChunkFrameField::Domain),
        (header, ChunkFrameField::Header),
        (version, ChunkFrameField::Version),
        (count, ChunkFrameField::TokenCount),
        (length, ChunkFrameField::BodyLength),
        (records, ChunkFrameField::Records),
    ];
    for (image, field) in cases {
        let claimed = ChunkDigest::from(*blake3::hash(&image).as_bytes());
        assert_eq!(
            verify_chunk_image(StoredChunkRef::new(
                claimed,
                ChunkImage::from(image.as_slice())
            )),
            Err(ValueError::MalformedChunk { field }),
        );
    }

    let wrong = ChunkDigest::from([0_u8; 32]);
    let actual = ChunkDigest::from(*blake3::hash(&good).as_bytes());
    assert_eq!(
        verify_chunk_image(StoredChunkRef::new(
            wrong,
            ChunkImage::from(good.as_slice())
        )),
        Err(ValueError::DigestMismatch {
            expected: wrong,
            actual
        }),
    );
}

/// A body that is not well-formed records is never framed.
#[test]
fn a_malformed_body_is_never_framed()
{
    for body in [
        [0x06_u8].as_slice(),
        [0x02_u8, 1, 2].as_slice(),
        [0x01_u8].as_slice(),
    ] {
        assert_eq!(
            frame_chunk(TokenBody::from(body)),
            Err(ValueError::MalformedChunk {
                field: ChunkFrameField::Records,
            }),
            "the body {body:02x?} is refused"
        );
    }
}
