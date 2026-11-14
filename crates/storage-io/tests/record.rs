//! The record's header: it names its own place, and a read checks that
//! place before the bytes become a value, under both forms of the `Io`.

use std::collections::HashMap;

use gandr_storage_io::Buffer;
use gandr_storage_io::Chain;
use gandr_storage_io::Count;
use gandr_storage_io::Done;
use gandr_storage_io::Errno;
use gandr_storage_io::Handle;
use gandr_storage_io::Header;
use gandr_storage_io::Moved;
use gandr_storage_io::Pending;
use gandr_storage_io::Place;
use gandr_storage_io::Position;
use gandr_storage_io::RecordDigest;
use gandr_storage_io::RecordLength;
use gandr_storage_io::Segment;
use gandr_storage_io::SegmentId;
use gandr_storage_io::Shard;

use crate::common::BLOCK;
use crate::common::Scratch;
use crate::common::completions;
use crate::common::forms;

/// The place of shard 3, segment 9, at `offset`.
///
/// # Specification
/// trivial.
fn place(offset: Position) -> Place
{
    Place {
        shard: Shard::from(3_u64),
        segment: SegmentId::from(9_u64),
        offset,
    }
}

/// The header of one block's record at `at`.
///
/// # Specification
/// trivial.
fn header(at: Place) -> Header
{
    Header {
        place: at,
        length: RecordLength::from(4_096_u64),
        digest: RecordDigest::from([0x3c_u8; 32]),
    }
}

/// The record that `header` heads: its header, then one block of `0x5a`.
///
/// # Specification
/// trivial.
fn record(header: &Header) -> Buffer
{
    let mut bytes = Vec::from(Buffer::from(header));
    bytes.extend_from_slice(&[0x5a_u8; BLOCK]);
    Buffer::from(bytes)
}

/// The count of bytes in a record of one block.
///
/// # Specification
/// trivial.
fn record_length() -> Moved
{
    Moved::from(u32::from(Header::size()).saturating_add(4_096))
}

/// An encoded header takes `Header::size` bytes, and reads back as itself
/// at its own place. At a place of another shard, segment or offset, it is
/// refused as corrupt.
#[test]
fn a_header_reads_back_only_at_its_own_place()
{
    let at = place(Position::from(8_192_u64));
    let encoded = Buffer::from(&header(at));
    assert_eq!(encoded.length(), Header::size(), "a header takes its size");
    assert_eq!(
        encoded.header(at),
        Ok(header(at)),
        "a header reads back at its own place"
    );
    let others = [
        Place {
            shard: Shard::from(4_u64),
            ..at
        },
        Place {
            segment: SegmentId::from(10_u64),
            ..at
        },
        place(Position::from(0_u64)),
    ];
    for other in others {
        assert_eq!(
            encoded.header(other),
            Err(Errno::CORRUPT),
            "a header is refused at {other:?}"
        );
    }
}

/// A change of any one byte of a header fails its checksum, and so does a
/// buffer shorter than a header.
#[test]
fn a_changed_byte_fails_the_checksum()
{
    let at = place(Position::from(0_u64));
    let encoded = Vec::from(Buffer::from(&header(at)));
    for changed in 0 .. encoded.len() {
        let mut bytes = encoded.clone();
        if let Some(byte) = bytes.get_mut(changed) {
            *byte ^= 0x01;
        }
        assert_eq!(
            Buffer::from(bytes).header(at),
            Err(Errno::CORRUPT),
            "a header with byte {changed} changed is refused"
        );
    }
    let mut short = encoded;
    short.pop();
    assert_eq!(
        Buffer::from(short).header(at),
        Err(Errno::CORRUPT),
        "a short header is refused"
    );
}

/// A read of a record at the place that its header names completes with
/// the record's bytes, under each form.
#[test]
fn a_read_of_the_expected_place_passes()
{
    for mut io in forms(Count::from(8_u32)) {
        let form = io.form();
        let scratch = Scratch::new();
        let handle = Handle::from(scratch.open());
        let mut segment = Segment::new(handle.clone(), Position::from(0_u64));
        let at = place(Position::from(0_u64));
        let write = io
            .append(&mut segment, record(&header(at)), Chain::Linked)
            .expect("the record's append stages");
        let read = io
            .read_record(&handle, at, Buffer::from(vec![0_u8; 4_176]), Chain::Alone)
            .expect("the read stages");
        let done = completions(&mut io);
        let wrote = done
            .iter()
            .find(|each| each.pending == write)
            .expect("the append completes");
        assert_eq!(
            wrote.outcome,
            Ok(record_length()),
            "the append writes the record under {form:?}"
        );
        let back = done
            .into_iter()
            .find(|each| each.pending == read)
            .expect("the read completes");
        assert_eq!(
            back.outcome,
            Ok(record_length()),
            "the read takes the record under {form:?}"
        );
        assert_eq!(
            back.buffer,
            Some(record(&header(at))),
            "the read holds the record under {form:?}"
        );
    }
}

/// A record whose header names another place reads as corrupt: a record
/// written at the wrong offset, a read that expects another segment, and a
/// read past the end of the file. Each read gives its buffer back.
#[test]
fn a_misdirected_record_reads_corrupt()
{
    for mut io in forms(Count::from(8_u32)) {
        let form = io.form();
        let scratch = Scratch::new();
        let handle = Handle::from(scratch.open());
        let mut segment = Segment::new(handle.clone(), Position::from(0_u64));
        let first = place(Position::from(0_u64));
        let writes = [
            io.append(&mut segment, record(&header(first)), Chain::Linked)
                .expect("the first record's append stages"),
            io.append(&mut segment, record(&header(first)), Chain::Linked)
                .expect("the misdirected record's append stages"),
        ];
        let second = place(Position::from(4_176_u64));
        let expected = [
            second,
            Place {
                segment: SegmentId::from(10_u64),
                ..first
            },
            place(Position::from(8_352_u64)),
        ];
        let reads: Vec<_> = expected
            .iter()
            .map(|at| {
                io.read_record(&handle, *at, Buffer::from(vec![0_u8; 4_176]), Chain::Alone)
                    .expect("the read stages")
            })
            .collect();
        let done: HashMap<Pending, Done> = completions(&mut io)
            .into_iter()
            .map(|each| (each.pending, each))
            .collect();
        for write in writes {
            let wrote = done.get(&write).expect("the append completes");
            assert_eq!(
                wrote.outcome,
                Ok(record_length()),
                "each append writes a record under {form:?}"
            );
        }
        for (read, at) in reads.iter().zip(expected) {
            let back = done.get(read).expect("the read completes");
            assert_eq!(
                back.outcome,
                Err(Errno::CORRUPT),
                "a read expecting {at:?} is corrupt under {form:?}"
            );
            assert!(
                back.buffer.is_some(),
                "a corrupt read gives its buffer back under {form:?}"
            );
        }
    }
}
