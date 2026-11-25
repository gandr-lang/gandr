//! The write against each subject: the bytes of a write at the other end of a
//! socket, a short write to a socket that cannot take each byte at once, an
//! empty range, and a closed descriptor. A socket of the host's `std` is the
//! other end, and the oracle of the bytes.

use core::num::NonZeroU16;
use std::io::ErrorKind;
use std::io::Read as _;
use std::os::fd::AsRawFd as _;
use std::os::fd::IntoRawFd as _;
use std::os::unix::net::UnixStream;

use gandr_boot_core::Length;
use gandr_boot_core::Range;
use gandr_boot_io::Descriptor;
use gandr_boot_io::ErrorNumber;
use gandr_boot_io::Operation;

use crate::harness::SUBJECTS;
use crate::harness::started;

/// The error number of a descriptor that the process does not hold.
const EBADF: ErrorNumber = ErrorNumber(NonZeroU16::new(9).expect("9 is not zero"));

/// The bytes of a write that a socket of the host takes at once.
const SMALL: usize = 1000;

/// The bytes of a write that no socket of the host takes at once: a socket of
/// Linux holds some hundreds of kibibytes by default.
const LARGE: usize = 16 << 20;

/// `length` bytes that differ from their neighbours, so a moved byte shows.
///
/// # Specification
/// trivial.
fn bytes(length: usize) -> Vec<u8>
{
    (0_u8 ..= 250).cycle().take(length).collect()
}

/// A write that a socket takes at once gives the count of each byte, and the
/// other end reads the same bytes.
#[test]
fn a_write_gives_each_byte_to_the_other_end()
{
    let sent = bytes(SMALL);
    for subject in &SUBJECTS {
        let name = subject.name;
        let (writer, mut reader) = UnixStream::pair().expect("the host makes a socket pair");
        let io = started(subject);
        // SAFETY: the range is a live vector, and nothing writes it during the
        // call.
        let count = unsafe {
            (subject.write)(
                &io,
                Descriptor(writer.as_raw_fd()),
                Range::from(sent.as_slice()),
            )
        };
        assert_eq!(Ok(Length(SMALL)), count, "{name}: the count of the write");
        let mut received = vec![0_u8; SMALL];
        reader
            .read_exact(&mut received)
            .expect("the other end reads the bytes of the write");
        assert_eq!(sent, received, "{name}: the bytes at the other end");
        assert_eq!(Ok(()), (subject.stop)(io), "{name}: stop");
    }
}

/// A socket that does not wait and cannot take each byte at once takes the
/// first bytes alone. The count is above 0 and below the length, the other end
/// reads those first bytes, and no byte after them.
#[test]
fn a_full_socket_takes_a_short_write_of_the_first_bytes()
{
    let sent = bytes(LARGE);
    for subject in &SUBJECTS {
        let name = subject.name;
        let (writer, mut reader) = UnixStream::pair().expect("the host makes a socket pair");
        writer
            .set_nonblocking(true)
            .expect("the host makes the socket not wait");
        let io = started(subject);
        // SAFETY: the range is a live vector, and nothing writes it during the
        // call.
        let count = unsafe {
            (subject.write)(
                &io,
                Descriptor(writer.as_raw_fd()),
                Range::from(sent.as_slice()),
            )
        }
        .unwrap_or_else(|refused| panic!("{name}: write: {refused}"));
        assert!(
            count.0 > 0 && count.0 < LARGE,
            "{name}: a short count, not {}",
            count.0
        );
        let mut received = vec![0_u8; count.0];
        reader
            .read_exact(&mut received)
            .expect("the other end reads the bytes of the count");
        assert_eq!(
            sent.get(.. count.0),
            Some(received.as_slice()),
            "{name}: the first bytes at the other end"
        );
        reader
            .set_nonblocking(true)
            .expect("the host makes the other end not wait");
        let after = reader.read(&mut [0_u8; 1]).map_err(|error| error.kind());
        assert_eq!(
            Err(ErrorKind::WouldBlock),
            after,
            "{name}: no byte after the count"
        );
        assert_eq!(Ok(()), (subject.stop)(io), "{name}: stop");
    }
}

/// A write of an empty range gives the count 0, and the other end reads no
/// byte. After the close, a write of an empty range is refused under the name
/// `write` with `EBADF`, so the call reaches the kernel also for an empty
/// range.
#[test]
fn a_write_of_an_empty_range_gives_zero_and_gives_no_byte()
{
    for subject in &SUBJECTS {
        let name = subject.name;
        let (writer, mut reader) = UnixStream::pair().expect("the host makes a socket pair");
        let io = started(subject);
        let descriptor = Descriptor(writer.into_raw_fd());
        let empty: [u8; 0] = [];
        // SAFETY: the range is empty, so the kernel reads no byte of it.
        let count = unsafe { (subject.write)(&io, descriptor, Range::from(empty.as_slice())) };
        assert_eq!(Ok(Length(0)), count, "{name}: the write of an empty range");
        reader
            .set_nonblocking(true)
            .expect("the host makes the other end not wait");
        let after = reader.read(&mut [0_u8; 1]).map_err(|error| error.kind());
        assert_eq!(
            Err(ErrorKind::WouldBlock),
            after,
            "{name}: no byte at the other end"
        );
        assert_eq!(Ok(()), (subject.close)(&io, descriptor), "{name}: close");
        // SAFETY: the range is empty, so the kernel reads no byte of it.
        let closed = unsafe { (subject.write)(&io, descriptor, Range::from(empty.as_slice())) };
        assert_eq!(
            Err((Operation::Write, EBADF)),
            closed.map_err(|refused| (refused.operation(), refused.number())),
            "{name}: the write of an empty range to a closed descriptor"
        );
        assert_eq!(Ok(()), (subject.stop)(io), "{name}: stop");
    }
}

/// A write to a descriptor after its close is refused under the name `write`,
/// with the error number `EBADF`.
#[test]
fn a_write_to_a_closed_descriptor_is_refused_with_ebadf()
{
    let sent = bytes(SMALL);
    for subject in &SUBJECTS {
        let name = subject.name;
        let (writer, _reader) = UnixStream::pair().expect("the host makes a socket pair");
        let io = started(subject);
        let descriptor = Descriptor(writer.into_raw_fd());
        assert_eq!(Ok(()), (subject.close)(&io, descriptor), "{name}: close");
        // SAFETY: the range is a live vector, and nothing writes it during the
        // call.
        let write = unsafe { (subject.write)(&io, descriptor, Range::from(sent.as_slice())) };
        assert_eq!(
            Err((Operation::Write, EBADF)),
            write.map_err(|refused| (refused.operation(), refused.number())),
            "{name}: write"
        );
        assert_eq!(Ok(()), (subject.stop)(io), "{name}: stop");
    }
}
