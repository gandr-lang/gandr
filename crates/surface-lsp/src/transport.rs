//! The base protocol's framing: a header block naming the body's length, an
//! empty line, then exactly that many bytes of body.
//!
//! A header line ends at `\r\n`; a bare `\n` is read as the same terminator,
//! since nothing else in the block can carry one. `Content-Length` is matched
//! case-insensitively and is required; every other header, `Content-Type`
//! included, is read and ignored, as the protocol admits only UTF-8 JSON.

use core::fmt;
use std::io;
use std::io::BufRead;
use std::io::Read as _;
use std::io::Write;

use anodized::spec;
use quenchant_shape::shape::Maybe;

/// The most bytes one body may hold.
///
/// economy: 64 MiB. The ceiling bounds the buffer a broken or hostile length
/// would allocate before a byte of the body arrives; a source file past it is
/// not a document an editor sends whole on every change.
const BODY_CEILING: usize = 0x0400_0000;

/// The most bytes one header line may hold, its terminator included.
///
/// economy: 1 KiB. The protocol defines two headers, each a short name and a
/// short value; the ceiling bounds the buffer a line with no terminator fills.
const HEADER_CEILING: usize = 1_024;

/// The one header the framing reads, compared case-insensitively.
const CONTENT_LENGTH: &str = "content-length";

quenchant_shape::reason_enum! {
    /// Why no frame was read.
    pub mod read_frame {
        /// The reason the stream yields no further frame.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The stream ended at a frame boundary: the client closed it.
            Closed,
        }
    }
}

/// One message body: the bytes a frame carries after its header block.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Body(Vec<u8>);

impl From<Vec<u8>> for Body
{
    /// Read the bytes as a body.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: Vec<u8>) -> Self
    {
        Self(bytes)
    }
}

impl AsRef<[u8]> for Body
{
    /// The body's bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        &self.0
    }
}

/// Why the transport could not carry a frame.
#[derive(Debug)]
pub enum TransportFault
{
    /// Reading or writing the stream failed.
    Io(io::Error),
    /// The stream ended inside a frame: in its header block or its body.
    Truncated,
    /// A header line is not `name: value` in UTF-8.
    MalformedHeader,
    /// A header line ran past the header ceiling without a terminator.
    LongHeader,
    /// The header block named no `Content-Length`.
    MissingLength,
    /// The `Content-Length` value is not a decimal count of bytes.
    MalformedLength,
    /// The `Content-Length` value is past the body ceiling.
    Oversized,
    /// A message could not be encoded as JSON.
    Encode(serde_json::Error),
}

impl fmt::Display for TransportFault
{
    /// Writes what failed, and the underlying error where there is one.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            | Self::Io(ref error) => write!(f, "the stream failed: {error}"),
            | Self::Truncated => f.write_str("the stream ended inside a frame"),
            | Self::MalformedHeader => f.write_str("a header line is not `name: value` in UTF-8"),
            | Self::LongHeader => {
                write!(f, "a header line runs past {HEADER_CEILING} bytes")
            },
            | Self::MissingLength => f.write_str("a header block names no Content-Length"),
            | Self::MalformedLength => {
                f.write_str("a Content-Length value is not a decimal count of bytes")
            },
            | Self::Oversized => {
                write!(f, "a Content-Length value is past {BODY_CEILING} bytes")
            },
            | Self::Encode(ref error) => write!(f, "a message could not be encoded: {error}"),
        }
    }
}

impl core::error::Error for TransportFault
{
    /// The stream's or the encoder's own error, where the fault carries one.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn source(&self) -> Option<&(dyn core::error::Error + 'static)>
    {
        match *self {
            | Self::Io(ref error) => Some(error),
            | Self::Encode(ref error) => Some(error),
            | Self::Truncated
            | Self::MalformedHeader
            | Self::LongHeader
            | Self::MissingLength
            | Self::MalformedLength
            | Self::Oversized => None,
        }
    }
}

/// Read the next frame's body from `input`.
///
/// # Specification
/// - requires: nothing; any byte stream is admissible input.
/// - ensures: the body is exactly the `Content-Length` bytes after the header
///   block's empty line, and `input` is left at the first byte of the next
///   frame. A stream that ends before a frame's first byte is
///   [`read_frame::Absent::Closed`].
/// - provides: the one reader of the client's stream.
/// - fails: [`TransportFault::Io`] for a failed read;
///   [`TransportFault::Truncated`] for a stream ending inside a frame;
///   [`TransportFault::MalformedHeader`], [`TransportFault::LongHeader`],
///   [`TransportFault::MissingLength`], [`TransportFault::MalformedLength`] and
///   [`TransportFault::Oversized`] for a header block the framing cannot read.
///   No fault resynchronises: a stream that lost its framing has no boundary
///   left to find.
/// - panics: none.
/// - intension: the header block is read a bounded line at a time; the body is
///   allocated only once its length is under the ceiling.
///
/// # Errors
/// Each [`TransportFault`] but [`TransportFault::Encode`], as above.
///
/// # Adequacy
/// - hypothesis: L3 — empty and consecutive frames, closed and cut streams,
///   malformed and boundary-sized headers, body lengths at and above the
///   ceiling, and injected I/O failures distinguish boundary shifts and
///   misclassified errors through exact bodies, leftovers and fault kinds.
/// - witness: `transport::tests::a_round_trip_preserves_the_payload`
/// - witness: `transport::tests::eof_at_a_boundary_is_clean`
/// - witness: `transport::tests::a_header_block_the_framing_cannot_read_is_refused`
/// - witness: `transport::tests::framing_limits_and_empty_bodies_have_exact_boundaries`
/// - witness: `transport::tests::stream_failures_keep_their_kind_and_write_progress`
#[spec(ensures: |ret| match ret {
    Ok(Maybe::Present(ref body)) => body.as_ref().len() <= BODY_CEILING,
    Err(TransportFault::Encode(_)) => false,
    _ => true,
})]
#[inline]
pub fn read_frame<Input>(
    input: &mut Input
) -> Result<Maybe<Body, read_frame::Absent>, TransportFault>
where
    Input: BufRead,
{
    let mut length = None;
    let mut line = Vec::new();
    let mut at_boundary = true;
    loop {
        line.clear();
        let ceiling = u64::try_from(HEADER_CEILING).unwrap_or(u64::MAX);
        let read = input
            .by_ref()
            .take(ceiling)
            .read_until(b'\n', &mut line)
            .map_err(TransportFault::Io)?;
        if read == 0 {
            return if at_boundary {
                Ok(Maybe::Absent(read_frame::Absent::Closed))
            }
            else {
                Err(TransportFault::Truncated)
            };
        }
        at_boundary = false;
        let Some(content) = line.strip_suffix(b"\n")
        else {
            return Err(if line.len() >= HEADER_CEILING {
                TransportFault::LongHeader
            }
            else {
                TransportFault::Truncated
            });
        };
        let content = content.strip_suffix(b"\r").unwrap_or(content);
        if content.is_empty() {
            break;
        }
        let header =
            core::str::from_utf8(content).map_err(|_not_utf8| TransportFault::MalformedHeader)?;
        let Some((name, value)) = header.split_once(':')
        else {
            return Err(TransportFault::MalformedHeader);
        };
        if name.trim().eq_ignore_ascii_case(CONTENT_LENGTH) {
            let parsed = value
                .trim()
                .parse::<usize>()
                .map_err(|_not_decimal| TransportFault::MalformedLength)?;
            length = Some(parsed);
        }
    }
    let Some(length) = length
    else {
        return Err(TransportFault::MissingLength);
    };
    if length > BODY_CEILING {
        return Err(TransportFault::Oversized);
    }
    let mut body = vec![0_u8; length];
    input.read_exact(&mut body).map_err(|error| {
        if error.kind() == io::ErrorKind::UnexpectedEof {
            TransportFault::Truncated
        }
        else {
            TransportFault::Io(error)
        }
    })?;

    Ok(Maybe::Present(Body(body)))
}

/// Write `body` to `output` as one frame, and flush it.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `output` receives `Content-Length: n\r\n\r\n` and the `n` bytes
///   of `body`, then is flushed, so the client reads the frame without waiting
///   on a buffer.
/// - provides: the one writer of the server's stream; [`read_frame()`] reads
///   back bodies no larger than its incoming-body ceiling.
/// - fails: [`TransportFault::Io`] for a failed write or flush.
/// - panics: none.
///
/// # Errors
/// [`TransportFault::Io`] as above.
///
/// # Adequacy
/// - hypothesis: L3 — a two-byte non-ASCII body has a pinned byte-counted
///   frame; failures before the header, after it, inside the body and at flush
///   distinguish wrong lengths, dropped bytes, omitted flushes and swallowed
///   errors by exact wire bytes, flush counts and fault kinds.
/// - witness: `transport::tests::a_round_trip_preserves_the_payload`
/// - witness: `transport::tests::stream_failures_keep_their_kind_and_write_progress`
#[spec(ensures: |ret| matches!(ret, Ok(()) | Err(TransportFault::Io(_))))]
#[inline]
pub fn write_frame<Output>(
    output: &mut Output,
    body: &Body,
) -> Result<(), TransportFault>
where
    Output: Write,
{
    write!(output, "Content-Length: {}\r\n\r\n", body.0.len()).map_err(TransportFault::Io)?;
    output.write_all(&body.0).map_err(TransportFault::Io)?;
    output.flush().map_err(TransportFault::Io)?;

    Ok(())
}

#[cfg(test)]
mod tests
{
    use std::io;
    use std::io::Read as _;

    use anodized::spec;
    use quenchant_shape::shape::Maybe;

    use super::Body;
    use super::TransportFault;
    use super::read_frame;
    use super::write_frame;

    /// A stream whose next read fails with a connection reset.
    struct Reset;

    impl io::Read for Reset
    {
        /// Refuse the read with the stream's connection-reset error.
        ///
        /// # Specification
        /// - requires: nothing.
        /// - ensures: no bytes are accepted.
        /// - provides: a failed underlying read at either framing stage.
        /// - fails: a connection-reset I/O error on every call.
        /// - panics: none.
        ///
        /// # Errors
        /// Returns `io::ErrorKind::ConnectionReset`.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — header and body read failures retain their exact
        ///   connection-reset kind rather than becoming truncation or success.
        /// - witness: `transport::tests::stream_failures_keep_their_kind_and_write_progress`
        #[spec(ensures: |ret| matches!(ret, Err(ref error)
            if error.kind() == io::ErrorKind::ConnectionReset))]
        fn read(
            &mut self,
            _buffer: &mut [u8],
        ) -> io::Result<usize>
        {
            Err(io::ErrorKind::ConnectionReset.into())
        }
    }

    /// A writer exposing accepted bytes and flushes, with bounded failures.
    struct Probe
    {
        /// Bytes accepted before a failure.
        bytes: Vec<u8>,
        /// Maximum accepted bytes before the stream breaks.
        limit: usize,
        /// Whether flushing fails after recording the flush.
        fail_flush: bool,
        /// Number of flush attempts.
        flushes: usize,
    }

    impl io::Write for Probe
    {
        /// Accept the prefix fitting the limit, or report a broken stream.
        ///
        /// # Specification
        /// - requires: nothing.
        /// - ensures: successful writes append exactly the accepted prefix; a
        ///   full writer retains its bytes unchanged.
        /// - provides: partial writes at either header or body boundaries.
        /// - fails: a broken-pipe error when no capacity remains.
        /// - panics: none.
        ///
        /// # Errors
        /// Returns `io::ErrorKind::BrokenPipe` at the limit.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — zero, header-complete, partial-body and unbounded
        ///   capacities distinguish dropped prefixes, over-acceptance and lost
        ///   write errors through exact bytes and error kinds.
        /// - witness: `transport::tests::stream_failures_keep_their_kind_and_write_progress`
        #[spec(
            captures: before = self.bytes.len(),
            ensures: |ret| match ret {
                Ok(count) => count == self.limit.saturating_sub(before).min(buf.len())
                    && self.bytes.get(before..) == buf.get(..count),
                Err(ref error) => self.limit <= before && self.bytes.len() == before
                    && error.kind() == io::ErrorKind::BrokenPipe,
            },
        )]
        fn write(
            &mut self,
            buf: &[u8],
        ) -> io::Result<usize>
        {
            let available = self.limit.saturating_sub(self.bytes.len());
            if available == 0 {
                return Err(io::ErrorKind::BrokenPipe.into());
            }
            let count = available.min(buf.len());
            self.bytes.extend_from_slice(&buf[.. count]);
            Ok(count)
        }

        /// Record the flush and report its configured outcome.
        ///
        /// # Specification
        /// - requires: nothing.
        /// - ensures: one flush attempt is recorded, saturating at
        ///   `usize::MAX`.
        /// - provides: observation of the frame's final flush.
        /// - fails: permission denied exactly when `fail_flush` is set.
        /// - panics: none.
        ///
        /// # Errors
        /// Returns `io::ErrorKind::PermissionDenied` when configured.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — successful and failed final flushes distinguish
        ///   missing flushes and ignored errors by count and exact error kind.
        /// - witness: `transport::tests::stream_failures_keep_their_kind_and_write_progress`
        #[spec(
            captures: before = self.flushes,
            ensures: |ret| self.flushes == before.saturating_add(1_usize)
                && match ret {
                    Ok(()) => !self.fail_flush,
                    Err(ref error) => self.fail_flush
                        && error.kind() == io::ErrorKind::PermissionDenied,
                },
        )]
        fn flush(&mut self) -> io::Result<()>
        {
            self.flushes = self.flushes.saturating_add(1_usize);
            if self.fail_flush {
                Err(io::ErrorKind::PermissionDenied.into())
            }
            else {
                Ok(())
            }
        }
    }

    #[test]
    fn a_round_trip_preserves_the_payload()
    {
        let first = Body::from(br#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#.to_vec());
        let second = Body::from("{\"text\":\"é😀\"}".as_bytes().to_vec());
        let mut written = Vec::new();
        write_frame(&mut written, &first).expect("a vector takes every write");
        write_frame(&mut written, &second).expect("a vector takes every write");
        let mut stream = written.as_slice();
        assert_eq!(
            read_frame(&mut stream).expect("first frame"),
            Maybe::Present(first)
        );
        assert_eq!(
            read_frame(&mut stream).expect("second frame"),
            Maybe::Present(second)
        );
        assert_eq!(
            read_frame(&mut stream).expect("frame boundary"),
            Maybe::Absent(super::read_frame::Absent::Closed)
        );
    }

    #[test]
    fn eof_at_a_boundary_is_clean()
    {
        let mut empty: &[u8] = &[];
        assert_eq!(
            read_frame(&mut empty).expect("empty stream"),
            Maybe::Absent(super::read_frame::Absent::Closed)
        );
        for cut in [
            b"Content-Length: 5\r\n".as_slice(),
            b"Content-Length: 5\r\n\r\nab".as_slice(),
            b"Content-Len".as_slice(),
        ] {
            let mut stream = cut;
            assert!(matches!(
                read_frame(&mut stream),
                Err(TransportFault::Truncated)
            ));
        }
    }

    #[test]
    fn a_header_block_the_framing_cannot_read_is_refused()
    {
        let cases: [(&[u8], TransportFault); 6] = [
            (b"Content-Type: x\r\n\r\n{}", TransportFault::MissingLength),
            (
                b"Content-Length: two\r\n\r\n{}",
                TransportFault::MalformedLength,
            ),
            (
                b"Content-Length: 67108865\r\n\r\n",
                TransportFault::Oversized,
            ),
            (b"no colon here\r\n\r\n", TransportFault::MalformedHeader),
            (b"\xff: x\r\n\r\n", TransportFault::MalformedHeader),
            (&[b'x'; 1_024], TransportFault::LongHeader),
        ];
        for (bytes, expected) in cases {
            let mut stream = bytes;
            let actual = read_frame(&mut stream).expect_err("invalid frame");
            assert_eq!(
                core::mem::discriminant(&actual),
                core::mem::discriminant(&expected)
            );
        }
        let mut lower: &[u8] = b"content-length: 2\n\n{}";
        assert_eq!(
            read_frame(&mut lower).expect("lowercase header"),
            Maybe::Present(Body::from(b"{}".to_vec()))
        );
    }

    #[test]
    fn framing_limits_and_empty_bodies_have_exact_boundaries()
    {
        let mut empty: &[u8] = b"Content-Length: 0\r\n\r\nnext";
        assert_eq!(
            read_frame(&mut empty).expect("empty body"),
            Maybe::Present(Body::default())
        );
        assert_eq!(empty, b"next");
        let mut exact: &[u8] = b"Content-Length: 67108864\r\n\r\n";
        assert!(matches!(
            read_frame(&mut exact),
            Err(TransportFault::Truncated)
        ));
        let mut header = vec![b'x'; super::HEADER_CEILING];
        header[0] = b':';
        header[super::HEADER_CEILING.saturating_sub(1)] = b'\n';
        header.push(b'\n');
        assert!(matches!(
            read_frame(&mut header.as_slice()),
            Err(TransportFault::MissingLength)
        ));
        header[super::HEADER_CEILING.saturating_sub(1)] = b'x';
        assert!(matches!(
            read_frame(&mut header.as_slice()),
            Err(TransportFault::LongHeader)
        ));
    }

    #[test]
    fn stream_failures_keep_their_kind_and_write_progress()
    {
        for prefix in [b"".as_slice(), b"Content-Length: 1\r\n\r\n".as_slice()] {
            let mut input = io::BufReader::new(io::Cursor::new(prefix).chain(Reset));
            assert!(
                matches!(read_frame(&mut input), Err(TransportFault::Io(ref error))
                if error.kind() == io::ErrorKind::ConnectionReset)
            );
        }
        let body = Body::from("é".as_bytes().to_vec());
        let golden = b"Content-Length: 2\r\n\r\n\xc3\xa9";
        for limit in [0_usize, 21, 22, usize::MAX] {
            let mut output = Probe {
                bytes: Vec::new(),
                limit,
                fail_flush: false,
                flushes: 0,
            };
            let result = write_frame(&mut output, &body);
            if limit == usize::MAX {
                assert!(result.is_ok());
                assert_eq!(output.bytes, golden);
                assert_eq!(output.flushes, 1_usize);
            }
            else {
                assert!(matches!(result, Err(TransportFault::Io(ref error))
                    if error.kind() == io::ErrorKind::BrokenPipe));
                assert_eq!(output.bytes, golden[.. limit]);
                assert_eq!(output.flushes, 0_usize);
            }
        }
        let mut output = Probe {
            bytes: Vec::new(),
            limit: usize::MAX,
            fail_flush: true,
            flushes: 0,
        };
        assert!(
            matches!(write_frame(&mut output, &body), Err(TransportFault::Io(ref error))
            if error.kind() == io::ErrorKind::PermissionDenied)
        );
        assert_eq!(output.bytes, golden);
        assert_eq!(output.flushes, 1_usize);
    }
}
