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
/// - hypothesis: L3 — the decision surfaces are a frame and the next one across
///   a written stream, a close at a boundary and inside a frame, a header block
///   without a length, with a non-decimal length and past the ceiling, each
///   separated by its exact body, absence or fault.
/// - witness: `transport::tests::a_round_trip_preserves_the_payload`
/// - witness: `transport::tests::eof_at_a_boundary_is_clean`
/// - witness: `transport::tests::a_header_block_the_framing_cannot_read_is_refused`
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
///   back exactly the body written.
/// - fails: [`TransportFault::Io`] for a failed write or flush.
/// - panics: none.
///
/// # Errors
/// [`TransportFault::Io`] as above.
///
/// # Adequacy
/// - hypothesis: L3 — two frames written to one stream are read back body for
///   body, the second starting where the first ends.
/// - witness: `transport::tests::a_round_trip_preserves_the_payload`
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
    use std::io::BufRead;

    use quenchant_shape::shape::Maybe;

    use super::Body;
    use super::TransportFault;
    use super::read_frame;
    use super::write_frame;

    /// The outcome of one read from `stream`, with its fault flattened to its
    /// debug form so it compares.
    ///
    /// # Specification
    /// trivial.
    fn read<Input>(stream: &mut Input) -> Result<Maybe<Body, super::read_frame::Absent>, String>
    where
        Input: BufRead,
    {
        read_frame(stream).map_err(|fault| format!("{fault:?}"))
    }

    #[test]
    fn a_round_trip_preserves_the_payload()
    {
        let first = Body::from(br#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#.to_vec());
        let second = Body::from("{\"text\":\"é😀\"}".as_bytes().to_vec());
        let mut written = Vec::new();
        write_frame(&mut written, &first).expect("a vector takes every write");
        write_frame(&mut written, &second).expect("a vector takes every write");
        let written = Body::from(written);
        let mut stream = written.as_ref();
        assert_eq!(
            read(&mut stream),
            Ok(Maybe::Present(first)),
            "the first body"
        );
        assert_eq!(
            read(&mut stream),
            Ok(Maybe::Present(second)),
            "the second body starts where the first ends, its length in bytes"
        );
        assert_eq!(
            read(&mut stream),
            Ok(Maybe::Absent(super::read_frame::Absent::Closed)),
            "then the stream is closed"
        );
    }

    #[test]
    fn eof_at_a_boundary_is_clean()
    {
        let mut empty: &[u8] = &[];
        assert_eq!(
            read(&mut empty),
            Ok(Maybe::Absent(super::read_frame::Absent::Closed)),
            "an empty stream closes at a boundary"
        );
        for cut in [
            b"Content-Length: 5\r\n".to_vec(),
            b"Content-Length: 5\r\n\r\nab".to_vec(),
            b"Content-Len".to_vec(),
        ] {
            let mut stream = cut.as_slice();
            assert_eq!(
                read(&mut stream),
                Err(format!("{:?}", TransportFault::Truncated)),
                "a stream cut inside a frame is truncated: {cut:?}"
            );
        }
    }

    #[test]
    fn a_header_block_the_framing_cannot_read_is_refused()
    {
        let cases: [(&[u8], TransportFault); 5] = [
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
            (&[b'x'; 1_024], TransportFault::LongHeader),
        ];
        for (bytes, fault) in cases {
            let mut stream = bytes;
            assert_eq!(
                read(&mut stream),
                Err(format!("{fault:?}")),
                "the header block is refused as {fault}"
            );
        }
        let mut lower: &[u8] = b"content-length: 2\n\n{}";
        assert_eq!(
            read(&mut lower),
            Ok(Maybe::Present(Body::from(b"{}".to_vec()))),
            "the name is matched case-insensitively and a bare newline ends a line"
        );
    }
}
