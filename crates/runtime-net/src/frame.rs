//! The framing every wire carries: a part is a little-endian `u32` length,
//! then that many bytes, at most [`MAX_FRAME`]. A frame a stream carries opens
//! with the same [`Prefix`], and the chunk wire's requests and answers and the
//! world wire's configurations and answers are each parts one after another:
//!
//! ```text
//! part(bytes) := u32le length || bytes, at most MAX_FRAME bytes
//! ```
//!
//! # Boundaries
//!
//! - **Bytes, not meaning.** A part is bytes; what they mean is the wire's that
//!   reads them.
//! - **A bad prefix ends the reading.** [`Parts`] yields [`Malformed`] once for
//!   bytes that do not frame, and nothing after.

use anodized::spec;
use gandr_storage_values::ManifestImage;

use crate::endpoint::Fault;

/// The longest frame, in bytes, either end sends or accepts: 16 MiB.
pub const MAX_FRAME: u32 = 0x0100_0000;

/// The bytes of a length prefix.
pub const PREFIX: usize = 4_usize;

/// The length a frame or a part opens with, at most [`MAX_FRAME`]: on the
/// wire, [`PREFIX`] little-endian bytes.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(transparent)]
pub struct Prefix(u32);

impl TryFrom<usize> for Prefix
{
    type Error = Oversized;

    /// The prefix of `length` bytes.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success, the prefix's length is `length`.
    /// - fails: [`Oversized`] for a length past [`MAX_FRAME`].
    /// - panics: none.
    ///
    /// # Errors
    /// [`Oversized`], carrying `length`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a frame or a part of at most [`MAX_FRAME`] bytes is
    ///   sent whole, and a longer frame is refused before any byte is sent.
    /// - witness: `tests::endpoint::two_endpoints_exchange_frames_on_loopback`
    /// - witness: `tests::endpoint::an_oversized_frame_and_an_unknown_stream_are_refused`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&prefix| usize::from(prefix) == length))]
    fn try_from(length: usize) -> Result<Self, Oversized>
    {
        u32::try_from(length)
            .ok()
            .filter(|&length| length <= MAX_FRAME)
            .map(Self)
            .ok_or_else(|| Oversized(u64::try_from(length).unwrap_or(u64::MAX)))
    }
}

impl TryFrom<[u8; PREFIX]> for Prefix
{
    type Error = Oversized;

    /// The prefix `bytes` announce.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success, the prefix's bytes are `bytes`.
    /// - fails: [`Oversized`] for a length announced past [`MAX_FRAME`].
    /// - panics: none.
    ///
    /// # Errors
    /// [`Oversized`], carrying the length announced.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a part announced at [`MAX_FRAME`] bytes is read, and
    ///   one announced past it does not frame.
    /// - witness: `tests::chunks::a_part_announced_past_the_frame_limit_does_not_frame`
    /// - witness: `tests::endpoint::two_endpoints_exchange_frames_on_loopback`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&prefix| <[u8; PREFIX]>::from(prefix) == bytes))]
    fn try_from(bytes: [u8; PREFIX]) -> Result<Self, Oversized>
    {
        let length = u32::from_le_bytes(bytes);
        if length > MAX_FRAME {
            return Err(Oversized(u64::from(length)));
        }
        Ok(Self(length))
    }
}

impl From<Prefix> for [u8; PREFIX]
{
    /// The prefix's bytes on the wire.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(Prefix(length): Prefix) -> Self
    {
        length.to_le_bytes()
    }
}

impl From<Prefix> for usize
{
    /// The length the prefix announces.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(Prefix(length): Prefix) -> Self
    {
        // `MAX_FRAME` fits every supported target's `usize`.
        Self::try_from(length).unwrap_or(Self::MAX)
    }
}

/// A frame or a part longer than [`MAX_FRAME`], by its length in bytes.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(transparent)]
pub struct Oversized(u64);

impl From<Oversized> for Fault
{
    /// The endpoint's refusal of an oversized frame.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(Oversized(length): Oversized) -> Self
    {
        Self::Oversized { length }
    }
}

/// Parts one after another, each a little-endian `u32` length, then that many
/// bytes, at most [`MAX_FRAME`].
#[derive(Clone, Debug, Default, Eq, PartialEq)]
#[repr(transparent)]
pub struct Framed(Vec<u8>);

impl Framed
{
    /// Append one part, `pieces` one after another, its length first.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success, the bytes grew by the prefix and the pieces; on
    ///   failure, they are unchanged.
    /// - fails: [`Oversized`] for pieces longer than [`MAX_FRAME`] together.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Oversized`], carrying the part's length.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every part a request and an answer carry reads back
    ///   whole at the other end.
    /// - witness: `tests::chunks::a_second_fetch_carries_only_the_chunks_an_edit_changed`
    #[spec(captures: before = self.0.len(), ensures: |ret| ret.is_ok() || self.0.len() == before)]
    pub(super) fn push(
        &mut self,
        pieces: &[Part<'_>],
    ) -> Result<(), Oversized>
    {
        let length = pieces
            .iter()
            .fold(0_usize, |sum, piece| sum.saturating_add(piece.0.len()));
        let prefix = Prefix::try_from(length)?;
        self.0.reserve(length.saturating_add(PREFIX));
        self.0.extend_from_slice(&<[u8; PREFIX]>::from(prefix));
        for piece in pieces {
            self.0.extend_from_slice(piece.0);
        }
        Ok(())
    }
}

impl From<Vec<u8>> for Framed
{
    /// The parts `bytes` hold, read as they arrived.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: Vec<u8>) -> Self
    {
        Self(bytes)
    }
}

impl AsRef<[u8]> for Framed
{
    /// The bytes, borrowed.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        &self.0
    }
}

/// Bytes this framing does not frame.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Malformed;

/// The bytes of one part.
#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct Part<'bytes>(pub &'bytes [u8]);

impl<'bytes> Part<'bytes>
{
    /// The part read as a manifest image.
    ///
    /// # Specification
    /// trivial.
    pub(super) fn manifest(self) -> ManifestImage<'bytes>
    {
        ManifestImage::from(self.0)
    }
}

/// The parts of a framed run of bytes not yet read, in order.
#[derive(Clone, Debug)]
#[repr(transparent)]
pub struct Parts<'bytes>(pub &'bytes [u8]);

impl<'bytes> Iterator for Parts<'bytes>
{
    type Item = Result<Part<'bytes>, Malformed>;

    /// The next part, or [`Malformed`] once for bytes that do not frame,
    /// after which nothing is read.
    ///
    /// # Specification
    /// trivial.
    fn next(&mut self) -> Option<Self::Item>
    {
        if self.0.is_empty() {
            return None;
        }
        let framed = self
            .0
            .split_first_chunk::<PREFIX>()
            .and_then(|(&prefix, rest)| {
                let length = Prefix::try_from(prefix).ok()?;
                rest.split_at_checked(usize::from(length))
            });
        let Some((part, rest)) = framed
        else {
            self.0 = &[];
            return Some(Err(Malformed));
        };
        self.0 = rest;
        Some(Ok(Part(part)))
    }
}
