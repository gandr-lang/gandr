//! The record: a header and its bytes. The header names the record's own
//! place, and its checksum covers that place. So a read of another place
//! fails at the header, before its bytes become a value.
//!
//! The header is 80 bytes, little-endian: the checksum, then the shard, the
//! segment, the offset, the length and the digest. The checksum is the first
//! 16 bytes of the BLAKE3 hash of the 64 bytes after it. The digest covers
//! the record's bytes, and the checksum covers the coordinate. A digest alone
//! cannot tell a misdirected record before the reader has its bytes.

use crate::ring::Moved;
use crate::ring::Position;

/// The shard that writes a record.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Shard(u64);

impl From<u64> for Shard
{
    /// # Specification
    /// trivial.
    #[inline]
    fn from(shard: u64) -> Self
    {
        Self(shard)
    }
}

impl From<Shard> for u64
{
    /// # Specification
    /// trivial.
    #[inline]
    fn from(shard: Shard) -> Self
    {
        shard.0
    }
}

/// A segment of a shard, by its number in the shard.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SegmentId(u64);

impl From<u64> for SegmentId
{
    /// # Specification
    /// trivial.
    #[inline]
    fn from(segment: u64) -> Self
    {
        Self(segment)
    }
}

impl From<SegmentId> for u64
{
    /// # Specification
    /// trivial.
    #[inline]
    fn from(segment: SegmentId) -> Self
    {
        segment.0
    }
}

/// The count of a record's bytes after its header.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RecordLength(u64);

impl From<u64> for RecordLength
{
    /// # Specification
    /// trivial.
    #[inline]
    fn from(length: u64) -> Self
    {
        Self(length)
    }
}

impl From<RecordLength> for u64
{
    /// # Specification
    /// trivial.
    #[inline]
    fn from(length: RecordLength) -> Self
    {
        length.0
    }
}

/// The digest of a record's bytes, which the store keys the record by.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RecordDigest([u8; 32]);

impl From<[u8; 32]> for RecordDigest
{
    /// # Specification
    /// trivial.
    #[inline]
    fn from(digest: [u8; 32]) -> Self
    {
        Self(digest)
    }
}

impl From<RecordDigest> for [u8; 32]
{
    /// # Specification
    /// trivial.
    #[inline]
    fn from(digest: RecordDigest) -> Self
    {
        digest.0
    }
}

/// The place of a record: its shard, its segment, and its offset in the
/// segment's file.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Place
{
    /// The shard that writes the record.
    pub shard: Shard,
    /// The segment that holds the record.
    pub segment: SegmentId,
    /// The offset of the record's header in the segment's file.
    pub offset: Position,
}

/// A record's header: its own place, the count of its bytes, and their
/// digest.
///
/// [`Buffer::from`](crate::Buffer) encodes it with its checksum, and
/// [`Buffer::header`](crate::Buffer::header) checks it against the place
/// that a reader expects.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Header
{
    /// The place that the record is written at.
    pub place: Place,
    /// The count of the record's bytes after the header.
    pub length: RecordLength,
    /// The digest of the record's bytes.
    pub digest: RecordDigest,
}

impl Header
{
    /// The count of bytes that a header takes before the record's bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn size() -> Moved
    {
        Moved::from(80_u32)
    }
}
