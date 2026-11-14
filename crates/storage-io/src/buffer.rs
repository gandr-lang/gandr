//! The buffer: the bytes that move into a submission and come back with its
//! completion. Only this module reads the bytes, so no signature of the
//! crate holds a slice of them.

use std::fs::File;
use std::os::unix::fs::FileExt as _;

use anodized::spec;

use crate::record::Header;
use crate::record::Place;
use crate::record::RecordDigest;
use crate::record::RecordLength;
use crate::record::SegmentId;
use crate::record::Shard;
use crate::ring::Moved;
use crate::ring::Position;
use crate::sys::Errno;
use crate::sys::Word;

/// The bytes that an operation writes from or reads into. The `Io` owns
/// the buffer from its submission to its completion, and the completion
/// gives it back.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Buffer(Vec<u8>);

impl From<Vec<u8>> for Buffer
{
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: Vec<u8>) -> Self
    {
        Self(bytes)
    }
}

impl From<Buffer> for Vec<u8>
{
    /// # Specification
    /// trivial.
    #[inline]
    fn from(buffer: Buffer) -> Self
    {
        buffer.0
    }
}

impl From<&Header> for Buffer
{
    /// The header's 80 bytes, its checksum first.
    ///
    /// # Specification
    /// - ensures: 80 bytes, which [`Buffer::header`] reads back as `header` at
    ///   the header's own place.
    /// - panics: none.
    /// - executable: none — the round trip is the witness's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an encoded header reads back at its own place, and is
    ///   refused at each other place.
    /// - witness: `tests::record::a_header_reads_back_only_at_its_own_place`
    #[inline]
    fn from(header: &Header) -> Self
    {
        let mut covered = [0_u8; 64];
        let fields = u64::from(header.place.shard)
            .to_le_bytes()
            .into_iter()
            .chain(u64::from(header.place.segment).to_le_bytes())
            .chain(u64::from(header.place.offset).to_le_bytes())
            .chain(u64::from(header.length).to_le_bytes())
            .chain(<[u8; 32]>::from(header.digest));
        for (slot, byte) in covered.iter_mut().zip(fields) {
            *slot = byte;
        }
        let mut bytes = Vec::with_capacity(80);
        if let Some(checksum) = blake3::hash(&covered).as_bytes().first_chunk::<16>() {
            bytes.extend_from_slice(checksum);
        }
        bytes.extend_from_slice(&covered);
        Self(bytes)
    }
}

impl Buffer
{
    /// The address of the first byte, for an entry that reads from it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn address(&self) -> Word
    {
        Word::from(self.0.as_ptr().expose_provenance())
    }

    /// The address of the first byte, for an entry that writes into it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn address_mut(&mut self) -> Word
    {
        Word::from(self.0.as_mut_ptr().expose_provenance())
    }

    /// The count of bytes, at most `u32::MAX`, as an entry carries it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn length(&self) -> Moved
    {
        Moved::from(u32::try_from(self.0.len()).unwrap_or(u32::MAX))
    }

    /// Read from `file` at `at` into the buffer, by one positioned read.
    ///
    /// # Specification
    /// - ensures: on `Ok`, the count of bytes read, at most the buffer's
    ///   length.
    /// - fails: the error number of the read.
    /// - panics: none.
    /// - executable: none — the file is the kernel's.
    ///
    /// # Errors
    /// The error number that the read answers.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the blocking form reads back the bytes that a linked
    ///   write wrote.
    /// - witness: `tests::io::a_linked_write_sync_and_read_complete_in_order`
    #[inline]
    pub fn read_from(
        &mut self,
        file: &File,
        at: Position,
    ) -> Result<Moved, Errno>
    {
        file.read_at(&mut self.0, u64::from(at))
            .map(|read| Moved::from(u32::try_from(read).unwrap_or(u32::MAX)))
            .map_err(Errno::from)
    }

    /// Write the buffer into `file` at `at`, by one positioned write.
    ///
    /// # Specification
    /// - ensures: on `Ok`, the count of bytes written, at most the buffer's
    ///   length.
    /// - fails: the error number of the write.
    /// - panics: none.
    /// - executable: none — the file is the kernel's.
    ///
    /// # Errors
    /// The error number that the write answers.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the blocking form's write fails on a file open to
    ///   read alone, and cancels the sync linked to it.
    /// - witness: `tests::io::a_failed_write_cancels_its_linked_sync`
    #[inline]
    pub fn write_into(
        &self,
        file: &File,
        at: Position,
    ) -> Result<Moved, Errno>
    {
        file.write_at(&self.0, u64::from(at))
            .map(|written| Moved::from(u32::try_from(written).unwrap_or(u32::MAX)))
            .map_err(Errno::from)
    }

    /// The header at the start of the buffer, when its checksum holds and it
    /// names the place `expected`.
    ///
    /// # Specification
    /// - ensures: on `Ok`, a header whose place is `expected`.
    /// - fails: [`Errno::CORRUPT`] when the buffer holds fewer than 80 bytes,
    ///   the checksum fails, or the header names another place.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Errno::CORRUPT`] for a short buffer, a failed checksum, or a header
    /// of another place.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an encoded header reads back at its own place, and is
    ///   refused at each other place and with any byte changed.
    /// - witness: `tests::record::a_header_reads_back_only_at_its_own_place`
    /// - witness: `tests::record::a_changed_byte_fails_the_checksum`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |header| header.place == expected))]
    #[inline]
    pub fn header(
        &self,
        expected: Place,
    ) -> Result<Header, Errno>
    {
        let (checksum, rest) = self.0.split_first_chunk::<16>().ok_or(Errno::CORRUPT)?;
        let covered = rest.first_chunk::<64>().ok_or(Errno::CORRUPT)?;
        if blake3::hash(covered).as_bytes().first_chunk::<16>() != Some(checksum) {
            return Err(Errno::CORRUPT);
        }
        let (shard, rest) = covered.split_first_chunk::<8>().ok_or(Errno::CORRUPT)?;
        let (segment, rest) = rest.split_first_chunk::<8>().ok_or(Errno::CORRUPT)?;
        let (offset, rest) = rest.split_first_chunk::<8>().ok_or(Errno::CORRUPT)?;
        let (length, rest) = rest.split_first_chunk::<8>().ok_or(Errno::CORRUPT)?;
        let digest = rest.first_chunk::<32>().ok_or(Errno::CORRUPT)?;
        let header = Header {
            place: Place {
                shard: Shard::from(u64::from_le_bytes(*shard)),
                segment: SegmentId::from(u64::from_le_bytes(*segment)),
                offset: Position::from(u64::from_le_bytes(*offset)),
            },
            length: RecordLength::from(u64::from_le_bytes(*length)),
            digest: RecordDigest::from(*digest),
        };
        if header.place == expected {
            Ok(header)
        }
        else {
            Err(Errno::CORRUPT)
        }
    }
}
