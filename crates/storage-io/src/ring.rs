//! The ring: one worker's `io_uring`, with its submission and completion
//! queues mapped into the process through the system calls of `sys`.

use core::mem::size_of;
use core::ptr::NonNull;
use core::sync::atomic::AtomicU32;
use core::sync::atomic::Ordering;
use std::os::fd::AsFd as _;
use std::os::fd::AsRawFd as _;
use std::os::fd::BorrowedFd;
use std::os::fd::OwnedFd;

use crate::sys;
use crate::sys::Errno;
use crate::sys::Mapped;
use crate::sys::Word;
use crate::uapi;
use crate::uapi::io_uring_cqe;
use crate::uapi::io_uring_params;
use crate::uapi::io_uring_sqe;

/// A count of entries or of completions.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Count(u32);

impl From<u32> for Count
{
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: u32) -> Self
    {
        Self(count)
    }
}

impl From<Count> for u32
{
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: Count) -> Self
    {
        count.0
    }
}

/// The key of a submission, which its completion carries back.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Key(u64);

impl From<u64> for Key
{
    /// # Specification
    /// trivial.
    #[inline]
    fn from(key: u64) -> Self
    {
        Self(key)
    }
}

/// A position in a file, in bytes.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Position(u64);

impl From<u64> for Position
{
    /// # Specification
    /// trivial.
    #[inline]
    fn from(position: u64) -> Self
    {
        Self(position)
    }
}

/// A count of bytes that an operation moved.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Moved(u32);

impl From<Moved> for u32
{
    /// # Specification
    /// trivial.
    #[inline]
    fn from(moved: Moved) -> Self
    {
        moved.0
    }
}

/// The bytes that an operation writes from or reads into. A submission
/// names the buffer, and the buffer stays with its owner until the
/// completion.
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

/// The end of one submission: its key, and the bytes it moved or the error
/// number it failed with.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Completion
{
    /// The submission's key.
    pub key: Key,
    /// The bytes moved, or the error number.
    pub outcome: Result<Moved, Errno>,
}

/// The submission queue holds no free entry.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Full;

/// One submission, before the ring takes it.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy)]
pub struct Entry
{
    /// The kernel's form of the submission.
    sqe: io_uring_sqe,
}

impl Entry
{
    /// An entry of `opcode` on `file` over `length` bytes at `address`, at
    /// `position`, with `key`.
    ///
    /// # Specification
    /// trivial.
    fn of(
        opcode: Word,
        file: BorrowedFd<'_>,
        address: Word,
        length: Word,
        position: Position,
        key: Key,
    ) -> Self
    {
        Self {
            sqe: io_uring_sqe {
                opcode: u8::try_from(usize::from(opcode)).unwrap_or(u8::MAX),
                flags: 0,
                ioprio: 0,
                fd: file.as_raw_fd(),
                __bindgen_anon_1: uapi::io_uring_sqe__bindgen_ty_1 { off: position.0 },
                __bindgen_anon_2: uapi::io_uring_sqe__bindgen_ty_2 {
                    addr: u64::try_from(usize::from(address)).unwrap_or(u64::MAX),
                },
                len: u32::try_from(usize::from(length)).unwrap_or(u32::MAX),
                __bindgen_anon_3: uapi::io_uring_sqe__bindgen_ty_3 { rw_flags: 0 },
                user_data: key.0,
                __bindgen_anon_4: uapi::io_uring_sqe__bindgen_ty_4 { buf_index: 0 },
                personality: 0,
                __bindgen_anon_5: uapi::io_uring_sqe__bindgen_ty_5 { splice_fd_in: 0 },
                __bindgen_anon_6: uapi::io_uring_sqe__bindgen_ty_6 {
                    _bindgen_opaque_blob: [0; 2],
                },
            },
        }
    }

    /// A write of `buffer` into `file` at `position`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn write(
        file: BorrowedFd<'_>,
        buffer: &Buffer,
        position: Position,
        key: Key,
    ) -> Self
    {
        Self::of(
            Word::from(uapi::IORING_OP_WRITE),
            file,
            Word::from(buffer.0.as_ptr().expose_provenance()),
            Word::from(buffer.0.len()),
            position,
            key,
        )
    }

    /// A read from `file` at `position` into `buffer`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn read(
        file: BorrowedFd<'_>,
        buffer: &mut Buffer,
        position: Position,
        key: Key,
    ) -> Self
    {
        Self::of(
            Word::from(uapi::IORING_OP_READ),
            file,
            Word::from(buffer.0.as_mut_ptr().expose_provenance()),
            Word::from(buffer.0.len()),
            position,
            key,
        )
    }

    /// A sync of `file`'s data and metadata.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn sync(
        file: BorrowedFd<'_>,
        key: Key,
    ) -> Self
    {
        Self::of(
            Word::from(uapi::IORING_OP_FSYNC),
            file,
            Word::from(0_usize),
            Word::from(0_usize),
            Position(0),
            key,
        )
    }

    /// This entry, with the next entry of its batch linked to it: the next
    /// starts only after this one succeeds, and the kernel cancels it when
    /// this one fails.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn linked(mut self) -> Self
    {
        self.sqe.flags |= 1_u8.checked_shl(uapi::IOSQE_IO_LINK_BIT).unwrap_or(0);
        self
    }
}

/// A position in one of the ring's queues. It counts each entry ever
/// queued and wraps; the queue's mask takes it to a slot.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Index(u32);

impl Index
{
    /// The position `count` entries past this one.
    ///
    /// # Specification
    /// trivial.
    const fn plus(
        self,
        count: Count,
    ) -> Self
    {
        Self(self.0.wrapping_add(count.0))
    }

    /// The entries from `earlier` up to this position.
    ///
    /// # Specification
    /// trivial.
    const fn since(
        self,
        earlier: Self,
    ) -> Count
    {
        Count(self.0.wrapping_sub(earlier.0))
    }

    /// The slot of this position under the queue's `mask`.
    ///
    /// # Specification
    /// trivial.
    const fn masked(
        self,
        mask: Self,
    ) -> Self
    {
        Self(self.0 & mask.0)
    }
}

impl From<Index> for Word
{
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: Index) -> Self
    {
        Self::from(index.0)
    }
}

/// A word of the ring that the kernel and the process share: a head, a
/// tail or a mask.
///
/// # Specification
/// trivial.
#[repr(transparent)]
struct RingWord(AtomicU32);

impl RingWord
{
    /// The position that the word holds.
    ///
    /// # Specification
    /// trivial.
    fn load(
        &self,
        ordering: Ordering,
    ) -> Index
    {
        Index(self.0.load(ordering))
    }

    /// Set the word to `index`.
    ///
    /// # Specification
    /// trivial.
    fn store(
        &self,
        index: Index,
        ordering: Ordering,
    )
    {
        self.0.store(index.0, ordering);
    }
}

/// One mapping of the ring's memory, unmapped when it drops.
struct Mapping
{
    /// The first byte.
    start: Mapped,
    /// The bytes mapped.
    length: Word,
}

impl Mapping
{
    /// The place of a `T` at `offset` from the start, when the whole `T`
    /// lies inside the mapping at its alignment.
    ///
    /// # Specification
    /// - ensures: `Some` of the pointer `offset` bytes past the start when
    ///   `size_of::<T>()` bytes from there lie inside the mapping and the
    ///   pointer is aligned for `T`; `None` otherwise.
    /// - panics: none.
    /// - executable: none — the predicate would repeat the bounds check.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the queues read at the kernel's offsets carry a
    ///   linked write, sync and read to their completions.
    /// - witness: `tests::ring::a_linked_write_sync_and_read_complete_in_order`
    fn at<T>(
        &self,
        offset: Word,
    ) -> Option<NonNull<T>>
    {
        if offset.plus(Word::from(size_of::<T>())) > self.length {
            return None;
        }
        // SAFETY: `offset` plus the size of a `T` lies inside the mapping.
        let place = unsafe { self.start.at::<T>(offset) };
        place.is_aligned().then_some(place)
    }

    /// The ring word at `offset`.
    ///
    /// # Specification
    /// - ensures: `Some` of the shared word when it lies inside the mapping at
    ///   its alignment; `None` otherwise.
    /// - panics: none.
    /// - executable: none — the word is shared with the kernel.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the queue's head and tail, read here, carry a linked
    ///   write, sync and read to their completions.
    /// - witness: `tests::ring::a_linked_write_sync_and_read_complete_in_order`
    fn word(
        &self,
        offset: Word,
    ) -> Option<&RingWord>
    {
        let place = self.at::<RingWord>(offset)?;
        // SAFETY: `place` lies inside the mapping at its alignment; the
        // mapping lives as long as `self`, and the kernel and the process
        // touch the word only by atomic accesses.
        Some(unsafe { place.as_ref() })
    }
}

impl Drop for Mapping
{
    /// # Specification
    /// trivial.
    fn drop(&mut self)
    {
        // SAFETY: `start` and `length` name the whole mapping that
        // `sys::map` made, and nothing reads it after the drop.
        let _unmapped: Result<(), Errno> = unsafe { sys::unmap(self.start, self.length) };
    }
}

/// The kernel's ring is malformed: an offset it reports lies outside its
/// mapping.
const MALFORMED: Errno = Errno::NO_SYSTEM_CALL;

/// One worker's `io_uring`: its descriptor, and its queues mapped into the
/// process.
pub struct Ring
{
    /// The kernel's sizes, offsets and features of the ring.
    params: io_uring_params,
    /// The submission queue, which holds the completion queue too when the
    /// kernel maps both at once.
    queues: Mapping,
    /// The completion queue, when the kernel maps it apart.
    completions: Option<Mapping>,
    /// The submission entries.
    entries: Mapping,
    /// The entries pushed and not yet submitted.
    staged: Count,
    /// The ring's descriptor, dropped after each mapping.
    descriptor: OwnedFd,
}

impl Ring
{
    /// Set up a ring of `entries` submission entries and map its queues.
    ///
    /// # Specification
    /// - ensures: on `Ok`, an empty ring whose queues the process can read and
    ///   write.
    /// - fails: the kernel's error number, such as [`Errno::PERMISSION`] or
    ///   [`Errno::NO_SYSTEM_CALL`].
    /// - panics: none.
    /// - executable: none — the ring is a kernel object, which no predicate
    ///   reads.
    ///
    /// # Errors
    /// The kernel's error number, when it refuses the ring or a mapping.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a ring set up here completes a linked write, sync and
    ///   read in order.
    /// - witness: `tests::ring::a_linked_write_sync_and_read_complete_in_order`
    #[inline]
    pub fn new(entries: Count) -> Result<Self, Errno>
    {
        let mut params = io_uring_params::default();
        let descriptor = sys::setup(Word::from(entries.0), &mut params)?;
        let ring = descriptor.as_fd();
        let submit = Word::from(params.sq_off.array)
            .plus(Word::from(params.sq_entries).times(Word::from(size_of::<u32>())));
        let complete = Word::from(params.cq_off.cqes)
            .plus(Word::from(params.cq_entries).times(Word::from(size_of::<io_uring_cqe>())));
        let single = params.features & uapi::IORING_FEAT_SINGLE_MMAP != 0;
        let queue_length = if single { submit.max(complete) } else { submit };
        let queues = Mapping {
            start: sys::map(ring, queue_length, Word::from(uapi::IORING_OFF_SQ_RING))?,
            length: queue_length,
        };
        let completions = if single {
            None
        }
        else {
            Some(Mapping {
                start: sys::map(ring, complete, Word::from(uapi::IORING_OFF_CQ_RING))?,
                length: complete,
            })
        };
        let entry_length =
            Word::from(params.sq_entries).times(Word::from(size_of::<io_uring_sqe>()));
        let entries = Mapping {
            start: sys::map(ring, entry_length, Word::from(uapi::IORING_OFF_SQES))?,
            length: entry_length,
        };
        Ok(Self {
            params,
            queues,
            completions,
            entries,
            staged: Count(0),
            descriptor,
        })
    }

    /// The mapping that holds the completion queue.
    ///
    /// # Specification
    /// trivial.
    fn completion_queue(&self) -> &Mapping
    {
        self.completions.as_ref().unwrap_or(&self.queues)
    }

    /// Stage `entry` in the next free slot of the submission queue.
    ///
    /// # Specification
    /// - ensures: on `Ok`, the entry staged after each entry before it.
    /// - fails: [`Full`] when the queue holds no free slot.
    /// - panics: none.
    /// - executable: none — the slot is shared memory, which the predicate
    ///   would read as the body writes it.
    ///
    /// # Errors
    /// [`Full`] when each slot holds an entry that the kernel has not
    /// consumed, or the kernel's offsets name no slot.
    ///
    /// # Safety
    /// - unsafe invariants: each buffer that `entry` names stays valid, and no
    ///   other access touches it, until the entry's completion.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — three entries staged in order complete in order.
    /// - witness: `tests::ring::a_linked_write_sync_and_read_complete_in_order`
    #[inline]
    pub unsafe fn push(
        &mut self,
        entry: Entry,
    ) -> Result<(), Full>
    {
        let offsets = self.params.sq_off;
        let head = self
            .queues
            .word(Word::from(offsets.head))
            .ok_or(Full)?
            .load(Ordering::Acquire);
        let tail = self
            .queues
            .word(Word::from(offsets.tail))
            .ok_or(Full)?
            .load(Ordering::Relaxed);
        let mask = self
            .queues
            .word(Word::from(offsets.ring_mask))
            .ok_or(Full)?
            .load(Ordering::Relaxed);
        let next = tail.plus(self.staged);
        if next.since(head) >= Count(self.params.sq_entries) {
            return Err(Full);
        }
        let slot = next.masked(mask);
        let sqe = self
            .entries
            .at::<io_uring_sqe>(Word::from(slot).times(Word::from(size_of::<io_uring_sqe>())))
            .ok_or(Full)?;
        let index = self
            .queues
            .at::<Index>(
                Word::from(offsets.array)
                    .plus(Word::from(slot).times(Word::from(size_of::<u32>()))),
            )
            .ok_or(Full)?;
        // SAFETY: `sqe` lies inside the entries' mapping at its alignment, and
        // the kernel reads it only after the tail moves past its slot.
        unsafe {
            sqe.write(entry.sqe);
        }
        // SAFETY: `index` lies inside the queue's mapping at its alignment,
        // and the kernel reads it only after the tail moves past its slot.
        unsafe {
            index.write(slot);
        }
        self.staged = Count(self.staged.0.wrapping_add(1));
        Ok(())
    }

    /// Submit each staged entry and wait until `wait` completions stand.
    ///
    /// # Specification
    /// - ensures: on `Ok`, the count of entries the kernel consumed; no entry
    ///   stays staged.
    /// - fails: the kernel's error number.
    /// - panics: none.
    /// - executable: none — the queue is shared with the kernel.
    ///
    /// # Errors
    /// The kernel's error number from `io_uring_enter`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one submission of three linked entries gives three
    ///   completions in order.
    /// - witness: `tests::ring::a_linked_write_sync_and_read_complete_in_order`
    #[inline]
    pub fn submit(
        &mut self,
        wait: Count,
    ) -> Result<Count, Errno>
    {
        let tail = self
            .queues
            .word(Word::from(self.params.sq_off.tail))
            .ok_or(MALFORMED)?;
        tail.store(
            tail.load(Ordering::Relaxed).plus(self.staged),
            Ordering::Release,
        );
        let submit = self.staged;
        self.staged = Count(0);
        // SAFETY: each pushed entry's buffers stay valid by `push`'s
        // invariant, and the mappings live as long as `self`.
        let consumed = unsafe {
            sys::enter(
                self.descriptor.as_fd(),
                Word::from(submit.0),
                Word::from(wait.0),
                Word::from(uapi::IORING_ENTER_GETEVENTS),
            )
        }?;
        Ok(Count(
            u32::try_from(usize::from(consumed)).unwrap_or(u32::MAX),
        ))
    }

    /// The next completion, which frees its slot; `None` when none stands.
    ///
    /// # Specification
    /// - ensures: each completion once, in the order the kernel posts them.
    /// - panics: none.
    /// - executable: none — the queue is shared with the kernel.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a write, a sync and a read linked in that order
    ///   complete in that order, and a failed write's linked sync completes
    ///   cancelled.
    /// - witness: `tests::ring::a_linked_write_sync_and_read_complete_in_order`
    /// - witness: `tests::ring::a_failed_write_cancels_its_linked_sync`
    #[inline]
    pub fn complete(&mut self) -> Option<Completion>
    {
        let offsets = self.params.cq_off;
        let queue = self.completion_queue();
        let head = queue.word(Word::from(offsets.head))?;
        let tail = queue
            .word(Word::from(offsets.tail))?
            .load(Ordering::Acquire);
        let mask = queue
            .word(Word::from(offsets.ring_mask))?
            .load(Ordering::Relaxed);
        let at = head.load(Ordering::Relaxed);
        if at == tail {
            return None;
        }
        let slot = at.masked(mask);
        let place = queue.at::<io_uring_cqe>(
            Word::from(offsets.cqes)
                .plus(Word::from(slot).times(Word::from(size_of::<io_uring_cqe>()))),
        )?;
        // SAFETY: `place` lies inside the queue's mapping at its alignment,
        // and the kernel wrote it before it moved the tail past its slot.
        let cqe = unsafe { place.as_ref() };
        let outcome = match u32::try_from(cqe.res) {
            Ok(moved) => Ok(Moved(moved)),
            Err(_negative) => Err(Errno::from(cqe.res)),
        };
        let completion = Completion {
            key: Key(cqe.user_data),
            outcome,
        };
        head.store(at.plus(Count(1)), Ordering::Release);
        Some(completion)
    }
}
