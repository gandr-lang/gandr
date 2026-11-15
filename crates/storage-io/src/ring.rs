//! The ring: one worker's `io_uring`, with its submission and completion
//! queues mapped into the process through the system calls of `sys`.

use core::alloc::Allocator;
use core::mem::size_of;
use core::ptr::NonNull;
use core::sync::atomic::AtomicU32;
use core::sync::atomic::AtomicU64;
use core::sync::atomic::Ordering;
use std::os::fd::AsFd as _;
use std::os::fd::AsRawFd as _;
use std::os::fd::BorrowedFd;
use std::os::fd::OwnedFd;

use crate::buffer::Buffer;
use crate::buffer::FileSlot;
use crate::buffer::Slot;
use crate::buffer::Table;
use crate::sys;
use crate::sys::Errno;
use crate::sys::Mapped;
use crate::sys::Word;
use crate::uapi;
use crate::uapi::io_uring_cqe;
use crate::uapi::io_uring_params;
use crate::uapi::io_uring_sqe;
use crate::uapi::iovec;

/// The table of the next ring that the process sets up.
static TABLES: AtomicU64 = AtomicU64::new(0);

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
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
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

impl From<Position> for u64
{
    /// # Specification
    /// trivial.
    #[inline]
    fn from(position: Position) -> Self
    {
        position.0
    }
}

impl Position
{
    /// The position `moved` bytes past this one, saturated at the last
    /// byte.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn plus(
        self,
        moved: Moved,
    ) -> Self
    {
        Self(self.0.saturating_add(u64::from(moved.0)))
    }
}

/// A count of bytes that an operation moved.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Moved(u32);

impl From<u32> for Moved
{
    /// # Specification
    /// trivial.
    #[inline]
    fn from(moved: u32) -> Self
    {
        Self(moved)
    }
}

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
    /// An entry of `opcode` on `file`, or on no file, over `length` bytes at
    /// `address`, at `position`, with `key`.
    ///
    /// # Specification
    /// trivial.
    fn of(
        opcode: Word,
        file: Option<BorrowedFd<'_>>,
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
                fd: file.map_or(-1, |file| file.as_raw_fd()),
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

    /// This entry, reading or writing by `slot` of its ring's table of fixed
    /// buffers.
    ///
    /// # Specification
    /// trivial.
    fn fixed(
        mut self,
        opcode: Word,
        slot: Slot,
    ) -> Self
    {
        self.sqe.opcode = u8::try_from(usize::from(opcode)).unwrap_or(u8::MAX);
        self.sqe.__bindgen_anon_4 = uapi::io_uring_sqe__bindgen_ty_4 { buf_index: slot.0 };
        self
    }

    /// A write of `buffer` into `file` at `position`, by its slot when
    /// `table` registers it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn write<A>(
        file: BorrowedFd<'_>,
        buffer: &Buffer<A>,
        table: Table,
        position: Position,
        key: Key,
    ) -> Self
    where
        A: Allocator,
    {
        let entry = Self::of(
            Word::from(uapi::IORING_OP_WRITE),
            Some(file),
            buffer.address(),
            Word::from(u32::from(buffer.length())),
            position,
            key,
        );
        buffer.slot_in(table).map_or(entry, |slot| {
            entry.fixed(Word::from(uapi::IORING_OP_WRITE_FIXED), slot)
        })
    }

    /// A read from `file` at `position` into `buffer`, by its slot when
    /// `table` registers it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn read<A>(
        file: BorrowedFd<'_>,
        buffer: &mut Buffer<A>,
        table: Table,
        position: Position,
        key: Key,
    ) -> Self
    where
        A: Allocator,
    {
        let length = Word::from(u32::from(buffer.length()));
        let slot = buffer.slot_in(table);
        let entry = Self::of(
            Word::from(uapi::IORING_OP_READ),
            Some(file),
            buffer.address_mut(),
            length,
            position,
            key,
        );
        slot.map_or(entry, |slot| {
            entry.fixed(Word::from(uapi::IORING_OP_READ_FIXED), slot)
        })
    }

    /// A sync of `file`'s data, and of the metadata a read of the data
    /// needs, as `fdatasync(2)` gives.
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
        let mut entry = Self::of(
            Word::from(uapi::IORING_OP_FSYNC),
            Some(file),
            Word::from(0_usize),
            Word::from(0_usize),
            Position(0),
            key,
        );
        entry.sqe.__bindgen_anon_3 = uapi::io_uring_sqe__bindgen_ty_3 {
            fsync_flags: uapi::IORING_FSYNC_DATASYNC,
        };
        entry
    }

    /// This entry, moving its first `kept` bytes alone.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn limited(
        mut self,
        kept: Moved,
    ) -> Self
    {
        self.sqe.len = self.sqe.len.min(kept.0);
        self
    }

    /// A cancel of the submission keyed `target`, itself keyed `key`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn cancel(
        target: Key,
        key: Key,
    ) -> Self
    {
        Self::of(
            Word::from(uapi::IORING_OP_ASYNC_CANCEL),
            None,
            Word::from(usize::try_from(target.0).unwrap_or(usize::MAX)),
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

    /// This entry, naming its file by `slot` of its ring's table of fixed
    /// files rather than by its descriptor.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn by_slot(
        mut self,
        slot: FileSlot,
    ) -> Self
    {
        self.sqe.fd = i32::try_from(slot.0).unwrap_or(i32::MAX);
        self.sqe.flags |= 1_u8.checked_shl(uapi::IOSQE_FIXED_FILE_BIT).unwrap_or(0);
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
    /// - witness: `tests::io::a_linked_write_sync_and_read_complete_in_order`
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
    /// - witness: `tests::io::a_linked_write_sync_and_read_complete_in_order`
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
const MALFORMED: Errno = Errno::PROTOCOL;

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
    /// The entries pushed since the tail last moved.
    pushed: Count,
    /// The entries past the tail that no `io_uring_enter` consumed yet.
    unsubmitted: Count,
    /// The ring's table of fixed buffers.
    table: Table,
    /// The ring's descriptor, dropped after each mapping.
    descriptor: OwnedFd,
}

impl Ring
{
    /// Set up a ring of `entries` submission entries and map its queues.
    ///
    /// # Specification
    /// - ensures: on `Ok`, an empty ring of at least `entries` submission
    ///   entries, whose queues the process can read and write, on a kernel that
    ///   keeps each submission stable once it is consumed.
    /// - fails: the kernel's error number, such as [`Errno::PERMISSION`] or
    ///   [`Errno::NO_SYSTEM_CALL`], or [`Errno::NOT_SUPPORTED`] for a kernel
    ///   without `IORING_FEAT_SUBMIT_STABLE`.
    /// - panics: none.
    /// - executable: none — the ring is a kernel object, which no predicate
    ///   reads.
    ///
    /// # Errors
    /// The kernel's error number, when it refuses the ring or a mapping, and
    /// [`Errno::NOT_SUPPORTED`] when its submissions are not stable.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a ring set up here completes a linked write, sync and
    ///   read in order.
    /// - witness: `tests::io::a_linked_write_sync_and_read_complete_in_order`
    #[inline]
    pub fn new(entries: Count) -> Result<Self, Errno>
    {
        let mut params = io_uring_params::default();
        let descriptor = sys::setup(Word::from(entries.0), &mut params)?;
        if params.features & uapi::IORING_FEAT_SUBMIT_STABLE == 0 {
            return Err(Errno::NOT_SUPPORTED);
        }
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
            pushed: Count(0),
            unsubmitted: Count(0),
            table: Table(TABLES.fetch_add(1, Ordering::Relaxed)),
            descriptor,
        })
    }

    /// The ring's table of fixed buffers.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn table(&self) -> Table
    {
        self.table
    }

    /// Register `buffers` as the ring's table of fixed buffers, each at its
    /// index, and mark each with its slot.
    ///
    /// # Specification
    /// - ensures: on `Ok`, each buffer carries its slot in the ring's table,
    ///   and the kernel holds its pages until the ring closes.
    /// - fails: the kernel's error number, such as `EBUSY` for a ring that
    ///   registers a table already, or `ENOMEM` past the locked-memory limit;
    ///   [`Errno::INVALID`] for more buffers than a slot counts.
    /// - panics: none.
    /// - executable: none — the registration is the kernel's.
    ///
    /// # Errors
    /// The kernel's error number, or [`Errno::INVALID`] past `u16::MAX`
    /// buffers.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — buffers registered here carry a fixed write and read.
    /// - witness: `tests::io::a_registered_buffer_carries_a_fixed_write_and_read`
    #[inline]
    pub fn register<A, Outer>(
        &self,
        buffers: &mut [Buffer<A>],
        vectors: &mut alloc::vec::Vec<iovec, Outer>,
    ) -> Result<(), Errno>
    where
        A: Allocator,
        Outer: Allocator,
    {
        let count = u16::try_from(buffers.len()).map_err(|_overflow| Errno::INVALID)?;
        vectors.clear();
        vectors.extend(buffers.iter_mut().map(|buffer| iovec {
            iov_base: core::ptr::with_exposed_provenance_mut(usize::from(buffer.address_mut())),
            iov_len: u64::from(u32::from(buffer.length())),
        }));
        // SAFETY: `vectors` names `count` vectors, each over the bytes of one
        // buffer that the caller keeps, and the registration reads them alone.
        let _registered = unsafe {
            sys::register(
                self.descriptor.as_fd(),
                Word::from(uapi::IORING_REGISTER_BUFFERS),
                vectors.as_ptr(),
                Word::from(u32::from(count)),
            )
        }?;
        for (index, buffer) in (0_u16 ..).zip(buffers.iter_mut()) {
            buffer.mark(self.table, Slot(index));
        }
        Ok(())
    }

    /// Register an empty table of `count` fixed files: each slot names no
    /// file until [`Ring::place`] puts one in it.
    ///
    /// # Specification
    /// - ensures: on `Ok`, the ring holds a table of `count` empty slots.
    /// - fails: the kernel's error number, such as `EBUSY` for a ring that
    ///   registers a table of files already.
    /// - panics: none.
    /// - executable: none — the registration is the kernel's.
    ///
    /// # Errors
    /// The kernel's error number.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a fixed file carries a write, a sync and a read, and
    ///   its slot comes back for another file once its handle drops.
    /// - witness: `tests::io::a_fixed_file_carries_a_write_sync_and_read`
    #[inline]
    pub fn register_files(
        &self,
        count: Count,
    ) -> Result<(), Errno>
    {
        let empty = alloc::vec![-1_i32; usize::try_from(count.0).unwrap_or(usize::MAX)];
        // SAFETY: `empty` names `count` descriptors, and the registration
        // reads them alone.
        let _registered = unsafe {
            sys::register(
                self.descriptor.as_fd(),
                Word::from(uapi::IORING_REGISTER_FILES),
                empty.as_ptr(),
                Word::from(count.0),
            )
        }?;
        Ok(())
    }

    /// Put `file` in `slot` of the ring's table of fixed files, in place of
    /// the file the slot held.
    ///
    /// # Specification
    /// - ensures: on `Ok`, an entry by `slot` reaches `file`; the kernel holds
    ///   its own share of `file` until the slot takes another or the ring
    ///   closes.
    /// - fails: the kernel's error number, such as `EINVAL` for a slot past the
    ///   table.
    /// - panics: none.
    /// - executable: none — the table is the kernel's.
    ///
    /// # Errors
    /// The kernel's error number.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Ring::register_files`].
    /// - witness: `tests::io::a_fixed_file_carries_a_write_sync_and_read`
    #[inline]
    pub fn place(
        &self,
        slot: FileSlot,
        file: BorrowedFd<'_>,
    ) -> Result<(), Errno>
    {
        let descriptor = file.as_raw_fd();
        let update = uapi::io_uring_files_update {
            offset: slot.0,
            resv: 0,
            fds: u64::try_from((&raw const descriptor).expose_provenance()).unwrap_or(u64::MAX),
        };
        // SAFETY: `update` names one descriptor, which lives through the
        // call, and the update reads it alone.
        let _updated = unsafe {
            sys::register(
                self.descriptor.as_fd(),
                Word::from(uapi::IORING_REGISTER_FILES_UPDATE),
                &raw const update,
                Word::from(1_u32),
            )
        }?;
        Ok(())
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
    /// - witness: `tests::io::a_linked_write_sync_and_read_complete_in_order`
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
        let next = tail.plus(self.pushed);
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
        self.pushed = Count(self.pushed.0.wrapping_add(1));
        Ok(())
    }

    /// Submit each entry that no call consumed yet, and wait until `wait`
    /// completions stand.
    ///
    /// # Specification
    /// - ensures: on `Ok`, the count of entries the kernel consumed; an entry
    ///   that the kernel did not consume stays for the next call.
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
    /// - witness: `tests::io::a_linked_write_sync_and_read_complete_in_order`
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
            tail.load(Ordering::Relaxed).plus(self.pushed),
            Ordering::Release,
        );
        let submit = Count(self.unsubmitted.0.wrapping_add(self.pushed.0));
        self.pushed = Count(0);
        self.unsubmitted = submit;
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
        let consumed = Count(
            u32::try_from(usize::from(consumed))
                .unwrap_or(u32::MAX)
                .min(submit.0),
        );
        self.unsubmitted = Count(submit.0.wrapping_sub(consumed.0));
        Ok(consumed)
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
    /// - witness: `tests::io::a_linked_write_sync_and_read_complete_in_order`
    /// - witness: `tests::io::a_failed_write_cancels_its_linked_sync`
    #[inline]
    pub fn complete(&self) -> Option<Completion>
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
