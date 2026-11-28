//! The IO core of the bootstrap, with no libc: open a file, read it, write to
//! a descriptor and close it. The crate is of the layer `boot`, outside the
//! integrity and the validity walls: it checks no term and keeps no value of
//! the store.
//!
//! The tool chain reads each source through Rust's `std`, which links libc.
//! The bootstrap needs these reads before gandr states them itself. Each
//! operation here takes an [`Io`] that [`start`] gives and [`stop`] ends.
//! [`open`] takes the path of a file as a [`Range`](gandr_boot_core::Range)
//! of `boot-core`, and gives a [`Descriptor`]. [`read`] writes the next bytes
//! of the file into a [`Place`](gandr_boot_core::Place), [`write()`] gives the
//! bytes of a [`Range`](gandr_boot_core::Range) to a descriptor, and
//! [`close`] ends the descriptor. Each refusal is one [`Refused`]: the name of
//! the operation and the error number of the kernel. No function allocates,
//! and no function panics.
//!
//! [`open`], [`read`], [`write()`] and [`close`] each make one system call by
//! the crate's own function in assembly, and they never repeat a call. So an
//! interrupted call is a refusal with the error number `EINTR`, and a write
//! that the kernel takes in part gives its count, and the caller decides. The
//! crate has no ring, so [`start`] and [`stop`] make no system call. A form
//! that reads through a ring keeps the address of the page of its ring in its
//! [`Io`].
//!
//! A crate of the layer `boot` is a stage of the bootstrap. A twin in gandr
//! replaces it, so each public function has no generic parameter and states
//! the clauses that the twin meets.
//!
//! # Boundaries
//!
//! The crate has the system calls of Linux on x86-64 alone. On each other
//! target the crate compiles, and each use of [`start`], [`open`], [`read`],
//! [`write()`], [`close`] or [`stop`] is one error of the compiler that names
//! the target. A seek and the walk of a directory are not in the crate.
//!
//! # References
//!
//! - `vault:01a1ebc5-2ff2-7833-b871-85901e734925` — newest: the data core of
//!   the bootstrap (§ boot-data-crates): the rules of a crate of the layer
//!   `boot`, and the row of this crate.
//! - `vault:01a1e7b4-8c77-7a81-9165-ff37ea870424` — newest: the IO direction (§
//!   io-direction-core): the IO core crate, whose signatures hold no generic
//!   parameter and no type of `std`.

#![no_std]

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
mod sys;
#[cfg(not(all(target_os = "linux", target_arch = "x86_64")))]
mod target;

use core::fmt;
use core::num::NonZeroU16;

#[cfg(not(all(target_os = "linux", target_arch = "x86_64")))]
pub use target::close;
#[cfg(not(all(target_os = "linux", target_arch = "x86_64")))]
pub use target::open;
#[cfg(not(all(target_os = "linux", target_arch = "x86_64")))]
pub use target::read;
#[cfg(not(all(target_os = "linux", target_arch = "x86_64")))]
pub use target::start;
#[cfg(not(all(target_os = "linux", target_arch = "x86_64")))]
pub use target::stop;
#[cfg(not(all(target_os = "linux", target_arch = "x86_64")))]
pub use target::write;

/// The handle of the IO core, from [`start`] to [`stop`].
///
/// The crate keeps no state, so the word is 0. A form that reads through a
/// ring keeps the address of the page of its ring in the word.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Debug, Eq, PartialEq)]
pub struct Io(usize);

/// A descriptor of an open file: the number that the kernel gives.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Descriptor(pub i32);

/// The operation that a refusal names.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Operation
{
    /// [`start`].
    Start,
    /// [`open`].
    Open,
    /// [`read`].
    Read,
    /// [`write()`].
    Write,
    /// [`close`].
    Close,
    /// [`stop`].
    Stop,
}

impl fmt::Display for Operation
{
    /// Writes the name of the operation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            Self::Start => "start",
            Self::Open => "open",
            Self::Read => "read",
            Self::Write => "write",
            Self::Close => "close",
            Self::Stop => "stop",
        })
    }
}

/// An error number of the host: `errno` on Linux.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ErrorNumber(pub NonZeroU16);

/// An operation that the kernel refuses: its name and an error number.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Refused
{
    /// The operation.
    operation: Operation,
    /// The error number.
    number: ErrorNumber,
}

impl Refused
{
    /// The refusal of `operation` with the error number `number`.
    ///
    /// # Specification
    /// trivial.
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    const fn new(
        operation: Operation,
        number: ErrorNumber,
    ) -> Self
    {
        Self { operation, number }
    }

    /// The operation that the refusal names.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub const fn operation(self) -> Operation
    {
        self.operation
    }

    /// The error number.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub const fn number(self) -> ErrorNumber
    {
        self.number
    }
}

impl fmt::Display for Refused
{
    /// Writes the operation's name and the error number.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "{}: error number {}", self.operation, self.number.0)
    }
}

impl core::error::Error for Refused
{
}

/// Starts the IO core.
///
/// # Specification
/// - ensures: a handle for the other operations. The crate makes no system call
///   and never refuses.
/// - panics: none.
/// - executable: none — the handle holds no state.
///
/// # Adequacy
/// - hypothesis: L2 — each witness starts a handle, reads through it and stops
///   it.
/// - witness: `tests::file::a_file_of_the_tree_reads_whole_in_steps_of_one_page`
///
/// # Errors
/// None. A form that reads through a ring refuses under the name `start` when
/// the kernel gives it no ring.
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
#[inline]
pub const fn start() -> Result<Io, Refused>
{
    Ok(Io(0))
}

/// Opens the file at `path` to read it.
///
/// # Safety
///
/// - unsafe invariants: the bytes of `path` are readable, a zero byte follows
///   its last byte, and no byte of `path` is zero.
///
/// # Specification
/// - requires: `path` is a path with no zero byte, and a zero byte follows it.
///   The caller holds this invariant; the crate does not read the zero byte.
/// - ensures: a descriptor of the file, open to read, which no child program
///   keeps; or the kernel's error number under the name `open`. A relative path
///   starts at the working directory of the process.
/// - panics: none.
/// - executable: none — the kernel opens the file.
///
/// # Adequacy
/// - hypothesis: L3 — a file of the tree opens and reads whole, and a path with
///   no file is refused with `ENOENT`.
/// - witness: `tests::file::a_file_of_the_tree_reads_whole_in_steps_of_one_page`
/// - witness: `tests::file::a_path_with_no_file_is_refused_with_the_error_number_of_the_kernel`
///
/// # Errors
/// The kernel's error number under the name `open`.
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
#[inline]
pub unsafe fn open(
    io: &Io,
    path: gandr_boot_core::Range,
) -> Result<Descriptor, Refused>
{
    let Io(_) = *io;
    // SAFETY: the caller's invariants hold for the bytes of the path and the
    // zero byte after it.
    unsafe { sys::open(path) }.map_err(|number| Refused::new(Operation::Open, number))
}

/// Reads the next bytes of the file of `descriptor` into the start of `place`.
///
/// # Safety
///
/// - unsafe invariants: the bytes of `place` are writable where it is not
///   empty, and no other access to them happens during the call.
///
/// # Specification
/// - ensures: the count of the bytes that the kernel wrote into the start of
///   `place`, at most its length. The count 0 for a place that is not empty is
///   the end of the file. An empty place gives the count 0 and takes no byte of
///   the file, and the kernel still checks the descriptor. Or the kernel's
///   error number under the name `read`, with no byte of `place` promised. A
///   signal that the process handles while the read waits refuses the read with
///   `EINTR`. The crate does not repeat the call, and the next read of the
///   descriptor takes the bytes that the kernel holds.
/// - panics: none.
/// - executable: none — the kernel writes the bytes.
///
/// # Adequacy
/// - hypothesis: L3 — a file of the tree reads whole in steps of one page and
///   equals the bytes that `std` reads; a file of 0 bytes gives 0 at the first
///   read; an empty place gives 0 and the next reads give the whole file; a
///   closed descriptor is refused with `EBADF`, also for an empty place; a
///   signal during a read that waits gives `EINTR`, and the next read gives the
///   bytes; a file with the descriptor 0 reads whole.
/// - witness: `tests::file::a_file_of_the_tree_reads_whole_in_steps_of_one_page`
/// - witness: `tests::file::a_file_of_no_bytes_gives_the_count_zero_at_the_first_read`
/// - witness: `tests::file::a_read_into_an_empty_place_gives_zero_and_takes_no_byte`
/// - witness: `tests::file::a_closed_descriptor_is_refused_with_ebadf`
/// - witness: `tests::interrupt::a_signal_refuses_a_read_that_waits_with_eintr`
/// - witness: `descriptor::zero::with_descriptor_zero_closed_a_file_takes_it_and_reads_whole_and_a_socket_takes_a_write`
///
/// # Errors
/// The kernel's error number under the name `read`.
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
#[inline]
pub unsafe fn read(
    io: &Io,
    descriptor: Descriptor,
    place: gandr_boot_core::Place,
) -> Result<gandr_boot_core::Length, Refused>
{
    let Io(_) = *io;
    // SAFETY: the caller's invariants hold for the bytes of the place.
    unsafe { sys::read(descriptor, place) }.map_err(|number| Refused::new(Operation::Read, number))
}

/// Gives the bytes of `bytes` to the file of `descriptor`, from its first
/// byte.
///
/// # Safety
///
/// - unsafe invariants: the bytes of `bytes` are readable where it is not
///   empty, and no other access writes them during the call.
///
/// # Specification
/// - ensures: the count of the first bytes of `bytes` that the kernel took, at
///   most its length. A count below the length is a short write: the kernel
///   took those bytes alone, and the caller gives the rest in a next call. An
///   empty range gives the count 0 and gives no byte, and the kernel still
///   checks the descriptor. Or the kernel's error number under the name
///   `write`, with no byte promised. A signal that the process handles while
///   the write waits, before the kernel takes a byte, refuses the write with
///   `EINTR`. The crate does not repeat the call.
/// - panics: none.
/// - executable: none — the kernel takes the bytes.
///
/// # Adequacy
/// - hypothesis: L3 — the bytes of a write equal the bytes that `std` reads at
///   the other end of a socket; a socket that cannot take each byte at once
///   takes the first bytes and gives their count; an empty range gives 0 and no
///   byte; a closed descriptor is refused with `EBADF`, also for an empty
///   range; a signal during a write that waits on a full socket gives `EINTR`,
///   and the next write takes the range; a socket with the descriptor 0 takes a
///   write.
/// - witness: `tests::write::a_write_gives_each_byte_to_the_other_end`
/// - witness: `tests::write::a_full_socket_takes_a_short_write_of_the_first_bytes`
/// - witness: `tests::write::a_write_of_an_empty_range_gives_zero_and_gives_no_byte`
/// - witness: `tests::write::a_write_to_a_closed_descriptor_is_refused_with_ebadf`
/// - witness: `tests::interrupt::a_signal_refuses_a_write_that_waits_with_eintr`
/// - witness: `descriptor::zero::with_descriptor_zero_closed_a_file_takes_it_and_reads_whole_and_a_socket_takes_a_write`
///
/// # Errors
/// The kernel's error number under the name `write`.
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
#[inline]
pub unsafe fn write(
    io: &Io,
    descriptor: Descriptor,
    bytes: gandr_boot_core::Range,
) -> Result<gandr_boot_core::Length, Refused>
{
    let Io(_) = *io;
    // SAFETY: the caller's invariants hold for the bytes of the range.
    unsafe { sys::write(descriptor, bytes) }
        .map_err(|number| Refused::new(Operation::Write, number))
}

/// Closes `descriptor`.
///
/// # Specification
/// - ensures: the descriptor is free for the kernel to give again; or the
///   kernel's error number under the name `close`.
/// - panics: none.
/// - executable: none — the kernel closes the descriptor.
///
/// # Adequacy
/// - hypothesis: L3 — a descriptor closes one time, and a second close is
///   refused with `EBADF`.
/// - witness: `tests::file::a_closed_descriptor_is_refused_with_ebadf`
///
/// # Errors
/// The kernel's error number under the name `close`.
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
#[inline]
pub fn close(
    io: &Io,
    descriptor: Descriptor,
) -> Result<(), Refused>
{
    let Io(_) = *io;
    sys::close(descriptor).map_err(|number| Refused::new(Operation::Close, number))
}

/// Stops the IO core and ends `io`.
///
/// # Specification
/// - ensures: the handle is gone. The crate makes no system call and never
///   refuses. A descriptor that is still open stays open.
/// - panics: none.
/// - executable: none — the handle holds no state.
///
/// # Adequacy
/// - hypothesis: L2 — each witness stops its handle after its last read.
/// - witness: `tests::file::a_file_of_the_tree_reads_whole_in_steps_of_one_page`
///
/// # Errors
/// None. A form that reads through a ring refuses under the name `stop` when
/// the kernel refuses to end its ring.
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
#[expect(
    clippy::needless_pass_by_value,
    reason = "taking the handle by value ends it, so no operation can name it after the stop"
)]
#[inline]
pub const fn stop(io: Io) -> Result<(), Refused>
{
    let Io(_) = io;
    Ok(())
}
