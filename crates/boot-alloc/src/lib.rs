//! Memory for the bootstrap from the kernel's mapping calls, with no libc.
//! The crate is of the layer `boot`, outside the integrity and the validity
//! walls: it checks no term and keeps no value of the store.
//!
//! The parts of the bootstrap need memory before gandr has an allocator of
//! its own. Rust's allocator takes its memory from libc, and the bootstrap
//! links no libc on Linux. This crate takes its memory from the kernel. On
//! Linux each mapping call is a system call by the crate's own function in
//! assembly. On macOS it is a declared function of the system library, which
//! is the kernel's interface on that host.
//!
//! A [`Mapper`] holds the size of a page that the caller states as a
//! [`PageSize`], and the crate asks no library for it. [`Mapper::map`] gives
//! a [`Block`] of whole pages of anonymous memory as a [`Request`] asks: a
//! [`Protection`] and a [`Backing`]. [`Block::protect`] changes its
//! protection, and [`Block::unmap`] gives it back. No protection runs code,
//! so no memory of the crate is executable. A [`Heap`] cuts blocks in size
//! classes from runs of pages, and it implements Rust's
//! [`Allocator`](core::alloc::Allocator) through a shared reference. Each
//! refusal is one [`Refused`]: the name of the operation and an error number.
//!
//! A crate of the layer `boot` is a stage of the bootstrap. A twin in gandr
//! replaces it, so each public function has no generic parameter and states
//! the clauses that the twin meets.
//!
//! # References
//!
//! - `vault:01a1ebc5-2ff2-7833-b871-85901e734925` — newest: the data core of
//!   the bootstrap (§ boot-data-crates): the rules of a crate of the layer
//!   `boot`, and the row of this crate.
//! - `vault:01a1e7b4-8c77-7a81-9165-ff37ea870424` — newest: the IO direction (§
//!   io-direction-no-libc): the path with no libc, and the census of the
//!   emitter's calls through libc.

#![no_std]

mod heap;
mod sys;

use core::fmt;
use core::num::NonZeroU16;
use core::num::NonZeroUsize;
use core::ptr::NonNull;

pub use crate::heap::Heap;

/// The error number of an argument that the call does not take: `EINVAL`.
const EINVAL: ErrorNumber = ErrorNumber(NonZeroU16::new(22).expect("22 is not zero"));

/// The error number of a call that finds no memory: `ENOMEM`.
const ENOMEM: ErrorNumber = ErrorNumber(NonZeroU16::new(12).expect("12 is not zero"));

/// A count of bytes.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Bytes(pub usize);

/// The bytes of a mapping or of a page: never zero.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Length(pub NonZeroUsize);

/// The address of the first byte of a block.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Base(pub NonNull<u8>);

/// The bytes that a heap grants for one allocation: their address and their
/// count, which can be more than the layout asks.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Granted(pub NonNull<[u8]>);

impl Granted
{
    /// The address of the first granted byte.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub const fn base(self) -> Base
    {
        Base(self.0.cast::<u8>())
    }
}

/// The size of the host's page in bytes: a power of two that the caller
/// reads from its host.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PageSize(Length);

impl PageSize
{
    /// The page size of `bytes` bytes.
    ///
    /// # Specification
    /// - ensures: a power of two gives its page size; each other count is
    ///   refused with `EINVAL` under the name `page`.
    /// - panics: none.
    /// - executable: none — the crate reads no page size from the host.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a count that is not a power of two is refused, and
    ///   the host's page size is admitted.
    /// - witness: `tests::map::a_page_size_is_a_power_of_two`
    ///
    /// # Errors
    /// `EINVAL` under the name `page`, for a count that is not a power of two.
    #[inline]
    pub const fn new(bytes: Bytes) -> Result<Self, Refused>
    {
        match NonZeroUsize::new(bytes.0) {
            Some(size) if size.is_power_of_two() => Ok(Self(Length(size))),
            _ => Err(Refused::new(Operation::Page, EINVAL)),
        }
    }

    /// The bytes of one page.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub const fn length(self) -> Length
    {
        self.0
    }
}

/// A count of whole pages.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Pages(pub NonZeroUsize);

/// What a block's bytes allow. No case runs code.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Protection
{
    /// No access: a read or a write faults.
    Inaccessible,
    /// Reads alone.
    Read,
    /// Reads and writes.
    ReadWrite,
}

/// Whether the host reserves memory for the pages of a block when it maps
/// them.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Backing
{
    /// The host counts each page against its memory when it maps the block.
    Reserved,
    /// The host counts a page only when a write touches it: a reservation of
    /// address space. Linux maps such pages with `MAP_NORESERVE`, and macOS
    /// counts no page before its first touch.
    Unreserved,
}

/// What a mapping asks of the host: the protection of its pages, and whether
/// the host reserves memory for them.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Request
{
    /// What the bytes allow.
    pub protection: Protection,
    /// Whether the host reserves memory for the pages.
    pub backing: Backing,
}

/// The host's mapping call over pages of one size, which the caller states.
/// The crate keeps no global state, so each mapper holds its own size.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Mapper(PageSize);

impl Mapper
{
    /// A mapper over pages of `page` bytes.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub const fn new(page: PageSize) -> Self
    {
        Self(page)
    }

    /// The size of a page.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub const fn page(self) -> PageSize
    {
        self.0
    }

    /// Maps `pages` pages of anonymous memory, as `request` asks.
    ///
    /// # Specification
    /// - ensures: a block of `pages` pages whose base is aligned to a page,
    ///   whose bytes allow what the request's protection allows, with the
    ///   request's backing; or the host's error number under the name `map`,
    ///   with each block that stands unchanged.
    /// - panics: none.
    /// - executable: none — the host decides what it maps.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the host is the oracle: each page of a reserved block
    ///   and of an unreserved block that is readable and writable takes a byte
    ///   and reads it back.
    /// - witness: `tests::map::a_block_takes_a_byte_on_each_page`
    ///
    /// # Errors
    /// A refusal under the name `map`: `ENOMEM` for a count whose bytes
    /// overflow a word, or the host's error number.
    #[inline]
    pub fn map(
        self,
        pages: Pages,
        request: Request,
    ) -> Result<Block, Refused>
    {
        let length = length(self.0, pages)?;
        let base =
            sys::map(length, request).map_err(|number| Refused::new(Operation::Map, number))?;
        Ok(Block { base, length })
    }
}

/// A block of whole pages that [`Mapper::map`] gives.
///
/// A reference that the caller makes from the base lives no longer than the
/// block, and no longer than its protection allows. [`Block::unmap`] takes
/// the block, so a block is given back once.
///
/// # Specification
/// trivial.
#[derive(Debug, Eq, PartialEq)]
pub struct Block
{
    /// The address of the first byte.
    base: Base,
    /// The bytes of the block: a whole number of pages.
    length: Length,
}

/// A block moves between threads.
///
/// # Safety
///
/// - unsafe invariants: a block owns its pages, which the process maps for each
///   of its threads, and no other value unmaps them.
// SAFETY: as above.
unsafe impl Send for Block
{
}

/// A block is shared between threads.
///
/// # Safety
///
/// - unsafe invariants: a shared block gives its base and its length alone, and
///   a change of protection is one call of the host.
// SAFETY: as above.
unsafe impl Sync for Block
{
}

impl Block
{
    /// The address of the first byte, aligned to a page.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub const fn base(&self) -> Base
    {
        self.base
    }

    /// The bytes of the block.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub const fn length(&self) -> Length
    {
        self.length
    }

    /// Sets the protection of the block to `protection`.
    ///
    /// # Specification
    /// - ensures: the block's bytes allow what `protection` allows; or the
    ///   host's error number under the name `protect`, with the protection
    ///   unchanged.
    /// - panics: none.
    /// - executable: none — the host sets the protection.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a block made read-only reads its byte, and the same
    ///   block made writable again takes a new one.
    /// - witness: `tests::map::a_block_made_read_only_reads_its_byte`
    ///
    /// # Errors
    /// The host's error number under the name `protect`.
    #[inline]
    pub fn protect(
        &self,
        protection: Protection,
    ) -> Result<(), Refused>
    {
        // SAFETY: a reference into the block that the new protection forbids
        // is the caller's to end, as the block's documentation states.
        unsafe { sys::protect(self.base, self.length, protection) }
            .map_err(|number| Refused::new(Operation::Protect, number))
    }

    /// Gives the block back to the host.
    ///
    /// # Specification
    /// - ensures: the block's pages are unmapped; or the host's error number
    ///   under the name `unmap`.
    /// - panics: none.
    /// - executable: none — the host unmaps the pages.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the mapped pages of the process are as many after a
    ///   heap ends as before it started.
    /// - witness: `pages::heap::mixed_blocks_leave_the_mapped_pages_as_they_were`
    ///
    /// # Errors
    /// The host's error number under the name `unmap`.
    #[inline]
    pub fn unmap(self) -> Result<(), Refused>
    {
        let Self { base, length } = self;
        // SAFETY: the call takes the block, and a reference into it is the
        // caller's to end, as the block's documentation states.
        unsafe { sys::unmap(base, length) }.map_err(|number| Refused::new(Operation::Unmap, number))
    }
}

/// The operation that a refusal names.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Operation
{
    /// [`PageSize::new`].
    Page,
    /// [`Mapper::map`], or the run of pages that a heap maps.
    Map,
    /// [`Block::protect`].
    Protect,
    /// [`Block::unmap`], or the run of pages that a heap gives back.
    Unmap,
    /// [`Heap::allocate`] and [`Heap::grow`], for a layout that no block
    /// takes.
    Allocate,
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
            Self::Page => "page",
            Self::Map => "map",
            Self::Protect => "protect",
            Self::Unmap => "unmap",
            Self::Allocate => "allocate",
        })
    }
}

/// An error number of the host: `errno` on Linux and on macOS.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ErrorNumber(pub NonZeroU16);

/// An operation that the host or the crate refuses: its name and an error
/// number.
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

/// The bytes of `pages` pages of `page` bytes each.
///
/// # Specification
/// - ensures: the product, or a refusal with `ENOMEM` under the name `map` when
///   it overflows a word.
/// - panics: none.
/// - executable: none — a product that overflows maps nothing.
///
/// # Adequacy
/// - hypothesis: L2 — a count of pages past the address space is refused before
///   the kernel sees it.
/// - witness: `tests::map::a_count_past_the_address_space_is_refused`
const fn length(
    page: PageSize,
    pages: Pages,
) -> Result<Length, Refused>
{
    match page.0.0.checked_mul(pages.0) {
        Some(length) => Ok(Length(length)),
        None => Err(Refused::new(Operation::Map, ENOMEM)),
    }
}
