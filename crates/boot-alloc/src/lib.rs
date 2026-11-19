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
//! [`map`] gives a [`Block`] of whole pages with a stated [`Protection`],
//! [`protect`] changes its protection, and [`unmap`] gives it back. The
//! caller states the size of a page as a [`PageSize`], and the crate asks no
//! library for it. A [`Heap`] cuts blocks in size classes from runs of pages,
//! and it implements Rust's [`Allocator`](core::alloc::Allocator) through a
//! shared reference. Each refusal is one [`Refused`]: the name of the
//! operation and an error number.
//!
//! A crate of the area `boot` is a stage of the bootstrap. A twin in gandr
//! replaces it, so each public function has no generic parameter and states
//! the clauses that the twin meets.
//!
//! # References
//!
//! - `vault:01a1ebc5-2ff2-7833-b871-85901e734925` — newest: the data core of
//!   the bootstrap (§ boot-data-crates): the rules of a crate of the area
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
pub(crate) const EINVAL: NonZeroU16 = NonZeroU16::new(22).expect("22 is not zero");

/// The error number of a call that finds no memory: `ENOMEM`.
pub(crate) const ENOMEM: NonZeroU16 = NonZeroU16::new(12).expect("12 is not zero");

/// The size of the host's page in bytes: a power of two that the caller
/// reads from its host.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PageSize(NonZeroUsize);

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
    pub const fn new(bytes: usize) -> Result<Self, Refused>
    {
        match NonZeroUsize::new(bytes) {
            Some(size) if size.is_power_of_two() => Ok(Self(size)),
            _ => Err(Refused::new(Operation::Page, EINVAL)),
        }
    }

    /// The bytes of one page.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub const fn bytes(self) -> NonZeroUsize
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
pub struct Pages(NonZeroUsize);

impl Pages
{
    /// The count of `count` pages.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub const fn new(count: NonZeroUsize) -> Self
    {
        Self(count)
    }

    /// The count.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub const fn count(self) -> NonZeroUsize
    {
        self.0
    }
}

/// What a block's bytes allow.
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
    /// Reads, and runs as machine code.
    ReadExecute,
}

/// A block of whole pages that [`map`] gives.
///
/// A reference that the caller makes from the base lives no longer than the
/// block, and no longer than its protection allows. [`unmap`] takes the
/// block, so a block is given back once.
///
/// # Specification
/// trivial.
#[derive(Debug, Eq, PartialEq)]
pub struct Block
{
    /// The address of the first byte.
    base: NonNull<u8>,
    /// The bytes of the block: a whole number of pages.
    length: NonZeroUsize,
}

impl Block
{
    /// The address of the first byte, aligned to a page.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub const fn base(&self) -> NonNull<u8>
    {
        self.base
    }

    /// The bytes of the block.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub const fn length(&self) -> NonZeroUsize
    {
        self.length
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
    /// [`map`], or the run of pages that a heap maps.
    Map,
    /// [`protect`].
    Protect,
    /// [`unmap`], or the run of pages that a heap gives back.
    Unmap,
    /// [`Heap::allocate`] and [`Heap::grow`], for a layout that no block
    /// takes.
    Allocate,
}

impl Operation
{
    /// The name of the operation.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub const fn name(self) -> &'static str
    {
        match self {
            Self::Page => "page",
            Self::Map => "map",
            Self::Protect => "protect",
            Self::Unmap => "unmap",
            Self::Allocate => "allocate",
        }
    }
}

/// An error number of the host: `errno` on Linux and on macOS.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ErrorNumber(NonZeroU16);

impl ErrorNumber
{
    /// The error number `number`.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn new(number: NonZeroU16) -> Self
    {
        Self(number)
    }

    /// The number.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub const fn get(self) -> NonZeroU16
    {
        self.0
    }
}

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
        number: NonZeroU16,
    ) -> Self
    {
        Self {
            operation,
            number: ErrorNumber::new(number),
        }
    }

    /// The refusal of `operation` with the host's error number `number`.
    ///
    /// # Specification
    /// trivial.
    const fn host(
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
        write!(
            f,
            "{}: error number {}",
            self.operation.name(),
            self.number.0
        )
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
) -> Result<NonZeroUsize, Refused>
{
    match page.0.checked_mul(pages.0) {
        Some(length) => Ok(length),
        None => Err(Refused::new(Operation::Map, ENOMEM)),
    }
}

/// Maps `pages` pages of `page` bytes each with the protection `protection`.
///
/// # Specification
/// - ensures: a block of `pages` pages whose base is aligned to a page and
///   whose bytes allow what `protection` allows; or the host's error number
///   under the name `map`, with each block that stands unchanged.
/// - panics: none.
/// - executable: none — the host decides what it maps.
///
/// # Adequacy
/// - hypothesis: L3 — the host is the oracle: each page of a block that is
///   readable and writable takes a byte and reads it back.
/// - witness: `tests::map::a_block_takes_a_byte_on_each_page`
///
/// # Errors
/// A refusal under the name `map`: `ENOMEM` for a count whose bytes overflow
/// a word, or the host's error number.
#[inline]
pub fn map(
    page: PageSize,
    pages: Pages,
    protection: Protection,
) -> Result<Block, Refused>
{
    let length = length(page, pages)?;
    let base =
        sys::map(length, protection).map_err(|number| Refused::host(Operation::Map, number))?;
    Ok(Block { base, length })
}

/// Sets the protection of `block` to `protection`.
///
/// # Specification
/// - ensures: the block's bytes allow what `protection` allows; or the host's
///   error number under the name `protect`, with the protection unchanged.
/// - panics: none.
/// - executable: none — the host sets the protection.
///
/// # Adequacy
/// - hypothesis: L3 — a block made read-only reads its byte, and the same block
///   made writable again takes a new one.
/// - witness: `tests::map::a_block_made_read_only_reads_its_byte`
///
/// # Errors
/// The host's error number under the name `protect`.
#[inline]
pub fn protect(
    block: &Block,
    protection: Protection,
) -> Result<(), Refused>
{
    // SAFETY: a reference into the block that the new protection forbids is
    // the caller's to end, as the block's documentation states.
    unsafe { sys::protect(block.base, block.length, protection) }
        .map_err(|number| Refused::host(Operation::Protect, number))
}

/// Gives `block` back to the host.
///
/// # Specification
/// - ensures: the block's pages are unmapped; or the host's error number under
///   the name `unmap`.
/// - panics: none.
/// - executable: none — the host unmaps the pages.
///
/// # Adequacy
/// - hypothesis: L3 — the mapped pages of the process are as many after a heap
///   ends as before it started.
/// - witness: `pages::heap::mixed_blocks_leave_the_mapped_pages_as_they_were`
///
/// # Errors
/// The host's error number under the name `unmap`.
#[inline]
#[expect(
    clippy::needless_pass_by_value,
    reason = "the call takes the block, so no caller unmaps it twice or protects it after"
)]
pub fn unmap(block: Block) -> Result<(), Refused>
{
    let Block { base, length } = block;
    // SAFETY: the call takes the block, and a reference into it is the
    // caller's to end, as the block's documentation states.
    unsafe { sys::unmap(base, length) }.map_err(|number| Refused::host(Operation::Unmap, number))
}
