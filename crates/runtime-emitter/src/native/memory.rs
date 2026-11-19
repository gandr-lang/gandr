//! The executable regions: one mapping each, bump-allocated, written under
//! the host's write-xor-execute discipline.
//!
//! On macOS arm64 a region is one `MAP_JIT` mapping. Write-xor-execute there
//! is per thread: `pthread_jit_write_protect_np(0)` makes every `MAP_JIT`
//! page writable and not executable for the calling thread, `(1)` the
//! reverse, with no system call, so another thread runs code in the region
//! while one writes. The instruction cache is not coherent with data writes,
//! so a written range is invalidated before it runs. The alternative,
//! `mprotect` per emission, is two system calls per function and stops every
//! other thread's code in the region while it writes.
//!
//! On Linux a region is one `memfd` mapped twice: writable at any address,
//! and readable and executable. Writes go through the first view and code
//! runs from the second, so no page is ever both writable and executable and
//! no thread waits on another's write. On x86-64 the executable view is mapped
//! with `MAP_32BIT`, below 2 GiB, which the static relocation model needs: an
//! address operand is a 32-bit absolute field. The instruction cache is
//! coherent with data writes on x86-64. On arm64 the patcher materialises an
//! address page-relative or by `movz`/`movk`, so the view goes anywhere; the
//! instruction cache is not coherent, so a written range is cleaned and
//! invalidated through its executable view before it runs.

use crate::native::Address;
use crate::native::CodeBytes;
use crate::native::table::Offset;

/// Why mapping a region failed: the host's error number.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct MapFailure(pub i32);

/// A region has no room for a reservation.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Full;

/// A range a region handed out.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Reservation
{
    /// Its first byte's offset in the region.
    start: Offset,
    /// Its length.
    length: Offset,
}

/// One executable region and its high-water mark.
///
/// # Specification
/// - ensures: the mapping stays mapped for the region's life, and a byte handed
///   out once is never handed out again.
/// - executable: none — the mapping's state is the host's, which no predicate
///   reads.
#[derive(Debug)]
pub struct Region
{
    /// The executable view's first byte.
    code: *mut u8,
    /// The writable view's first byte: the executable view itself on macOS.
    write: *mut u8,
    /// The mapping's length.
    capacity: usize,
    /// The bytes handed out.
    used: usize,
}

/// A region moves between threads.
///
/// # Safety
/// - unsafe invariants: the region owns its mappings, which no other value
///   unmaps; the emitter's cache moves it between threads only behind a mutex;
///   and a byte of it is written once, before any thread runs it.
// SAFETY: the region owns its mappings; the emitter's cache moves it between
// threads only behind a mutex, and code in it is immutable once written.
unsafe impl Send for Region
{
}

impl Region
{
    /// Hand out `length` bytes at a 16-byte boundary.
    ///
    /// # Specification
    /// - ensures: the range lies inside the mapping and after every earlier
    ///   reservation.
    /// - executable: none — the bound is the one comparison the body makes; a
    ///   predicate would restate it.
    ///
    /// # Errors
    /// [`Full`] when the range would pass the mapping's end; nothing is
    /// handed out.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every named program's function is placed in a
    ///   reservation beside the shared exits' copies; an overlapping range
    ///   overwrites a copy and changes an answer.
    /// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
    #[inline]
    pub fn reserve(
        &mut self,
        length: Offset,
    ) -> Result<Reservation, Full>
    {
        let start = self.used.next_multiple_of(16);
        let end = start.checked_add(length.0).ok_or(Full)?;
        if end > self.capacity {
            return Err(Full);
        }
        self.used = end;
        Ok(Reservation {
            start: Offset(start),
            length,
        })
    }

    /// The executable address of `reservation`'s first byte.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn address(
        &self,
        reservation: Reservation,
    ) -> Address
    {
        Address(self.code.wrapping_add(reservation.start.0).addr())
    }

    /// Run `write` over `reservation`'s writable bytes, then make them
    /// executable for every thread.
    ///
    /// # Specification
    /// - ensures: on macOS the calling thread's write toggle is restored and
    ///   the range's instruction cache invalidated whatever `write` returns.
    /// - executable: none — the toggle and the cache are the host's state,
    ///   which no predicate reads.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every named program is written through this and then
    ///   run native; a range left writable faults on its first instruction, a
    ///   stale instruction cache runs the bytes before.
    /// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
    #[inline]
    pub fn write<F, T>(
        &self,
        reservation: Reservation,
        write: F,
    ) -> T
    where
        F: FnOnce(CodeBytes<'_>) -> T,
    {
        let start = self.write.wrapping_add(reservation.start.0);
        open_writes();
        // SAFETY: the reservation lies inside the writable view, and no other
        // reservation overlaps it, so these bytes are borrowed once.
        let bytes = unsafe { core::slice::from_raw_parts_mut(start, reservation.length.0) };
        let result = write(CodeBytes(bytes));
        close_writes(self, reservation);
        result
    }
}

/// A byte count, `size_t` in the C declaration.
#[cfg(target_os = "macos")]
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Bytes(usize);

/// The cache maintenance libSystem declares in `<libkern/OSCacheControl.h>`.
///
/// # Safety
/// - unsafe invariants: the signature matches the declaration — `void *` and a
///   transparent `size_t` — and the range passed lies inside a live mapping.
#[cfg(target_os = "macos")]
#[expect(
    unused_doc_comments,
    reason = "the policy lint reads this block's safety section; rustdoc renders none on an extern block"
)]
unsafe extern "C" {
    /// Invalidate the instruction cache over a range.
    ///
    /// # Specification
    /// - requires: the range lies inside a live mapping.
    /// - ensures: an instruction fetched from the range afterwards reads the
    ///   bytes last written there.
    /// - executable: none — a foreign declaration has no body to check.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every named program runs native from bytes written
    ///   just before; a stale cache line would run other bytes.
    /// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
    fn sys_icache_invalidate(
        start: *mut core::ffi::c_void,
        length: Bytes,
    );
}

/// Make `MAP_JIT` pages writable, and not executable, for the calling
/// thread.
///
/// # Specification
/// trivial.
#[cfg(target_os = "macos")]
fn open_writes()
{
    // SAFETY: the toggle changes only this thread's view of MAP_JIT pages.
    unsafe {
        libc::pthread_jit_write_protect_np(0);
    }
}

/// Make `MAP_JIT` pages executable again for the calling thread, and
/// invalidate the instruction cache over `reservation`'s bytes in `region`.
///
/// # Specification
/// trivial.
#[cfg(target_os = "macos")]
fn close_writes(
    region: &Region,
    reservation: Reservation,
)
{
    // SAFETY: the toggle changes only this thread's view of MAP_JIT pages.
    unsafe {
        libc::pthread_jit_write_protect_np(1);
    }
    let start = region.code.wrapping_add(reservation.start.0);
    // SAFETY: the reservation lies inside the region's live mapping.
    unsafe {
        sys_icache_invalidate(start.cast(), Bytes(reservation.length.0));
    }
}

/// The writable view is always writable.
///
/// # Specification
/// trivial.
#[cfg(target_os = "linux")]
const fn open_writes()
{
}

/// The instruction cache is coherent with data writes on x86-64, and the
/// executable view never was writable.
///
/// # Specification
/// trivial.
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
const fn close_writes(
    region: &Region,
    reservation: Reservation,
)
{
    let _ = (region, reservation);
}

/// The cache maintenance the GCC runtime exports.
///
/// # Safety
/// - unsafe invariants: the signature matches the runtime's — two `void *`
///   bounds of one range — and the range lies inside a live mapping.
#[cfg(all(target_os = "linux", target_arch = "aarch64"))]
#[expect(
    unused_doc_comments,
    reason = "the policy lint reads this block's safety section; rustdoc renders none on an extern block"
)]
unsafe extern "C" {
    /// Clean the data cache and invalidate the instruction cache over a
    /// range, to the point of unification.
    ///
    /// # Specification
    /// - requires: the range lies inside a live, readable mapping.
    /// - ensures: an instruction fetched from the range afterwards reads the
    ///   bytes last written to the memory it maps, through any view.
    /// - executable: none — a foreign declaration has no body to check.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every named program runs native from bytes written
    ///   just before; a stale cache line would run other bytes.
    /// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
    fn __clear_cache(
        start: *mut core::ffi::c_void,
        end: *mut core::ffi::c_void,
    );
}

/// Clean and invalidate the caches over `reservation`'s bytes through the
/// executable view: the data cache is physically tagged, so cleaning the
/// executable alias writes back what the writable view wrote, and the
/// instruction cache is invalidated at the addresses code runs from.
///
/// # Specification
/// trivial.
#[cfg(all(target_os = "linux", target_arch = "aarch64"))]
fn close_writes(
    region: &Region,
    reservation: Reservation,
)
{
    let start = region.code.wrapping_add(reservation.start.0);
    let end = start.wrapping_add(reservation.length.0);
    // SAFETY: the reservation lies inside the region's live, readable
    // executable view.
    unsafe {
        __clear_cache(start.cast(), end.cast());
    }
}

/// The host's error number of the last failed call.
///
/// # Specification
/// trivial.
fn last_error() -> MapFailure
{
    MapFailure(std::io::Error::last_os_error().raw_os_error().unwrap_or(0))
}

#[cfg(target_os = "macos")]
impl Region
{
    /// Map a region of `capacity` bytes.
    ///
    /// # Specification
    /// - ensures: a readable, executable `MAP_JIT` mapping, write-protected for
    ///   the calling thread.
    /// - executable: none — the mapping's protection is the host's state, which
    ///   no predicate reads.
    ///
    /// # Errors
    /// [`MapFailure`] with the `mmap` error.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every named program runs from a region this maps; a
    ///   mapping without execute permission faults on the first copy.
    /// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
    #[inline]
    pub fn map(capacity: Offset) -> Result<Self, MapFailure>
    {
        // SAFETY: an anonymous private mapping with no address hint.
        let base = unsafe {
            libc::mmap(
                core::ptr::null_mut(),
                capacity.0,
                libc::PROT_READ | libc::PROT_WRITE | libc::PROT_EXEC,
                libc::MAP_PRIVATE | libc::MAP_ANON | libc::MAP_JIT,
                -1,
                0,
            )
        };
        if base == libc::MAP_FAILED {
            return Err(last_error());
        }
        Ok(Self {
            code: base.cast(),
            write: base.cast(),
            capacity: capacity.0,
            used: 0,
        })
    }
}

/// The executable view's placement flag: below 2 GiB for the x86-64 static
/// relocation model, anywhere for arm64.
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
const EXECUTABLE_PLACEMENT: libc::c_int = libc::MAP_32BIT;
/// The executable view's placement flag: below 2 GiB for the x86-64 static
/// relocation model, anywhere for arm64.
#[cfg(all(target_os = "linux", target_arch = "aarch64"))]
const EXECUTABLE_PLACEMENT: libc::c_int = 0;

#[cfg(target_os = "linux")]
impl Region
{
    /// Map a region of `capacity` bytes.
    ///
    /// # Specification
    /// - ensures: a writable view and a readable, executable view of one
    ///   anonymous file, the executable one below 2 GiB on x86-64.
    /// - executable: none — the mappings' protection and placement are the
    ///   host's state, which no predicate reads.
    ///
    /// # Errors
    /// [`MapFailure`] with the failing call's error.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every named program runs from a region this maps; a
    ///   view above 2 GiB fails the absolute patch, a missing execute
    ///   permission faults on the first copy.
    /// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
    #[inline]
    pub fn map(capacity: Offset) -> Result<Self, MapFailure>
    {
        let length =
            libc::off_t::try_from(capacity.0).map_err(|_overflow| MapFailure(libc::EINVAL))?;
        // SAFETY: the name is a NUL-terminated literal.
        let file = unsafe { libc::memfd_create(c"gandr-emitter".as_ptr(), libc::MFD_CLOEXEC) };
        if file < 0_i32 {
            return Err(last_error());
        }
        let views = || -> Result<Self, MapFailure> {
            // SAFETY: the descriptor is a fresh memfd.
            if unsafe { libc::ftruncate(file, length) } != 0_i32 {
                return Err(last_error());
            }
            // SAFETY: a shared mapping of the whole file, no address hint.
            let write = unsafe {
                libc::mmap(
                    core::ptr::null_mut(),
                    capacity.0,
                    libc::PROT_READ | libc::PROT_WRITE,
                    libc::MAP_SHARED,
                    file,
                    0,
                )
            };
            if write == libc::MAP_FAILED {
                return Err(last_error());
            }
            // SAFETY: a second shared mapping of the same file, below 2 GiB
            // on x86-64.
            let code = unsafe {
                libc::mmap(
                    core::ptr::null_mut(),
                    capacity.0,
                    libc::PROT_READ | libc::PROT_EXEC,
                    libc::MAP_SHARED | EXECUTABLE_PLACEMENT,
                    file,
                    0,
                )
            };
            if code == libc::MAP_FAILED {
                let failure = last_error();
                // SAFETY: the writable view is ours and unused.
                unsafe {
                    libc::munmap(write, capacity.0);
                }
                return Err(failure);
            }
            Ok(Self {
                code: code.cast(),
                write: write.cast(),
                capacity: capacity.0,
                used: 0,
            })
        };
        let mapped = views();
        // SAFETY: the descriptor is ours; the mappings keep the file alive.
        unsafe {
            libc::close(file);
        }
        mapped
    }
}

impl Drop for Region
{
    /// Unmap the region's views.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn drop(&mut self)
    {
        // SAFETY: the mapping is ours; nothing runs from it after the drop,
        // since the cache that hands out its code drops with it.
        unsafe {
            libc::munmap(self.code.cast(), self.capacity);
        }
        if self.write != self.code {
            // SAFETY: as above, for the writable view.
            unsafe {
                libc::munmap(self.write.cast(), self.capacity);
            }
        }
    }
}
