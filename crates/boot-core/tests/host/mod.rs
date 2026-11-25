//! Two pages from the host through its C library, which the test binaries
//! link through Rust's `std`: the first readable and writable, the second
//! with no access. A range that ends at the end of the first page faults on
//! any read or write past its end. The crate itself maps nothing.

use core::ffi::c_int;
use core::ffi::c_long;
use core::ffi::c_void;

use gandr_boot_core::Place;
use gandr_boot_core::Range;

/// A C `int`: a name, a protection, the flags, a descriptor or an answer.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Int(c_int);

/// A C `long`: the answer of `sysconf`.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Long(c_long);

/// A C `size_t`: the bytes of a mapping.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Size(usize);

/// A C `off_t`: an offset into a file.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Offset(i64);

/// The C library's reads of the host's configuration and its mapping calls.
///
/// # Safety
///
/// - unsafe invariants: each signature matches the declaration, with
///   transparent wrappers of the C types; a call names a range of its own
///   mapping, or a range that the kernel picks.
#[expect(
    unused_doc_comments,
    reason = "the policy lint reads this block's safety section; rustdoc renders none on an extern block"
)]
unsafe extern "C" {
    /// The C library's `sysconf`.
    ///
    /// # Specification
    /// trivial.
    fn sysconf(name: Int) -> Long;

    /// The C library's `mmap`.
    ///
    /// # Specification
    /// trivial.
    fn mmap(
        address: *mut c_void,
        length: Size,
        protection: Int,
        flags: Int,
        descriptor: Int,
        offset: Offset,
    ) -> *mut c_void;

    /// The C library's `mprotect`.
    ///
    /// # Specification
    /// trivial.
    fn mprotect(
        address: *mut c_void,
        length: Size,
        protection: Int,
    ) -> Int;

    /// The C library's `munmap`.
    ///
    /// # Specification
    /// trivial.
    fn munmap(
        address: *mut c_void,
        length: Size,
    ) -> Int;
}

/// The name of the page size for `sysconf`.
#[cfg(target_os = "linux")]
const SC_PAGESIZE: Int = Int(30);

/// The name of the page size for `sysconf`.
#[cfg(target_os = "macos")]
const SC_PAGESIZE: Int = Int(29);

/// The flag of a mapping that no file backs.
#[cfg(target_os = "linux")]
const MAP_ANONYMOUS: c_int = 0x20;

/// The flag of a mapping that no file backs.
#[cfg(target_os = "macos")]
const MAP_ANONYMOUS: c_int = 0x1000;

/// The flag of a mapping that no other process sees.
const MAP_PRIVATE: c_int = 0x02;

/// No access.
const PROT_NONE: Int = Int(0);

/// Reads and writes.
const PROT_READ_WRITE: Int = Int(1 | 2);

/// Two pages: the first readable and writable, the second with no access.
///
/// # Specification
/// trivial.
pub struct Guarded
{
    /// The first byte of the first page.
    base: *mut u8,
    /// The bytes of one page.
    page: usize,
}

impl Guarded
{
    /// Two pages of the host, the second with no access.
    ///
    /// # Specification
    /// trivial.
    pub fn new() -> Self
    {
        // SAFETY: `sysconf` reads a value of the host and writes no memory.
        let page = unsafe { sysconf(SC_PAGESIZE) };
        let page = usize::try_from(page.0).expect("the host reports a page size");
        let length = Size(page.checked_mul(2).expect("two pages fit a word"));
        // SAFETY: a private anonymous mapping at an address that the kernel
        // picks touches no memory that the process holds.
        let base = unsafe {
            mmap(
                core::ptr::null_mut(),
                length,
                PROT_READ_WRITE,
                Int(MAP_PRIVATE | MAP_ANONYMOUS),
                Int(-1),
                Offset(0),
            )
        };
        assert_ne!(usize::MAX, base.addr(), "the host maps two pages");
        let base = base.cast::<u8>();
        // SAFETY: the second page is the mapping's own, and nothing reads it.
        let answer = unsafe { mprotect(base.wrapping_add(page).cast(), Size(page), PROT_NONE) };
        assert_eq!(Int(0), answer, "the host takes the second page's access");
        Self { base, page }
    }

    /// The place of the last bytes of the first page, as many as `bytes`
    /// holds, which takes the bytes of `bytes`.
    ///
    /// # Specification
    /// trivial.
    pub fn tail(
        &self,
        bytes: Range,
    ) -> Place
    {
        let start = self
            .page
            .checked_sub(bytes.length.0)
            .expect("the bytes fit a page");
        let base = self.base.wrapping_add(start);
        // SAFETY: the bytes lie in the first page, which is readable and
        // writable, no reference into it lives, and the source is a live
        // array of the test.
        unsafe {
            core::ptr::copy_nonoverlapping(bytes.base, base, bytes.length.0);
        }
        Place {
            base,
            length: bytes.length,
        }
    }

    /// The same bytes as `place`, to read.
    ///
    /// # Specification
    /// trivial.
    pub const fn read(place: Place) -> Range
    {
        Range {
            base: place.base.cast_const(),
            length: place.length,
        }
    }

    /// The bytes of `place` as they stand.
    ///
    /// # Specification
    /// trivial.
    pub fn bytes(place: Place) -> Held
    {
        if place.length.0 == 0 {
            return Held(Vec::new());
        }
        // SAFETY: the place lies in the first page, which is readable.
        Held(unsafe { core::slice::from_raw_parts(place.base, place.length.0) }.to_vec())
    }
}

/// A copy of the bytes that a place holds, which a test compares.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Debug, Eq, PartialEq)]
pub struct Held(pub Vec<u8>);

impl Drop for Guarded
{
    /// Gives the two pages back.
    ///
    /// # Specification
    /// trivial.
    fn drop(&mut self)
    {
        let length = Size(self.page.checked_mul(2).expect("two pages fit a word"));
        // SAFETY: the two pages are this value's own, and no reference into
        // them lives.
        let answer = unsafe { munmap(self.base.cast(), length) };
        assert_eq!(Int(0), answer, "the host unmaps the two pages");
    }
}
