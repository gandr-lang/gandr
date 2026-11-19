//! What the tests read from the host through its C library, which the test
//! binaries link through Rust's `std`. The crate itself reads none of it.

use core::ffi::c_int;
use core::ffi::c_long;

use gandr_boot_alloc::Bytes;
use gandr_boot_alloc::PageSize;

/// The name of a value that `sysconf` reads.
///
/// # Specification
/// trivial.
#[repr(transparent)]
struct Name(c_int);

/// The value that `sysconf` answers, or `-1`.
///
/// # Specification
/// trivial.
#[repr(transparent)]
struct Answer(c_long);

/// The C library's reads of the host's configuration.
///
/// # Safety
///
/// - unsafe invariants: the signature matches the declaration, a transparent
///   `int` and `long`, and `sysconf` writes no memory of the process.
#[expect(
    unused_doc_comments,
    reason = "the policy lint reads this block's safety section; rustdoc renders none on an extern block"
)]
unsafe extern "C" {
    /// The C library's `sysconf`.
    ///
    /// # Specification
    /// trivial.
    fn sysconf(name: Name) -> Answer;
}

/// The name of the page size for `sysconf`.
#[cfg(target_os = "linux")]
const SC_PAGESIZE: Name = Name(30);

/// The name of the page size for `sysconf`.
#[cfg(target_os = "macos")]
const SC_PAGESIZE: Name = Name(29);

/// The host's page size, from its C library.
///
/// # Specification
/// trivial.
pub fn page() -> PageSize
{
    // SAFETY: `sysconf` reads a value of the host and writes no memory.
    let bytes = unsafe { sysconf(SC_PAGESIZE) };
    PageSize::new(Bytes(
        usize::try_from(bytes.0).expect("the host reports a page size"),
    ))
    .expect("the host's page size is a power of two")
}
