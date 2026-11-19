//! What the tests read from the host through its C library, which the test
//! binaries link through Rust's `std`. The crate itself reads none of it.

use core::ffi::c_int;
use core::ffi::c_long;

use gandr_boot_alloc::PageSize;

unsafe extern "C" {
    /// The C library's `sysconf`.
    fn sysconf(name: c_int) -> c_long;
}

/// The name of the page size for `sysconf`.
#[cfg(target_os = "linux")]
const SC_PAGESIZE: c_int = 30;

/// The name of the page size for `sysconf`.
#[cfg(target_os = "macos")]
const SC_PAGESIZE: c_int = 29;

/// The host's page size, from its C library.
///
/// # Specification
/// trivial.
pub fn page() -> PageSize
{
    // SAFETY: `sysconf` reads a value of the host and writes no memory.
    let bytes = unsafe { sysconf(SC_PAGESIZE) };
    PageSize::new(usize::try_from(bytes).expect("the host reports a page size"))
        .expect("the host's page size is a power of two")
}
