//! The host's three mapping calls, one module for each kernel. Each module
//! gives `map`, `protect` and `unmap` with one signature.

#[cfg(target_os = "linux")]
mod linux;
#[cfg(target_os = "macos")]
mod macos;

#[cfg(target_os = "linux")]
pub use linux::map;
#[cfg(target_os = "linux")]
pub use linux::protect;
#[cfg(target_os = "linux")]
pub use linux::unmap;
#[cfg(target_os = "macos")]
pub use macos::map;
#[cfg(target_os = "macos")]
pub use macos::protect;
#[cfg(target_os = "macos")]
pub use macos::unmap;

use crate::Protection;

/// The bits of a protection, as the kernel reads them.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Bits(u8);

/// The bits of the protection `protection`, which Linux and macOS spell
/// alike: read 1, write 2, execute 4.
///
/// # Specification
/// - ensures: no access is 0; read is 1; read and write is 3; read and execute
///   is 5.
/// - panics: none.
/// - executable: none — the kernel reads the bits.
///
/// # Adequacy
/// - hypothesis: L3 — a page made read-only reads its byte, and a page made
///   writable again takes one.
/// - witness: `tests::map::a_block_made_read_only_reads_its_byte`
const fn bits(protection: Protection) -> Bits
{
    Bits(match protection {
        Protection::Inaccessible => 0,
        Protection::Read => 1,
        Protection::ReadWrite => 1 | 2,
        Protection::ReadExecute => 1 | 4,
    })
}
