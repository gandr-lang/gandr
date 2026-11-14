//! The IO layer's witnesses, one module for each area.
//!
//! One target rather than one per area, so a witness path names the area it
//! belongs to (`tests::io::…`) instead of a file.

extern crate alloc;

#[cfg(test)]
#[cfg(all(
    target_os = "linux",
    any(
        target_arch = "aarch64",
        target_arch = "riscv64",
        target_arch = "x86_64"
    )
))]
mod common;
#[cfg(test)]
#[cfg(all(
    target_os = "linux",
    any(
        target_arch = "aarch64",
        target_arch = "riscv64",
        target_arch = "x86_64"
    )
))]
mod faults;
#[cfg(test)]
#[cfg(all(
    target_os = "linux",
    any(
        target_arch = "aarch64",
        target_arch = "riscv64",
        target_arch = "x86_64"
    )
))]
mod io;
