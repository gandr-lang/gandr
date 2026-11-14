//! The IO layer's witnesses, one module for each area.
//!
//! One target rather than one per area, so a witness path names the area it
//! belongs to (`tests::ring::…`) instead of a file.

#[cfg(test)]
#[cfg(all(
    target_os = "linux",
    any(target_arch = "x86_64", target_arch = "riscv64")
))]
mod ring;
