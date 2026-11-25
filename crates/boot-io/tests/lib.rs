//! The witnesses of `gandr-boot-io`: the file operations, the write and an
//! interrupted call, each through the one harness.
//!
//! One target rather than one per area, so a witness path names the area it
//! belongs to (`tests::file::…`) instead of a file.
//!
//! The witnesses call the system calls of Linux on x86-64. On each other
//! target this test target is empty.

#![cfg(all(target_os = "linux", target_arch = "x86_64"))]

#[cfg(test)]
mod file;
#[cfg(test)]
mod harness;
#[cfg(test)]
mod interrupt;
#[cfg(test)]
mod write;
