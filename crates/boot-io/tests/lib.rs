//! The witnesses of `gandr-boot-io`: the file operations, each through the one
//! harness.
//!
//! One target rather than one per area, so a witness path names the area it
//! belongs to (`tests::file::…`) instead of a file.

#[cfg(test)]
mod file;
#[cfg(test)]
mod harness;
