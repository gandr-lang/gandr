//! The witnesses of `gandr-boot-data`: the vector and the string buffer
//! against a heap of the host.
//!
//! One target rather than one per area, so a witness path names the area it
//! belongs to (`tests::vector::…`) instead of a file.

#[cfg(test)]
mod host;
#[cfg(test)]
mod string;
#[cfg(test)]
mod vector;
