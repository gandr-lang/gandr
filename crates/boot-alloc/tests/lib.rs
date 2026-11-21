//! The witnesses of `gandr-boot-alloc`: the mapping calls and the heap, each
//! against the host.
//!
//! One target rather than one per area, so a witness path names the area it
//! belongs to (`tests::map::…`) instead of a file.

#[cfg(test)]
mod heap;
#[cfg(test)]
mod host;
#[cfg(test)]
mod map;
