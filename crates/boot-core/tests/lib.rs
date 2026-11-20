//! The witnesses of `gandr-boot-core`: the block operations, the searches and
//! the checks, each through the one harness.
//!
//! One target rather than one per area, so a witness path names the area it
//! belongs to (`tests::block::…`) instead of a file.

#[cfg(test)]
mod block;
#[cfg(test)]
mod check;
#[cfg(test)]
mod harness;
#[cfg(test)]
mod host;
#[cfg(test)]
mod search;
