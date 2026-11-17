//! The crate's integration suites, one module per area.
//!
//! One target rather than one per area, so a contract's witness path names the
//! area it belongs to (`tests::gear::…`) instead of a file.

extern crate alloc;

#[cfg(test)]
mod common;

#[cfg(test)]
mod byte;
#[cfg(test)]
mod commitment;
#[cfg(test)]
mod gear;
#[cfg(test)]
mod typed;
