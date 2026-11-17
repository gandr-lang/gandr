//! The stencils' witnesses, one module per area.
//!
//! One target rather than one per area, so a witness path names the area it
//! belongs to (`tests::agreement::…`) instead of a file.

extern crate alloc;

#[cfg(test)]
mod accumulate;
#[cfg(test)]
mod agreement;
#[cfg(test)]
mod count;
#[cfg(test)]
mod exits;
#[cfg(test)]
mod generate;
#[cfg(test)]
mod layout;
#[cfg(test)]
mod support;
