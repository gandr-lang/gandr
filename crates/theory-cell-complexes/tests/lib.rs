//! The crate's integration suites, one module per area.
//!
//! One target rather than one per area, so a witness path names the area it
//! belongs to (`tests::subst::…`) instead of a file. The generated and deep
//! cases live here rather than beside the code because they need `std`: the
//! property runner, and a thread with a small stack.

extern crate alloc;

#[cfg(test)]
mod depth;
#[cfg(test)]
mod generate;
#[cfg(test)]
mod inhabitant;
#[cfg(test)]
mod order;
#[cfg(test)]
mod subst;
#[cfg(test)]
mod toy;
