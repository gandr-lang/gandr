//! The crate's integration suites, one module per area.
//!
//! One target rather than one per area, so a contract's witness path names the
//! area it belongs to (`tests::session::…`) instead of a file.

#[cfg(test)]
mod common;
#[cfg(test)]
mod generate;

#[cfg(test)]
mod checkpoint;
#[cfg(test)]
mod corpus;
#[cfg(test)]
mod diag;
#[cfg(test)]
mod diag_attr;
#[cfg(test)]
mod diag_obligations;
#[cfg(test)]
mod edit;
#[cfg(test)]
mod goals;
#[cfg(test)]
mod incremental;
#[cfg(test)]
mod items;
#[cfg(test)]
mod session;
