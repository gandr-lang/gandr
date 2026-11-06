//! The integration tests of `gandr-theory-graded-posets`: one target, each
//! area its own `cfg(test)` module, so a witness path reads
//! `tests::<area>::<name>`.

#[cfg(test)]
mod faces;
#[cfg(test)]
mod graded;
#[cfg(test)]
mod subcomplexes;
#[cfg(test)]
mod wide;
