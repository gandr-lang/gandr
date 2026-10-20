//! The integration tests of `gandr-core-checker`: one target, each area its own
//! `cfg(test)` module, so a witness path reads `tests::<area>::<name>`.

extern crate alloc;

#[cfg(test)]
mod codata;
#[cfg(test)]
mod native_formers;
#[cfg(test)]
mod recursive_data;
