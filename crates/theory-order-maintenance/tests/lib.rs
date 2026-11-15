//! The integration tests of `gandr-theory-order-maintenance`: one target,
//! each area its own `cfg(test)` module, so a witness path reads
//! `tests::<area>::<name>`.

extern crate alloc;

#[cfg(test)]
mod oracle;
