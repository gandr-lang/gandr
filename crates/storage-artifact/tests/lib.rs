//! The integration tests of `gandr-storage-artifact`: one target, each area its
//! own `cfg(test)` module, so a witness path reads `tests::<area>::<name>`.

extern crate alloc;

#[cfg(test)]
mod artifact_contract;
#[cfg(test)]
mod certificate_transport;
