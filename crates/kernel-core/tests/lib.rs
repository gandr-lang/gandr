//! The integration tests of `gandr-kernel-core`: one target, each area its own
//! `cfg(test)` module, so a witness path reads `tests::<area>::<name>`.

extern crate alloc;

#[cfg(test)]
mod acceptance;
#[cfg(test)]
mod adversarial_depth;
#[cfg(test)]
mod bridge_readmission;
#[cfg(test)]
mod codata;
#[cfg(test)]
mod flow_readmission;
#[cfg(test)]
mod native_formers;
#[cfg(test)]
mod recursive_data;
#[cfg(test)]
mod replay_laws;
#[cfg(test)]
mod sealed_export;
