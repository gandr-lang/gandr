//! The integration tests of `gandr-surface-lowering`: one target, each area its
//! own `cfg(test)` module, so a witness path reads `tests::<area>::<name>`.

extern crate alloc;

#[cfg(test)]
mod collapse;
#[cfg(test)]
mod lawvere;
#[cfg(test)]
mod modules;
#[cfg(test)]
mod namespace;
#[cfg(test)]
mod recognition;
#[cfg(test)]
mod scopes;
#[cfg(test)]
mod squier;
#[cfg(test)]
mod static_operators;
