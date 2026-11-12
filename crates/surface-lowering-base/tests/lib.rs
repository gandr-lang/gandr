//! The integration tests of `gandr-surface-lowering-base`: one target, each
//! area its own `cfg(test)` module, so a witness path reads
//! `tests::<area>::<name>`. The target takes `gandr-surface-lowering` as a
//! dev-dependency, so a case can lower a unit over this crate's items.

extern crate alloc;

#[cfg(test)]
mod attribute;
#[cfg(test)]
mod coincide;
#[cfg(test)]
mod desc_cells;
#[cfg(test)]
mod described;
#[cfg(test)]
mod model;
#[cfg(test)]
mod namespace;
#[cfg(test)]
mod recognition;
#[cfg(test)]
mod slot;
#[cfg(test)]
mod theory;
