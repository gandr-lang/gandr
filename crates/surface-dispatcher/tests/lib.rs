//! The integration tests of `gandr-surface-dispatcher`: one target, each area
//! its own `cfg(test)` module, so a witness path reads `tests::<area>::<name>`.

extern crate alloc;

#[cfg(test)]
mod boundary;
#[cfg(test)]
mod builtins;
#[cfg(test)]
mod census;
#[cfg(test)]
mod coincide;
#[cfg(test)]
mod compose;
#[cfg(test)]
mod corpus;
#[cfg(test)]
mod differential;
#[cfg(test)]
mod digest;
#[cfg(test)]
mod dispatch;
#[cfg(test)]
mod distances;
#[cfg(test)]
mod entries;
#[cfg(test)]
mod entry;
#[cfg(test)]
mod exercised;
#[cfg(test)]
mod locality;
#[cfg(test)]
mod manifold;
#[cfg(test)]
mod measure;
#[cfg(test)]
mod package;
#[cfg(test)]
mod parity;
#[cfg(test)]
mod report;
#[cfg(test)]
mod run;
#[cfg(test)]
mod script;
#[cfg(test)]
mod typed;
#[cfg(all(test, feature = "unfolding-probe"))]
mod unfolding;
#[cfg(test)]
mod walk;
#[cfg(test)]
mod weights;
