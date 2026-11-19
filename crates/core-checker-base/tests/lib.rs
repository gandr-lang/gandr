//! The integration tests of `gandr-core-checker-base`: one target, each area
//! its own `cfg(test)` module, so a witness path reads `tests::<area>::<name>`.

extern crate alloc;

#[cfg(test)]
mod codata;
#[cfg(test)]
mod flow;
#[cfg(test)]
mod forward;
#[cfg(test)]
mod judgement;
#[cfg(test)]
mod literal_identity;
#[cfg(test)]
mod module;
#[cfg(test)]
mod native_formers;
#[cfg(test)]
mod product;
#[cfg(test)]
mod quantified;
#[cfg(test)]
mod recursion;
#[cfg(test)]
mod recursive_data;
#[cfg(test)]
mod tactic;
#[cfg(test)]
mod ua;
#[cfg(test)]
mod univalence;
#[cfg(test)]
mod worlds;
