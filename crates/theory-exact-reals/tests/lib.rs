//! The integration tests of `gandr-theory-exact-reals`: one target, each area
//! its own `cfg(test)` module, so a witness path reads `tests::<area>::<name>`.

extern crate alloc;

#[cfg(test)]
mod ackermann;
#[cfg(test)]
mod approx;
#[cfg(test)]
mod cache;
#[cfg(test)]
mod certificate;
#[cfg(test)]
mod checkpoint;
#[cfg(test)]
mod dovetail;
#[cfg(test)]
mod dyadic;
#[cfg(test)]
mod elementary;
#[cfg(test)]
mod elimination;
#[cfg(test)]
mod interval;
#[cfg(test)]
mod minimal;
#[cfg(test)]
mod oracle;
#[cfg(test)]
mod plan;
#[cfg(test)]
mod quantifier;
#[cfg(test)]
mod validate;
