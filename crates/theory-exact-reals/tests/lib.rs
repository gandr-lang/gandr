//! The integration tests of `gandr-theory-exact-reals`: one target, each area
//! its own `cfg(test)` module, so a witness path reads `tests::<area>::<name>`.

#[cfg(test)]
mod dyadic;
#[cfg(test)]
mod interval;
#[cfg(test)]
mod oracle;
#[cfg(test)]
mod plan;
