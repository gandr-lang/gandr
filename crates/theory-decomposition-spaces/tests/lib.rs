//! The integration tests of `gandr-theory-decomposition-spaces`: one target,
//! each area its own `cfg(test)` module, so a witness path reads
//! `tests::<area>::<name>`.

#[cfg(test)]
mod composition;
#[cfg(test)]
mod pathway;
