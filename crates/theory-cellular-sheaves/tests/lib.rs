//! The integration tests of `gandr-theory-cellular-sheaves`: one target, each
//! area its own `cfg(test)` module, so a witness path reads
//! `tests::<area>::<name>`.

#[cfg(test)]
mod cochains;
#[cfg(test)]
mod reduce;
#[cfg(test)]
mod sheaf;
#[cfg(test)]
mod towers;
