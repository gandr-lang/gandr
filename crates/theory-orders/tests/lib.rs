//! The integration tests of `gandr-theory-orders`: one target, each area its
//! own `cfg(test)` module, so a witness path reads `tests::<area>::<name>`.

#[cfg(test)]
mod oracle;
