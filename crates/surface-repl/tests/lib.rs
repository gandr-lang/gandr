//! The integration tests of `gandr-surface-repl`: one target, each area its own
//! `cfg(test)` module, so a witness path reads `tests::<area>::<name>`.

#[cfg(test)]
mod live_match;
#[cfg(test)]
mod repl_loop;
#[cfg(test)]
mod terminal;
