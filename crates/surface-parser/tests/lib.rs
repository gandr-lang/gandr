//! The integration suites of `gandr-surface-parser`: acceptance over the
//! built-in surface, the melder's contracts, the grammar contracts only a
//! parse can witness, and the sweeps over the whole corpus.

#[cfg(test)]
mod acceptance;
#[cfg(test)]
mod common;
#[cfg(test)]
mod contracts;
#[cfg(test)]
mod grammar;
#[cfg(test)]
mod sweeps;
