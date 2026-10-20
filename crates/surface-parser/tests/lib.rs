//! The integration suites of `gandr-surface-parser`: acceptance over the
//! built-in surface, the melder's contracts, the grammar contracts only a
//! parse can witness, and the sweeps over the whole corpus.

#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        allocation_in_repeated_body,
        reason = "9 cost-shape sites; #814 lists them"
    )
)]

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
