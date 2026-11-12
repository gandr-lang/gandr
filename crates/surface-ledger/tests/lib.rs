//! The integration tests of `gandr-surface-ledger`: one target, each area its
//! own `cfg(test)` module, so a witness path reads `tests::<area>::<name>`.
//! The crate has no area of its own here yet: each witness of a ledger is a
//! unit test of the `ledger` module that builds it, and the driver's
//! `tests::cli` cases run each `gandr ledger` verb end to end.
