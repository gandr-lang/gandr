//! Behavioral witnesses for closed session types and endpoint replay.

#![cfg(test)]
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(clone_in_loop, reason = "1 cost-shape site; #814 lists it")
)]

extern crate alloc;

mod certified;
mod common;
mod construction;
mod monitor;
mod protocols;
mod relations;
