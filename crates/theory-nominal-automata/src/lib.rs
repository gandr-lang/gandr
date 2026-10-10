//! Finite register presentations of nominal automata over caller-owned names.
//!
//! Names need equality and ordering, not a global allocator. The word model
//! executes literal membership and supports epsilon name dropping.
//! Allocation-only word and tree models validate symbolic handles; tree terms
//! use a flat arena. See the crate README for model boundaries and public
//! references.

#![no_std]

extern crate alloc;

pub mod handle;
pub mod letter;
pub mod nda;
pub mod rnna;
pub mod rnta;
