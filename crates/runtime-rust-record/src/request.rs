//! The request: the build's command line for a crate and the paths of its
//! functions.
//!
//! A symbol names a function of one build. Cargo adds its own `-C metadata`
//! value to each crate, and that value enters each symbol. So the reader
//! takes the build's command line word for word, and builds none of its own.

use alloc::vec::Vec;
use std::ffi::OsString;

use crate::names::FunctionPath;

/// A crate, as one build compiles it, and the functions of it that a caller
/// needs.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Request
{
    /// The build's arguments to `rustc` for the crate, after the program's
    /// name, word for word.
    pub arguments: Vec<OsString>,
    /// Each function's path inside the crate.
    pub functions: Vec<FunctionPath>,
}
