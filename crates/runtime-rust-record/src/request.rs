//! The request: a crate's root file, the build's flags and the paths of
//! its functions.
//!
//! A symbol names a function of one build, so the reader compiles the crate
//! with the flags of that build. [`Request::flags`] is the one home of those
//! flags: the reader runs with them, and a build that links the crate passes
//! them too.

use alloc::vec::Vec;
use std::ffi::OsString;
use std::path::PathBuf;

use crate::names::CrateName;
use crate::names::FunctionPath;
use crate::names::Target;

/// The edition that a crate is written in.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Edition
{
    /// Rust 2021.
    E2021,
    /// Rust 2024.
    E2024,
}

/// A crate and the functions of it that a caller needs.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Request
{
    /// The crate's root file.
    pub root: PathBuf,
    /// The crate's name.
    pub name: CrateName,
    /// The crate's edition.
    pub edition: Edition,
    /// Each function's path inside the crate.
    pub functions: Vec<FunctionPath>,
}

impl Request
{
    /// The flags of the build that the record is for, after the program's
    /// name: a library of the request's name and edition at optimisation
    /// level 3, under the v0 mangling, for `target`, from the root file.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the fourteen flags of the command, setup
    #[must_use]
    #[inline]
    pub fn flags(
        &self,
        target: &Target,
    ) -> Vec<OsString>
    {
        let edition = match self.edition {
            Edition::E2021 => "2021",
            Edition::E2024 => "2024",
        };
        let mut flags = Vec::with_capacity(14);
        for flag in ["--crate-type", "lib", "--crate-name"] {
            flags.push(OsString::from(flag));
        }
        flags.push(OsString::from(self.name.as_ref()));
        flags.push(OsString::from("--edition"));
        flags.push(OsString::from(edition));
        for flag in [
            "-C",
            "opt-level=3",
            "-C",
            "symbol-mangling-version=v0",
            "--target",
        ] {
            flags.push(OsString::from(flag));
        }
        flags.push(OsString::from(target.as_ref()));
        flags.push(self.root.clone().into_os_string());
        flags
    }
}
