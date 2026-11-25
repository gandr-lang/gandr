//! The `llc` that the block compiler runs, as the build script chooses it.
//!
//! The build script and the emitter's tests read this one file, so the choice
//! that the build makes has its own witnesses.

use std::ffi::OsStr;
use std::ffi::OsString;
use std::path::PathBuf;

/// What the build's environment states as `GANDR_LLC`.
///
/// # Specification
/// trivial.
pub enum Stated
{
    /// A path, which the build keeps whole.
    Path(OsString),
    /// No path, so the build takes the `llc` of the sysroot.
    Unstated,
}

/// The `llc` of one build: the path that its environment states, or else the
/// `llc` under the host's directory of the sysroot.
///
/// A cross build states the path, because the `llc` of the building host
/// does not run where the tests run.
///
/// # Specification
/// - ensures: the stated path whole when `stated` holds one, and `sysroot` does
///   not run; else `<sysroot>/lib/rustlib/<host>/bin/llc`.
/// - errors: the error of `sysroot`, which runs with no stated path alone.
/// - executable: none — the build script links no crate of predicates, so the
///   three witnesses below check each clause.
///
/// # Cost
/// - allocation: the path of the `llc`, setup
///
/// # Adequacy
/// - hypothesis: L2 — a cross build names the path that it states, never the
///   `llc` of the building host's sysroot.
/// - witness: `tests::llc::a_stated_path_is_kept_whole_8133`
/// - witness: `tests::llc::an_unstated_path_is_the_llc_of_the_host_sysroot_8133`
/// - witness: `tests::llc::an_unread_sysroot_gives_its_error_8133`
pub fn llc<Sysroot, E>(
    stated: Stated,
    host: &OsStr,
    sysroot: Sysroot,
) -> Result<PathBuf, E>
where
    Sysroot: FnOnce() -> Result<PathBuf, E>,
{
    match stated {
        Stated::Path(path) => Ok(PathBuf::from(path)),
        Stated::Unstated => Ok(sysroot()?
            .join("lib")
            .join("rustlib")
            .join(host)
            .join("bin")
            .join("llc")),
    }
}
