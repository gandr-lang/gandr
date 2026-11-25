//! The identity of the crate's own build: the commit of the compiler that
//! builds it and the target that it builds for, so that the crate knows them
//! with no process at run time.

use std::env;
use std::io;
use std::process::Command;

/// Reads `rustc -vV` of the building compiler and gives its commit and the
/// target to the crate.
///
/// # Specification
/// - ensures: the crate's `GANDR_RUST_COMMIT` is the compiler's `commit-hash`,
///   and its `GANDR_RUST_TARGET` is the target that Cargo names.
/// - executable: none — the outputs are Cargo's instructions.
///
/// # Errors
/// An I/O error when `RUSTC` or `TARGET` is unset, when the compiler does
/// not run, or when it prints no commit.
///
/// # Adequacy
/// - hypothesis: L2 — the commit and the target that the crate holds equal the
///   ones that the toolchain of the build prints.
/// - witness: `tests::the_build_identity_is_the_toolchain_of_the_build`
fn main() -> io::Result<()>
{
    println!("cargo::rerun-if-env-changed=RUSTC");
    let rustc = env::var_os("RUSTC").ok_or_else(|| io::Error::other("Cargo sets RUSTC"))?;
    let target = env::var("TARGET").map_err(io::Error::other)?;
    let output = Command::new(&rustc).arg("-vV").output()?;
    let version = String::from_utf8_lossy(&output.stdout);
    let commit = version
        .lines()
        .find_map(|line| line.strip_prefix("commit-hash: "))
        .ok_or_else(|| io::Error::other("`rustc -vV` prints a commit-hash"))?;
    println!("cargo::rustc-env=GANDR_RUST_COMMIT={commit}");
    println!("cargo::rustc-env=GANDR_RUST_TARGET={target}");
    Ok(())
}
