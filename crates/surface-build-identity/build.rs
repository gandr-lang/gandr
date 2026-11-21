//! The identities of the build: one digest of what the kernel library
//! compiles, and one of what the library of the theory sites compiles.
//!
//! A verdict that one kernel recorded is recalled only by a kernel built from
//! the same sources against the same locked packages. A stratum that one
//! build of the sites certified is recalled only by the same build. Each
//! digest reads the closure of its library, as `src/digest.rs` states. So a
//! change of a test, of a README or of a package outside the closure changes
//! no digest, and the script runs again only when a watched path changes.

extern crate alloc;

use alloc::collections::BTreeSet;
use std::io;
use std::path::Path;
use std::path::PathBuf;

#[path = "src/digest.rs"]
mod digest;

/// The libraries whose closures the script digests: the package, the context
/// of its digest and the file in `OUT_DIR` that holds the digest.
const IDENTITIES: [(&str, &str, &str); 2] = [
    (
        "gandr-kernel-core",
        "gandr kernel build 2026-11-19",
        "kernel-build",
    ),
    (
        "gandr-theory-sites",
        "gandr theory sites build 2026-11-19",
        "sites-build",
    ),
];

/// Write `$OUT_DIR/kernel-build` and `$OUT_DIR/sites-build`, the 32-byte
/// digests of what the kernel library and the sites library compile.
///
/// # Specification
/// - ensures: each file holds [`digest::Workspace::digest`] of its library, and
///   the script prints each path either digest watches as one
///   `rerun-if-changed` line, in path order.
/// - executable: none — the outputs are files and Cargo's instructions.
///
/// # Errors
/// An I/O error reading the environment Cargo sets, as
/// [`digest::Workspace::digest`] fails, or writing a digest.
///
/// # Adequacy
/// - hypothesis: L3 — as [`digest::Workspace::digest`].
/// - witness: `digest::tests::what_the_library_does_not_compile_keeps_the_digest`
fn main() -> io::Result<()>
{
    let manifest = PathBuf::from(
        std::env::var_os("CARGO_MANIFEST_DIR")
            .ok_or_else(|| io::Error::other("Cargo sets CARGO_MANIFEST_DIR"))?,
    );
    let root = manifest
        .parent()
        .and_then(Path::parent)
        .ok_or_else(|| io::Error::other("the crate sits in the crates directory of the workspace"))?
        .to_path_buf();
    let workspace = digest::Workspace::read(root)?;
    let out = PathBuf::from(
        std::env::var_os("OUT_DIR").ok_or_else(|| io::Error::other("Cargo sets OUT_DIR"))?,
    );
    let mut watched = BTreeSet::new();
    for (library, context, file) in IDENTITIES {
        let digested = workspace.digest(
            &digest::PackageName::from(library),
            digest::Context::from(context),
        )?;
        std::fs::write(out.join(file), digested.digest)?;
        watched.extend(digested.watched);
    }
    for path in &watched {
        println!("cargo::rerun-if-changed={}", path.display());
    }
    Ok(())
}
