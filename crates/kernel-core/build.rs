//! The kernel's build identity: one digest of every kernel crate's manifest
//! and sources and of the workspace lock, written for the verdict keys to
//! bind.
//!
//! A verdict one kernel recorded is recalled only by a kernel built from the
//! same trusted sources against the same locked dependencies. A change to any
//! file of a `kernel-*` crate, or to any locked version, is another kernel,
//! and every key it computes differs. The script reruns when a kernel crate's
//! directory or the lock changes, and never for a change elsewhere in the
//! workspace.

use std::path::Path;
use std::path::PathBuf;

/// Write `$OUT_DIR/kernel-build`, the 32-byte digest of the kernel crates'
/// files and the workspace lock.
///
/// # Specification
/// - ensures: the digest reads each file under every `crates/kernel-*`
///   directory and `Cargo.lock`, in path order, each as its path relative to
///   the workspace, its length and its bytes, so two builds agree on it exactly
///   when those files agree.
/// - executable: none — the digest's agreement is a property of the files it
///   reads, observable only by building twice.
///
/// # Errors
/// An I/O error reading a file or the environment Cargo sets, or writing the
/// digest.
///
/// # Adequacy
/// - hypothesis: L2 — a verdict is recalled under the build that recorded it
///   and refused under another kernel version, which binds through the key.
/// - witness: `tests::verdicts::a_verdict_is_recalled_only_under_its_own_key`
fn main() -> std::io::Result<()>
{
    let manifest = PathBuf::from(
        std::env::var_os("CARGO_MANIFEST_DIR")
            .ok_or_else(|| std::io::Error::other("Cargo sets CARGO_MANIFEST_DIR"))?,
    );
    let crates = manifest
        .parent()
        .ok_or_else(|| std::io::Error::other("the kernel crate sits in the crates directory"))?;
    let workspace = crates
        .parent()
        .ok_or_else(|| std::io::Error::other("the crates directory sits in the workspace"))?;
    let mut files = Vec::new();
    for entry in std::fs::read_dir(crates)? {
        let path = entry?.path();
        let kernel = path
            .file_name()
            .and_then(|name| name.to_str())
            .is_some_and(|name| name.starts_with("kernel-"));
        if kernel && path.is_dir() {
            println!("cargo:rerun-if-changed={}", path.display());
            gather(&path, &mut files)?;
        }
    }
    let lock = workspace.join("Cargo.lock");
    println!("cargo:rerun-if-changed={}", lock.display());
    files.push(lock);
    files.sort();
    let mut hasher = blake3::Hasher::new_derive_key("gandr kernel build 2026-10-27");
    for file in &files {
        let relative = file.strip_prefix(workspace).unwrap_or(file);
        let bytes = std::fs::read(file)?;
        let _hashed = hasher
            .update(relative.as_os_str().as_encoded_bytes())
            .update(&u64::try_from(bytes.len()).unwrap_or(u64::MAX).to_le_bytes())
            .update(&bytes);
    }
    let out = PathBuf::from(
        std::env::var_os("OUT_DIR").ok_or_else(|| std::io::Error::other("Cargo sets OUT_DIR"))?,
    );
    std::fs::write(out.join("kernel-build"), hasher.finalize().as_bytes())
}

/// Every file under `directory` except build output, appended to `files`.
///
/// # Specification
/// - ensures: `files` gains each regular file below `directory`, skipping any
///   `target` directory, walked from a worklist of directories still to read.
/// - executable: none — a walk of the file system.
///
/// # Errors
/// An I/O error reading a directory.
///
/// # Adequacy
/// - hypothesis: L2 — as [`main`].
/// - witness: `tests::verdicts::a_verdict_is_recalled_only_under_its_own_key`
fn gather(
    directory: &Path,
    files: &mut Vec<PathBuf>,
) -> std::io::Result<()>
{
    let mut pending = vec![directory.to_path_buf()];
    while let Some(directory) = pending.pop() {
        for entry in std::fs::read_dir(&directory)? {
            let path = entry?.path();
            if path.is_dir() {
                if path.file_name().is_some_and(|name| name != "target") {
                    pending.push(path);
                }
            }
            else {
                files.push(path);
            }
        }
    }
    Ok(())
}
