//! The build, its lines and the exit codes, observed by spawning the binary
//! over a scratch table, a scratch lock and a scratch directory of keys.
//!
//! The process-level cases, in a `cfg(test)` module so the crate's lint wall
//! reads them as test code rather than as shipping code.

use std::path::PathBuf;
use std::process::Command;

/// A table of one crate of riscv64.
const TABLE: &str = "[[tool]]\nkey = \"github:a/tool\"\ntargets = [\"riscv64gc-unknown-linux-gnu\"]\nbuild = \"crate\"\ncrate = \"tool\"\n";

/// A lock of that crate at 1.2.3.
const LOCK: &str = "[[tools.\"github:a/tool\"]]\nversion = \"1.2.3\"\n";

/// A scratch directory of the running test, holding the table and the lock:
/// the test's thread names it.
///
/// # Specification
/// trivial.
fn scratch() -> PathBuf
{
    let test = std::thread::current()
        .name()
        .unwrap_or("test")
        .replace("::", "-");
    let directory =
        std::env::temp_dir().join(format!("host-tools-cli-{}-{test}", std::process::id()));
    let _gone = std::fs::remove_dir_all(&directory);
    std::fs::create_dir_all(&directory).unwrap();
    std::fs::write(directory.join("builds.toml"), TABLE).unwrap();
    std::fs::write(directory.join("mise.lock"), LOCK).unwrap();
    directory
}

/// The binary's build of riscv64 over the scratch directory `directory`, with
/// the builder's configuration `host`.
///
/// # Specification
/// trivial.
fn build(
    directory: &std::path::Path,
    host: &std::path::Path,
) -> std::process::Output
{
    Command::new(env!("CARGO_BIN_EXE_host-tools"))
        .args([
            "build",
            "--target",
            "riscv64gc-unknown-linux-gnu",
            "--mise-version",
            "2026.11.4",
        ])
        .arg("--into")
        .arg(directory.join("keys"))
        .arg("--builds")
        .arg(directory.join("builds.toml"))
        .arg("--lock")
        .arg(directory.join("mise.lock"))
        .arg("--host")
        .arg(host)
        .output()
        .unwrap()
}

#[test]
fn a_key_that_stands_is_kept_and_exits_zero()
{
    let directory = scratch();
    std::fs::create_dir_all(directory.join("keys/riscv64gc-unknown-linux-gnu/github-a-tool/1.2.3"))
        .unwrap();
    let output = build(&directory, &directory.join("absent.toml"));
    assert_eq!(String::from_utf8_lossy(&output.stderr), "");
    assert!(output.status.success());
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        "kept github:a/tool 1.2.3\n"
    );
    std::fs::remove_dir_all(&directory).unwrap();
}

#[test]
fn a_build_the_host_refuses_is_named_and_exits_two()
{
    let directory = scratch();
    let output = build(&directory, &directory.join("absent.toml"));
    assert_eq!(output.status.code(), Some(2_i32));
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        "failed github:a/tool 1.2.3: the host's configuration names no linker for riscv64gc-unknown-linux-gnu\n"
    );
    assert!(
        !directory
            .join("keys/riscv64gc-unknown-linux-gnu/github-a-tool/1.2.3")
            .exists()
    );
    std::fs::remove_dir_all(&directory).unwrap();
}

#[test]
fn a_malformed_invocation_exits_two()
{
    let output = Command::new(env!("CARGO_BIN_EXE_host-tools"))
        .args(["build", "--into", "keys"])
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(2_i32));
    assert!(String::from_utf8_lossy(&output.stderr).contains("--target"));
}
