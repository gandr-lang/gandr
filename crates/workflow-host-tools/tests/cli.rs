//! The build, the push, their lines and the exit codes, observed by spawning
//! the binary over a scratch table, a scratch lock and a scratch directory of
//! keys.
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

/// The binary's push over the scratch directory `directory`, with the
/// builder's configuration `host` and only `<directory>/bin` on the path.
///
/// # Specification
/// trivial.
fn push(
    directory: &std::path::Path,
    host: &std::path::Path,
) -> std::process::Output
{
    Command::new(env!("CARGO_BIN_EXE_host-tools"))
        .args(["push", "--mise-version", "2026.11.4"])
        .arg("--into")
        .arg(directory.join("keys"))
        .arg("--builds")
        .arg(directory.join("builds.toml"))
        .arg("--lock")
        .arg(directory.join("mise.lock"))
        .arg("--host")
        .arg(host)
        .env("PATH", directory.join("bin"))
        .output()
        .unwrap()
}

/// A program `name` in `<directory>/bin` that exits with `status`.
///
/// # Specification
/// trivial.
fn program(
    directory: &std::path::Path,
    name: &std::path::Path,
    status: &std::path::Path,
)
{
    use std::os::unix::fs::PermissionsExt as _;
    let bin = directory.join("bin");
    std::fs::create_dir_all(&bin).unwrap();
    let path = bin.join(name);
    std::fs::write(&path, format!("#!/bin/sh\nexit {}\n", status.display())).unwrap();
    std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o755_u32)).unwrap();
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

#[test]
fn a_push_with_no_receiver_does_nothing()
{
    let directory = scratch();
    let output = push(&directory, &directory.join("absent.toml"));
    assert_eq!(String::from_utf8_lossy(&output.stderr), "");
    assert!(output.status.success());
    assert_eq!(String::from_utf8_lossy(&output.stdout), "");
    assert!(!directory.join("keys/riscv64gc-unknown-linux-gnu").exists());
    std::fs::remove_dir_all(&directory).unwrap();
}

#[test]
fn a_refused_copy_is_named_and_exits_two()
{
    let directory = scratch();
    std::fs::create_dir_all(directory.join("keys/riscv64gc-unknown-linux-gnu/github-a-tool/1.2.3"))
        .unwrap();
    program(&directory, "mise".as_ref(), "0".as_ref());
    program(&directory, "rsync".as_ref(), "23".as_ref());
    let host = directory.join("host-tools.toml");
    std::fs::write(
        &host,
        "[[receiver]]\nhost = \"rv\"\ntarget = \"riscv64gc-unknown-linux-gnu\"\nmise = \".cargo/bin/mise\"\n",
    )
    .unwrap();
    let output = push(&directory, &host);
    assert_eq!(output.status.code(), Some(2_i32));
    let stdout = String::from_utf8_lossy(&output.stdout);
    let lines: Vec<&str> = stdout.lines().collect();
    assert_eq!(lines.len(), 3_usize, "{stdout}");
    assert_eq!(
        lines.first(),
        Some(&"updated mise on the builder to 2026.11.4")
    );
    assert_eq!(lines.get(1_usize), Some(&"kept github:a/tool 1.2.3"));
    assert!(
        lines
            .get(2_usize)
            .is_some_and(|line| line.starts_with("failed to push github:a/tool 1.2.3 to rv: ")),
        "{stdout}"
    );
    assert!(
        directory
            .join("keys/.pushed/builder/mise.2026.11.4")
            .is_file()
    );
    assert!(!directory.join("keys/.pushed/rv").exists());
    std::fs::remove_dir_all(&directory).unwrap();
}
