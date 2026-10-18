//! The prune, its report and the exit codes, observed by spawning the
//! binary over a scratch profile directory holding one recorded and one
//! superseded library.
//!
//! The process-level cases, in a `cfg(test)` module so the crate's lint wall
//! reads them as test code rather than as shipping code.

use std::process::Command;

/// The library the recorded build used.
const RECORDED: &str = "liba-00000000000000a1.rlib";

/// The library a dependency change superseded: 2 MiB.
const SUPERSEDED: &str = "liba-00000000000000f1.rlib";

/// The messages of a build of the recorded library, `LIBRARY` standing for
/// its path, ending in `FINISHED`.
const MESSAGES: &str = "{\"reason\":\"compiler-artifact\",\"filenames\":[\"LIBRARY\"]}\nFINISHED\n";

#[test]
fn a_prune_reports_what_it_removed()
{
    let root = std::env::temp_dir().join(format!("build-state-cli-{}-prune", std::process::id()));
    let profile = root.join("debug");
    let deps = profile.join("deps");
    std::fs::create_dir_all(&deps).unwrap();
    std::fs::write(deps.join(RECORDED), "lib").unwrap();
    std::fs::write(deps.join(SUPERSEDED), vec![0_u8; 0x0020_0000]).unwrap();
    let units = root.join("units.jsonl");
    std::fs::write(
        &units,
        MESSAGES
            .replace("LIBRARY", &deps.join(RECORDED).display().to_string())
            .replace("FINISHED", r#"{"reason":"build-finished","success":true}"#),
    )
    .unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_build-state"))
        .arg("prune")
        .arg("--profile-dir")
        .arg(&profile)
        .arg(&units)
        .output()
        .unwrap();
    assert_eq!(String::from_utf8_lossy(&output.stderr), "");
    assert!(output.status.success());
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        format!(
            "pruned 1 entries, 2 MiB, from {}; kept 1\n",
            profile.display()
        )
    );
    assert!(deps.join(RECORDED).exists());
    assert!(!deps.join(SUPERSEDED).exists());
    std::fs::remove_dir_all(&root).unwrap();
}

#[test]
fn a_refusal_removes_nothing_and_exits_two()
{
    let root = std::env::temp_dir().join(format!("build-state-cli-{}-refusal", std::process::id()));
    let profile = root.join("debug");
    let deps = profile.join("deps");
    std::fs::create_dir_all(&deps).unwrap();
    std::fs::write(deps.join(RECORDED), "lib").unwrap();
    std::fs::write(deps.join(SUPERSEDED), "old").unwrap();
    let failed = root.join("units.jsonl");
    std::fs::write(
        &failed,
        MESSAGES
            .replace("LIBRARY", &deps.join(RECORDED).display().to_string())
            .replace("FINISHED", r#"{"reason":"build-finished","success":false}"#),
    )
    .unwrap();
    let missing = root.join("missing.jsonl");
    for (file, refusal) in [
        (
            &failed,
            "the build failed, so its units are not a complete set",
        ),
        (&missing, "No such file or directory"),
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_build-state"))
            .arg("prune")
            .arg("--profile-dir")
            .arg(&profile)
            .arg(file)
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(2_i32));
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            stderr.starts_with(&format!("build-state: {}: ", file.display()))
                && stderr.contains(refusal),
            "{stderr}"
        );
        assert_eq!(String::from_utf8_lossy(&output.stdout), "");
        assert!(deps.join(SUPERSEDED).exists());
    }
    std::fs::remove_dir_all(&root).unwrap();
}

#[test]
fn a_malformed_invocation_exits_two()
{
    let output = Command::new(env!("CARGO_BIN_EXE_build-state"))
        .args(["prune", "--profile-dir", "target/debug"])
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(2_i32));
    assert!(String::from_utf8_lossy(&output.stderr).contains("MESSAGES"));
    let help = Command::new(env!("CARGO_BIN_EXE_build-state"))
        .arg("--help")
        .output()
        .unwrap();
    assert!(help.status.success());
}
