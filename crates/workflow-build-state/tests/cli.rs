//! The prune and the join, their reports and the exit codes, observed by
//! spawning the binary over scratch profile directories: one with a recorded
//! and a superseded library, and one restored state with two shards.
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
fn a_join_reports_what_it_took_and_dropped_7508()
{
    let root = std::env::temp_dir().join(format!("build-state-cli-{}-join", std::process::id()));
    if root.exists() {
        std::fs::remove_dir_all(&root).unwrap();
    }
    let (profile, first, second) = (
        root.join("debug"),
        root.join("a/debug"),
        root.join("b/debug"),
    );
    // Writes a library unit of the new layout under a profile: its
    // fingerprint of `value` naming the fingerprints `dependencies`, and its
    // library holding `marker`.
    let unit = |profile: &std::path::Path,
                package: &str,
                hash: &str,
                value: u64,
                dependencies: &[u64],
                marker: &str| {
        let directory = profile.join("build").join(package).join(hash);
        let fingerprint = directory.join("fingerprint");
        std::fs::create_dir_all(&fingerprint).unwrap();
        std::fs::create_dir_all(directory.join("out")).unwrap();
        let deps: Vec<String> = dependencies
            .iter()
            .map(|value| format!("[1,\"dependency\",false,{value}]"))
            .collect();
        let dep_info = format!("debug/build/{package}/{hash}/fingerprint/dep-lib-{package}");
        std::fs::write(
            fingerprint.join(format!("lib-{package}.json")),
            format!(
                "{{\"deps\":[{}],\"local\":[{{\"CheckDepInfo\":{{\"dep_info\":\"{dep_info}\",\"checksum\":false}}}}]}}",
                deps.join(",")
            ),
        )
        .unwrap();
        let text = format!("{:016x}", value.swap_bytes());
        std::fs::write(fingerprint.join(format!("lib-{package}")), text).unwrap();
        std::fs::write(
            fingerprint.join(format!("dep-lib-{package}")),
            "dependencies",
        )
        .unwrap();
        std::fs::write(
            directory
                .join("out")
                .join(format!("lib{package}-{hash}.rmeta")),
            marker,
        )
        .unwrap();
    };
    unit(&profile, "base", "00000000000000d1", 1, &[], "restored");
    unit(&first, "base", "00000000000000d1", 2, &[], "first");
    unit(&second, "base", "00000000000000d1", 3, &[], "second");
    unit(&second, "mixed", "00000000000000e1", 4, &[3], "second");
    let output = Command::new(env!("CARGO_BIN_EXE_build-state"))
        .arg("join")
        .arg("--profile-dir")
        .arg(&profile)
        .arg(&first)
        .arg(&second)
        .output()
        .unwrap();
    assert_eq!(String::from_utf8_lossy(&output.stderr), "");
    assert!(output.status.success());
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        format!(
            "joined 2 shards into {}: took 1 units, kept 0 restored, dropped 1\n",
            profile.display()
        )
    );
    let library = profile.join("build/base/00000000000000d1/out/libbase-00000000000000d1.rmeta");
    assert_eq!(std::fs::read_to_string(library).unwrap(), "first");
    assert!(!profile.join("build/mixed/00000000000000e1").exists());
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

#[cfg(target_os = "linux")]
#[test]
fn an_unwritable_report_exits_two_after_the_prune()
{
    let root = std::env::temp_dir().join(format!("build-state-cli-{}-full", std::process::id()));
    let profile = root.join("debug");
    let deps = profile.join("deps");
    std::fs::create_dir_all(&deps).unwrap();
    std::fs::write(deps.join(RECORDED), "lib").unwrap();
    std::fs::write(deps.join(SUPERSEDED), "old").unwrap();
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
        .stdout(std::fs::File::create("/dev/full").unwrap())
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(2_i32));
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.starts_with("build-state: standard output: "),
        "{stderr}"
    );
    assert!(deps.join(RECORDED).exists());
    assert!(!deps.join(SUPERSEDED).exists());
    std::fs::remove_dir_all(&root).unwrap();
}
