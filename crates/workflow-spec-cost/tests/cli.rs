//! The ranking, the build and profile invocations and the exit codes, observed
//! by spawning the binary.
//!
//! Each case builds a workspace in its own scratch directory: one crate whose
//! check on line 2 calls a helper whose check is on line 6, and a `target`
//! directory holding a file the parser would reject. A fake `cargo` lists one
//! binary with a test and an ignored test; a fake `perf` records its
//! invocations and prints four samples, one nested, one in a body, two in the
//! helper's check. Both log every invocation.
//!
//! The process-level cases, in a `cfg(test)` module so the crate's lint wall
//! reads them as test code rather than as shipping code.
#![cfg(unix)]

use std::path::PathBuf;
use std::process::Command;

/// The crate's source.
const SOURCE: &str = "\n\
        #[spec(ensures: |ret| helper(ret))]\n\
        fn outer() -> u8 { 1 }\n\
        \n\
        \n\
        #[spec(ensures: |ret| ret)]\n\
        fn helper(_: u8) -> bool { true }\n";

/// The fake `cargo`: logs its arguments and build flags, then lists one
/// binary.
const FAKE_CARGO: &str = r#"#!/bin/sh
printf 'cargo %s | %s | %s | %s\n' "$*" "$RUSTFLAGS" "$CARGO_TARGET_DIR" "$CARGO_PROFILE_TEST_DEBUG" >> "$FAKE_LOG"
printf '{"rust-build-meta":{},"rust-suites":{"gandr-a::tests":{"binary-id":"gandr-a::tests","binary-path":"%s/bin/test-binary","cwd":"%s/crates/a","testcases":{"pick::first":{"ignored":false},"skip::me":{"ignored":true}}}}}\n' "$FAKE_ROOT" "$FAKE_ROOT"
"#;

/// The fake `perf`: records log their invocation and directory and create
/// the data file; scripts print four samples.
const FAKE_PERF: &str = r#"#!/bin/sh
printf 'perf %s | %s\n' "$*" "$(pwd)" >> "$FAKE_LOG"
case "$1" in
  record)
    [ "$FAKE_PERF_MODE" = fail ] && exit 1
    while [ "$1" != -o ]; do shift; done
    : > "$2" ;;
  script)
    printf '\n\t    1 helper\n  crates/a/src/lib.rs:6 (inlined)\n\t    1 {closure#0}\n  crates/a/src/lib.rs:2\n\t    2 outer\n  crates/a/src/lib.rs:3\n'
    printf '\n\t    3 work\n  crates/a/src/lib.rs:9\n\t    3 anodized::__::eval_once::<u8, outer::{closure#1}>\n  ??:0\n\t    4 outer\n  crates/a/src/lib.rs:2\n'
    printf '\n\t    5 helper\n  crates/a/src/lib.rs:6\n'
    printf '\n\t    5 helper\n  crates/a/src/lib.rs:6\n\t    6 main\n  /rust/library/std/src/rt.rs:120\n' ;;
esac
"#;

/// A scratch workspace with the fakes first on the path.
#[derive(Debug)]
#[repr(transparent)]
struct Workspace
{
    /// The workspace root, canonical so it matches the binary's working
    /// directory.
    root: PathBuf,
}

impl Workspace
{
    /// Builds the scratch workspace for one case.
    ///
    /// # Specification
    /// - requires: a single-component `case` unique to the calling test.
    /// - ensures: the crate, the rejected file under `target` and the
    ///   executable fakes exist under a fresh root.
    /// - provides: an isolated workspace for one case.
    /// - fails: never.
    /// - panics: when the scratch directory cannot be prepared.
    /// - executable: none — the outcome is the filesystem, read back by the
    ///   cases that run the binary.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every case runs the binary in it; a missing crate or
    ///   fake changes that case's output.
    /// - witness: `tests::cli::a_profile_is_charged_to_its_outermost_specification`
    fn new(case: &std::path::Path) -> Self
    {
        use std::os::unix::fs::PermissionsExt as _;
        let scratch = std::env::temp_dir()
            .join(format!("spec-cost-{}", std::process::id()))
            .join(case);
        if scratch.exists() {
            std::fs::remove_dir_all(&scratch).unwrap();
        }
        std::fs::create_dir_all(scratch.join("crates/a/src")).unwrap();
        std::fs::create_dir_all(scratch.join("crates/a/target")).unwrap();
        std::fs::create_dir_all(scratch.join("bin")).unwrap();
        let root = std::fs::canonicalize(&scratch).unwrap();
        std::fs::write(root.join("crates/a/src/lib.rs"), SOURCE).unwrap();
        std::fs::write(root.join("crates/a/target/broken.rs"), "fn (").unwrap();
        for (name, script) in [("cargo", FAKE_CARGO), ("perf", FAKE_PERF)] {
            let path = root.join("bin").join(name);
            std::fs::write(&path, script).unwrap();
            std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o755)).unwrap();
        }
        Self { root }
    }

    /// The binary, run in the workspace with the fakes first on the path.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a command that runs the binary in this workspace at 2 Hz.
    /// - provides: the invocation every case extends.
    /// - fails: never.
    /// - panics: when the inherited path cannot be joined with the fakes'.
    /// - executable: none — the outcome is a command not yet run.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the cases observe the fakes' log, so a command that
    ///   missed the fakes would leave it empty.
    /// - witness: `tests::cli::a_profile_is_charged_to_its_outermost_specification`
    fn command(&self) -> Command
    {
        let path = std::env::join_paths(core::iter::once(self.root.join("bin")).chain(
            std::env::split_paths(&std::env::var_os("PATH").unwrap_or_default()),
        ))
        .unwrap();
        let mut command = Command::new(env!("CARGO_BIN_EXE_spec-cost"));
        command
            .current_dir(&self.root)
            .env("PATH", path)
            .env("FAKE_ROOT", &self.root)
            .env("FAKE_LOG", self.root.join("tools.log"))
            .args(["--frequency", "2"]);
        command
    }
}

#[test]
fn a_profile_is_charged_to_its_outermost_specification()
{
    let workspace = Workspace::new(std::path::Path::new("ranked"));
    let output = workspace
        .command()
        .args(["--test", "gandr-a::tests pick::first"])
        .output()
        .unwrap();
    assert_eq!(
        String::from_utf8_lossy(&output.stderr),
        "spec-cost: building the test binaries for sampling\nspec-cost: profiling gandr-a::tests \
             pick::first\n",
        "progress on standard error"
    );
    assert!(output.status.success(), "exit 0");
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        "profiled at 2 Hz\n\
             test                        sampled  in checks\n\
             gandr-a::tests pick::first    2.0 s      75.0%\n\
             \n\
             checks by charged time: the outermost check on each sampled stack; innermost is the \
             time the check itself was running\n\
             rank  charged   share  innermost  tests  check\n   \
             1    1.0 s   50.0%      1.5 s      1  crates/a/src/lib.rs:6  helper\n   \
             2    0.5 s   25.0%      0.0 s      1  crates/a/src/lib.rs:2  outer\n",
        "four samples at 2 Hz: the nested one charged to `outer`, the body to nothing"
    );
    let root = workspace.root.display();
    assert_eq!(
        std::fs::read_to_string(workspace.root.join("tools.log")).unwrap(),
        format!(
            "cargo nextest list --locked --message-format json --package gandr-a | --cfg \
                 anodized_panic -C force-frame-pointers=yes | {root}/target/spec-cost | \
                 line-tables-only\n\
                 perf record -q -F 2 --call-graph fp -o {root}/target/spec-cost/profiles/0.data -- \
                 {root}/bin/test-binary --exact pick::first --test-threads 1 -q | {root}/crates/a\n\
                 perf script -i {root}/target/spec-cost/profiles/0.data -F ip,sym,srcline --inline \
                 --full-source-path | {root}\n"
        ),
        "an enforcing build with frame pointers and line tables in its own directory; one \
             single-threaded run in the package's directory"
    );
    std::fs::remove_dir_all(&workspace.root).unwrap();
}

#[test]
fn an_unknown_test_is_refused_by_name()
{
    let workspace = Workspace::new(std::path::Path::new("unknown"));
    let output = workspace
        .command()
        .args(["--test", "gandr-a::tests skip::me"])
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(2_i32), "exit 2");
    assert_eq!(
        String::from_utf8_lossy(&output.stderr),
        "spec-cost: building the test binaries for sampling\nspec-cost: `gandr-a::tests` lists \
             no test `skip::me`\n",
        "an ignored test is not one a run would profile"
    );
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        "",
        "nothing on standard output"
    );
    std::fs::remove_dir_all(&workspace.root).unwrap();
}

#[test]
fn an_empty_store_names_nothing_to_profile()
{
    let workspace = Workspace::new(std::path::Path::new("empty"));
    let store = workspace.root.join("store");
    let output = workspace
        .command()
        .arg("--store")
        .arg(&store)
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(2_i32), "exit 2");
    assert_eq!(
        String::from_utf8_lossy(&output.stderr),
        format!(
            "spec-cost: {}: no stored run names an enforcing test; run `mise run ci:timing` \
                 first\n",
            store.display()
        ),
        "the refusal names the store and the task that fills it"
    );
    assert!(
        !workspace.root.join("tools.log").exists(),
        "nothing built or profiled"
    );
    std::fs::remove_dir_all(&workspace.root).unwrap();
}

#[test]
fn a_failing_profile_is_refused_with_its_invocation()
{
    let workspace = Workspace::new(std::path::Path::new("failing"));
    let output = workspace
        .command()
        .env("FAKE_PERF_MODE", "fail")
        .args(["--test", "gandr-a::tests pick::first"])
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(2_i32), "exit 2");
    let root = workspace.root.display();
    assert_eq!(
        String::from_utf8_lossy(&output.stderr),
        format!(
            "spec-cost: building the test binaries for sampling\nspec-cost: profiling \
                 gandr-a::tests pick::first\nspec-cost: `perf record -q -F 2 --call-graph fp -o \
                 {root}/target/spec-cost/profiles/0.data -- {root}/bin/test-binary --exact \
                 pick::first --test-threads 1 -q` failed: exit status: 1\n"
        ),
        "the invocation and its exit status"
    );
    assert_eq!(String::from_utf8_lossy(&output.stdout), "", "no ranking");
    std::fs::remove_dir_all(&workspace.root).unwrap();
}

#[test]
fn a_malformed_invocation_exits_two()
{
    for arguments in [["--tests", "0"], ["--frequency", "0"], [
        "--test",
        "pick::first",
    ]] {
        let output = Command::new(env!("CARGO_BIN_EXE_spec-cost"))
            .args(arguments)
            .output()
            .unwrap();
        assert_eq!(
            output.status.code(),
            Some(2_i32),
            "{arguments:?} is refused"
        );
        assert!(
            !output.stderr.is_empty(),
            "the usage message goes to standard error"
        );
    }
    let help = Command::new(env!("CARGO_BIN_EXE_spec-cost"))
        .arg("--help")
        .output()
        .unwrap();
    assert!(help.status.success(), "help exits 0");
    assert!(
        String::from_utf8_lossy(&help.stdout).contains("BINARY TEST"),
        "help goes to standard output"
    );
}
