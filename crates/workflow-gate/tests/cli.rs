//! The lists, the digests and the refusals of `gate inputs`, observed by
//! spawning the binary in a scratch repository. The fake `cargo` and the fake
//! `mise` of `tests/fakes` stand first on the path, and `git` is the real one.
//!
//! Each expected list and digest is the answer of the script that the program
//! replaces, on the same trees. So the cases hold the program to that script,
//! and no expected value comes from the program.
//! - see: #8273
//!
//! The scratch workspace holds three crates. Crate `b` depends on crate `a`,
//! and crate `a` reads `extra/data.txt` outside its directory. Tree two
//! differs from tree one by a file of `docs/`, and tree three by a source
//! file of crate `c`. A tree is a pure function of its files, so its name is
//! a constant.
//!
//! The fakes are files of the tree, never written per case: macOS assesses an
//! executable the first time it runs, one at a time across the machine.
//!
//! The process-level cases, in a `cfg(test)` module so the crate's lint wall
//! reads them as test code rather than as shipping code.

use std::path::Path;
use std::path::PathBuf;
use std::process::Command;

/// Tree one: the scratch workspace as `FILES` states it.
const ONE: &str = "db40411e9a70fab95068aaca90076753539c95f7";
/// Tree two: tree one with another text in `docs/a.md`.
const TWO: &str = "1628752a549b6f2336b2c4508ee33dd86b581022";
/// Tree three: tree one with no `needle` in the source of crate `c`.
const THREE: &str = "22f1e2a1570a91bf8c702ba60a02dcc245c6e957";

/// The files of tree one, each a path and its text.
const FILES: [(&str, &str); 12] = [
    ("Cargo.toml", "[workspace]\n"),
    ("Cargo.lock", "version = 4\n"),
    ("crates/a/Cargo.toml", "[package]\nname = \"a\"\n"),
    ("crates/a/src/lib.rs", "// needle\n"),
    ("crates/b/Cargo.toml", "[package]\nname = \"b\"\n"),
    ("crates/b/src/lib.rs", "// b\n"),
    ("crates/c/Cargo.toml", "[package]\nname = \"c\"\n"),
    ("crates/c/src/lib.rs", "// needle\n"),
    (
        ".config/gate-scope/table.json",
        "{\"reads\":{\"every\":[\"Cargo.lock\"],\"checks\":{\"check:table\":[\"docs/\"]}}}\n",
    ),
    (".config/tool/rule.txt", "rule\n"),
    ("docs/a.md", "a\n"),
    ("extra/data.txt", "data\n"),
];

/// What the fake `mise` lists: the two checks of the cases. The first holds
/// its `env` out of order and two keys that are no input.
const TASKS: &str = "[{\"name\":\"check:scoped\",\"run\":[\"echo scoped\"],\"env\":{\"B\":\"2\",\"A\":\"1\"},\
                     \"tools\":{},\"depends\":[\"check:table\"],\"dir\":\"/somewhere\",\"source\":\"/x\"},\
                     {\"name\":\"check:table\",\"run\":[\"echo table\"],\"env\":{},\"tools\":{},\"depends\":[]}]\n";

/// The inputs of `check:scoped` over the workspace at tree one, before the
/// line of its task.
const SCOPED: &str = ".config/tool/\t9d47b4055b71190489529c0afe99c5e3a4918379\n\
                      Cargo.lock\t8b7c362149892ab72701c6e237242ba87a47328b\n\
                      Cargo.toml\tbdaba83374898ab3f40bddc2397fd13e02ce5352\n\
                      crates/a/\t3ad6205a96390460d244655127aaae3598e42dfd\n\
                      crates/a/Cargo.toml\t679b5178e896501767b7d0f64363b42e6ef8724e\n\
                      crates/b/\taa2fe0cf4179996adbc5d3e5842c281dba9810bd\n\
                      crates/b/Cargo.toml\t356b281d4cd39504abedd28fb93162c8812a24f0\n\
                      crates/c/\t2340e47eb61dfd40d21f36c617e49072b1c46425\n\
                      crates/c/Cargo.toml\t63ca64c622aa86b6282f1075d0705766a87b1bb3\n\
                      extra/data.txt\t1269488f7fb1f4b56a8c0e5eb48cecbfadfa9219\n\
                      missing.toml\tabsent\n";

/// The line of a task whose definition is the text `case-task`.
const CASE_TASK: &str = "f7a842d75244f415f5966b16a665e1528774a8e59757c0c25fd03d080520d01d";

/// The line of the grep of `check:scoped` at tree one.
const GREP: &str =
    "grep:crates:needle\te79f432bd03f2ca6b6b1183e54e5e9e55103430dc6f310ebd7484d94ab5bf1e7\n";

/// Runs `git` in `$root` with `$args` and no configuration of the host, and
/// gives what it printed with no last newline.
macro_rules! git {
    ($root:expr, $args:expr) => {{
        let output = Command::new("git")
            .args($args)
            .current_dir(&$root)
            .env("GIT_CONFIG_GLOBAL", "/dev/null")
            .env("GIT_CONFIG_SYSTEM", "/dev/null")
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "git: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        String::from_utf8(output.stdout)
            .unwrap()
            .trim_end()
            .to_owned()
    }};
}

/// Writes `$text` at `$path` under `$root`.
macro_rules! put {
    ($root:expr, $path:expr, $text:expr) => {{
        let file = $root.join($path);
        std::fs::create_dir_all(file.parent().unwrap()).unwrap();
        std::fs::write(file, $text).unwrap();
    }};
}

/// A fresh scratch repository for the case `$name`, which holds the three
/// trees. Beside it stand the answers of the fakes. Gives the repository's
/// root as git names it.
macro_rules! scratch {
    ($name:literal) => {{
        let base = std::env::temp_dir().join(format!("gate-{}-{}", std::process::id(), $name));
        if base.exists() {
            std::fs::remove_dir_all(&base).unwrap();
        }
        let repo = base.join("repo");
        std::fs::create_dir_all(&repo).unwrap();
        let _init = git!(repo, ["init", "--quiet", "--object-format=sha1"]);
        for (path, text) in FILES {
            put!(repo, path, text);
        }
        let _added = git!(repo, ["add", "-A"]);
        assert_eq!(git!(repo, ["write-tree"]), ONE);
        put!(repo, "docs/a.md", "b\n");
        let _added = git!(repo, ["add", "-A"]);
        assert_eq!(git!(repo, ["write-tree"]), TWO);
        put!(repo, "docs/a.md", "a\n");
        put!(repo, "crates/c/src/lib.rs", "// c\n");
        let _added = git!(repo, ["add", "-A"]);
        assert_eq!(git!(repo, ["write-tree"]), THREE);
        let root = PathBuf::from(git!(repo, ["rev-parse", "--show-toplevel"]));
        let at = root.display();
        let metadata = format!(
            "{{\"packages\":[{{\"name\":\"a\",\"manifest_path\":\"{at}/crates/a/Cargo.toml\",\"dependencies\":[]}},\
             {{\"name\":\"b\",\"manifest_path\":\"{at}/crates/b/Cargo.toml\",\"dependencies\":[{{\"name\":\"a\"}},{{\"name\":\"serde\"}}]}},\
             {{\"name\":\"c\",\"manifest_path\":\"{at}/crates/c/Cargo.toml\",\"dependencies\":[]}}]}}\n"
        );
        std::fs::write(base.join("metadata.json"), metadata).unwrap();
        std::fs::write(base.join("tasks.json"), TASKS).unwrap();
        root
    }};
}

/// Runs the binary in the repository `$root` with `$args`, the fakes first
/// on the path. `$task` is the definition that stands for each task, or
/// `None` to ask the fake `mise`. `$metadata` names the answer of the fake
/// `cargo` beside the repository.
macro_rules! gate {
    ($root:expr, $args:expr, $task:expr, $metadata:literal $(,)?) => {{
        let root: &Path = &$root;
        let task: Option<&str> = $task;
        let base = root.parent().unwrap();
        let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
        let mut paths = vec![manifest.join("tests/fakes")];
        paths.extend(std::env::split_paths(
            &std::env::var_os("PATH").unwrap_or_default(),
        ));
        let mut command = Command::new(env!("CARGO_BIN_EXE_gate"));
        let _command = command
            .arg("--tables")
            .arg(manifest.join("tests/tables"))
            .args($args)
            .current_dir(root)
            .env("PATH", std::env::join_paths(paths).unwrap())
            .env("GIT_CONFIG_GLOBAL", "/dev/null")
            .env("GIT_CONFIG_SYSTEM", "/dev/null")
            .env("FAKE_CARGO_METADATA", base.join($metadata))
            .env("FAKE_MISE_TASKS", base.join("tasks.json"))
            .env_remove("GATE_INPUTS_TABLE")
            .env_remove("GATE_INPUTS_TASK");
        if let Some(text) = task {
            let _command = command.env("GATE_INPUTS_TASK", text);
        }
        command.output().unwrap()
    }};
}

/// What the run `$output` printed to standard output.
macro_rules! out {
    ($output:expr) => {
        String::from_utf8_lossy(&$output.stdout).into_owned()
    };
}

/// What the run `$output` printed to standard error.
macro_rules! err {
    ($output:expr) => {
        String::from_utf8_lossy(&$output.stderr).into_owned()
    };
}

#[test]
fn a_list_holds_each_input_of_its_scope()
{
    let root = scratch!("list");
    let output = gate!(
        root,
        ["inputs", "list", ONE, "--workspace", "check:scoped"],
        Some("case-task"),
        "metadata.json"
    );
    assert_eq!(err!(output), "");
    assert_eq!(
        out!(output),
        format!("{SCOPED}task:check:scoped\t{CASE_TASK}\n{GREP}")
    );
    assert!(output.status.success());
}

#[test]
fn an_excluded_crate_stays_when_a_scoped_crate_needs_it()
{
    let root = scratch!("exclude");
    let output = gate!(
        &root,
        &[
            "inputs",
            "list",
            ONE,
            "--workspace --exclude a --exclude c",
            "check:scoped"
        ],
        Some("case-task"),
        "metadata.json",
    );
    assert_eq!(err!(output), "");
    // Crate `b` is in the scope and needs crate `a`, so the directory of `a`
    // and its outside file stay. The directory of `c` leaves, and its
    // manifest stays, as the manifest of each crate does.
    let expected = SCOPED.replace("crates/c/\t2340e47eb61dfd40d21f36c617e49072b1c46425\n", "");
    assert_eq!(
        out!(output),
        format!("{expected}task:check:scoped\t{CASE_TASK}\n{GREP}")
    );
}

#[test]
fn a_table_check_reads_its_row_at_the_commit_and_starts_no_cargo()
{
    let root = scratch!("table");
    // The fake `cargo` fails on a file that does not exist, so a run that
    // starts Cargo is refused.
    let output = gate!(
        root,
        ["inputs", "list", ONE, "--workspace", "check:table"],
        Some("case-task"),
        "no-such.json"
    );
    assert_eq!(err!(output), "");
    assert_eq!(
        out!(output),
        format!(
            "Cargo.lock\t8b7c362149892ab72701c6e237242ba87a47328b\n\
             docs/\t1916a083dfa163cf6c9c0a417959bb15bfd9f0f3\n\
             table:check:table\tc80d070bc2365ab0d2ad0b727bb415a8a0f34bdf11c1bac37bcf1db3d6b390d3\n\
             task:check:table\t{CASE_TASK}\n"
        )
    );
}

#[test]
fn one_run_gives_each_pair_and_two_commits_with_one_tree_share_a_grep()
{
    let root = scratch!("pairs");
    let output = gate!(
        &root,
        &[
            "--times",
            "inputs",
            "digest",
            "--commit",
            ONE,
            "--commit",
            TWO,
            "--check",
            "check:scoped",
            "--check",
            "check:table",
            "--workspace",
        ],
        Some("case-task"),
        "metadata.json",
    );
    // The change of tree two is no input of `check:scoped`, so its digest
    // holds. The table check reads `docs/`, so its digest changes.
    assert_eq!(
        out!(output),
        format!(
            "{ONE}\tcheck:scoped\t1da5e1b97ae3d9d76e605ed5b1fc00b6ed391e3fd0e42a27a5c28b8c1c7d7760\n\
             {ONE}\tcheck:table\t153ec4f0c56706141543a964abc11e739ded62c7603e0be560c6f9576c370050\n\
             {TWO}\tcheck:scoped\t1da5e1b97ae3d9d76e605ed5b1fc00b6ed391e3fd0e42a27a5c28b8c1c7d7760\n\
             {TWO}\tcheck:table\t3b4e522999d9558cb9c21e1329bbba48d3c7352d72b871e8ec6ba998c555d8d3\n"
        )
    );
    let times = err!(output);
    for part in [
        "cargo metadata",
        "git cat-file --batch-check",
        "git cat-file --batch (tables)",
        "git grep",
    ] {
        assert!(
            times.contains(&format!("    1 call(s)  {part}\n")),
            "{part}: {times}"
        );
    }
    assert!(!times.contains("mise"), "{times}");
}

#[test]
fn a_changed_crate_changes_its_digest_and_runs_its_own_grep()
{
    let root = scratch!("changed");
    let output = gate!(
        &root,
        &[
            "--times",
            "inputs",
            "digest",
            "--commit",
            ONE,
            "--commit",
            THREE,
            "--check",
            "check:scoped",
            "--workspace"
        ],
        Some("case-task"),
        "metadata.json",
    );
    assert_eq!(
        out!(output),
        format!(
            "{ONE}\tcheck:scoped\t1da5e1b97ae3d9d76e605ed5b1fc00b6ed391e3fd0e42a27a5c28b8c1c7d7760\n\
             {THREE}\tcheck:scoped\t865b0883c45712526900fbf60a58faff01ffd98c21ce996d20c485fb73d4eca5\n"
        )
    );
    let times = err!(output);
    assert!(times.contains("    2 call(s)  git grep\n"), "{times}");
}

#[test]
fn the_task_that_mise_lists_is_an_input()
{
    let root = scratch!("mise");
    let output = gate!(
        root,
        [
            "--times",
            "inputs",
            "list",
            ONE,
            "--workspace",
            "check:scoped"
        ],
        None,
        "metadata.json"
    );
    // The digest is that of `{depends, env, run, tools}` of the task, compact
    // and with sorted keys, so `dir` and `source` are no input.
    assert_eq!(
        out!(output),
        format!(
            "{SCOPED}task:check:scoped\tef544004efecce85bfd1ba579c4aa318b9371c950ac3fa93785ae66446d15c9a\n{GREP}"
        )
    );
    let times = err!(output);
    assert!(times.contains("    1 call(s)  mise tasks ls\n"), "{times}");
}

#[test]
fn a_check_that_mise_does_not_list_is_refused()
{
    let root = scratch!("unlisted");
    let output = gate!(
        root,
        ["inputs", "list", ONE, "--workspace", "check:other"],
        None,
        "metadata.json"
    );
    assert_eq!(err!(output), "gate: mise holds no task `check:other`\n");
    assert_eq!(out!(output), "");
    assert_eq!(output.status.code(), Some(2_i32));
}

#[test]
fn a_failed_cargo_is_refused_by_its_command()
{
    let root = scratch!("cargo");
    let output = gate!(
        root,
        ["inputs", "list", ONE, "--workspace", "check:scoped"],
        Some("case-task"),
        "no-such.json"
    );
    let refusal = err!(output);
    assert!(
        refusal.starts_with(
            "gate: cargo metadata --format-version 1 --no-deps --locked --manifest-path "
        ),
        "{refusal}"
    );
    assert!(refusal.contains(" failed: "), "{refusal}");
    assert_eq!(out!(output), "");
    assert_eq!(output.status.code(), Some(2_i32));
}

/// The tree of the first scratch tree with a source that reads three target
/// features.
const FEATURES: &str = "bc770d33648370215a6fd46c39d255d410dcab58";

/// What each key of the cases holds between its check and its inputs: the
/// commit of the fake compiler, and no flag.
const PLAIN: &str = "\"compiler\":\"0123456789abcdef0123456789abcdef01234567\",\"flags\":{}";

/// What each key of the cases holds after its inputs, with the profile of the
/// rows of inputs.
const REST: &str = "\"policy\":\"case-policy\",\"profile\":\"case\",\"scope\":\"--workspace\",\"target\":\"\
                    case-host\",\"target_features\":{}}";

/// The digest of the inputs of `check:scoped` at the first and at the second
/// scratch tree, which differ in `docs/` alone.
const SCOPED_DIGEST: &str = "1da5e1b97ae3d9d76e605ed5b1fc00b6ed391e3fd0e42a27a5c28b8c1c7d7760";

/// The digest of the inputs of `check:table` at the first scratch tree.
const TABLE_DIGEST: &str = "153ec4f0c56706141543a964abc11e739ded62c7603e0be560c6f9576c370050";

/// Runs `gate verdict key` with `$args` in `$root`, with the fakes on the
/// path, the fake compiler, a fixed policy and the variables of `$env`. The
/// environment holds nothing else, so no flag of the host that runs the case
/// enters a key.
macro_rules! key {
    ($root:expr, $args:expr, $env:expr $(,)?) => {{
        let root: &Path = &$root;
        let base = root.parent().unwrap();
        let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
        let mut paths = vec![manifest.join("tests/fakes")];
        paths.extend(std::env::split_paths(
            &std::env::var_os("PATH").unwrap_or_default(),
        ));
        let variables: &[(&str, &str)] = &$env;
        Command::new(env!("CARGO_BIN_EXE_gate"))
            .arg("--tables")
            .arg(manifest.join("tests/tables"))
            .args(["verdict", "key"])
            .args($args)
            .current_dir(root)
            .env_clear()
            .env("PATH", std::env::join_paths(paths).unwrap())
            .env("GIT_CONFIG_GLOBAL", "/dev/null")
            .env("GIT_CONFIG_SYSTEM", "/dev/null")
            .env("FAKE_CARGO_METADATA", base.join("metadata.json"))
            .env("FAKE_MISE_TASKS", base.join("tasks.json"))
            .env("GATE_INPUTS_TASK", "case-task")
            .env("GATE_VERDICT_RUSTC", manifest.join("tests/fakes/rustc"))
            .env("GATE_VERDICT_POLICY", "case-policy")
            .envs(variables.iter().copied())
            .output()
            .unwrap()
    }};
}

#[test]
fn a_key_is_the_line_of_the_script()
{
    let root = scratch!("key");
    // The fake `mise` fails on `mise run`, so a run that asks the task for
    // the policy is refused.
    let output = key!(root, ["--tree", ONE, "check:scoped", "check:tree"], []);
    assert_eq!(err!(output), "");
    assert_eq!(
        out!(output),
        format!(
            "{{\"base_inputs\":\"\",\"check\":\"check:scoped\",{PLAIN},\"inputs\":\"{SCOPED_DIGEST}\",{REST}\n\
             {{\"base\":\"\",\"check\":\"check:tree\",{PLAIN},\"policy\":\"case-policy\",\"profile\":\"test\",\
             \"scope\":\"--workspace\",\"target\":\"case-host\",\"target_features\":{{}},\"tree\":\"{ONE}\"}}\n"
        )
    );
    assert!(output.status.success());
}

#[test]
fn a_key_binds_the_base_of_a_check_that_reads_it()
{
    let root = scratch!("key-base");
    let output = key!(
        root,
        ["--tree", ONE, "check:scoped", "check:table", "check:tree"],
        [("GATE_BASE", TWO)]
    );
    assert_eq!(err!(output), "");
    // The row of `check:scoped` reads its base, and the row of `check:table`
    // does not. A check of the tree binds the base as it stands.
    assert_eq!(
        out!(output),
        format!(
            "{{\"base_inputs\":\"{SCOPED_DIGEST}\",\"check\":\"check:scoped\",{PLAIN},\"inputs\":\"{SCOPED_DIGEST}\",\
             {REST}\n{{\"base_inputs\":\"\",\"check\":\"check:table\",{PLAIN},\"inputs\":\"{TABLE_DIGEST}\",{REST}\n\
             {{\"base\":\"{TWO}\",\"check\":\"check:tree\",{PLAIN},\"policy\":\"case-policy\",\"profile\":\"test\",\
             \"scope\":\"--workspace\",\"target\":\"case-host\",\"target_features\":{{}},\"tree\":\"{ONE}\"}}\n"
        )
    );
}

#[test]
fn a_key_holds_each_flag_and_each_feature_of_the_host()
{
    let root = scratch!("key-flags");
    put!(root, "crates/c/src/lib.rs", "// needle\n");
    put!(
        root,
        "crates/a/src/feature.rs",
        "#[cfg(target_feature = \"avx2\")]\n#[cfg(target_feature=\"fma\")]\n#[cfg(any(target_feature = \"neon\", \
         target_feature = \"avx2\"))]\n"
    );
    let _added = git!(root, ["add", "-A"]);
    assert_eq!(git!(root, ["write-tree"]), FEATURES);
    let output = key!(root, ["--tree", FEATURES, "check:tree"], [
        ("RUSTFLAGS", "-Ccase-flag"),
        ("CARGO_PROFILE_DEV_DEBUG", "0"),
        ("CARGO_TARGET_CASE_RUSTFLAGS", "-Cother"),
        ("OTHER_RUSTFLAGS", "no"),
        ("CARGO_BUILD_TARGET", "case-target"),
    ]);
    assert_eq!(err!(output), "");
    // The fake compiler holds `fma` on only with the flag of `RUSTFLAGS`, and
    // it holds no `neon`. The target is not the host, so the key names the
    // host. `OTHER_RUSTFLAGS` is no variable that Cargo reads.
    assert_eq!(
        out!(output),
        format!(
            "{{\"base\":\"\",\"check\":\"check:tree\",\"compiler\":\"0123456789abcdef0123456789abcdef01234567\",\"flags\":\
             {{\"CARGO_BUILD_TARGET\":\"case-target\",\"CARGO_PROFILE_DEV_DEBUG\":\"0\",\"CARGO_TARGET_CASE_RUSTFLAGS\":\"\
             -Cother\",\"RUSTFLAGS\":\"-Ccase-flag\"}},\"host\":\"case-host\",\"policy\":\"case-policy\",\"profile\":\"test\",\
             \"scope\":\"--workspace\",\"target\":\"case-target\",\"target_features\":{{\"avx2\":true,\"fma\":true,\"neon\":\
             false}},\"tree\":\"{FEATURES}\"}}\n"
        )
    );
}

#[test]
fn a_check_with_no_row_of_a_verdict_is_refused()
{
    let root = scratch!("key-rowless");
    let output = key!(root, ["--tree", ONE, "check:other"], []);
    assert_eq!(
        err!(output),
        "gate: check:other holds no row in verdicts.json\n"
    );
    assert_eq!(out!(output), "");
    assert_eq!(output.status.code(), Some(2_i32));
}

/// Runs `git commit-tree` in `$root` for the tree `$tree` with the words of
/// `$more`, as a fixed author, and gives the commit.
macro_rules! commit {
    ($root:expr, $tree:expr, $more:expr $(,)?) => {{
        let more: &[&str] = &$more;
        let mut words = vec![
            "-c",
            "user.name=case",
            "-c",
            "user.email=case@example.invalid",
            "commit-tree",
            $tree,
        ];
        words.extend_from_slice(more);
        git!($root, words)
    }};
}

/// The first `$count` characters of `$text`, as a line of a read shows a
/// name.
macro_rules! cut {
    ($text:expr, $count:literal) => {
        $text.get(.. $count).unwrap()
    };
}

/// The first 16 digits of the SHA-256 of `$text`: the last part of the ref
/// of a record whose key is the text.
macro_rules! hash {
    ($text:expr) => {{
        use std::io::Write as _;
        let mut child = Command::new("sha256sum")
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .spawn()
            .unwrap();
        child
            .stdin
            .take()
            .unwrap()
            .write_all($text.as_bytes())
            .unwrap();
        let output = child.wait_with_output().unwrap();
        cut!(String::from_utf8(output.stdout).unwrap(), 16).to_owned()
    }};
}

/// Runs `gate verdict read` with `$args` in `$root`, as `key!` runs a key.
/// The remote of the records is the bare repository `remote.git` beside the
/// repository, and the file of allowed signers is `signers` there.
macro_rules! read {
    ($root:expr, $args:expr, $env:expr $(,)?) => {{
        let root: &Path = &$root;
        let base = root.parent().unwrap();
        let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
        let mut paths = vec![manifest.join("tests/fakes")];
        paths.extend(std::env::split_paths(
            &std::env::var_os("PATH").unwrap_or_default(),
        ));
        let variables: &[(&str, &str)] = &$env;
        Command::new(env!("CARGO_BIN_EXE_gate"))
            .arg("--tables")
            .arg(manifest.join("tests/tables"))
            .args(["verdict", "read"])
            .args($args)
            .current_dir(root)
            .env_clear()
            .env("PATH", std::env::join_paths(paths).unwrap())
            .env("GIT_CONFIG_GLOBAL", "/dev/null")
            .env("GIT_CONFIG_SYSTEM", "/dev/null")
            .env("FAKE_CARGO_METADATA", base.join("metadata.json"))
            .env("FAKE_MISE_TASKS", base.join("tasks.json"))
            .env("GATE_INPUTS_TASK", "case-task")
            .env("GATE_VERDICT_RUSTC", manifest.join("tests/fakes/rustc"))
            .env("GATE_VERDICT_POLICY", "case-policy")
            .env("GATE_VERDICT_REMOTE", base.join("remote.git"))
            .env("GATE_VERDICT_SIGNERS", base.join("signers"))
            .envs(variables.iter().copied())
            .output()
            .unwrap()
    }};
}

/// A scratch repository for the case `$name` with a bare remote of records
/// beside it and an empty file of allowed signers.
macro_rules! remote {
    ($name:literal) => {{
        let root = scratch!($name);
        let base = root.parent().unwrap().to_path_buf();
        let _bare = git!(base, [
            "init",
            "--quiet",
            "--bare",
            "--object-format=sha1",
            "remote.git"
        ]);
        std::fs::write(base.join("signers"), "").unwrap();
        root
    }};
}

/// Points `HEAD` of `$root` at the commit `$commit`.
macro_rules! head {
    ($root:expr, $commit:expr) => {{
        let commit: &str = &$commit;
        let _moved = git!($root, ["update-ref", "HEAD", commit]);
    }};
}

/// Sends each of `$refspecs` from `$root` to the bare remote beside it.
macro_rules! push {
    ($root:expr, $refspecs:expr) => {{
        let refspecs: &[String] = &$refspecs;
        let remote = $root
            .parent()
            .unwrap()
            .join("remote.git")
            .display()
            .to_string();
        let mut words = vec!["push", "--quiet", remote.as_str()];
        words.extend(refspecs.iter().map(String::as_str));
        let _pushed = git!($root, words);
    }};
}

#[test]
fn a_check_with_the_inputs_of_its_base_holds_with_no_remote()
{
    let root = scratch!("read-base");
    let base = commit!(root, TWO, ["-m", "base"]);
    let head = commit!(root, ONE, ["-p", base.as_str(), "-m", "head"]);
    head!(root, head);
    // Trees one and two differ in `docs/` alone, which is no input of the
    // check. The run has no remote and no compiler, so a call of either
    // refuses it.
    let output = read!(root, ["check:scoped"], [
        ("GATE_BASE", base.as_str()),
        ("GATE_VERDICT_TRUNK_OK", base.as_str()),
        ("GATE_VERDICT_SCOPE", "--workspace"),
        ("GATE_VERDICT_REMOTE", "/nonexistent/remote.git"),
        ("GATE_VERDICT_RUSTC", "/nonexistent/rustc"),
    ]);
    assert_eq!(
        err!(output),
        format!(
            "verdict: check:scoped holds on {}: its inputs are those of the base {}, which passed, so the \
             check does not run again\n",
            cut!(ONE, 12),
            cut!(base, 12)
        )
    );
    assert_eq!(output.status.code(), Some(0_i32));
}

#[test]
fn a_change_of_a_task_holds_no_check_by_its_base()
{
    let root = remote!("read-task");
    // The index of the scratch holds tree three, and the change adds a task
    // file to it.
    let base = commit!(root, THREE, ["-m", "base"]);
    put!(root, ".config/mise/tasks/case.toml", "[case]\n");
    let _added = git!(root, ["add", "-A"]);
    let tree = git!(root, ["write-tree"]);
    let head = commit!(root, tree.as_str(), ["-p", base.as_str(), "-m", "head"]);
    head!(root, head);
    let key = out!(key!(root, ["--tree", tree.as_str(), "check:scoped"], [(
        "GATE_BASE",
        base.as_str()
    )]));
    let output = read!(root, ["check:scoped"], [
        ("GATE_BASE", base.as_str()),
        ("GATE_VERDICT_TRUNK_OK", base.as_str()),
        ("GATE_VERDICT_SCOPE", "--workspace"),
    ]);
    // The task file is no input of the check, so its digest at the head is
    // its digest at the base. The change of a task still holds no check.
    assert_eq!(
        err!(output),
        format!(
            "verdict: no record binds the inputs of check:scoped in this run, {}\n\
             verdict: no record holds check:scoped on {}, so the job runs them\n",
            hash!(key.trim_end()),
            cut!(tree, 12)
        )
    );
    assert_eq!(output.status.code(), Some(1_i32));
}

#[test]
fn a_base_that_the_trunk_does_not_hold_holds_no_check()
{
    let root = remote!("read-trunk");
    let base = commit!(root, TWO, ["-m", "base"]);
    let head = commit!(root, ONE, ["-p", base.as_str(), "-m", "head"]);
    head!(root, head);
    let key = out!(key!(root, ["--tree", ONE, "check:scoped"], [(
        "GATE_BASE",
        base.as_str()
    )]));
    let output = read!(root, ["check:scoped"], [
        ("GATE_BASE", base.as_str()),
        ("GATE_VERDICT_TRUNK_OK", ""),
        ("GATE_VERDICT_SCOPE", "--workspace"),
    ]);
    assert_eq!(
        err!(output),
        format!(
            "verdict: no record binds the inputs of check:scoped in this run, {}\n\
             verdict: no record holds check:scoped on {}, so the job runs them\n",
            hash!(key.trim_end()),
            cut!(ONE, 12)
        )
    );
    assert_eq!(output.status.code(), Some(1_i32));
}

#[test]
fn a_check_with_no_record_runs()
{
    let root = remote!("read-none");
    let head = commit!(root, ONE, ["-m", "head"]);
    head!(root, head);
    let key = out!(key!(root, ["--tree", ONE, "check:scoped"], []));
    // The listing names the check by its prefix, so it gives this record of
    // another key too, and the read must not take it.
    let other = commit!(root, ONE, [
        "-m",
        "verdict: check:scoped passes",
        "-m",
        key.trim_end()
    ]);
    push!(root, [format!(
        "{other}:refs/verdicts/inputs/check-scoped/0123456789abcdef"
    )]);
    let output = read!(root, ["check:scoped", "check:tree"], [(
        "GATE_VERDICT_SCOPE",
        "--workspace"
    )]);
    assert_eq!(
        err!(output),
        format!(
            "verdict: no record binds the inputs of check:scoped in this run, {}\n\
             verdict: no record holds check:scoped check:tree on {}, so the job runs them\n",
            hash!(key.trim_end()),
            cut!(ONE, 12)
        )
    );
    assert_eq!(output.status.code(), Some(1_i32));
}

#[test]
fn a_record_with_a_body_of_another_key_does_not_hold()
{
    let root = remote!("read-forged");
    let base = commit!(root, TWO, ["-m", "base"]);
    let head = commit!(root, ONE, ["-p", base.as_str(), "-m", "head"]);
    head!(root, head);
    let key = out!(key!(root, ["--tree", ONE, "check:tree"], [(
        "GATE_BASE",
        base.as_str()
    )]));
    let key = key.trim_end();
    let forged = key.replace("case-policy", "other-policy");
    let record = commit!(root, ONE, [
        "-m",
        "verdict: check:tree passes",
        "-m",
        forged.as_str()
    ]);
    push!(root, [format!(
        "{record}:refs/verdicts/{ONE}/check-tree/{}",
        hash!(key)
    )]);
    let output = read!(root, ["check:tree"], [
        ("GATE_BASE", base.as_str()),
        ("GATE_VERDICT_TRUNK_OK", base.as_str()),
        ("GATE_VERDICT_SCOPE", "--workspace"),
    ]);
    assert_eq!(
        err!(output),
        format!(
            "verdict: the record {} of check:tree does not hold: its body is not the run's key\n\
             verdict: no record holds check:tree on {}, so the job runs them\n",
            hash!(key),
            cut!(ONE, 12)
        )
    );
    assert_eq!(output.status.code(), Some(1_i32));
}

#[test]
fn a_record_of_the_tree_holds_against_its_own_base()
{
    let root = remote!("read-signed");
    let dir = root.parent().unwrap().to_path_buf();
    // The base changes crate `c` against the head, so the check of inputs
    // does not hold by its base and reads its record.
    let earlier = commit!(root, TWO, ["-m", "earlier base"]);
    let base = commit!(root, THREE, ["-p", earlier.as_str(), "-m", "base"]);
    let head = commit!(root, ONE, ["-p", base.as_str(), "-m", "head"]);
    head!(root, head);
    let signing = dir.join("signing");
    let made = Command::new("ssh-keygen")
        .args(["-q", "-t", "ed25519", "-N", "", "-C", "case", "-f"])
        .arg(&signing)
        .output()
        .unwrap();
    assert!(made.status.success(), "ssh-keygen: {}", err!(made));
    let public = std::fs::read_to_string(dir.join("signing.pub")).unwrap();
    std::fs::write(
        dir.join("signers"),
        format!("case@example.invalid namespaces=\"git\" {public}"),
    )
    .unwrap();
    // The record of the tree passed on the earlier base, with the scope that
    // the scope script gives against that base.
    let earlier_scope = format!("--workspace --exclude base-{}", cut!(earlier, 7));
    let tree_key = out!(key!(root, ["--tree", ONE, "check:tree"], [
        ("GATE_BASE", earlier.as_str()),
        ("GATE_SCOPE", earlier_scope.as_str()),
    ]));
    let tree_key = tree_key.trim_end();
    let signing_key = format!("user.signingkey={}", signing.display());
    let signed = git!(root, [
        "-c",
        "user.name=case",
        "-c",
        "user.email=case@example.invalid",
        "-c",
        "gpg.format=ssh",
        "-c",
        signing_key.as_str(),
        "commit-tree",
        "-S",
        ONE,
        "-m",
        "verdict: check:tree passes",
        "-m",
        tree_key,
    ]);
    // The record of the inputs binds the run's own key, and no one signed
    // it. So the one batch of signatures fails, and each record asks alone.
    let own_scope = format!("--workspace --exclude base-{}", cut!(base, 7));
    let inputs_key = out!(key!(root, ["--tree", ONE, "check:scoped"], [
        ("GATE_BASE", base.as_str()),
        ("GATE_SCOPE", own_scope.as_str()),
    ]));
    let inputs_key = inputs_key.trim_end();
    let unsigned = commit!(root, ONE, [
        "-m",
        "verdict: check:scoped passes",
        "-m",
        inputs_key
    ]);
    push!(root, [
        format!(
            "{signed}:refs/verdicts/{ONE}/check-tree/{}",
            hash!(tree_key)
        ),
        format!(
            "{unsigned}:refs/verdicts/inputs/check-scoped/{}",
            hash!(inputs_key)
        ),
    ]);
    let trunk = format!("{earlier} {base}");
    let output = read!(root, ["check:scoped", "check:tree"], [
        ("GATE_BASE", base.as_str()),
        ("GATE_VERDICT_TRUNK_OK", trunk.as_str()),
    ]);
    let said = err!(output);
    let lines: Vec<&str> = said.lines().collect();
    assert_eq!(lines.len(), 3, "{said}");
    assert!(
        lines[0].starts_with(&format!(
            "verdict: the record {} of check:scoped does not hold: its signature does not verify: ",
            hash!(inputs_key)
        )),
        "{said}"
    );
    assert_eq!(
        lines[1],
        format!(
            "verdict: check:tree holds on {}: the record {} binds this run's key, so the check does not \
             run again",
            cut!(ONE, 12),
            cut!(signed, 12)
        )
    );
    assert_eq!(
        lines[2],
        format!(
            "verdict: no record holds check:scoped on {}, so the job runs them",
            cut!(ONE, 12)
        )
    );
    assert_eq!(output.status.code(), Some(1_i32));
}
