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
