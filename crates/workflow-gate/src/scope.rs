//! The packages of a change: each crate that the change can break.
//!
//! A gate must run only what a change can break. A crate can break when the
//! change touches its directory or a crate that it depends on. So the scope
//! of a change is each touched crate and each crate that depends on one,
//! through a dependency of each kind, until the set does not grow.
//!
//! The table `scope.json` of the crate maps each path outside the crates: a
//! workspace input gives the whole workspace, a source of the corpus gives
//! the crates whose tests read the corpus, and a page gives no crate. A path
//! that no crate and no row holds gives the whole workspace, and the scope
//! names that path. The binary carries the table, so a run reads the table
//! of the binary, not the table of the tree that it judges.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use core::fmt;
use std::path::PathBuf;

use crate::call::Part;
use crate::call::Parts;
use crate::call::Program;
use crate::error::GateError;
use crate::name::Commit;
use crate::tables::Member;
use crate::tables::Workspace;

/// The table of the scope, which the binary carries.
const TABLE: &str = include_str!("../scope.json");

/// The most paths that a whole workspace names as its cause.
const CAUSES: usize = 5;

/// What a row of the table gives to a path that it holds.
#[derive(Clone, Copy, Debug, Eq, PartialEq, serde::Deserialize)]
#[serde(rename_all = "lowercase")]
enum Reach
{
    /// The whole workspace.
    Workspace,
    /// The crates whose tests read the corpus, and their dependents.
    Readers,
    /// No crate.
    None,
}

/// One row of the table: a path and what it gives.
#[derive(Clone, Debug, serde::Deserialize)]
struct Row
{
    /// A file, a directory that ends in `/`, or `**` and the end of a name.
    path: String,
    /// What the row gives to each path that it holds.
    scope: Reach,
}

impl Row
{
    /// Whether the row holds `path`.
    ///
    /// # Specification
    /// trivial.
    fn holds(
        &self,
        path: &str,
    ) -> bool
    {
        self.path.strip_prefix("**").map_or_else(
            || {
                if self.path.ends_with('/') {
                    path.starts_with(self.path.as_str())
                }
                else {
                    path == self.path
                }
            },
            |end| path.ends_with(end),
        )
    }
}

/// The table of the scope.
#[derive(Clone, Debug, serde::Deserialize)]
struct Table
{
    /// The crates whose tests read the corpus.
    readers: Vec<String>,
    /// The rows, in order: the first row that holds a path decides it.
    rows: Vec<Row>,
}

/// The scope of a change.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Scoped
{
    /// The whole workspace, with its causes: the first paths that no crate
    /// holds, or the fact that the set holds each crate.
    Workspace(Vec<String>),
    /// No crate: the change touches no path that a crate reads.
    None,
    /// The crates of the scope, in the order of their names.
    Packages(BTreeSet<String>),
}

impl Scoped
{
    /// The package arguments of Cargo for the scope: `--workspace`, or `-p`
    /// and the name of each crate. No argument for no crate.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: one word for each crate, setup
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a scope of two crates and the whole workspace; a lost
    ///   `-p` or a lost name changes the asserted words.
    /// - witness: `scope::tests::the_arguments_name_each_package_of_the_scope`
    #[inline]
    #[must_use]
    pub fn arguments(&self) -> Vec<String>
    {
        match *self {
            Self::Workspace(_) => vec!["--workspace".to_owned()],
            Self::None => Vec::new(),
            Self::Packages(ref names) => names
                .iter()
                .flat_map(|name| ["-p".to_owned(), name.clone()])
                .collect(),
        }
    }
}

impl fmt::Display for Scoped
{
    /// Writes the line of `gate scope`: `workspace`, `none`, or `packages`
    /// and the names.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a scope of two crates; a lost word changes the
    ///   asserted line.
    /// - witness: `scope::tests::the_arguments_name_each_package_of_the_scope`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Workspace(_) => f.write_str("workspace"),
            Self::None => f.write_str("none"),
            Self::Packages(ref names) => {
                f.write_str("packages")?;
                for name in names {
                    write!(f, " {name}")?;
                }
                Ok(())
            },
        }
    }
}

/// What `gate scope` and `gate scoped` compare: a base and a head.
#[derive(Clone, Debug)]
pub struct ScopeRequest
{
    /// The base of the change.
    pub base: Commit,
    /// The head of the change. With none, the head is the working tree, with
    /// each untracked path that git does not ignore.
    pub head: Option<Commit>,
    /// The touched crates alone, with no dependent.
    pub touched: bool,
}

/// The scope of the paths `changed` over the crates `members`, by `table`.
///
/// # Specification
/// - requires: each path is relative to the root of the workspace.
/// - ensures: the whole workspace when a path is a workspace input, when no
///   crate and no row holds a path, when a reader of the table is no crate, or
///   when the set holds each crate. Else no crate when the set is empty. Else
///   each crate that holds a path and each reader for a path of the corpus.
///   Unless `only_touched` holds, also each crate that depends on one of them,
///   until the set does not grow. The deepest crate directory decides a path in
///   nested crates.
/// - provides: the rule of `gate scope`, apart from the programs.
/// - fails: never.
/// - panics: none.
///
/// # Cost
/// - allocation: the dependents of each crate and the set, growth within the
///   crates of the workspace
///
/// # Adequacy
/// - hypothesis: L2 — one case for each rule of the scope on a workspace of
///   four crates, and each crate of the trunk as a change; a closure that stops
///   at the touched crate, a closure under `only_touched`, or a lost row,
///   changes the asserted scope.
/// - witness: `scope::tests::each_row_of_the_rule_gives_its_scope`
/// - witness: `scope::tests::each_crate_of_the_trunk_brings_each_crate_that_depends_on_it`
/// - witness: `scope::tests::the_touched_scope_of_the_kernel_is_the_kernel_alone`
fn rule(
    changed: &[&str],
    members: &[Member],
    table: &Table,
    only_touched: bool,
) -> Scoped
{
    let names: BTreeSet<&str> = members.iter().map(Member::name).collect();
    let mut causes: Vec<String> = Vec::new();
    let mut touched: BTreeSet<&str> = BTreeSet::new();
    for &path in changed {
        let owner = members
            .iter()
            .filter(|member| {
                !member.dir().is_empty()
                    && path
                        .strip_prefix(member.dir())
                        .is_some_and(|rest| rest.starts_with('/'))
            })
            .max_by_key(|member| member.dir().len());
        if let Some(member) = owner {
            let _new = touched.insert(member.name());
            continue;
        }
        match table.rows.iter().find(|row| row.holds(path)) {
            Some(row) => match row.scope {
                Reach::Workspace => causes.push(format!("{path}: a workspace input")),
                Reach::Readers => {
                    for reader in &table.readers {
                        if names.contains(reader.as_str()) {
                            let _new = touched.insert(reader.as_str());
                        }
                        else {
                            causes.push(format!(
                                "{reader}: a reader of the corpus that is no package"
                            ));
                        }
                    }
                },
                Reach::None => {},
            },
            None => causes.push(format!(
                "{path}: no package and no row of the table hold it"
            )),
        }
    }
    if !causes.is_empty() {
        causes.sort();
        causes.dedup();
        causes.truncate(CAUSES);
        return Scoped::Workspace(causes);
    }
    if touched.is_empty() {
        return Scoped::None;
    }
    let mut set = touched;
    if !only_touched {
        let mut dependents: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
        for member in members {
            for dep in member.deps() {
                dependents
                    .entry(dep.as_str())
                    .or_default()
                    .push(member.name());
            }
        }
        let mut work: Vec<&str> = set.iter().copied().collect();
        while let Some(name) = work.pop() {
            for &dependent in dependents.get(name).into_iter().flatten() {
                if set.insert(dependent) {
                    work.push(dependent);
                }
            }
        }
    }
    if set.len() == members.len() {
        return Scoped::Workspace(vec!["the scope holds each package".to_owned()]);
    }
    Scoped::Packages(set.into_iter().map(str::to_owned).collect())
}

/// The table that the binary carries.
///
/// # Specification
/// trivial.
fn table() -> Result<Table, GateError>
{
    serde_json::from_str(TABLE).map_err(|error| GateError::Read {
        what: "scope.json".to_owned(),
        reason: error.to_string(),
    })
}

/// The scope of the change of `request`.
///
/// # Specification
/// - requires: the working directory is in a git worktree of the workspace.
/// - ensures: the scope of [`rule`] over the paths that differ between the base
///   and the head, and the crates that `cargo metadata` reads in the worktree.
/// - provides: the answer of `gate scope` and the scope of `gate scoped`.
/// - fails: [`GateError::Command`] when git or Cargo fails, and
///   [`GateError::Read`] when an answer or the table does not read.
/// - panics: none.
/// - intension: one `git rev-parse`, then `cargo metadata`, `git diff` and,
///   with no head, `git ls-files` at the same time. The parts of the run show
///   each count.
/// - executable: none — the outcome is the external processes'.
///
/// # Errors
/// As `fails` lists.
///
/// # Cost
/// - allocation: the crates, the paths and the scope, setup
///
/// # Adequacy
/// - hypothesis: L2 — the scope of each crate of the trunk as a change reads
///   the real metadata of the workspace; a lost crate or a lost dependency
///   changes the asserted scope.
/// - witness: `scope::tests::each_crate_of_the_trunk_brings_each_crate_that_depends_on_it`
#[inline]
pub fn scope(
    request: &ScopeRequest,
    parts: &Parts,
) -> Result<Scoped, GateError>
{
    let table = table()?;
    let here = std::env::current_dir().map_err(|error| GateError::Read {
        what: "the working directory".to_owned(),
        reason: error.to_string(),
    })?;
    let top = Program {
        part: Part::from("git rev-parse"),
        name: "git",
        arguments: &["rev-parse", "--show-toplevel"],
        input: "",
    }
    .start(&here)?
    .finish(parts)?;
    let root = PathBuf::from(String::from_utf8_lossy(top.as_ref()).trim());
    let manifest = root.join("Cargo.toml");
    let manifest = manifest.to_string_lossy();
    let metadata = [
        "metadata",
        "--format-version",
        "1",
        "--no-deps",
        "--locked",
        "--manifest-path",
        manifest.as_ref(),
    ];
    let mut diff = vec!["diff", "--no-renames", "--name-only", request.base.as_ref()];
    diff.extend(request.head.as_ref().map(AsRef::as_ref));
    // Each program starts before the run takes an answer, so they run at the
    // same time.
    let cargo = Program {
        part: Part::from("cargo metadata"),
        name: "cargo",
        arguments: &metadata,
        input: "",
    }
    .start(&root)?;
    let git = Program {
        part: Part::from("git diff"),
        name: "git",
        arguments: &diff,
        input: "",
    }
    .start(&root)?;
    let untracked = request
        .head
        .is_none()
        .then(|| {
            Program {
                part: Part::from("git ls-files"),
                name: "git",
                arguments: &["ls-files", "--others", "--exclude-standard"],
                input: "",
            }
            .start(&root)
        })
        .transpose()?;
    let changed = git.finish(parts)?;
    let untracked = untracked.map(|running| running.finish(parts)).transpose()?;
    let workspace = Workspace::read(&cargo.finish(parts)?, &root)?;
    let changed = String::from_utf8_lossy(changed.as_ref());
    let untracked = untracked
        .as_ref()
        .map(|answer| String::from_utf8_lossy(answer.as_ref()));
    let paths: Vec<&str> = changed
        .lines()
        .chain(untracked.iter().flat_map(|text| text.lines()))
        .filter(|path| !path.is_empty())
        .collect();
    Ok(rule(&paths, workspace.members(), &table, request.touched))
}

#[cfg(test)]
mod tests
{
    use alloc::collections::BTreeSet;
    use std::path::Path;
    use std::path::PathBuf;
    use std::process::Command;

    use super::Scoped;
    use super::rule;
    use super::table;
    use crate::call::Answer;
    use crate::tables::Member;
    use crate::tables::Workspace;

    /// A workspace of four crates: `b` depends on `a`, `c` on `b`, and `d`
    /// on nothing; `a` is the one reader of the corpus.
    fn four() -> (Workspace, super::Table)
    {
        let metadata = r#"{"packages":[
            {"name":"a","manifest_path":"/w/crates/a/Cargo.toml","dependencies":[]},
            {"name":"b","manifest_path":"/w/crates/b/Cargo.toml","dependencies":[{"name":"a"}]},
            {"name":"c","manifest_path":"/w/crates/c/Cargo.toml","dependencies":[{"name":"b"},{"name":"serde"}]},
            {"name":"d","manifest_path":"/w/crates/d/Cargo.toml","dependencies":[]}
        ]}"#;
        let workspace =
            Workspace::read(&Answer::from(metadata.as_bytes().to_vec()), Path::new("/w"))
                .expect("the metadata reads");
        let mut table = table().expect("the table of the crate reads");
        table.readers = vec!["a".to_owned()];
        (workspace, table)
    }

    fn packages(names: &[&str]) -> Scoped
    {
        Scoped::Packages(names.iter().map(|&name| name.to_owned()).collect())
    }

    #[test]
    fn each_row_of_the_rule_gives_its_scope()
    {
        let (workspace, table) = four();
        let scope = |changed: &[&str]| rule(changed, workspace.members(), &table, false);
        assert_eq!(
            scope(&["crates/b/src/lib.rs"]),
            packages(&["b", "c"]),
            "a crate brings each crate that depends on it, until the set does not grow"
        );
        assert_eq!(
            scope(&["crates/d/README.md", "crates/d/tests/case.rs"]),
            packages(&["d"]),
            "a page in a crate is a path of the crate"
        );
        assert_eq!(
            scope(&["corpus/model/a.gandr"]),
            packages(&["a", "b", "c"]),
            "a source of the corpus brings the readers and their dependents"
        );
        assert_eq!(
            scope(&["library/std/list.gandr"]),
            packages(&["a", "b", "c"]),
            "a source of the library brings the readers and their dependents"
        );
        for input in [
            "Cargo.toml",
            "Cargo.lock",
            "rust-toolchain.toml",
            "clippy.toml",
            "rustfmt.toml",
            ".config/nextest.toml",
            ".cargo/config.toml",
        ] {
            assert!(
                matches!(scope(&[input, "crates/d/src/lib.rs"]), Scoped::Workspace(ref causes) if causes == &[format!("{input}: a workspace input")]),
                "{input} is a workspace input"
            );
        }
        assert_eq!(
            scope(&["hotpath/policy.toml"]),
            Scoped::Workspace(vec![
                "hotpath/policy.toml: no package and no row of the table hold it".to_owned()
            ]),
            "a path that nothing names gives the whole workspace, and the cause names it"
        );
        assert_eq!(
            scope(&[
                "README.md",
                "crates/README.md",
                "docs/a.md",
                ".github/workflows/x.yml"
            ]),
            Scoped::None,
            "a page out of each crate gives no crate"
        );
        assert_eq!(
            scope(&["crates/a/src/lib.rs", "crates/d/src/lib.rs"]),
            Scoped::Workspace(vec!["the scope holds each package".to_owned()]),
            "a set that holds each crate is the whole workspace"
        );
        let (workspace, mut table) = four();
        table.readers = vec!["gone".to_owned()];
        assert_eq!(
            rule(&["corpus/a.gandr"], workspace.members(), &table, false),
            Scoped::Workspace(vec![
                "gone: a reader of the corpus that is no package".to_owned()
            ]),
            "a reader that is no crate gives the whole workspace"
        );
    }

    #[test]
    fn the_arguments_name_each_package_of_the_scope()
    {
        let scope = packages(&["b", "c"]);
        assert_eq!(scope.to_string(), "packages b c");
        assert_eq!(scope.arguments(), ["-p", "b", "-p", "c"]);
        let whole = Scoped::Workspace(Vec::new());
        assert_eq!(whole.to_string(), "workspace");
        assert_eq!(whole.arguments(), ["--workspace"]);
        assert_eq!(Scoped::None.to_string(), "none");
        assert_eq!(Scoped::None.arguments(), Vec::<String>::new());
    }

    /// The root of the trunk and its crates, from its `cargo metadata`.
    fn trunk() -> (PathBuf, Workspace)
    {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let root = root
            .canonicalize()
            .expect("the root of the workspace resolves");
        let output =
            Command::new(std::env::var("CARGO").unwrap_or_else(|_unset| "cargo".to_owned()))
                .args([
                    "metadata",
                    "--format-version",
                    "1",
                    "--no-deps",
                    "--locked",
                    "--offline",
                ])
                .current_dir(&root)
                .output()
                .expect("cargo metadata starts");
        assert!(output.status.success(), "cargo metadata ends with success");
        let workspace =
            Workspace::read(&Answer::from(output.stdout), &root).expect("the metadata reads");
        (root, workspace)
    }

    /// Whether a Rust source below `dir` names a path that climbs to
    /// `corpus/` or to `library/`.
    fn climbs_to_the_corpus(dir: &Path) -> bool
    {
        let mut work: Vec<PathBuf> = vec![dir.to_path_buf()];
        while let Some(path) = work.pop() {
            let Ok(entries) = std::fs::read_dir(&path)
            else {
                continue;
            };
            for entry in entries.flatten() {
                let path = entry.path();
                if path.is_dir() {
                    if path.file_name().is_some_and(|name| name != "target") {
                        work.push(path);
                    }
                }
                else if path.extension().is_some_and(|extension| extension == "rs")
                    && std::fs::read_to_string(&path)
                        .is_ok_and(|text| text.contains("../corpus") || text.contains("../library"))
                {
                    return true;
                }
            }
        }
        false
    }

    #[test]
    fn each_crate_that_reads_the_corpus_is_in_the_scope_of_the_corpus()
    {
        let (root, workspace) = trunk();
        let table = table().expect("the table of the crate reads");
        let members = workspace.members();
        let Scoped::Packages(scope) = rule(&["corpus/a.gandr"], members, &table, false)
        else {
            panic!("a change of the corpus gives a set of crates");
        };
        // This crate names the two paths in the search, and reads neither.
        let missing: Vec<&str> = members
            .iter()
            .filter(|member| member.name() != env!("CARGO_PKG_NAME"))
            .filter(|member| !scope.contains(member.name()))
            .filter(|member| climbs_to_the_corpus(&root.join(member.dir())))
            .map(Member::name)
            .collect();
        assert_eq!(
            missing,
            Vec::<&str>::new(),
            "a source of these crates reads below `corpus/` or `library/`, so `readers` of \
             `scope.json` names each one, or a crate that it depends on"
        );
    }

    #[test]
    fn the_touched_scope_of_the_kernel_is_the_kernel_alone()
    {
        let (small, rows) = four();
        let touched = |changed: &[&str]| rule(changed, small.members(), &rows, true);
        assert_eq!(touched(&["crates/b/src/lib.rs"]), packages(&["b"]));
        assert_eq!(touched(&["corpus/model/a.gandr"]), packages(&["a"]));
        assert_eq!(
            touched(&["Cargo.lock"]),
            Scoped::Workspace(vec!["Cargo.lock: a workspace input".to_owned()])
        );
        let (_root, workspace) = trunk();
        let table = table().expect("the table of the crate reads");
        let members = workspace.members();
        let kernel = members
            .iter()
            .find(|member| member.dir() == "crates/kernel-term")
            .expect("the trunk has the crate kernel-term");
        let path = "crates/kernel-term/src/lib.rs";
        assert_eq!(
            rule(&[path], members, &table, true),
            packages(&[kernel.name()]),
            "the touched scope has no dependent"
        );
        let Scoped::Packages(crate_scope) = rule(&[path], members, &table, false)
        else {
            panic!("the crate scope of kernel-term is a set of packages");
        };
        let dependents: BTreeSet<&str> = members
            .iter()
            .filter(|member| member.deps().contains(kernel.name()))
            .map(Member::name)
            .collect();
        assert!(
            !dependents.is_empty(),
            "kernel-term has a dependent in the trunk"
        );
        for dependent in dependents {
            assert!(
                crate_scope.contains(dependent),
                "the crate scope has the dependent {dependent}, which the touched scope leaves out"
            );
        }
    }

    #[test]
    fn each_crate_of_the_trunk_brings_each_crate_that_depends_on_it()
    {
        let (_root, workspace) = trunk();
        let table = table().expect("the table of the crate reads");
        let members = workspace.members();
        let names: BTreeSet<&str> = members.iter().map(Member::name).collect();
        for reader in &table.readers {
            assert!(
                names.contains(reader.as_str()),
                "the reader {reader} is a crate"
            );
        }
        for member in members {
            let path = format!("{}/src/lib.rs", member.dir());
            let scope = rule(&[path.as_str()], members, &table, false);
            let Scoped::Packages(ref set) = scope
            else {
                assert!(
                    matches!(scope, Scoped::Workspace(ref causes) if causes == &["the scope holds each package"]),
                    "{} gives the crates or the whole workspace: {scope:?}",
                    member.name()
                );
                continue;
            };
            assert!(
                set.contains(member.name()),
                "{} is in its own scope",
                member.name()
            );
            for dependent in members
                .iter()
                .filter(|other| other.deps().contains(member.name()))
            {
                assert!(
                    set.contains(dependent.name()),
                    "{} depends on {}, so it is in its scope",
                    dependent.name(),
                    member.name()
                );
            }
        }
    }
}
