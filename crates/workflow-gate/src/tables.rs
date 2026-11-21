//! The tables that name the inputs of a check, the crates of the workspace
//! and the tasks of mise.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use std::path::Path;

use crate::call::Answer;
use crate::call::Part;
use crate::error::GateError;
use crate::list::Digest;
use crate::name::Check;
use crate::name::Scope;

/// The refusal of a text that is not the JSON that this crate reads.
///
/// # Specification
/// trivial.
///
/// # Cost
/// - allocation: the name and the reason of the refusal, error path
///
/// # Adequacy
/// - hypothesis: L3 — a refusal names the text that does not read, so another
///   name changes the asserted message.
/// - witness: `tables::tests::a_table_that_is_not_json_is_refused_by_its_name`
#[inline]
fn unread(
    what: Part,
    error: &serde_json::Error,
) -> GateError
{
    GateError::Read {
        what: what.to_string(),
        reason: error.to_string(),
    }
}

/// A crate of the workspace.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Member
{
    /// The package's name.
    name: String,
    /// The crate's directory, relative to the root.
    dir: String,
    /// Each crate of the workspace that the crate depends on, by any kind of
    /// dependency.
    deps: BTreeSet<String>,
}

/// What Cargo's metadata holds of one dependency.
#[repr(transparent)]
#[derive(Debug, serde::Deserialize)]
struct Dependency
{
    /// The name of the package that the dependency names.
    name: String,
}

/// What Cargo's metadata holds of one package.
#[derive(Debug, serde::Deserialize)]
struct Package
{
    /// The package's name.
    name: String,
    /// The absolute path of the package's manifest.
    manifest_path: String,
    /// Each dependency of the package, of any kind.
    dependencies: Vec<Dependency>,
}

/// The packages of Cargo's metadata.
#[repr(transparent)]
#[derive(Debug, serde::Deserialize)]
struct Metadata
{
    /// Each package of the workspace.
    packages: Vec<Package>,
}

/// The crates of the workspace.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Workspace(Vec<Member>);

impl Workspace
{
    /// The crates that `cargo metadata --no-deps` printed as `metadata`, for
    /// the workspace at `root`.
    ///
    /// # Specification
    /// - requires: `root` is the path that Cargo wrote in front of each
    ///   manifest.
    /// - ensures: one crate for each package, with its directory relative to
    ///   `root` and with each of its dependencies that is a package of the
    ///   workspace.
    /// - provides: the crates and the closure of a scope.
    /// - fails: [`GateError::Read`] when `metadata` is not the JSON of Cargo's
    ///   metadata.
    /// - panics: none.
    /// - executable: none — the reference is the script before this crate,
    ///   whose lists the cases pin.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Cost
    /// - allocation: one crate for each package, growth within the packages of
    ///   the metadata
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the list of the script on a workspace of three
    ///   crates; a directory that keeps the root or the manifest's name, or a
    ///   dependency outside the workspace kept as a crate, changes a path of
    ///   the list.
    /// - witness: `tests::cli::a_list_holds_each_input_of_its_scope`
    /// - witness: `tables::tests::a_table_that_is_not_json_is_refused_by_its_name`
    #[inline]
    pub fn read(
        metadata: &Answer,
        root: &Path,
    ) -> Result<Self, GateError>
    {
        let parsed: Metadata = serde_json::from_slice(metadata.as_ref())
            .map_err(|error| unread(Part::from("cargo metadata"), &error))?;
        let prefix = format!("{}/", root.to_string_lossy().trim_end_matches('/'));
        let names: BTreeSet<&str> = parsed
            .packages
            .iter()
            .map(|package| package.name.as_str())
            .collect();
        let mut members = Vec::with_capacity(parsed.packages.len());
        for package in &parsed.packages {
            let manifest = package.manifest_path.as_str();
            let dir = manifest.strip_prefix(prefix.as_str()).unwrap_or(manifest);
            let dir = dir.strip_suffix("/Cargo.toml").unwrap_or(dir);
            let deps = package
                .dependencies
                .iter()
                .filter(|dependency| names.contains(dependency.name.as_str()))
                .map(|dependency| dependency.name.clone())
                .collect();
            members.push(Member {
                name: package.name.clone(),
                dir: dir.to_owned(),
                deps,
            });
        }
        Ok(Self(members))
    }
}

/// One grep of a check: a pattern and the path that the check greps.
#[derive(Clone, Debug, Eq, PartialEq, serde::Deserialize)]
pub struct Grep
{
    /// The pattern, as `git grep -e` reads it.
    pub pattern: String,
    /// The path under which the check greps.
    #[serde(rename = "in")]
    pub within: String,
}

/// The row of one check in `verdicts.json`.
#[derive(Clone, Debug, Default, Eq, PartialEq, serde::Deserialize)]
pub struct CheckRow
{
    /// Whether the check reads its paths from its row of `table.json`.
    #[serde(default)]
    pub table: bool,
    /// Each path of the check's own definition. A row that holds this member
    /// is a row of a check of inputs, as a row of the table is.
    #[serde(default)]
    pub inputs: Option<Vec<String>>,
    /// The profile that the check builds. A row with no profile is no row of
    /// a verdict.
    #[serde(default)]
    pub profile: String,
    /// Whether the verdict of the check reads the base of its change.
    #[serde(default)]
    pub base: bool,
    /// Each grep of the check.
    #[serde(default)]
    pub greps: Vec<Grep>,
}

impl CheckRow
{
    /// What the record of the check binds: the digest of its inputs, when its
    /// row holds `inputs` or it is a row of the table, or else the tree.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a check of inputs and a check of the tree; a check of
    ///   the table read as a check of the tree binds the tree, and the asserted
    ///   line changes.
    /// - witness: `tests::cli::a_key_is_the_line_of_the_script`
    #[inline]
    #[must_use]
    pub const fn form(&self) -> Form
    {
        if self.inputs.is_some() || self.table {
            Form::Inputs
        }
        else {
            Form::Tree
        }
    }
}

/// What the record of a check binds.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Form
{
    /// The digest of the inputs of the check.
    Inputs,
    /// The tree of the run.
    Tree,
}

/// `verdicts.json`: the checks that hold a record of a verdict, and the
/// logins that sign a record.
#[derive(Clone, Debug, Default, Eq, PartialEq, serde::Deserialize)]
struct Verdicts
{
    /// Each login whose signing keys a record verifies against.
    #[serde(default)]
    signers: Vec<String>,
    /// The row of each check, by its name.
    #[serde(default)]
    checks: BTreeMap<String, CheckRow>,
}

/// `inputs.json`: the paths of the workspace's configuration, and the files
/// outside its directory that a crate reads.
#[derive(Clone, Debug, Default, Eq, PartialEq, serde::Deserialize)]
struct Inputs
{
    /// Each path of the workspace's configuration.
    #[serde(default)]
    workspace: Vec<String>,
    /// For a crate, each path outside its directory that it reads.
    #[serde(default)]
    outside: BTreeMap<String, Vec<String>>,
}

/// The two tables of the worktree that name the inputs of a check.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Tables
{
    /// `inputs.json`.
    inputs: Inputs,
    /// `verdicts.json`.
    verdicts: Verdicts,
}

impl Tables
{
    /// The tables whose texts are `inputs` and `verdicts`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the two tables as their texts state them; a key that a text
    ///   does not hold stands as empty.
    /// - provides: the paths of a check and its row.
    /// - fails: [`GateError::Read`] that names `inputs.json` or `verdicts.json`
    ///   when that text is not the JSON of its table.
    /// - panics: none.
    /// - executable: none — the reference is the script before this crate,
    ///   whose lists the cases pin.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Cost
    /// - allocation: the rows of the two tables, setup
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a text of each table that is no JSON; a refusal that
    ///   names the other table changes the asserted message.
    /// - witness: `tables::tests::a_table_that_is_not_json_is_refused_by_its_name`
    /// - witness: `tests::cli::a_list_holds_each_input_of_its_scope`
    #[inline]
    pub fn read(
        inputs: &Answer,
        verdicts: &Answer,
    ) -> Result<Self, GateError>
    {
        Ok(Self {
            inputs: serde_json::from_slice(inputs.as_ref())
                .map_err(|error| unread(Part::from("inputs.json"), &error))?,
            verdicts: serde_json::from_slice(verdicts.as_ref())
                .map_err(|error| unread(Part::from("verdicts.json"), &error))?,
        })
    }

    /// The row of `check` in `verdicts.json`, or the empty row.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: a copy of the row, growth within the row of the check
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the row gives the greps of a check and whether it
    ///   reads the table, so the empty row for each check drops the line of the
    ///   grep and the line of the table.
    /// - witness: `tests::cli::a_list_holds_each_input_of_its_scope`
    /// - witness: `tests::cli::a_table_check_reads_its_row_at_the_commit_and_starts_no_cargo`
    #[inline]
    #[must_use]
    pub fn row(
        &self,
        check: &Check,
    ) -> CheckRow
    {
        self.verdicts
            .checks
            .get(check.as_ref())
            .cloned()
            .unwrap_or_default()
    }

    /// Each login of `signers` in `verdicts.json`, in the order of the table.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a read with no file of allowed signers asks GitHub
    ///   for the keys of each login, so no login asks for none and refuses the
    ///   read; the hosted jobs witness it, and no case reaches GitHub.
    /// - witness: `tests::cli::a_record_with_a_body_of_another_key_does_not_hold`
    #[inline]
    #[must_use]
    pub fn signers(&self) -> &[String]
    {
        &self.verdicts.signers
    }

    /// The paths that the inputs of `check` over `scope` name. A path that
    /// ends in `/` names a directory.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: for a check of the table, the paths of `reads.every` and of
    ///   the check's row in `landing`. For each other check: the directory of
    ///   each crate of the scope and of its dependency closure, the manifest of
    ///   each crate of the workspace, each path of `workspace` in
    ///   `inputs.json`, each path of `outside` for a crate of the closure, and
    ///   each path of the check's `inputs`. The scope is each crate that no
    ///   `--exclude` of `scope` names. The paths stand in the order of their
    ///   bytes, and no path stands two times.
    /// - provides: what a check reads, as the paths whose objects name it.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the reference is the script before this crate,
    ///   whose lists the cases pin.
    ///
    /// # Cost
    /// - allocation: the closure and the paths, growth within the crates of the
    ///   workspace and the rows of the tables
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the lists of the script for the whole workspace, for
    ///   a scope that excludes a crate that a scoped crate needs, and for a
    ///   check of the table; a closure that stops at the scope drops the
    ///   directory of crate `a`, and a manifest list of the closure alone drops
    ///   the manifest of crate `c`.
    /// - witness: `tests::cli::a_list_holds_each_input_of_its_scope`
    /// - witness: `tests::cli::an_excluded_crate_stays_when_a_scoped_crate_needs_it`
    /// - witness: `tests::cli::a_table_check_reads_its_row_at_the_commit_and_starts_no_cargo`
    #[inline]
    #[must_use]
    pub fn paths(
        &self,
        scope: &Scope,
        check: &Check,
        workspace: &Workspace,
        landing: &Table,
    ) -> Vec<String>
    {
        let row = self.row(check);
        let mut out: BTreeSet<String> = BTreeSet::new();
        if row.table {
            if let Some(reads) = landing.reads.as_ref() {
                out.extend(reads.every.iter().flatten().cloned());
                out.extend(
                    reads
                        .checks
                        .get(check.as_ref())
                        .into_iter()
                        .flatten()
                        .cloned(),
                );
            }
            return out.into_iter().collect();
        }
        let by: BTreeMap<&str, &Member> = workspace
            .0
            .iter()
            .map(|member| (member.name.as_str(), member))
            .collect();
        let words: Vec<&str> = scope
            .as_ref()
            .split(' ')
            .filter(|word| !word.is_empty())
            .collect();
        let excluded: BTreeSet<&str> = words
            .windows(2)
            .filter(|pair| pair.first() == Some(&"--exclude"))
            .filter_map(|pair| pair.get(1).copied())
            .collect();
        let mut closure: BTreeSet<&str> = workspace
            .0
            .iter()
            .map(|member| member.name.as_str())
            .filter(|name| !excluded.contains(name))
            .collect();
        let mut work: Vec<&str> = closure.iter().copied().collect();
        while let Some(name) = work.pop() {
            for dep in by
                .get(name)
                .copied()
                .into_iter()
                .flat_map(|member| &member.deps)
            {
                if closure.insert(dep.as_str()) {
                    work.push(dep.as_str());
                }
            }
        }
        for name in &closure {
            out.extend(by.get(name).map(|member| format!("{}/", member.dir)));
            out.extend(
                self.inputs
                    .outside
                    .get(*name)
                    .into_iter()
                    .flatten()
                    .cloned(),
            );
        }
        out.extend(
            workspace
                .0
                .iter()
                .map(|member| format!("{}/Cargo.toml", member.dir)),
        );
        out.extend(self.inputs.workspace.iter().cloned());
        out.extend(row.inputs.unwrap_or_default());
        out.into_iter().collect()
    }
}

/// The lists of `table.json` that a check of the table reads.
#[derive(Clone, Debug, Default, Eq, PartialEq, serde::Deserialize)]
struct Reads
{
    /// The paths that each check reads.
    #[serde(default)]
    every: Option<Vec<String>>,
    /// The paths of each check, by its name.
    #[serde(default)]
    checks: BTreeMap<String, Vec<String>>,
}

/// `table.json` at a commit.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq, serde::Deserialize)]
pub struct Table
{
    /// The lists of the table.
    #[serde(default)]
    reads: Option<Reads>,
}

impl From<&str> for Table
{
    /// The table whose text is `text`. A text that is not the JSON of a table
    /// gives the empty table, as a commit with no table does.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the lists of the table, growth within the text
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the list of the script for a check of the table; the
    ///   empty table for each text drops the two paths of the list.
    /// - witness: `tests::cli::a_table_check_reads_its_row_at_the_commit_and_starts_no_cargo`
    #[inline]
    fn from(text: &str) -> Self
    {
        serde_json::from_str(text).unwrap_or_default()
    }
}

impl Table
{
    /// The line of the table for `check`: the digest of its two lists.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `table:<check>`, a tab, and the SHA-256 of the compact JSON
    ///   `[every, own]` with a newline, where `every` is `reads.every` or
    ///   `null` and `own` is the check's row or the empty list.
    /// - provides: the text of the two lists as an input, so a path that leaves
    ///   a row changes the digest of the check.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the reference is the script before this crate,
    ///   whose line the case pins.
    ///
    /// # Cost
    /// - allocation: the JSON of the two lists and the line, growth within the
    ///   row of the check
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the line of the script for the table of tree one; a
    ///   text with no newline, or with the two lists in the other order,
    ///   changes the pinned digest.
    /// - witness: `tests::cli::a_table_check_reads_its_row_at_the_commit_and_starts_no_cargo`
    #[inline]
    #[must_use]
    pub fn line(
        &self,
        check: &Check,
    ) -> String
    {
        let reads = self.reads.as_ref();
        let every = reads
            .and_then(|lists| lists.every.clone())
            .map_or(serde_json::Value::Null, serde_json::Value::from);
        let own = reads
            .and_then(|lists| lists.checks.get(check.as_ref()))
            .cloned()
            .unwrap_or_default();
        let text = format!(
            "{}\n",
            serde_json::Value::Array(vec![every, serde_json::Value::from(own)])
        );
        format!("table:{check}\t{}", Digest::from(text.as_bytes()))
    }
}

/// The definition of each task, by the task's name, as the text whose digest
/// is an input.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Tasks(BTreeMap<String, String>);

impl Tasks
{
    /// The tasks that `mise tasks ls --json` printed as `listing`.
    ///
    /// # Specification
    /// - requires: the feature `preserve_order` of `serde_json` is off, so an
    ///   object keeps its keys in order.
    /// - ensures: for each task with a name, the compact JSON of its `run`,
    ///   `env`, `tools` and `depends`, with the keys of each object in order. A
    ///   key that the task does not hold stands as `null`.
    /// - provides: what a task runs as an input of its check, with no path of
    ///   the checkout in it.
    /// - fails: [`GateError::Read`] when `listing` is not a JSON list.
    /// - panics: none.
    /// - executable: none — the reference is the script before this crate,
    ///   whose line the case pins.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Cost
    /// - allocation: one definition for each task, growth within the listing
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the line of the script for a task whose `env` is out
    ///   of order and which holds `dir` and `source`; keys as written, or one
    ///   more key in the text, changes the pinned digest.
    /// - witness: `tests::cli::the_task_that_mise_lists_is_an_input`
    /// - witness: `tables::tests::a_table_that_is_not_json_is_refused_by_its_name`
    #[inline]
    pub fn read(listing: &Answer) -> Result<Self, GateError>
    {
        let tasks: Vec<serde_json::Value> = serde_json::from_slice(listing.as_ref())
            .map_err(|error| unread(Part::from("mise tasks ls"), &error))?;
        let mut out = BTreeMap::new();
        for task in &tasks {
            let Some(name) = task.get("name").and_then(serde_json::Value::as_str)
            else {
                continue;
            };
            let mut picked = serde_json::Map::new();
            for key in ["run", "env", "tools", "depends"] {
                let _old = picked.insert(
                    key.to_owned(),
                    task.get(key).cloned().unwrap_or(serde_json::Value::Null),
                );
            }
            let _old = out.insert(
                name.to_owned(),
                serde_json::Value::Object(picked).to_string(),
            );
        }
        Ok(Self(out))
    }

    /// The tasks of `checks`, each with the definition `text`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: one definition for each check, growth within the checks of
    ///   the request
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the line of the script for the definition
    ///   `case-task`; another text changes the pinned digest.
    /// - witness: `tests::cli::a_list_holds_each_input_of_its_scope`
    #[inline]
    #[must_use]
    pub fn fixed(
        checks: &[Check],
        text: &Answer,
    ) -> Self
    {
        let text = String::from_utf8_lossy(text.as_ref());
        Self(
            checks
                .iter()
                .map(|check| (check.as_ref().to_owned(), text.clone().into_owned()))
                .collect(),
        )
    }

    /// The line of the task of `check`: the digest of its definition.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `task:<check>`, a tab, and the SHA-256 of the definition with
    ///   no newline.
    /// - provides: the task's own definition as an input of its check.
    /// - fails: [`GateError::Unlisted`] with the check when no task has its
    ///   name.
    /// - panics: none.
    /// - executable: none — the reference is the script before this crate,
    ///   whose line the cases pin.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Cost
    /// - allocation: the line, growth within the name of the check
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the line of the script for a fixed definition and for
    ///   a listed task, and a check that mise does not list; a line for an
    ///   absent task in place of the refusal changes the exit status.
    /// - witness: `tests::cli::a_list_holds_each_input_of_its_scope`
    /// - witness: `tests::cli::a_check_that_mise_does_not_list_is_refused`
    #[inline]
    pub fn line(
        &self,
        check: &Check,
    ) -> Result<String, GateError>
    {
        let text = self
            .0
            .get(check.as_ref())
            .ok_or_else(|| GateError::Unlisted {
                check: check.clone(),
            })?;
        Ok(format!("task:{check}\t{}", Digest::from(text.as_bytes())))
    }
}

#[cfg(test)]
mod tests
{
    use std::path::Path;

    use super::Tables;
    use super::Tasks;
    use super::Workspace;
    use crate::call::Answer;
    use crate::error::GateError;

    /// The answer whose text is `$text`.
    macro_rules! answer {
        ($text:literal) => {
            Answer::from($text.to_vec())
        };
    }

    /// The name of the text that the refusal of `$result` holds.
    macro_rules! refused {
        ($result:expr) => {
            match $result {
                Err(GateError::Read { what, .. }) => what,
                _ => String::from("no refusal of a read"),
            }
        };
    }

    #[test]
    fn a_table_that_is_not_json_is_refused_by_its_name()
    {
        assert_eq!(
            refused!(Tables::read(&answer!(b"{"), &answer!(b"{}"))),
            "inputs.json"
        );
        assert_eq!(
            refused!(Tables::read(&answer!(b"{}"), &answer!(b"["))),
            "verdicts.json"
        );
        assert_eq!(
            refused!(Workspace::read(&answer!(b"{}"), Path::new("/root"))),
            "cargo metadata"
        );
        assert_eq!(refused!(Tasks::read(&answer!(b"{}"))), "mise tasks ls");
        assert!(Tables::read(&answer!(b"{}"), &answer!(b"{}")).is_ok());
    }
}
