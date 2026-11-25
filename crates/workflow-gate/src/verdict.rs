//! The key of the verdict of a check: each input that the verdict reads, as
//! one line of JSON.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use core::fmt;
use std::path::Path;
use std::path::PathBuf;

use crate::call::Part;
use crate::call::Parts;
use crate::call::Program;
use crate::call::Running;
use crate::error::GateError;
use crate::list::Listed;
use crate::name::Check;
use crate::name::Commit;
use crate::name::Scope;
use crate::run::Ground;
use crate::run::Request;
use crate::run::lists_on;
use crate::tables::CheckRow;
use crate::tables::Form;
use crate::tables::Tables;

/// The names of the variables whose values Cargo reads for the flags, the
/// target and the profile of a build.
const FLAGS: [&str; 7] = [
    "RUSTFLAGS",
    "RUSTDOCFLAGS",
    "CARGO_ENCODED_RUSTFLAGS",
    "CARGO_ENCODED_RUSTDOCFLAGS",
    "CARGO_BUILD_RUSTFLAGS",
    "CARGO_BUILD_RUSTDOCFLAGS",
    "CARGO_BUILD_TARGET",
];

/// What a caller asks of one run of keys.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct KeyRequest
{
    /// The checks, in the order of the lines.
    pub checks: Vec<Check>,
    /// The tree of the verdict. Without it, the run reads the tree of `HEAD`.
    pub tree: Option<Commit>,
    /// The base of the change, which `GATE_BASE` names. Without it, a key
    /// binds the empty text as its base.
    pub base: Option<Commit>,
    /// The scope of each check, which `GATE_SCOPE` names, or `--workspace`.
    pub scope: Scope,
    /// The directory of the tables. Without it, the run reads
    /// `.config/gate-scope` of the worktree.
    pub tables: Option<PathBuf>,
}

/// The key of one check: one line of JSON, with the members of each object
/// in the order of their names.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Key(String);

impl AsRef<str> for Key
{
    /// The line, with no newline.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a check of inputs with no record names the hash of
    ///   its key; a hash of another text changes the asserted line.
    /// - witness: `tests::cli::a_check_with_no_record_runs`
    #[inline]
    fn as_ref(&self) -> &str
    {
        &self.0
    }
}

impl fmt::Display for Key
{
    /// Writes the line, with no newline.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the lines of the script for two checks; a line with
    ///   another text changes the asserted output.
    /// - witness: `tests::cli::a_key_is_the_line_of_the_script`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(&self.0)
    }
}

/// The members of a key, declared in the order of their names. A key of
/// inputs holds `inputs` and `base_inputs`, and another key holds `tree` and
/// `base`.
#[derive(Debug, serde::Serialize)]
struct Line<'run>
{
    /// The base of the change, or the empty text.
    #[serde(skip_serializing_if = "Option::is_none")]
    base: Option<&'run str>,
    /// The digest of the inputs at the base, or the empty text.
    #[serde(skip_serializing_if = "Option::is_none")]
    base_inputs: Option<&'run str>,
    /// The check.
    check: &'run str,
    /// The commit of the compiler.
    compiler: &'run str,
    /// Each variable that Cargo reads for a build, with its value.
    flags: &'run BTreeMap<String, String>,
    /// The host, when it is not the target.
    #[serde(skip_serializing_if = "Option::is_none")]
    host: Option<&'run str>,
    /// The digest of the inputs at the tree.
    #[serde(skip_serializing_if = "Option::is_none")]
    inputs: Option<&'run str>,
    /// The revision of the policy.
    policy: &'run str,
    /// The profile that the check builds.
    profile: &'run str,
    /// The scope of the check.
    scope: &'run str,
    /// The target of the build.
    target: &'run str,
    /// Each target feature that the tree reads, on or off.
    target_features: &'run BTreeMap<String, bool>,
    /// The tree.
    #[serde(skip_serializing_if = "Option::is_none")]
    tree: Option<&'run str>,
}

/// The programs whose answers each key of a run shares.
#[derive(Debug)]
pub struct Asked<'run>
{
    /// `rustc -vV`.
    compiler: Running<'run>,
    /// The task that prints the revision of the policy, when no variable
    /// gives it.
    policy: Option<Running<'run>>,
    /// The grep for the target features that the tree reads.
    features: Running<'run>,
}

/// The part of a key that each check of one run shares.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Common
{
    /// The host of the compiler.
    host: String,
    /// The target of the build.
    target: String,
    /// The commit of the compiler.
    compiler: String,
    /// The revision of the policy.
    policy: String,
    /// Each variable that Cargo reads for a build, with its value.
    flags: BTreeMap<String, String>,
    /// Each target feature that the tree reads, on or off.
    target_features: BTreeMap<String, bool>,
}

/// Each variable of the environment that Cargo reads for the flags, the
/// target and the profile of a build.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one entry for each variable whose name is one of [`FLAGS`],
///   `CARGO_PROFILE_` and one or more of `A` to `Z`, `0` to `9` and `_`, or
///   `CARGO_TARGET_`, one or more of those characters and `_RUSTFLAGS`. The
///   value is the whole value of the variable.
/// - provides: the `flags` of a key.
/// - fails: never.
/// - panics: none.
/// - executable: none — the outcome is a value of the environment.
///
/// # Cost
/// - allocation: the name and the value of each such variable, setup
///
/// # Adequacy
/// - hypothesis: L3 — a run with `RUSTFLAGS`, a profile variable, a target
///   variable and a variable of another name; a filter that takes each
///   variable, or that drops the profile, changes the asserted line.
/// - witness: `tests::cli::a_key_holds_each_flag_and_each_feature_of_the_host`
#[inline]
fn flags() -> BTreeMap<String, String>
{
    let upper = |text: &str| {
        !text.is_empty()
            && text
                .bytes()
                .all(|byte| byte.is_ascii_uppercase() || byte.is_ascii_digit() || byte == b'_')
    };
    std::env::vars_os()
        .filter_map(|(name, value)| Some((name.into_string().ok()?, value.into_string().ok()?)))
        .filter(|&(ref name, _)| {
            FLAGS.contains(&name.as_str())
                || name.strip_prefix("CARGO_PROFILE_").is_some_and(upper)
                || name
                    .strip_prefix("CARGO_TARGET_")
                    .and_then(|rest| rest.strip_suffix("_RUSTFLAGS"))
                    .is_some_and(upper)
        })
        .collect()
}

impl<'run> Asked<'run>
{
    /// Starts the programs whose answers each key shares, and waits for none.
    ///
    /// # Specification
    /// - requires: `root` is the root of a worktree of git, and `words` are the
    ///   arguments of the grep for the features at the tree.
    /// - ensures: the compiler `rustc`, the task of the policy when `policy` is
    ///   empty, and the grep run.
    /// - provides: the three programs at the same time as the lists of the run.
    /// - fails: [`GateError::Command`] when a program does not start.
    /// - panics: none.
    /// - executable: none — the outcome is the external processes'.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Cost
    /// - allocation: the command of each process, setup
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a run with a policy in its environment and a `mise`
    ///   that fails; a start of the task with the variable set refuses the run.
    /// - witness: `tests::cli::a_key_is_the_line_of_the_script`
    #[inline]
    pub fn start(
        root: &Path,
        rustc: &'run Program<'run>,
        policy: &'run Program<'run>,
        features: &'run Program<'run>,
    ) -> Result<Self, GateError>
    {
        Ok(Self {
            compiler: rustc.start(root)?,
            policy: std::env::var_os("GATE_VERDICT_POLICY")
                .is_none_or(|given| given.is_empty())
                .then(|| policy.start(root))
                .transpose()?,
            features: features.start(root)?,
        })
    }
}

impl Common
{
    /// Takes the answers of the programs, and asks the compiler for the
    /// features that are on when the tree reads one.
    ///
    /// # Specification
    /// - requires: `asked` holds the programs of [`Asked::start`], and `rustc`
    ///   names the compiler that it started.
    /// - ensures: the host and the commit of the compiler; the target, which is
    ///   `CARGO_BUILD_TARGET` when it is not empty and the host otherwise; the
    ///   policy of `GATE_VERDICT_POLICY`, or of the task; the flags of
    ///   [`flags`]; and each target feature that a source under `crates` reads,
    ///   with `true` when the compiler holds it on under the flags of the host.
    /// - provides: the part of a key that each check of one run shares, read
    ///   one time.
    /// - fails: [`GateError::Command`] when a program fails.
    /// - panics: none.
    /// - intension: the compiler prints its configuration only when the tree
    ///   reads a feature. The flags of the host are the first of these that
    ///   holds: `CARGO_ENCODED_RUSTFLAGS`, `RUSTFLAGS`, the variable of the
    ///   target, the target's table of Cargo, the build table of Cargo.
    /// - executable: none — the outcome is the external processes'.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Cost
    /// - allocation: the texts of the common part and the flags of the host,
    ///   setup
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a tree that reads two features, with a compiler that
    ///   holds one on, and a tree that reads none; a feature that is always
    ///   off, or a host in a native key, changes the asserted line.
    /// - witness: `tests::cli::a_key_holds_each_flag_and_each_feature_of_the_host`
    /// - witness: `tests::cli::a_key_is_the_line_of_the_script`
    #[inline]
    pub fn finish(
        asked: Asked<'_>,
        root: &Path,
        rustc: &Program<'_>,
        parts: &Parts,
    ) -> Result<Self, GateError>
    {
        let word = |text: &str, label: &str| {
            text.lines()
                .find_map(|line| line.strip_prefix(label))
                .and_then(|rest| rest.split_whitespace().next())
                .unwrap_or_default()
                .to_owned()
        };
        let quoted = |line: &str| {
            let name = line.strip_suffix('"')?;
            Some(name.rsplit('"').next()?.to_owned())
        };
        let version = asked.compiler.finish(parts)?;
        let version = String::from_utf8_lossy(version.as_ref());
        let host = word(&version, "host:");
        let target = std::env::var("CARGO_BUILD_TARGET")
            .ok()
            .filter(|given| !given.is_empty())
            .unwrap_or_else(|| host.clone());
        let policy = match asked.policy {
            Some(running) => String::from_utf8_lossy(running.finish(parts)?.as_ref())
                .trim_end_matches('\n')
                .to_owned(),
            None => std::env::var("GATE_VERDICT_POLICY").unwrap_or_default(),
        };
        let found = asked.features.finish(parts)?;
        let read: BTreeSet<String> = String::from_utf8_lossy(found.as_ref())
            .lines()
            .filter_map(quoted)
            .collect();
        let mut on = BTreeSet::new();
        if !read.is_empty() {
            let variable = format!(
                "CARGO_TARGET_{}_RUSTFLAGS",
                target.to_ascii_uppercase().replace(['.', '-'], "_")
            );
            let table = |name: String| {
                let arguments = [
                    "-Zunstable-options",
                    "config",
                    "get",
                    "--format",
                    "json-value",
                    &name,
                ];
                let answer = Program {
                    part: Part::from("cargo config get"),
                    name: "cargo",
                    arguments: &arguments,
                    input: "",
                }
                .start(root)
                .ok()?
                .finish(parts)
                .ok()?;
                serde_json::from_slice::<Vec<String>>(answer.as_ref()).ok()
            };
            let split = |text: String, at: char| {
                text.split(at)
                    .filter(|flag| !flag.is_empty())
                    .map(str::to_owned)
                    .collect::<Vec<String>>()
            };
            let host_flags = std::env::var("CARGO_ENCODED_RUSTFLAGS").map_or_else(
                |_unset| {
                    std::env::var("RUSTFLAGS").map_or_else(
                        |_unset| {
                            std::env::var(&variable)
                                .ok()
                                .filter(|given| !given.is_empty())
                                .map_or_else(
                                    || {
                                        table(format!("target.{target}.rustflags"))
                                            .or_else(|| table("build.rustflags".to_owned()))
                                            .unwrap_or_default()
                                    },
                                    |own| split(own, ' '),
                                )
                        },
                        |plain| split(plain, ' '),
                    )
                },
                |encoded| split(encoded, '\u{1f}'),
            );
            let mut arguments = vec!["--print", "cfg", "--target", target.as_str()];
            arguments.extend(host_flags.iter().map(String::as_str));
            let printed = Program {
                part: Part::from("rustc --print cfg"),
                name: rustc.name,
                arguments: &arguments,
                input: "",
            }
            .start(root)?
            .finish(parts)?;
            on = String::from_utf8_lossy(printed.as_ref())
                .lines()
                .filter(|line| line.starts_with("target_feature=\""))
                .filter_map(quoted)
                .collect();
        }
        Ok(Self {
            compiler: word(&version, "commit-hash:"),
            policy,
            flags: flags(),
            target_features: read
                .into_iter()
                .map(|feature| {
                    let held = on.contains(&feature);
                    (feature, held)
                })
                .collect(),
            host,
            target,
        })
    }
}

/// The digests of the inputs of one check of inputs.
#[derive(Clone, Copy, Debug)]
pub struct Digests<'run>
{
    /// The digest at the tree.
    pub tree: &'run str,
    /// The digest at the base, or the empty text when the run has no digest
    /// at a base.
    pub base: &'run str,
}

impl Common
{
    /// The key of `check` with its `row`, on `tree`, against `base` or no
    /// base, over `scope`.
    ///
    /// # Specification
    /// - requires: `digests` holds the digests of the check when its row is a
    ///   row of a check of inputs.
    /// - ensures: with `digests`, the common part with no tree, and the check,
    ///   the profile, the scope, the digest at the tree as `inputs`, and the
    ///   digest at the base as `base_inputs` when the row reads the base, else
    ///   the empty text. With no `digests`, the common part with the tree, and
    ///   the check, the profile, the scope and the base. The members of each
    ///   object stand in the order of their names.
    /// - provides: one form of the key for the write and for the read of a
    ///   record.
    /// - fails: [`GateError::Read`] when the line does not serialize.
    /// - panics: none.
    /// - executable: none — the reference is the script before this module,
    ///   whose keys the cases pin.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Cost
    /// - allocation: the line, growth within the common part
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the lines of the script for a check of inputs and for
    ///   a check of the tree, with a base and with none; a key that binds the
    ///   tree for a check of inputs, or the base for a row that does not read
    ///   it, changes the asserted line.
    /// - witness: `tests::cli::a_key_is_the_line_of_the_script`
    /// - witness: `tests::cli::a_key_binds_the_base_of_a_check_that_reads_it`
    #[inline]
    pub fn line(
        &self,
        check: &Check,
        row: &CheckRow,
        tree: &Commit,
        base: Option<&Commit>,
        scope: &Scope,
        digests: Option<Digests<'_>>,
    ) -> Result<Key, GateError>
    {
        let line = Line {
            base: digests.is_none().then_some(base.map_or("", Commit::as_ref)),
            base_inputs: digests.map(|held| if row.base { held.base } else { "" }),
            check: check.as_ref(),
            compiler: &self.compiler,
            flags: &self.flags,
            host: (self.host != self.target).then_some(self.host.as_str()),
            inputs: digests.map(|held| held.tree),
            policy: &self.policy,
            profile: &row.profile,
            scope: scope.as_ref(),
            target: &self.target,
            target_features: &self.target_features,
            tree: digests.is_none().then_some(tree.as_ref()),
        };
        serde_json::to_string(&line)
            .map(Key)
            .map_err(|error| GateError::Read {
                what: format!("the key of {check}"),
                reason: error.to_string(),
            })
    }
}

/// The tree of `HEAD`.
///
/// # Specification
/// - requires: the working directory is in a worktree of git.
/// - ensures: the tree that `HEAD:` names, as `HEAD^{tree}` names it.
/// - provides: the tree of a run that names none.
/// - fails: [`GateError::Command`] when git fails.
/// - panics: none.
/// - executable: none — the outcome is the external process's.
///
/// # Errors
/// As `fails` lists.
///
/// # Cost
/// - allocation: the name of the tree, setup
///
/// # Adequacy
/// - hypothesis: L2 — a key with no `--tree` in a scratch repository; the tree
///   of another commit changes the asserted line.
/// - witness: `tests::cli::a_key_is_the_line_of_the_script`
#[inline]
pub fn head_tree(parts: &Parts) -> Result<Commit, GateError>
{
    let answer = Program {
        part: Part::from("git rev-parse"),
        name: "git",
        arguments: &["rev-parse", "HEAD:"],
        input: "",
    }
    .start(Path::new("."))?
    .finish(parts)?;
    Ok(Commit::from(
        String::from_utf8_lossy(answer.as_ref()).trim(),
    ))
}

/// The row of each of `checks`, in their order.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one row for each check, as `verdicts.json` states it.
/// - provides: the profile and the form of each key of a run.
/// - fails: [`GateError::Rowless`] for the first check whose row holds no
///   profile.
/// - panics: none.
/// - executable: none — the outcome is a value.
///
/// # Errors
/// As `fails` lists.
///
/// # Cost
/// - allocation: a copy of each row, growth within the checks
///
/// # Adequacy
/// - hypothesis: L2 — a check with no row; a row with no profile read as a row
///   gives a key with the empty profile and status 0.
/// - witness: `tests::cli::a_check_with_no_row_of_a_verdict_is_refused`
#[inline]
pub fn rows(
    tables: &Tables,
    checks: &[Check],
) -> Result<Vec<CheckRow>, GateError>
{
    checks
        .iter()
        .map(|check| {
            let row = tables.row(check);
            if row.profile.is_empty() {
                Err(GateError::Rowless {
                    check: check.clone(),
                })
            }
            else {
                Ok(row)
            }
        })
        .collect()
}

/// The digest of each check at the first commit of a run, and at its second.
///
/// # Specification
/// - requires: `listed` stands in the order of the commits and then of
///   `checks`.
/// - ensures: the digest of each check at the first commit, and its digest at
///   the second commit when the run holds one.
/// - provides: the digests that a key binds and that a read compares.
/// - fails: never.
/// - panics: none.
/// - executable: none — the outcome is a value.
///
/// # Cost
/// - allocation: two maps of the digests, growth within the lists
///
/// # Adequacy
/// - hypothesis: L2 — a key of a check that reads its base; the digest at the
///   tree in place of the digest at the base changes the asserted line.
/// - witness: `tests::cli::a_key_binds_the_base_of_a_check_that_reads_it`
#[inline]
#[must_use]
pub fn split(
    listed: &[Listed],
    checks: &[Check],
) -> (BTreeMap<String, String>, BTreeMap<String, String>)
{
    let (at_tree, at_base) = listed.split_at(checks.len().min(listed.len()));
    let digests = |part: &[Listed]| {
        part.iter()
            .map(|item| (item.check().to_string(), item.list().digest().to_string()))
            .collect()
    };
    (digests(at_tree), digests(at_base))
}

/// The three programs of the common part of a run's keys: the compiler, the
/// task of the policy, and the grep for the target features of a tree.
#[derive(Debug)]
pub struct Shared<'run>
{
    /// The compiler: `GATE_VERDICT_RUSTC`, or `rustc`.
    compiler: String,
    /// The words of the grep for the target features that a source of the
    /// tree reads.
    features: [&'run str; 8],
}

impl<'run> Shared<'run>
{
    /// The programs of the common part on `tree`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the name of the compiler, setup
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each case of the key names a fake compiler, and a
    ///   tree that reads three features; `rustc` in its place, or a grep of
    ///   another tree, changes the asserted line.
    /// - witness: `tests::cli::a_key_is_the_line_of_the_script`
    /// - witness: `tests::cli::a_key_holds_each_flag_and_each_feature_of_the_host`
    #[inline]
    #[must_use]
    pub fn new(tree: &'run Commit) -> Self
    {
        Self {
            compiler: std::env::var("GATE_VERDICT_RUSTC")
                .unwrap_or_else(|_absent| "rustc".to_owned()),
            features: [
                "grep",
                "-h",
                "-o",
                "-E",
                "target_feature *= *\"[^\"]+\"",
                tree.as_ref(),
                "--",
                ":(top)crates/*.rs",
            ],
        }
    }

    /// The compiler, the task of the policy and the grep, in that order.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the lines of the script; a program with another name
    ///   changes the commit, the policy or the features of each asserted line.
    /// - witness: `tests::cli::a_key_is_the_line_of_the_script`
    #[inline]
    #[must_use]
    pub fn programs(&self) -> [Program<'_>; 3]
    {
        [
            Program {
                part: Part::from("rustc -vV"),
                name: &self.compiler,
                arguments: &["-vV"],
                input: "",
            },
            Program {
                part: Part::from("mise run workflow:revision"),
                name: "mise",
                arguments: &["run", "--quiet", "workflow:revision"],
                input: "",
            },
            Program {
                part: Part::from("git grep (target features)"),
                name: "git",
                arguments: &self.features,
                input: "",
            },
        ]
    }
}

/// The key of each check of `request`, in the order of its checks.
///
/// # Specification
/// - requires: the working directory is in a worktree of git, and `git`,
///   `cargo`, `mise` and the compiler are on the path. `GATE_VERDICT_RUSTC`
///   names another compiler, and `GATE_VERDICT_POLICY` gives the revision of
///   the policy.
/// - ensures: one key for each check, as [`Common::line`] states it. A check of
///   inputs binds the digest of its inputs at the tree over the scope of the
///   request, and their digest at its base when its row reads the base.
/// - provides: the keys of a gate in one run, with one read of the compiler, of
///   the policy, of the crates and of the tasks.
/// - fails: [`GateError::Rowless`] when a check has no profile in
///   `verdicts.json`, and each refusal of [`lists_on`].
/// - panics: none.
/// - intension: the compiler, the task of the policy and the grep for the
///   features start before the lists of the run, and give their answers after
///   them. A run with no check of inputs asks for no list.
/// - executable: none — the outcome is the external processes'.
///
/// # Errors
/// As `fails` lists.
///
/// # Cost
/// - allocation: the common part, the lists and one line for each check, growth
///   within the checks of the request
///
/// # Adequacy
/// - hypothesis: L2 — the lines of the script for a check of inputs and for a
///   check of the tree, with a base and with none; a key that binds the tree
///   for a check of inputs, or the base for a row that does not read it,
///   changes the asserted line.
/// - witness: `tests::cli::a_key_is_the_line_of_the_script`
/// - witness: `tests::cli::a_key_binds_the_base_of_a_check_that_reads_it`
/// - witness: `tests::cli::a_check_with_no_row_of_a_verdict_is_refused`
#[inline]
pub fn keys(
    request: &KeyRequest,
    parts: &Parts,
) -> Result<Vec<Key>, GateError>
{
    let ground = Ground::read(
        &Request {
            commits: Vec::new(),
            checks: Vec::new(),
            scope: request.scope.clone(),
            tables: request.tables.clone(),
        },
        parts,
    )?;
    keys_on(&ground, request, parts)
}

/// The key of each check of `request` on `ground`, as [`keys`] gives it.
///
/// # Specification
/// - requires: `ground` is the ground of the worktree of the run.
/// - ensures: as [`keys`] ensures. The tasks of `ground`, when it holds them,
///   stand in place of a read of mise.
/// - provides: the keys of a write, on the ground and the tasks that the write
///   read one time.
/// - fails: as [`keys`] fails.
/// - panics: none.
/// - executable: none — the outcome is the external processes'.
///
/// # Errors
/// As `fails` lists.
///
/// # Cost
/// - allocation: the common part, the lists and one line for each check, growth
///   within the checks of the request
///
/// # Adequacy
/// - hypothesis: L2 — as [`keys`], and the keys of a write; a write whose key
///   is not the key of the read writes a record that holds no check.
/// - witness: `tests::cli::a_key_is_the_line_of_the_script`
/// - witness: `tests::cli::a_gate_writes_one_record_for_its_checks`
#[inline]
pub fn keys_on(
    ground: &Ground,
    request: &KeyRequest,
    parts: &Parts,
) -> Result<Vec<Key>, GateError>
{
    let tree = match request.tree {
        Some(ref tree) => tree.clone(),
        None => head_tree(parts)?,
    };
    let base = request
        .base
        .as_ref()
        .filter(|given| !AsRef::<str>::as_ref(*given).is_empty());
    let mut asking = Request {
        commits: vec![tree.clone()],
        checks: Vec::new(),
        scope: request.scope.clone(),
        tables: request.tables.clone(),
    };
    let rows = rows(&ground.tables, &request.checks)?;
    for (check, row) in request.checks.iter().zip(&rows) {
        if row.form() == Form::Inputs {
            asking.checks.push(check.clone());
            if let Some(base) = base
                && row.base
                && asking.commits.len() == 1
            {
                asking.commits.push(base.clone());
            }
        }
    }
    let shared = Shared::new(&tree);
    let [rustc, policy, features] = shared.programs();
    // The three programs start before the lists, so they run at the same
    // time as the programs of the lists.
    let asked = Asked::start(&ground.root, &rustc, &policy, &features)?;
    let listed = if asking.checks.is_empty() {
        Vec::new()
    }
    else {
        lists_on(ground.clone(), &asking, parts)?
    };
    let common = Common::finish(asked, &ground.root, &rustc, parts)?;
    let (at_tree, at_base) = split(&listed, &asking.checks);
    request
        .checks
        .iter()
        .zip(&rows)
        .map(|(check, row)| {
            let digests = at_tree.get(check.as_ref()).map(|held| Digests {
                tree: held,
                base: at_base.get(check.as_ref()).map_or("", String::as_str),
            });
            common.line(check, row, &tree, base, &request.scope, digests)
        })
        .collect()
}
