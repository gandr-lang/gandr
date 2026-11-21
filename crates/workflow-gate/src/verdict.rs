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
use crate::name::Check;
use crate::name::Commit;
use crate::name::Scope;
use crate::run::Ground;
use crate::run::Request;
use crate::run::lists;

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
    /// The directory of the tables. Without it, the run reads
    /// `.config/gate-scope` of the worktree.
    pub tables: Option<PathBuf>,
}

/// The key of one check: one line of JSON, with the members of each object
/// in the order of their names.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Key(String);

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
struct Asked<'run>
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
struct Common
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
///   value is the text before its first newline.
/// - provides: the `flags` of a key, as the script filters them.
/// - fails: never.
/// - panics: none.
/// - executable: none — the reference is the script before this module, whose
///   keys the cases pin.
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
    // economy: a value with a newline gives the script one line of `env` for
    // each of its lines, and this filter reads its first line alone. ceiling:
    // a host whose flags hold a newline needs the script's reading of the
    // lines after the first, until #8279 takes the script's key out.
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
        .map(|(name, value)| {
            let line = value.lines().next().unwrap_or_default().to_owned();
            (name, line)
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
    fn start(
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
    fn finish(
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

/// The key of each check of `request`, in the order of its checks.
///
/// # Specification
/// - requires: the working directory is in a worktree of git, and `git`,
///   `cargo`, `mise` and the compiler are on the path. `GATE_VERDICT_RUSTC`
///   names another compiler, and `GATE_VERDICT_POLICY` gives the revision of
///   the policy.
/// - ensures: one key for each check. A check whose row holds `inputs`, or is a
///   row of the table, binds the digest of its inputs at the tree over
///   `GATE_SCOPE`, or over `--workspace`. It binds their digest at `GATE_BASE`
///   too when its row reads the base, and the empty text otherwise. Another
///   check binds the tree and `GATE_BASE`. Each key is the line that the script
///   before this module printed for its check.
/// - provides: the keys of a gate in one run, with one read of the compiler, of
///   the policy, of the crates and of the tasks.
/// - fails: [`GateError::Rowless`] when a check has no profile in
///   `verdicts.json`, and each refusal of [`lists`].
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
    let here = Path::new(".");
    let tree = if let Some(ref tree) = request.tree {
        tree.clone()
    }
    else {
        // `HEAD:` names the tree of `HEAD`, as `HEAD^{tree}` does.
        let answer = Program {
            part: Part::from("git rev-parse"),
            name: "git",
            arguments: &["rev-parse", "HEAD:"],
            input: "",
        }
        .start(here)?
        .finish(parts)?;
        Commit::from(String::from_utf8_lossy(answer.as_ref()).trim())
    };
    let base = std::env::var("GATE_BASE").unwrap_or_default();
    let scope = std::env::var("GATE_SCOPE")
        .ok()
        .filter(|given| !given.is_empty())
        .unwrap_or_else(|| "--workspace".to_owned());
    let mut asking = Request {
        commits: vec![tree.clone()],
        checks: Vec::new(),
        scope: Scope::from(scope.as_str()),
        tables: request.tables.clone(),
    };
    let Ground { root, tables } = Ground::read(&asking, parts)?;
    let mut rows = Vec::with_capacity(request.checks.len());
    for check in &request.checks {
        let row = tables.row(check);
        if row.profile.is_empty() {
            return Err(GateError::Rowless {
                check: check.clone(),
            });
        }
        if row.inputs.is_some() || row.table {
            asking.checks.push(check.clone());
            if row.base && !base.is_empty() && asking.commits.len() == 1 {
                asking.commits.push(Commit::from(base.as_str()));
            }
        }
        rows.push(row);
    }
    let named = std::env::var("GATE_VERDICT_RUSTC").unwrap_or_else(|_absent| "rustc".to_owned());
    let pattern = format!("{tree}");
    let words = [
        "grep",
        "-h",
        "-o",
        "-E",
        "target_feature *= *\"[^\"]+\"",
        pattern.as_str(),
        "--",
        ":(top)crates/*.rs",
    ];
    let rustc = Program {
        part: Part::from("rustc -vV"),
        name: &named,
        arguments: &["-vV"],
        input: "",
    };
    let policy = Program {
        part: Part::from("mise run workflow:revision"),
        name: "mise",
        arguments: &["run", "--quiet", "workflow:revision"],
        input: "",
    };
    let features = Program {
        part: Part::from("git grep (target features)"),
        name: "git",
        arguments: &words,
        input: "",
    };
    // The three programs start before the lists, so they run at the same
    // time as the programs of the lists.
    // economy: the lists read the root and the tables a second time, which
    // is one start of git and two files. ceiling: a run that counts that
    // start gives the lists the ground of this function, as #8279 does.
    let asked = Asked::start(&root, &rustc, &policy, &features)?;
    let listed = if asking.checks.is_empty() {
        Vec::new()
    }
    else {
        lists(&asking, parts)?
    };
    let common = Common::finish(asked, &root, &rustc, parts)?;
    // The lists stand in the order of the commits and then of the checks, so
    // the first list of each check is the one at the tree.
    let mut at_tree = BTreeMap::new();
    let mut at_base = BTreeMap::new();
    for (place, item) in listed.iter().enumerate() {
        let digests = if place < asking.checks.len() {
            &mut at_tree
        }
        else {
            &mut at_base
        };
        let _first = digests.insert(item.check().to_string(), item.list().digest().to_string());
    }
    let tree = tree.to_string();
    let mut keys = Vec::with_capacity(rows.len());
    for (check, row) in request.checks.iter().zip(&rows) {
        let name: &str = check.as_ref();
        let inputs = at_tree.get(name);
        let line = Line {
            base: inputs.is_none().then_some(base.as_str()),
            base_inputs: inputs.map(|_held| {
                if row.base {
                    at_base.get(name).map_or("", String::as_str)
                }
                else {
                    ""
                }
            }),
            check: name,
            compiler: &common.compiler,
            flags: &common.flags,
            host: (common.host != common.target).then_some(common.host.as_str()),
            inputs: inputs.map(String::as_str),
            policy: &common.policy,
            profile: &row.profile,
            scope: &scope,
            target: &common.target,
            target_features: &common.target_features,
            tree: inputs.is_none().then_some(tree.as_str()),
        };
        keys.push(Key(serde_json::to_string(&line).map_err(|error| {
            GateError::Read {
                what: format!("the key of {check}"),
                reason: error.to_string(),
            }
        })?));
    }
    Ok(keys)
}
