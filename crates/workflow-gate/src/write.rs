//! The write and the send of the records of a gate.
//!
//! A gate signs one record for all the checks that passed. The body of the
//! record holds the key of each check, one key on each line, and the ref of
//! each check names the record. So a gate reads its signing key one time. One
//! `git update-ref --stdin` writes each ref, and one push sends the refs of a
//! tree.

use alloc::collections::BTreeSet;
use core::fmt::Write as _;
use std::path::Path;
use std::path::PathBuf;

use crate::call::Part;
use crate::call::Parts;
use crate::call::Program;
use crate::error::GateError;
use crate::name::Check;
use crate::name::Commit;
use crate::name::Scope;
use crate::record::End;
use crate::record::Reading;
use crate::record::Short;
use crate::record::hash;
use crate::record::segment;
use crate::run::Ground;
use crate::run::Request;
use crate::tables::Form;
use crate::tables::Tasks;
use crate::verdict::KeyRequest;
use crate::verdict::keys_on;
use crate::verdict::rows;

/// How many times a write asks the signing program for the record.
const ATTEMPTS: u8 = 2;

/// What a write of the records of a gate asks.
#[derive(Clone, Debug)]
pub struct WriteRequest
{
    /// The tree that the gate passed on.
    pub tree: Commit,
    /// The checks that the gate ran, by the names of their tasks.
    pub checks: Vec<Check>,
    /// The checks that the gate held by a base or by a record. The gate did not
    /// run them, so it signs no record of them.
    pub held: BTreeSet<Check>,
    /// The base of the change.
    pub base: Option<Commit>,
    /// The scope of each check of a key.
    pub scope: Scope,
    /// The directory of `inputs.json` and `verdicts.json`.
    pub tables: Option<PathBuf>,
}

/// What a send of the records of a tree asks.
#[derive(Clone, Debug)]
pub struct SendRequest
{
    /// The commit whose tree the records name.
    pub commit: Commit,
    /// The remote of the records.
    pub remote: String,
}

/// Writes one signed record for the checks of `request` that hold a row of a
/// verdict, and names it by the ref of each check.
///
/// # Specification
/// - requires: the working directory is in a worktree of git, and `git` and
///   `mise` are on the path. Git signs a commit with `-S`.
/// - ensures: the checks are each check of the request and each task that its
///   `depends` names, as [`Tasks::ran`] gives them, that `verdicts.json` holds
///   and that `held` does not. With none, nothing. Else one commit of the tree
///   with no parent, whose body holds the key of each check, one key on each
///   line, and one ref for each check that names the commit. A line for each
///   check names the record. A signature that fails two times writes no ref,
///   and its line names the command that writes the record again.
/// - provides: the record of a gate with one read of the signing key.
/// - fails: [`GateError::Rowless`] when a check has no profile, each refusal of
///   [`keys_on`], and [`GateError::Command`] when git fails to write the refs.
/// - panics: none.
/// - intension: one start of mise for the tasks, one key for each check on one
///   ground, at most two starts of the signing program, and one start of git
///   for the refs.
/// - executable: none — the outcome is the external processes'.
///
/// # Errors
/// As `fails` lists.
///
/// # Cost
/// - allocation: the tasks, the keys, the body and one ref for each check,
///   growth within the checks of the gate
///
/// # Adequacy
/// - hypothesis: L3 — a gate of two checks and one held check, whose record the
///   read holds for each check; a record for each check, or a record of the
///   held check, changes the refs and the lines.
/// - witness: `tests::cli::a_gate_writes_one_record_for_its_checks`
#[inline]
pub fn write(
    request: &WriteRequest,
    parts: &Parts,
) -> Result<Reading, GateError>
{
    let mut ground = Ground::read(
        &Request {
            commits: Vec::new(),
            checks: Vec::new(),
            scope: request.scope.clone(),
            tables: request.tables.clone(),
        },
        parts,
    )?;
    let listing = Program {
        part: Part::from("mise tasks ls"),
        name: "mise",
        arguments: &["tasks", "ls", "--json", "--hidden"],
        input: "",
    }
    .start(&ground.root)?
    .end(parts)?;
    // A run with no task list takes the names as the caller gives them.
    let tasks = listing
        .status
        .success()
        .then(|| Tasks::read(&listing.output).ok())
        .flatten();
    let ran = tasks.as_ref().map_or_else(
        || request.checks.clone(),
        |tasks| tasks.ran(&request.checks),
    );
    if std::env::var_os("GATE_INPUTS_TASK").is_none() {
        ground.tasks = tasks;
    }
    let signed: Vec<Check> = ran
        .into_iter()
        .filter(|check| {
            !ground.tables.row(check).profile.is_empty() && !request.held.contains(check)
        })
        .collect();
    if signed.is_empty() {
        return Ok(Reading {
            lines: String::new(),
            end: End::Held,
        });
    }
    let forms = rows(&ground.tables, &signed)?;
    let root = &ground.root;
    let keys = keys_on(
        &ground,
        &KeyRequest {
            checks: signed.clone(),
            tree: Some(request.tree.clone()),
            base: request.base.clone(),
            scope: request.scope.clone(),
            tables: request.tables.clone(),
        },
        parts,
    )?;
    let names = signed
        .iter()
        .map(AsRef::<str>::as_ref)
        .collect::<Vec<&str>>()
        .join(" ");
    let tree: &str = request.tree.as_ref();
    let subject = format!("verdict: {names} pass on {}", Short(tree));
    let body = keys
        .iter()
        .map(AsRef::<str>::as_ref)
        .collect::<Vec<&str>>()
        .join("\n");
    let mut lines = String::new();
    let Some(record) = sign(root, &subject, &body, tree, &names, &mut lines, parts)?
    else {
        let _written = writeln!(
            lines,
            "verdict: {names} passed, but its record did not sign after {ATTEMPTS} attempts; write it \
             without running the checks: gate verdict write {tree} {names}"
        );
        return Ok(Reading {
            lines,
            end: End::Runs,
        });
    };
    let mut updates = String::new();
    for ((check, key), row) in signed.iter().zip(&keys).zip(&forms) {
        let place = match row.form() {
            Form::Inputs => format!("refs/verdicts/inputs/{}/{}", segment(check), hash(key)),
            Form::Tree => format!("refs/verdicts/{tree}/{}/{}", segment(check), hash(key)),
        };
        let _written = writeln!(updates, "update {place} {record}");
    }
    let _written = Program {
        part: Part::from("git update-ref --stdin"),
        name: "git",
        arguments: &["update-ref", "--stdin"],
        input: &updates,
    }
    .start(root)?
    .finish(parts)?;
    for check in &signed {
        let _written = writeln!(
            lines,
            "verdict: {check} passes on {}; the record is {}",
            Short(tree),
            Short(&record)
        );
    }
    Ok(Reading {
        lines,
        end: End::Held,
    })
}

/// Signs the record of `tree` whose message is `subject` and `body`, and gives
/// its commit, or none after [`ATTEMPTS`] failed signatures.
///
/// # Specification
/// - requires: the working directory is in a worktree of git.
/// - ensures: the commit of the first signature that passes; a line in `lines`
///   for each attempt that fails.
/// - provides: one read of the signing key for a gate when the first attempt
///   passes.
/// - fails: [`GateError::Command`] when git does not start.
/// - panics: none.
/// - executable: none — the outcome is the external process's.
///
/// # Errors
/// As `fails` lists.
///
/// # Cost
/// - allocation: the arguments and the commit, growth within the message
///
/// # Adequacy
/// - hypothesis: L2 — a gate whose record signs; a commit with no signature
///   holds no check of a read.
/// - witness: `tests::cli::a_gate_writes_one_record_for_its_checks`
#[inline]
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        primitive_signature,
        reason = "the message and the tree are the words of one call of git, which takes them as text"
    )
)]
fn sign(
    root: &Path,
    subject: &str,
    body: &str,
    tree: &str,
    names: &str,
    lines: &mut String,
    parts: &Parts,
) -> Result<Option<String>, GateError>
{
    for attempt in 1 ..= ATTEMPTS {
        let ended = Program {
            part: Part::from("git commit-tree -S"),
            name: "git",
            arguments: &["commit-tree", "-S", "-m", subject, "-m", body, tree],
            input: "",
        }
        .start(root)?
        .end(parts)?;
        if ended.status.success() {
            return Ok(Some(
                String::from_utf8_lossy(ended.output.as_ref())
                    .trim()
                    .to_owned(),
            ));
        }
        let _written = writeln!(
            lines,
            "verdict: {names} passed; signing attempt {attempt} of {ATTEMPTS} failed"
        );
    }
    Ok(None)
}

/// Sends the records of the tree of the commit of `request` to its remote in
/// one push.
///
/// # Specification
/// - requires: the working directory is in a worktree of git.
/// - ensures: each ref under the tree, and each record of inputs whose commit
///   holds the tree, on the remote. A line names the checks of the refs, or
///   says that the tree has no record.
/// - provides: the send of a gate's records in one round trip.
/// - fails: [`GateError::Command`] when git fails.
/// - panics: none.
/// - intension: one start of git for the tree, one for the refs and one push.
/// - executable: none — the outcome is the external processes'.
///
/// # Errors
/// As `fails` lists.
///
/// # Cost
/// - allocation: the refs of the tree and the line, growth within the refs
///
/// # Adequacy
/// - hypothesis: L3 — a gate's record sent to a bare remote, and a tree with no
///   record; a push of each ref of the repository, or none, changes the refs of
///   the remote.
/// - witness: `tests::cli::a_gate_writes_one_record_for_its_checks`
#[inline]
pub fn send(
    request: &SendRequest,
    parts: &Parts,
) -> Result<Reading, GateError>
{
    let here = std::env::current_dir().map_err(|error| GateError::Read {
        what: "the working directory".to_owned(),
        reason: error.to_string(),
    })?;
    let named = format!("{}^{{tree}}", request.commit);
    let tree = Program {
        part: Part::from("git rev-parse"),
        name: "git",
        arguments: &["rev-parse", &named],
        input: "",
    }
    .start(&here)?
    .finish(parts)?;
    let tree = String::from_utf8_lossy(tree.as_ref()).trim().to_owned();
    let listed = Program {
        part: Part::from("git for-each-ref"),
        name: "git",
        arguments: &[
            "for-each-ref",
            "--format=%(refname) %(tree)",
            "refs/verdicts/",
        ],
        input: "",
    }
    .start(&here)?
    .finish(parts)?;
    let under = format!("refs/verdicts/{tree}/");
    let text = String::from_utf8_lossy(listed.as_ref());
    let refs: Vec<&str> = text
        .lines()
        .filter_map(|line| {
            let (name, of) = line.split_once(' ')?;
            (name.starts_with(&under) || (name.starts_with("refs/verdicts/inputs/") && of == tree))
                .then_some(name)
        })
        .collect();
    let mut lines = String::new();
    if refs.is_empty() {
        let _written = writeln!(
            lines,
            "verdict: no record of the tree {}, so none is pushed",
            Short(&tree)
        );
        return Ok(Reading {
            lines,
            end: End::Held,
        });
    }
    let mut arguments = vec!["push", "--quiet", "--no-verify", request.remote.as_str()];
    arguments.extend(refs.iter().copied());
    let _pushed = Program {
        part: Part::from("git push"),
        name: "git",
        arguments: &arguments,
        input: "",
    }
    .start(&here)?
    .finish(parts)?;
    // The checks of the refs, by the part before the hash of each ref.
    let checks: BTreeSet<&str> = refs
        .iter()
        .filter_map(|name| name.rsplit('/').nth(1))
        .collect();
    let _written = writeln!(
        lines,
        "verdict: pushed the records of the tree {}: {}",
        Short(&tree),
        checks.into_iter().collect::<Vec<&str>>().join(" ")
    );
    Ok(Reading {
        lines,
        end: End::Held,
    })
}
