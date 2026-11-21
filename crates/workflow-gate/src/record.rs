//! The read of the records of a gate: which check holds on a tree, by the
//! inputs of its base or by a signed record of a pass.
//!
//! A record is a commit with no parent. Its message holds the key of a pass,
//! and an allowed signer signs it. A check of inputs has one ref for the key
//! of the run. Another check has one ref for each key on the tree, and each
//! such record names its own base. A read asks the remote two times at most:
//! one listing of the refs of all checks, and one fetch of the refs that
//! stand.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use core::fmt;
use core::fmt::Write as _;
use core::ops::Bound;
use std::io::BufRead as _;
use std::path::Path;
use std::path::PathBuf;

use gandr_workflow_github::Site;
use serde_json::Value;

use crate::call::Answer;
use crate::call::Part;
use crate::call::Parts;
use crate::call::Program;
use crate::call::Running;
use crate::call::Variable;
use crate::error::GateError;
use crate::list::Digest;
use crate::name::Check;
use crate::name::Commit;
use crate::name::Scope;
use crate::run::Ground;
use crate::run::Request;
use crate::run::lists_on;
use crate::tables::CheckRow;
use crate::tables::Form;
use crate::verdict::Asked;
use crate::verdict::Common;
use crate::verdict::Digests;
use crate::verdict::Key;
use crate::verdict::Shared;
use crate::verdict::head_tree;
use crate::verdict::rows;
use crate::verdict::split;

/// The path of the task files. A change of one holds no check by its base.
const TASKS: &str = ".config/mise/tasks";

/// The letters of base64, in the order of their values.
const LETTERS: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

/// The site of the compare of a base with the trunk on GitHub.
const COMPARE: Site = Site::new("trunk_holds", "api GET");

/// The site of the read of the signing keys of each signer on GitHub.
const SIGNERS: Site = Site::new("prepare", "api GET");

/// What a caller asks of one read.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReadRequest
{
    /// The checks, in the order of the lines.
    pub checks: Vec<Check>,
    /// The directory of the tables and of the scope script. Without it, the
    /// run reads `.config/gate-scope` of the worktree.
    pub tables: Option<PathBuf>,
    /// The base of the change, which `GATE_BASE` names.
    pub base: Option<Commit>,
    /// The scope of each read, which `GATE_VERDICT_SCOPE` gives. Without it,
    /// the run asks the scope script.
    pub scope: Option<Scope>,
    /// The file of allowed signers, which `GATE_VERDICT_SIGNERS` names.
    /// Without it, the run asks GitHub for the keys of each signer.
    pub signers: Option<PathBuf>,
    /// The bases that the trunk holds, separated by spaces, which
    /// `GATE_VERDICT_TRUNK_OK` gives. Without it, git or GitHub answers.
    pub trunk_holds: Option<String>,
    /// The remote of the records: `GATE_VERDICT_REMOTE`, or `origin`.
    pub remote: String,
    /// The trunk: `GANDR_TRUNK`, or `landing`.
    pub trunk: String,
    /// The token that a hosted job gives the remote, from `GH_TOKEN` under
    /// `GITHUB_ACTIONS`.
    pub token: Option<String>,
}

/// How a read ends.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum End
{
    /// Each check holds.
    Held,
    /// A check holds by no record, so the job runs it.
    Runs,
    /// GitHub gave no signing key, so the read decides nothing.
    Refused,
}

/// What a read found: one line for each fact, in the order of the checks,
/// and how it ends.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Reading
{
    /// The lines for the error output, each with its newline.
    pub lines: String,
    /// How the read ends.
    pub end: End,
}

/// A commit that the fetch gave, as the read needs it.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct Object
{
    /// Whether the object is a commit.
    commit: bool,
    /// The tree of the commit.
    tree: String,
    /// Whether the commit has a parent.
    parent: bool,
    /// The body of its message: the text after its first paragraph.
    body: String,
}

/// What a read found for one check before the signatures.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Found
{
    /// The check has the inputs of its base.
    ByBase,
    /// The scope of the check did not read.
    Unscoped,
    /// No record binds the inputs of the check under the key whose hash this
    /// is.
    Unbound(String),
    /// Each record of the check, in the order of the listing: its ref, and
    /// its commit when its shape holds, or the reason that it does not.
    Records(Vec<(String, Result<String, String>)>),
}

/// Whether the trunk holds a base.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Trunk
{
    /// The trunk holds the base, so the base passed.
    Holds,
    /// The trunk does not hold the base.
    Lacks,
}

/// How the fetch of a read ended.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Fetch
{
    /// The fetch passed, or the read wanted no ref.
    Done,
    /// The fetch failed.
    Failed,
}

/// The file of the allowed signers of a read. A file that the read wrote
/// leaves at the end of the read.
#[derive(Debug)]
struct Allowed
{
    /// The path of the file.
    path: PathBuf,
    /// Whether the read wrote the file.
    written: bool,
}

impl Drop for Allowed
{
    /// Removes the file when the read wrote it.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the file holds the keys of the signers for one read
    ///   alone; a file that stays is a file of the temporary directory, and no
    ///   read of a record changes.
    /// - witness: `tests::cli::a_record_of_the_tree_holds_against_its_own_base`
    #[inline]
    fn drop(&mut self)
    {
        if self.written {
            let _removed = std::fs::remove_file(&self.path);
        }
    }
}

/// The first 12 characters of a name, as a line of a read shows it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Short<'name>(&'name str);

impl fmt::Display for Short<'_>
{
    /// Writes the first 12 characters of the name.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the last line of a read names the tree by 12
    ///   characters; the whole name changes the asserted line.
    /// - witness: `tests::cli::a_check_with_no_record_runs`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(self.0.get(.. 12).unwrap_or(self.0))
    }
}

/// The first 16 digits of the SHA-256 of `key`: the last part of the ref
/// of its record.
///
/// # Specification
/// trivial.
///
/// # Adequacy
/// - hypothesis: L2 — a check of inputs with no record names the hash of its
///   key; another digest changes the asserted line.
/// - witness: `tests::cli::a_check_with_no_record_runs`
#[inline]
fn hash(key: &Key) -> String
{
    let digest = Digest::from(key.as_ref().as_bytes()).to_string();
    digest.get(.. 16).unwrap_or(&digest).to_owned()
}

/// The name of `check` as one part of a ref, which holds no colon.
///
/// # Specification
/// trivial.
///
/// # Adequacy
/// - hypothesis: L2 — a record of `check:case` stands under `check-case`; a
///   name with its colon lists no ref.
/// - witness: `tests::cli::a_record_with_a_body_of_another_key_does_not_hold`
#[inline]
fn segment(check: &Check) -> String
{
    check.as_ref().replace(':', "-")
}

/// Bytes in base64 with its padding, as `base64 -w0` writes them.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Base64<'bytes>(&'bytes [u8]);

impl fmt::Display for Base64<'_>
{
    /// Writes the letters of the bytes.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: four letters for each three bytes, and `=` for each byte that
    ///   the last group lacks.
    /// - provides: the header of the token that a hosted job gives the remote.
    /// - fails: when the formatter fails.
    /// - panics: none.
    /// - executable: none — the reference is `base64 -w0`, whose letters the
    ///   test pins.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Cost
    /// - allocation: none in steady state
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a text for each length of a last group, and the text
    ///   of a token; a lost padding or a shifted letter changes a vector.
    /// - witness: `record::tests::base64_writes_each_length_of_a_last_group`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        for group in self.0.chunks(3) {
            let at = |place: usize| u32::from(group.get(place).copied().unwrap_or_default());
            let bits = (at(0) << 16_u32) | (at(1) << 8_u32) | at(2);
            for (place, shift) in [18_u32, 12, 6, 0].into_iter().enumerate() {
                let letter = if place <= group.len() {
                    usize::try_from((bits >> shift) & 0x3f)
                        .ok()
                        .and_then(|value| LETTERS.get(value))
                        .copied()
                        .unwrap_or(b'=')
                }
                else {
                    b'='
                };
                f.write_char(char::from(letter))?;
            }
        }
        Ok(())
    }
}

/// The commits of `answer`, which `git cat-file --batch` printed.
///
/// # Specification
/// - requires: `answer` is what git printed for a list of names, one each.
/// - ensures: for each name that git found, its object: whether it is a commit,
///   its tree, whether it has a parent, and the body of its message. A name
///   that git did not find has no entry.
/// - provides: each fact of a record that the read checks, from one start of
///   git.
/// - fails: never.
/// - panics: none.
/// - executable: none — the outcome is a value.
///
/// # Cost
/// - allocation: the tree and the body of each commit, growth within the answer
///
/// # Adequacy
/// - hypothesis: L2 — a record whose body is another key; a body read from the
///   subject on gives the reason that the body is not a key.
/// - witness: `tests::cli::a_record_with_a_body_of_another_key_does_not_hold`
#[inline]
fn objects(answer: &Answer) -> BTreeMap<String, Object>
{
    let mut found = BTreeMap::new();
    let mut rest: &[u8] = answer.as_ref();
    let mut head = Vec::new();
    loop {
        head.clear();
        if rest.read_until(b'\n', &mut head).unwrap_or_default() == 0 {
            break;
        }
        let line = String::from_utf8_lossy(&head);
        let mut words = line.trim_end_matches('\n').split(' ');
        let (Some(name), Some(kind), Some(size)) = (words.next(), words.next(), words.next())
        else {
            continue;
        };
        let size = size.parse::<usize>().unwrap_or_default();
        let (content, after) = rest
            .split_at_checked(size)
            .unwrap_or_else(|| (rest, <&[u8]>::default()));
        rest = after.get(1 ..).unwrap_or_default();
        let content = String::from_utf8_lossy(content);
        let (headers, message) = content.split_once("\n\n").unwrap_or((&content, ""));
        let mut object = Object {
            commit: kind == "commit",
            ..Object::default()
        };
        for line in headers.lines() {
            if let Some(tree) = line.strip_prefix("tree ") {
                tree.clone_into(&mut object.tree);
            }
            object.parent |= line.starts_with("parent ");
        }
        message
            .split_once("\n\n")
            .map_or("", |(_subject, body)| body)
            .clone_into(&mut object.body);
        let _first = found.insert(name.to_owned(), object);
    }
    found
}

/// Each JSON value of the body of `object`, in its order, or none when a
/// value does not read.
///
/// # Specification
/// trivial.
///
/// # Adequacy
/// - hypothesis: L2 — a record whose body is another key reads as one value
///   that is not the key; a body read as no value gives another reason.
/// - witness: `tests::cli::a_record_with_a_body_of_another_key_does_not_hold`
#[inline]
fn values(object: &Object) -> Option<Vec<Value>>
{
    serde_json::Deserializer::from_str(&object.body)
        .into_iter::<Value>()
        .collect::<Result<Vec<Value>, _>>()
        .ok()
}

/// Whether the shape of the record `object` holds for `key`: a commit with
/// no parent, whose tree is the run's tree when `key` binds a tree, and
/// whose body is `key`.
///
/// # Specification
/// - requires: `tree` is the run's tree when `key` binds a tree.
/// - ensures: `Ok` when each part of the shape holds, else the reason of the
///   first part that does not, in the order of the list above.
/// - provides: the check of a record that needs no signature.
/// - fails: never.
/// - panics: none.
/// - executable: none — the outcome is a value.
///
/// # Errors
/// The reason, as a line of the read states it.
///
/// # Cost
/// - allocation: the values of the body and of the key, growth within the key
///
/// # Adequacy
/// - hypothesis: L2 — a record whose body is another key; a body that is not
///   compared holds the check with status 0.
/// - witness: `tests::cli::a_record_with_a_body_of_another_key_does_not_hold`
#[inline]
fn shape(
    object: Option<&Object>,
    key: &Key,
    tree: Option<&Commit>,
) -> Result<(), String>
{
    let object = object
        .filter(|found| found.commit)
        .ok_or_else(|| "it is not a commit".to_owned())?;
    if object.parent {
        return Err("it has a parent".to_owned());
    }
    if tree.is_some_and(|tree| AsRef::<str>::as_ref(tree) != object.tree) {
        return Err("its tree is not the run's tree".to_owned());
    }
    let body = values(object).ok_or_else(|| "its body is not a key".to_owned())?;
    let own: Option<Value> = serde_json::from_str(key.as_ref()).ok();
    match (body.as_slice(), own.as_ref()) {
        (&[ref value], Some(own)) if value == own => Ok(()),
        _ => Err("its body is not the run's key".to_owned()),
    }
}

/// The base that the body of a record of the tree names.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the text of `base` in the first value of the body; the empty text
///   when the value holds no base, or a base of `null` or `false`.
/// - provides: the base whose scope and whose trunk the record's key reads.
/// - fails: never.
/// - panics: none.
/// - executable: none — the outcome is a value.
///
/// # Errors
/// `its body is not a key` when the body does not read as JSON, or its first
/// value is neither an object nor `null`.
///
/// # Cost
/// - allocation: the values of the body, growth within the body
///
/// # Adequacy
/// - hypothesis: L2 — a record of the tree on a base that the run does not
///   name; the run's base in place of the record's changes the key, and the
///   record does not hold.
/// - witness: `tests::cli::a_record_of_the_tree_holds_against_its_own_base`
#[inline]
fn named_base(object: Option<&Object>) -> Result<String, String>
{
    let refused = || "its body is not a key".to_owned();
    let object = object.filter(|found| found.commit).ok_or_else(refused)?;
    let body = values(object).ok_or_else(refused)?;
    match body.first() {
        None | Some(&Value::Null) => Ok(String::new()),
        Some(&Value::Object(ref members)) => Ok(match members.get("base") {
            None | Some(&Value::Null | &Value::Bool(false)) => String::new(),
            Some(&Value::String(ref base)) => base.clone(),
            Some(other) => other.to_string(),
        }),
        Some(_) => Err(refused()),
    }
}

/// Whether the trunk holds each of `bases`.
///
/// # Specification
/// - requires: the working directory is in a worktree of git.
/// - ensures: with `trunk_holds` in the request, each base that it names holds.
///   Else a base holds when git finds it below `origin/<trunk>`, or when GitHub
///   compares it with the trunk as `ahead` or `identical`.
/// - provides: the check that a base passed, since the trunk holds only a
///   commit that passed.
/// - fails: [`GateError::Command`] when a wait for git or for GitHub fails.
/// - panics: none.
/// - intension: one start of git for each base, at the same time, and one start
///   of GitHub for each base that git does not find, at the same time.
/// - executable: none — the outcome is the external processes'.
///
/// # Errors
/// As `fails` lists.
///
/// # Cost
/// - allocation: the arguments of each call and one entry for each base, growth
///   within the bases
///
/// # Adequacy
/// - hypothesis: L2 — a base that the trunk does not hold; a base that holds by
///   no answer holds the check by its base.
/// - witness: `tests::cli::a_base_that_the_trunk_does_not_hold_holds_no_check`
#[inline]
fn trunk_holds(
    request: &ReadRequest,
    root: &Path,
    bases: &BTreeSet<Commit>,
    parts: &Parts,
) -> Result<BTreeMap<Commit, Trunk>, GateError>
{
    let mut held = BTreeMap::new();
    if let Some(ref listed) = request.trunk_holds {
        for base in bases {
            let answer = if listed
                .split(' ')
                .any(|word| word == AsRef::<str>::as_ref(base))
            {
                Trunk::Holds
            }
            else {
                Trunk::Lacks
            };
            let _first = held.insert(base.clone(), answer);
        }
        return Ok(held);
    }
    let trunk = format!("origin/{}", request.trunk);
    let words: Vec<[&str; 4]> = bases
        .iter()
        .map(|base| ["merge-base", "--is-ancestor", base.as_ref(), trunk.as_str()])
        .collect();
    let mut running = Vec::with_capacity(words.len());
    for arguments in &words {
        running.push(
            Program {
                part: Part::from("git merge-base --is-ancestor"),
                name: "git",
                arguments,
                input: "",
            }
            .start(root)?,
        );
    }
    let mut asked = Vec::new();
    for (base, call) in bases.iter().zip(running) {
        if call.end(parts)?.status.success() {
            let _first = held.insert(base.clone(), Trunk::Holds);
        }
        else {
            asked.push(base);
        }
    }
    // GitHub answers for each base that the repository does not find below
    // the trunk.
    let paths: Vec<String> = asked
        .iter()
        .map(|base| {
            format!(
                "repos/{{owner}}/{{repo}}/compare/{base}...{}",
                request.trunk
            )
        })
        .collect();
    let words: Vec<Vec<&str>> = paths
        .iter()
        .map(|path| {
            let mut words: Vec<&str> = COMPARE.words().into_iter().map(<&str>::from).collect();
            words.extend([path.as_str(), "--jq", ".status"]);
            words
        })
        .collect();
    let mut running = Vec::with_capacity(words.len());
    for arguments in &words {
        running.push(
            Program {
                part: Part::from("gh api compare"),
                name: "gh",
                arguments,
                input: "",
            }
            .start(root)?,
        );
    }
    for (base, call) in asked.into_iter().zip(running) {
        let ended = call.end(parts)?;
        let status = String::from_utf8_lossy(ended.output.as_ref());
        let answer = if ended.status.success() && matches!(status.trim(), "ahead" | "identical") {
            Trunk::Holds
        }
        else {
            Trunk::Lacks
        };
        let _first = held.insert(base.clone(), answer);
    }
    Ok(held)
}

/// Starts `script` for each of `bases`: against that base, or against the
/// base of the environment for `None`.
///
/// # Specification
/// - requires: `script` runs the scope script.
/// - ensures: one running script for each base, in the order of `bases`.
/// - provides: the scope of each record against its own base, at the same time
///   as the other programs of the read.
/// - fails: [`GateError::Command`] when a script does not start.
/// - panics: none.
/// - executable: none — the outcome is the external processes'.
///
/// # Errors
/// As `fails` lists.
///
/// # Cost
/// - allocation: the command of each process, growth within the bases
///
/// # Adequacy
/// - hypothesis: L2 — a record of the tree on a base that the run does not
///   name; the scope against the run's base changes the key.
/// - witness: `tests::cli::a_record_of_the_tree_holds_against_its_own_base`
#[inline]
fn start_scopes<'run>(
    script: Program<'run>,
    root: &Path,
    bases: &[Option<&'run Commit>],
) -> Result<Vec<Running<'run>>, GateError>
{
    let mut running = Vec::with_capacity(bases.len());
    for base in bases {
        running.push(match *base {
            Some(base) => script.start_with(root, &[Variable {
                name: "GATE_BASE",
                value: base.as_ref(),
            }])?,
            None => script.start(root)?,
        });
    }
    Ok(running)
}

/// The scope that each script of `running` printed, or none for a script
/// that failed.
///
/// # Specification
/// trivial.
///
/// # Adequacy
/// - hypothesis: L2 — a record of the tree on a base that the run does not
///   name; a scope with its newline gives another key.
/// - witness: `tests::cli::a_record_of_the_tree_holds_against_its_own_base`
#[inline]
fn finish_scopes(
    running: Vec<Running<'_>>,
    parts: &Parts,
) -> Result<Vec<Option<String>>, GateError>
{
    let mut scopes = Vec::with_capacity(running.len());
    for call in running {
        let ended = call.end(parts)?;
        scopes.push(ended.status.success().then(|| {
            String::from_utf8_lossy(ended.output.as_ref())
                .trim_end_matches('\n')
                .to_owned()
        }));
    }
    Ok(scopes)
}

/// The common part of the keys of a read, and the file of its allowed
/// signers.
///
/// # Specification
/// - requires: `asked` holds the programs of the common part, and `rustc` names
///   the compiler that it started.
/// - ensures: the common part, and the file of `signers` of the request, or a
///   written file of the keys that GitHub gives for each login of `logins`, one
///   line each as `<login>@users.noreply.github.com namespaces="git" <key>`. No
///   file when GitHub gave no key.
/// - provides: the two answers that each record of a read needs, at the same
///   time.
/// - fails: each refusal of [`Common::finish`], [`GateError::Command`] when a
///   call of GitHub fails, and [`GateError::Read`] when the file does not
///   write.
/// - panics: none.
/// - intension: one start of GitHub for each login, at the same time as the
///   programs of the common part.
/// - executable: none — the outcome is the external processes'.
///
/// # Errors
/// As `fails` lists.
///
/// # Cost
/// - allocation: the arguments of each call and the lines of the file, setup
///
/// # Adequacy
/// - hypothesis: L2 — a record with a file of allowed signers; a read that
///   verifies against no file refuses each signature.
/// - witness: `tests::cli::a_record_of_the_tree_holds_against_its_own_base`
#[inline]
fn prepare(
    request: &ReadRequest,
    logins: &[String],
    asked: Asked<'_>,
    rustc: &Program<'_>,
    root: &Path,
    parts: &Parts,
) -> Result<(Common, Option<Allowed>), GateError>
{
    let paths: Vec<String> = if request.signers.is_some() {
        Vec::new()
    }
    else {
        logins
            .iter()
            .map(|login| format!("users/{login}/ssh_signing_keys"))
            .collect()
    };
    let words: Vec<Vec<&str>> = paths
        .iter()
        .map(|path| {
            let mut words: Vec<&str> = SIGNERS.words().into_iter().map(<&str>::from).collect();
            words.extend([path.as_str(), "--jq", ".[].key"]);
            words
        })
        .collect();
    let mut running = Vec::with_capacity(words.len());
    for arguments in &words {
        running.push(
            Program {
                part: Part::from("gh api ssh_signing_keys"),
                name: "gh",
                arguments,
                input: "",
            }
            .start(root)?,
        );
    }
    let common = Common::finish(asked, root, rustc, parts)?;
    if let Some(ref given) = request.signers {
        return Ok((
            common,
            Some(Allowed {
                path: given.clone(),
                written: false,
            }),
        ));
    }
    let mut lines = String::new();
    for (login, call) in logins.iter().zip(running) {
        let keys = call.finish(parts)?;
        for key in String::from_utf8_lossy(keys.as_ref()).lines() {
            let _written = writeln!(
                lines,
                "{login}@users.noreply.github.com namespaces=\"git\" {key}"
            );
        }
    }
    if lines.is_empty() {
        return Ok((common, None));
    }
    let path = std::env::temp_dir().join(format!("gate-signers-{}", std::process::id()));
    std::fs::write(&path, lines).map_err(|error| GateError::Read {
        what: path.display().to_string(),
        reason: error.to_string(),
    })?;
    Ok((
        common,
        Some(Allowed {
            path,
            written: true,
        }),
    ))
}

/// The commits of `oids` whose signature an allowed signer made, and the
/// reason of each other one.
///
/// # Specification
/// - requires: each of `oids` is a commit that the repository holds.
/// - ensures: `Ok` for each commit that `git verify-commit` passes against the
///   file of `allowed`, and else the reason with the text that git printed,
///   each newline as a space.
/// - provides: the signature of each record of a read.
/// - fails: [`GateError::Command`] when a wait for git fails.
/// - panics: none.
/// - intension: one start of git for all commits. When it fails, one start for
///   each commit, at the same time, gives the reason of each.
/// - executable: none — the outcome is the external processes'.
///
/// # Errors
/// As `fails` lists.
///
/// # Cost
/// - allocation: the arguments and one entry for each commit, growth within the
///   commits
///
/// # Adequacy
/// - hypothesis: L2 — a signed record and a record of a key with no signature;
///   a batch whose failure fails each commit refuses the signed record too.
/// - witness: `tests::cli::a_record_of_the_tree_holds_against_its_own_base`
#[inline]
fn signatures(
    oids: &BTreeSet<String>,
    allowed: &Allowed,
    root: &Path,
    parts: &Parts,
) -> Result<BTreeMap<String, Result<(), String>>, GateError>
{
    let mut verified = BTreeMap::new();
    if oids.is_empty() {
        return Ok(verified);
    }
    let file = format!("gpg.ssh.allowedSignersFile={}", allowed.path.display());
    let mut words = vec!["-c", file.as_str(), "verify-commit"];
    words.extend(oids.iter().map(String::as_str));
    let batch = Program {
        part: Part::from("git verify-commit"),
        name: "git",
        arguments: &words,
        input: "",
    }
    .start(root)?
    .end(parts)?;
    if batch.status.success() {
        for oid in oids {
            let _first = verified.insert(oid.clone(), Ok(()));
        }
        return Ok(verified);
    }
    // One bad record fails the batch, so each commit asks again alone.
    let words: Vec<[&str; 4]> = oids
        .iter()
        .map(|oid| ["-c", file.as_str(), "verify-commit", oid.as_str()])
        .collect();
    let mut running = Vec::with_capacity(words.len());
    for arguments in &words {
        running.push(
            Program {
                part: Part::from("git verify-commit"),
                name: "git",
                arguments,
                input: "",
            }
            .start(root)?,
        );
    }
    for (oid, call) in oids.iter().zip(running) {
        let ended = call.end(parts)?;
        let outcome = if ended.status.success() {
            Ok(())
        }
        else {
            let mut said = String::from_utf8_lossy(ended.errors.as_ref()).into_owned();
            said.push_str(&String::from_utf8_lossy(ended.output.as_ref()));
            let said = said.trim_end_matches('\n').replace('\n', " ");
            Err(format!("its signature does not verify: {said} "))
        };
        let _first = verified.insert(oid.clone(), outcome);
    }
    Ok(verified)
}

/// The facts of the run's base: whether the trunk holds it, whether the
/// change holds no task file, and the scope of the run.
#[derive(Debug)]
struct Facts
{
    /// Whether a check of inputs can hold by the run's base.
    by_base: bool,
    /// The scope of the run, or none when it did not read.
    scope: Option<Scope>,
}

impl Facts
{
    /// Reads the facts of the run's base.
    ///
    /// # Specification
    /// - requires: the working directory is in a worktree of git, `script` runs
    ///   the scope script, and `digested` holds the checks of inputs.
    /// - ensures: `by_base` when the run names a base, the trunk holds it, the
    ///   change from it to `tree` holds no task file, and the scope reads. The
    ///   scope of `GATE_VERDICT_SCOPE`, or of the script when the run names a
    ///   base or a check of inputs.
    /// - provides: the first answers of a read, with no call of the remote.
    /// - fails: each refusal of [`trunk_holds`], and [`GateError::Command`]
    ///   when a program does not start.
    /// - panics: none.
    /// - intension: the script starts first, and the diff and the trunk's
    ///   answer run at its time.
    /// - executable: none — the outcome is the external processes'.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Cost
    /// - allocation: the scope, setup
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a change of a task file and a base that the trunk
    ///   does not hold; a fact read as held for either holds the check by its
    ///   base.
    /// - witness: `tests::cli::a_change_of_a_task_holds_no_check_by_its_base`
    /// - witness: `tests::cli::a_base_that_the_trunk_does_not_hold_holds_no_check`
    #[inline]
    fn read(
        request: &ReadRequest,
        script: Program<'_>,
        root: &Path,
        tree: &Commit,
        digested: &[Check],
        parts: &Parts,
    ) -> Result<Self, GateError>
    {
        let base = request.base.as_ref();
        let own = if request.scope.is_none() && (base.is_some() || !digested.is_empty()) {
            start_scopes(script, root, &[None])?
        }
        else {
            Vec::new()
        };
        let words = base.map(|base| ["diff", "--quiet", base.as_ref(), tree.as_ref(), "--", TASKS]);
        let diff = words
            .as_ref()
            .map(|arguments| {
                Program {
                    part: Part::from("git diff --quiet (tasks)"),
                    name: "git",
                    arguments,
                    input: "",
                }
                .start(root)
            })
            .transpose()?;
        let held = match base {
            Some(base) => {
                trunk_holds(request, root, &BTreeSet::from([base.clone()]), parts)?.get(base)
                    == Some(&Trunk::Holds)
            },
            None => false,
        };
        let same_tasks = match diff {
            Some(call) => call.end(parts)?.status.success(),
            None => false,
        };
        let scope = match request.scope {
            Some(ref given) => Some(given.clone()),
            None => finish_scopes(own, parts)?
                .into_iter()
                .next()
                .flatten()
                .map(|text| Scope::from(text.as_str())),
        };
        Ok(Self {
            by_base: base.is_some() && held && same_tasks && scope.is_some(),
            scope,
        })
    }
}

/// The checks of `request` that hold on the tree of `HEAD`, by the inputs of
/// their base or by a signed record of a pass, with a line for each fact.
///
/// # Specification
/// - requires: the working directory is in a worktree of git, and `git`,
///   `cargo`, `mise`, `gh` and the compiler are on the path.
/// - ensures: a check of inputs holds by its base when the run names a base,
///   the trunk holds it, the change holds no task file, the scope reads, and
///   the digest of its inputs at the tree is their digest at the base. Else a
///   check of inputs holds when the remote holds the record of its key over the
///   scope, with the shape of [`shape`] and a signature of an allowed signer.
///   Another check holds by the first record on the tree, in the order of the
///   listing, whose base the trunk holds and whose key is the run's key against
///   that base and over the scope against that base, with that shape and
///   signature. Each line is a line of the script before this module, word for
///   word. The end is [`End::Held`] when each check holds, [`End::Runs`] with a
///   last line that names the checks that do not, and [`End::Refused`] when
///   GitHub gave no signing key.
/// - provides: the read of a gate and of a hosted job in one run.
/// - fails: [`GateError::Rowless`] for a check with no row, and each refusal of
///   the programs of a key, of [`lists_on`] and of the calls of a read.
/// - panics: none.
/// - intension: a run whose checks all hold by their base starts no program of
///   the common part, no call of GitHub and no call of the remote. One listing
///   of the remote for all checks, and one fetch for the refs that stand. One
///   `git verify-commit` for all records.
/// - executable: none — the outcome is the external processes'.
///
/// # Errors
/// As `fails` lists.
///
/// # Cost
/// - allocation: the lists, the keys, the listing of the remote and the objects
///   of the records, growth within the checks and their records
///
/// # Adequacy
/// - hypothesis: L2 — a check that holds by its base, a check with no record, a
///   record of another key, and a signed record of the tree on its own base; a
///   read that holds a check by a record that does not verify, or that names no
///   check, changes the asserted lines or status.
/// - witness: `tests::cli::a_check_with_the_inputs_of_its_base_holds_with_no_remote`
/// - witness: `tests::cli::a_check_with_no_record_runs`
/// - witness: `tests::cli::a_record_with_a_body_of_another_key_does_not_hold`
/// - witness: `tests::cli::a_record_of_the_tree_holds_against_its_own_base`
#[inline]
pub fn read(
    request: &ReadRequest,
    parts: &Parts,
) -> Result<Reading, GateError>
{
    let tree = head_tree(parts)?;
    let ground = Ground::read(
        &Request {
            commits: vec![tree.clone()],
            checks: Vec::new(),
            scope: Scope::from("--workspace"),
            tables: request.tables.clone(),
        },
        parts,
    )?;
    let root = ground.root.clone();
    let config = request
        .tables
        .clone()
        .unwrap_or_else(|| root.join(".config/gate-scope"));
    let path = config.join("scope.bash").to_string_lossy().into_owned();
    let script = Program {
        part: Part::from("scope.bash --lints"),
        name: &path,
        arguments: &["--lints"],
        input: "",
    };
    let rows = rows(&ground.tables, &request.checks)?;
    let shared = Shared::new(&tree);
    let [rustc, policy, features] = shared.programs();
    let header = request.token.as_ref().map_or_else(String::new, |token| {
        let token = format!("x-access-token:{token}");
        format!(
            "http.https://github.com/.extraheader=AUTHORIZATION: basic {}",
            Base64(token.as_bytes())
        )
    });
    // The listing names each check by the prefix of its refs, so it needs no
    // key and runs beside the keys.
    let patterns: Vec<String> = request
        .checks
        .iter()
        .zip(&rows)
        .map(|(check, row)| match row.form() {
            Form::Inputs => format!("refs/verdicts/inputs/{}/*", segment(check)),
            Form::Tree => format!("refs/verdicts/{tree}/{}/*", segment(check)),
        })
        .collect();
    let mut list_words: Vec<&str> = Vec::with_capacity(patterns.len().saturating_add(4));
    if !header.is_empty() {
        list_words.extend(["-c", header.as_str()]);
    }
    list_words.extend(["ls-remote", request.remote.as_str()]);
    list_words.extend(patterns.iter().map(String::as_str));
    let lister = || Program {
        part: Part::from("git ls-remote"),
        name: "git",
        arguments: &list_words,
        input: "",
    };
    // A check of the tree never holds by its base, so its run needs the
    // common part and the listing, and they start first.
    let tree_first = rows.iter().any(|row| row.form() == Form::Tree);
    let mut asked = if tree_first {
        Some(Asked::start(&root, &rustc, &policy, &features)?)
    }
    else {
        None
    };
    let mut listing = if tree_first {
        Some(lister().start(&root)?)
    }
    else {
        None
    };
    let digested: Vec<Check> = request
        .checks
        .iter()
        .zip(&rows)
        .filter(|&(_, row)| row.form() == Form::Inputs)
        .map(|(check, _)| check.clone())
        .collect();
    let facts = Facts::read(request, script, &root, &tree, &digested, parts)?;
    let (at_tree, at_base) = match facts.scope {
        Some(ref scope) if !digested.is_empty() => {
            let mut commits = vec![tree.clone()];
            commits.extend(request.base.clone());
            let listed = lists_on(
                ground.clone(),
                &Request {
                    commits,
                    checks: digested.clone(),
                    scope: scope.clone(),
                    tables: request.tables.clone(),
                },
                parts,
            )?;
            split(&listed, &digested)
        },
        _ => (BTreeMap::new(), BTreeMap::new()),
    };
    let mut found: Vec<Found> = request
        .checks
        .iter()
        .zip(&rows)
        .map(|(check, row)| {
            let name: &str = check.as_ref();
            let same = at_tree
                .get(name)
                .is_some_and(|held| at_base.get(name) == Some(held));
            if facts.by_base && row.form() == Form::Inputs && same {
                Found::ByBase
            }
            else {
                Found::Records(Vec::new())
            }
        })
        .collect();
    let mut lines = String::new();
    let base = request.base.as_ref();
    if found.iter().all(|one| *one == Found::ByBase) {
        say(&mut lines, &request.checks, &found, &tree, base);
        return Ok(Reading {
            lines,
            end: End::Held,
        });
    }
    let listing = match listing.take() {
        Some(running) => running,
        None => lister().start(&root)?,
    };
    let asked = match asked.take() {
        Some(running) => running,
        None => Asked::start(&root, &rustc, &policy, &features)?,
    };
    let (common, allowed) = prepare(
        request,
        ground.tables.signers(),
        asked,
        &rustc,
        &root,
        parts,
    )?;
    let Some(allowed) = allowed
    else {
        // The script stops at the first check that needs a record, so the
        // lines of the checks before it stand.
        let first = found
            .iter()
            .position(|one| *one != Found::ByBase)
            .unwrap_or_default();
        say(
            &mut lines,
            request.checks.get(.. first).unwrap_or_default(),
            &found,
            &tree,
            base,
        );
        let _written = writeln!(
            lines,
            "verdict: GitHub gave no signing key for the signers of {}",
            config.join("verdicts.json").display()
        );
        return Ok(Reading {
            lines,
            end: End::Refused,
        });
    };
    let records = Records {
        request,
        rows: &rows,
        common: &common,
        tree: &tree,
        root: &root,
        script,
        header: &header,
        scope: facts.scope.as_ref(),
        at_tree: &at_tree,
        at_base: &at_base,
    };
    records.find(&mut found, listing, &allowed, parts)?;
    say(&mut lines, &request.checks, &found, &tree, base);
    // A check holds by its base, or by its first record that holds.
    let holds = |one: &Found| match *one {
        Found::ByBase => true,
        Found::Records(ref records) => records.iter().any(|&(_, ref outcome)| outcome.is_ok()),
        Found::Unscoped | Found::Unbound(_) => false,
    };
    let missing: Vec<&str> = request
        .checks
        .iter()
        .zip(&found)
        .filter(|&(_, one)| !holds(one))
        .map(|(check, _)| check.as_ref())
        .collect();
    if missing.is_empty() {
        return Ok(Reading {
            lines,
            end: End::Held,
        });
    }
    let _written = writeln!(
        lines,
        "verdict: no record holds {} on {}, so the job runs them",
        missing.join(" "),
        Short(tree.as_ref())
    );
    Ok(Reading {
        lines,
        end: End::Runs,
    })
}

/// Writes the lines of each of `checks` with what the read found for it.
///
/// # Specification
/// - requires: `found` holds one entry for each check of the read, and each
///   record that holds `Ok` verified.
/// - ensures: for each check in order: the line of a hold by the base; the line
///   of a scope that did not read; the line of no record of the inputs; or one
///   line for each record that does not hold before the first that does, and
///   the line of that record.
/// - provides: the lines of the script before this module, word for word.
/// - fails: never.
/// - panics: none.
/// - executable: none — the outcome is the text.
///
/// # Cost
/// - allocation: the lines, growth within the records
///
/// # Adequacy
/// - hypothesis: L2 — a hold by the base, no record, and a record of another
///   key; a line with other words changes the asserted output.
/// - witness: `tests::cli::a_check_with_the_inputs_of_its_base_holds_with_no_remote`
/// - witness: `tests::cli::a_record_with_a_body_of_another_key_does_not_hold`
#[inline]
fn say(
    lines: &mut String,
    checks: &[Check],
    found: &[Found],
    tree: &Commit,
    base: Option<&Commit>,
)
{
    for (check, one) in checks.iter().zip(found) {
        match *one {
            Found::ByBase => {
                let _written = writeln!(
                    lines,
                    "verdict: {check} holds on {}: its inputs are those of the base {}, which passed, so the check does not run again",
                    Short(tree.as_ref()),
                    Short(base.map_or("", Commit::as_ref))
                );
            },
            Found::Unscoped => {
                let _written = writeln!(
                    lines,
                    "verdict: the scope of {check} did not read, so the run reads no record of it"
                );
            },
            Found::Unbound(ref key) => {
                let _written = writeln!(
                    lines,
                    "verdict: no record binds the inputs of {check} in this run, {key}"
                );
            },
            Found::Records(ref records) => {
                for &(ref name, ref outcome) in records {
                    match *outcome {
                        Ok(ref commit) => {
                            let _written = writeln!(
                                lines,
                                "verdict: {check} holds on {}: the record {} binds this run's key, so the check does not run again",
                                Short(tree.as_ref()),
                                Short(commit)
                            );
                            break;
                        },
                        Err(ref reason) => {
                            let _written = writeln!(
                                lines,
                                "verdict: the record {} of {check} does not hold: {reason}",
                                name.rsplit('/').next().unwrap_or_default()
                            );
                        },
                    }
                }
            },
        }
    }
}

/// Each ref of the remote that the running `listing` names, with its commit,
/// by the name of the ref.
///
/// # Specification
/// - requires: `listing` runs `git ls-remote`.
/// - ensures: each ref and its commit as `git ls-remote` lists them; no ref
///   when the listing fails.
/// - provides: the one listing of a read, which ran beside the keys.
/// - fails: [`GateError::Command`] when the wait for git fails.
/// - panics: none.
/// - executable: none — the outcome is the external process's.
///
/// # Errors
/// As `fails` lists.
///
/// # Cost
/// - allocation: the refs, growth within the listing
///
/// # Adequacy
/// - hypothesis: L2 — a check with no record, and a record of another key that
///   the listing gives by the prefix of its check; a match by prefix and not by
///   the whole ref takes that record.
/// - witness: `tests::cli::a_check_with_no_record_runs`
/// - witness: `tests::cli::a_record_with_a_body_of_another_key_does_not_hold`
#[inline]
fn listed(
    listing: Running<'_>,
    parts: &Parts,
) -> Result<BTreeMap<String, String>, GateError>
{
    let ended = listing.end(parts)?;
    if !ended.status.success() {
        return Ok(BTreeMap::new());
    }
    Ok(String::from_utf8_lossy(ended.output.as_ref())
        .lines()
        .filter_map(|line| {
            let (commit, name) = line.split_once('\t')?;
            Some((name.to_owned(), commit.to_owned()))
        })
        .collect())
}

/// What the records of a read need of the run.
#[derive(Debug)]
struct Records<'run>
{
    /// The request.
    request: &'run ReadRequest,
    /// The row of each check.
    rows: &'run [CheckRow],
    /// The common part of the keys.
    common: &'run Common,
    /// The tree of the run.
    tree: &'run Commit,
    /// The root of the worktree.
    root: &'run Path,
    /// The scope script.
    script: Program<'run>,
    /// The header of the token for the remote, or the empty text.
    header: &'run str,
    /// The scope of the run, or none when it did not read.
    scope: Option<&'run Scope>,
    /// The digest of each check of inputs at the tree.
    at_tree: &'run BTreeMap<String, String>,
    /// The digest of each check of inputs at the base.
    at_base: &'run BTreeMap<String, String>,
}

impl Records<'_>
{
    /// Finds the records of each check of `found` that does not hold by its
    /// base in the answer of `listing`, and verifies them.
    ///
    /// # Specification
    /// - requires: `found` holds [`Found::ByBase`] or an empty list of records
    ///   for each check of the request; `listing` lists the refs of each check
    ///   by its prefix.
    /// - ensures: for a check of inputs, [`Found::Unscoped`] when the scope did
    ///   not read, [`Found::Unbound`] when the remote lists no record of its
    ///   key or the fetch fails, and else its one record. For another check,
    ///   each record that the remote lists on the tree. A record holds `Ok`
    ///   only when its shape and its signature hold.
    /// - provides: the records of a read, with two calls of the remote.
    /// - fails: each refusal of the programs of the read.
    /// - panics: none.
    /// - executable: none — the outcome is the external processes'.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Cost
    /// - allocation: the keys, the listing and the objects, growth within the
    ///   records
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a record of another key and a signed record of the
    ///   tree; a record that holds with no signature holds the first.
    /// - witness: `tests::cli::a_record_with_a_body_of_another_key_does_not_hold`
    /// - witness: `tests::cli::a_record_of_the_tree_holds_against_its_own_base`
    #[inline]
    fn find(
        &self,
        found: &mut [Found],
        listing: Running<'_>,
        allowed: &Allowed,
        parts: &Parts,
    ) -> Result<(), GateError>
    {
        let base = self.request.base.as_ref();
        // The key and the ref of each check of inputs.
        let mut keys: BTreeMap<usize, (Key, String)> = BTreeMap::new();
        for (place, (check, row)) in self.request.checks.iter().zip(self.rows).enumerate() {
            let Some(one) = found.get_mut(place)
            else {
                continue;
            };
            if *one == Found::ByBase {
                continue;
            }
            if row.form() == Form::Tree {
                continue;
            }
            let Some(scope) = self.scope
            else {
                *one = Found::Unscoped;
                continue;
            };
            let name: &str = check.as_ref();
            let digests = Digests {
                tree: self.at_tree.get(name).map_or("", String::as_str),
                base: self.at_base.get(name).map_or("", String::as_str),
            };
            let key = self
                .common
                .line(check, row, self.tree, base, scope, Some(digests))?;
            let name = format!("refs/verdicts/inputs/{}/{}", segment(check), hash(&key));
            let _first = keys.insert(place, (key, name));
        }
        let listing = listed(listing, parts)?;
        // The refs that stand, each one time, and one fetch for all of them.
        let mut wanted = BTreeSet::new();
        for (place, (one, check)) in found.iter().zip(&self.request.checks).enumerate() {
            if let Some(&(_, ref name)) = keys.get(&place) {
                if listing.contains_key(name) {
                    let _new = wanted.insert(name.clone());
                }
            }
            else if *one != Found::ByBase && *one != Found::Unscoped {
                for (name, _) in self.under(check, &listing) {
                    let _new = wanted.insert(name.clone());
                }
            }
        }
        let fetched = self.fetch(&wanted, parts)?;
        let oid = |name: &str| listing.get(name).cloned().unwrap_or_default();
        let objects = if fetched == Fetch::Done && !wanted.is_empty() {
            let mut input = String::new();
            for name in &wanted {
                let _written = writeln!(input, "{}", oid(name));
            }
            objects(
                &Program {
                    part: Part::from("git cat-file --batch (records)"),
                    name: "git",
                    arguments: &["cat-file", "--batch"],
                    input: &input,
                }
                .start(self.root)?
                .finish(parts)?,
            )
        }
        else {
            BTreeMap::new()
        };
        // Each check of inputs: its one record, or no record.
        for (&place, &(ref key, ref name)) in &keys {
            let Some(one) = found.get_mut(place)
            else {
                continue;
            };
            *one = if fetched == Fetch::Done && wanted.contains(name) {
                let commit = oid(name);
                Found::Records(vec![(
                    name.clone(),
                    shape(objects.get(&commit), key, None).map(|()| commit),
                )])
            }
            else {
                Found::Unbound(hash(key))
            };
        }
        self.tree_records(found, &listing, fetched, &objects, parts)?;
        // One signature check for each commit whose shape holds.
        let shaped: BTreeSet<String> = found
            .iter()
            .filter_map(|one| match *one {
                Found::Records(ref records) => Some(records),
                Found::ByBase | Found::Unscoped | Found::Unbound(_) => None,
            })
            .flatten()
            .filter_map(|&(_, ref outcome)| outcome.as_ref().ok().cloned())
            .collect();
        let verified = signatures(&shaped, allowed, self.root, parts)?;
        for one in found.iter_mut() {
            if let Found::Records(ref mut records) = *one {
                for &mut (_, ref mut outcome) in records.iter_mut() {
                    if let Ok(ref commit) = *outcome
                        && let Some(&Err(ref reason)) = verified.get(commit)
                    {
                        *outcome = Err(reason.clone());
                    }
                }
            }
        }
        Ok(())
    }

    /// The refs of `listing` under the prefix of the records of `check` on
    /// the tree, with their commits, by name.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a signed record of the tree; a prefix of another
    ///   check takes no record.
    /// - witness: `tests::cli::a_record_of_the_tree_holds_against_its_own_base`
    #[inline]
    fn under<'list>(
        &self,
        check: &Check,
        listing: &'list BTreeMap<String, String>,
    ) -> Vec<(&'list String, &'list String)>
    {
        let prefix = format!("refs/verdicts/{}/{}/", self.tree, segment(check));
        listing
            .range::<str, _>((Bound::Included(prefix.as_str()), Bound::Unbounded))
            .take_while(|&(name, _)| name.starts_with(&prefix))
            .collect()
    }

    /// Fetches each ref of `wanted` from the remote to the same ref here.
    ///
    /// # Specification
    /// - requires: the remote lists each ref of `wanted`.
    /// - ensures: [`Fetch::Done`] when the fetch passes or no ref is wanted.
    /// - provides: the one fetch of a read.
    /// - fails: [`GateError::Command`] when git does not start.
    /// - panics: none.
    /// - executable: none — the outcome is the external process's.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Cost
    /// - allocation: the refspecs, growth within the refs
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a signed record; a read with no fetch has no object
    ///   and holds no check.
    /// - witness: `tests::cli::a_record_of_the_tree_holds_against_its_own_base`
    #[inline]
    fn fetch(
        &self,
        wanted: &BTreeSet<String>,
        parts: &Parts,
    ) -> Result<Fetch, GateError>
    {
        if wanted.is_empty() {
            return Ok(Fetch::Done);
        }
        let specs: Vec<String> = wanted
            .iter()
            .map(|name| format!("+{name}:{name}"))
            .collect();
        let mut words: Vec<&str> = Vec::with_capacity(specs.len().saturating_add(6));
        if !self.header.is_empty() {
            words.extend(["-c", self.header]);
        }
        words.extend([
            "fetch",
            "--quiet",
            "--no-tags",
            self.request.remote.as_str(),
        ]);
        words.extend(specs.iter().map(String::as_str));
        let ended = Program {
            part: Part::from("git fetch"),
            name: "git",
            arguments: &words,
            input: "",
        }
        .start(self.root)?
        .end(parts)?;
        Ok(if ended.status.success() {
            Fetch::Done
        }
        else {
            Fetch::Failed
        })
    }

    /// The records of each check of the tree: the base that each names, the
    /// trunk and the scope of that base, the key against it, and the shape.
    ///
    /// # Specification
    /// - requires: `listing` and `objects` are the listing and the objects of
    ///   the read, and `fetched` tells how the fetch ended.
    /// - ensures: for each check of the tree, each record of the listing under
    ///   its prefix, with `Ok` when the record names a base that the trunk
    ///   holds, the scope against that base reads, the hash of the key against
    ///   that base is the last part of its ref, and its shape holds. Else the
    ///   reason of the first part that fails, in that order.
    /// - provides: the records of a check that each name their own base.
    /// - fails: each refusal of [`trunk_holds`] and of the scope scripts.
    /// - panics: none.
    /// - intension: one scope script for each distinct base, at the same time
    ///   as the trunk's answers.
    /// - executable: none — the outcome is the external processes'.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Cost
    /// - allocation: the bases, their scopes and one key for each record,
    ///   growth within the records
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a signed record of the tree on a base that the run
    ///   does not name; a key against the run's base refuses it.
    /// - witness: `tests::cli::a_record_of_the_tree_holds_against_its_own_base`
    #[inline]
    fn tree_records(
        &self,
        found: &mut [Found],
        listing: &BTreeMap<String, String>,
        fetched: Fetch,
        objects: &BTreeMap<String, Object>,
        parts: &Parts,
    ) -> Result<(), GateError>
    {
        // The base that each record names, or the reason that it names none.
        let mut named: Vec<(usize, String, String, Result<Commit, String>)> = Vec::new();
        for (place, ((one, row), check)) in found
            .iter()
            .zip(self.rows)
            .zip(&self.request.checks)
            .enumerate()
        {
            if row.form() == Form::Inputs || *one == Found::ByBase {
                continue;
            }
            for (name, commit) in self.under(check, listing) {
                let base = if fetched == Fetch::Done {
                    named_base(objects.get(commit)).and_then(|base| {
                        if base.is_empty() {
                            Err("it names no base".to_owned())
                        }
                        else {
                            Ok(Commit::from(base.as_str()))
                        }
                    })
                }
                else {
                    Err("the fetch failed".to_owned())
                };
                named.push((place, name.clone(), commit.clone(), base));
            }
        }
        let bases: BTreeSet<Commit> = named
            .iter()
            .filter_map(|&(_, _, _, ref base)| base.as_ref().ok().cloned())
            .collect();
        let order: Vec<Option<&Commit>> = if self.request.scope.is_some() {
            Vec::new()
        }
        else {
            bases.iter().map(Some).collect()
        };
        let running = start_scopes(self.script, self.root, &order)?;
        let trunk = trunk_holds(self.request, self.root, &bases, parts)?;
        let scopes: BTreeMap<&Commit, Option<Scope>> = match self.request.scope {
            Some(ref given) => bases
                .iter()
                .map(|base| (base, Some(given.clone())))
                .collect(),
            None => bases
                .iter()
                .zip(
                    finish_scopes(running, parts)?
                        .into_iter()
                        .map(|read| read.map(|text| Scope::from(text.as_str()))),
                )
                .collect(),
        };
        for &(place, ref name, ref commit, ref base) in &named {
            let outcome = base.clone().and_then(|base| {
                if trunk.get(&base) != Some(&Trunk::Holds) {
                    return Err(format!(
                        "the trunk does not hold its base {}",
                        Short(base.as_ref())
                    ));
                }
                let Some(&Some(ref scope)) = scopes.get(&base)
                else {
                    return Err(format!(
                        "the scope against its base {} did not read",
                        Short(base.as_ref())
                    ));
                };
                let (Some(check), Some(row)) =
                    (self.request.checks.get(place), self.rows.get(place))
                else {
                    return Err("its body is not a key".to_owned());
                };
                let key = self
                    .common
                    .line(check, row, self.tree, Some(&base), scope, None)
                    .map_err(|refusal| refusal.to_string())?;
                let own = hash(&key);
                if name.rsplit('/').next() != Some(own.as_str()) {
                    return Err(format!("its key is not the run's key, {own}"));
                }
                shape(objects.get(commit), &key, Some(self.tree)).map(|()| commit.clone())
            });
            if let Some(&mut Found::Records(ref mut records)) = found.get_mut(place) {
                records.push((name.clone(), outcome));
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests
{
    use super::Base64;

    #[test]
    fn base64_writes_each_length_of_a_last_group()
    {
        // `base64 -w0` wrote each of these letters.
        let vectors = [
            ("", ""),
            ("M", "TQ=="),
            ("Ma", "TWE="),
            ("Man", "TWFu"),
            ("Many", "TWFueQ=="),
            ("Manyx", "TWFueXg="),
            ("Manyxy", "TWFueXh5"),
            ("x-access-token:case", "eC1hY2Nlc3MtdG9rZW46Y2FzZQ=="),
        ];
        for (text, letters) in vectors {
            assert_eq!(
                Base64(text.as_bytes()).to_string(),
                letters,
                "the base64 of {text:?}"
            );
        }
    }
}
