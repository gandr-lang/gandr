//! Hydration's fetch: a `gh:` coordinate's repository, checked out at the
//! revision its dependent's lock records.
//!
//! # A checkout is named by its revision
//!
//! A `gh:acme-org/rope` coordinate names a repository on GitHub, and its
//! dependent's lock names the revision the package stands at. The repository's
//! top directory at that revision roots the package, which then resolves as a
//! `path:` dependency does. Its checkout sits at
//! `<checkouts>/<owner>/<repository>/<revision>` under the directory this
//! process installed ([`install_hydration`]). A checkout is written whole or
//! not at all: the fetch writes a sibling directory and renames it into place,
//! so a later check reads every checkout standing there as complete, and never
//! fetches it again.
//!
//! # The driver runs `git`
//!
//! The revision is asked of the remote with `git ls-remote`, only when `gandr
//! lock` meets a coordinate its lock does not record, and the tree is fetched
//! with a shallow `git fetch` of that revision alone. GitHub serves a bare
//! revision with no credential, so no crate speaks its protocol. The fetch
//! never prompts, and a fetch that fails is the dependency's refusal, spelled
//! with what `git` answered.
//!
//! # The revision says where, and the address says what
//!
//! The checkout is checked as any source is, and its identity is committed
//! and compared with the lock's pointer as a `path:` dependency's is. The
//! revision only says where to look: two coordinates whose trees agree have
//! one address.
//!
//! # References
//!
//! - `vault:01a17cb3-d471-72b2-9bd2-70a46f74c3de` — lineage: §
//!   build-owner-fetch — a fetch names the address it expects, and the
//!   coordinate only says where to look.
//! - `vault:01a178aa-d585-7822-9cf0-40459729a925` — background: §
//!   package-design-typed-hydration — `fetch : Address × Coordinate → F Bytes`.

use std::path::Path;
use std::path::PathBuf;
use std::process::Command;
use std::process::Stdio;
use std::sync::OnceLock;

use anodized::spec;

use crate::verdicts::AlreadyInstalled;

/// Where GitHub serves its repositories, the remote a driver fetches a `gh:`
/// coordinate from.
pub const GITHUB: &str = "https://github.com";

/// The hydration this process installed.
// economy: one place per process to keep checkouts, read where every import
// of a `gh:` coordinate resolves, as the verdict cache is read where every
// readmission funnels.
static INSTALLED: OnceLock<Hydration> = OnceLock::new();

/// Where a process keeps the checkouts of `gh:` coordinates and the remote it
/// fetches them from.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Hydration
{
    /// The directory every checkout sits under.
    checkouts: PathBuf,
    /// The remote's address, each repository at `<remote>/<owner>/<name>`.
    remote: String,
}

impl Hydration
{
    /// Checkouts kept under `checkouts`, fetched from `remote`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        checkouts: PathBuf,
        remote: String,
    ) -> Self
    {
        Self { checkouts, remote }
    }
}

/// Install `hydration` for every resolution this process makes after, unless
/// one is installed already, which stays.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`AlreadyInstalled`].
#[inline]
pub fn install_hydration(hydration: Hydration) -> Result<(), AlreadyInstalled>
{
    INSTALLED
        .set(hydration)
        .map_err(|_refused| AlreadyInstalled)
}

/// A repository on GitHub, as a `gh:` coordinate writes it.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Repository
{
    /// The account or organisation holding it.
    owner: String,
    /// Its name.
    name: String,
}

impl Repository
{
    /// The repository `written` names, `acme-org/rope`; none for a text that
    /// is not an owner and a name joined by one slash.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: present exactly when `written` is two segments joined by one
    ///   `/`, the owner of ASCII letters, digits and `-`, the name of ASCII
    ///   letters, digits, `-`, `_` and `.` and neither `.` nor `..`: GitHub's
    ///   own names, which never climb out of the checkout's directory.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a coordinate reads back as it is written, and a
    ///   segment that climbs or a third segment reads as none.
    /// - witness: `tests::package::a_gh_coordinate_reads_back_and_refuses_a_climbing_name_4714`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.as_ref().is_none_or(|repository| alloc::format!("{repository}") == written.0))]
    pub fn written(written: Written<'_>) -> Option<Self>
    {
        let (owner, name) = written.0.split_once('/')?;
        let owned = !owner.is_empty()
            && owner
                .bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || byte == b'-');
        let named = !name.is_empty()
            && name != "."
            && name != ".."
            && name
                .bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'_' | b'.'));
        (owned && named).then(|| Self {
            owner: String::from(owner),
            name: String::from(name),
        })
    }

    /// The repository's address on `remote`.
    ///
    /// # Specification
    /// trivial.
    fn address(
        &self,
        remote: &Remote<'_>,
    ) -> String
    {
        alloc::format!("{}/{}/{}", remote.0, self.owner, self.name)
    }
}

impl core::fmt::Display for Repository
{
    /// The repository as a coordinate writes it, `acme-org/rope`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        write!(f, "{}/{}", self.owner, self.name)
    }
}

/// A text a coordinate writes after its scheme.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct Written<'text>(pub &'text str);

/// A remote's address, as the installed hydration names it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Remote<'text>(&'text str);

/// The arguments a `git` command runs with, after its directory.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Arguments<'list>(&'list [&'list str]);

/// A revision of a repository: the 20 bytes of a commit's object name.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Revision([u8; 20]);

impl Revision
{
    /// The revision the 40 lowercase hexadecimal digits `written` opens with
    /// spell, and what follows them; none when it opens with fewer.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: present exactly when `written` opens with 40 lowercase
    ///   hexadecimal digits; the revision they spell, which displays as them.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a lock recording a revision reads back equal, and an
    ///   uppercase or short revision reads as none.
    /// - witness: `tests::package::a_gh_coordinate_reads_back_and_refuses_a_climbing_name_4714`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.is_none_or(|(revision, rest)| alloc::format!("{revision}").len() == 40
        && written.0.len() == rest.0.len().saturating_add(40)))]
    pub fn opening(written: Written<'_>) -> Option<(Self, Written<'_>)>
    {
        let mut bytes = [0_u8; 20];
        for (index, byte) in bytes.iter_mut().enumerate() {
            let at = index.saturating_mul(2);
            let pair = written.0.get(at .. at.saturating_add(2))?;
            if !pair
                .bytes()
                .all(|digit| matches!(digit, b'0' ..= b'9' | b'a' ..= b'f'))
            {
                return None;
            }
            *byte = u8::from_str_radix(pair, 16).ok()?;
        }
        Some((Self(bytes), Written(written.0.get(40 ..)?)))
    }
}

impl core::fmt::Display for Revision
{
    /// The revision as 40 lowercase hexadecimal digits.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        self.0.iter().try_for_each(|byte| write!(f, "{byte:02x}"))
    }
}

/// The checkout of `repository` at `revision` standing under the installed
/// hydration; none when no hydration is installed or none stands there.
///
/// # Specification
/// trivial.
#[must_use]
pub(super) fn checkout(
    repository: &Repository,
    revision: Revision,
) -> Option<PathBuf>
{
    let directory = placed(INSTALLED.get()?, repository, revision);
    directory.is_dir().then_some(directory)
}

/// The directory the checkout of `repository` at `revision` sits at under
/// `hydration`.
///
/// # Specification
/// trivial.
fn placed(
    hydration: &Hydration,
    repository: &Repository,
    revision: Revision,
) -> PathBuf
{
    hydration
        .checkouts
        .join(&repository.owner)
        .join(&repository.name)
        .join(alloc::format!("{revision}"))
}

/// The revision the remote's `HEAD` of `repository` names now.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the revision `git ls-remote <remote>/<owner>/<name> HEAD` answers
///   first, run in the checkouts' directory and never prompting, so no
///   repository the process runs in rewrites the remote's address.
/// - provides: the revision `gandr lock` records for a coordinate its lock does
///   not.
/// - fails: [`Unfetched`] when no hydration is installed, `git` cannot run or
///   fails, or it answers no revision.
/// - panics: none.
/// - executable: none — the answer is the remote's.
///
/// # Errors
/// [`Unfetched`], as above.
///
/// # Adequacy
/// - hypothesis: L3 — a repository's `HEAD` is the revision the lock records.
/// - witness: `tests::package::a_gh_coordinate_is_fetched_at_the_revision_its_lock_records_4714`
pub(super) fn head(repository: &Repository) -> Result<Revision, Unfetched>
{
    let hydration = INSTALLED.get().ok_or(Unfetched::Uninstalled)?;
    std::fs::create_dir_all(&hydration.checkouts)
        .map_err(|error| Unfetched::Unwritten(error.to_string()))?;
    let answer = git(
        &hydration.checkouts,
        Arguments(&[
            "ls-remote",
            &repository.address(&Remote(&hydration.remote)),
            "HEAD",
        ]),
    )?;
    Revision::opening(Written(&answer))
        .map(|(revision, _rest)| revision)
        .ok_or_else(|| Unfetched::Git(alloc::format!("`HEAD` names no revision: {answer}")))
}

/// The checkout of `repository` at `revision`: the one standing, or one
/// fetched now.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the directory [`checkout`] names. Where none stands, `git`
///   fetches the revision alone, shallow and never prompting, into a sibling
///   directory, checks its `HEAD` is the revision, drops its `.git` and renames
///   it into place; a checkout another process placed first is read as it
///   stands.
/// - provides: the tree a `gh:` dependency resolves as.
/// - fails: [`Unfetched`] when no hydration is installed, the directory cannot
///   be written, or `git` fails or checks out another revision.
/// - panics: none.
/// - executable: none — the clause is about the file system and the remote.
///
/// # Errors
/// [`Unfetched`], as above.
///
/// # Adequacy
/// - hypothesis: L3 — a revision is fetched once, read again from its checkout,
///   and fetched again once its checkout is removed.
/// - witness: `tests::package::a_gh_coordinate_is_fetched_at_the_revision_its_lock_records_4714`
pub(super) fn fetched(
    repository: &Repository,
    revision: Revision,
) -> Result<PathBuf, Unfetched>
{
    let hydration = INSTALLED.get().ok_or(Unfetched::Uninstalled)?;
    let directory = placed(hydration, repository, revision);
    if directory.is_dir() {
        return Ok(directory);
    }
    let parent = directory.parent().ok_or(Unfetched::Uninstalled)?;
    let staging = parent.join(alloc::format!(".{revision}.{}", std::process::id()));
    let written = |error: std::io::Error| Unfetched::Unwritten(error.to_string());
    if staging.exists() {
        std::fs::remove_dir_all(&staging).map_err(written)?;
    }
    std::fs::create_dir_all(&staging).map_err(written)?;
    let spelled = alloc::format!("{revision}");
    let address = repository.address(&Remote(&hydration.remote));
    let steps = git(&staging, Arguments(&["init", "--quiet"]))
        .and_then(|_| {
            git(
                &staging,
                Arguments(&["fetch", "--quiet", "--depth", "1", &address, &spelled]),
            )
        })
        .and_then(|_| {
            git(
                &staging,
                Arguments(&[
                    "-c",
                    "advice.detachedHead=false",
                    "checkout",
                    "--quiet",
                    "FETCH_HEAD",
                ]),
            )
        })
        .and_then(|_| git(&staging, Arguments(&["rev-parse", "HEAD"])));
    let checked = match steps {
        Ok(head) if head.trim() == spelled => std::fs::remove_dir_all(staging.join(".git"))
            .and_then(|()| std::fs::rename(&staging, &directory))
            .map_err(written),
        Ok(head) => Err(Unfetched::Git(alloc::format!(
            "the fetch checked out `{}`, not `{spelled}`",
            head.trim()
        ))),
        Err(unfetched) => Err(unfetched),
    };
    match checked {
        Ok(()) => Ok(directory),
        Err(_) if directory.is_dir() => {
            drop(std::fs::remove_dir_all(&staging));
            Ok(directory)
        },
        Err(unfetched) => {
            drop(std::fs::remove_dir_all(&staging));
            Err(unfetched)
        },
    }
}

/// What `git` writes to standard output run with `arguments` in `directory`,
/// never prompting and never reading a repository above `directory`: one the
/// process runs in would rewrite the remote's address by its own
/// configuration.
///
/// # Specification
/// trivial.
fn git(
    directory: &Path,
    arguments: Arguments<'_>,
) -> Result<String, Unfetched>
{
    let output = Command::new("git")
        .arg("-C")
        .arg(directory)
        .args(arguments.0)
        .env("GIT_TERMINAL_PROMPT", "0")
        .env("GIT_CEILING_DIRECTORIES", directory)
        .stdin(Stdio::null())
        .output()
        .map_err(|error| Unfetched::Git(alloc::format!("`git` does not run: {error}")))?;
    if output.status.success() {
        Ok(String::from_utf8_lossy(&output.stdout).into_owned())
    }
    else {
        Err(Unfetched::Git(
            String::from_utf8_lossy(&output.stderr).trim().to_owned(),
        ))
    }
}

/// Why a `gh:` coordinate's tree was not fetched.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Unfetched
{
    /// The process installed no hydration: no directory keeps checkouts.
    Uninstalled,
    /// The checkout's directory cannot be written.
    Unwritten(String),
    /// `git` failed, or answered otherwise than asked; what it said.
    Git(String),
}

impl core::fmt::Display for Unfetched
{
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        match *self {
            Self::Uninstalled => {
                f.write_str("no directory keeps checkouts: set `XDG_CACHE_HOME` or `HOME`")
            },
            Self::Unwritten(ref why) => write!(f, "the checkout cannot be written: {why}"),
            Self::Git(ref said) => write!(f, "git: {said}"),
        }
    }
}

impl core::error::Error for Unfetched
{
}
