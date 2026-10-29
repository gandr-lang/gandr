//! Codecov's public API for the repository, read through `curl`: an upload's
//! totals, the upload of `main` before it, and an upload's files.

use core::fmt;
use core::num::ParseIntError;
use core::str::FromStr;
use core::time::Duration;
use std::process::Command;
use std::time::Instant;

use serde::Deserialize;
use serde::de::DeserializeOwned;

use crate::error::GuardError;
use crate::measure::Lines;

/// Codecov's API root for repositories hosted on GitHub.
const API: &str = "https://api.codecov.io/api/v2/github";

/// How long to wait between two readings of an upload still processing.
const POLL: Duration = Duration::from_secs(15);

/// How many of `main`'s uploads, newest first, the baseline is sought among.
const LISTED: u32 = 50;

/// The length of a commit's short form.
const SHORT: usize = 7;

/// A repository on GitHub, `OWNER/NAME`.
///
/// # Specification
/// - provides: the repository whose uploads are compared.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Repository
{
    /// The account owning it.
    owner: String,
    /// Its name within the owner.
    name: String,
}

impl FromStr for Repository
{
    type Err = GuardError;

    /// Reads `OWNER/NAME`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the text, which holds exactly one `/` with a
    ///   non-empty part either side.
    /// - provides: the repository whose uploads are compared.
    /// - fails: [`GuardError::Repository`] for any other text.
    /// - panics: none.
    /// - executable: none — the outcome is the parse itself.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `OWNER/NAME`, no `/`, two `/` and an empty part;
    ///   accepting any of the last three changes a parse.
    /// - witness: `codecov::tests::a_repository_is_owner_and_name`
    #[inline]
    fn from_str(text: &str) -> Result<Self, Self::Err>
    {
        match text.split_once('/') {
            Some((owner, name)) if !owner.is_empty() && !name.is_empty() && !name.contains('/') => {
                Ok(Self {
                    owner: owner.to_owned(),
                    name: name.to_owned(),
                })
            },
            _ => Err(GuardError::Repository {
                text: text.to_owned(),
            }),
        }
    }
}

impl fmt::Display for Repository
{
    /// Writes `OWNER/NAME`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "{}/{}", self.owner, self.name)
    }
}

/// A commit, by its full or abbreviated hexadecimal name.
#[repr(transparent)]
#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
pub struct CommitSha(String);

impl FromStr for CommitSha
{
    type Err = GuardError;

    /// Reads seven to forty lowercase hexadecimal digits.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the text.
    /// - provides: the commit whose upload is compared.
    /// - fails: [`GuardError::Sha`] for any other text.
    /// - panics: none.
    /// - executable: none — the outcome is the parse itself.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — forty and seven digits, six, forty-one, uppercase and
    ///   a branch name; a length bound off by one or accepting uppercase
    ///   changes a parse.
    /// - witness: `codecov::tests::a_commit_is_seven_to_forty_hex_digits`
    #[inline]
    fn from_str(text: &str) -> Result<Self, Self::Err>
    {
        let hex = text
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a' ..= b'f').contains(&byte));
        if hex && (SHORT ..= 40).contains(&text.len()) {
            Ok(Self(text.to_owned()))
        }
        else {
            Err(GuardError::Sha {
                text: text.to_owned(),
            })
        }
    }
}

impl CommitSha
{
    /// The commit's first seven digits, for a title.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub const fn short(&self) -> ShortSha<'_>
    {
        ShortSha(self)
    }
}

impl fmt::Display for CommitSha
{
    /// Writes the commit as given.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(&self.0)
    }
}

/// A commit written by its first seven digits.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct ShortSha<'sha>(&'sha CommitSha);

impl fmt::Display for ShortSha<'_>
{
    /// Writes the commit's first seven digits.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(self.0.0.get(.. SHORT).unwrap_or(&self.0.0))
    }
}

/// How long to wait for Codecov to finish processing an upload.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Wait(Duration);

impl FromStr for Wait
{
    type Err = ParseIntError;

    /// Reads whole seconds written in decimal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from_str(text: &str) -> Result<Self, Self::Err>
    {
        text.parse()
            .map(|seconds| Self(Duration::from_secs(seconds)))
    }
}

/// How many source files an upload covers.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, Ord, PartialEq, PartialOrd)]
pub struct FileCount(u64);

impl fmt::Display for FileCount
{
    /// Writes the count in decimal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "{}", self.0)
    }
}

/// An upload's totals as Codecov states them.
///
/// # Specification
/// - provides: the files it covers and its lines.
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq)]
pub struct Totals
{
    /// The source files the upload covers.
    pub files: FileCount,
    /// The lines measured and covered over all of them.
    #[serde(flatten)]
    pub lines: Lines,
}

/// One processed upload of the repository: its commit and its totals.
///
/// # Specification
/// - provides: one side of the comparison.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Upload
{
    /// The commit measured.
    pub sha: CommitSha,
    /// What the upload covers.
    pub totals: Totals,
}

/// One source file of an upload and its lines.
///
/// # Specification
/// - provides: what a crate's lines are summed from.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
pub struct MeasuredFile
{
    /// The file's path from the repository root.
    #[serde(rename = "name")]
    pub path: FilePath,
    /// Its lines.
    pub totals: Lines,
}

/// A source file's path from the repository root.
#[repr(transparent)]
#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
pub struct FilePath(String);

impl FilePath
{
    /// The crate the file belongs to.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the second component of a path under `crates/`; otherwise the
    ///   first component, which is the whole path of a file at the root.
    /// - provides: the row a file's lines are summed into.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the component match is the clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a file under `crates/`, one under `contrib/` and one
    ///   at the root; taking the first component under `crates/` lumps every
    ///   crate into one row.
    /// - witness: `codecov::tests::a_file_belongs_to_its_crate`
    #[must_use]
    #[inline]
    pub fn crate_name(&self) -> CrateName
    {
        let mut components = self.0.split('/');
        let first = components.next().unwrap_or_default();
        let name = match (first, components.next()) {
            ("crates", Some(directory)) => directory,
            _ => first,
        };
        CrateName(name.to_owned())
    }
}

/// The crate a source file belongs to: the directory under `crates/`, or
/// the first component of a path outside it.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CrateName(String);

impl fmt::Display for CrateName
{
    /// Writes the crate's directory name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(&self.0)
    }
}

/// Codecov's processing state of an upload.
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "lowercase")]
enum State
{
    /// Processed: its totals are final.
    Complete,
    /// Still processing.
    Pending,
    /// Processing failed.
    Error,
    /// Not processed.
    Skipped,
}

impl fmt::Display for State
{
    /// Writes the state as Codecov spells it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            Self::Complete => "complete",
            Self::Pending => "pending",
            Self::Error => "error",
            Self::Skipped => "skipped",
        })
    }
}

/// One commit as Codecov's commit endpoints answer it.
#[derive(Debug, Deserialize)]
struct Listed
{
    /// The commit.
    commitid: CommitSha,
    /// Its upload's processing state.
    state: State,
    /// Its totals, absent until processed.
    totals: Option<Totals>,
}

/// Codecov's commit listing.
#[repr(transparent)]
#[derive(Debug, Deserialize)]
struct Listing
{
    /// The commits, newest first.
    results: Vec<Listed>,
}

/// Codecov's report of one upload.
#[repr(transparent)]
#[derive(Debug, Deserialize)]
struct Report
{
    /// Every file the upload covers.
    files: Vec<MeasuredFile>,
}

/// An address on Codecov's API.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
struct Route(String);

/// Requests `route` and reads its JSON answer.
///
/// # Specification
/// - requires: `curl` on the path.
/// - ensures: the answer, read as `T`.
/// - provides: the one place a Codecov request's failure becomes a refusal.
/// - fails: [`GuardError::Fetch`], naming the address, when `curl` cannot start
///   or exits unsuccessfully (an HTTP error included), or the answer is not
///   `T`.
/// - panics: none.
/// - executable: none — the outcome is the external process's.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — a fake `curl` that answers, one that fails with a
///   message, and one that answers what is not JSON; a swallowed exit status or
///   a lost message changes the observed result.
/// - witness: `tests::cli::a_drop_opens_the_issue`
/// - witness: `tests::cli::a_failing_request_is_reported_with_its_address`
fn get<T>(route: &Route) -> Result<T, GuardError>
where
    T: DeserializeOwned,
{
    let refuse = |message: String| GuardError::Fetch {
        url: route.0.clone(),
        message,
    };
    let output = Command::new("curl")
        .args([
            "--silent",
            "--show-error",
            "--fail",
            "--location",
            "--retry",
            "3",
            "--header",
            "Accept: application/json",
            &route.0,
        ])
        .output()
        .map_err(|error| refuse(error.to_string()))?;
    if !output.status.success() {
        return Err(refuse(format!(
            "{}: {}",
            output.status,
            String::from_utf8_lossy(&output.stderr).trim()
        )));
    }
    serde_json::from_slice(&output.stdout).map_err(|error| refuse(error.to_string()))
}

/// The processed upload of `sha`, waiting up to `wait` for Codecov to finish
/// processing it.
///
/// # Specification
/// - requires: `curl` on the path.
/// - ensures: the commit's totals once Codecov reports it complete.
/// - provides: the later side of the comparison.
/// - fails: [`GuardError::Unprocessed`] when processing ends in error or is
///   skipped, or is still pending once `wait` has passed; every refusal of the
///   request.
/// - panics: none.
/// - executable: none — the outcome is the external service's.
/// - intension: reads again every fifteen seconds while pending, sleeping no
///   later than `wait` allows.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — a complete upload and a pending one with no wait; a
///   pending upload read as complete, or one refused while complete, changes
///   the observed result.
/// - witness: `tests::cli::a_drop_opens_the_issue`
/// - witness: `tests::cli::a_pending_head_is_skipped_for_the_newest_processed_upload_3978`
#[inline]
pub fn upload(
    repository: &Repository,
    sha: &CommitSha,
    wait: Wait,
) -> Result<Upload, GuardError>
{
    let route = Route(format!(
        "{API}/{}/repos/{}/commits/{sha}/",
        repository.owner, repository.name
    ));
    let started = Instant::now();
    loop {
        let listed: Listed = get(&route)?;
        let pending = match (listed.state, listed.totals) {
            (State::Complete, Some(totals)) => {
                return Ok(Upload {
                    sha: listed.commitid,
                    totals,
                });
            },
            (State::Complete, None) | (State::Pending, _) => listed.state,
            (State::Error | State::Skipped, _) => {
                return Err(GuardError::Unprocessed {
                    sha: sha.to_string(),
                    state: listed.state.to_string(),
                });
            },
        };
        let remaining = wait.0.saturating_sub(started.elapsed());
        if remaining.is_zero() {
            return Err(GuardError::Unprocessed {
                sha: sha.to_string(),
                state: pending.to_string(),
            });
        }
        std::thread::sleep(POLL.min(remaining));
    }
}

/// One upload of `main` Codecov has not processed: its commit and the state
/// Codecov lists it in.
///
/// # Specification
/// - provides: the line the report names a skipped upload by.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Skipped
{
    /// The commit measured.
    pub sha: CommitSha,
    /// Codecov's state of its upload: never [`State::Complete`] with totals.
    state: State,
}

impl fmt::Display for Skipped
{
    /// Writes one sentence naming the commit and its state.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(
            f,
            "Codecov has not processed the upload of {}: its state is `{}`. The comparison skips it.",
            self.sha, self.state
        )
    }
}

/// The newest processed upload of `main` at or before a commit's, and every
/// unprocessed upload above it.
///
/// # Specification
/// - provides: the later side of the comparison when the head's upload is
///   unprocessed, and the uploads the report names as skipped.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Newest
{
    /// The newest processed upload.
    pub upload: Upload,
    /// The unprocessed uploads above it, newest first.
    pub skipped: Vec<Skipped>,
}

/// `main`'s uploads from `sha`'s on, newest first, as Codecov lists them.
///
/// # Specification
/// - requires: `curl` on the path.
/// - ensures: the listing's entries from `sha`'s, which comes first.
/// - provides: the listing [`previous`] and [`newest`] walk.
/// - fails: [`GuardError::Unlisted`] when `sha` is not among the newest fifty
///   of `main`'s uploads; every refusal of the request.
/// - panics: none.
/// - executable: none — the outcome is the external service's.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — as [`previous`].
/// - witness: `tests::cli::an_unlisted_head_or_a_missing_baseline_is_refused`
fn listed_from(
    repository: &Repository,
    sha: &CommitSha,
) -> Result<Vec<Listed>, GuardError>
{
    let route = Route(format!(
        "{API}/{}/repos/{}/commits/?branch=main&page_size={LISTED}",
        repository.owner, repository.name
    ));
    let listing: Listing = get(&route)?;
    let from: Vec<Listed> = listing
        .results
        .into_iter()
        .skip_while(|listed| listed.commitid != *sha)
        .collect();
    if from.is_empty() {
        return Err(GuardError::Unlisted {
            sha: sha.to_string(),
        });
    }
    Ok(from)
}

/// The processed upload of `main` that precedes `sha`'s.
///
/// # Specification
/// - requires: `curl` on the path.
/// - ensures: the first processed upload after `sha` in Codecov's listing of
///   `main`'s uploads, newest first.
/// - provides: the earlier side of the comparison.
/// - fails: [`GuardError::Unlisted`] when `sha` is not among the newest fifty
///   of `main`'s uploads; [`GuardError::NoBaseline`] when no processed upload
///   follows it; every refusal of the request.
/// - panics: none.
/// - executable: none — the outcome is the external service's.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — a listing whose entry after the head is unprocessed, one
///   without the head, and one with nothing after it; taking the newest upload,
///   the head's neighbour regardless of state, or the oldest changes the
///   baseline.
/// - witness: `tests::cli::a_drop_opens_the_issue`
/// - witness: `tests::cli::an_unlisted_head_or_a_missing_baseline_is_refused`
#[inline]
pub fn previous(
    repository: &Repository,
    sha: &CommitSha,
) -> Result<Upload, GuardError>
{
    listed_from(repository, sha)?
        .into_iter()
        .skip(1)
        .find_map(|listed| match (listed.state, listed.totals) {
            (State::Complete, Some(totals)) => Some(Upload {
                sha: listed.commitid,
                totals,
            }),
            _ => None,
        })
        .ok_or_else(|| GuardError::NoBaseline {
            sha: sha.to_string(),
        })
}

/// The newest processed upload of `main` at or before `sha`'s, and every
/// unprocessed upload above it.
///
/// # Specification
/// - requires: `curl` on the path.
/// - ensures: the first processed upload from `sha`'s on in Codecov's listing
///   of `main`'s uploads, newest first, and every entry before it, `sha`'s
///   included, as skipped.
/// - provides: the later side of the comparison when `sha`'s upload is
///   unprocessed, so an unprocessed upload never stands in for main's coverage.
/// - fails: [`GuardError::Unlisted`] when `sha` is not among the newest fifty
///   of `main`'s uploads; [`GuardError::NoBaseline`] when no processed upload
///   is listed from it on; every refusal of the request.
/// - panics: none.
/// - executable: none — the outcome is the external service's.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — a pending head above a processed upload, and a pending
///   head above another pending upload; taking the head, the head's neighbour
///   regardless of state, or dropping a skipped upload changes the report.
/// - witness: `tests::cli::a_pending_head_is_skipped_for_the_newest_processed_upload_3978`
/// - witness: `tests::cli::two_unprocessed_uploads_in_a_row_open_their_issue`
#[inline]
pub fn newest(
    repository: &Repository,
    sha: &CommitSha,
) -> Result<Newest, GuardError>
{
    let mut skipped = Vec::new();
    for listed in listed_from(repository, sha)? {
        match (listed.state, listed.totals) {
            (State::Complete, Some(totals)) => {
                return Ok(Newest {
                    upload: Upload {
                        sha: listed.commitid,
                        totals,
                    },
                    skipped,
                });
            },
            (state, _) => skipped.push(Skipped {
                sha: listed.commitid,
                state,
            }),
        }
    }
    Err(GuardError::NoBaseline {
        sha: sha.to_string(),
    })
}

/// Every source file `sha`'s upload covers, with its lines.
///
/// # Specification
/// - requires: `curl` on the path.
/// - ensures: one entry per file Codecov's report lists.
/// - provides: what a crate's lines are summed from.
/// - fails: every refusal of the request.
/// - panics: none.
/// - executable: none — the outcome is the external service's.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — two uploads' files summed per crate; a file dropped or
///   attributed to the other upload changes the table.
/// - witness: `tests::cli::a_drop_opens_the_issue`
#[inline]
pub fn files(
    repository: &Repository,
    sha: &CommitSha,
) -> Result<Vec<MeasuredFile>, GuardError>
{
    let route = Route(format!(
        "{API}/{}/repos/{}/report/?sha={sha}",
        repository.owner, repository.name
    ));
    let report: Report = get(&route)?;
    Ok(report.files)
}

#[cfg(test)]
mod tests
{
    use super::CommitSha;
    use super::FilePath;
    use super::Repository;

    #[test]
    fn a_file_belongs_to_its_crate()
    {
        let name = |path: &str| FilePath(path.to_owned()).crate_name().to_string();
        assert_eq!(name("crates/core-checker/src/lib.rs"), "core-checker");
        assert_eq!(name("contrib/vscode/src/main.ts"), "contrib");
        assert_eq!(name("build.rs"), "build.rs");
    }

    #[test]
    fn a_repository_is_owner_and_name()
    {
        assert_eq!(
            "gandr-lang/gandr"
                .parse::<Repository>()
                .map(|repository| repository.to_string()),
            Ok("gandr-lang/gandr".to_owned())
        );
        for text in ["gandr", "a/b/c", "/gandr", "gandr-lang/", ""] {
            assert!(text.parse::<Repository>().is_err(), "{text}");
        }
    }

    #[test]
    fn a_commit_is_seven_to_forty_hex_digits()
    {
        let full = "f6b04aebd5fff9512341d81310be4a4446db3ba4";
        let sha = full.parse::<CommitSha>().unwrap();
        assert_eq!(sha.to_string(), full);
        assert_eq!(sha.short().to_string(), "f6b04ae");
        assert_eq!(
            "f6b04ae".parse::<CommitSha>().unwrap().short().to_string(),
            "f6b04ae"
        );
        for text in ["f6b04a", &format!("{full}0"), "F6B04AE", "main", ""] {
            assert!(text.parse::<CommitSha>().is_err(), "{text}");
        }
    }
}
