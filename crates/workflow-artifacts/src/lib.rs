//! The list of the files that a program writes, and the gate that holds the
//! tree to it.
//!
//! The list is `.config/replay/artifacts.json`. Each row names files of the
//! tree that a program writes, with their kind. An output and a ratchet are
//! functions of the tree, so the tree does not track them. A first input, a
//! record and a record of one moment stay, each with its reason. A row that
//! still has tracked files names the unit that takes them out in `pending`.
//!
//! [`tracked`] refuses a tracked file below a path of an output or of a
//! ratchet, and a `pending` row with no tracked file. [`unclean`] refuses a
//! changed file and a file that git does not know, after the run of the
//! gates. Each finding names the row of the list that holds its path.

extern crate alloc;

use alloc::borrow::ToOwned as _;
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;

/// The path of the list, from the root of the tree.
pub const LIST: &str = ".config/replay/artifacts.json";

/// The kind of the files of a row.
#[derive(Clone, Copy, Debug, Eq, PartialEq, serde::Deserialize)]
pub enum Kind
{
    /// A function of the tree, which the store of the outputs holds.
    #[serde(rename = "output")]
    Output,
    /// A debt list, which the base holds and a change only shrinks.
    #[serde(rename = "ratchet")]
    Ratchet,
    /// A file that a program reads before a program of the tree runs.
    #[serde(rename = "first input")]
    FirstInput,
    /// A file that a person writes.
    #[serde(rename = "record")]
    Record,
    /// The data of one run, which no later change writes.
    #[serde(rename = "record of one moment")]
    RecordOfOneMoment,
}

impl Kind
{
    /// Whether the tree does not track a file of this kind.
    ///
    /// # Specification
    /// - ensures: true for an output and a ratchet, false for each kind that
    ///   stays with its reason.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a tracked file of a ratchet is refused, and a tracked
    ///   file of a record is not.
    /// - witness: `tests::list::a_tracked_output_is_refused_and_a_record_stays`
    #[spec(ensures: |ret| ret == matches!(*self, Self::Output | Self::Ratchet))]
    #[inline]
    #[must_use]
    pub const fn leaves(&self) -> bool
    {
        matches!(*self, Self::Output | Self::Ratchet)
    }

    /// The kind with its article, as a finding names it.
    ///
    /// # Specification
    /// trivial.
    const fn named(self) -> &'static str
    {
        match self {
            Self::Output => "an output",
            Self::Ratchet => "a ratchet",
            Self::FirstInput => "a first input",
            Self::Record => "a record",
            Self::RecordOfOneMoment => "a record of one moment",
        }
    }
}

/// How a row stands for more than one row.
#[derive(Clone, Copy, Debug, Eq, PartialEq, serde::Deserialize)]
pub enum Each
{
    /// One row for each directory of `crates/`, with `{crate}` read as the
    /// name of that directory.
    #[serde(rename = "crate")]
    Crate,
}

/// One row of the list. The list has more fields for the replay; this crate
/// reads the fields of the gate.
#[derive(Clone, Debug, Eq, PartialEq, serde::Deserialize)]
pub struct Row
{
    /// The name of the row.
    pub name: String,
    /// The kind of its files.
    pub kind: Kind,
    /// Its paths: a path that ends in `/` holds each path below it.
    pub paths: Vec<String>,
    /// How the row stands for more than one row.
    #[serde(default)]
    pub each: Option<Each>,
    /// The unit that takes its tracked files out of the tree.
    #[serde(default)]
    pub pending: Option<String>,
}

impl Row
{
    /// The name and the paths of each row that this row stands for.
    ///
    /// # Specification
    /// - ensures: the row itself with no `each`; else one pair for each name of
    ///   `crates`, with `{crate}` in the name and the paths read as that name.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a row of each crate refuses a tracked file below the
    ///   directory of one crate, and names that crate.
    /// - witness: `tests::list::a_row_of_each_crate_names_its_crate`
    #[spec(ensures: |ret| self.each.is_some() || ret.len() == 1)]
    #[inline]
    #[must_use]
    pub fn expanded(
        &self,
        crates: &[String],
    ) -> Vec<(String, Vec<String>)>
    {
        match self.each {
            None => alloc::vec![(self.name.clone(), self.paths.clone())],
            Some(Each::Crate) => crates
                .iter()
                .map(|name| {
                    (
                        self.name.replace("{crate}", name),
                        self.paths
                            .iter()
                            .map(|path| path.replace("{crate}", name))
                            .collect(),
                    )
                })
                .collect(),
        }
    }
}

/// The rows of the list.
///
/// # Specification
/// - ensures: each row of the JSON array, or the error of a text that is no
///   array of rows, of a kind that the list does not have, or of an `each` that
///   it does not have.
/// - panics: none.
///
/// # Errors
/// The [`serde_json::Error`] of a text that is no list of rows.
///
/// # Adequacy
/// - hypothesis: L3 — the rows of an output, a ratchet with `pending` and a
///   record read as written, and a kind that the list does not have refuses.
/// - witness: `tests::list::the_rows_read_their_kinds`
#[spec(ensures: |ret| ret.is_ok() || ret.is_err())]
#[inline]
pub fn read(text: &str) -> Result<Vec<Row>, serde_json::Error>
{
    serde_json::from_str(text)
}

/// Whether the path `held` of the list holds the path `path` of the tree.
///
/// # Specification
/// - ensures: true when the two are equal, or when `held` ends in `/` and
///   `path` starts with it.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a directory holds a file below it and not a file whose
///   name only starts with the name of the directory.
/// - witness: `tests::list::a_directory_holds_the_files_below_it`
#[spec(ensures: |ret| !ret || path.starts_with(held))]
#[inline]
#[must_use]
pub fn holds(
    held: &str,
    path: &str,
) -> bool
{
    path == held || (held.ends_with('/') && path.starts_with(held))
}

/// A refusal of the gate.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Finding
{
    /// A tracked file below a path of an output or of a ratchet.
    Tracked
    {
        /// The path of the file.
        path: String,
        /// The name of the row that holds it.
        row: String,
        /// The kind of the row.
        kind: Kind,
    },
    /// A `pending` row whose paths hold no tracked file.
    Waits
    {
        /// The name of the row.
        row: String,
        /// The unit that it names.
        unit: String,
    },
    /// A file that a run of the gates changed or wrote.
    Unclean
    {
        /// The path of the file.
        path: String,
        /// Whether git does not know the file.
        unknown: bool,
        /// The name of the row that holds it, if a row holds it.
        row: Option<String>,
    },
}

impl fmt::Display for Finding
{
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Tracked {
                ref path,
                ref row,
                kind,
            } => write!(
                f,
                "{path}: the tree tracks it, and the row `{row}` of {LIST} gives it as {}; remove it from the tree, or give its row a kind that stays and a reason",
                kind.named()
            ),
            Self::Waits { ref row, ref unit } => write!(
                f,
                "{LIST}: the row `{row}` waits for `{unit}`, and the tree tracks no file of it; remove its `pending`"
            ),
            Self::Unclean {
                ref path,
                unknown,
                ref row,
            } => {
                let what = if unknown {
                    "git does not know it and does not ignore it"
                }
                else {
                    "it changed"
                };
                match *row {
                    Some(ref row) => write!(
                        f,
                        "{path}: {what} after the gates; the row `{row}` of {LIST} holds it"
                    ),
                    None => write!(
                        f,
                        "{path}: {what} after the gates, and no row of {LIST} holds it; add the row of its writer"
                    ),
                }
            },
        }
    }
}

/// The tracked files that the paths `held` hold, from the sorted `files`.
///
/// # Specification
/// trivial.
fn below<'files>(
    held: &str,
    files: &'files [String],
) -> &'files [String]
{
    let start = files.partition_point(|file| file.as_str() < held);
    let rest = files.get(start ..).unwrap_or_default();
    let count = rest.partition_point(|file| holds(held, file));
    rest.get(.. count).unwrap_or_default()
}

/// The refusals of the tracked files of the tree.
///
/// # Specification
/// - requires: `files` is sorted, as `git ls-files` prints it.
/// - ensures: one [`Finding::Tracked`] for each tracked file below a path of a
///   row of an output or a ratchet with no `pending`, in the order of the rows;
///   then one [`Finding::Waits`] for each `pending` row whose paths hold no
///   tracked file. A row of each crate stands for its row of each name of
///   `crates`.
/// - panics: none.
///
/// # Cost
/// - time: a binary search of `files` for each path of each row
/// - allocation: the findings, and the paths of a row of each crate
///
/// # Adequacy
/// - hypothesis: L3 — a tracked output refuses and names its row; a tracked
///   record stays; a `pending` row with tracked files stays, and one with none
///   refuses.
/// - witness: `tests::list::a_tracked_output_is_refused_and_a_record_stays`
#[spec(ensures: |ret| ret.len() <= files.len().saturating_add(rows.len()))]
#[inline]
#[must_use]
pub fn tracked(
    rows: &[Row],
    crates: &[String],
    files: &[String],
) -> Vec<Finding>
{
    let mut found = Vec::new();
    let mut waits = Vec::new();
    for row in rows.iter().filter(|row| row.kind.leaves()) {
        let expanded = row.expanded(crates);
        match row.pending {
            Some(ref unit) => {
                let any = expanded
                    .iter()
                    .any(|&(_, ref paths)| paths.iter().any(|held| !below(held, files).is_empty()));
                if !any {
                    waits.push(Finding::Waits {
                        row: row.name.clone(),
                        unit: unit.clone(),
                    });
                }
            },
            None => {
                for &(ref name, ref paths) in &expanded {
                    for held in paths {
                        found.extend(below(held, files).iter().map(|path| Finding::Tracked {
                            path: path.clone(),
                            row: name.clone(),
                            kind: row.kind,
                        }));
                    }
                }
            },
        }
    }
    found.append(&mut waits);
    found
}

/// One entry of `git status --porcelain=v1 -z`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Entry
{
    /// The path of the file in the work tree.
    pub path: String,
    /// Whether git does not know the file: the code `??`.
    pub unknown: bool,
}

/// The entries of the output of `git status --porcelain=v1 -z`.
///
/// # Specification
/// - ensures: one entry for each record `XY <path>`, in order. A record of a
///   rename or a copy has a second path, the path of its source, which the
///   entry does not keep.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a changed file, an unknown file and a rename read as
///   their paths in the work tree.
/// - witness: `tests::list::the_status_reads_each_entry`
#[spec(ensures: |ret| ret.len() <= status.len())]
#[inline]
#[must_use]
pub fn entries(status: &[u8]) -> Vec<Entry>
{
    let mut out = Vec::new();
    let mut records = status.split(|&byte| byte == 0);
    while let Some(record) = records.next() {
        let Some((&[x, y], rest)) = record.split_first_chunk::<2>()
        else {
            continue;
        };
        let Some(path) = rest.strip_prefix(b" ")
        else {
            continue;
        };
        if matches!(x, b'R' | b'C') {
            let _source = records.next();
        }
        out.push(Entry {
            path: String::from_utf8_lossy(path).into_owned(),
            unknown: x == b'?' && y == b'?',
        });
    }
    out
}

/// The refusals of a checkout after the run of the gates.
///
/// # Specification
/// - ensures: one [`Finding::Unclean`] for each entry, in order, with the name
///   of the first row of the list whose paths hold it.
/// - panics: none.
///
/// # Cost
/// - time: each path of each row for each entry; a clean checkout has none
///
/// # Adequacy
/// - hypothesis: L3 — a file that a writer of the list changed names its row,
///   and an unknown file of a writer that the list does not have names none.
/// - witness: `tests::list::an_unclean_checkout_names_the_rows_of_its_files`
#[spec(ensures: |ret| ret.len() == status.len())]
#[inline]
#[must_use]
pub fn unclean(
    rows: &[Row],
    crates: &[String],
    status: &[Entry],
) -> Vec<Finding>
{
    let expanded: Vec<(String, Vec<String>)> =
        rows.iter().flat_map(|row| row.expanded(crates)).collect();
    status
        .iter()
        .map(|entry| Finding::Unclean {
            path: entry.path.clone(),
            unknown: entry.unknown,
            row: expanded
                .iter()
                .find(|&&(_, ref paths)| paths.iter().any(|held| holds(held, &entry.path)))
                .map(|&(ref name, _)| name.to_owned()),
        })
        .collect()
}

/// The names of the directories of `crates/` of the tree at `root`, sorted.
///
/// # Specification
/// - ensures: the name of each directory of `crates/`, in byte order.
/// - fails: a directory that cannot be read.
/// - panics: none.
///
/// # Errors
/// The [`std::io::Error`] of `crates/` that cannot be read.
///
/// # Adequacy
/// - hypothesis: L3 — the crates of a tree are its directories of `crates/`,
///   and a file there is none.
/// - witness: `tests::cli::the_gate_refuses_a_tracked_output_and_an_unclean_checkout`
#[spec(ensures: |ret| ret.is_ok() || ret.is_err())]
#[inline]
pub fn crates(root: &std::path::Path) -> std::io::Result<Vec<String>>
{
    let mut names = Vec::new();
    for entry in std::fs::read_dir(root.join("crates"))? {
        let entry = entry?;
        if entry.file_type()?.is_dir()
            && let Some(name) = entry.file_name().to_str()
        {
            names.push(name.to_owned());
        }
    }
    names.sort_unstable();
    Ok(names)
}
