//! The citation window: a work that appeared before the cutoff year, cited
//! at a site that no entry of the policy keeps, is refused.
//!
//! The policy is `.config/references/window.toml`: the line `cutoff = <year>`
//! and one `[[site]]` entry for each site and each older work that the window
//! keeps. An entry has its `site`, its `work` and its `exemplar`, which says
//! why no newer work states what the site builds. An entry that covers a
//! crate or a corpus subject whole is refused, so a new citation of an older
//! work is refused at its site.
//!
//! The year of a work is the year of its `work` row in
//! `ledger/references.sql`. With no row, it is the year that its citation key
//! carries, `Author-YYYY-…`, or its arXiv identifier carries.

use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;

use crate::cites::Citation;
use crate::cites::Kind;

/// The year and the newer work of a cited work, from its `work` row.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Work
{
    /// The year the work appeared.
    pub year: u16,
    /// The newest work by the same authors on the same subject, if known.
    pub newer: Option<String>,
}

/// The `work` rows of `ledger/references.sql`, by key.
///
/// # Specification
/// - ensures: each line `INSERT INTO work VALUES('<key>',<year>,<newer>);`,
///   with `NULL` for no newer work and `''` for a quote in a string, as the row
///   of its key.
/// - panics: none.
///
/// # Cost
/// - allocation: the map of the rows, setup
///
/// # Adequacy
/// - hypothesis: L3 — a row with a newer work, a row with `NULL` and a line of
///   another table read as written.
/// - witness: `tests::window::the_work_rows_read_their_years`
#[inline]
#[must_use]
pub fn works(ledger: &str) -> BTreeMap<String, Work>
{
    ledger
        .lines()
        .filter_map(|line| {
            let values = line
                .strip_prefix("INSERT INTO work VALUES(")?
                .strip_suffix(");")?;
            let (key, rest) = quoted(values)?;
            let (year, newer) = rest.strip_prefix(',')?.split_once(',')?;
            let newer = match newer {
                "NULL" => None,
                quoted_newer => Some(quoted(quoted_newer)?.0),
            };
            Some((key, Work {
                year: year.parse().ok()?,
                newer,
            }))
        })
        .collect()
}

/// The SQL string at the start of `text` and the text after it.
///
/// # Specification
/// trivial.
fn quoted(text: &str) -> Option<(String, &str)>
{
    let mut rest = text.strip_prefix('\'')?;
    let mut value = String::new();
    loop {
        let (part, after) = rest.split_once('\'')?;
        value.push_str(part);
        match after.strip_prefix('\'') {
            Some(more) => {
                value.push('\'');
                rest = more;
            },
            None => return Some((value, after)),
        }
    }
}

/// One `[[site]]` entry of the policy.
#[derive(Clone, Debug, Eq, PartialEq, serde::Deserialize)]
struct Entry
{
    /// The site.
    site: Option<String>,
    /// The work it keeps.
    work: Option<String>,
    /// Why no newer work states what the site builds.
    exemplar: Option<String>,
}

/// An entry of the policy that covers a crate or a subject whole.
#[derive(Clone, Debug, Eq, PartialEq, serde::Deserialize)]
struct Whole
{
    /// The crate.
    name: Option<String>,
    /// The corpus subject.
    subject: Option<String>,
}

/// The policy file, as TOML.
#[derive(Debug, serde::Deserialize)]
struct File
{
    /// The year the window opens.
    cutoff: Option<i64>,
    /// The entries that keep one work at one site.
    #[serde(default)]
    site: Vec<Entry>,
    /// The entries that cover a crate whole.
    #[serde(default, rename = "crate")]
    krate: Vec<Whole>,
    /// The entries that cover a corpus subject whole.
    #[serde(default)]
    corpus: Vec<Whole>,
}

/// Why the policy cannot be read.
#[derive(Debug, Eq, PartialEq)]
pub enum PolicyFault
{
    /// The text is no TOML of the policy's shape.
    Toml(String),
    /// The cutoff is missing, is no year, or is not on its own line
    /// `cutoff = <year>`, which the readers of the issues read.
    Cutoff,
}

impl fmt::Display for PolicyFault
{
    /// The fault, as `window.toml: <what>`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Toml(ref error) => write!(f, "window.toml: {error}"),
            Self::Cutoff => f.write_str(
                "window.toml: `cutoff` is the year the citation window opens, a whole number on its own line `cutoff = <year>`",
            ),
        }
    }
}

/// The policy of the window: the cutoff year, the entries that keep a work
/// at a site, and the entries refused.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Policy
{
    /// The year the window opens.
    pub cutoff: u16,
    /// Each entry that keeps a work at a site: the site, the work, and the
    /// entry as the findings name it.
    kept: Vec<(String, String, String)>,
    /// Each entry refused, as the findings name it, and why.
    refused: Vec<(String, &'static str)>,
}

impl Policy
{
    /// Reads the policy from the text of `window.toml`.
    ///
    /// # Specification
    /// - ensures: the cutoff; each `[[site]]` entry with its site, its work and
    ///   its exemplar kept; each `[[site]]` entry that lacks one of them
    ///   refused; each `[[crate]]` and `[[corpus]]` entry refused.
    /// - fails: text that is no TOML of the policy's shape, and a cutoff that
    ///   is missing, no year, or not on its own line.
    /// - panics: none.
    ///
    /// # Errors
    /// [`PolicyFault::Toml`] or [`PolicyFault::Cutoff`].
    ///
    /// # Cost
    /// - allocation: the entries, setup
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an entry with no exemplar and a crate entry are
    ///   refused by name, and a cutoff that the line form does not read is
    ///   refused.
    /// - witness: `tests::window::an_entry_missing_a_field_and_a_whole_crate_are_refused`
    /// - witness: `tests::window::a_cutoff_off_its_line_is_refused`
    #[inline]
    pub fn read(text: &str) -> Result<Self, PolicyFault>
    {
        let file: File =
            toml::from_str(text).map_err(|error| PolicyFault::Toml(format!("{error}")))?;
        let cutoff = file
            .cutoff
            .and_then(|year| u16::try_from(year).ok())
            .filter(|&year| line_cutoff(text) == Some(year))
            .ok_or(PolicyFault::Cutoff)?;
        let mut kept = Vec::new();
        let mut refused = Vec::new();
        for entry in file.site {
            match (entry.site, entry.work, entry.exemplar) {
                (Some(site), Some(work), Some(exemplar))
                    if !site.is_empty() && !work.is_empty() && !exemplar.is_empty() =>
                {
                    let shown = format!("[[site]] {site} {work}");
                    kept.push((site, work, shown));
                },
                (site, work, _exemplar) => refused.push((
                    format!(
                        "[[site]] {} {}",
                        site.unwrap_or_default(),
                        work.unwrap_or_default()
                    ),
                    "needs a `site`, the `work` it keeps and its `exemplar`: why no newer work states what the site builds",
                )),
            }
        }
        for whole in file.krate {
            refused.push((
                format!("[[crate]] {}", whole.name.unwrap_or_default()),
                "covers a crate whole: write one `[[site]]` entry for each site and each older work",
            ));
        }
        for whole in file.corpus {
            refused.push((
                format!("[[corpus]] {}", whole.subject.unwrap_or_default()),
                "covers a corpus subject whole: write one `[[site]]` entry for each site and each older work",
            ));
        }
        Ok(Self {
            cutoff,
            kept,
            refused,
        })
    }

    /// The count of the entries that keep a work at a site.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn entries(&self) -> usize
    {
        self.kept.len()
    }
}

/// The year on the line `cutoff = <year>` of `text`, as the readers of the
/// issues read it.
///
/// # Specification
/// trivial.
fn line_cutoff(text: &str) -> Option<u16>
{
    text.lines().find_map(|line| {
        let value = line
            .strip_prefix("cutoff")?
            .trim_start()
            .strip_prefix('=')?
            .trim();
        value.parse().ok()
    })
}

/// The year of the cited work `key`: its row's, else the year its citation
/// key or its arXiv identifier carries.
///
/// # Specification
/// - ensures: the row's year; else for `arXiv:YYMM.…` the year `20YY`; for
///   `arXiv:<archive>/YYMM…` the year `19YY` from `90`, else `20YY`; for a key
///   that is no locator, `Author-YYYY-…`, its year; else none.
/// - panics: none.
fn year(
    key: &str,
    works: &BTreeMap<String, Work>,
) -> Option<u16>
{
    if let Some(work) = works.get(key) {
        return Some(work.year);
    }
    let two = |digits: &str| -> Option<u16> {
        let pair = digits.get(.. 2)?;
        pair.bytes()
            .all(|byte| byte.is_ascii_digit())
            .then(|| pair.parse().ok())?
    };
    if let Some(identifier) = key.strip_prefix("arXiv:") {
        if identifier
            .get(4 ..)
            .is_some_and(|rest| rest.starts_with('.'))
            && identifier
                .get(.. 4)
                .is_some_and(|stem| stem.bytes().all(|byte| byte.is_ascii_digit()))
        {
            return two(identifier).map(|yy| yy.saturating_add(2000));
        }
        let (_archive, number) = identifier.split_once('/')?;
        return two(number).map(|yy| yy.saturating_add(if yy >= 90 { 1900 } else { 2000 }));
    }
    if key.starts_with("doi:") {
        return None;
    }
    let (_author, rest) = key.split_once('-')?;
    let digits = rest.get(.. 4)?;
    let first = digits.bytes().next()?;
    (matches!(first, b'1' | b'2')
        && digits.bytes().all(|byte| byte.is_ascii_digit())
        && rest.get(4 ..).is_some_and(|after| after.starts_with('-')))
    .then(|| digits.parse().ok())?
}

/// The findings of the window over the citations `cites`, the work rows
/// `works` and the policy `policy`, in a fixed order.
///
/// # Specification
/// - ensures: first each entry refused; then each citation of a work with no
///   year; then each citation of a work older than the cutoff that no entry
///   keeps at its site, naming the newer work when its row names one; then each
///   entry that keeps no citation older than the cutoff. Within each part, the
///   lines are in the order of their entry or their location, then of their
///   text.
/// - panics: none.
///
/// # Cost
/// - allocation: the findings and the index of the kept entries, setup
///
/// # Adequacy
/// - hypothesis: L3 — a site no entry keeps is refused with its newer work; a
///   site entry keeps its work at its site alone; a work row's year wins over
///   its identifier's; a work with no year and an entry that keeps nothing are
///   refused.
/// - witness: `tests::window::an_older_work_at_a_site_no_entry_keeps_is_refused`
/// - witness: `tests::window::a_site_entry_keeps_its_work_at_its_site_alone`
/// - witness: `tests::window::a_work_row_year_wins_over_its_identifier`
/// - witness: `tests::window::an_entry_missing_a_field_and_a_whole_crate_are_refused`
#[inline]
#[must_use]
pub fn findings(
    cites: &[Citation],
    works: &BTreeMap<String, Work>,
    policy: &Policy,
) -> Vec<String>
{
    let mut parts: [Vec<(String, String)>; 4] = Default::default();
    let &mut [ref mut refused, ref mut undated, ref mut old, ref mut idle] = &mut parts;
    for &(ref entry, why) in &policy.refused {
        refused.push((entry.clone(), format!("window.toml: {entry} {why}")));
    }
    let mut index: BTreeMap<(&str, &str), Vec<usize>> = BTreeMap::new();
    for (at, &(ref site, ref work, _)) in policy.kept.iter().enumerate() {
        index
            .entry((site.as_str(), work.as_str()))
            .or_default()
            .push(at);
    }
    let mut used = vec![false; policy.kept.len()];
    for cite in cites {
        if !matches!(cite.kind, Kind::Cite | Kind::Locator | Kind::Corpus)
            || cite.key.starts_with("vault:")
        {
            continue;
        }
        let Some(year) = year(&cite.key, works)
        else {
            undated.push((
                cite.location.clone(),
                format!(
                    "{}: `{}` states no year: add its row to `work` in ledger/references.sql, the year the work appeared",
                    cite.location, cite.key
                ),
            ));
            continue;
        };
        if year >= policy.cutoff {
            continue;
        }
        let site = cite.site();
        let covering = index.get(&(site.as_str(), cite.key.as_str()));
        for &at in covering.into_iter().flatten() {
            if let Some(slot) = used.get_mut(at) {
                *slot = true;
            }
        }
        if covering.is_none() {
            let newer = works
                .get(&cite.key)
                .and_then(|work| work.newer.as_ref())
                .map_or_else(String::new, |newer| format!(", such as `{newer}`"));
            old.push((
                cite.location.clone(),
                format!(
                    "{}: `{}` appeared in {year}, before the citation window opens in {}; cite the newest work that states what {site} builds{newer}, or allow the site in .config/references/window.toml with why no newer work states it",
                    cite.location, cite.key, policy.cutoff
                ),
            ));
        }
    }
    for (&(_, _, ref shown), used) in policy.kept.iter().zip(used) {
        if !used {
            idle.push((
                shown.clone(),
                format!(
                    "window.toml: {shown} covers no citation older than {}; delete it",
                    policy.cutoff
                ),
            ));
        }
    }
    parts
        .into_iter()
        .flat_map(|mut part| {
            part.sort();
            part.into_iter().map(|(_place, line)| line)
        })
        .collect()
}
