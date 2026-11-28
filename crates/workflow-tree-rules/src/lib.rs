//! The rules of each tracked file of the tree, read from the files of
//! `.config/` that hold their patterns.
//!
//! | Rule | Refuses | Its patterns |
//! | --- | --- | --- |
//! | `residue` | a conflict marker or the residue of a merge tool in a line, and a file named as such residue | [`RESIDUE_LINES`], [`RESIDUE_NAMES`] |
//! | `paths` | the path of a home directory in a line, unless a name of [`PLACEHOLDERS`] follows the home directory | [`HOME_PATHS`], [`PLACEHOLDERS`] |
//! | `markdown` | a tracked Markdown file that the list of READMEs does not hold | [`READMES`] |
//!
//! A file of patterns holds one regular expression a line. A list holds one
//! name or one glob a line, and a line that starts with `#` is a comment. The
//! file `cases.json` beside the patterns of `residue` and of `paths` holds the
//! cases of the rule, and the tests of the crate read them.

extern crate alloc;

use alloc::collections::BTreeSet;
use core::fmt;
use std::path::Path;

use regex::Regex;
use regex::RegexBuilder;

/// The line patterns of the rule `residue`.
pub const RESIDUE_LINES: &str = ".config/merge-residue/patterns";

/// The path patterns of the rule `residue`.
pub const RESIDUE_NAMES: &str = ".config/merge-residue/names";

/// The line patterns of the rule `paths`.
pub const HOME_PATHS: &str = ".config/local-paths/patterns";

/// The names of a home directory that the rule `paths` lets stand.
pub const PLACEHOLDERS: &str = ".config/local-paths/placeholders";

/// The globs of the Markdown files that the rule `markdown` lets stand.
pub const READMES: &str = ".config/markdown/readmes";

/// The files whose lines the rule `residue` does not read: its cases hold
/// residue by design.
const RESIDUE_SKIPS: [&str; 1] = [".config/merge-residue/cases.json"];

/// The files whose lines the rule `paths` does not read: its patterns and its
/// cases hold such paths by design.
const PATH_SKIPS: [&str; 2] = [HOME_PATHS, ".config/local-paths/cases.json"];

/// The bytes at the start of a file in which a NUL makes the file binary, as
/// git reads it.
const BINARY_PROBE: usize = 8_000;

/// A rule of the tree.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Rule
{
    /// No merge residue.
    Residue,
    /// No path of a home directory.
    Paths,
    /// Markdown only on the list of READMEs.
    Markdown,
}

impl Rule
{
    /// Each rule, in the order of its findings.
    pub const ALL: [Self; 3] = [Self::Residue, Self::Paths, Self::Markdown];

    /// The name of the rule, as `--rule` takes it.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub const fn name(self) -> &'static str
    {
        match self {
            Self::Residue => "residue",
            Self::Paths => "paths",
            Self::Markdown => "markdown",
        }
    }

    /// Whether the rule reads the lines of a file.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub const fn reads_lines(self) -> bool
    {
        match self {
            Self::Residue | Self::Paths => true,
            Self::Markdown => false,
        }
    }
}

impl fmt::Display for Rule
{
    /// Writes the name of the rule.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(self.name())
    }
}

/// A file of the rules that cannot be read, or a pattern that does not
/// compile.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Fault
{
    /// The file, from the root of the tree.
    pub path: String,
    /// What failed.
    pub message: String,
}

impl fmt::Display for Fault
{
    /// Writes the path and the message.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "`{}`: {}", self.path, self.message)
    }
}

/// A line or a file that breaks a rule.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Finding
{
    /// The rule.
    pub rule: Rule,
    /// The file, from the root of the tree.
    pub path: String,
    /// The line, from 1; absent for a rule of the name of the file.
    pub line: Option<usize>,
    /// The line as written, or what the name breaks.
    pub text: String,
}

impl fmt::Display for Finding
{
    /// Writes `<path>:<line>: <rule>: <text>`, or `<path>: <rule>: <text>`
    /// for a finding of a name.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a finding of a line and one of a name; a lost line
    ///   number or rule changes the text.
    /// - witness: `tests::cli::the_gate_names_each_finding_and_exits_one`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match self.line {
            Some(line) => write!(f, "{}:{line}: {}: {}", self.path, self.rule, self.text),
            None => write!(f, "{}: {}: {}", self.path, self.rule, self.text),
        }
    }
}

/// The patterns and the lists of each rule.
#[derive(Clone, Debug)]
pub struct Rules
{
    /// The line patterns of `residue`.
    residue_lines: Vec<Regex>,
    /// The path patterns of `residue`.
    residue_names: Vec<Regex>,
    /// The line patterns of `paths`.
    home_paths: Vec<Regex>,
    /// The names of a home directory that `paths` lets stand.
    placeholders: BTreeSet<String>,
    /// The globs of the Markdown files that `markdown` lets stand.
    readmes: Vec<String>,
    /// The name below `/Users/` or `/home/` in a match of `paths`.
    unix_name: Regex,
    /// The name below `\Users\` in a match of `paths`.
    windows_name: Regex,
}

impl Rules
{
    /// Reads the patterns and the lists of each rule below `root`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each pattern of [`RESIDUE_LINES`], [`RESIDUE_NAMES`] and
    ///   [`HOME_PATHS`], one a non-empty line; each name of [`PLACEHOLDERS`]
    ///   and each glob of [`READMES`], one a line that is not empty and not a
    ///   comment.
    /// - provides: the rules that each judgement applies.
    /// - fails: a [`Fault`] naming the file that cannot be read, or the pattern
    ///   that does not compile.
    /// - panics: none.
    /// - executable: none — the outcome is the files on disk.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the files of the tree read, and a pattern that does
    ///   not compile refuses by its file.
    /// - witness: `tests::cases::each_case_of_residue_reads_as_recorded`
    /// - witness: `tests::cli::a_pattern_that_does_not_compile_is_a_fault`
    #[inline]
    pub fn read(root: &Path) -> Result<Self, Fault>
    {
        let text = |path: &str| {
            std::fs::read_to_string(root.join(path)).map_err(|error| Fault {
                path: path.to_owned(),
                message: error.to_string(),
            })
        };
        let patterns = |path: &str| -> Result<Vec<Regex>, Fault> {
            text(path)?
                .lines()
                .filter(|line| !line.is_empty())
                .map(|line| {
                    RegexBuilder::new(line)
                        .multi_line(true)
                        .build()
                        .map_err(|error| Fault {
                            path: path.to_owned(),
                            message: format!("`{line}`: {error}"),
                        })
                })
                .collect()
        };
        let list = |path: &str| -> Result<Vec<String>, Fault> {
            Ok(text(path)?
                .lines()
                .map(str::trim)
                .filter(|line| !line.is_empty() && !line.starts_with('#'))
                .map(str::to_owned)
                .collect())
        };
        let fixed = |pattern: &str| {
            Regex::new(pattern).map_err(|error| Fault {
                path: "the crate".to_owned(),
                message: format!("`{pattern}`: {error}"),
            })
        };
        Ok(Self {
            residue_lines: patterns(RESIDUE_LINES)?,
            residue_names: patterns(RESIDUE_NAMES)?,
            home_paths: patterns(HOME_PATHS)?,
            placeholders: list(PLACEHOLDERS)?.into_iter().collect(),
            readmes: list(READMES)?,
            unix_name: fixed(r#"/(Users|home)/([^/[:space:]"'`),>\]]+)"#)?,
            windows_name: fixed(r"\\Users\\([^\\[:space:]]+)")?,
        })
    }

    /// Whether a line holds merge residue.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: true when a line pattern of `residue` matches the line.
    /// - provides: the rule `residue` of each line.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the match is the clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each case of `.config/merge-residue/cases.json`.
    /// - witness: `tests::cases::each_case_of_residue_reads_as_recorded`
    #[must_use]
    #[inline]
    pub fn residue_line(
        &self,
        line: &str,
    ) -> bool
    {
        self.residue_lines
            .iter()
            .any(|pattern| pattern.is_match(line))
    }

    /// Whether a path names a file of merge residue.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: true when a path pattern of `residue` matches the path.
    /// - provides: the rule `residue` of each name.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the match is the clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each case of `.config/merge-residue/cases.json` with
    ///   a path.
    /// - witness: `tests::cases::each_case_of_residue_reads_as_recorded`
    #[must_use]
    #[inline]
    pub fn residue_name(
        &self,
        path: &str,
    ) -> bool
    {
        self.residue_names
            .iter()
            .any(|pattern| pattern.is_match(path))
    }

    /// Whether a line holds the path of a home directory that no placeholder
    /// names.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: true when a match of a pattern of `paths` in the line has no
    ///   name below its home directory, as the home of `root` has none, or a
    ///   name that [`PLACEHOLDERS`] does not hold. Each match is judged alone.
    /// - provides: the rule `paths` of each line.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the match is the clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each case of `.config/local-paths/cases.json`: a home
    ///   of macOS, of Linux and of Windows, the root's home, a placeholder, and
    ///   a path that only ends in a home name.
    /// - witness: `tests::cases::each_case_of_paths_reads_as_recorded`
    #[must_use]
    #[inline]
    pub fn home_path(
        &self,
        line: &str,
    ) -> bool
    {
        self.home_paths.iter().any(|pattern| {
            pattern.find_iter(line).any(|found| {
                let text = found.as_str();
                let name = self
                    .unix_name
                    .captures(text)
                    .and_then(|captures| captures.get(2))
                    .or_else(|| self.windows_name.captures(text)?.get(1));
                name.is_none_or(|name| !self.placeholders.contains(name.as_str()))
            })
        })
    }

    /// Whether the list of READMEs holds a path.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: true when a glob of [`READMES`] matches the whole path: the
    ///   path has as many segments as the glob, and each `*` of a segment
    ///   stands for any run of characters of that segment.
    /// - provides: the rule `markdown`.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the match is the clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the README of the root and of a crate, a page of the
    ///   docs, a README one folder too deep and a sketch of the corpus; a `*`
    ///   that crosses a `/` changes a verdict.
    /// - witness: `tests::cases::the_list_of_readmes_holds_each_readme_alone`
    #[must_use]
    #[inline]
    pub fn readme(
        &self,
        path: &str,
    ) -> bool
    {
        self.readmes.iter().any(|glob| {
            let mut globs = glob.split('/');
            let mut names = path.split('/');
            loop {
                match (globs.next(), names.next()) {
                    (Some(glob), Some(name)) if segment(glob, name) => {},
                    (None, None) => return true,
                    (Some(_) | None, Some(_) | None) => return false,
                }
            }
        })
    }

    /// Judges the name of a tracked file.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `findings` gains one finding of `residue` when the path names
    ///   merge residue, and one of `markdown` when the path ends in `.md` and
    ///   the list of READMEs does not hold it; each only for a rule of `rules`.
    /// - provides: the rules of each name.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the findings are the clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Rules::residue_name`] and [`Rules::readme`].
    /// - witness: `tests::cli::the_gate_names_each_finding_and_exits_one`
    #[inline]
    pub fn judge_name(
        &self,
        rules: &BTreeSet<Rule>,
        path: &str,
        findings: &mut Vec<Finding>,
    )
    {
        let mut found = |rule: Rule, text: &str| {
            findings.push(Finding {
                rule,
                path: path.to_owned(),
                line: None,
                text: text.to_owned(),
            });
        };
        if rules.contains(&Rule::Residue) && self.residue_name(path) {
            found(Rule::Residue, "a file named as merge residue");
        }
        let markdown = Path::new(path)
            .extension()
            .is_some_and(|extension| extension.eq_ignore_ascii_case("md"));
        if rules.contains(&Rule::Markdown) && markdown && !self.readme(path) {
            found(
                Rule::Markdown,
                "a Markdown file outside the list of READMEs; move its prose into rustdoc",
            );
        }
    }

    /// Judges each line of the text of a tracked file.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `findings` gains one finding of `residue` for each line with
    ///   merge residue, and one of `paths` for each line with the path of a
    ///   home directory, with its number from 1; each only for a rule of
    ///   `rules`, and never for a file that the rule skips by design.
    /// - provides: the rules of each line.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the findings are the clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a conflict marker and a home path in a file of the
    ///   tree, and the cases file that holds them by design.
    /// - witness: `tests::cli::the_gate_names_each_finding_and_exits_one`
    #[inline]
    pub fn judge_text(
        &self,
        rules: &BTreeSet<Rule>,
        path: &str,
        text: &str,
        findings: &mut Vec<Finding>,
    )
    {
        let residue = rules.contains(&Rule::Residue)
            && !RESIDUE_SKIPS.contains(&path)
            && self
                .residue_lines
                .iter()
                .any(|pattern| pattern.is_match(text));
        let paths = rules.contains(&Rule::Paths)
            && !PATH_SKIPS.contains(&path)
            && self.home_paths.iter().any(|pattern| pattern.is_match(text));
        if !(residue || paths) {
            return;
        }
        for (index, line) in text.lines().enumerate() {
            let mut found = |rule: Rule| {
                findings.push(Finding {
                    rule,
                    path: path.to_owned(),
                    line: Some(index.saturating_add(1)),
                    text: line.to_owned(),
                });
            };
            if residue && self.residue_line(line) {
                found(Rule::Residue);
            }
            if paths && self.home_path(line) {
                found(Rule::Paths);
            }
        }
    }
}

/// Whether a file is binary, as git reads it: a NUL in its first bytes.
///
/// # Specification
/// - requires: nothing.
/// - ensures: true when a NUL stands in the first [`BINARY_PROBE`] bytes.
/// - provides: the files whose lines no rule reads.
/// - fails: never.
/// - panics: none.
/// - executable: none — the scan is the clause.
///
/// # Adequacy
/// - hypothesis: L3 — a binary file with a home path is not read.
/// - witness: `tests::cli::the_gate_names_each_finding_and_exits_one`
#[must_use]
#[inline]
pub fn binary(bytes: &[u8]) -> bool
{
    bytes.iter().take(BINARY_PROBE).any(|&byte| byte == 0)
}

/// Whether a glob of one segment matches a whole name: each `*` stands for
/// any run of characters.
///
/// # Specification
/// - requires: nothing.
/// - ensures: true when the literal parts of the glob appear in order in the
///   name, the first at its start and the last at its end.
/// - provides: [`Rules::readme`].
/// - fails: never.
/// - panics: none.
/// - executable: none — the match is the clause.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Rules::readme`].
/// - witness: `tests::cases::the_list_of_readmes_holds_each_readme_alone`
fn segment(
    glob: &str,
    name: &str,
) -> bool
{
    let mut parts = glob.split('*');
    let first = parts.next().unwrap_or_default();
    let Some(mut rest) = name.strip_prefix(first)
    else {
        return false;
    };
    let mut last = None;
    for part in parts {
        if let Some(previous) = last.replace(part) {
            match rest.find(previous) {
                Some(at) => {
                    rest = rest
                        .get(at.saturating_add(previous.len()) ..)
                        .unwrap_or_default();
                },
                None => return false,
            }
        }
    }
    last.map_or(rest.is_empty(), |last| rest.ends_with(last))
}
