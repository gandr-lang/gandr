//! The split of a `sqlite3` dump of a ledger into the files of the tree.
//!
//! A ledger of the tree is the text of a `sqlite3` dump in several files: one
//! file holds the schema, and each other file holds the rows of one name. The
//! name of a row is its first value, such as the crate of a purposes row or
//! the id of a feature. A [`RowPath`] is a path with one `{}`, which the name
//! of each row fills.
//!
//! [`split`] reads the dump line by line. It drops the frame of the dump,
//! `PRAGMA foreign_keys=OFF;`, `BEGIN TRANSACTION;` and `COMMIT;`. A line
//! that opens `INSERT INTO <table> VALUES(` is a row, and it goes to the file
//! of its name, after the rows of that name before it. Each other line goes to
//! the schema. Each line of a file ends with a newline.
//!
//! The split creates no directory. So a row of a name whose directory does not
//! exist, such as a crate with no directory under `crates/`, fails the split.
//! A name that is no plain file name, with a `/` or as `.` or `..`, fails the
//! split too, so a row writes nothing outside its directory.
//!
//! The text of each file stays in memory to the end of the dump. Then each
//! file is written with one call, the schema first and then each file of rows
//! in the order of its first row.

extern crate alloc;

use alloc::collections::BTreeMap;
use core::fmt;
use std::path::Path;
use std::path::PathBuf;

use anodized::spec;

/// The lines of the frame of a `sqlite3` dump, which no file of the tree
/// holds.
const FRAME: [&str; 3] = ["PRAGMA foreign_keys=OFF;", "BEGIN TRANSACTION;", "COMMIT;"];

/// The place of the name of a row in a [`RowPath`].
const NAME: &str = "{}";

/// The path of the file of the rows of a name: the text before and after the
/// one `{}` that the name fills.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RowPath
{
    /// The text before the name.
    before: String,
    /// The text after the name.
    after: String,
}

impl RowPath
{
    /// The row path that `path` spells, such as `crates/{}/purposes.sql`.
    ///
    /// # Specification
    /// - ensures: the row path whose file of a name is `path` with `{}` as the
    ///   name.
    /// - fails: `path` holds not one `{}`.
    /// - panics: none.
    ///
    /// # Errors
    /// [`SplitFault::Template`] naming `path`.
    ///
    /// # Cost
    /// - allocation: the two parts of the path, setup
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a path with one `{}` reads, and a path with none is
    ///   refused by name.
    /// - witness: `tests::split::a_row_with_no_place_is_refused_by_name`
    #[spec(ensures: |ref ret| ret.is_ok() == (path.matches(NAME).count() == 1))]
    #[inline]
    pub fn new(path: &str) -> Result<Self, SplitFault>
    {
        match path.split_once(NAME) {
            Some((before, after)) if !after.contains(NAME) => Ok(Self {
                before: String::from(before),
                after: String::from(after),
            }),
            Some(_) | None => Err(SplitFault::Template {
                path: String::from(path),
            }),
        }
    }

    /// The file of the rows of `name`.
    ///
    /// # Specification
    /// trivial.
    fn of(
        &self,
        name: &str,
    ) -> PathBuf
    {
        PathBuf::from(format!("{}{name}{}", self.before, self.after))
    }
}

/// Why a dump does not split into the files of the tree.
#[derive(Debug)]
pub enum SplitFault
{
    /// The path of the rows holds not one `{}`.
    Template
    {
        /// The path.
        path: String,
    },
    /// A row has no name, or a name that is no plain file name.
    Row
    {
        /// The line of the row in the dump, from one.
        line: usize,
    },
    /// A file could not be written, such as the file of a name whose
    /// directory does not exist.
    Unwritable
    {
        /// The file.
        path: PathBuf,
        /// Why.
        error: std::io::Error,
    },
}

impl fmt::Display for SplitFault
{
    /// Writes the fault and what it names.
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
            Self::Template { ref path } => {
                write!(f, "`{path}` holds not one `{{}}` for the name of a row")
            },
            Self::Row { line } => write!(
                f,
                "line {line} of the dump: the first value of the row is no quoted file name"
            ),
            Self::Unwritable {
                ref path,
                ref error,
            } => write!(f, "{}: cannot write: {error}", path.display()),
        }
    }
}

/// What a split wrote, and the work of each part.
#[derive(Debug, Eq, PartialEq)]
pub struct Split
{
    /// The files written: the schema first, then the file of the rows of each
    /// name in the order of its first row.
    pub paths: Vec<PathBuf>,
    /// The count of the lines of the dump.
    pub lines: usize,
}

/// Split the dump `text` into `schema` and the files that `rows` names.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `schema` holds each line of the dump that is no row and no line
///   of the frame, in order; for each name, the file of `rows` holds each row
///   of that name, in order. The paths are returned, the schema first and then
///   each file of rows in the order of its first row.
/// - fails: a row has no name or a name that is no plain file name; a file
///   cannot be written.
/// - panics: none.
///
/// # Errors
/// [`SplitFault::Row`] naming the line of the row, or
/// [`SplitFault::Unwritable`] naming the file.
///
/// # Cost
/// - time: one pass over the lines of the dump, and one write of each file
/// - allocation: the text of each file and its path, setup
///
/// # Adequacy
/// - hypothesis: L3 — a dump of two tables splits into its schema and one file
///   for each name, with the frame dropped and the rows in the order of the
///   dump; a second split gives the same bytes; a row of a name with no
///   directory and a name with a `/` are refused by name.
/// - witness: `tests::split::a_dump_splits_into_its_schema_and_a_file_for_each_name`
/// - witness: `tests::split::a_row_with_no_place_is_refused_by_name`
#[spec(ensures: |ref ret| ret.as_ref().map_or(true, |split| split.paths.first() == Some(&schema.to_path_buf())))]
#[inline]
pub fn split(
    text: &str,
    schema: &Path,
    rows: &RowPath,
) -> Result<Split, SplitFault>
{
    let mut files: Vec<(PathBuf, String)> = vec![(schema.to_path_buf(), String::new())];
    // The place of the file of each name in `files`.
    let mut places: BTreeMap<String, usize> = BTreeMap::new();
    let mut lines = 0_usize;
    for (index, line) in text.lines().enumerate() {
        lines = index.saturating_add(1);
        if FRAME.contains(&line) {
            continue;
        }
        let file = match row_name(line) {
            Named::Schema => 0,
            Named::Row(name) => *places.entry(name).or_insert_with_key(|name| {
                files.push((rows.of(name), String::new()));
                files.len().saturating_sub(1)
            }),
            Named::Refused => return Err(SplitFault::Row { line: lines }),
        };
        if let Some(&mut (_, ref mut held)) = files.get_mut(file) {
            held.push_str(line);
            held.push('\n');
        }
    }
    let paths = files
        .into_iter()
        .map(|(path, held)| match std::fs::write(&path, held) {
            Ok(()) => Ok(path),
            Err(error) => Err(SplitFault::Unwritable { path, error }),
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(Split { paths, lines })
}

/// What a line of a dump is to the split.
#[derive(Debug, Eq, PartialEq)]
enum Named
{
    /// A line of the schema.
    Schema,
    /// A row, with its name.
    Row(String),
    /// A row with no name, or with a name that is no plain file name.
    Refused,
}

/// What `line` is: a row with the name of its first value, or a line of the
/// schema.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a line that opens `INSERT INTO <table> VALUES(` is a row; its
///   name is its first value, a quoted text with each `''` read as `'`. A row
///   whose first value is not a quoted text, or whose name is empty, `.`, `..`,
///   or holds a `/` or a NUL, is refused. Each other line is of the schema.
/// - panics: none.
/// - executable: none — the cases of the split state each kind of line.
///
/// # Cost
/// - allocation: the name of a row, setup
///
/// # Adequacy
/// - hypothesis: L3 — as [`split`], and a name with a doubled quote is read
///   whole.
/// - witness: `tests::split::a_dump_splits_into_its_schema_and_a_file_for_each_name`
/// - witness: `tests::split::a_row_with_no_place_is_refused_by_name`
fn row_name(line: &str) -> Named
{
    let Some(rest) = line.strip_prefix("INSERT INTO ")
    else {
        return Named::Schema;
    };
    let Some((table, values)) = rest.split_once(" VALUES(")
    else {
        return Named::Schema;
    };
    if table.is_empty() || table.contains(char::is_whitespace) {
        return Named::Schema;
    }
    let Some(quoted) = values.strip_prefix('\'')
    else {
        return Named::Refused;
    };
    let mut name = String::new();
    let mut chars = quoted.chars();
    loop {
        match chars.next() {
            Some('\'') => {
                if chars.as_str().starts_with('\'') {
                    let _doubled = chars.next();
                    name.push('\'');
                }
                else {
                    break;
                }
            },
            Some(other) => name.push(other),
            None => return Named::Refused,
        }
    }
    if name.is_empty() || name == "." || name == ".." || name.contains(['/', '\0']) {
        Named::Refused
    }
    else {
        Named::Row(name)
    }
}
