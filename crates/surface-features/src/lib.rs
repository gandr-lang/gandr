//! The features ledger, read as the guide an author writes from.
//!
//! `ledger/features/<id>.sql` holds one row per feature of gandr: its area,
//! its name, its status, one sentence on what it is, and the exemplar and
//! corpus sources that show it. `ledger/features-schema.sql` defines the
//! table. [`FeatureLedger::read`] reads them under a tree's root, and
//! [`FeatureLedger::built_in`] reads the copy the binary was built with: what
//! the running toolchain implements, which a package's constraints are
//! checked against wherever the package stands.
//! `ledger list` prints a line per feature, narrowed to an area and a
//! status; `ledger show <id>` prints a feature's row, then each of its
//! exemplars' sources whole, whose `///` comments explain the form, then its
//! corpus witnesses' paths. The Model Context Protocol server's `ledger_list`
//! and `ledger_show` answer the same as JSON. Before writing a form, an author
//! lists its area and shows each feature the form uses. Every row is held by
//! `check:ledger`, which refuses a path that does not exist and an empty line,
//! and every exemplar by `check:exemplars`, so what the verbs print is what the
//! tree holds.
//!
//! # Boundaries
//!
//! The ledger's files are the parts of one SQLite dump: the schema, and one
//! file for each row. The reader reads the two statements the dump writes for
//! the table: the `CREATE TABLE feature(…)`, whose column names it checks
//! against its own, and one `INSERT INTO feature VALUES(…);` per line, each
//! value `NULL` or a quoted string with `''` for a quote. Every column is
//! `TEXT`, and the table's own constraints keep a newline out of a name and a
//! line. Every other line is the dump's frame and is passed over; a row of
//! any other shape refuses the ledger naming its file and its line
//! ([`FeaturesFault::Features`]). A file of rows holds one row, whose id is
//! the name of the file.
//!
//! The needs of the rows are a second table of the dump, `requires`.
//! `ledger/requires-schema.sql` defines it, and `ledger/requires/<id>.sql`
//! holds one `INSERT INTO requires VALUES('<id>','<need>');` for each row
//! that the row `<id>` needs. A row with no need has no file, and a tree
//! with no directory `ledger/requires/` states no need. A need that names no
//! row refuses the ledger ([`FeaturesFault::Need`]), and so do needs that
//! come back to their row ([`FeaturesFault::Cycle`]). The tier of a row is 1
//! with no need, and 1 more than the largest tier of a need.

use core::fmt;
use core::str::FromStr;
use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
use serde_json::Map;
use serde_json::Value;
use serde_json::json;

/// Why the features ledger could not be read or could not answer.
#[derive(Debug)]
pub enum FeaturesFault
{
    /// A file of the features ledger, or an exemplar it names, could not be
    /// read.
    Unread
    {
        /// The file.
        path: PathBuf,
        /// Why.
        error: std::io::Error,
    },
    /// A line of the features ledger is not what the reader reads.
    Features
    {
        /// The ledger's file.
        path: PathBuf,
        /// The line, counted from one.
        line: usize,
        /// What is wrong with it.
        malformed: Malformed,
    },
    /// A spelling of no status.
    Status
    {
        /// The spelling.
        spelling: String,
    },
    /// An area no feature is in.
    NoArea
    {
        /// The area asked for.
        area: String,
        /// The ledger's areas, in byte order, separated by commas.
        areas: String,
    },
    /// An id no feature has.
    NoFeature
    {
        /// The id asked for.
        id: String,
    },
    /// A line of the table `requires` names an id that no feature has.
    Need
    {
        /// The feature that the line is of.
        feature: String,
        /// What the line says it needs.
        needs: String,
    },
    /// The needs of a feature do not end: they come back to a feature that
    /// they started from.
    Cycle
    {
        /// The first feature, in the ledger's order, whose needs do not end.
        id: String,
    },
}

impl fmt::Display for FeaturesFault
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
            Self::Unread {
                ref path,
                ref error,
            } => write!(f, "{}: cannot read: {error}", path.display()),
            Self::Features {
                ref path,
                line,
                malformed,
            } => write!(f, "{}:{line}: {malformed}", path.display()),
            Self::Status { ref spelling } => write!(
                f,
                "`{spelling}` is no status: implemented, partial, planned or declined"
            ),
            Self::NoArea {
                ref area,
                ref areas,
            } => write!(
                f,
                "no feature is in the area `{area}`; the areas are {areas}"
            ),
            Self::NoFeature { ref id } => write!(f, "no feature is `{id}`"),
            Self::Need {
                ref feature,
                ref needs,
            } => write!(
                f,
                "the feature `{feature}` needs `{needs}`, and one of the two is no feature"
            ),
            Self::Cycle { ref id } => write!(
                f,
                "the needs of the feature `{id}` do not end: a need comes back to its feature"
            ),
        }
    }
}

/// The ledger's schema, from a tree's root.
const SCHEMA: &str = "ledger/features-schema.sql";

/// The directory of the ledger's rows, from a tree's root: one file
/// `<id>.sql` for each row.
const ROWS: &str = "ledger/features";

/// The ledger the binary was built with: the schema, then each row in the
/// order of its id, which the build script writes.
const BUILT_IN: &str = include_str!(concat!(env!("OUT_DIR"), "/features.sql"));

/// The statement that opens the table's definition.
const CREATE: &str = "CREATE TABLE feature(";

/// The statement that opens a row.
const INSERT: &str = "INSERT INTO feature VALUES(";

/// The schema of the table of the needs, from a tree's root.
const NEEDS_SCHEMA: &str = "ledger/requires-schema.sql";

/// The directory of the needs, from a tree's root: one file `<id>.sql` for
/// each row that has a need.
const NEEDS: &str = "ledger/requires";

/// The statement that opens the definition of the table of the needs.
const CREATE_NEEDS: &str = "CREATE TABLE requires(";

/// The statement that opens a need.
const INSERT_NEEDS: &str = "INSERT INTO requires VALUES(";

/// The columns of the table of the needs, in the order the dump writes them.
const NEED_COLUMNS: [&str; 2] = ["feature", "needs"];

/// What a row's `exemplar` holds when the crate tests are its evidence.
const CRATE_TESTS: &str = "crate-tests";

/// The table's columns, in the order the dump writes them.
const COLUMNS: [&str; 12] = [
    "id",
    "area",
    "name",
    "parent",
    "status",
    "notability",
    "compared_to",
    "line",
    "crate",
    "corpus",
    "exemplar",
    "issue",
];

/// Where a feature stands.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Status
{
    /// gandr has it.
    Implemented,
    /// gandr has part of it; the row's issue names the rest.
    Partial,
    /// gandr will have it; the row's issue is the plan.
    Planned,
    /// gandr will not have it; the row's issue says why.
    Declined,
}

impl fmt::Display for Status
{
    /// Writes the status as the ledger spells it.
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
            Self::Implemented => "implemented",
            Self::Partial => "partial",
            Self::Planned => "planned",
            Self::Declined => "declined",
        })
    }
}

impl FromStr for Status
{
    type Err = FeaturesFault;

    /// Reads a status as the ledger spells it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the status whose spelling is `spelling`.
    /// - fails: a spelling of no status.
    /// - panics: none.
    ///
    /// # Errors
    /// [`FeaturesFault::Status`] naming the spelling.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every status reads back from its spelling, and a
    ///   spelling of none is refused.
    /// - witness: `tests::a_status_reads_back_from_its_spelling`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |status| status.to_string() == spelling))]
    #[inline]
    fn from_str(spelling: &str) -> Result<Self, Self::Err>
    {
        match spelling {
            "implemented" => Ok(Self::Implemented),
            "partial" => Ok(Self::Partial),
            "planned" => Ok(Self::Planned),
            "declined" => Ok(Self::Declined),
            _ => Err(FeaturesFault::Status {
                spelling: String::from(spelling),
            }),
        }
    }
}

/// A feature's identifier, its row's `id`.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct FeatureId(pub String);

impl AsRef<str> for FeatureId
{
    /// The identifier's text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        &self.0
    }
}

/// The text of a ledger dump, as the file holds it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Dump<'text>(&'text str);

/// An area of the ledger, a row's `area`.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Area(pub String);

/// One row of the ledger.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Feature
{
    /// `id`.
    id: String,
    /// `area`.
    area: String,
    /// `name`.
    name: String,
    /// `parent`, the feature this one refines.
    parent: Option<String>,
    /// `status`.
    status: Status,
    /// `notability`.
    notability: String,
    /// `compared_to`, what an uncommon or unique feature is uncommon among.
    compared_to: Option<String>,
    /// `line`, the one sentence on what the feature is.
    line: String,
    /// `crate`, the crates that implement it.
    crates: Option<String>,
    /// `corpus`, the sources and tests that witness it.
    corpus: Option<String>,
    /// `exemplar`, the sources that show it, or the crate tests.
    exemplar: Option<String>,
    /// `issue`.
    issue: Option<String>,
    /// The ids of the rows that this one needs, in byte order: its lines of
    /// the table `requires`.
    requires: Vec<String>,
    /// The tier: 1 with no need, and 1 more than the largest tier of a need.
    tier: usize,
}

/// The value of a cell: the closed set of the kinds a row holds.
#[derive(Clone, Copy)]
enum Shown<'row>
{
    /// A column of text.
    Text(&'row str),
    /// The `status` column.
    Status(Status),
}

impl fmt::Display for Shown<'_>
{
    /// Writes the value as the dump writes it.
    ///
    /// # Specification
    /// trivial.
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Text(text) => f.write_str(text),
            Self::Status(ref status) => status.fmt(f),
        }
    }
}

/// One column of a row and its value, `None` where the row holds `NULL`.
#[derive(Clone, Copy)]
struct Cell<'row>
{
    /// The column's name.
    column: &'static str,
    /// The value.
    value: Option<Shown<'row>>,
}

impl Feature
{
    /// The row's columns, in the dump's order, each with its value.
    ///
    /// # Specification
    /// trivial.
    fn cells(&self) -> [Cell<'_>; 12]
    {
        [
            Cell {
                column: "id",
                value: Some(Shown::Text(&self.id)),
            },
            Cell {
                column: "area",
                value: Some(Shown::Text(&self.area)),
            },
            Cell {
                column: "name",
                value: Some(Shown::Text(&self.name)),
            },
            Cell {
                column: "parent",
                value: self.parent.as_deref().map(Shown::Text),
            },
            Cell {
                column: "status",
                value: Some(Shown::Status(self.status)),
            },
            Cell {
                column: "notability",
                value: Some(Shown::Text(&self.notability)),
            },
            Cell {
                column: "compared_to",
                value: self.compared_to.as_deref().map(Shown::Text),
            },
            Cell {
                column: "line",
                value: Some(Shown::Text(&self.line)),
            },
            Cell {
                column: "crate",
                value: self.crates.as_deref().map(Shown::Text),
            },
            Cell {
                column: "corpus",
                value: self.corpus.as_deref().map(Shown::Text),
            },
            Cell {
                column: "exemplar",
                value: self.exemplar.as_deref().map(Shown::Text),
            },
            Cell {
                column: "issue",
                value: self.issue.as_deref().map(Shown::Text),
            },
        ]
    }

    /// The row as a JSON object: each column that holds a value, by name,
    /// then its tier and its needs.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: an object with `id`, `area`, `name`, `status`, `notability`
    ///   and `line`, each other column that holds a value, `tier`, and
    ///   `requires` when the row has a need.
    /// - provides: the rows the Model Context Protocol server's `ledger_list`
    ///   and `ledger_show` answer.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a row with and without its optional columns is read
    ///   back from its object, and a row with a need states it.
    /// - witness: `tests::a_row_is_its_object`
    /// - witness: `tests::a_tier_is_one_more_than_the_largest_tier_of_a_need`
    ///
    /// # Cost
    /// - allocation: the object and each value's text, growth within the row's
    ///   columns
    #[spec(ensures: |ret| ret.get("id").and_then(Value::as_str) == Some(self.id.as_str())
        && ret.get("status").and_then(Value::as_str).and_then(|spelling| spelling.parse::<Status>().ok())
            == Some(self.status))]
    #[inline]
    #[must_use]
    pub fn json(&self) -> Value
    {
        let mut object = Map::new();
        for cell in self.cells() {
            if let Some(value) = cell.value {
                let _replaced = object.insert(String::from(cell.column), json!(value.to_string()));
            }
        }
        let _tier = object.insert(String::from("tier"), json!(self.tier));
        if !self.requires.is_empty() {
            let _needs = object.insert(String::from("requires"), json!(self.requires));
        }
        Value::Object(object)
    }

    /// The tier of the row: 1 with no need, and 1 more than the largest tier
    /// of a need.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn tier(&self) -> usize
    {
        self.tier
    }

    /// The ids of the rows that this one needs, in byte order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn requires(&self) -> &[String]
    {
        self.requires.as_slice()
    }
}

impl fmt::Display for Feature
{
    /// Writes the row as `ledger list` prints it:
    /// `id [status, tier n] name: line`.
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
            "{} [{}, tier {}] {}: {}",
            self.id, self.status, self.tier, self.name, self.line
        )
    }
}

/// A row's statement after its opening: the values, then `);`.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Values<'text>(&'text str);

impl Values<'_>
{
    /// The row's values, in order: `None` for `NULL`, the text for a quoted
    /// string, its doubled quotes read as one.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one value per `NULL` or quoted string the statement lists,
    ///   separated by commas and closed by `);`.
    /// - fails: a value of any other shape, an unclosed string, or text after
    ///   the closing `);`.
    /// - panics: none.
    ///
    /// # Errors
    /// What the row is malformed by.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the committed ledger's rows read whole, a doubled
    ///   quote reads as one, and a number, an unclosed string and a missing
    ///   close are refused.
    /// - witness: `tests::the_committed_ledger_reads_every_row`
    /// - witness: `tests::a_quote_is_written_twice`
    /// - witness: `tests::a_value_of_another_shape_refuses_the_ledger_naming_its_line`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |values| !values.is_empty()))]
    fn read(self) -> Result<Vec<Option<String>>, Malformed>
    {
        let mut values = Vec::new();
        let mut rest = self.0;
        loop {
            if let Some(after) = rest.strip_prefix("NULL") {
                values.push(None);
                rest = after;
            }
            else if let Some(quoted) = rest.strip_prefix('\'') {
                let mut text = String::new();
                let mut remaining = quoted;
                rest = loop {
                    let Some((before, after)) = remaining.split_once('\'')
                    else {
                        return Err(Malformed::Unclosed);
                    };
                    text.push_str(before);
                    match after.strip_prefix('\'') {
                        Some(escaped) => {
                            text.push('\'');
                            remaining = escaped;
                        },
                        None => break after,
                    }
                };
                values.push(Some(text));
            }
            else {
                return Err(Malformed::Value);
            }
            if let Some(after) = rest.strip_prefix(',') {
                rest = after;
            }
            else if rest == ");" {
                return Ok(values);
            }
            else {
                return Err(Malformed::Close);
            }
        }
    }
}

/// How a line of the dump fails to be what the reader reads.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Malformed
{
    /// A value is neither `NULL` nor a quoted string.
    Value,
    /// A quoted string is not closed on its line.
    Unclosed,
    /// A value is followed by neither a comma nor the closing `);`.
    Close,
    /// A row's values are not one per column.
    Width,
    /// A column the table requires holds `NULL`.
    Required,
    /// The table's columns are not the ones the reader reads, in its order.
    Columns,
    /// A file of rows holds not one row, or its row's id is not the name of
    /// the file.
    File,
    /// A file of needs holds no need, or the need of a row that the name of
    /// the file does not name.
    Needs,
}

impl fmt::Display for Malformed
{
    /// Writes what is wrong with the line.
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
            Self::Value => "a value is neither NULL nor a quoted string",
            Self::Unclosed => "a quoted string is not closed on its line",
            Self::Close => "a value is followed by neither a comma nor `);`",
            Self::Width => "the row's values are not one per column",
            Self::Required => "a column the table requires is NULL",
            Self::Columns => "the table's columns are not the ones the reader reads",
            Self::File => "the file holds not one row, or its row's id is not the file's name",
            Self::Needs => {
                "the file holds no need, or the need of a row that its name does not name"
            },
        })
    }
}

/// A row read from its values, in the dump's column order.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the feature whose columns are `values`, in [`COLUMNS`] order.
/// - fails: not one value per column, a required column `NULL`, or a status of
///   no spelling.
/// - panics: none.
///
/// # Errors
/// What the row is malformed by; [`Malformed::Value`] for an unknown status.
///
/// # Adequacy
/// - hypothesis: L3 — the committed ledger's rows read whole, and a short row
///   is refused.
/// - witness: `tests::the_committed_ledger_reads_every_row`
/// - witness: `tests::a_value_of_another_shape_refuses_the_ledger_naming_its_line`
#[spec(ensures: |ref ret| ret.as_ref().map_or(true, |feature| !feature.id.is_empty()))]
fn feature(values: Vec<Option<String>>) -> Result<Feature, Malformed>
{
    let Ok(
        [
            id,
            area,
            name,
            parent,
            status,
            notability,
            compared_to,
            line,
            crates,
            corpus,
            exemplar,
            issue,
        ],
    ) = <[Option<String>; 12]>::try_from(values)
    else {
        return Err(Malformed::Width);
    };
    let (Some(id), Some(area), Some(name), Some(status), Some(notability), Some(line)) =
        (id, area, name, status, notability, line)
    else {
        return Err(Malformed::Required);
    };
    Ok(Feature {
        id,
        area,
        name,
        parent,
        status: status.parse().map_err(|_unknown| Malformed::Value)?,
        notability,
        compared_to,
        line,
        crates,
        corpus,
        exemplar,
        issue,
        requires: Vec::new(),
        tier: 1,
    })
}

/// A line of the table `requires` read from its values: the feature, then
/// the feature that it needs.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the two values, in the order of [`NEED_COLUMNS`].
/// - fails: not two values, or a `NULL`.
/// - panics: none.
///
/// # Errors
/// What the line is malformed by.
///
/// # Adequacy
/// - hypothesis: L3 — the needs of a scratch ledger read whole, and a line of
///   one value is refused.
/// - witness: `tests::a_tier_is_one_more_than_the_largest_tier_of_a_need`
/// - witness: `tests::a_need_of_no_row_and_a_cycle_refuse_the_ledger`
#[spec(ensures: |ref ret| matches!(*ret, Ok(_) | Err(Malformed::Width | Malformed::Required)))]
fn need(values: Vec<Option<String>>) -> Result<(String, String), Malformed>
{
    let Ok([feature, needs]) = <[Option<String>; 2]>::try_from(values)
    else {
        return Err(Malformed::Width);
    };
    let (Some(feature), Some(needs)) = (feature, needs)
    else {
        return Err(Malformed::Required);
    };
    Ok((feature, needs))
}

/// What a text of the dump holds: the rows of the table `feature`, and the
/// lines of the table `requires`, each a feature and a feature it needs.
#[derive(Debug, Default)]
struct Tables
{
    /// The rows.
    features: Vec<Feature>,
    /// The needs.
    needs: Vec<(String, String)>,
}

/// The features ledger: every row, in the dump's order, which is by `id`.
#[derive(Clone, Debug)]
pub struct FeatureLedger
{
    /// The tree the ledger was read under; its paths are relative to it.
    root: PathBuf,
    /// The rows.
    features: Vec<Feature>,
}

/// One exemplar of a shown feature, read whole.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Exemplar
{
    /// Its path, as the row names it.
    path: String,
    /// Its source.
    source: String,
}

/// A feature as `ledger show` prints it: its row, its exemplars' sources and
/// its corpus witnesses' paths.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ShownFeature
{
    /// The row.
    feature: Feature,
    /// Each exemplar the row names, read, in the row's order.
    exemplars: Vec<Exemplar>,
    /// Each corpus path the row names, in the row's order.
    corpus: Vec<String>,
}

impl FeatureLedger
{
    /// Read the ledger under the tree `root`: the schema at
    /// `ledger/features-schema.sql`, each row file of `ledger/features/`,
    /// and, when the tree has the directory `ledger/requires/`, the schema at
    /// `ledger/requires-schema.sql` and each file of needs.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one feature per row file, in the order of the ids, each
    ///   column read from its value, with its needs and its tier.
    /// - fails: a file cannot be read; the columns of a schema are not the
    ///   reader's; a row is not one `NULL` or quoted string per column with
    ///   every required column set and a status of the four; a file of rows
    ///   holds not one row, or a row that its name does not name; a file of
    ///   needs holds no need, or a need of a row that its name does not name;
    ///   a need names no row; the needs of a row do not end.
    /// - panics: none.
    ///
    /// # Errors
    /// [`FeaturesFault::Unread`] naming the file,
    /// [`FeaturesFault::Features`] naming the file, the line and what is
    /// wrong with it, [`FeaturesFault::Need`] or [`FeaturesFault::Cycle`].
    ///
    /// # Cost
    /// - allocation: the text of each file and the paths of the rows, setup
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the committed ledger reads every row file, a scratch
    ///   ledger with a malformed row is refused naming its line, a file whose
    ///   row its name does not name is refused, and so is a file of needs of
    ///   a different row.
    /// - witness: `tests::the_committed_ledger_reads_every_row`
    /// - witness: `tests::a_value_of_another_shape_refuses_the_ledger_naming_its_line`
    /// - witness: `tests::a_row_stands_in_the_file_of_its_id`
    /// - witness: `tests::a_need_of_no_row_and_a_cycle_refuse_the_ledger`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |ledger| ledger.root == root))]
    #[inline]
    pub fn read(root: &Path) -> Result<Self, FeaturesFault>
    {
        let unread = |path: &Path| {
            let path = path.to_path_buf();
            move |error| FeaturesFault::Unread { path, error }
        };
        let schema = root.join(SCHEMA);
        let text = std::fs::read_to_string(&schema).map_err(unread(&schema))?;
        let _columns = Self::parsed(&schema, Dump(&text))?;
        let mut tables = Tables::default();
        for path in Self::files(&root.join(ROWS))? {
            let text = std::fs::read_to_string(&path).map_err(unread(&path))?;
            let mut rows = Self::parsed(&path, Dump(&text))?.features;
            let named = match *rows.as_slice() {
                [ref row] => path.file_stem().is_some_and(|stem| stem == row.id.as_str()),
                _ => false,
            };
            if !named {
                return Err(FeaturesFault::Features {
                    path,
                    line: 1,
                    malformed: Malformed::File,
                });
            }
            tables.features.append(&mut rows);
        }
        let directory = root.join(NEEDS);
        if directory.is_dir() {
            let schema = root.join(NEEDS_SCHEMA);
            let text = std::fs::read_to_string(&schema).map_err(unread(&schema))?;
            let _columns = Self::parsed(&schema, Dump(&text))?;
            for path in Self::files(&directory)? {
                let text = std::fs::read_to_string(&path).map_err(unread(&path))?;
                let mut needs = Self::parsed(&path, Dump(&text))?.needs;
                let named = !needs.is_empty()
                    && needs.iter().all(|need| {
                        path.file_stem()
                            .is_some_and(|stem| stem == need.0.as_str())
                    });
                if !named {
                    return Err(FeaturesFault::Features {
                        path,
                        line: 1,
                        malformed: Malformed::Needs,
                    });
                }
                tables.needs.append(&mut needs);
            }
        }
        Self::settled(root, tables)
    }

    /// The files `*.sql` of `directory`, in the order of their names.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each file of the directory whose extension is `sql`, in the
    ///   byte order of the file stems.
    /// - fails: the directory cannot be read.
    /// - panics: none.
    ///
    /// # Errors
    /// [`FeaturesFault::Unread`] naming the directory.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the committed ledger reads its rows in the order of
    ///   their ids.
    /// - witness: `tests::the_committed_ledger_reads_every_row`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |paths| paths.is_sorted_by(|left, right| left.file_stem() <= right.file_stem())))]
    fn files(directory: &Path) -> Result<Vec<PathBuf>, FeaturesFault>
    {
        let mut paths: Vec<PathBuf> = std::fs::read_dir(directory)
            .and_then(|entries| {
                entries
                    .map(|entry| entry.map(|entry| entry.path()))
                    .collect()
            })
            .map_err(|error| FeaturesFault::Unread {
                path: directory.to_path_buf(),
                error,
            })?;
        paths.retain(|path| path.extension().is_some_and(|extension| extension == "sql"));
        paths.sort_by(|left, right| left.file_stem().cmp(&right.file_stem()));
        Ok(paths)
    }

    /// The ledger of `tables`, under `root`: each row with its needs and its
    /// tier.
    ///
    /// # Specification
    /// - requires: the rows of `tables` are in the byte order of their ids.
    /// - ensures: each row holds the needs that the lines of `tables` give
    ///   it, in byte order, and its tier: 1 with no need, and 1 more than the
    ///   largest tier of a need.
    /// - fails: a line names an id that no row has, or the needs of a row do
    ///   not end.
    /// - panics: none.
    ///
    /// # Errors
    /// [`FeaturesFault::Need`] naming the line, or [`FeaturesFault::Cycle`]
    /// naming the first row whose needs do not end.
    ///
    /// # Termination
    /// - reason: each pass over the rows gives a tier to one row or more, or
    ///   it ends the loop with the refusal of a cycle.
    /// - measure: the rows with no tier.
    ///
    /// # Cost
    /// - allocation: one list of needs and one tier for each row, setup
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a chain of three rows has the tiers 1, 2 and 3, a
    ///   need of no row is refused by its line, and two rows that need each
    ///   other are refused by the first of them.
    /// - witness: `tests::a_tier_is_one_more_than_the_largest_tier_of_a_need`
    /// - witness: `tests::a_need_of_no_row_and_a_cycle_refuse_the_ledger`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |ledger| ledger.root == root
        && ledger.features.iter().all(|feature| feature.tier > feature.requires.len().min(1))))]
    fn settled(
        root: &Path,
        tables: Tables,
    ) -> Result<Self, FeaturesFault>
    {
        let Tables {
            mut features,
            needs,
        } = tables;
        let at = |features: &[Feature], id: &str| {
            features
                .binary_search_by(|row| row.id.as_str().cmp(id))
                .ok()
        };
        let mut edges: Vec<Vec<usize>> = Vec::new();
        edges.resize_with(features.len(), Vec::new);
        for (feature, need) in needs {
            let (Some(from), Some(to)) = (at(&features, &feature), at(&features, &need))
            else {
                return Err(FeaturesFault::Need {
                    feature,
                    needs: need,
                });
            };
            if let Some(below) = edges.get_mut(from) {
                below.push(to);
            }
            if let Some(row) = features.get_mut(from) {
                row.requires.push(need);
            }
        }
        // A tier of 0 is a row that no pass gave a tier yet.
        let mut tiers: Vec<usize> = vec![0_usize; features.len()];
        let mut tiered = 0_usize;
        while tiered < features.len() {
            let before = tiered;
            for (row, below) in edges.iter().enumerate() {
                if tiers.get(row).is_none_or(|&tier| tier != 0_usize) {
                    continue;
                }
                let tier = below
                    .iter()
                    .try_fold(1_usize, |tier, &need| match tiers.get(need) {
                        Some(&under) if under != 0_usize => Some(tier.max(under.saturating_add(1))),
                        _ => None,
                    });
                if let (Some(tier), Some(slot)) = (tier, tiers.get_mut(row)) {
                    *slot = tier;
                    tiered = tiered.saturating_add(1);
                }
            }
            if tiered == before {
                let id = features
                    .iter()
                    .zip(&tiers)
                    .find(|&(_row, &tier)| tier == 0_usize)
                    .map(|(row, _tier)| row.id.clone())
                    .unwrap_or_default();
                return Err(FeaturesFault::Cycle { id });
            }
        }
        for (row, tier) in features.iter_mut().zip(tiers) {
            row.tier = tier;
            row.requires.sort_unstable();
        }
        Ok(Self {
            root: root.to_path_buf(),
            features,
        })
    }

    /// The ledger the binary was built with, its exemplars read under the
    /// working directory.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`Self::read`] reads the tree's own ledger, over the
    ///   schemas, the rows of `ledger/features/` and the needs of
    ///   `ledger/requires/` as the binary was built.
    /// - provides: what the running toolchain implements, read wherever the
    ///   checked package stands.
    /// - fails: as [`Self::read`] for a malformed row, a need of no row and
    ///   needs that do not end; never for the file, which is the binary's own.
    /// - panics: none.
    ///
    /// # Errors
    /// [`FeaturesFault::Features`] naming the line and what is wrong with it,
    /// [`FeaturesFault::Need`] or [`FeaturesFault::Cycle`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the built-in ledger is the committed one, row for
    ///   row, while the tree's ledger is the one the binary was built from.
    /// - witness: `tests::the_built_in_ledger_is_the_committed_one`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |ledger| ledger.root == Path::new(".")))]
    #[inline]
    pub fn built_in() -> Result<Self, FeaturesFault>
    {
        Self::settled(
            Path::new("."),
            Self::parsed(Path::new(ROWS), Dump(BUILT_IN))?,
        )
    }

    /// The tables `dump` holds, read from `path`.
    ///
    /// # Specification
    /// - requires: `dump` is the file at `path`.
    /// - ensures: each row and each need of `dump`, in the order of its lines;
    ///   the columns of each table that `dump` defines are the reader's.
    /// - fails: as [`Self::read`], for a malformed line.
    /// - panics: none.
    ///
    /// # Errors
    /// [`FeaturesFault::Features`] naming `path`, the line and what is wrong
    /// with it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::read`].
    /// - witness: `tests::a_value_of_another_shape_refuses_the_ledger_naming_its_line`
    /// - witness: `tests::a_tier_is_one_more_than_the_largest_tier_of_a_need`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |tables| tables.features.iter().all(|feature| !feature.id.is_empty())))]
    fn parsed(
        path: &Path,
        dump: Dump<'_>,
    ) -> Result<Tables, FeaturesFault>
    {
        let refused = |line: usize, malformed: Malformed| FeaturesFault::Features {
            path: path.to_path_buf(),
            line: line.saturating_add(1),
            malformed,
        };
        let mut tables = Tables::default();
        let mut columns: Option<(Vec<&str>, &[&str])> = None;
        for (number, line) in dump.0.lines().enumerate() {
            if let Some(&mut (ref mut read, expected)) = columns.as_mut() {
                let trimmed = line.trim_start();
                if trimmed.starts_with(')') {
                    if read.as_slice() != expected {
                        return Err(refused(number, Malformed::Columns));
                    }
                    columns = None;
                }
                else if !trimmed.starts_with("CHECK(") && !trimmed.starts_with("PRIMARY KEY(") {
                    read.extend(trimmed.split_whitespace().next());
                }
            }
            else if line == CREATE {
                columns = Some((Vec::with_capacity(COLUMNS.len()), COLUMNS.as_slice()));
            }
            else if line == CREATE_NEEDS {
                columns = Some((
                    Vec::with_capacity(NEED_COLUMNS.len()),
                    NEED_COLUMNS.as_slice(),
                ));
            }
            else if let Some(values) = line.strip_prefix(INSERT) {
                let feature = Values(values)
                    .read()
                    .and_then(feature)
                    .map_err(|malformed| refused(number, malformed))?;
                tables.features.push(feature);
            }
            else if let Some(values) = line.strip_prefix(INSERT_NEEDS) {
                let need = Values(values)
                    .read()
                    .and_then(need)
                    .map_err(|malformed| refused(number, malformed))?;
                tables.needs.push(need);
            }
        }
        Ok(tables)
    }

    /// Where the ledger's feature `id` stands.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the status of the row whose id is `id`.
    /// - provides: a toolchain's answer to a package's `features` constraint,
    ///   which a status [`Status::Implemented`] or [`Status::Partial`] meets.
    /// - fails: no row is `id`.
    /// - panics: none.
    ///
    /// # Errors
    /// [`FeaturesFault::NoFeature`] naming the id.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each of a scratch ledger's four rows stands at its
    ///   own status, and an id no row holds is refused.
    /// - witness: `tests::a_feature_stands_at_its_row_s_status`
    #[spec(ensures: |ref ret| ret.as_ref().err().is_none_or(|fault|
        matches!(*fault, FeaturesFault::NoFeature { id: ref missing } if *missing == id.0)))]
    #[inline]
    pub fn status(
        &self,
        id: &FeatureId,
    ) -> Result<Status, FeaturesFault>
    {
        self.features
            .iter()
            .find(|feature| feature.id == id.0)
            .map(|feature| feature.status)
            .ok_or_else(|| FeaturesFault::NoFeature { id: id.0.clone() })
    }

    /// The ids of the features a toolchain built with this ledger meets: each
    /// row at [`Status::Implemented`] or [`Status::Partial`], in the ledger's
    /// order.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each id [`FeatureLedger::status`] answers implemented or
    ///   partial for, and no other.
    /// - provides: a toolchain's description, which another build compares a
    ///   package's `features` against.
    /// - panics: none.
    /// - executable: none — the ids are an iterator the caller drains.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the implemented and partial rows of a scratch ledger
    ///   are met, its declined and planned rows are not.
    /// - witness: `tests::a_feature_stands_at_its_row_s_status`
    #[inline]
    pub fn met(&self) -> impl Iterator<Item = &str>
    {
        self.features
            .iter()
            .filter(|feature| matches!(feature.status, Status::Implemented | Status::Partial))
            .map(|feature| feature.id.as_str())
    }

    /// The features in `area`, when one is named, with `status`, when one is
    /// named, in the ledger's order.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: every row whose area is `area` and whose status is `status`,
    ///   each where named, and no other, in the ledger's order.
    /// - provides: `ledger list [--area <area>] [--status <status>]`.
    /// - fails: an area no row is in.
    /// - panics: none.
    ///
    /// # Errors
    /// [`FeaturesFault::NoArea`] naming the area and the ledger's areas.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the committed ledger narrows to one area, to one
    ///   status and to both, and an unknown area is refused naming the areas.
    /// - witness: `tests::a_list_narrows_to_an_area_and_a_status`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |listed| listed.iter().all(|feature|
        area.is_none_or(|area| feature.area == area.0) && status.is_none_or(|status| feature.status == status))))]
    #[inline]
    pub fn listed(
        &self,
        area: Option<&Area>,
        status: Option<Status>,
    ) -> Result<Vec<Feature>, FeaturesFault>
    {
        if let Some(area) = area
            && !self.features.iter().any(|feature| feature.area == area.0)
        {
            let mut areas: Vec<&str> = self
                .features
                .iter()
                .map(|feature| feature.area.as_str())
                .collect();
            areas.sort_unstable();
            areas.dedup();
            return Err(FeaturesFault::NoArea {
                area: area.0.clone(),
                areas: areas.join(", "),
            });
        }
        Ok(self
            .features
            .iter()
            .filter(|feature| {
                area.is_none_or(|area| feature.area == area.0)
                    && status.is_none_or(|status| feature.status == status)
            })
            .cloned()
            .collect())
    }

    /// The feature `id`: its row, each exemplar it names read whole, and each
    /// corpus path it names.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the row whose id is `id`; one exemplar per path its
    ///   `exemplar` names other than `crate-tests`, each with the file's text
    ///   under the root; and its `corpus` paths, in the row's order.
    /// - provides: `ledger show <id>`.
    /// - fails: no row is `id`, or an exemplar cannot be read.
    /// - panics: none.
    ///
    /// # Errors
    /// [`FeaturesFault::NoFeature`] naming the id, or [`FeaturesFault::Unread`]
    /// naming the exemplar.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a committed feature shows its exemplar's bytes and
    ///   its corpus paths, a feature whose evidence is the crate tests shows
    ///   none, and an unknown id is refused.
    /// - witness: `tests::a_feature_shows_its_exemplar_whole_and_its_corpus`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |shown| shown.feature.id == id.0))]
    #[inline]
    pub fn shown(
        &self,
        id: &FeatureId,
    ) -> Result<ShownFeature, FeaturesFault>
    {
        let Some(feature) = self.features.iter().find(|feature| feature.id == id.0)
        else {
            return Err(FeaturesFault::NoFeature { id: id.0.clone() });
        };
        let exemplars = feature
            .exemplar
            .iter()
            .flat_map(|paths| paths.split_whitespace())
            .filter(|&path| path != CRATE_TESTS)
            .map(|path| {
                let file = self.root.join(path);
                std::fs::read_to_string(&file)
                    .map(|source| Exemplar {
                        path: String::from(path),
                        source,
                    })
                    .map_err(|error| FeaturesFault::Unread { path: file, error })
            })
            .collect::<Result<Vec<Exemplar>, FeaturesFault>>()?;
        let corpus = feature
            .corpus
            .iter()
            .flat_map(|paths| paths.split_whitespace())
            .map(String::from)
            .collect();
        Ok(ShownFeature {
            feature: feature.clone(),
            exemplars,
            corpus,
        })
    }
}

impl ShownFeature
{
    /// The feature as a JSON object: `feature`, its row's object; `exemplars`,
    /// each `{path, source}`; `corpus`, its paths.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one element of `exemplars` per exemplar read and of `corpus`
    ///   per path, in order.
    /// - provides: the Model Context Protocol server's `ledger_show`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a shown feature's object carries its exemplar's
    ///   source and its corpus paths.
    /// - witness: `tests::a_feature_shows_its_exemplar_whole_and_its_corpus`
    #[spec(ensures: |ret| ret.pointer("/exemplars").and_then(Value::as_array).map(Vec::len) == Some(self.exemplars.len()))]
    #[inline]
    #[must_use]
    pub fn json(&self) -> Value
    {
        let exemplars: Vec<Value> = self
            .exemplars
            .iter()
            .map(|exemplar| json!({ "path": exemplar.path, "source": exemplar.source }))
            .collect();
        json!({
            "feature": self.feature.json(),
            "exemplars": exemplars,
            "corpus": self.corpus,
        })
    }
}

impl fmt::Display for ShownFeature
{
    /// Writes the feature as `ledger show` prints it: each column that holds
    /// a value as `column: value`; then, for each exemplar, `--- <path>` and
    /// its source; then `--- corpus` and each path on a line.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        for cell in self.feature.cells() {
            if let Some(value) = cell.value {
                writeln!(f, "{}: {value}", cell.column)?;
            }
        }
        for exemplar in &self.exemplars {
            writeln!(f, "--- {}", exemplar.path)?;
            f.write_str(&exemplar.source)?;
            if !exemplar.source.ends_with('\n') {
                writeln!(f)?;
            }
        }
        if !self.corpus.is_empty() {
            writeln!(f, "--- corpus")?;
            for path in &self.corpus {
                writeln!(f, "{path}")?;
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests
{
    use core::fmt::Write as _;
    use std::path::Path;
    use std::path::PathBuf;

    use serde_json::json;

    use super::Area;
    use super::FeatureId;
    use super::FeatureLedger;
    use super::FeaturesFault;
    use super::Malformed;
    use super::Status;
    use super::Values;

    /// The tree the committed ledger is read under.
    ///
    /// # Specification
    /// trivial.
    fn committed() -> PathBuf
    {
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
    }

    /// The `INSERT` lines of a scratch ledger.
    #[repr(transparent)]
    #[derive(Clone, Copy)]
    struct Rows<'text>(&'text str);

    /// A scratch tree holding `rows` as its ledger, and its exemplars.
    #[repr(transparent)]
    struct Scratch(PathBuf);

    impl Scratch
    {
        /// A tree named for `name`: the schema of the reader's columns, and
        /// each line of `rows` in the file of the first value that it quotes.
        ///
        /// # Specification
        /// trivial.
        fn new(
            name: &Path,
            rows: Rows<'_>,
        ) -> Self
        {
            let root = std::env::temp_dir().join(format!(
                "gandr-features-{}-{}",
                name.display(),
                std::process::id()
            ));
            std::fs::create_dir_all(root.join(super::ROWS)).expect("the scratch tree is created");
            let mut text = String::from("CREATE TABLE feature(\n");
            for column in super::COLUMNS {
                writeln!(text, "  {column} TEXT,").expect("a string takes a line");
            }
            text.push_str("  CHECK(line <> '')\n) WITHOUT ROWID;\n");
            std::fs::write(root.join(super::SCHEMA), text).expect("the scratch schema is written");
            let scratch = Self(root);
            for row in rows.0.lines() {
                let id = row
                    .split('\'')
                    .nth(1)
                    .expect("a scratch row quotes its id first");
                scratch.row(id, row);
            }
            scratch
        }

        /// Write `row` as the file of rows `<file>.sql`.
        ///
        /// # Specification
        /// trivial.
        fn row(
            &self,
            file: &str,
            row: &str,
        )
        {
            std::fs::write(
                self.0.join(super::ROWS).join(format!("{file}.sql")),
                format!("{row}\n"),
            )
            .expect("the scratch row is written");
        }

        /// Write `lines` as the file of needs `<file>.sql`, with the schema
        /// of the table of the needs.
        ///
        /// # Specification
        /// trivial.
        fn needs(
            &self,
            file: &str,
            lines: &str,
        )
        {
            std::fs::create_dir_all(self.0.join(super::NEEDS))
                .expect("the scratch directory of the needs is created");
            std::fs::write(
                self.0.join(super::NEEDS_SCHEMA),
                "CREATE TABLE requires(\n  feature TEXT,\n  needs TEXT,\n  PRIMARY KEY(feature, needs),\n  CHECK(needs <> feature)\n) WITHOUT ROWID;\n",
            )
            .expect("the scratch schema of the needs is written");
            std::fs::write(self.0.join(super::NEEDS).join(format!("{file}.sql")), lines)
                .expect("the scratch needs are written");
        }
    }

    impl Drop for Scratch
    {
        /// Remove the tree.
        ///
        /// # Specification
        /// trivial.
        fn drop(&mut self)
        {
            let _ignored = std::fs::remove_dir_all(&self.0);
        }
    }

    #[test]
    fn the_committed_ledger_reads_every_row()
    {
        let root = committed();
        let ledger = FeatureLedger::read(&root).expect("the committed ledger reads");
        let rows = std::fs::read_dir(root.join(super::ROWS))
            .expect("the rows list")
            .count();
        assert_eq!(ledger.features.len(), rows, "one feature per row file");
        let ids: Vec<&str> = ledger
            .features
            .iter()
            .map(|feature| feature.id.as_str())
            .collect();
        assert!(
            ids.is_sorted_by(|earlier, later| earlier < later),
            "the ledger orders rows by id"
        );
        assert!(
            ledger
                .features
                .iter()
                .all(|feature| !feature.line.is_empty()),
            "every row says what its feature is"
        );
    }

    #[test]
    fn a_quote_is_written_twice()
    {
        assert_eq!(
            Values("'the pool''s start',NULL,'''');").read(),
            Ok(vec![
                Some(String::from("the pool's start")),
                None,
                Some(String::from("'"))
            ])
        );
    }

    #[test]
    fn a_value_of_another_shape_refuses_the_ledger_naming_its_line()
    {
        for (row, malformed) in [
            ("'a',42);", Malformed::Value),
            ("'a','b);", Malformed::Unclosed),
            ("'a','b'", Malformed::Close),
            ("'a','b');", Malformed::Width),
        ] {
            let scratch = Scratch::new(
                Path::new("malformed"),
                Rows(&format!("INSERT INTO feature VALUES({row}\n")),
            );
            let refused = FeatureLedger::read(&scratch.0);
            assert!(
                matches!(refused, Err(FeaturesFault::Features { line: 1, malformed: named, .. }) if named == malformed),
                "{row}: {refused:?}"
            );
        }
        let required = Scratch::new(
            Path::new("required"),
            Rows(
                "INSERT INTO feature VALUES('a','b','c',NULL,'implemented','ordinary',NULL,NULL,'d',NULL,NULL,NULL);\n",
            ),
        );
        assert!(matches!(
            FeatureLedger::read(&required.0),
            Err(FeaturesFault::Features {
                malformed: Malformed::Required,
                ..
            })
        ));
    }

    #[test]
    fn a_row_stands_in_the_file_of_its_id()
    {
        let row = "INSERT INTO feature VALUES('a','syntax','A',NULL,'planned','ordinary',NULL,'What a is.',NULL,NULL,NULL,'#1');";
        let scratch = Scratch::new(Path::new("named"), Rows(""));
        scratch.row("b", row);
        let elsewhere = FeatureLedger::read(&scratch.0);
        assert!(
            matches!(elsewhere, Err(FeaturesFault::Features { ref path, malformed: Malformed::File, .. }) if path.ends_with("b.sql")),
            "a row in the file of another id: {elsewhere:?}"
        );
        scratch.row("b", &format!("{row}\n{}", row.replace("'a'", "'b'")));
        let two = FeatureLedger::read(&scratch.0);
        assert!(
            matches!(
                two,
                Err(FeaturesFault::Features {
                    malformed: Malformed::File,
                    ..
                })
            ),
            "two rows in one file: {two:?}"
        );
        scratch.row("b", &row.replace("'a'", "'b'"));
        assert_eq!(
            FeatureLedger::read(&scratch.0)
                .expect("each row in the file of its id reads")
                .features
                .len(),
            1
        );
    }

    #[test]
    fn a_status_reads_back_from_its_spelling()
    {
        for status in [
            Status::Implemented,
            Status::Partial,
            Status::Planned,
            Status::Declined,
        ] {
            assert_eq!(status.to_string().parse::<Status>().ok(), Some(status));
        }
        assert!(matches!(
            "finished".parse::<Status>(),
            Err(FeaturesFault::Status { spelling }) if spelling == "finished"
        ));
    }

    #[test]
    fn a_list_narrows_to_an_area_and_a_status()
    {
        let ledger = FeatureLedger::read(&committed()).expect("the committed ledger reads");
        let all = ledger.listed(None, None).expect("an unnarrowed list lists");
        assert_eq!(all.len(), ledger.features.len());
        let workflow = Area(String::from("workflow"));
        let area = ledger
            .listed(Some(&workflow), None)
            .expect("the area lists");
        assert!(!area.is_empty() && area.len() < all.len());
        let planned = ledger
            .listed(None, Some(Status::Planned))
            .expect("the status lists");
        assert!(
            planned
                .iter()
                .all(|feature| feature.status == Status::Planned)
        );
        let both = ledger
            .listed(Some(&workflow), Some(Status::Implemented))
            .expect("both narrow");
        assert_eq!(
            both,
            area.iter()
                .filter(|feature| feature.status == Status::Implemented)
                .cloned()
                .collect::<Vec<_>>()
        );
        let refused = ledger.listed(Some(&Area(String::from("astrology"))), None);
        assert!(
            matches!(refused, Err(FeaturesFault::NoArea { ref area, ref areas }) if area == "astrology" && areas.contains("workflow")),
            "{refused:?}"
        );
    }

    #[test]
    fn a_row_is_its_object()
    {
        let scratch = Scratch::new(
            Path::new("object"),
            Rows(
                "INSERT INTO feature VALUES('a','syntax','A',NULL,'planned','ordinary',NULL,'What a is.',NULL,NULL,NULL,'#1');\n",
            ),
        );
        let ledger = FeatureLedger::read(&scratch.0).expect("the scratch ledger reads");
        let listed = ledger.listed(None, None).expect("it lists");
        assert_eq!(
            listed.iter().map(super::Feature::json).collect::<Vec<_>>(),
            vec![json!({
                "id": "a", "area": "syntax", "name": "A", "status": "planned",
                "notability": "ordinary", "line": "What a is.", "issue": "#1", "tier": 1,
            })]
        );
        assert_eq!(
            listed.iter().map(ToString::to_string).collect::<Vec<_>>(),
            vec!["a [planned, tier 1] A: What a is."]
        );
    }

    /// The three rows of a scratch ledger whose needs are a chain or a cycle.
    const THREE: &str = "INSERT INTO feature VALUES('a','syntax','A',NULL,'planned','ordinary',NULL,'What a is.',NULL,NULL,NULL,'#1');\nINSERT INTO feature VALUES('b','syntax','B',NULL,'planned','ordinary',NULL,'What b is.',NULL,NULL,NULL,'#1');\nINSERT INTO feature VALUES('c','syntax','C',NULL,'planned','ordinary',NULL,'What c is.',NULL,NULL,NULL,'#1');\n";

    #[test]
    fn a_tier_is_one_more_than_the_largest_tier_of_a_need()
    {
        let scratch = Scratch::new(Path::new("tiers"), Rows(THREE));
        scratch.needs("b", "INSERT INTO requires VALUES('b','a');\n");
        scratch.needs(
            "c",
            "INSERT INTO requires VALUES('c','b');\nINSERT INTO requires VALUES('c','a');\n",
        );
        let ledger = FeatureLedger::read(&scratch.0).expect("the scratch ledger reads");
        let listed = ledger.listed(None, None).expect("it lists");
        assert_eq!(
            listed
                .iter()
                .map(|feature| (feature.tier(), feature.requires().to_vec()))
                .collect::<Vec<_>>(),
            vec![
                (1, vec![]),
                (2, vec![String::from("a")]),
                (3, vec![String::from("a"), String::from("b")]),
            ],
            "each row has its needs in byte order and its tier"
        );
        assert_eq!(
            listed.last().map(super::Feature::json),
            Some(json!({
                "id": "c", "area": "syntax", "name": "C", "status": "planned",
                "notability": "ordinary", "line": "What c is.", "issue": "#1", "tier": 3,
                "requires": ["a", "b"],
            })),
            "the object of a row states its tier and its needs"
        );
    }

    #[test]
    fn a_need_of_no_row_and_a_cycle_refuse_the_ledger()
    {
        let absent = Scratch::new(Path::new("need-of-no-row"), Rows(THREE));
        absent.needs("b", "INSERT INTO requires VALUES('b','z');\n");
        let refused = FeatureLedger::read(&absent.0);
        assert!(
            matches!(refused, Err(FeaturesFault::Need { ref feature, ref needs }) if feature == "b" && needs == "z"),
            "{refused:?}"
        );

        let cycle = Scratch::new(Path::new("need-cycle"), Rows(THREE));
        cycle.needs("b", "INSERT INTO requires VALUES('b','c');\n");
        cycle.needs("c", "INSERT INTO requires VALUES('c','b');\n");
        let refused = FeatureLedger::read(&cycle.0);
        assert!(
            matches!(refused, Err(FeaturesFault::Cycle { ref id }) if id == "b"),
            "{refused:?}"
        );

        let misfiled = Scratch::new(Path::new("need-misfiled"), Rows(THREE));
        misfiled.needs("b", "INSERT INTO requires VALUES('c','a');\n");
        let refused = FeatureLedger::read(&misfiled.0);
        assert!(
            matches!(
                refused,
                Err(FeaturesFault::Features {
                    malformed: Malformed::Needs,
                    ..
                })
            ),
            "{refused:?}"
        );

        let short = Scratch::new(Path::new("need-short"), Rows(THREE));
        short.needs("b", "INSERT INTO requires VALUES('b');\n");
        let refused = FeatureLedger::read(&short.0);
        assert!(
            matches!(
                refused,
                Err(FeaturesFault::Features {
                    malformed: Malformed::Width,
                    ..
                })
            ),
            "{refused:?}"
        );
    }

    #[test]
    fn the_built_in_ledger_is_the_committed_one()
    {
        assert_eq!(
            FeatureLedger::built_in()
                .expect("the built-in ledger reads")
                .features,
            FeatureLedger::read(&committed())
                .expect("the committed ledger reads")
                .features,
            "the binary carries the tree's ledger, row for row"
        );
    }

    #[test]
    fn a_feature_stands_at_its_row_s_status()
    {
        let scratch = Scratch::new(
            Path::new("status"),
            Rows(concat!(
                "INSERT INTO feature VALUES('declined','syntax','D',NULL,'declined','ordinary',NULL,'What d is.',NULL,NULL,NULL,'#1');\n",
                "INSERT INTO feature VALUES('implemented','syntax','I',NULL,'implemented','ordinary',NULL,'What i is.',NULL,NULL,'crate-tests',NULL);\n",
                "INSERT INTO feature VALUES('partial','syntax','P',NULL,'partial','ordinary',NULL,'What p is.',NULL,NULL,'crate-tests','#3');\n",
                "INSERT INTO feature VALUES('planned','syntax','Q',NULL,'planned','ordinary',NULL,'What q is.',NULL,NULL,NULL,'#5');\n",
            )),
        );
        let ledger = FeatureLedger::read(&scratch.0).expect("the scratch ledger reads");
        let status = |id: &str| ledger.status(&FeatureId(String::from(id)));
        assert_eq!(
            ["declined", "implemented", "partial", "planned"]
                .map(|id| status(id).expect("the row stands")),
            [
                Status::Declined,
                Status::Implemented,
                Status::Partial,
                Status::Planned
            ],
            "each row at its own status"
        );
        let absent = status("absent");
        assert!(
            matches!(absent, Err(FeaturesFault::NoFeature { ref id }) if id == "absent"),
            "{absent:?}"
        );
        assert_eq!(
            ledger.met().collect::<Vec<_>>(),
            ["implemented", "partial"],
            "a toolchain built with the ledger meets its implemented and partial rows"
        );
    }

    #[test]
    fn a_feature_shows_its_exemplar_whole_and_its_corpus()
    {
        let scratch = Scratch::new(
            Path::new("shown"),
            Rows(
                "INSERT INTO feature VALUES('a','syntax','A',NULL,'implemented','ordinary',NULL,'What a is.','surface-parser','tests/a.rs fixture/a.gandr::a','ledger/a.gandr',NULL);\n\
             INSERT INTO feature VALUES('b','syntax','B',NULL,'implemented','ordinary',NULL,'What b is.','surface-parser','tests/b.rs','crate-tests',NULL);\n",
            ),
        );
        std::fs::write(
            scratch.0.join("ledger/a.gandr"),
            "/// `a`: shown.\ndef a = 1 ;\n",
        )
        .expect("the exemplar is written");
        let ledger = FeatureLedger::read(&scratch.0).expect("the scratch ledger reads");
        let shown = ledger
            .shown(&FeatureId(String::from("a")))
            .expect("a shows");
        assert_eq!(
            shown.to_string(),
            "id: a\narea: syntax\nname: A\nstatus: implemented\nnotability: ordinary\nline: What a is.\n\
             crate: surface-parser\ncorpus: tests/a.rs fixture/a.gandr::a\nexemplar: ledger/a.gandr\n\
             --- ledger/a.gandr\n/// `a`: shown.\ndef a = 1 ;\n--- corpus\ntests/a.rs\nfixture/a.gandr::a\n"
        );
        assert_eq!(
            shown.json().pointer("/exemplars/0/source"),
            Some(&json!("/// `a`: shown.\ndef a = 1 ;\n"))
        );
        let tested = ledger
            .shown(&FeatureId(String::from("b")))
            .expect("b shows");
        assert!(
            tested.json().pointer("/exemplars/0").is_none(),
            "the crate tests are no source"
        );
        assert!(matches!(
            ledger.shown(&FeatureId(String::from("c"))),
            Err(FeaturesFault::NoFeature { id }) if id == "c"
        ));
        let committed = FeatureLedger::read(&committed()).expect("the committed ledger reads");
        let ledger_row = committed
            .shown(&FeatureId(String::from("features-exemplars")))
            .expect("a committed feature shows");
        assert!(
            ledger_row
                .to_string()
                .contains("--- corpus\ncorpus/ledger/features\n")
        );
    }
}
