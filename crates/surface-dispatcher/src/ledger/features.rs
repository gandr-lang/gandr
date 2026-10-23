//! The features ledger, read as the guide an author writes from.
//!
//! `ledger/features.sql` holds one row per feature of gandr: its area, its
//! name, its status, one sentence on what it is, and the exemplar and corpus
//! sources that show it. [`FeatureLedger::read`] reads it under a tree's root.
//! `gandr ledger list` prints a line per feature, narrowed to an area and a
//! status; `gandr ledger show <id>` prints a feature's row, then each of its
//! exemplars' sources whole, whose `///` comments explain the form, then its
//! corpus witnesses' paths. The Model Context Protocol server's `ledger_list`
//! and `ledger_show` answer the same as JSON. Before writing a form, an author
//! lists its area and shows each feature the form uses. Every row is held by
//! `check:ledger`, which refuses a path that does not exist and an empty line,
//! and every exemplar by `check:exemplars`, so what the verbs print is what the
//! tree holds.
//!
//! # The dump is read, never executed
//!
//! The ledger's one copy is a SQLite dump. The reader reads the two statements
//! the dump writes for the table: the `CREATE TABLE feature(…)`, whose column
//! names it checks against its own, and one `INSERT INTO feature VALUES(…);`
//! per line, each value `NULL` or a quoted string with `''` for a quote. Every
//! column is `TEXT`, and the table's own constraints keep a newline out of a
//! name and a line. Every other line is the dump's frame and is passed over; a
//! row of any other shape refuses the ledger naming its line
//! ([`LedgerFault::Features`]).

use core::fmt;
use core::str::FromStr;
use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
use serde_json::Map;
use serde_json::Value;
use serde_json::json;

use super::LedgerFault;

/// The ledger's file, from a tree's root.
const LEDGER: &str = "ledger/features.sql";

/// The statement that opens the table's definition.
const CREATE: &str = "CREATE TABLE feature(";

/// The statement that opens a row.
const INSERT: &str = "INSERT INTO feature VALUES(";

/// What a row's `exemplar` holds when the crate tests are its evidence.
const CRATE_TESTS: &str = "crate-tests";

/// The table's columns, in the order the dump writes them.
const COLUMNS: [&str; 13] = [
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
    "since",
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
    type Err = LedgerFault;

    /// Reads a status as the ledger spells it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the status whose spelling is `spelling`.
    /// - fails: a spelling of no status.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LedgerFault::Status`] naming the spelling.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every status reads back from its spelling, and a
    ///   spelling of none is refused.
    /// - witness: `ledger::features::tests::a_status_reads_back_from_its_spelling`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |status| status.to_string() == spelling))]
    #[inline]
    fn from_str(spelling: &str) -> Result<Self, Self::Err>
    {
        match spelling {
            "implemented" => Ok(Self::Implemented),
            "partial" => Ok(Self::Partial),
            "planned" => Ok(Self::Planned),
            "declined" => Ok(Self::Declined),
            _ => Err(LedgerFault::Status {
                spelling: String::from(spelling),
            }),
        }
    }
}

/// A feature's identifier, its row's `id`.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FeatureId(pub String);

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
    /// `since`, the pull requests it landed in.
    since: Option<String>,
}

/// One column of a row and its value, `None` where the row holds `NULL`.
#[derive(Clone, Copy)]
struct Cell<'row>
{
    /// The column's name.
    column: &'static str,
    /// The value.
    value: Option<&'row dyn fmt::Display>,
}

impl Feature
{
    /// The row's columns, in the dump's order, each with its value.
    ///
    /// # Specification
    /// trivial.
    fn cells(&self) -> [Cell<'_>; 13]
    {
        [
            Cell {
                column: "id",
                value: Some(&self.id),
            },
            Cell {
                column: "area",
                value: Some(&self.area),
            },
            Cell {
                column: "name",
                value: Some(&self.name),
            },
            Cell {
                column: "parent",
                value: self
                    .parent
                    .as_ref()
                    .map(|value| -> &dyn fmt::Display { value }),
            },
            Cell {
                column: "status",
                value: Some(&self.status),
            },
            Cell {
                column: "notability",
                value: Some(&self.notability),
            },
            Cell {
                column: "compared_to",
                value: self
                    .compared_to
                    .as_ref()
                    .map(|value| -> &dyn fmt::Display { value }),
            },
            Cell {
                column: "line",
                value: Some(&self.line),
            },
            Cell {
                column: "crate",
                value: self
                    .crates
                    .as_ref()
                    .map(|value| -> &dyn fmt::Display { value }),
            },
            Cell {
                column: "corpus",
                value: self
                    .corpus
                    .as_ref()
                    .map(|value| -> &dyn fmt::Display { value }),
            },
            Cell {
                column: "exemplar",
                value: self
                    .exemplar
                    .as_ref()
                    .map(|value| -> &dyn fmt::Display { value }),
            },
            Cell {
                column: "issue",
                value: self
                    .issue
                    .as_ref()
                    .map(|value| -> &dyn fmt::Display { value }),
            },
            Cell {
                column: "since",
                value: self
                    .since
                    .as_ref()
                    .map(|value| -> &dyn fmt::Display { value }),
            },
        ]
    }

    /// The row as a JSON object: each column that holds a value, by name.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: an object with `id`, `area`, `name`, `status`, `notability`
    ///   and `line`, and each other column that holds a value.
    /// - provides: the rows the Model Context Protocol server's `ledger_list`
    ///   and `ledger_show` answer.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a row with and without its optional columns is read
    ///   back from its object.
    /// - witness: `ledger::features::tests::a_row_is_its_object`
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
        Value::Object(object)
    }
}

impl fmt::Display for Feature
{
    /// Writes the row as `ledger list` prints it: `id [status] name: line`.
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
            "{} [{}] {}: {}",
            self.id, self.status, self.name, self.line
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
    /// - witness: `ledger::features::tests::the_committed_ledger_reads_every_row`
    /// - witness: `ledger::features::tests::a_quote_is_written_twice`
    /// - witness: `ledger::features::tests::a_value_of_another_shape_refuses_the_ledger_naming_its_line`
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
/// - witness: `ledger::features::tests::the_committed_ledger_reads_every_row`
/// - witness: `ledger::features::tests::a_value_of_another_shape_refuses_the_ledger_naming_its_line`
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
            since,
        ],
    ) = <[Option<String>; 13]>::try_from(values)
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
        since,
    })
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
    /// Read the ledger under the tree `root`, at `ledger/features.sql`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one feature per `INSERT INTO feature` line, in the file's
    ///   order, each column read from its value.
    /// - fails: the file cannot be read; its table's columns are not
    ///   [`COLUMNS`]; a row is not one `NULL` or quoted string per column with
    ///   every required column set and a status of the four.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LedgerFault::Unread`] naming the file, or [`LedgerFault::Features`]
    /// naming the file, the line and what is wrong with it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the committed ledger reads every row with its count
    ///   of statements, and a scratch ledger with a malformed row is refused
    ///   naming its line.
    /// - witness: `ledger::features::tests::the_committed_ledger_reads_every_row`
    /// - witness: `ledger::features::tests::a_value_of_another_shape_refuses_the_ledger_naming_its_line`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |ledger| ledger.root == root))]
    #[inline]
    pub fn read(root: &Path) -> Result<Self, LedgerFault>
    {
        let path = root.join(LEDGER);
        let text = std::fs::read_to_string(&path).map_err(|error| LedgerFault::Unread {
            path: path.clone(),
            error,
        })?;
        let refused = |line: usize, malformed: Malformed| LedgerFault::Features {
            path: path.clone(),
            line: line.saturating_add(1),
            malformed,
        };
        let mut features = Vec::new();
        let mut columns: Option<Vec<&str>> = None;
        for (number, line) in text.lines().enumerate() {
            if let Some(read) = columns.as_mut() {
                let trimmed = line.trim_start();
                if trimmed.starts_with(')') {
                    if read.as_slice() != COLUMNS.as_slice() {
                        return Err(refused(number, Malformed::Columns));
                    }
                    columns = None;
                }
                else if !trimmed.starts_with("CHECK(") {
                    read.extend(trimmed.split_whitespace().next());
                }
            }
            else if line == CREATE {
                columns = Some(Vec::with_capacity(COLUMNS.len()));
            }
            else if let Some(values) = line.strip_prefix(INSERT) {
                let feature = Values(values)
                    .read()
                    .and_then(feature)
                    .map_err(|malformed| refused(number, malformed))?;
                features.push(feature);
            }
        }
        Ok(Self {
            root: root.to_path_buf(),
            features,
        })
    }

    /// The features in `area`, when one is named, with `status`, when one is
    /// named, in the ledger's order.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: every row whose area is `area` and whose status is `status`,
    ///   each where named, and no other, in the ledger's order.
    /// - provides: `gandr ledger list [--area <area>] [--status <status>]`.
    /// - fails: an area no row is in.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LedgerFault::NoArea`] naming the area and the ledger's areas.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the committed ledger narrows to one area, to one
    ///   status and to both, and an unknown area is refused naming the areas.
    /// - witness: `ledger::features::tests::a_list_narrows_to_an_area_and_a_status`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |listed| listed.iter().all(|feature|
        area.is_none_or(|area| feature.area == area.0) && status.is_none_or(|status| feature.status == status))))]
    #[inline]
    pub fn listed(
        &self,
        area: Option<&Area>,
        status: Option<Status>,
    ) -> Result<Vec<Feature>, LedgerFault>
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
            return Err(LedgerFault::NoArea {
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
    /// - provides: `gandr ledger show <id>`.
    /// - fails: no row is `id`, or an exemplar cannot be read.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LedgerFault::NoFeature`] naming the id, or [`LedgerFault::Unread`]
    /// naming the exemplar.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a committed feature shows its exemplar's bytes and
    ///   its corpus paths, a feature whose evidence is the crate tests shows
    ///   none, and an unknown id is refused.
    /// - witness: `ledger::features::tests::a_feature_shows_its_exemplar_whole_and_its_corpus`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |shown| shown.feature.id == id.0))]
    #[inline]
    pub fn shown(
        &self,
        id: &FeatureId,
    ) -> Result<ShownFeature, LedgerFault>
    {
        let Some(feature) = self.features.iter().find(|feature| feature.id == id.0)
        else {
            return Err(LedgerFault::NoFeature { id: id.0.clone() });
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
                    .map_err(|error| LedgerFault::Unread { path: file, error })
            })
            .collect::<Result<Vec<Exemplar>, LedgerFault>>()?;
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
    /// - witness: `ledger::features::tests::a_feature_shows_its_exemplar_whole_and_its_corpus`
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
    use super::LedgerFault;
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
        /// A tree named for `name`, its ledger the frame around `rows`.
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
            std::fs::create_dir_all(root.join("ledger")).expect("the scratch tree is created");
            let mut text = String::from(
                "PRAGMA foreign_keys=OFF;\nBEGIN TRANSACTION;\nCREATE TABLE feature(\n",
            );
            for column in super::COLUMNS {
                writeln!(text, "  {column} TEXT,").expect("a string takes a line");
            }
            text.push_str("  CHECK(line <> '')\n) WITHOUT ROWID;\n");
            text.push_str(rows.0);
            text.push_str("COMMIT;\n");
            std::fs::write(root.join(super::LEDGER), text).expect("the scratch ledger is written");
            Self(root)
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
        let text = std::fs::read_to_string(root.join(super::LEDGER)).expect("the ledger reads");
        let rows = text
            .lines()
            .filter(|line| line.starts_with(super::INSERT))
            .count();
        assert_eq!(ledger.features.len(), rows, "one feature per row");
        let ids: Vec<&str> = ledger
            .features
            .iter()
            .map(|feature| feature.id.as_str())
            .collect();
        assert!(
            ids.is_sorted_by(|earlier, later| earlier < later),
            "the dump orders rows by id"
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
                matches!(refused, Err(LedgerFault::Features { line: 19, malformed: named, .. }) if named == malformed),
                "{row}: {refused:?}"
            );
        }
        let required = Scratch::new(
            Path::new("required"),
            Rows(
                "INSERT INTO feature VALUES('a','b','c',NULL,'implemented','ordinary',NULL,NULL,'d',NULL,NULL,NULL,NULL);\n",
            ),
        );
        assert!(matches!(
            FeatureLedger::read(&required.0),
            Err(LedgerFault::Features {
                malformed: Malformed::Required,
                ..
            })
        ));
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
            Err(LedgerFault::Status { spelling }) if spelling == "finished"
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
            matches!(refused, Err(LedgerFault::NoArea { ref area, ref areas }) if area == "astrology" && areas.contains("workflow")),
            "{refused:?}"
        );
    }

    #[test]
    fn a_row_is_its_object()
    {
        let scratch = Scratch::new(
            Path::new("object"),
            Rows(
                "INSERT INTO feature VALUES('a','syntax','A',NULL,'planned','ordinary',NULL,'What a is.',NULL,NULL,NULL,'#1',NULL);\n",
            ),
        );
        let ledger = FeatureLedger::read(&scratch.0).expect("the scratch ledger reads");
        let listed = ledger.listed(None, None).expect("it lists");
        assert_eq!(
            listed.iter().map(super::Feature::json).collect::<Vec<_>>(),
            vec![json!({
                "id": "a", "area": "syntax", "name": "A", "status": "planned",
                "notability": "ordinary", "line": "What a is.", "issue": "#1",
            })]
        );
        assert_eq!(
            listed.iter().map(ToString::to_string).collect::<Vec<_>>(),
            vec!["a [planned] A: What a is."]
        );
    }

    #[test]
    fn a_feature_shows_its_exemplar_whole_and_its_corpus()
    {
        let scratch = Scratch::new(
            Path::new("shown"),
            Rows(
                "INSERT INTO feature VALUES('a','syntax','A',NULL,'implemented','ordinary',NULL,'What a is.','surface-parser','tests/a.rs fixture/a.gandr::a','ledger/a.gandr',NULL,'#2');\n\
             INSERT INTO feature VALUES('b','syntax','B',NULL,'implemented','ordinary',NULL,'What b is.','surface-parser','tests/b.rs','crate-tests',NULL,'#3');\n",
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
             crate: surface-parser\ncorpus: tests/a.rs fixture/a.gandr::a\nexemplar: ledger/a.gandr\nsince: #2\n\
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
            Err(LedgerFault::NoFeature { id }) if id == "c"
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
