//! **Twin census**: for each crate of the workspace, whether the emitter
//! depends on it, read from `cargo metadata`; and the count of its generic
//! public items and the share of its public functions that an export can
//! carry, read from the JSON of rustdoc.
//!
//! A twin is a function of a crate that gandr source states. Two carriers run
//! it: an object that a build links, and a record that the runtime loads
//! through the emitter. A crate that `gandr-runtime-emitter` depends on cannot
//! take the record, because the emitter runs before the record loads. So the
//! census marks each crate that the emitter reaches. An entry under the C
//! convention carries no type parameter and no trait bound, so the census
//! counts the public items that have one. An export carries fixed-width
//! integers and addresses, so the census counts the public functions whose
//! operands and result are such values.
//!
//! - [`Workspace::read`] reads the JSON of `cargo metadata` with its resolved
//!   graph: each crate of the workspace with its directory and its library, and
//!   each crate that the emitter reaches by a normal or a build dependency,
//!   directly or through other crates. A dev dependency is no part of the
//!   emitter.
//! - [`rustdoc::read`] reads the counts of one library in the JSON that rustdoc
//!   writes for it, with what an export needs to carry each public function,
//!   and [`Workspace::set_surface`] puts them in the row of its crate.
//! - [`test_names`] reads the names of the tests in a source, and
//!   [`Workspace::set_tests`] puts them in the row of its crate.
//! - [`Workspace::candidates`] ranks the crates that can take a twin.
//! - [`Workspace::render`] writes the text of the census with the first three
//!   candidates, which the binary prints. No file of the tree holds it.
//!
//! The graph is the one that Cargo resolves for the workspace, with the
//! features of each member unified. So an optional dependency that a different
//! member turns on counts as a dependency of the emitter, as it does in a build
//! of the workspace.

pub mod rustdoc;

extern crate alloc;

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::vec::Vec;
use core::cmp::Reverse;
use core::fmt;
use core::fmt::Write as _;

use anodized::spec;
use rustdoc::Carry;
use rustdoc::Surface;

/// The package of the emitter.
pub const EMITTER: &str = "gandr-runtime-emitter";

/// Why the census could not read the metadata or the JSON of rustdoc.
///
/// # Specification
/// - provides: one variant for each refusal, each with the reason or the format
///   that it refuses.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CensusError
{
    /// The text is not the JSON of `cargo metadata` with its resolved graph.
    Metadata
    {
        /// The reason of the JSON reader.
        reason: String,
    },
    /// The workspace has no package `gandr-runtime-emitter`.
    NoEmitter,
    /// The text is not the JSON that rustdoc writes for a library.
    Rustdoc
    {
        /// The reason of the JSON reader.
        reason: String,
    },
    /// The JSON of rustdoc has a format that the census does not read.
    RustdocFormat
    {
        /// The format of the file.
        found: u32,
    },
}

impl fmt::Display for CensusError
{
    /// The refusal, with the crates that it names.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: none
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Metadata { ref reason } => {
                write!(
                    f,
                    "the metadata is not the JSON of `cargo metadata`: {reason}"
                )
            },
            Self::NoEmitter => write!(f, "the workspace has no package `{EMITTER}`"),
            Self::Rustdoc { ref reason } => {
                write!(f, "the text is not the JSON of rustdoc: {reason}")
            },
            Self::RustdocFormat { found } => write!(
                f,
                "the JSON of rustdoc has the format {found}; the census reads the format {}",
                rustdoc::FORMAT
            ),
        }
    }
}

impl core::error::Error for CensusError
{
}

/// What Cargo's metadata holds of one package.
#[derive(Debug, serde::Deserialize)]
struct Package
{
    /// The identifier of the package in the resolved graph.
    id: String,
    /// The package's name.
    name: String,
    /// The absolute path of the package's manifest.
    manifest_path: String,
    /// The targets of the package.
    targets: Vec<Target>,
}

/// One target of a package.
#[derive(Debug, serde::Deserialize)]
struct Target
{
    /// The kinds of the target: `lib`, `bin`, `proc-macro` and others.
    kind: Vec<String>,
    /// The name of the target.
    name: String,
}

impl Target
{
    /// Whether the target is a library that rustdoc documents.
    ///
    /// # Specification
    /// trivial.
    fn library(&self) -> bool
    {
        self.kind.iter().any(|kind| {
            matches!(
                kind.as_str(),
                "lib" | "rlib" | "dylib" | "cdylib" | "staticlib" | "proc-macro"
            )
        })
    }
}

/// The kind of one edge of the resolved graph: `null` for a normal
/// dependency, `"dev"` or `"build"`.
#[repr(transparent)]
#[derive(Debug, serde::Deserialize)]
struct DepKind
{
    /// The kind, absent for a normal dependency.
    kind: Option<String>,
}

/// One edge of the resolved graph.
#[derive(Debug, serde::Deserialize)]
struct NodeDep
{
    /// The identifier of the package that the edge reaches.
    pkg: String,
    /// The kinds of the edge.
    dep_kinds: Vec<DepKind>,
}

/// One node of the resolved graph.
#[derive(Debug, serde::Deserialize)]
struct Node
{
    /// The identifier of the package.
    id: String,
    /// Each edge of the package.
    deps: Vec<NodeDep>,
}

/// The resolved graph of the metadata.
#[repr(transparent)]
#[derive(Debug, serde::Deserialize)]
struct Resolve
{
    /// Each node.
    nodes: Vec<Node>,
}

/// The parts of Cargo's metadata that the census reads.
#[derive(Debug, serde::Deserialize)]
struct Metadata
{
    /// Each package of the graph.
    packages: Vec<Package>,
    /// The identifiers of the packages of the workspace.
    workspace_members: Vec<String>,
    /// The resolved graph.
    resolve: Resolve,
    /// The target directory of the workspace.
    target_directory: String,
}

/// Where a crate stands with respect to the emitter.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Standing
{
    /// The crate is the emitter.
    Emitter,
    /// The emitter depends on the crate.
    Under,
    /// The emitter does not depend on the crate.
    Apart,
}

/// One crate of the census.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Row
{
    /// Where the crate stands with respect to the emitter.
    standing: Standing,
    /// The name of the crate's library, with `_` for each `-`, if it has one.
    library: Option<String>,
    /// The counts of the library, once it is read.
    surface: Option<Surface>,
    /// The name of each test of the crate, once its sources are read.
    tests: Option<Vec<String>>,
}

/// Each crate of the workspace, by its directory below `crates/`, with its
/// standing and the counts of its library; and the target directory
/// of the workspace.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Workspace
{
    /// Each crate.
    crates: BTreeMap<String, Row>,
    /// The target directory of the workspace.
    target_directory: String,
}

impl Workspace
{
    /// The census of the workspace whose `cargo metadata --format-version 1`
    /// printed `metadata`.
    ///
    /// # Specification
    /// - requires: nothing; a text that is not the metadata is refused.
    /// - ensures: one entry for each package of the workspace, keyed by the
    ///   name of its directory. The emitter is [`Standing::Emitter`]. A package
    ///   is [`Standing::Under`] exactly when a path of normal or build edges of
    ///   the resolved graph leads from the emitter to it.
    /// - provides: the rows of the census.
    /// - fails: [`CensusError::Metadata`] when `metadata` is not the JSON of
    ///   the metadata with its resolved graph; [`CensusError::NoEmitter`] when
    ///   no package of the workspace is the emitter.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Cost
    /// - allocation: the parsed metadata, the edges of the graph and one entry
    ///   for each crate, growth within the metadata
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a graph of five crates separates a normal edge, a
    ///   build edge through a second crate, a dev edge and a crate with no
    ///   edge; a text that is not JSON and a workspace with no emitter are each
    ///   refused by name.
    /// - witness: `tests::census::a_crate_under_the_emitter_is_marked_and_a_dev_edge_is_not`
    /// - witness: `tests::census::metadata_with_no_emitter_or_no_json_is_refused_by_name`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |workspace| {
        workspace.crates.values().filter(|row| row.standing == Standing::Emitter).count() == 1
    }))]
    #[inline]
    pub fn read(metadata: &[u8]) -> Result<Self, CensusError>
    {
        let parsed: Metadata =
            serde_json::from_slice(metadata).map_err(|error| CensusError::Metadata {
                reason: error.to_string(),
            })?;
        let members: BTreeSet<&str> = parsed
            .workspace_members
            .iter()
            .map(String::as_str)
            .collect();
        let emitter = parsed
            .packages
            .iter()
            .find(|package| package.name == EMITTER && members.contains(package.id.as_str()))
            .ok_or(CensusError::NoEmitter)?;
        let edges: BTreeMap<&str, Vec<&str>> = parsed
            .resolve
            .nodes
            .iter()
            .map(|node| {
                let reached = node
                    .deps
                    .iter()
                    .filter(|dep| {
                        dep.dep_kinds
                            .iter()
                            .any(|kind| kind.kind.as_deref() != Some("dev"))
                    })
                    .map(|dep| dep.pkg.as_str())
                    .collect();
                (node.id.as_str(), reached)
            })
            .collect();
        let mut reached: BTreeSet<&str> = BTreeSet::new();
        let mut frontier = alloc::vec![emitter.id.as_str()];
        while let Some(id) = frontier.pop() {
            for &next in edges.get(id).map_or(&[][..], Vec::as_slice) {
                if reached.insert(next) {
                    frontier.push(next);
                }
            }
        }
        let crates = parsed
            .packages
            .iter()
            .filter(|package| members.contains(package.id.as_str()))
            .map(|package| {
                let standing = if package.id == emitter.id {
                    Standing::Emitter
                }
                else if reached.contains(package.id.as_str()) {
                    Standing::Under
                }
                else {
                    Standing::Apart
                };
                let library = package
                    .targets
                    .iter()
                    .find(|target| target.library())
                    .map(|target| target.name.replace('-', "_"));
                (directory(&package.manifest_path), Row {
                    standing,
                    library,
                    surface: None,
                    tests: None,
                })
            })
            .collect();
        Ok(Self {
            crates,
            target_directory: parsed.target_directory,
        })
    }

    /// The target directory of the workspace, as Cargo's metadata gives it.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub fn target_directory(&self) -> &str
    {
        &self.target_directory
    }

    /// Each crate with a library: the directory of the crate, and the name of
    /// its library with `_` for each `-`, the stem of the file that rustdoc
    /// writes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn libraries(&self) -> impl Iterator<Item = (&str, &str)>
    {
        self.crates
            .iter()
            .filter_map(|(name, row)| Some((name.as_str(), row.library.as_deref()?)))
    }

    /// Puts `surface`, the counts of the library of the crate in the directory
    /// `crate_directory`, in the row of that crate. A directory that is no
    /// crate of the workspace changes nothing.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn set_surface(
        &mut self,
        crate_directory: &str,
        surface: Surface,
    )
    {
        if let Some(row) = self.crates.get_mut(crate_directory) {
            row.surface = Some(surface);
        }
    }

    /// Puts `tests`, the names of the tests of the crate in the directory
    /// `crate_directory`, in the row of that crate. A directory that is no
    /// crate of the workspace changes nothing.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn set_tests(
        &mut self,
        crate_directory: &str,
        tests: Vec<String>,
    )
    {
        if let Some(row) = self.crates.get_mut(crate_directory) {
            row.tests = Some(tests);
        }
    }

    /// Each crate that can take a twin, best first: the crate has a test, its
    /// library has a public function, and each public function is in the
    /// export fragment or has a wrapper. The order is the fewest generic
    /// public items, then the most functions in the fragment, then the most
    /// tests, then the name.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as the summary states; a crate with no counts or no tests is
    ///   not in it.
    /// - panics: none.
    ///
    /// # Cost
    /// - allocation: one entry for each crate that can take a twin
    ///
    /// # Adequacy
    /// - hypothesis: L3 — four crates that can take a twin, in the four keys of
    ///   the order, and three that cannot: no test, a refused function and no
    ///   function.
    /// - witness: `tests::census::the_next_twins_are_ranked_by_generic_items_fragment_and_tests`
    #[spec(ensures: |ret| ret.len() <= self.crates.len())]
    #[must_use]
    #[inline]
    pub fn candidates(&self) -> Vec<&str>
    {
        let mut candidates: Vec<(&str, &Surface, usize)> = self
            .crates
            .iter()
            .filter_map(|(name, row)| {
                let surface = row.surface.as_ref()?;
                let tests = row.tests.as_ref()?.len();
                let carried = !surface.entries.is_empty()
                    && surface
                        .entries
                        .iter()
                        .all(|entry| !matches!(entry.carry, Carry::Refused(_)));
                (tests > 0 && carried).then_some((name.as_str(), surface, tests))
            })
            .collect();
        candidates.sort_by_key(|&(name, surface, tests)| {
            (
                surface.generic_items,
                Reverse(surface.exportable),
                Reverse(tests),
                name,
            )
        });
        candidates.into_iter().map(|(name, ..)| name).collect()
    }

    /// The count of crates under the emitter, and the count of crates.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the first count is the count of [`Standing::Under`] entries;
    ///   the second is the count of entries.
    /// - panics: none.
    ///
    /// # Cost
    /// - allocation: none
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::read`].
    /// - witness: `tests::census::a_crate_under_the_emitter_is_marked_and_a_dev_edge_is_not`
    #[spec(ensures: |ret| ret.0 <= ret.1 && ret.1 == self.crates.len())]
    #[must_use]
    #[inline]
    pub fn counts(&self) -> (usize, usize)
    {
        let under = self
            .crates
            .values()
            .filter(|row| row.standing == Standing::Under)
            .count();
        (under, self.crates.len())
    }

    /// The text of the census, as Markdown.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one row for each crate, in the order of its directory, with
    ///   `yes`, `no` or `the emitter`, with the count of generic public items,
    ///   and with the public functions in the export fragment as a count of the
    ///   public functions and a share; `no library` or `not read` in the two
    ///   cells of a crate with no counts. One line with the counts of
    ///   [`Self::counts`], and one line with each sum.
    /// - panics: none.
    /// - executable: none — the text is its golden's to show.
    ///
    /// # Cost
    /// - allocation: the text, growth within the crates
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the golden of a graph of five crates, one of them
    ///   with no library; the section of the next twins of a fixture workspace.
    /// - witness: `tests::census::a_crate_under_the_emitter_is_marked_and_a_dev_edge_is_not`
    /// - witness: `tests::cli::the_census_of_the_fixture_is_its_text`
    #[must_use]
    #[inline]
    pub fn render(&self) -> String
    {
        let mut text = String::from(
            "# Twin census\n\nA twin is a function of a crate that gandr source states. A crate is \
             under the emitter when `gandr-runtime-emitter` depends on it by a normal or a build \
             dependency, directly or through other crates. A twin of such a crate runs as an \
             object, and not as a record that the runtime loads.\n\nAn item is generic when it \
             has a type parameter or a trait bound. An entry under the C convention carries \
             neither, so a generic item has no twin without a wrapper. The column counts the \
             public functions, methods, types, traits and type aliases of the crate's library \
             that are generic.\n\nAn export carries a function that is not generic, whose \
             operands are fixed-width integers or addresses, and whose result is one of the \
             two. A fixed-width integer is `u8` to `u64`, `i8` to `i64`, `usize` or `isize`. An \
             address is a reference or a raw pointer to a sized type. The column gives the \
             count of such public functions and methods, of the count of all, and its \
             share.\n\n`twin-census` prints this text from `cargo metadata` and from the JSON \
             that rustdoc writes for each library.\n\n| Crate | Under the emitter | Generic \
             items | Export fragment |\n| ----- | ----------------- | ------------- | \
             --------------- |\n",
        );
        let mut sum = Surface::default();
        for (name, row) in &self.crates {
            let standing = match row.standing {
                Standing::Emitter => "the emitter",
                Standing::Under => "yes",
                Standing::Apart => "no",
            };
            let _infallible = match (row.library.as_ref(), row.surface.as_ref()) {
                (_, Some(surface)) => {
                    sum.generic_items = sum.generic_items.saturating_add(surface.generic_items);
                    sum.functions = sum.functions.saturating_add(surface.functions);
                    sum.exportable = sum.exportable.saturating_add(surface.exportable);
                    writeln!(
                        text,
                        "| `{name}` | {standing} | {} | {} |",
                        surface.generic_items,
                        share(surface.exportable, surface.functions)
                    )
                },
                (None, None) => {
                    writeln!(text, "| `{name}` | {standing} | no library | no library |")
                },
                (Some(_), None) => {
                    writeln!(text, "| `{name}` | {standing} | not read | not read |")
                },
            };
        }
        let (under, all) = self.counts();
        let _infallible = writeln!(
            text,
            "\nCrates under the emitter: {under} of {all}.\n\nGeneric public items: {}.\n\nPublic \
             functions in the export fragment: {}.",
            sum.generic_items,
            share(sum.exportable, sum.functions)
        );
        self.render_next_twins(&mut text);
        text
    }

    /// Writes the section of the next twins to `text`.
    ///
    /// # Specification
    /// trivial.
    fn render_next_twins(
        &self,
        text: &mut String,
    )
    {
        let candidates = self.candidates();
        let _infallible = writeln!(
            text,
            "\n## The next twins\n\nA crate can take a twin when it has a test, and each of its \
             public functions is in the export fragment or has a wrapper. A wrapper passes each \
             operand as its words and gives the result as its words. A result of more than one \
             word goes to an address that the caller gives. The census ranks such crates by the \
             fewest generic public items, then by the most functions in the fragment, then by \
             the most tests, and names the first {NEXT}.\n\nCrates that can take a twin: {}.",
            candidates.len()
        );
        for (place, name) in candidates.iter().take(NEXT).enumerate() {
            let Some(row) = self.crates.get(*name)
            else {
                continue;
            };
            let carrier = match row.standing {
                Standing::Emitter => "The carrier is the object, because the crate is the emitter.",
                Standing::Under => {
                    "The carrier is the object, because the emitter depends on the crate."
                },
                Standing::Apart => {
                    "The carrier is the object, or the record that the runtime loads."
                },
            };
            let _infallible = writeln!(
                text,
                "\n### {}. `{name}`\n\n{carrier}\n\n| Function | What an export needs |\n| \
                 -------- | -------------------- |",
                place.saturating_add(1)
            );
            for entry in row.surface.iter().flat_map(|surface| &surface.entries) {
                let _infallible = match entry.carry {
                    Carry::Fragment => writeln!(text, "| `{}` | nothing |", entry.name),
                    Carry::Wrapper { operands, result } => writeln!(
                        text,
                        "| `{}` | a wrapper: {} in, {} out{} |",
                        entry.name,
                        words(operands),
                        words(result),
                        if result > 1 { ", at an address" } else { "" }
                    ),
                    Carry::Refused(ref reason) => {
                        writeln!(text, "| `{}` | no wrapper: {reason} |", entry.name)
                    },
                };
            }
            let tests = row.tests.as_deref().unwrap_or_default();
            let names: Vec<String> = tests
                .iter()
                .map(|test| alloc::format!("`{test}`"))
                .collect();
            let _infallible = writeln!(text, "\nTests: {}. {}.", tests.len(), names.join(", "));
        }
    }
}

/// The count of the next twins that the census names.
const NEXT: usize = 3;

/// `count` words, as a text.
///
/// # Specification
/// trivial.
fn words(count: usize) -> String
{
    if count == 1 {
        String::from("1 word")
    }
    else {
        alloc::format!("{count} words")
    }
}

/// The name of each test in `source`, the text of a Rust file: each
/// function after an attribute `#[test]`, in the order of the text.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one name for each line `#[test]` that a line with `fn <name>`
///   follows, after other attributes and comments.
/// - panics: none.
///
/// # Cost
/// - allocation: the names
///
/// # Adequacy
/// - hypothesis: L3 — a text with a test, a test with a second attribute, a
///   function with no attribute and an attribute in a comment.
/// - witness: `tests::census::each_function_after_a_test_attribute_is_a_test`
#[must_use]
#[inline]
pub fn test_names(source: &str) -> Vec<String>
{
    let mut names = Vec::new();
    let mut pending = false;
    for line in source.lines() {
        let line = line.trim_start();
        if line == "#[test]" {
            pending = true;
            continue;
        }
        if !pending || line.starts_with("#[") || line.starts_with("//") {
            continue;
        }
        pending = false;
        let Some((_, rest)) = line.split_once("fn ")
        else {
            continue;
        };
        let name: String = rest
            .chars()
            .take_while(|&c| c.is_alphanumeric() || c == '_')
            .collect();
        if !name.is_empty() {
            names.push(name);
        }
    }
    names
}

/// `part of whole`, with the share in whole percent, rounded down, when
/// `whole` is not zero.
///
/// # Specification
/// trivial.
fn share(
    part: usize,
    whole: usize,
) -> String
{
    part.saturating_mul(100).checked_div(whole).map_or_else(
        || alloc::format!("{part} of {whole}"),
        |percent| alloc::format!("{part} of {whole} ({percent} %)"),
    )
}

/// The name of the directory of the manifest at `manifest_path`.
///
/// # Specification
/// trivial.
fn directory(manifest_path: &str) -> String
{
    let dir = manifest_path
        .strip_suffix("/Cargo.toml")
        .unwrap_or(manifest_path);
    String::from(dir.rsplit('/').next().unwrap_or(dir))
}
