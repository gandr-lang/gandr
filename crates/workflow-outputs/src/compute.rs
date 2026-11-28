//! The values of one kind of output for a tree: each read from the store, or
//! computed by the writer of the kind and written to the store.
//!
//! The writer of the records and the writer of the roles compute one value
//! from one source. The refusals of a source read the library and the other
//! sources, so one walk computes them for each source of a tree. The values
//! of a kind in [`TESTED`] come from a run of the tests of its package, which
//! give each value to the store.

use core::fmt;
use core::num::NonZeroUsize;
use core::time::Duration;
use std::io;
use std::path::Path;
use std::process::Command;
use std::time::Instant;

use anodized::spec;
use gandr_workflow_output_store::Digest;
use gandr_workflow_output_store::Kind;
use gandr_workflow_output_store::Listed;
use gandr_workflow_output_store::Store;
use gandr_workflow_output_store::given;

use crate::recovery::RecordError;
use crate::recovery::Recorder;
use crate::refusals;
use crate::refusals::RefusalsError;
use crate::roles::Roles;
use crate::roles::RolesError;
use crate::tree::Source;
use crate::tree::Tree;
use crate::tree::TreeError;
use crate::workspace;

/// The kind of the captures of the terminal face: the SVG of each state of a
/// scene, which the tests of the face give.
pub const CAPTURES: Kind = Kind("captures");

/// The kind of the layouts of the formatter at its two pages, which the tests
/// of the formatter give.
pub const FORMATTED: Kind = Kind("formatted");

/// The kind of the hovers of the headline sources, which the editor harness
/// of the language server gives.
pub const HOVERS: Kind = Kind("hovers");

/// The kind of the pages of the presentation printer, which the tests of the
/// printer give.
pub const PRINTED: Kind = Kind("printed");

/// The kind of the recovery records.
pub const RECOVERY: Kind = Kind("recovery");

/// The kind of the refusals that `gandr check` prints for a refusing source.
pub const REFUSALS: Kind = Kind("refusals");

/// The kind of the diagnostics that the terminal renderer writes, which the
/// tests of the renderer give.
pub const RENDERED: Kind = Kind("rendered");

/// The kind of the roles that the highlight gives a source.
pub const ROLES: Kind = Kind("roles");

/// The kind of the items of a corpus source that carry no comment, which the
/// comment gate of the corpus gives. It is a ratchet.
pub const UNCOMMENTED: Kind = Kind("uncommented");

/// The kind of the kinds of name that the editor answers nothing at, which
/// the coverage sweep of the language server gives. It is a ratchet.
pub const UNANSWERED: Kind = Kind("unanswered");

/// Each kind, in the order of the names.
pub const KINDS: [Kind; 10] = [
    CAPTURES,
    FORMATTED,
    HOVERS,
    PRINTED,
    RECOVERY,
    REFUSALS,
    RENDERED,
    ROLES,
    UNANSWERED,
    UNCOMMENTED,
];

/// Each kind that is a ratchet: a line of a value is a member, and the gate
/// refuses a member that the head has and the base does not have. The head
/// can drop a member.
pub const RATCHETS: [Kind; 2] = [UNANSWERED, UNCOMMENTED];

/// A kind whose values only a test can compute: the tests of its package give
/// each value to the store.
#[derive(Clone, Copy, Debug)]
pub struct Tested
{
    /// The kind.
    pub kind: Kind,
    /// The package whose tests give the values.
    pub package: &'static str,
    /// The filter of nextest that names those tests.
    pub filter: &'static str,
    /// The paths of the tree outside the packages that the tests read.
    pub inputs: &'static [&'static str],
}

/// Each kind whose values only a test can compute, in the order of the names.
pub const TESTED: [Tested; 7] = [
    Tested {
        kind: CAPTURES,
        package: "gandr-surface-tui",
        filter: "test(/^captures::/)",
        inputs: &[],
    },
    Tested {
        kind: FORMATTED,
        package: "gandr-surface-format",
        filter: "test(/^format::/) & !test(/^format::sweeps::/)",
        inputs: &[],
    },
    Tested {
        kind: HOVERS,
        package: "gandr-surface-lsp",
        filter: "test(=editor::shapes::the_headline_sources_give_their_hovers)",
        inputs: &crate::tree::REFUSAL_INPUTS,
    },
    Tested {
        kind: PRINTED,
        package: "gandr-surface-pretty",
        filter: "test(/^goldens::/)",
        inputs: &[],
    },
    Tested {
        kind: RENDERED,
        package: "gandr-surface-render-terminal",
        filter: "test(/^render::/)",
        inputs: &crate::tree::REFUSAL_INPUTS,
    },
    Tested {
        kind: UNANSWERED,
        package: "gandr-surface-lsp-core",
        filter: "test(=hover::tests::coverage::sweeps::every_corpus_name_answers_or_is_owed)",
        inputs: &["corpus"],
    },
    Tested {
        kind: UNCOMMENTED,
        package: "gandr-surface-corpus",
        filter: "test(=comments::gate::the_fixture_gives_its_uncommented_items)",
        inputs: &["corpus"],
    },
];

/// The entry of [`TESTED`] of the kind `kind`, or `None` when a writer of
/// this crate computes the kind.
///
/// # Specification
/// trivial.
#[inline]
#[must_use]
pub fn tested(kind: Kind) -> Option<&'static Tested>
{
    TESTED.iter().find(|tested| tested.kind == kind)
}

/// The package that holds the writer of each kind. Its closure in the
/// workspace builds the binary.
pub const TOOL_PACKAGE: &str = "gandr-workflow-outputs";

/// The directory below `crates/` of the package that holds each writer.
pub const TOOL_DIRECTORY: &str = "workflow-outputs";

/// The directory below `crates/` of the package of the store, whose keys
/// each kind writes.
pub const STORE_DIRECTORY: &str = "workflow-output-store";

/// The packages that compute the kind `kind`, beside the package of the
/// writers.
///
/// Their closure in the workspace is the tool of the kind, so a change of a
/// package that only another kind reads moves no key of `kind`.
///
/// # Specification
/// trivial.
#[inline]
#[must_use]
pub fn packages(kind: Kind) -> &'static [&'static str]
{
    if let Some(tested) = tested(kind) {
        return core::slice::from_ref(&tested.package);
    }
    if kind == RECOVERY {
        &[
            "gandr-surface-grammar",
            "gandr-surface-parser",
            "gandr-surface-syntax",
        ]
    }
    else if kind == ROLES {
        &[
            "gandr-surface-grammar",
            "gandr-surface-parser",
            "gandr-surface-render-remote",
            "gandr-surface-syntax",
        ]
    }
    else {
        &[
            "gandr-surface-diagnostics",
            "gandr-surface-dispatcher",
            "gandr-surface-evaluate",
            "gandr-surface-render-terminal",
        ]
    }
}

/// The directories below `crates/` of the tool of the kind `kind`, in name
/// order, each one time.
///
/// They are the closure of each package that computes the kind in the output
/// of `cargo metadata`, with the package of the writers and the package of
/// the store. The closure of a kind in [`TESTED`] holds the development
/// dependencies of its package, which build its tests.
///
/// # Specification
/// trivial.
#[inline]
#[must_use]
pub fn tool_packages(
    metadata: &serde_json::Value,
    kind: Kind,
) -> Vec<String>
{
    let closure: fn(&serde_json::Value, &str) -> Vec<String> = if tested(kind).is_some() {
        workspace::test_closure
    }
    else {
        workspace::closure
    };
    let mut directories: Vec<String> = packages(kind)
        .iter()
        .flat_map(|package| closure(metadata, package))
        .chain([TOOL_DIRECTORY.to_owned(), STORE_DIRECTORY.to_owned()])
        .collect();
    directories.sort();
    directories.dedup();
    directories
}

/// The writer of the values of one kind, under one grammar.
#[derive(Debug)]
pub enum Writer<'grammar>
{
    /// The writer of the recovery records.
    Recovery(Recorder<'grammar>),
    /// The writer of the roles.
    Roles(Roles<'grammar>),
}

impl Writer<'_>
{
    /// The kind that the writer computes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn kind(&self) -> Kind
    {
        match *self {
            Self::Recovery(_) => RECOVERY,
            Self::Roles(_) => ROLES,
        }
    }

    /// The value of the source `name`, whose text is `text`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`ComputeError::Record`] or [`ComputeError::Roles`] when the source
    /// gives no value.
    #[inline]
    pub fn value(
        &self,
        name: &str,
        text: &str,
    ) -> Result<String, ComputeError>
    {
        match *self {
            Self::Recovery(ref recorder) => {
                recorder.record(text).map_err(|error| ComputeError::Record {
                    name: name.to_owned(),
                    error,
                })
            },
            Self::Roles(ref roles) => roles.value(text).map_err(|error| ComputeError::Roles {
                name: name.to_owned(),
                error,
            }),
        }
    }
}

/// Why the values of a tree could not be given.
///
/// # Specification
/// - provides: one variant for each part that refuses.
#[derive(Debug)]
pub enum ComputeError
{
    /// The tree could not be read.
    Tree(TreeError),
    /// A source gives no record.
    Record
    {
        /// The name of the source.
        name: String,
        /// The refusal of the writer.
        error: RecordError,
    },
    /// A source gives no roles.
    Roles
    {
        /// The name of the source.
        name: String,
        /// The refusal of the writer.
        error: RolesError,
    },
    /// The walk of the refusing sources could not read a path.
    Refusals(RefusalsError),
    /// The store could not be read or written.
    Store(io::Error),
    /// `cargo metadata` gave no packages of the workspace.
    Metadata(String),
    /// The run of the tests of a kind failed.
    Tests
    {
        /// The name of the kind.
        kind: &'static str,
        /// The last line that the run wrote.
        line: String,
    },
}

impl fmt::Display for ComputeError
{
    /// Writes one line that names the part and its refusal.
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
            Self::Tree(ref error) => write!(f, "{error}"),
            Self::Record {
                ref name,
                ref error,
            } => write!(f, "{name}: {error}"),
            Self::Roles {
                ref name,
                ref error,
            } => write!(f, "{name}: {error}"),
            Self::Refusals(ref error) => write!(f, "{error}"),
            Self::Store(ref error) => write!(f, "the store: {error}"),
            Self::Metadata(ref error) => write!(f, "{error}"),
            Self::Tests { kind, ref line } => {
                write!(f, "the tests of the kind {kind} failed: {line}")
            },
        }
    }
}

/// A refusal is an error value, so a caller can return it.
impl core::error::Error for ComputeError
{
}

/// One part of a run: its name, how many times it ran and its time.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Part
{
    /// The name of the part.
    pub name: &'static str,
    /// How many items the part did.
    pub count: usize,
    /// The time of the part.
    pub time: Duration,
}

/// The values of a tree: each source with its value, in name order.
pub type Valued = Vec<(Source, Vec<u8>)>;

/// The values of a tree, with the cost of each part of the run.
#[derive(Debug)]
pub struct Values
{
    /// Each source of the tree with its value, in name order.
    pub values: Vec<(Source, Vec<u8>)>,
    /// How many values the run computed; the store held the rest.
    pub computed: usize,
    /// The parts of the run, in their order.
    pub parts: Vec<Part>,
}

/// The values of a tree that the store holds, before a run computes the
/// rest.
#[derive(Debug)]
pub struct Held
{
    /// Each source of the tree, in name order.
    pub sources: Vec<Source>,
    /// The key of each source.
    pub keys: Vec<Digest>,
    /// The value of each source that the store holds.
    pub values: Vec<Option<Vec<u8>>>,
    /// The parts of the lookup, in their order.
    pub parts: Vec<Part>,
}

impl Held
{
    /// How many sources have no value in the store.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn missing(&self) -> usize
    {
        self.values.iter().filter(|value| value.is_none()).count()
    }
}

/// The values of the kind `kind` of `tree` under the tool `tool` that `store`
/// holds.
///
/// # Specification
/// - ensures: one key and one place for a value for each source.
///
/// # Errors
/// [`ComputeError`] when the tree or the store refuses.
///
/// # Adequacy
/// - hypothesis: L3 — a second run holds each value that a first run computed,
///   and another tool or another kind holds none.
/// - witness: `compute::tests::the_values_of_a_tree_are_its_records`
/// - witness: `compute::tests::each_kind_has_its_own_values`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |held| held.keys.len() == held.sources.len() && held.values.len() == held.sources.len()))]
#[inline]
pub fn held(
    store: &Store,
    tree: &Tree,
    tool: &Digest,
    kind: Kind,
) -> Result<Held, ComputeError>
{
    let mut parts = Vec::new();
    let started = Instant::now();
    let sources = tree.sources().map_err(ComputeError::Tree)?;
    parts.push(Part {
        name: "list the sources",
        count: sources.len(),
        time: started.elapsed(),
    });
    let started = Instant::now();
    let keys: Vec<Digest> = sources
        .iter()
        .map(|source| Digest::of_parts([tool.0.as_slice(), source.object.as_bytes()]))
        .collect();
    let mut values: Vec<Option<Vec<u8>>> = Vec::with_capacity(sources.len());
    for key in &keys {
        values.push(store.get(kind, key).map_err(ComputeError::Store)?);
    }
    parts.push(Part {
        name: "read the store",
        count: keys.len(),
        time: started.elapsed(),
    });
    Ok(Held {
        sources,
        keys,
        values,
        parts,
    })
}

/// The values of `tree` under the tool `tool`, of the kind of `writer`.
///
/// Each source's value is read from `store`, or computed by `writer` and
/// written to `store`. The run reads the contents of the sources that it
/// computes in one batch, and computes them on each available core.
///
/// # Specification
/// - ensures: one value for each source of the tree, in name order.
///
/// # Errors
/// [`ComputeError`] when the tree, a source or the store refuses.
///
/// # Adequacy
/// - hypothesis: L3 — the values of a tree equal the records of its sources, a
///   second run computes none, and the values of a second kind are its own.
/// - witness: `compute::tests::the_values_of_a_tree_are_its_records`
/// - witness: `compute::tests::each_kind_has_its_own_values`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |values| values.values.is_sorted_by(|left, right| left.0 <= right.0)))]
#[inline]
pub fn values(
    store: &Store,
    tree: &Tree,
    tool: &Digest,
    writer: &Writer<'_>,
) -> Result<Values, ComputeError>
{
    let kind = writer.kind();
    let Held {
        sources,
        keys,
        values: mut held,
        mut parts,
    } = self::held(store, tree, tool, kind)?;
    let missing: Vec<usize> = held
        .iter()
        .enumerate()
        .filter_map(|(index, value)| value.is_none().then_some(index))
        .collect();
    let started = Instant::now();
    let objects: Vec<&str> = missing
        .iter()
        .filter_map(|&index| sources.get(index).map(|source| source.object.as_str()))
        .collect();
    let contents = if objects.is_empty() {
        Vec::new()
    }
    else {
        tree.contents(&objects).map_err(ComputeError::Tree)?
    };
    parts.push(Part {
        name: "read the sources",
        count: contents.len(),
        time: started.elapsed(),
    });
    let started = Instant::now();
    let records = values_together(writer, &sources, &missing, &contents)?;
    parts.push(Part {
        name: "compute the values",
        count: records.len(),
        time: started.elapsed(),
    });
    let started = Instant::now();
    for (&index, record) in missing.iter().zip(records) {
        if let Some(key) = keys.get(index) {
            store
                .put(kind, key, record.as_bytes())
                .map_err(ComputeError::Store)?;
        }
        if let Some(slot) = held.get_mut(index) {
            *slot = Some(record.into_bytes());
        }
    }
    let entries: Vec<Listed> = sources
        .iter()
        .zip(&keys)
        .map(|(source, key)| Listed {
            key: *key,
            object: source.object.clone(),
            name: source.name.clone(),
        })
        .collect();
    store
        .list(kind, tree.id(), &entries)
        .map_err(ComputeError::Store)?;
    parts.push(Part {
        name: "write the store",
        count: missing.len(),
        time: started.elapsed(),
    });
    let values = sources
        .into_iter()
        .zip(held)
        .map(|(source, value)| (source, value.unwrap_or_default()))
        .collect();
    Ok(Values {
        values,
        computed: missing.len(),
        parts,
    })
}

/// The values of the sources at `missing`, whose contents are `contents`,
/// computed by `writer` on each available core, in the order of `missing`.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`ComputeError`] when a source gives no value.
fn values_together(
    writer: &Writer<'_>,
    sources: &[Source],
    missing: &[usize],
    contents: &[Vec<u8>],
) -> Result<Vec<String>, ComputeError>
{
    let cores = std::thread::available_parallelism().map_or(1, NonZeroUsize::get);
    let share = missing.len().div_ceil(cores).max(1);
    let jobs: Vec<(&[usize], &[Vec<u8>])> =
        missing.chunks(share).zip(contents.chunks(share)).collect();
    let answers: Vec<Result<Vec<String>, ComputeError>> = std::thread::scope(|scope| {
        #[expect(
            clippy::needless_collect,
            reason = "each thread starts before the first join, so the shares compute together"
        )]
        let handles: Vec<_> = jobs
            .iter()
            .map(|&(indices, texts)| {
                scope.spawn(move || {
                    indices
                        .iter()
                        .zip(texts)
                        .map(|(&index, text)| {
                            let name = sources.get(index).map_or("", |source| source.name.as_str());
                            let text = String::from_utf8_lossy(text);
                            writer.value(name, &text)
                        })
                        .collect()
                })
            })
            .collect();
        handles
            .into_iter()
            .map(|handle| {
                handle.join().unwrap_or_else(|_| {
                    Err(ComputeError::Store(io::Error::other(
                        "a thread of the values stopped",
                    )))
                })
            })
            .collect()
    });
    let mut records = Vec::with_capacity(missing.len());
    for answer in answers {
        records.extend(answer?);
    }
    Ok(records)
}

/// The values of the kind `kind` that `store` lists for `tree`, in name
/// order.
///
/// Gives `None` when the store has no list of the tree or lacks a value of
/// the list. The list is the work of the tool of the tree, so the reader
/// needs no key of that tool.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`ComputeError::Store`] when the store refuses.
///
/// # Adequacy
/// - hypothesis: L3 — a tree that a run computed is listed with each value,
///   under no tool; a tree that no run computed is not listed, and no list of
///   one kind serves another kind.
/// - witness: `compute::tests::a_computed_tree_is_listed_under_no_tool`
#[inline]
pub fn listed(
    store: &Store,
    tree: &Tree,
    kind: Kind,
) -> Result<Option<Valued>, ComputeError>
{
    Ok(read_list(store, kind, tree.id())?.map(|(_, values)| values))
}

/// The entries of a list, and the value of each entry.
type ListedValues = (Vec<Listed>, Valued);

/// The list of `kind` that `store` holds at `name`, with the value of each
/// entry, or `None` when the store has no such list or lacks a value of it.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`ComputeError::Store`] when the store refuses.
fn read_list(
    store: &Store,
    kind: Kind,
    name: &str,
) -> Result<Option<ListedValues>, ComputeError>
{
    let Some(entries) = store.listed(kind, name).map_err(ComputeError::Store)?
    else {
        return Ok(None);
    };
    let mut values = Vec::with_capacity(entries.len());
    for entry in &entries {
        let Some(value) = store.get(kind, &entry.key).map_err(ComputeError::Store)?
        else {
            return Ok(None);
        };
        values.push((
            Source {
                name: entry.name.clone(),
                object: entry.object.clone(),
            },
            value,
        ));
    }
    Ok(Some((entries, values)))
}

/// The refusals of each refusing source of `tree` under the tool `tool`.
///
/// One walk computes them all, because a refusal reads the library and the
/// other sources. The store holds each text at the digest of its bytes, so
/// two trees share a text that did not change. It holds the list of the
/// texts at the digest of the tool with the inputs of the walk, so a tree
/// with those inputs needs no walk. `checkout` is a directory that holds the
/// files of `tree`. With no such directory and no list, the run gives
/// `None`.
///
/// # Specification
/// - ensures: the values are in name order.
///
/// # Errors
/// [`ComputeError`] when the tree, the walk or the store refuses.
///
/// # Adequacy
/// - hypothesis: L3 — a run with no directory and no list gives nothing; a run
///   with the directory walks one time; a second tree with the same corpus
///   needs no directory and no walk.
/// - witness: `compute::tests::one_walk_serves_each_tree_with_its_inputs`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |values| values.as_ref().is_none_or(|values| values.values.is_sorted_by(|left, right| left.0 <= right.0))))]
#[inline]
pub fn refusals(
    store: &Store,
    tree: &Tree,
    tool: &Digest,
    checkout: Option<&Path>,
) -> Result<Option<Values>, ComputeError>
{
    let mut parts = Vec::new();
    let started = Instant::now();
    let sources = tree.refusing().map_err(ComputeError::Tree)?;
    let inputs = tree.refusal_inputs().map_err(ComputeError::Tree)?;
    let walk = Digest::of_parts([b"walk".as_slice(), tool.0.as_slice(), inputs.as_bytes()]).hex();
    parts.push(Part {
        name: "list the sources",
        count: sources.len(),
        time: started.elapsed(),
    });
    let started = Instant::now();
    let held = read_list(store, REFUSALS, &walk)?;
    parts.push(Part {
        name: "read the list",
        count: held.as_ref().map_or(0, |held| held.1.len()),
        time: started.elapsed(),
    });
    if let Some((entries, values)) = held {
        store
            .list(REFUSALS, tree.id(), &entries)
            .map_err(ComputeError::Store)?;
        return Ok(Some(Values {
            values,
            computed: 0,
            parts,
        }));
    }
    let Some(checkout) = checkout
    else {
        return Ok(None);
    };
    let started = Instant::now();
    let roots = refusals::REFUSING
        .iter()
        .map(|directory| checkout.join("corpus").join(directory))
        .filter(|root| root.exists())
        .collect();
    let rendered = refusals::rendered(checkout, roots).map_err(ComputeError::Refusals)?;
    parts.push(Part {
        name: "walk the sources",
        count: rendered.len(),
        time: started.elapsed(),
    });
    let started = Instant::now();
    let mut entries = Vec::with_capacity(sources.len());
    let mut values = Vec::with_capacity(sources.len());
    for source in sources {
        let text = source
            .name
            .strip_prefix("fixture/")
            .and_then(|below| rendered.get(Path::new(below)))
            .map_or("", String::as_str);
        let key = Digest::of_parts([b"text".as_slice(), text.as_bytes()]);
        store
            .put(REFUSALS, &key, text.as_bytes())
            .map_err(ComputeError::Store)?;
        entries.push(Listed {
            key,
            object: source.object.clone(),
            name: source.name.clone(),
        });
        values.push((source, text.as_bytes().to_vec()));
    }
    for name in [walk.as_str(), tree.id()] {
        store
            .list(REFUSALS, name, &entries)
            .map_err(ComputeError::Store)?;
    }
    parts.push(Part {
        name: "write the store",
        count: values.len(),
        time: started.elapsed(),
    });
    Ok(Some(Values {
        computed: values.len(),
        values,
        parts,
    }))
}

/// The refusals of the work tree of the checkout `root`, under the tool of
/// that work tree.
///
/// The values come from the list that `store` holds for the inputs of the
/// walk, or from one walk of the checkout, which fills `store`. A run on a
/// tree whose corpus, library and tool an earlier run read thus starts no
/// walk. An earlier run of `outputs` on such a tree is such a run.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`ComputeError`] when cargo, the tree, the walk or the store refuses.
#[inline]
pub fn work_tree_refusals(
    store: &Store,
    root: &Path,
) -> Result<Values, ComputeError>
{
    let (tree, tool) = work_tree_tool(root, REFUSALS)?;
    refusals(store, &tree, &tool, Some(root))?.ok_or_else(|| {
        ComputeError::Refusals(RefusalsError {
            faults: vec![root.to_path_buf()],
        })
    })
}

/// The values of the kind of `tested` of the work tree of the checkout
/// `root`, under the tool of that work tree.
///
/// The values come from the list that `store` holds for the run of the tests
/// with the inputs of the work tree, or from one run of the tests in the
/// checkout, which fills `store`. An earlier run of `outputs` on a tree with
/// the same tool and inputs thus spares the run of the tests.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`ComputeError`] when cargo, the tree, the tests or the store refuses.
#[inline]
pub fn work_tree_tested(
    store: &Store,
    root: &Path,
    tested: &Tested,
) -> Result<Values, ComputeError>
{
    let (tree, tool) = work_tree_tool(root, tested.kind)?;
    tested_values(store, &tree, &tool, tested, Some(root))?.ok_or_else(|| ComputeError::Tests {
        kind: tested.kind.0,
        line: String::from("the checkout gives no values"),
    })
}

/// The work tree of the checkout `root`, and the digest of the tool of the
/// kind `kind` in it.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`ComputeError`] when cargo or the tree refuses.
fn work_tree_tool(
    root: &Path,
    kind: Kind,
) -> Result<(Tree, Digest), ComputeError>
{
    let metadata = workspace::metadata(root).map_err(ComputeError::Metadata)?;
    let packages = tool_packages(&metadata, kind);
    let packages: Vec<&str> = packages.iter().map(String::as_str).collect();
    let manifests = workspace::closure(&metadata, TOOL_PACKAGE);
    let manifests: Vec<&str> = manifests.iter().map(String::as_str).collect();
    let tree = Tree::of_work_tree(root, &root.join("target")).map_err(ComputeError::Tree)?;
    let tool = tree
        .tool(&packages, &manifests)
        .map_err(ComputeError::Tree)?;
    Ok((tree, tool))
}

/// The values of the kind of `tested` of `tree` under the tool `tool`.
///
/// The tests of the kind compute the values, so the store holds the list of
/// each run at the digest of the tool with the inputs of the tests. A tree
/// with those inputs reads that list and runs no test. Else, with the
/// directory `checkout` of the tree, the run starts the tests of the kind
/// there, with `GANDR_OUTPUT_STORE` and `GANDR_OUTPUT_RUN` set, and lists
/// the values that they give. With no such directory and no list, it gives
/// `None`.
///
/// # Specification
/// - ensures: the values are in name order.
///
/// # Errors
/// [`ComputeError`] when the tree, the run of the tests or the store
/// refuses.
#[spec(ensures: |ret| ret.as_ref().map_or(true, |values| values.as_ref().is_none_or(|values| values.values.is_sorted_by(|left, right| left.0 <= right.0))))]
#[inline]
pub fn tested_values(
    store: &Store,
    tree: &Tree,
    tool: &Digest,
    tested: &Tested,
    checkout: Option<&Path>,
) -> Result<Option<Values>, ComputeError>
{
    let kind = tested.kind;
    let mut parts = Vec::new();
    let started = Instant::now();
    let inputs = tree.inputs(tested.inputs).map_err(ComputeError::Tree)?;
    let run = Digest::of_parts([b"run".as_slice(), tool.0.as_slice(), inputs.as_bytes()]).hex();
    let held = read_list(store, kind, &run)?;
    parts.push(Part {
        name: "read the list",
        count: held.as_ref().map_or(0, |held| held.1.len()),
        time: started.elapsed(),
    });
    if let Some((entries, values)) = held {
        store
            .list(kind, tree.id(), &entries)
            .map_err(ComputeError::Store)?;
        return Ok(Some(Values {
            values,
            computed: 0,
            parts,
        }));
    }
    let Some(checkout) = checkout
    else {
        return Ok(None);
    };
    let started = Instant::now();
    let directory =
        checkout
            .join("target/outputs-run")
            .join(format!("{}.{}", kind.0, std::process::id()));
    match std::fs::remove_dir_all(&directory) {
        Ok(()) => {},
        Err(error) if error.kind() == io::ErrorKind::NotFound => {},
        Err(error) => return Err(ComputeError::Store(error)),
    }
    let root = std::path::absolute(store.root()).map_err(ComputeError::Store)?;
    let ran = Command::new(std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into()))
        .args(["nextest", "run", "--locked", "--no-fail-fast"])
        .args(["--package", tested.package, "-E", tested.filter])
        .env(given::STORE, &root)
        .env(given::RUN, &directory)
        .current_dir(checkout)
        .output()
        .map_err(|error| ComputeError::Tests {
            kind: kind.0,
            line: error.to_string(),
        })?;
    if !ran.status.success() {
        let line = String::from_utf8_lossy(&ran.stderr)
            .lines()
            .rev()
            .find(|line| !line.trim().is_empty())
            .unwrap_or_default()
            .to_owned();
        return Err(ComputeError::Tests { kind: kind.0, line });
    }
    let entries = given::entries(&directory, kind).map_err(ComputeError::Store)?;
    let mut values = Vec::with_capacity(entries.len());
    for entry in &entries {
        let value = store
            .get(kind, &entry.key)
            .map_err(ComputeError::Store)?
            .ok_or_else(|| {
                ComputeError::Store(io::Error::new(
                    io::ErrorKind::NotFound,
                    format!(
                        "the run gave {} and the store holds no value of it",
                        entry.name
                    ),
                ))
            })?;
        values.push((
            Source {
                name: entry.name.clone(),
                object: entry.object.clone(),
            },
            value,
        ));
    }
    parts.push(Part {
        name: "run the tests",
        count: values.len(),
        time: started.elapsed(),
    });
    for name in [run.as_str(), tree.id()] {
        store
            .list(kind, name, &entries)
            .map_err(ComputeError::Store)?;
    }
    let _removed = std::fs::remove_dir_all(&directory);
    Ok(Some(Values {
        computed: values.len(),
        values,
        parts,
    }))
}

#[cfg(test)]
mod tests
{
    use gandr_surface_grammar::built_in;
    use gandr_workflow_output_store::Digest;
    use gandr_workflow_output_store::Store;

    use super::RECOVERY;
    use super::REFUSALS;
    use super::ROLES;
    use super::Writer;
    use super::held;
    use super::listed;
    use super::refusals;
    use super::values;
    use crate::recovery::Recorder;
    use crate::roles::Roles;
    use crate::tree::Tree;
    use crate::tree::scratch_repository;

    /// A source that parses whole.
    const WHOLE: &str = include_str!("compute/fixtures/a-definition-of-one.gandr");

    /// A source that stops in an open parenthesis.
    const CUT: &str =
        include_str!("compute/unformatted/a-definition-that-stops-in-a-parenthesis.gandr");

    /// The values of a tree are the records of its sources; a second run
    /// reads each from the store, and another tool computes each again.
    #[test]
    fn the_values_of_a_tree_are_its_records()
    {
        let root = scratch_repository("compute", &[
            ("crates/surface-corpus/strict/values.gandr", WHOLE),
            ("corpus/model/circle.gandr", CUT),
        ]);
        let store = Store::at(root.join("store"));
        let tree = Tree::of_revision(&root, "HEAD").expect("the commit has a tree");
        let pbg = built_in().expect("the built-in grammar builds");
        let recorder = Recorder::new(&pbg).expect("each mold has a rule");
        let records: Vec<Vec<u8>> = [CUT, WHOLE]
            .map(|text| {
                recorder
                    .record(text)
                    .expect("the source gives a tree")
                    .into_bytes()
            })
            .to_vec();
        let writer = Writer::Recovery(recorder);
        let tool = Digest::of_parts([b"tool".as_slice()]);
        let first = values(&store, &tree, &tool, &writer).expect("the values are given");
        assert_eq!(first.computed, 2);
        let given: Vec<Vec<u8>> = first.values.into_iter().map(|(_, value)| value).collect();
        assert_eq!(given, records);
        let second = values(&store, &tree, &tool, &writer).expect("the values are given");
        assert_eq!(second.computed, 0);
        let other = Digest::of_parts([b"other tool".as_slice()]);
        assert_eq!(
            held(&store, &tree, &tool, RECOVERY)
                .expect("the store reads")
                .missing(),
            0
        );
        assert_eq!(
            held(&store, &tree, &other, RECOVERY)
                .expect("the store reads")
                .missing(),
            2
        );
        assert_eq!(
            values(&store, &tree, &other, &writer)
                .expect("the values are given")
                .computed,
            2
        );
        std::fs::remove_dir_all(root).expect("the repository is removed");
    }

    /// The roles of a tree are not its records: the store holds each kind
    /// under its own name, and a run of one kind gives no value of the
    /// other.
    #[test]
    fn each_kind_has_its_own_values()
    {
        let root = scratch_repository("kinds", &[(
            "crates/surface-corpus/strict/values.gandr",
            WHOLE,
        )]);
        let store = Store::at(root.join("store"));
        let tree = Tree::of_revision(&root, "HEAD").expect("the commit has a tree");
        let pbg = built_in().expect("the built-in grammar builds");
        let tool = Digest::of_parts([b"tool".as_slice()]);
        let records = Writer::Recovery(Recorder::new(&pbg).expect("each mold has a rule"));
        let first = values(&store, &tree, &tool, &records).expect("the records are given");
        assert_eq!(first.computed, 1);
        assert_eq!(
            held(&store, &tree, &tool, ROLES)
                .expect("the store reads")
                .missing(),
            1,
            "a run of the records writes no roles"
        );
        let roles = Roles::new(&pbg).expect("the grammar gives a role table");
        let written = roles.value(WHOLE).expect("the source gives roles");
        let roles = Writer::Roles(roles);
        let second = values(&store, &tree, &tool, &roles).expect("the roles are given");
        assert_eq!(second.computed, 1);
        let given: Vec<Vec<u8>> = second.values.into_iter().map(|(_, value)| value).collect();
        assert_eq!(given, [written.into_bytes()]);
        assert_eq!(
            held(&store, &tree, &tool, RECOVERY)
                .expect("the store reads")
                .missing(),
            0,
            "the roles leave each record in its place"
        );
        std::fs::remove_dir_all(root).expect("the repository is removed");
    }

    /// A tree that a run computed is listed with each value, and the reader
    /// names no tool. A tree that no run computed is not listed, and the
    /// list of the records is no list of the roles.
    #[test]
    fn a_computed_tree_is_listed_under_no_tool()
    {
        let root = scratch_repository("listed", &[
            ("crates/surface-corpus/strict/values.gandr", WHOLE),
            ("corpus/model/circle.gandr", CUT),
        ]);
        let store = Store::at(root.join("store"));
        let tree = Tree::of_revision(&root, "HEAD").expect("the commit has a tree");
        assert_eq!(
            listed(&store, &tree, RECOVERY)
                .expect("the store reads")
                .map(|values| values.len()),
            None,
            "no run computed the tree"
        );
        let pbg = built_in().expect("the built-in grammar builds");
        let writer = Writer::Recovery(Recorder::new(&pbg).expect("each mold has a rule"));
        let tool = Digest::of_parts([b"a tool that the reader does not know".as_slice()]);
        let computed = values(&store, &tree, &tool, &writer).expect("the values are given");
        let read = listed(&store, &tree, RECOVERY)
            .expect("the store reads")
            .expect("the tree is listed");
        assert_eq!(read, computed.values);
        assert_eq!(
            listed(&store, &tree, ROLES)
                .expect("the store reads")
                .map(|values| values.len()),
            None,
            "the list of the records is no list of the roles"
        );
        std::fs::remove_dir_all(root).expect("the repository is removed");
    }

    /// A run with no directory of the tree and no list gives nothing. A run
    /// with the directory walks one time and lists the tree. A second tree
    /// with the same corpus and another file needs no directory and no walk.
    #[test]
    fn one_walk_serves_each_tree_with_its_inputs()
    {
        let root = scratch_repository("refusals", &[(
            "corpus/pathological/unformatted/open.gandr",
            CUT,
        )]);
        let store = Store::at(root.join(".git/store"));
        let tree = Tree::of_revision(&root, "HEAD").expect("the commit has a tree");
        let tool = Digest::of_parts([b"tool".as_slice()]);
        assert!(
            refusals(&store, &tree, &tool, None)
                .expect("the store reads")
                .is_none(),
            "no directory and no list give nothing"
        );
        let walked = refusals(&store, &tree, &tool, Some(&root))
            .expect("the walk reads the source")
            .expect("the directory gives the values");
        assert_eq!(walked.computed, 1);
        assert_eq!(
            listed(&store, &tree, REFUSALS).expect("the store reads"),
            Some(walked.values.clone())
        );
        std::fs::write(root.join("notes.md"), "notes\n").expect("the file is written");
        let other =
            Tree::of_work_tree(&root, &root.join(".git")).expect("the work tree has a tree");
        assert_ne!(other.id(), tree.id());
        let read = refusals(&store, &other, &tool, None)
            .expect("the store reads")
            .expect("the list of the inputs gives the values");
        assert_eq!(read.computed, 0);
        assert_eq!(read.values, walked.values);
        std::fs::remove_dir_all(root).expect("the repository is removed");
    }
}
