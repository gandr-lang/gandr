//! The values of one kind of output for a tree: each read from the store, or
//! computed by the writer of the kind and written to the store.

use core::fmt;
use core::num::NonZeroUsize;
use core::time::Duration;
use std::io;
use std::time::Instant;

use anodized::spec;

use crate::recovery::RecordError;
use crate::recovery::Recorder;
use crate::roles::Roles;
use crate::roles::RolesError;
use crate::store::Digest;
use crate::store::Kind;
use crate::store::Listed;
use crate::store::Store;
use crate::tree::Source;
use crate::tree::Tree;
use crate::tree::TreeError;

/// The kind of the recovery records.
pub const RECOVERY: Kind = Kind("recovery");

/// The kind of the roles that the highlight gives a source.
pub const ROLES: Kind = Kind("roles");

/// Each kind, in the order of the names.
pub const KINDS: [Kind; 2] = [RECOVERY, ROLES];

/// The package that computes each kind. Its closure in the workspace is the
/// tool of each kind.
pub const TOOL_PACKAGE: &str = "gandr-workflow-outputs";

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
    /// The store could not be read or written.
    Store(io::Error),
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
            Self::Store(ref error) => write!(f, "the store: {error}"),
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
    let Some(entries) = store.listed(kind, tree.id()).map_err(ComputeError::Store)?
    else {
        return Ok(None);
    };
    let mut values = Vec::with_capacity(entries.len());
    for entry in entries {
        let Some(value) = store.get(kind, &entry.key).map_err(ComputeError::Store)?
        else {
            return Ok(None);
        };
        values.push((
            Source {
                name: entry.name,
                object: entry.object,
            },
            value,
        ));
    }
    Ok(Some(values))
}

#[cfg(test)]
mod tests
{
    use gandr_surface_grammar::built_in;

    use super::RECOVERY;
    use super::ROLES;
    use super::Writer;
    use super::held;
    use super::listed;
    use super::values;
    use crate::recovery::Recorder;
    use crate::roles::Roles;
    use crate::store::Digest;
    use crate::store::Store;
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
}
