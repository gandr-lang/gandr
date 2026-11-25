//! The values of the recovery records of a tree: each read from the store,
//! or computed and written to it.

use core::fmt;
use core::num::NonZeroUsize;
use core::time::Duration;
use std::io;
use std::time::Instant;

use anodized::spec;

use crate::recovery::RecordError;
use crate::recovery::Recorder;
use crate::store::Digest;
use crate::store::Kind;
use crate::store::Store;
use crate::tree::Source;
use crate::tree::Tree;
use crate::tree::TreeError;

/// The kind of the recovery records.
pub const RECOVERY: Kind = Kind("recovery");

/// The package that computes the recovery records. Its closure in the
/// workspace is the tool of the kind.
pub const RECOVERY_PACKAGE: &str = "gandr-workflow-outputs";

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

/// The recovery records of `tree` under the tool `tool`.
///
/// Each source's value is read from `store`, or computed by `recorder` and
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
/// - hypothesis: L3 — the values of a tree equal the records of its sources,
///   and a second run computes none.
/// - witness: `compute::tests::the_values_of_a_tree_are_its_records`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |values| values.values.is_sorted_by(|left, right| left.0 <= right.0)))]
#[inline]
pub fn recovery(
    store: &Store,
    tree: &Tree,
    tool: &Digest,
    recorder: &Recorder<'_>,
) -> Result<Values, ComputeError>
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
    let mut held: Vec<Option<Vec<u8>>> = Vec::with_capacity(sources.len());
    for key in &keys {
        held.push(store.get(RECOVERY, key).map_err(ComputeError::Store)?);
    }
    parts.push(Part {
        name: "read the store",
        count: keys.len(),
        time: started.elapsed(),
    });
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
    let records = records_together(recorder, &sources, &missing, &contents)?;
    parts.push(Part {
        name: "compute the records",
        count: records.len(),
        time: started.elapsed(),
    });
    let started = Instant::now();
    for (&index, record) in missing.iter().zip(records) {
        if let Some(key) = keys.get(index) {
            store
                .put(RECOVERY, key, record.as_bytes())
                .map_err(ComputeError::Store)?;
        }
        if let Some(slot) = held.get_mut(index) {
            *slot = Some(record.into_bytes());
        }
    }
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

/// The records of the sources at `missing`, whose contents are `contents`,
/// computed on each available core, in the order of `missing`.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`ComputeError::Record`] when a source gives no record.
fn records_together(
    recorder: &Recorder<'_>,
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
                            let name = sources
                                .get(index)
                                .map_or_else(String::new, |source| source.name.clone());
                            let text = String::from_utf8_lossy(text);
                            recorder
                                .record(&text)
                                .map_err(|error| ComputeError::Record { name, error })
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
                        "a thread of the records stopped",
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

#[cfg(test)]
mod tests
{
    use gandr_surface_grammar::built_in;

    use super::recovery;
    use crate::recovery::Recorder;
    use crate::store::Digest;
    use crate::store::Store;
    use crate::tree::Tree;
    use crate::tree::scratch_repository;

    /// The values of a tree are the records of its sources; a second run
    /// reads each from the store, and another tool computes each again.
    #[test]
    fn the_values_of_a_tree_are_its_records()
    {
        let root = scratch_repository("compute", &[
            ("crates/surface-corpus/strict/values.gandr", "def one = 1\n"),
            ("corpus/model/circle.gandr", "def two = (\n"),
        ]);
        let store = Store::at(root.join("store"));
        let tree = Tree::of_revision(&root, "HEAD").expect("the commit has a tree");
        let pbg = built_in().expect("the built-in grammar builds");
        let recorder = Recorder::new(&pbg).expect("each mold has a rule");
        let tool = Digest::of_parts([b"tool".as_slice()]);
        let first = recovery(&store, &tree, &tool, &recorder).expect("the values are given");
        assert_eq!(first.computed, 2);
        let records: Vec<Vec<u8>> = ["def two = (\n", "def one = 1\n"]
            .map(|text| {
                recorder
                    .record(text)
                    .expect("the source gives a tree")
                    .into_bytes()
            })
            .to_vec();
        let values: Vec<Vec<u8>> = first.values.into_iter().map(|(_, value)| value).collect();
        assert_eq!(values, records);
        let second = recovery(&store, &tree, &tool, &recorder).expect("the values are given");
        assert_eq!(second.computed, 0);
        let other = Digest::of_parts([b"other tool".as_slice()]);
        assert_eq!(
            recovery(&store, &tree, &other, &recorder)
                .expect("the values are given")
                .computed,
            2
        );
        std::fs::remove_dir_all(root).expect("the repository is removed");
    }
}
