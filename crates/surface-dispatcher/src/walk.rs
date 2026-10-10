//! The walk: a verb's paths, read and composed one source at a time.
//!
//! # A walk streams
//!
//! The walk holds one source's text at a time, and the step it yields borrows
//! it: a run over a large tree keeps one source in memory, not the tree. The
//! report accumulates as the walk goes, so it is complete once the walk is
//! exhausted, whatever the driver did with each step.
//!
//! # Every path answers
//!
//! A path that cannot be read faults, and so does a path that names no
//! source: a directory holding no `.gandr` file, which would otherwise pass
//! as a settled run over nothing. The walk continues past a fault, so one run
//! reports every path that faults.

use std::ffi::OsStr;
use std::path::Path;
use std::path::PathBuf;

use gandr_surface_corpus::Settlement;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::PbgError;
use gandr_surface_grammar::built_in;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::compose::ComposeFault;
use crate::compose::Composed;
use crate::compose::compose;
use crate::report::RunReport;
use crate::root::SourceRoot;
use crate::root::classify;

quenchant_shape::reason_enum! {
    /// Why a walk yields no further step.
    pub mod walk_step {
        /// The reason no step is yielded.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// Every path has been walked.
            Exhausted,
        }
    }
}

/// The extension a source found by listing a directory carries.
const EXTENSION: &str = "gandr";

/// How one source stands against the root it sits under.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Standing
{
    /// The lowering read it and every declaration settled.
    Settled,
    /// The lowering read it and at least one declaration is unsettled.
    Unsettled,
    /// The lowering refused it as a whole, under the strict or the fixture
    /// root, which expect declarations.
    Refused,
    /// A pending source carrying a refusal no expectation can state, as its
    /// root expects: the lowering refused it as a whole, or refused one of its
    /// declarations at the declaration's own form. Its declarations are not
    /// counted.
    Pending,
    /// A pending source carrying no such refusal: every expectation it needs
    /// can be stated, so it belongs under the fixture root.
    Lowered,
}

impl Standing
{
    /// How `composed`, a source under `root`, stands against its root.
    ///
    /// # Specification
    /// - requires: `composed` is what a source under `root` became.
    /// - ensures: a pending source refused whole, or carrying a declaration
    ///   refused at its own form, is [`Self::Pending`], and one carrying
    ///   neither [`Self::Lowered`]; a strict or fixture source refused whole is
    ///   [`Self::Refused`]; otherwise [`Self::Settled`] exactly when every
    ///   declaration settled, and [`Self::Unsettled`] when one did not.
    /// - provides: the standing a walk step and a session submission carry,
    ///   read by one function so the two cannot disagree.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — whole refusals, refused forms, ordinary declarations
    ///   and an owed declaration have exact standings under the three roots.
    ///   These finite cases separate root precedence and settlement, not every
    ///   possible composition or filesystem classification.
    /// - witness: `walk::tests::each_root_stands_its_sources`
    #[inline]
    #[must_use]
    #[anodized::spec(ensures: |ret| match *composed {
        Composed::Refused(_) => matches!((root, ret),
            (SourceRoot::Pending, Self::Pending)
                | (SourceRoot::Strict | SourceRoot::Fixture, Self::Refused)),
        Composed::Settled { ref report, ref unstatable, .. } => match root {
            SourceRoot::Pending => ret == if unstatable.is_empty() { Self::Lowered } else { Self::Pending },
            SourceRoot::Strict | SourceRoot::Fixture => ret == match report.tally().settlement() {
                Settlement::Settled => Self::Settled,
                Settlement::Unsettled => Self::Unsettled,
            },
        },
    })]
    pub fn of(
        root: SourceRoot,
        composed: &Composed<'_>,
    ) -> Self
    {
        match (root, composed) {
            | (SourceRoot::Pending, &Composed::Refused(_)) => Self::Pending,
            | (SourceRoot::Pending, &Composed::Settled { ref unstatable, .. }) => {
                if unstatable.is_empty() {
                    Self::Lowered
                }
                else {
                    Self::Pending
                }
            },
            | (SourceRoot::Strict | SourceRoot::Fixture, &Composed::Refused(_)) => Self::Refused,
            | (SourceRoot::Strict | SourceRoot::Fixture, &Composed::Settled { ref report, .. }) => {
                match report.tally().settlement() {
                    | Settlement::Settled => Self::Settled,
                    | Settlement::Unsettled => Self::Unsettled,
                }
            },
        }
    }
}

/// Why a path could not be carried through the pipeline.
#[derive(Debug)]
pub enum SourceFault<'walk>
{
    /// The path could not be listed or read, or its text is not UTF-8.
    Unreadable(std::io::Error),
    /// The path names no source: a directory holding no `.gandr` file.
    NoSource,
    /// The built-in grammar did not build, so no source can be parsed.
    Grammar(&'walk PbgError),
    /// The source could not be carried through the pipeline.
    Compose(ComposeFault<'walk>),
}

impl core::fmt::Display for SourceFault<'_>
{
    /// Writes the fault and what it names.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes the source-fault context and its underlying error;
    ///   composition faults retain their declaration-position information.
    /// - fails: propagates the formatter's write failure.
    /// - panics: none.
    /// - executable: none — the formatter's output and failure channel are
    ///   opaque; no emitted text is returned for a local predicate to inspect.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a real composition fault is rendered through this
    ///   wrapper and its nonzero declaration position is asserted numerically.
    ///   This observes the diagnostic field, not explanatory wording or all
    ///   operating-system messages and writer failures.
    /// - witness: `compose::tests::a_kernel_disagreement_is_an_engine_fault`
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        match *self {
            | Self::Unreadable(ref error) => write!(f, "unreadable: {error}"),
            | Self::NoSource => f.write_str("names no `.gandr` source"),
            | Self::Grammar(error) => write!(f, "the built-in grammar did not build: {error}"),
            | Self::Compose(ref fault) => fault.fmt(f),
        }
    }
}

/// One step of a walk.
#[derive(Debug)]
#[expect(
    clippy::large_enum_variant,
    reason = "a walk yields one step per source and the caller consumes it in place; boxing the composition would allocate once per source to shrink a value that is never stored"
)]
pub enum Step<'walk>
{
    /// One source, carried through the pipeline.
    Source
    {
        /// The source's path, as the walk reached it from a path it was
        /// given.
        path: &'walk Path,
        /// The root the source sits under.
        root: SourceRoot,
        /// The source's text, which every span of `composed` is measured
        /// against.
        text: SourceText<'walk>,
        /// What the source became.
        composed: Composed<'walk>,
        /// How it stands against its root.
        standing: Standing,
    },
    /// A path the walk could not carry through the pipeline.
    Fault
    {
        /// The path, as the walk reached it from a path it was given.
        path: &'walk Path,
        /// Why.
        fault: SourceFault<'walk>,
    },
}

/// A walk over the paths a verb was given, yielding one source at a time.
#[derive(Debug)]
pub struct Walk
{
    /// The grammar every source is parsed under, built once per walk.
    grammar: Result<Pbg, PbgError>,
    /// The paths not yet started, the next on top.
    arguments: Vec<PathBuf>,
    /// The path being walked.
    argument: PathBuf,
    /// Whether the path being walked has answered yet.
    answered: Answered,
    /// The entries of the path being walked still to visit, the next on top.
    entries: Vec<Entry>,
    /// The source or directory last reached.
    path: PathBuf,
    /// The text of the source last read.
    text: String,
    /// What the walk has counted so far.
    report: RunReport,
}

/// An entry of the path being walked, still to visit.
#[derive(Debug)]
enum Entry
{
    /// The path given itself, which may be a source of any name or a
    /// directory.
    Argument,
    /// A directory reached by listing.
    Directory(PathBuf),
    /// A source reached by listing.
    Source(PathBuf),
}

/// Whether the path being walked has answered with a source or a fault.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Answered
{
    /// Not yet: if its entries run out now, it named no source.
    Not,
    /// It has; no further answer is owed.
    Yes,
}

impl Walk
{
    /// A walk over `paths`, in the order given, nothing yet read.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the walk visits `paths` in order and has read nothing; the
    ///   built-in grammar is built once, here, which is computation, not I/O.
    /// - provides: the walk a verb routes to.
    /// - fails: never; a grammar that does not build faults each path the walk
    ///   reaches.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — missing arguments answer in their given order, and a
    ///   tree created after construction is read successfully on the first
    ///   step. These distinguish lost paths and eager consumption; they do not
    ///   measure grammar construction or arbitrary filesystem races.
    /// - witness: `walk::tests::every_path_answers_in_order`
    /// - witness: `walk::tests::late_changes_preserve_pending_sources_and_exhaustion`
    #[inline]
    #[must_use]
    #[anodized::spec(
        captures: [offered = paths.len()],
        ensures: |ref ret| ret.arguments.len() == offered
            && usize::from(ret.report.sources().read()) == 0
            && usize::from(ret.report.sources().faulted()) == 0
            && usize::from(ret.report.lowerings()) == 0,
    )]
    pub fn new(paths: Vec<PathBuf>) -> Self
    {
        let mut arguments = paths;
        arguments.reverse();
        Self {
            grammar: built_in(),
            arguments,
            argument: PathBuf::new(),
            answered: Answered::Yes,
            entries: Vec::new(),
            path: PathBuf::new(),
            text: String::new(),
            report: RunReport::default(),
        }
    }

    /// What the walk has counted so far: once the walk is exhausted, the
    /// runner's report for the run.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn report(&self) -> RunReport
    {
        self.report
    }

    /// The next source or fault of the walk.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each path given is visited in order. A directory is walked
    ///   depth-first in byte order, visiting its directories and non-symlink
    ///   `.gandr` entries without following links found in the listing. An
    ///   explicit path may be a link; a non-directory argument is one source,
    ///   whatever its name. Each source is classified by its canonical path,
    ///   read, and composed once, and its step names it by the path the walk
    ///   reached it through and carries the text its spans are measured
    ///   against. A path that cannot be listed or read is a
    ///   [`SourceFault::Unreadable`] step, and a path that yields no source and
    ///   no fault a [`SourceFault::NoSource`] step after its last entry. Every
    ///   step is counted in [`Walk::report`] before it is returned. Exhaustion
    ///   is stable: further steps remain exhausted without changing the report.
    /// - provides: the one pass both verbs render.
    /// - fails: never; every fault is a step, and the walk continues past it.
    /// - panics: none.
    /// - intension: holds one source's text at a time; lists each directory
    ///   once; recursion-free, the pending entries an explicit stack.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — ordered source/fault rows distinguish nested
    ///   traversal, filtering, explicit-file and explicit-link handling, and
    ///   root policies. A directory replaced after discovery faults without
    ///   losing its queued sibling; exhaustion preserves the report even after
    ///   the tree is removed. These are finite filesystem transitions, not
    ///   coverage of special-file reads or every concurrent filesystem
    ///   mutation.
    /// - witness: `walk::tests::a_tree_is_walked_in_order`
    /// - witness: `walk::tests::every_path_answers_in_order`
    /// - witness: `walk::tests::each_root_stands_its_sources`
    /// - witness: `walk::tests::late_changes_preserve_pending_sources_and_exhaustion`
    /// - witness: `walk::tests::an_explicit_link_uses_its_target_root_and_keeps_its_path`
    #[inline]
    #[anodized::spec(
        captures: [pending_arguments = self.arguments.len(), was_answered = self.answered == Answered::Yes],
        ensures: |ref ret| match *ret {
            Maybe::Absent(walk_step::Absent::Exhausted) => pending_arguments == 0,
            Maybe::Present(Step::Source { root, ref composed, standing, .. }) =>
                standing == Standing::of(root, composed),
            Maybe::Present(Step::Fault { fault: SourceFault::NoSource, .. }) =>
                !was_answered || pending_arguments != 0,
            Maybe::Present(Step::Fault { .. }) => true,
        },
    )]
    pub fn step(&mut self) -> Maybe<Step<'_>, walk_step::Absent>
    {
        loop {
            let Some(entry) = self.entries.pop()
            else {
                if self.answered == Answered::Not {
                    self.answered = Answered::Yes;
                    self.report.faulted();
                    return Maybe::Present(Step::Fault {
                        path: &self.argument,
                        fault: SourceFault::NoSource,
                    });
                }
                let Some(argument) = self.arguments.pop()
                else {
                    return Maybe::Absent(walk_step::Absent::Exhausted);
                };
                self.argument = argument;
                self.answered = Answered::Not;
                self.entries.push(Entry::Argument);
                continue;
            };
            match entry {
                | Entry::Argument => match std::fs::metadata(&self.argument) {
                    | Ok(metadata) if metadata.is_dir() => {
                        self.path.clone_from(&self.argument);
                        if let Err(error) = self.list() {
                            return Maybe::Present(self.unreadable(error));
                        }
                    },
                    | Ok(_) => {
                        self.path.clone_from(&self.argument);
                        return Maybe::Present(self.source());
                    },
                    | Err(error) => {
                        self.path.clone_from(&self.argument);
                        return Maybe::Present(self.unreadable(error));
                    },
                },
                | Entry::Directory(directory) => {
                    self.path = directory;
                    if let Err(error) = self.list() {
                        return Maybe::Present(self.unreadable(error));
                    }
                },
                | Entry::Source(source) => {
                    self.path = source;
                    return Maybe::Present(self.source());
                },
            }
        }
    }

    /// Push the directory's directories and non-symlink `.gandr` entries,
    /// so they pop in byte order of their names.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: success appends the selected children in descending path
    ///   order, leaving earlier pending entries in place; failure leaves the
    ///   pending entries unchanged.
    /// - fails: the I/O error listing the path or reading an entry's type.
    /// - panics: none.
    ///
    /// # Errors
    /// The I/O error listing the directory or reading an entry's type met.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nested ordered files and an ignored link observe
    ///   filtering and stack order. Replacing a queued directory with a file
    ///   observes failure without discarding its pending sibling; errors
    ///   partway through directory iteration are outside these witnesses.
    /// - witness: `walk::tests::a_tree_is_walked_in_order`
    /// - witness: `walk::tests::late_changes_preserve_pending_sources_and_exhaustion`
    #[anodized::spec(
        captures: [before = self.entries.len()],
        ensures: |ref ret| if ret.is_err() {
            self.entries.len() == before
        } else {
            self.entries.get(before..).is_some_and(|added|
                added.iter().all(|entry| match *entry {
                    Entry::Directory(ref path) => path.parent() == Some(self.path.as_path()),
                    Entry::Source(ref path) => path.parent() == Some(self.path.as_path())
                        && path.extension() == Some(OsStr::new(EXTENSION)),
                    Entry::Argument => false,
                }) && added.windows(2).all(|pair| match *pair {
                    [ref left, ref right] => entry_path(left) >= entry_path(right),
                    _ => false,
                }))
        },
    )]
    fn list(&mut self) -> std::io::Result<()>
    {
        let mut found = Vec::new();
        let listing = std::fs::read_dir(&self.path)?;
        for listed in listing {
            let listed = listed?;
            let kind = listed.file_type()?;
            let path = listed.path();
            if kind.is_dir() {
                found.push(Entry::Directory(path));
            }
            else if !kind.is_symlink() && path.extension() == Some(OsStr::new(EXTENSION)) {
                found.push(Entry::Source(path));
            }
        }
        found.sort_by(|left, right| entry_path(right).cmp(entry_path(left)));
        self.entries.append(&mut found);
        Ok(())
    }

    /// A fault for `self.path`, counted.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the unreadable fault at the current path with the
    ///   supplied error, marks the argument answered and counts one fault,
    ///   saturating.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — missing arguments and a queued directory replaced by
    ///   a file retain their paths, fault category and exact fault counts while
    ///   later sources remain reachable. Other operating-system errors and
    ///   counter saturation are not independently introduced here.
    /// - witness: `walk::tests::every_path_answers_in_order`
    /// - witness: `walk::tests::late_changes_preserve_pending_sources_and_exhaustion`
    #[anodized::spec(
        captures: [
            expected_path = self.path.as_path(),
            before_faulted = usize::from(self.report.sources().faulted()),
            expected_kind = error.kind(),
            expected_os_error = error.raw_os_error(),
        ],
        ensures: |ref ret| self.answered == Answered::Yes
            && usize::from(self.report.sources().faulted()) == before_faulted.saturating_add(1)
            && match *ret {
                Step::Fault { path, fault: SourceFault::Unreadable(ref error) } =>
                    path == expected_path && error.kind() == expected_kind
                        && error.raw_os_error() == expected_os_error,
                _ => false,
            },
    )]
    fn unreadable(
        &mut self,
        error: std::io::Error,
    ) -> Step<'_>
    {
        self.answered = Answered::Yes;
        self.report.faulted();
        Step::Fault {
            path: &self.path,
            fault: SourceFault::Unreadable(error),
        }
    }

    /// Classify, read and compose the source at `self.path`, counted.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: marks the argument answered and returns either the complete
    ///   source with its canonical root and corresponding standing, or its
    ///   read, grammar or composition fault. The original path is retained and
    ///   the source or fault is counted once.
    /// - fails: never; errors are returned as fault steps.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — exact paths, complete source bytes, standings and
    ///   counters separate source and fault outcomes; an explicit Unix link
    ///   separates canonical classification from the reported path. The local
    ///   predicate observes path length and standing, while witnesses compare
    ///   full paths. Grammar-construction failure is not forced.
    /// - witness: `walk::tests::each_root_stands_its_sources`
    /// - witness: `walk::tests::every_path_answers_in_order`
    /// - witness: `walk::tests::late_changes_preserve_pending_sources_and_exhaustion`
    /// - witness: `walk::tests::an_explicit_link_uses_its_target_root_and_keeps_its_path`
    #[anodized::spec(
        captures: [path_bytes = self.path.as_os_str().len()],
        ensures: |ref ret| match *ret {
            Step::Source { path, root, ref composed, standing, .. } =>
                path.as_os_str().len() == path_bytes && standing == Standing::of(root, composed),
            Step::Fault { path, ref fault } => path.as_os_str().len() == path_bytes
                && !matches!(*fault, SourceFault::NoSource),
        },
    )]
    fn source(&mut self) -> Step<'_>
    {
        self.answered = Answered::Yes;
        let root = match read_source(&self.path, &mut self.text) {
            | Ok(root) => root,
            | Err(error) => return self.unreadable(error),
        };
        let grammar = match self.grammar {
            | Ok(ref grammar) => grammar,
            | Err(ref error) => {
                self.report.faulted();
                return Step::Fault {
                    path: &self.path,
                    fault: SourceFault::Grammar(error),
                };
            },
        };
        match compose(
            grammar,
            root.corpus_root(),
            SourceText::from(self.text.as_str()),
            self.report.lowerings_mut(),
        ) {
            | Ok(composed) => {
                let standing = Standing::of(root, &composed);
                self.report.read(root, &composed, standing);
                Step::Source {
                    path: &self.path,
                    root,
                    text: SourceText::from(self.text.as_str()),
                    composed,
                    standing,
                }
            },
            | Err(fault) => {
                self.report.faulted();
                Step::Fault {
                    path: &self.path,
                    fault: SourceFault::Compose(fault),
                }
            },
        }
    }
}

/// Classify the source at `path` by its canonical path, and read its text
/// into `text`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: success replaces `text` with the complete UTF-8 file and returns
///   the root of its canonical path. On any error, the previous text is
///   unchanged.
/// - fails: the I/O error from canonicalization or reading, including a
///   directory or invalid UTF-8.
/// - panics: none.
///
/// # Errors
/// The I/O error canonicalizing or reading the path met.
///
/// # Adequacy
/// - hypothesis: L3 — missing, directory and invalid-UTF-8 paths preserve a
///   nonempty Unicode sentinel exactly. Successful walk steps retain complete
///   source bytes; a Unix link under a different lexical root uses its target's
///   root. These cases do not model every I/O error or concurrent file rewrite.
/// - witness: `walk::tests::failed_reads_preserve_the_previous_source`
/// - witness: `walk::tests::late_changes_preserve_pending_sources_and_exhaustion`
/// - witness: `walk::tests::an_explicit_link_uses_its_target_root_and_keeps_its_path`
#[anodized::spec(
    captures: [before = text.len()],
    ensures: |ref ret| ret.is_ok() || text.len() == before,
)]
pub fn read_source(
    path: &Path,
    text: &mut String,
) -> std::io::Result<SourceRoot>
{
    let canonical = std::fs::canonicalize(path)?;
    *text = std::fs::read_to_string(path)?;
    Ok(classify(&canonical))
}

/// The path an entry reached by listing names.
///
/// # Specification
/// - requires: `entry` is a listed directory or source, not an argument marker.
/// - ensures: returns that entry's contained path.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a listed directory before multiple source files produces
///   the exact expected depth-first order, distinguishing either listed path
///   being lost or substituted. Argument markers are outside this helper's
///   domain.
/// - witness: `walk::tests::a_tree_is_walked_in_order`
#[anodized::spec(
    requires: !matches!(*entry, Entry::Argument),
    ensures: |ret| match *entry {
        Entry::Directory(ref path) | Entry::Source(ref path) => ret == path,
        Entry::Argument => false,
    },
)]
fn entry_path(entry: &Entry) -> &Path
{
    match *entry {
        | Entry::Directory(ref path) | Entry::Source(ref path) => path,
        | Entry::Argument => Path::new(""),
    }
}

#[cfg(test)]
mod tests
{
    use std::io;
    use std::path::Path;
    use std::path::PathBuf;

    use gandr_surface_syntax::SourceText;
    use quenchant_shape::shape::Maybe;

    use super::SourceFault;
    use super::Standing;
    use super::Step;
    use super::Walk;
    use crate::report::SourceCount;
    use crate::root::SourceRoot;
    use crate::root::classify;

    /// A fresh scratch directory, removed when dropped.
    #[repr(transparent)]
    struct Scratch(PathBuf);

    impl Scratch
    {
        /// An empty directory named for `test` and this process.
        ///
        /// # Specification
        /// - requires: the derived temporary path is exclusively owned by this
        ///   fixture, may be replaced and has a writable parent.
        /// - ensures: returns an empty readable directory at that path.
        /// - fails: never.
        /// - panics: if a stale directory cannot be removed or a new one
        ///   created.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — isolated trees accept the fixture's nested files,
        ///   and exact walk rows observe their contents. These witnesses use
        ///   fresh temporary namespaces, not hostile permissions or
        ///   interference.
        /// - witness: `walk::tests::a_tree_is_walked_in_order`
        /// - witness: `walk::tests::late_changes_preserve_pending_sources_and_exhaustion`
        #[anodized::spec(ensures: |ref ret|
            std::fs::read_dir(&ret.0).is_ok_and(|mut entries| entries.next().is_none()))]
        fn new(test: &Path) -> Self
        {
            let root = std::env::temp_dir().join(format!(
                "gandr-dispatcher-{}-{}",
                test.display(),
                std::process::id()
            ));
            if root.exists() {
                std::fs::remove_dir_all(&root).expect("a stale scratch directory is removed");
            }
            std::fs::create_dir_all(&root).expect("the scratch directory is created");
            Self(root)
        }

        /// Write `text` at `relative`, creating its directories.
        ///
        /// # Specification
        /// - requires: `relative` names a writable file below the owned fixture
        ///   using a nonempty relative sequence of normal path components.
        /// - ensures: creates the required parent directories and writes
        ///   `text`.
        /// - fails: never.
        /// - panics: if a parent is absent from the path or filesystem creation
        ///   or writing fails.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — nested source files have their complete bytes and
        ///   resulting walk outcomes observed. This separates missing parents
        ///   and wrong contents for the fixture paths, not arbitrary path
        ///   shapes or external filesystem mutation.
        /// - witness: `walk::tests::a_tree_is_walked_in_order`
        /// - witness: `walk::tests::late_changes_preserve_pending_sources_and_exhaustion`
        /// - witness: `walk::tests::an_explicit_link_uses_its_target_root_and_keeps_its_path`
        #[anodized::spec(requires: relative.is_relative() && relative.file_name().is_some()
            && relative.components().all(|component|
                matches!(component, std::path::Component::Normal(_))))]
        fn file(
            &self,
            relative: &Path,
            text: SourceText<'_>,
        )
        {
            let path = self.0.join(relative);
            std::fs::create_dir_all(path.parent().expect("a file has a parent"))
                .expect("the directories are created");
            std::fs::write(path, text.as_ref()).expect("the file is written");
        }
    }

    impl Drop for Scratch
    {
        /// Remove the directory and everything under it.
        ///
        /// # Specification
        /// - requires: the fixture exclusively owns its removable directory.
        /// - ensures: the fixture directory no longer exists.
        /// - fails: never.
        /// - panics: if removal fails.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — a populated tree's path is retained across drop
        ///   and observed absent afterward. This detects omitted cleanup on
        ///   normal exit, not unwinding or external permission changes.
        /// - witness: `walk::tests::late_changes_preserve_pending_sources_and_exhaustion`
        #[anodized::spec(ensures: self.0.try_exists().is_ok_and(|exists| !exists))]
        fn drop(&mut self)
        {
            let removed = std::fs::remove_dir_all(&self.0);
            assert!(removed.is_ok(), "the scratch directory is removed");
        }
    }

    /// What a test row records of one step.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum Seen
    {
        /// A source, and how it stands.
        Source(Standing),
        /// A path that could not be listed or read.
        Unreadable,
        /// A path that yielded no source.
        NoSource,
        /// The grammar did not build.
        Grammar,
        /// The pipeline faulted on a source.
        Compose,
    }

    impl From<&Step<'_>> for Seen
    {
        /// What a test row records of `step`.
        ///
        /// # Specification
        /// - requires: nothing.
        /// - ensures: preserves a source's standing, or records the exact
        ///   source-fault category without retaining its borrowed payload.
        /// - fails: never.
        /// - panics: none.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — exact rows separate source standings, unreadable
        ///   paths and empty directories. Grammar and composition engine faults
        ///   are outside these filesystem fixtures.
        /// - witness: `walk::tests::a_tree_is_walked_in_order`
        /// - witness: `walk::tests::every_path_answers_in_order`
        /// - witness: `walk::tests::each_root_stands_its_sources`
        #[anodized::spec(ensures: |ret| match (step, ret) {
            (&Step::Source { standing, .. }, Self::Source(observed)) => observed == standing,
            (&Step::Fault { fault: SourceFault::Unreadable(_), .. }, Self::Unreadable)
                | (&Step::Fault { fault: SourceFault::NoSource, .. }, Self::NoSource)
                | (&Step::Fault { fault: SourceFault::Grammar(_), .. }, Self::Grammar)
                | (&Step::Fault { fault: SourceFault::Compose(_), .. }, Self::Compose) => true,
            _ => false,
        })]
        fn from(step: &Step<'_>) -> Self
        {
            match *step {
                | Step::Source { standing, .. } => Self::Source(standing),
                | Step::Fault { ref fault, .. } => match *fault {
                    | SourceFault::Unreadable(_) => Self::Unreadable,
                    | SourceFault::NoSource => Self::NoSource,
                    | SourceFault::Grammar(_) => Self::Grammar,
                    | SourceFault::Compose(_) => Self::Compose,
                },
            }
        }
    }

    /// Every step of a walk over `paths`, as `(path relative to base, seen)`,
    /// and the exhausted walk.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: records each step in order, strips `base` only when it is a
    ///   prefix, and returns an exhausted walk whose source and fault counts
    ///   agree with the recorded rows.
    /// - fails: never; source faults are recorded as rows.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — exact relative paths, standings and aggregate counts
    ///   on nested, empty and missing inputs detect lost, duplicated or
    ///   reordered observations. These fixtures use an ancestral base, not
    ///   every possible prefix relationship or filesystem fault.
    /// - witness: `walk::tests::a_tree_is_walked_in_order`
    /// - witness: `walk::tests::every_path_answers_in_order`
    /// - witness: `walk::tests::each_root_stands_its_sources`
    #[anodized::spec(ensures: |ref ret| {
        let sources = ret.0.iter().filter(|row| matches!(row.1, Seen::Source(_))).count();
        ret.1.arguments.is_empty() && ret.1.entries.is_empty()
            && ret.1.answered == super::Answered::Yes
            && sources == usize::from(ret.1.report().sources().read())
            && ret.0.len().checked_sub(sources) == Some(usize::from(ret.1.report().sources().faulted()))
    })]
    fn steps(
        base: &Path,
        paths: Vec<PathBuf>,
    ) -> (Vec<(PathBuf, Seen)>, Walk)
    {
        let mut walk = Walk::new(paths);
        let mut seen = Vec::new();
        while let Maybe::Present(step) = walk.step() {
            let kind = Seen::from(&step);
            let path = match step {
                | Step::Source { path, .. } | Step::Fault { path, .. } => path,
            };
            seen.push((path.strip_prefix(base).unwrap_or(path).to_path_buf(), kind));
        }
        (seen, walk)
    }

    /// `(path, seen)` rows with owned paths.
    ///
    /// # Specification
    ///
    /// trivial.
    fn rows(pairs: &[(&Path, Seen)]) -> Vec<(PathBuf, Seen)>
    {
        pairs
            .iter()
            .map(|&(path, seen)| (path.to_path_buf(), seen))
            .collect()
    }

    #[test]
    fn a_tree_is_walked_in_order()
    {
        let scratch = Scratch::new(Path::new("tree"));
        scratch.file(Path::new("tree/b.gandr"), SourceText::from("def b = 2 ;"));
        scratch.file(
            Path::new("tree/a/z.gandr"),
            SourceText::from("def z = missing ;"),
        );
        scratch.file(Path::new("tree/a/y.gandr"), SourceText::from("def y = 1 ;"));
        scratch.file(
            Path::new("tree/a/notes.txt"),
            SourceText::from("not a source"),
        );
        scratch.file(Path::new("tree/c.gandr"), SourceText::from("ret 3"));
        scratch.file(Path::new("named.source"), SourceText::from("def n = 4 ;"));
        scratch.file(
            Path::new("elsewhere/linked.gandr"),
            SourceText::from("def l = 5 ;"),
        );
        #[cfg(unix)]
        std::os::unix::fs::symlink(
            scratch.0.join("elsewhere/linked.gandr"),
            scratch.0.join("tree/linked.gandr"),
        )
        .expect("the link is made");

        let (seen, walk) = steps(&scratch.0, vec![
            scratch.0.join("tree"),
            scratch.0.join("named.source"),
        ]);
        assert_eq!(
            seen,
            rows(&[
                (Path::new("tree/a/y.gandr"), Seen::Source(Standing::Settled)),
                (
                    Path::new("tree/a/z.gandr"),
                    Seen::Source(Standing::Unsettled)
                ),
                (Path::new("tree/b.gandr"), Seen::Source(Standing::Settled)),
                (Path::new("tree/c.gandr"), Seen::Source(Standing::Refused)),
                (Path::new("named.source"), Seen::Source(Standing::Settled)),
            ]),
            "depth-first in name order, sources only, no link followed, an explicit file of any name"
        );
        let report = walk.report();
        assert_eq!(
            report.sources().strict(),
            SourceCount::from(5_usize),
            "five strict sources"
        );
        assert_eq!(
            report.sources().refused(),
            SourceCount::from(1_usize),
            "one refused whole"
        );
        assert_eq!(
            usize::from(report.lowerings()),
            5_usize,
            "one lowering per source read"
        );
        assert_eq!(
            usize::from(report.tally().declarations().unsettled()),
            1_usize,
            "the undefined name is the one unsettled declaration"
        );
    }

    #[test]
    fn every_path_answers_in_order()
    {
        let scratch = Scratch::new(Path::new("answers"));
        scratch.file(
            Path::new("empty/notes.txt"),
            SourceText::from("not a source"),
        );
        scratch.file(Path::new("one.gandr"), SourceText::from("def one = 1 ;"));
        let (seen, walk) = steps(&scratch.0, vec![
            scratch.0.join("absent.gandr"),
            scratch.0.join("empty"),
            scratch.0.join("one.gandr"),
            scratch.0.join("absent"),
        ]);
        assert_eq!(
            seen,
            rows(&[
                (Path::new("absent.gandr"), Seen::Unreadable),
                (Path::new("empty"), Seen::NoSource),
                (Path::new("one.gandr"), Seen::Source(Standing::Settled)),
                (Path::new("absent"), Seen::Unreadable),
            ]),
            "each path answers once, in the order given"
        );
        assert_eq!(
            walk.report().sources().faulted(),
            SourceCount::from(3_usize),
            "three faults"
        );
        assert_eq!(
            walk.report().sources().read(),
            SourceCount::from(1_usize),
            "one source read"
        );
    }

    #[test]
    fn each_root_stands_its_sources()
    {
        let scratch = Scratch::new(Path::new("roots"));
        let owes = SourceText::from("@[ owes(1) ] def a : Integer ;");
        scratch.file(Path::new("corpus/strict/owes.gandr"), owes);
        scratch.file(Path::new("corpus/fixture/owes.gandr"), owes);
        scratch.file(
            Path::new("corpus/fixture/whole.gandr"),
            SourceText::from("ret 3"),
        );
        scratch.file(
            Path::new("corpus/fixture/pending/outside.gandr"),
            SourceText::from("ret 3"),
        );
        scratch.file(
            Path::new("corpus/fixture/pending/lowered.gandr"),
            SourceText::from("def a = 1 ;"),
        );
        scratch.file(
            Path::new("corpus/fixture/pending/form.gandr"),
            SourceText::from(
                "def rec f(x: Integer) -> -F Integer { ret x }\ndef broken = missing ;",
            ),
        );
        let (seen, walk) = steps(&scratch.0, vec![scratch.0.join("corpus")]);
        assert_eq!(
            seen,
            rows(&[
                (
                    Path::new("corpus/fixture/owes.gandr"),
                    Seen::Source(Standing::Settled)
                ),
                (
                    Path::new("corpus/fixture/pending/form.gandr"),
                    Seen::Source(Standing::Pending)
                ),
                (
                    Path::new("corpus/fixture/pending/lowered.gandr"),
                    Seen::Source(Standing::Lowered)
                ),
                (
                    Path::new("corpus/fixture/pending/outside.gandr"),
                    Seen::Source(Standing::Pending)
                ),
                (
                    Path::new("corpus/fixture/whole.gandr"),
                    Seen::Source(Standing::Refused)
                ),
                (
                    Path::new("corpus/strict/owes.gandr"),
                    Seen::Source(Standing::Unsettled)
                ),
            ]),
            "the root each source sits under decides its standing"
        );
        let report = walk.report();
        let sources = report.sources();
        assert_eq!(
            (sources.strict(), sources.fixture(), sources.pending()),
            (
                SourceCount::from(1_usize),
                SourceCount::from(2_usize),
                SourceCount::from(3_usize)
            ),
            "each source counted under its root"
        );
        assert_eq!(
            (sources.refused(), sources.lowered_pending()),
            (SourceCount::from(1_usize), SourceCount::from(1_usize)),
            "the fixture source refused whole, and the pending source lowered"
        );
        assert_eq!(
            (
                usize::from(report.tally().declarations().settled()),
                usize::from(report.tally().declarations().unsettled())
            ),
            (2_usize, 1_usize),
            "a pending source's declarations are not counted; a lowered one's are"
        );
        assert_eq!(
            classify(&scratch.0.join("corpus/fixture/pending/outside.gandr")),
            SourceRoot::Pending,
            "the pending set is classified by location"
        );
    }

    #[test]
    fn late_changes_preserve_pending_sources_and_exhaustion()
    {
        let scratch = Scratch::new(Path::new("late-changes"));
        let root = scratch.0.join("strict/tree");
        let mut walk = Walk::new(vec![root.clone()]);
        let first = "def first = 1 ;";
        let last = "def last = 2 ;";
        scratch.file(Path::new("strict/tree/0.gandr"), SourceText::from(first));
        let changed = root.join("a");
        std::fs::create_dir_all(&changed).expect("the intermediate directory is created");
        scratch.file(Path::new("strict/tree/b.gandr"), SourceText::from(last));

        let Maybe::Present(Step::Source { path, text, .. }) = walk.step()
        else {
            panic!("the tree created after construction is read on demand");
        };
        assert_eq!(
            path.strip_prefix(&root).expect("inside the tree"),
            Path::new("0.gandr")
        );
        assert_eq!(text, SourceText::from(first));
        std::fs::remove_dir(&changed).expect("the discovered directory is removed");
        std::fs::write(&changed, "no longer a directory").expect("a file replaces it");

        let Maybe::Present(Step::Fault {
            path,
            fault: SourceFault::Unreadable(_),
        }) = walk.step()
        else {
            panic!("the changed directory is reported as an unreadable listing");
        };
        assert_eq!(path, changed.as_path());
        let Maybe::Present(Step::Source { path, text, .. }) = walk.step()
        else {
            panic!("the listing fault leaves the later source queued");
        };
        assert_eq!(
            path.strip_prefix(&root).expect("inside the tree"),
            Path::new("b.gandr")
        );
        assert_eq!(text, SourceText::from(last));
        let report = walk.report();
        assert_eq!(usize::from(report.sources().read()), 2);
        assert_eq!(usize::from(report.sources().faulted()), 1);
        assert_eq!(usize::from(report.lowerings()), 2);
        assert!(matches!(
            walk.step(),
            Maybe::Absent(super::walk_step::Absent::Exhausted)
        ));
        assert_eq!(walk.report(), report);

        let removed = root
            .parent()
            .expect("the strict directory")
            .parent()
            .expect("the fixture root");
        drop(scratch);
        assert!(removed.try_exists().is_ok_and(|exists| !exists));
        assert!(matches!(
            walk.step(),
            Maybe::Absent(super::walk_step::Absent::Exhausted)
        ));
        assert_eq!(walk.report(), report);
    }

    #[test]
    fn failed_reads_preserve_the_previous_source()
    {
        let scratch = Scratch::new(Path::new("failed-reads"));
        let absent = scratch.0.join("absent.gandr");
        let invalid = scratch.0.join("invalid.gandr");
        std::fs::write(&invalid, [0xff_u8]).expect("the invalid UTF-8 file is written");
        let previous = "previous λ\r\n";
        let mut text = previous.to_owned();
        for (path, expected_kind) in [
            (absent.as_path(), Some(io::ErrorKind::NotFound)),
            (scratch.0.as_path(), None),
            (invalid.as_path(), Some(io::ErrorKind::InvalidData)),
        ] {
            let error =
                super::read_source(path, &mut text).expect_err("the path is not a readable source");
            if let Some(kind) = expected_kind {
                assert_eq!(error.kind(), kind);
            }
            assert_eq!(
                text, previous,
                "an unsuccessful read leaves the previous source intact"
            );
        }
    }

    #[cfg(unix)]
    #[test]
    fn an_explicit_link_uses_its_target_root_and_keeps_its_path()
    {
        let scratch = Scratch::new(Path::new("explicit-link"));
        let source = SourceText::from("def greeting = \"λ\" ;\r\n");
        scratch.file(Path::new("fixture/pending/target.gandr"), source);
        let target = scratch.0.join("fixture/pending/target.gandr");
        std::fs::create_dir_all(scratch.0.join("strict")).expect("the alias directory is created");
        let alias = scratch.0.join("strict/alias.gandr");
        std::os::unix::fs::symlink(&target, &alias).expect("the explicit link is created");
        assert_eq!(classify(&alias), SourceRoot::Strict);
        let mut walk = Walk::new(vec![alias.clone()]);
        let Maybe::Present(Step::Source {
            path,
            root,
            text,
            standing,
            ..
        }) = walk.step()
        else {
            panic!("an explicit symbolic link is read as its target");
        };
        assert_eq!(path, alias.as_path());
        assert_eq!(root, SourceRoot::Pending);
        assert_eq!(standing, Standing::Lowered);
        assert_eq!(text, source);
    }
}
