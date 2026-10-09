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
    /// - hypothesis: L3 — each arm is reached by a source of its root and
    ///   shape, asserted at its exact standing.
    /// - witness: `walk::tests::each_root_stands_its_sources`
    #[inline]
    #[must_use]
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
    /// trivial.
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
    /// - hypothesis: L3 — the order is observed through the faults of absent
    ///   paths, reported in the order given.
    /// - witness: `walk::tests::every_path_answers_in_order`
    #[inline]
    #[must_use]
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
    /// - ensures: each path given is visited in order. A path that is a
    ///   directory is walked depth-first in byte order of its entries' names,
    ///   reaching every directory and every regular `.gandr` file below it and
    ///   following no symbolic link; any other path is read as one source,
    ///   whatever its name. Each source is classified by its canonical path,
    ///   read, and composed once, and its step names it by the path the walk
    ///   reached it through and carries the text its spans are measured
    ///   against. A path that cannot be listed or read is a
    ///   [`SourceFault::Unreadable`] step, and a path that yields no source and
    ///   no fault a [`SourceFault::NoSource`] step after its last entry. Every
    ///   step is counted in [`Walk::report`] before it is returned.
    /// - provides: the one pass both verbs render.
    /// - fails: never; every fault is a step, and the walk continues past it.
    /// - panics: none.
    /// - intension: holds one source's text at a time; lists each directory
    ///   once; recursion-free, the pending entries an explicit stack.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a tree with a nested directory, a non-source file, a
    ///   symbolic link, an explicit file of another extension, an empty
    ///   directory and an absent path, each step asserted at its exact path and
    ///   kind, the report's counts at the end; a pending source refused as
    ///   outside the fragment, refused otherwise, and lowered.
    /// - witness: `walk::tests::a_tree_is_walked_in_order`
    /// - witness: `walk::tests::every_path_answers_in_order`
    /// - witness: `walk::tests::each_root_stands_its_sources`
    #[inline]
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

    /// Push the directory at `self.path`'s directories and `.gandr` files,
    /// so they pop in byte order of their names.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// The I/O error listing the directory or reading an entry's type met.
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
    /// trivial.
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
    /// trivial.
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
/// trivial.
///
/// # Errors
/// The I/O error canonicalizing or reading the path met, a path naming a
/// directory or text that is not UTF-8 among them.
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
/// trivial.
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
        ///
        /// trivial.
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
        ///
        /// trivial.
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
        ///
        /// trivial.
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
        ///
        /// trivial.
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
    ///
    /// trivial.
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
}
