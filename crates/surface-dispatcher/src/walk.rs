//! The walk: a verb's paths, read and composed in order.
//!
//! # A serial walk streams
//!
//! The serial walk holds one source's text at a time, and the step it yields
//! borrows it: a run over a large tree keeps one source in memory, not the
//! tree. The report accumulates as the walk goes, so it is complete once the
//! walk is exhausted, whatever the driver did with each step.
//!
//! # A wider walk forks by source
//!
//! [`Walk::visit`] at a width above one first reaches every path, then reads,
//! parses and lowers the sources on a pool, each thread taking the largest
//! source no thread has taken yet, and then judges, settles, counts and
//! hands each source to its visitor in walk order on the calling thread. A
//! source's state stays private to the thread lowering it until the calling
//! thread takes it whole; the grammar is the one value the threads share, and
//! only read. Every step, count and verdict is the serial walk's.
//!
//! # Every path answers
//!
//! A path that cannot be read faults, and so does a path that names no
//! source: a directory holding no `.gandr` file, which would otherwise pass
//! as a settled run over nothing. The walk continues past a fault, so one run
//! reports every path that faults.

use alloc::collections::BTreeMap;
use core::cmp::Reverse;
use core::ops::ControlFlow;
use core::sync::atomic::AtomicUsize;
use core::sync::atomic::Ordering;
use std::ffi::OsStr;
use std::path::Path;
use std::path::PathBuf;
use std::sync::OnceLock;

use anodized::spec;
use gandr_surface_corpus::Settlement;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::PbgError;
use gandr_surface_grammar::built_in;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::compose::ComposeFault;
use crate::compose::Composed;
use crate::compose::Lowering;
use crate::compose::LoweringCount;
use crate::compose::compose;
use crate::compose::judge_lowering;
use crate::compose::lower_source;
use crate::report::RunReport;
use crate::root::SourceRoot;
use crate::root::classify;
use crate::width::Width;

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
    #[spec(ensures: |ret| match *composed {
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

/// A walk over the paths a verb was given, yielding its sources in order.
#[derive(Debug)]
pub struct Walk
{
    /// The grammar every source is parsed under, built once per walk.
    grammar: Result<Pbg, PbgError>,
    /// Where the walk is among the paths it was given.
    traversal: Traversal,
    /// The text of the source the serial walk read last.
    text: String,
    /// What the walk has counted so far.
    report: RunReport,
}

/// Where a walk is among the paths it was given.
#[derive(Debug)]
struct Traversal
{
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

/// What the traversal reached next, at the walk's current path.
#[derive(Debug)]
enum Reached
{
    /// A source to classify, read and compose.
    Source,
    /// A path that could not be listed, or whose kind could not be read.
    Unreadable(std::io::Error),
    /// The path given yielded no source and no fault.
    NoSource,
}

/// What a pool thread made of one source of a wider walk.
#[derive(Debug)]
#[expect(
    clippy::large_enum_variant,
    reason = "one per source, moved once into its step; boxing the lowering would allocate once \
              per source to shrink the rare unreadable one"
)]
enum Forked<'text>
{
    /// The source could not be classified or read.
    Unreadable(std::io::Error),
    /// The source was read and carried through [`lower_source`].
    Lowered
    {
        /// The root its canonical path sits under.
        root: SourceRoot,
        /// Its text, which every span of `lowering` is measured against.
        text: SourceText<'text>,
        /// What parsing and lowering it came to.
        lowering: Result<Lowering<'text>, ComposeFault<'text>>,
        /// The lowerings performed: one, unless the parse failed.
        lowerings: LoweringCount,
    },
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
    #[spec(
        captures: [offered = paths.len()],
        ensures: |ref ret| ret.traversal.arguments.len() == offered
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
            traversal: Traversal {
                arguments,
                argument: PathBuf::new(),
                answered: Answered::Yes,
                entries: Vec::new(),
                path: PathBuf::new(),
            },
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
    #[spec(
        captures: [
            pending_arguments = self.traversal.arguments.len(),
            was_answered = self.traversal.answered == Answered::Yes,
        ],
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
        match self.traversal.reach() {
            | Maybe::Absent(absent) => Maybe::Absent(absent),
            | Maybe::Present(Reached::Source) => Maybe::Present(self.source()),
            | Maybe::Present(Reached::Unreadable(error)) => Maybe::Present(self.unreadable(error)),
            | Maybe::Present(Reached::NoSource) => {
                self.report.faulted();
                Maybe::Present(Step::Fault {
                    path: &self.traversal.path,
                    fault: SourceFault::NoSource,
                })
            },
        }
    }

    /// Hand every step of the walk to `visitor`, in walk order, lowering the
    /// sources on `width` threads, and answer the walk's report.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `visitor` receives exactly the steps [`Walk::step`] yields
    ///   from this walk, in its order, each counted into the report before it
    ///   is handed over. The answer is `Continue` with the exhausted walk's
    ///   report, or the first `Break` `visitor` returns, after which no step is
    ///   handed over or counted and no thread starts another source.
    ///   [`Width::SERIAL`], or a grammar that did not build, runs the serial
    ///   walk itself. Any other width first reaches every path; then as many
    ///   threads as the width answers, never more than the sources, the calling
    ///   thread among them, classify, read, parse and lower the sources, each
    ///   taking the largest source by bytes that no thread has taken. The
    ///   calling thread meanwhile judges, settles, counts and hands over each
    ///   source in walk order as its lowering arrives, and lowers a source
    ///   itself whenever the next one in walk order has not arrived. A single
    ///   source is lowered on the calling thread alone, and the host is asked
    ///   its width only when there are two sources or more. A thread the host
    ///   refuses to start leaves its sources to the others; with none started,
    ///   the calling thread lowers each source in walk order.
    /// - provides: the pass `check` and `test` run, at the width the driver
    ///   chose.
    /// - fails: never; every fault is a step, and the walk continues past it.
    /// - panics: only by propagating a panic of `visitor` or of a pool thread,
    ///   once every thread has stopped.
    /// - intension: the serial walk holds one source's text at a time; a wider
    ///   walk lists every directory before it reads a source, holds every
    ///   source's text until the visit ends, and each lowering until its source
    ///   is handed over.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — trees mixing nested sources, unreadable paths, empty
    ///   directories and every root yield the same rows and reports at widths
    ///   one and three; the corpus yields equal compositions, step by step, at
    ///   every width tried. A single source and a stopped visit are observed
    ///   exactly. Thread interleavings beyond those runs, and filesystem
    ///   changes during a visit, are outside these witnesses.
    /// - witness: `walk::tests::a_tree_is_walked_in_order`
    /// - witness: `walk::tests::every_path_answers_in_order`
    /// - witness: `walk::tests::each_root_stands_its_sources`
    /// - witness: `walk::tests::a_stopped_visit_hands_over_nothing_more`
    /// - witness: `corpus::corpus::every_width_composes_the_corpus_alike`
    #[inline]
    #[spec(ensures: |ref ret| match *ret {
        ControlFlow::Continue(ref report) => usize::from(report.lowerings())
            <= usize::from(report.sources().read()).saturating_add(usize::from(report.sources().faulted())),
        ControlFlow::Break(_) => true,
    })]
    pub fn visit<Stop, Visitor>(
        mut self,
        width: Width,
        mut visitor: Visitor,
    ) -> ControlFlow<Stop, RunReport>
    where
        Visitor: FnMut(Step<'_>) -> ControlFlow<Stop>,
    {
        let grammar = match self.grammar {
            | Ok(ref grammar) if width != Width::SERIAL => grammar,
            | Ok(_) | Err(_) => {
                while let Maybe::Present(step) = self.step() {
                    visitor(step)?;
                }
                return ControlFlow::Continue(self.report);
            },
        };
        let mut paths = Vec::new();
        let mut found = Vec::new();
        while let Maybe::Present(reached) = self.traversal.reach() {
            paths.push(core::mem::take(&mut self.traversal.path));
            found.push(reached);
        }
        // One text slot per path reached, filled by whichever thread lowers
        // that source; a fault's slot stays empty.
        let texts: Vec<OnceLock<String>> = paths.iter().map(|_| OnceLock::new()).collect();
        let mut order: Vec<(Reverse<u64>, usize)> = paths
            .iter()
            .zip(&found)
            .enumerate()
            .filter(|&(_, (_, reached))| matches!(*reached, Reached::Source))
            .map(|(position, (path, _))| {
                let bytes = std::fs::metadata(path).map_or(0, |metadata| metadata.len());
                (Reverse(bytes), position)
            })
            .collect();
        order.sort_unstable();
        let threads = match order.len() {
            | 0 | 1 => 1,
            | sources => usize::from(core::num::NonZeroUsize::from(width.threads())).min(sources),
        };
        let cursor = AtomicUsize::new(0);
        // The largest source no thread has taken, lowered.
        let take = || {
            let &(_, position) = order.get(cursor.fetch_add(1, Ordering::Relaxed))?;
            let (path, text) = (paths.get(position)?, texts.get(position)?);
            Some((position, fork(grammar, path, text)))
        };
        let (sender, receiver) = std::sync::mpsc::channel();
        std::thread::scope(|scope| {
            let mut pool = 0_usize;
            for _ in 1 .. threads {
                let sender = sender.clone();
                let started = std::thread::Builder::new().spawn_scoped(scope, move || {
                    while let Some(lowered) = take() {
                        if sender.send(lowered).is_err() {
                            break;
                        }
                    }
                });
                if started.is_ok() {
                    pool = pool.saturating_add(1);
                }
            }
            drop(sender);
            // Lowerings that arrived ahead of their turn in walk order.
            let mut early = BTreeMap::new();
            let walked = paths.iter().zip(found).zip(&texts).enumerate();
            for (position, ((path, reached), text)) in walked {
                let step = match reached {
                    | Reached::NoSource => {
                        self.report.faulted();
                        Step::Fault {
                            path,
                            fault: SourceFault::NoSource,
                        }
                    },
                    | Reached::Unreadable(error) => {
                        self.report.faulted();
                        Step::Fault {
                            path,
                            fault: SourceFault::Unreadable(error),
                        }
                    },
                    | Reached::Source => {
                        let forked = loop {
                            if pool == 0 {
                                break fork(grammar, path, text);
                            }
                            if let Some(forked) = early.remove(&position) {
                                break forked;
                            }
                            if let Ok((arrived, forked)) = receiver.try_recv() {
                                early.insert(arrived, forked);
                                continue;
                            }
                            if let Some((taken, forked)) = take() {
                                if taken == position {
                                    break forked;
                                }
                                early.insert(taken, forked);
                                continue;
                            }
                            match receiver.recv() {
                                | Ok((arrived, forked)) => {
                                    early.insert(arrived, forked);
                                },
                                // Every pool thread has stopped without it:
                                // one panicked, and the scope will say so.
                                | Err(_) => break fork(grammar, path, text),
                            }
                        };
                        match forked {
                            | Forked::Unreadable(error) => {
                                self.report.faulted();
                                Step::Fault {
                                    path,
                                    fault: SourceFault::Unreadable(error),
                                }
                            },
                            | Forked::Lowered {
                                root,
                                text,
                                lowering,
                                lowerings,
                            } => {
                                self.report.lowerings_mut().absorb(lowerings);
                                let composed = lowering.and_then(|lowering| {
                                    judge_lowering(root.corpus_root(), lowering)
                                });
                                settled(&mut self.report, path, root, text, composed)
                            },
                        }
                    },
                };
                if let ControlFlow::Break(stop) = visitor(step) {
                    cursor.store(order.len(), Ordering::Relaxed);
                    return ControlFlow::Break(stop);
                }
            }
            ControlFlow::Continue(())
        })?;
        ControlFlow::Continue(self.report)
    }
}

impl Traversal
{
    /// Advance the traversal to the next source or fault, leaving its path in
    /// `self.path`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each path given is reached in order. A directory is walked
    ///   depth-first in byte order, reaching its directories and non-symlink
    ///   `.gandr` entries without following links found in the listing. An
    ///   explicit path may be a link; a non-directory argument is one source,
    ///   whatever its name. A path that cannot be listed, or whose kind cannot
    ///   be read, is [`Reached::Unreadable`]; a path that reached no source and
    ///   no fault is [`Reached::NoSource`] after its last entry, at that path.
    ///   Anything reached marks the path given answered. Nothing is read and
    ///   nothing is counted. Exhaustion is stable.
    /// - fails: never; a fault is reached like a source.
    /// - panics: none.
    /// - intension: lists each directory once; recursion-free, the pending
    ///   entries an explicit stack.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the walk's ordered rows observe every outcome reached
    ///   here; the late-change witness observes a listing fault reached after
    ///   discovery without losing its queued sibling.
    /// - witness: `walk::tests::a_tree_is_walked_in_order`
    /// - witness: `walk::tests::every_path_answers_in_order`
    /// - witness: `walk::tests::late_changes_preserve_pending_sources_and_exhaustion`
    #[spec(
        captures: [pending_arguments = self.arguments.len(), was_answered = self.answered == Answered::Yes],
        ensures: |ref ret| match *ret {
            Maybe::Absent(walk_step::Absent::Exhausted) => pending_arguments == 0 && self.entries.is_empty(),
            Maybe::Present(Reached::NoSource) => !was_answered || pending_arguments != 0,
            Maybe::Present(Reached::Source | Reached::Unreadable(_)) => self.answered == Answered::Yes,
        },
    )]
    fn reach(&mut self) -> Maybe<Reached, walk_step::Absent>
    {
        loop {
            let Some(entry) = self.entries.pop()
            else {
                if self.answered == Answered::Not {
                    self.answered = Answered::Yes;
                    self.path.clone_from(&self.argument);
                    return Maybe::Present(Reached::NoSource);
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
                | Entry::Argument => {
                    self.path.clone_from(&self.argument);
                    match std::fs::metadata(&self.path) {
                        | Ok(metadata) if metadata.is_dir() => {
                            if let Err(error) = self.list() {
                                self.answered = Answered::Yes;
                                return Maybe::Present(Reached::Unreadable(error));
                            }
                        },
                        | Ok(_) => {
                            self.answered = Answered::Yes;
                            return Maybe::Present(Reached::Source);
                        },
                        | Err(error) => {
                            self.answered = Answered::Yes;
                            return Maybe::Present(Reached::Unreadable(error));
                        },
                    }
                },
                | Entry::Directory(directory) => {
                    self.path = directory;
                    if let Err(error) = self.list() {
                        self.answered = Answered::Yes;
                        return Maybe::Present(Reached::Unreadable(error));
                    }
                },
                | Entry::Source(source) => {
                    self.path = source;
                    self.answered = Answered::Yes;
                    return Maybe::Present(Reached::Source);
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
    #[spec(
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
}

impl Walk
{
    /// A fault for the path last reached, counted.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the unreadable fault at the current path with the
    ///   supplied error and counts one fault, saturating.
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
    #[spec(
        captures: [
            expected_path = self.traversal.path.as_path(),
            before_faulted = usize::from(self.report.sources().faulted()),
            expected_kind = error.kind(),
            expected_os_error = error.raw_os_error(),
        ],
        ensures: |ref ret| usize::from(self.report.sources().faulted()) == before_faulted.saturating_add(1)
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
        self.report.faulted();
        Step::Fault {
            path: &self.traversal.path,
            fault: SourceFault::Unreadable(error),
        }
    }

    /// Classify, read and compose the source last reached, counted.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns either the complete source with its canonical root
    ///   and corresponding standing, or its read, grammar or composition fault.
    ///   The original path is retained and the source or fault is counted once.
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
    #[spec(
        captures: [path_bytes = self.traversal.path.as_os_str().len()],
        ensures: |ref ret| match *ret {
            Step::Source { path, root, ref composed, standing, .. } =>
                path.as_os_str().len() == path_bytes && standing == Standing::of(root, composed),
            Step::Fault { path, ref fault } => path.as_os_str().len() == path_bytes
                && !matches!(*fault, SourceFault::NoSource),
        },
    )]
    fn source(&mut self) -> Step<'_>
    {
        let root = match read_source(&self.traversal.path, &mut self.text) {
            | Ok(root) => root,
            | Err(error) => return self.unreadable(error),
        };
        let grammar = match self.grammar {
            | Ok(ref grammar) => grammar,
            | Err(ref error) => {
                self.report.faulted();
                return Step::Fault {
                    path: &self.traversal.path,
                    fault: SourceFault::Grammar(error),
                };
            },
        };
        let text = SourceText::from(self.text.as_str());
        let composed = compose(
            grammar,
            root.corpus_root(),
            text,
            self.report.lowerings_mut(),
        );
        settled(&mut self.report, &self.traversal.path, root, text, composed)
    }
}

/// The step a source composed under `root` makes, counted into `report`.
///
/// # Specification
/// - requires: `composed` is what the source at `path`, read as `text` under
///   `root`, became.
/// - ensures: a composition is a [`Step::Source`] with its standing, counted as
///   read; a fault is a [`Step::Fault`] of [`SourceFault::Compose`], counted as
///   faulted.
/// - provides: the one counting both the serial and the wider walk perform, so
///   the two cannot count a source differently.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — settled, unsettled, refused and pending sources are
///   counted under their roots by the walk witnesses at both widths.
/// - witness: `walk::tests::each_root_stands_its_sources`
/// - witness: `walk::tests::a_tree_is_walked_in_order`
#[spec(
    captures: [
        read_before = usize::from(report.sources().read()),
        faulted_before = usize::from(report.sources().faulted()),
    ],
    ensures: |ref ret| match *ret {
        Step::Source { root, ref composed, standing, .. } => standing == Standing::of(root, composed)
            && usize::from(report.sources().read()) == read_before.saturating_add(1)
            && usize::from(report.sources().faulted()) == faulted_before,
        Step::Fault { ref fault, .. } => matches!(*fault, SourceFault::Compose(_))
            && usize::from(report.sources().read()) == read_before
            && usize::from(report.sources().faulted()) == faulted_before.saturating_add(1),
    },
)]
fn settled<'step>(
    report: &mut RunReport,
    path: &'step Path,
    root: SourceRoot,
    text: SourceText<'step>,
    composed: Result<Composed<'step>, ComposeFault<'step>>,
) -> Step<'step>
{
    match composed {
        | Ok(composed) => {
            let standing = Standing::of(root, &composed);
            report.read(root, &composed, standing);
            Step::Source {
                path,
                root,
                text,
                composed,
                standing,
            }
        },
        | Err(fault) => {
            report.faulted();
            Step::Fault {
                path,
                fault: SourceFault::Compose(fault),
            }
        },
    }
}

/// Classify, read, parse and lower the source at `path`, its text kept in
/// `text`: one pool thread's share of a wider walk.
///
/// # Specification
/// - requires: `text` is the empty slot for this source alone.
/// - ensures: a source that cannot be classified or read is
///   [`Forked::Unreadable`]; otherwise its text fills `text` and it is
///   [`Forked::Lowered`] with its root, what [`lower_source`] made of it and
///   the lowerings that took, exactly as the serial walk's composition would
///   lower it.
/// - fails: never; a fault is carried in the answer.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the corpus at several widths composes equal to the serial
///   walk source by source, and the fault trees read their unreadable sources
///   alike at both widths.
/// - witness: `corpus::corpus::every_width_composes_the_corpus_alike`
/// - witness: `walk::tests::every_path_answers_in_order`
#[spec(ensures: |ref ret| match *ret {
    Forked::Lowered { text: lowered, lowerings, .. } => text.get().is_some_and(|held| lowered == SourceText::from(held.as_str()))
        && usize::from(lowerings) <= 1,
    Forked::Unreadable(_) => true,
})]
fn fork<'text>(
    grammar: &Pbg,
    path: &Path,
    text: &'text OnceLock<String>,
) -> Forked<'text>
{
    let mut read = String::new();
    match read_source(path, &mut read) {
        | Err(error) => Forked::Unreadable(error),
        | Ok(root) => {
            let text = SourceText::from(text.get_or_init(|| read).as_str());
            let mut lowerings = LoweringCount::default();
            let lowering = lower_source(grammar, text, &mut lowerings);
            Forked::Lowered {
                root,
                text,
                lowering,
                lowerings,
            }
        },
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
#[spec(
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
#[spec(
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
    use core::convert::Infallible;
    use core::num::NonZeroUsize;
    use core::ops::ControlFlow;
    use std::io;
    use std::path::Path;
    use std::path::PathBuf;

    use anodized::spec;
    use gandr_surface_syntax::SourceText;
    use quenchant_shape::shape::Maybe;

    use super::SourceFault;
    use super::Standing;
    use super::Step;
    use super::Walk;
    use crate::report::RunReport;
    use crate::report::SourceCount;
    use crate::root::SourceRoot;
    use crate::root::classify;
    use crate::width::Threads;
    use crate::width::Width;

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
        #[spec(ensures: |ref ret|
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
        #[spec(requires: relative.is_relative() && relative.file_name().is_some()
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
        #[spec(ensures: self.0.try_exists().is_ok_and(|exists| !exists))]
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
        #[spec(ensures: |ret| match (step, ret) {
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
    #[spec(ensures: |ref ret| {
        let sources = ret.0.iter().filter(|row| matches!(row.1, Seen::Source(_))).count();
        ret.1.traversal.arguments.is_empty() && ret.1.traversal.entries.is_empty()
            && ret.1.traversal.answered == super::Answered::Yes
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

    /// The serial walk and three threads: the widths a visit is compared at.
    ///
    /// # Specification
    /// trivial.
    fn widths() -> [Width; 2]
    {
        [
            Width::SERIAL,
            Width::Threads(Threads::from(NonZeroUsize::MIN.saturating_add(2))),
        ]
    }

    /// Every step a visit over `paths` at `width` hands over, as
    /// `(path relative to base, seen)`, and the visit's report.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: records each step in the order handed over, strips `base`
    ///   only when it is a prefix, and returns the report the visit answers,
    ///   whose source and fault counts agree with the recorded rows.
    /// - fails: never; source faults are recorded as rows.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the rows and report are compared whole against the
    ///   serial walk's over nested, empty, missing and rooted inputs, which
    ///   detects a lost, doubled, reordered or differently counted step.
    /// - witness: `walk::tests::a_tree_is_walked_in_order`
    /// - witness: `walk::tests::every_path_answers_in_order`
    /// - witness: `walk::tests::each_root_stands_its_sources`
    #[spec(ensures: |ref ret| {
        let sources = ret.0.iter().filter(|row| matches!(row.1, Seen::Source(_))).count();
        sources == usize::from(ret.1.sources().read())
            && ret.0.len().checked_sub(sources) == Some(usize::from(ret.1.sources().faulted()))
    })]
    fn visited(
        base: &Path,
        paths: Vec<PathBuf>,
        width: Width,
    ) -> (Vec<(PathBuf, Seen)>, RunReport)
    {
        let mut seen = Vec::new();
        let ControlFlow::Continue(report) =
            Walk::new(paths).visit(width, |step| -> ControlFlow<Infallible> {
                let kind = Seen::from(&step);
                let path = match step {
                    | Step::Source { path, .. } | Step::Fault { path, .. } => path,
                };
                seen.push((path.strip_prefix(base).unwrap_or(path).to_path_buf(), kind));
                ControlFlow::Continue(())
            });
        (seen, report)
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

        let paths = vec![scratch.0.join("tree"), scratch.0.join("named.source")];
        let (seen, walk) = steps(&scratch.0, paths.clone());
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
        for width in widths() {
            assert_eq!(
                visited(&scratch.0, paths.clone(), width),
                (seen.clone(), report),
                "a visit at {width:?} hands over the serial walk's steps and counts"
            );
        }
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
        let paths = vec![
            scratch.0.join("absent.gandr"),
            scratch.0.join("empty"),
            scratch.0.join("one.gandr"),
            scratch.0.join("absent"),
        ];
        let (seen, walk) = steps(&scratch.0, paths.clone());
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
        for width in widths() {
            assert_eq!(
                visited(&scratch.0, paths.clone(), width),
                (seen.clone(), walk.report()),
                "a visit at {width:?} answers every path in the serial walk's order"
            );
        }
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
        for width in widths() {
            assert_eq!(
                visited(&scratch.0, vec![scratch.0.join("corpus")], width),
                (seen.clone(), report),
                "a visit at {width:?} stands each source under its root"
            );
        }
    }

    #[test]
    fn a_stopped_visit_hands_over_nothing_more()
    {
        let scratch = Scratch::new(Path::new("stopped"));
        scratch.file(Path::new("a.gandr"), SourceText::from("def a = 1 ;"));
        scratch.file(Path::new("b.gandr"), SourceText::from("def b = 2 ;"));
        scratch.file(Path::new("c.gandr"), SourceText::from("def c = 3 ;"));
        for width in widths() {
            let mut handed = Vec::new();
            let stopped = Walk::new(vec![scratch.0.clone()]).visit(width, |step| {
                let path = match step {
                    | Step::Source { path, .. } | Step::Fault { path, .. } => path,
                };
                handed.push(path.strip_prefix(&scratch.0).unwrap_or(path).to_path_buf());
                if handed.len() == 2 {
                    ControlFlow::Break(path.to_path_buf())
                }
                else {
                    ControlFlow::Continue(())
                }
            });
            assert_eq!(
                stopped,
                ControlFlow::Break(scratch.0.join("b.gandr")),
                "the visit answers the visitor's stop at {width:?}"
            );
            assert_eq!(
                handed,
                vec![PathBuf::from("a.gandr"), PathBuf::from("b.gandr")],
                "no step follows the stop at {width:?}"
            );
        }
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
