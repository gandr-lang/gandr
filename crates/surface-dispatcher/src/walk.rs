//! The walk: a verb's paths, read, grouped by import and composed in order.
//!
//! # Every source is read before any is judged
//!
//! [`Walk::visit`] first reaches every path it was given and reads every source
//! they name, then groups the sources into the import-connected components
//! they make (the `component` module), lowers and judges each component once,
//! and hands each source to its visitor in walk order, the component's verdict
//! projected onto it. A component needs every member read before any is
//! judged — an importer may be reached before the source it imports or after
//! it — so the walk holds every source's text until the visit ends, and each
//! component's verdicts until its last source is handed over. The report
//! accumulates as the walk goes, so it is complete once the visit ends,
//! whatever the visitor did with each step.
//!
//! The alternative was a stepped walk holding one source at a time, which can
//! judge an importer only over its own import closure, lowering and checking
//! each source it imports once more per importer. The choice reverses for a
//! tree whose text does not fit in memory, when the walk reads the import
//! graph first and each component's texts again when it lowers it.
//!
//! # Every path answers
//!
//! A path that cannot be read faults, and so does a path that names no
//! source: a directory holding no `.gandr` file, which would otherwise pass
//! as a settled run over nothing. The walk continues past a fault, so one run
//! reports every path that faults.
//!
//! # Components fork; judgement keeps walk order
//!
//! At a width above one, `Walk::visit` forks by component: one job per
//! component, its text's byte length the estimate, the jobs sorted largest
//! first behind one atomic cursor that each thread — the calling thread among
//! them — advances to take the next. A job parses and lowers its component
//! into an arena of its own, so no component's state is shared; the grammar is
//! the one value every thread reads. The calling thread judges, readmits,
//! settles and counts each component when the first of its sources comes up in
//! walk order and its lowering has arrived over a channel, holds a lowering
//! that arrives early until its turn, and takes a job itself whenever the next
//! component in walk order has not arrived. A visitor that stops the visit
//! stops the cursor, so no thread starts another component. Every count,
//! verdict and printed byte is the serial visit's: the walk tests compare rows
//! and reports at widths one and three, the corpus suite compares every
//! composition at two, seven and the host's width with the serial visit's, and
//! the driver's suite compares both streams and the exit at several widths,
//! set by flag and by environment. `Width::SERIAL` is that serial visit, which
//! lowers each component on the calling thread when its first source comes up,
//! and the reference every wider visit is tested against.
//!
//! **Largest first.** A component is the unit because it is one parse and one
//! lowering, and the largest bounds the tail: started first, it ends while the
//! small ones fill the other threads, so the last thread to finish ends on a
//! small one. The alternatives were the walk's own order, which can leave the
//! largest for last, and recursive halving of the list, which balances counts
//! rather than bytes. The estimate reverses to a measured cost per component
//! if byte length stops predicting it.
//!
//! **Judgement stays in walk order.** The checker, the kernel's readmission and
//! the settle comparison run on the calling thread, one component after
//! another, while the pool lowers the components after it. Each component is
//! judged alone, so judging on the pool would give the same verdicts, but a
//! checker that consults what earlier components admitted needs that order,
//! and judgement is under a twentieth of a corpus walk. The choice reverses if
//! judgement grows into the tail of a wide visit, when the components whose
//! judgement depends on no other move onto the pool.
//!
//! **Scoped threads, not `rayon`.** The pool is `std::thread::scope` and the
//! cursor. The alternative was `rayon`; on the corpus, with the same cursor and
//! the same in-order consumer, it measures the same as scoped threads, since
//! there is nothing for work stealing to steal from one shared cursor. The
//! choice reverses when the dispatcher forks below the component, by source,
//! form or declaration, where nested work wants a stealing pool, or when a
//! long-lived process — the session, the language server — keeps a pool warm
//! across runs. The stage verb (the `stage` module) meets the first condition
//! and runs on `rayon`; the walk forks by component alone, so it keeps scoped
//! threads.

use alloc::collections::BTreeMap;
use alloc::collections::btree_map;
use core::cell::OnceCell;
use core::cmp::Reverse;
use core::ops::ControlFlow;
use core::sync::atomic::AtomicUsize;
use core::sync::atomic::Ordering;
use std::ffi::OsStr;
use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
use gandr_core_checker::HostGrant;
use gandr_surface_corpus::CorpusRoot;
use gandr_surface_corpus::Settlement;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::PbgError;
use gandr_surface_grammar::built_in;
use gandr_surface_parser::parse;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::component::Component;
use crate::component::Confirmation;
use crate::component::Given;
use crate::component::Grouped;
use crate::component::ParsedBytes;
use crate::component::Reading;
use crate::component::group;
use crate::compose::ComposeFault;
use crate::compose::Composed;
use crate::compose::Lowering;
use crate::compose::LoweringCount;
use crate::compose::judge_component;
use crate::compose::lower_parsed_unit;
use crate::compose::lower_unit_source;
use crate::report::RunReport;
use crate::root::SourceRoot;
use crate::root::classify;
use crate::width::Width;

quenchant_shape::reason_enum! {
    /// Why a traversal reaches nothing further.
    pub mod walk_step {
        /// The reason nothing is reached.
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
    /// - hypothesis: L3 — whole refusals, refused forms, a code the IL never
    ///   carries, ordinary declarations and an owed declaration have exact
    ///   standings under the three roots. These finite cases separate root
    ///   precedence and settlement, not every possible composition or
    ///   filesystem classification.
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
            (SourceRoot::Pending, &Composed::Refused(_)) => Self::Pending,
            (SourceRoot::Pending, &Composed::Settled { ref unstatable, .. }) => {
                if unstatable.is_empty() {
                    Self::Lowered
                }
                else {
                    Self::Pending
                }
            },
            (SourceRoot::Strict | SourceRoot::Fixture, &Composed::Refused(_)) => Self::Refused,
            (SourceRoot::Strict | SourceRoot::Fixture, &Composed::Settled { ref report, .. }) => {
                match report.tally().settlement() {
                    Settlement::Settled => Self::Settled,
                    Settlement::Unsettled => Self::Unsettled,
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
            Self::Unreadable(ref error) => write!(f, "unreadable: {error}"),
            Self::NoSource => f.write_str("names no `.gandr` source"),
            Self::Grammar(error) => write!(f, "the built-in grammar did not build: {error}"),
            Self::Compose(ref fault) => fault.fmt(f),
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
        /// The text every span of `composed` is measured against: the text
        /// of the source's component up to the end of the source's own, which
        /// stands last.
        text: SourceText<'walk>,
        /// Where the source's own text starts in `text`.
        base: ByteOffset,
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

/// A walk over the paths a verb was given, visiting its sources in order.
#[derive(Debug)]
pub struct Walk
{
    /// The grammar every source is parsed under, built once per walk.
    grammar: Result<Pbg, PbgError>,
    /// Where the walk is among the paths it was given.
    traversal: Traversal,
    /// What the walk has counted so far.
    report: RunReport,
    /// The host operations every source's held capabilities are bounded by.
    grant: HostGrant,
}

/// Where a walk is among the paths it was given.
#[derive(Debug)]
pub struct Traversal
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
pub enum Reached
{
    /// A source to classify, read and compose.
    Source,
    /// A path that could not be listed, or whose kind could not be read.
    Unreadable(std::io::Error),
    /// The path given yielded no source and no fault.
    NoSource,
}

/// What one path reached came to once read.
#[derive(Debug)]
enum Slot
{
    /// A source read, by its position among the sources given to `group`.
    Given
    {
        /// Its position among the sources given.
        given: usize,
        /// The root its canonical path sits under.
        root: SourceRoot,
    },
    /// A path that could not be listed, classified or read.
    Unreadable(std::io::Error),
    /// The path given yielded no source and no fault.
    NoSource,
}

/// What a thread made of one component: its lowering and the sources it
/// lowered.
#[derive(Debug)]
struct Job<'text>
{
    /// What parsing and lowering the component came to; `None` when its parse
    /// does not confirm how [`group`] read its imports
    /// ([`Component::confirms`]), and it is grouped again ([`regroup`]).
    lowering: Option<Result<Lowering<'text>, ComposeFault<'text>>>,
    /// The sources lowered: the component's, unless its parse failed or did
    /// not confirm its reading.
    lowerings: LoweringCount,
    /// The bytes parsed: the component's text.
    parsed: ParsedBytes,
}

/// One source's composition, held until the last step standing at it is
/// handed over.
#[derive(Clone, Debug)]
struct Held<'text>
{
    /// What the source composed to.
    composed: Result<Composed<'text>, ComposeFault<'text>>,
    /// Its unit's text, up to the source's own end.
    text: SourceText<'text>,
    /// Where the source's own bytes start in `text`.
    start: ByteOffset,
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
    ///   tree created after construction is read when the walk is visited.
    ///   These distinguish lost paths and eager reading; they do not measure
    ///   grammar construction or arbitrary filesystem races.
    /// - witness: `walk::tests::every_path_answers_in_order`
    /// - witness: `walk::tests::a_tree_is_read_when_visited`
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
        Self {
            grammar: built_in(),
            traversal: Traversal::new(paths),
            report: RunReport::default(),
            grant: HostGrant::UNBOUNDED,
        }
    }

    /// The walk judging every source's held capabilities within `grant`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the walk, unchanged but for its grant, which every source it
    ///   composes is judged under; a walk is under no grant until given one.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a source declaring a held capability beyond the grant
    ///   is refused by name under the grant, at one width and several, and owed
    ///   under none.
    /// - witness: `walk::tests::a_grant_bounds_every_source_the_walk_judges`
    #[inline]
    #[must_use]
    #[spec(captures: [expected = grant.clone()], ensures: |ref ret| ret.grant == expected)]
    pub fn granting(
        mut self,
        grant: HostGrant,
    ) -> Self
    {
        self.grant = grant;
        self
    }

    /// Hand every step of the walk to `visitor`, in walk order, lowering the
    /// components on `width` threads, and answer the walk's report.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: every path given is reached in order. A directory is walked
    ///   depth-first in byte order, reaching its directories and non-symlink
    ///   `.gandr` entries without following links found in the listing. An
    ///   explicit path may be a link; a non-directory argument is one source,
    ///   whatever its name. Every source reached is classified by its canonical
    ///   path and read before any is judged, and the sources are grouped into
    ///   the import-connected components they and the sources they import make
    ///   (`component::group`). Each component is parsed and lowered once,
    ///   counting each of its sources once among the lowerings, and judged,
    ///   settled and admitted once (`compose::judge_component`) when the first
    ///   of its sources comes up in walk order. `visitor` receives one step per
    ///   path reached, in walk order, each counted into the report before it is
    ///   handed over: a source's step names it by the path the walk reached it
    ///   through, carries the component's verdict projected onto it, and
    ///   measures its spans against its component's text up to the end of its
    ///   own, which starts at its base; a path that cannot be listed or read is
    ///   a [`SourceFault::Unreadable`] step; a path that yields no source and
    ///   no fault is a [`SourceFault::NoSource`] step after its last entry; a
    ///   grammar that did not build faults every source read. The answer is
    ///   `Continue` with the run's report, or the first `Break` `visitor`
    ///   returns, after which no step is handed over or counted and no thread
    ///   starts another component. As many threads as the width answers, never
    ///   more than the components, the calling thread among them, lower the
    ///   components, each taking the largest component by bytes that no thread
    ///   has taken; the calling thread meanwhile judges and hands over the
    ///   sources in walk order, and lowers a component itself whenever the next
    ///   one in walk order has not arrived. One component is lowered on the
    ///   calling thread alone, and the host is asked its width only when there
    ///   are two or more; at [`Width::SERIAL`] the calling thread lowers each
    ///   component when its first source comes up. A thread the host refuses to
    ///   start leaves its components to the others.
    /// - provides: the pass `check` and `test` run, at the width the driver
    ///   chose.
    /// - fails: never; every fault is a step, and the walk continues past it.
    /// - panics: only by propagating a panic of `visitor` or of a pool thread,
    ///   once every thread has stopped.
    /// - executable: none — the steps are handed to an opaque visitor; the
    ///   witnesses compare rows, reports and compositions across widths.
    /// - intension: lists each directory once and reads each source once,
    ///   recursion-free, the pending entries an explicit stack; holds every
    ///   source's text until the visit ends, each lowering until its component
    ///   is judged and each component's verdicts until its last source is
    ///   handed over.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — trees mixing nested sources, unreadable paths, empty
    ///   directories and every root yield the same rows and reports at widths
    ///   one and three; the corpus yields equal compositions, step by step, at
    ///   every width tried; a diamond of importers is lowered once and each
    ///   source reports its own declarations. A single source and a stopped
    ///   visit are observed exactly. Thread interleavings beyond those runs,
    ///   and filesystem changes during a visit, are outside these witnesses.
    /// - witness: `walk::tests::a_tree_is_walked_in_order`
    /// - witness: `walk::tests::every_path_answers_in_order`
    /// - witness: `walk::tests::each_root_stands_its_sources`
    /// - witness: `walk::tests::a_stopped_visit_hands_over_nothing_more`
    /// - witness: `walk::tests::an_importer_is_judged_over_its_sibling`
    /// - witness: `tests::corpus::sweeps::every_width_composes_the_corpus_alike`
    #[inline]
    pub fn visit<Stop, Visitor>(
        mut self,
        width: Width,
        mut visitor: Visitor,
    ) -> ControlFlow<Stop, RunReport>
    where
        Visitor: FnMut(Step<'_>) -> ControlFlow<Stop>,
    {
        let mut paths = Vec::new();
        let mut slots = Vec::new();
        let mut given = Vec::new();
        while let Maybe::Present(reached) = self.traversal.reach() {
            let path = self.traversal.take_path();
            slots.push(match reached {
                Reached::NoSource => Slot::NoSource,
                Reached::Unreadable(error) => Slot::Unreadable(error),
                Reached::Source => match read_given(&path) {
                    Ok(source) => {
                        let root = source.root;
                        given.push(source);
                        Slot::Given {
                            given: given.len().saturating_sub(1),
                            root,
                        }
                    },
                    Err(error) => Slot::Unreadable(error),
                },
            });
            paths.push(path);
        }
        let grammar = match self.grammar {
            Ok(ref grammar) => grammar,
            Err(ref error) => {
                for (path, slot) in paths.iter().zip(slots) {
                    self.report.faulted();
                    let fault = match slot {
                        Slot::NoSource => SourceFault::NoSource,
                        Slot::Unreadable(unread) => SourceFault::Unreadable(unread),
                        Slot::Given { .. } => SourceFault::Grammar(error),
                    };
                    visitor(Step::Fault { path, fault })?;
                }
                return ControlFlow::Continue(self.report);
            },
        };
        let grant = &self.grant;
        let grouped = group(grammar, given, Reading::ImportForms);
        self.report.parsed_mut().absorb(grouped.parsed);
        // Each component its parse did not confirm, grouped again once its
        // turn comes.
        let regrouped: Vec<OnceCell<Grouped>> =
            grouped.components.iter().map(|_| OnceCell::new()).collect();
        // How many steps still to come stand at each source of each
        // component: its compositions are held until the last is handed over.
        let mut owed: Vec<Vec<usize>> = grouped
            .components
            .iter()
            .map(|component| vec![0_usize; component.members.len()])
            .collect();
        for placed in &grouped.placed {
            if let Some(count) = owed
                .get_mut(placed.component)
                .and_then(|members| members.get_mut(placed.member))
            {
                *count = count.saturating_add(1);
            }
        }
        let mut order: Vec<(Reverse<usize>, usize)> = grouped
            .components
            .iter()
            .enumerate()
            .map(|(position, component)| (Reverse(component.text.len()), position))
            .collect();
        order.sort_unstable();
        let threads = match order.len() {
            0 | 1 => 1,
            components => {
                usize::from(core::num::NonZeroUsize::from(width.threads())).min(components)
            },
        };
        let cursor = AtomicUsize::new(0);
        // The largest component no thread has taken, lowered.
        let take = || {
            let &(_, position) = order.get(cursor.fetch_add(1, Ordering::Relaxed))?;
            Some((position, lower(grammar, grouped.components.get(position)?)))
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
            // Each judged component's compositions, by source, taken as the
            // last step standing at each is handed over.
            let mut judged: BTreeMap<usize, Vec<Option<Held<'_>>>> = BTreeMap::new();
            for (path, slot) in paths.iter().zip(slots) {
                let step = match slot {
                    Slot::NoSource => {
                        self.report.faulted();
                        Step::Fault {
                            path,
                            fault: SourceFault::NoSource,
                        }
                    },
                    Slot::Unreadable(error) => {
                        self.report.faulted();
                        Step::Fault {
                            path,
                            fault: SourceFault::Unreadable(error),
                        }
                    },
                    Slot::Given { given, root } => {
                        let Some(&placed) = grouped.placed.get(given)
                        else {
                            continue;
                        };
                        let Some(component) = grouped.components.get(placed.component)
                        else {
                            continue;
                        };
                        if let btree_map::Entry::Vacant(unjudged) = judged.entry(placed.component) {
                            let job = loop {
                                if pool == 0 {
                                    break lower(grammar, component);
                                }
                                if let Some(job) = early.remove(&placed.component) {
                                    break job;
                                }
                                if let Ok((arrived, job)) = receiver.try_recv() {
                                    early.insert(arrived, job);
                                    continue;
                                }
                                if let Some((taken, job)) = take() {
                                    if taken == placed.component {
                                        break job;
                                    }
                                    early.insert(taken, job);
                                    continue;
                                }
                                match receiver.recv() {
                                    Ok((arrived, job)) => {
                                        early.insert(arrived, job);
                                    },
                                    // Every pool thread has stopped without
                                    // it: one panicked, and the scope will say
                                    // so.
                                    Err(_) => break lower(grammar, component),
                                }
                            };
                            self.report.lowerings_mut().absorb(job.lowerings);
                            self.report.parsed_mut().absorb(job.parsed);
                            let held = if let Some(lowering) = job.lowering {
                                judge(
                                    &mut self.report,
                                    (root.corpus_root(), grant),
                                    component,
                                    lowering,
                                )
                                .into_iter()
                                .map(Some)
                                .collect()
                            }
                            else {
                                let Some(again) = regrouped
                                    .get(placed.component)
                                    .map(|cell| cell.get_or_init(|| regroup(grammar, component)))
                                else {
                                    continue;
                                };
                                judge_regrouped(
                                    &mut self.report,
                                    grammar,
                                    (root.corpus_root(), grant),
                                    again,
                                )
                            };
                            unjudged.insert(held);
                        }
                        let Some(remaining) = owed
                            .get_mut(placed.component)
                            .and_then(|members| members.get_mut(placed.member))
                        else {
                            continue;
                        };
                        *remaining = remaining.saturating_sub(1);
                        let last = *remaining == 0;
                        let held = judged
                            .get_mut(&placed.component)
                            .and_then(|held| held.get_mut(placed.member))
                            .and_then(|held| if last { held.take() } else { held.clone() });
                        if owed
                            .get(placed.component)
                            .is_some_and(|members| members.iter().all(|&count| count == 0))
                        {
                            let _handed = judged.remove(&placed.component);
                        }
                        let Some(held) = held
                        else {
                            continue;
                        };
                        settled(
                            &mut self.report,
                            path,
                            root,
                            (held.text, held.start),
                            held.composed,
                        )
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
    /// A traversal of `paths`, in the order given, nothing yet reached.
    ///
    /// # Specification
    /// trivial.
    pub fn new(paths: Vec<PathBuf>) -> Self
    {
        let mut arguments = paths;
        arguments.reverse();
        Self {
            arguments,
            argument: PathBuf::new(),
            answered: Answered::Yes,
            entries: Vec::new(),
            path: PathBuf::new(),
        }
    }

    /// The source or directory last reached.
    ///
    /// # Specification
    /// trivial.
    pub fn path(&self) -> &Path
    {
        &self.path
    }

    /// The source or directory last reached, taken, leaving an empty path.
    ///
    /// # Specification
    /// trivial.
    pub fn take_path(&mut self) -> PathBuf
    {
        core::mem::take(&mut self.path)
    }

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
    ///   here; a tree written after the walk is built is listed when it is
    ///   visited, an empty directory in it listing nothing.
    /// - witness: `walk::tests::a_tree_is_walked_in_order`
    /// - witness: `walk::tests::every_path_answers_in_order`
    /// - witness: `walk::tests::a_tree_is_read_when_visited`
    #[spec(
        captures: [pending_arguments = self.arguments.len(), was_answered = self.answered == Answered::Yes],
        ensures: |ref ret| match *ret {
            Maybe::Absent(walk_step::Absent::Exhausted) => pending_arguments == 0 && self.entries.is_empty(),
            Maybe::Present(Reached::NoSource) => !was_answered || pending_arguments != 0,
            Maybe::Present(Reached::Source | Reached::Unreadable(_)) => self.answered == Answered::Yes,
        },
    )]
    pub fn reach(&mut self) -> Maybe<Reached, walk_step::Absent>
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
                Entry::Argument => {
                    self.path.clone_from(&self.argument);
                    match std::fs::metadata(&self.path) {
                        Ok(metadata) if metadata.is_dir() => {
                            if let Err(error) = self.list() {
                                self.answered = Answered::Yes;
                                return Maybe::Present(Reached::Unreadable(error));
                            }
                        },
                        Ok(_) => {
                            self.answered = Answered::Yes;
                            return Maybe::Present(Reached::Source);
                        },
                        Err(error) => {
                            self.answered = Answered::Yes;
                            return Maybe::Present(Reached::Unreadable(error));
                        },
                    }
                },
                Entry::Directory(directory) => {
                    self.path = directory;
                    if let Err(error) = self.list() {
                        self.answered = Answered::Yes;
                        return Maybe::Present(Reached::Unreadable(error));
                    }
                },
                Entry::Source(source) => {
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
    /// - hypothesis: L3 — nested ordered files, an empty directory and an
    ///   ignored link observe filtering and stack order; errors partway through
    ///   directory iteration are outside these witnesses.
    /// - witness: `walk::tests::a_tree_is_walked_in_order`
    /// - witness: `walk::tests::a_tree_is_read_when_visited`
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

/// The step a source composed under `root` makes, counted into `report`.
///
/// # Specification
/// - requires: `composed` is what the source at `path`, read under `root`,
///   became over `text`, its own text starting at `base`.
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
    (text, base): (SourceText<'step>, ByteOffset),
    composed: Result<Composed<'step>, ComposeFault<'step>>,
) -> Step<'step>
{
    match composed {
        Ok(composed) => {
            let standing = Standing::of(root, &composed);
            report.read(root, &composed, standing);
            Step::Source {
                path,
                root,
                text,
                base,
                composed,
                standing,
            }
        },
        Err(fault) => {
            report.faulted();
            Step::Fault {
                path,
                fault: SourceFault::Compose(fault),
            }
        },
    }
}

/// Parse and lower `component` once: one thread's share of a visit.
///
/// # Specification
/// - requires: `component` was laid out by `component::group`.
/// - ensures: when the component's text parses and its tree confirms how its
///   imports were read ([`Component::confirms`]), what [`lower_parsed_unit`]
///   makes of that tree and the unit, and every source of the component
///   lowered. A text read [`Reading::Whole`] that does not parse is its
///   [`ComposeFault::Parse`], no source lowered; under
///   [`Reading::ImportForms`], a text that does not parse or does not confirm
///   comes to no lowering, no source lowered, for the walk to group again. The
///   component's text is counted parsed either way.
/// - fails: never; a fault is carried in the answer.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the corpus at several widths composes equal to the serial
///   visit source by source; a diamond's base is lowered once; an import its
///   component's parse does not read is judged as each source's own parse reads
///   it; an importer is parsed whole once.
/// - witness: `tests::corpus::sweeps::every_width_composes_the_corpus_alike`
/// - witness: `walk::tests::an_importer_is_judged_over_its_sibling`
/// - witness: `walk::tests::an_import_its_parse_does_not_read_is_grouped_again`
/// - witness: `walk::tests::an_import_parses_its_importer_once_617`
#[spec(ensures: |ref ret| usize::from(ret.lowerings) <= component.members.len()
    && usize::from(ret.parsed) == component.text.len())]
fn lower<'text>(
    grammar: &Pbg,
    component: &'text Component,
) -> Job<'text>
{
    let mut lowerings = LoweringCount::default();
    let lowering = match parse(grammar, SourceText::from(component.text.as_str())) {
        Ok(parsed) if component.confirms(grammar, parsed.tree()) == Confirmation::Confirmed => {
            Some(lower_parsed_unit(
                grammar,
                parsed,
                &component.unit,
                &mut lowerings,
            ))
        },
        Ok(_) => None,
        Err(_) if component.reading == Reading::ImportForms => None,
        Err(error) => Some(Err(ComposeFault::Parse(error))),
    };
    Job {
        lowering,
        lowerings,
        parsed: ParsedBytes::from(component.text.len()),
    }
}

/// Judge `component` from what lowering it came to, under `root` and
/// `grant`: each source's composition beside its unit's text up to the
/// source's own end and where its bytes start.
///
/// # Specification
/// - requires: `lowering` is what [`lower`] or [`lower_unit_source`] made of
///   `component`.
/// - ensures: one held composition per member, in member order: what
///   [`judge_component`] makes of a lowering, or the lowering's fault at every
///   source; `report`'s spellings advance as [`judge_component`] says.
/// - fails: never; a fault is carried in the answer.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`lower`].
/// - witness: `walk::tests::an_importer_is_judged_over_its_sibling`
/// - witness: `walk::tests::an_import_its_parse_does_not_read_is_grouped_again`
#[spec(ensures: |ref ret| ret.len() == component.members.len())]
fn judge<'text>(
    report: &mut RunReport,
    (root, grant): (CorpusRoot, &HostGrant),
    component: &'text Component,
    lowering: Result<Lowering<'text>, ComposeFault<'text>>,
) -> Vec<Held<'text>>
{
    let composed = match lowering {
        Ok(lowering) => judge_component(
            root,
            (lowering, SourceText::from(component.text.as_str())),
            grant,
            &component.members,
            report.spellings_mut(),
        ),
        Err(fault) => component
            .members
            .iter()
            .map(|_| Err(fault.clone()))
            .collect(),
    };
    composed
        .into_iter()
        .zip(&component.members)
        .map(|(composed, member)| Held {
            composed,
            text: SourceText::from(
                component
                    .text
                    .get(.. usize::from(member.end))
                    .unwrap_or_default(),
            ),
            start: member.start,
        })
        .collect()
}

/// Lower and judge each component of `again`, under `root` and `grant`, and
/// hand back each given source's held composition in the order given.
///
/// # Specification
/// - requires: `again` is what [`regroup`] made of one component.
/// - ensures: each component of `again` parsed and lowered once with
///   [`lower_unit_source`] and judged with [`judge`], its sources counted
///   lowered and its text and `again`'s grouping counted parsed into `report`;
///   one held composition per given source, in the order given, none for a
///   source no component holds.
/// - fails: never; a fault is carried in the answer.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`regroup`].
/// - witness: `walk::tests::an_import_its_parse_does_not_read_is_grouped_again`
#[spec(ensures: |ref ret| ret.len() == again.placed.len())]
fn judge_regrouped<'text>(
    report: &mut RunReport,
    grammar: &Pbg,
    (root, grant): (CorpusRoot, &HostGrant),
    again: &'text Grouped,
) -> Vec<Option<Held<'text>>>
{
    report.parsed_mut().absorb(again.parsed);
    let mut parts: Vec<Vec<Option<Held<'text>>>> = Vec::with_capacity(again.components.len());
    for part in &again.components {
        let mut lowerings = LoweringCount::default();
        let lowering = lower_unit_source(
            grammar,
            SourceText::from(part.text.as_str()),
            &part.unit,
            &mut lowerings,
        );
        report.lowerings_mut().absorb(lowerings);
        report
            .parsed_mut()
            .absorb(ParsedBytes::from(part.text.len()));
        parts.push(
            judge(report, (root, grant), part, lowering)
                .into_iter()
                .map(Some)
                .collect(),
        );
    }
    again
        .placed
        .iter()
        .map(|at| {
            parts
                .get_mut(at.component)
                .and_then(|members| members.get_mut(at.member))
                .and_then(Option::take)
        })
        .collect()
}

/// `component`'s sources grouped again, each importer's imports read from
/// its own whole parse.
///
/// # Specification
/// - requires: `component` was laid out by `component::group`.
/// - ensures: [`group`] under [`Reading::Whole`] of the component's sources, in
///   member order, each with its path, root and own text; `placed` holds each
///   member's place, in member order.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a source whose import sits inside a module, read from its
///   forms beside the base it names, is laid out alone, as [`Reading::Whole`]
///   lays it out.
/// - witness: `walk::tests::an_import_its_parse_does_not_read_is_grouped_again`
#[spec(ensures: |ref ret| ret.placed.len() == component.members.len())]
fn regroup(
    grammar: &Pbg,
    component: &Component,
) -> Grouped
{
    let given = component
        .sources
        .iter()
        .zip(&component.members)
        .map(|(source, member)| Given {
            path: source.path.clone(),
            root: source.root,
            text: String::from(
                component
                    .text
                    .get(usize::from(member.start) .. usize::from(member.end))
                    .unwrap_or_default(),
            ),
        })
        .collect();
    group(grammar, given, Reading::Whole)
}

/// Classify the source at `path` by its canonical path and read it, as a
/// source given to `component::group`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the source's canonical path, the root it sits under and its
///   complete UTF-8 text, as [`read_source`] reads them.
/// - fails: the I/O error canonicalizing or reading the path met.
/// - panics: none.
///
/// # Errors
/// The I/O error canonicalizing or reading the path met.
///
/// # Adequacy
/// - hypothesis: L3 — missing, directory and linked paths answer as
///   [`read_source`]'s witnesses observe, through the visit.
/// - witness: `walk::tests::every_path_answers_in_order`
/// - witness: `walk::tests::an_explicit_link_uses_its_target_root_and_keeps_its_path`
#[spec(ensures: |ref ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|given| given.path.is_absolute()))]
fn read_given(path: &Path) -> std::io::Result<Given>
{
    let mut text = String::new();
    let root = read_source(path, &mut text)?;
    let canonical = std::fs::canonicalize(path)?;
    Ok(Given {
        path: canonical,
        root,
        text,
    })
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
/// - witness: `walk::tests::a_tree_is_read_when_visited`
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
        Entry::Directory(ref path) | Entry::Source(ref path) => path,
        Entry::Argument => Path::new(""),
    }
}

#[cfg(test)]
pub mod tests
{
    use core::convert::Infallible;
    use core::fmt::Write as _;
    use core::num::NonZeroUsize;
    use core::ops::ControlFlow;
    use std::io;
    use std::path::Path;
    use std::path::PathBuf;

    use anodized::spec;
    use gandr_core_checker::HostGrant;
    use gandr_core_term::effect::OperationName;
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
    pub struct Scratch(PathBuf);

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
        /// - witness: `walk::tests::a_tree_is_read_when_visited`
        #[spec(ensures: |ref ret|
            std::fs::read_dir(&ret.0).is_ok_and(|mut entries| entries.next().is_none()))]
        pub fn new(test: &Path) -> Self
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

        /// The directory.
        ///
        /// # Specification
        /// trivial.
        pub fn root(&self) -> &Path
        {
            &self.0
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
        /// - witness: `walk::tests::a_tree_is_read_when_visited`
        /// - witness: `walk::tests::an_explicit_link_uses_its_target_root_and_keeps_its_path`
        #[spec(requires: relative.is_relative() && relative.file_name().is_some()
            && relative.components().all(|component|
                matches!(component, std::path::Component::Normal(_))))]
        pub fn file(
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
        /// - witness: `walk::tests::a_tree_is_read_when_visited`
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
                Step::Source { standing, .. } => Self::Source(standing),
                Step::Fault { ref fault, .. } => match *fault {
                    SourceFault::Unreadable(_) => Self::Unreadable,
                    SourceFault::NoSource => Self::NoSource,
                    SourceFault::Grammar(_) => Self::Grammar,
                    SourceFault::Compose(_) => Self::Compose,
                },
            }
        }
    }

    /// The serial visit and three threads: the widths a visit is compared at,
    /// the serial one first, as the reference.
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
    /// - hypothesis: L3 — the rows and report are compared whole across widths
    ///   over nested, empty, missing and rooted inputs, which detects a lost,
    ///   doubled, reordered or differently counted step.
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
                    Step::Source { path, .. } | Step::Fault { path, .. } => path,
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
        scratch.file(Path::new("tree/c.gandr"), SourceText::from("pure 3"));
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
        let (seen, report) = visited(&scratch.0, paths.clone(), Width::SERIAL);
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
        assert_eq!(
            report.sources().faulted(),
            SourceCount::from(0_usize),
            "no path faults"
        );
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
                "a visit at {width:?} hands over the serial visit's steps and counts"
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
        let (seen, report) = visited(&scratch.0, paths.clone(), Width::SERIAL);
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
            report.sources().faulted(),
            SourceCount::from(3_usize),
            "three faults"
        );
        assert_eq!(
            report.sources().read(),
            SourceCount::from(1_usize),
            "one source read"
        );
        for width in widths() {
            assert_eq!(
                visited(&scratch.0, paths.clone(), width),
                (seen.clone(), report),
                "a visit at {width:?} answers every path in the serial visit's order"
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
            SourceText::from("pure 3"),
        );
        scratch.file(
            Path::new("corpus/fixture/pending/outside.gandr"),
            SourceText::from("pure 3"),
        );
        scratch.file(
            Path::new("corpus/fixture/pending/lowered.gandr"),
            SourceText::from("def a = 1 ;"),
        );
        scratch.file(
            Path::new("corpus/fixture/pending/form.gandr"),
            SourceText::from(
                "def f @[a : Type] (x: a) -> -F a { return x }\ndef broken = missing ;",
            ),
        );
        scratch.file(
            Path::new("corpus/fixture/pending/coded.gandr"),
            SourceText::from("def small : Type ; def small = Integer ;"),
        );
        let (seen, report) = visited(&scratch.0, vec![scratch.0.join("corpus")], Width::SERIAL);
        assert_eq!(
            seen,
            rows(&[
                (
                    Path::new("corpus/fixture/owes.gandr"),
                    Seen::Source(Standing::Settled)
                ),
                (
                    Path::new("corpus/fixture/pending/coded.gandr"),
                    Seen::Source(Standing::Lowered)
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
            "the root each source sits under decides its standing; a code the command IL \
             never carries leaves a pending source lowered"
        );
        let sources = report.sources();
        assert_eq!(
            (sources.strict(), sources.fixture(), sources.pending()),
            (
                SourceCount::from(1_usize),
                SourceCount::from(2_usize),
                SourceCount::from(4_usize)
            ),
            "each source counted under its root"
        );
        assert_eq!(
            (sources.refused(), sources.lowered_pending()),
            (SourceCount::from(1_usize), SourceCount::from(2_usize)),
            "the fixture source refused whole, and the pending sources lowered"
        );
        assert_eq!(
            (
                usize::from(report.tally().declarations().settled()),
                usize::from(report.tally().declarations().unsettled())
            ),
            (3_usize, 1_usize),
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
    fn a_grant_bounds_every_source_the_walk_judges()
    {
        let scratch = Scratch::new(Path::new("granted"));
        scratch.file(
            Path::new("corpus/fixture/both.gandr"),
            SourceText::from("@[ owes(1) ] def fs : Cap {read, write} ;"),
        );
        scratch.file(
            Path::new("corpus/fixture/read.gandr"),
            SourceText::from("@[ owes(1) ] def reads : Cap {read} ;"),
        );
        let reading =
            HostGrant::within([&OperationName::from("read")]).expect("the host offers `read`");
        for width in widths() {
            for (grant, both) in [
                (HostGrant::UNBOUNDED, Standing::Settled),
                (reading.clone(), Standing::Unsettled),
            ] {
                let mut seen = Vec::new();
                let ControlFlow::Continue(_report) = Walk::new(vec![scratch.0.join("corpus")])
                    .granting(grant.clone())
                    .visit(width, |step| -> ControlFlow<Infallible> {
                        let kind = Seen::from(&step);
                        let path = match step {
                            Step::Source { path, .. } | Step::Fault { path, .. } => path,
                        };
                        seen.push((
                            path.strip_prefix(&scratch.0).unwrap_or(path).to_path_buf(),
                            kind,
                        ));
                        ControlFlow::Continue(())
                    });
                assert_eq!(
                    seen,
                    rows(&[
                        (Path::new("corpus/fixture/both.gandr"), Seen::Source(both)),
                        (
                            Path::new("corpus/fixture/read.gandr"),
                            Seen::Source(Standing::Settled)
                        ),
                    ]),
                    "at {width:?} under {grant:?}, a capability claiming `write` is owed \
                     only where no grant bounds it, and one within the grant stays owed"
                );
            }
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
                    Step::Source { path, .. } | Step::Fault { path, .. } => path,
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
    fn a_tree_is_read_when_visited()
    {
        let scratch = Scratch::new(Path::new("late-changes"));
        let root = scratch.0.join("strict/tree");
        let walk = Walk::new(vec![root.clone()]);
        let first = "def first = 1 ;";
        let last = "def last = 2 ;";
        scratch.file(Path::new("strict/tree/0.gandr"), SourceText::from(first));
        std::fs::create_dir_all(root.join("a")).expect("an empty directory is created");
        scratch.file(Path::new("strict/tree/b.gandr"), SourceText::from(last));

        let mut read = Vec::new();
        let ControlFlow::Continue(report) =
            walk.visit(Width::SERIAL, |step| -> ControlFlow<Infallible> {
                if let Step::Source { path, text, .. } = step {
                    read.push((
                        path.strip_prefix(&root)
                            .expect("inside the tree")
                            .to_path_buf(),
                        <&str>::from(text).to_owned(),
                    ));
                }
                ControlFlow::Continue(())
            });
        assert_eq!(
            read,
            [
                (PathBuf::from("0.gandr"), first.to_owned()),
                (PathBuf::from("b.gandr"), last.to_owned())
            ],
            "the tree written after the walk was built is read when it is visited"
        );
        assert_eq!(usize::from(report.sources().read()), 2);
        assert_eq!(usize::from(report.sources().faulted()), 0);
        assert_eq!(usize::from(report.lowerings()), 2);

        let removed = root
            .parent()
            .expect("the strict directory")
            .parent()
            .expect("the fixture root")
            .to_path_buf();
        drop(scratch);
        assert!(removed.try_exists().is_ok_and(|exists| !exists));
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
        let mut read = Vec::new();
        let ControlFlow::Continue(_report) = Walk::new(vec![alias.clone()]).visit(
            Width::SERIAL,
            |step| -> ControlFlow<Infallible> {
                if let Step::Source {
                    path,
                    root,
                    text,
                    standing,
                    ..
                } = step
                {
                    read.push((
                        path.to_path_buf(),
                        root,
                        standing,
                        <&str>::from(text).to_owned(),
                    ));
                }
                ControlFlow::Continue(())
            },
        );
        assert_eq!(
            read,
            [(
                alias,
                SourceRoot::Pending,
                Standing::Lowered,
                <&str>::from(source).to_owned()
            )],
            "an explicit symbolic link is read as its target, under its target's root"
        );
    }

    #[test]
    fn an_importer_is_judged_over_its_sibling()
    {
        let scratch = Scratch::new(Path::new("importers"));
        // The bytes of each declaration segment of a kernel artifact, in
        // admission order.
        let segments = |image: &[u8]| -> Vec<Vec<u8>> {
            let decoded =
                gandr_kernel_term::decode(image.into()).expect("the kernel's export decodes");
            let mut start = usize::from(decoded.segments().header_end());
            let mut cut = Vec::new();
            for &end in decoded.segments().declaration_ends() {
                let end = usize::from(end);
                cut.push(image.get(start .. end).unwrap_or_default().to_vec());
                start = end;
            }
            cut
        };
        let base = "@[ checks ]\ndata Point : Type {\n  Here : Point;\n}\n\n@[ checks ]\ndef here \
                    : Point ;\ndef here = Here ;\n";
        scratch.file(Path::new("fixture/base.gandr"), SourceText::from(base));
        for side in ["left", "right"] {
            scratch.file(
                Path::new(&format!("fixture/{side}.gandr")),
                SourceText::from(
                    format!(
                        "import \"./base.gandr\" ;\n\n@[ checks ]\ndef {side} : Point ;\ndef \
                         {side} = here ;\n"
                    )
                    .as_str(),
                ),
            );
        }
        // A diamond: the top reaches the base through both sides, and names
        // it too, since an import brings in its source's own declarations and
        // not what that source imports.
        scratch.file(
            Path::new("fixture/top.gandr"),
            SourceText::from(
                "import \"./left.gandr\" ;\nimport \"./right.gandr\" ;\nimport \"./base.gandr\" \
                 ;\n\n@[ checks ]\ndef top : Point ;\ndef top = left ;\n",
            ),
        );
        // A source no import joins to the diamond: a component of its own.
        scratch.file(
            Path::new("fixture/apart.gandr"),
            SourceText::from("@[ checks ]\ndef apart : Integer ;\ndef apart = 1 ;\n"),
        );
        for width in widths() {
            let mut judged = Vec::new();
            let ControlFlow::Continue(report) = Walk::new(vec![scratch.0.join("fixture")]).visit(
                width,
                |step| -> ControlFlow<Infallible> {
                    let Step::Source {
                        path,
                        text,
                        base: own,
                        composed:
                            crate::compose::Composed::Settled {
                                ref report,
                                kernel: Maybe::Present(ref kernel),
                                ..
                            },
                        standing,
                        ..
                    } = step
                    else {
                        panic!("each source is judged and admitted: {step:?}");
                    };
                    let name = path
                        .file_stem()
                        .map(|stem| stem.to_string_lossy().into_owned());
                    assert_eq!(standing, Standing::Settled, "{name:?} settles");
                    let declared: Vec<String> = report
                        .declarations()
                        .iter()
                        .map(|declaration| declaration.name().to_string())
                        .collect();
                    judged.push((
                        name.unwrap_or_default(),
                        (<&str>::from(text).to_owned(), own),
                        declared,
                        segments(kernel.as_ref()),
                    ));
                    ControlFlow::Continue(())
                },
            );
            assert_eq!(
                usize::from(report.lowerings()),
                5_usize,
                "at {width:?}, each of the five sources is lowered once, the base \
                 among them, however many import it"
            );
            let find = |wanted: &str| {
                judged
                    .iter()
                    .find(|&&(ref name, ..)| name == wanted)
                    .unwrap_or_else(|| panic!("{wanted} is walked"))
            };
            let &(_, (ref base_text, _), ref base_declared, ref base_segments) = find("base");
            assert_eq!(
                base_declared,
                &["Point", "here"],
                "the base reports its own declarations"
            );
            for side in ["left", "right", "top"] {
                let &(_, (ref text, own), ref declared, ref segments) = find(side);
                assert!(
                    text.get(.. usize::from(own))
                        .is_some_and(|before| before.starts_with(base_text.as_str())),
                    "{side} is judged after the base it imports"
                );
                assert_eq!(
                    declared,
                    &[side],
                    "{side} reports its own declaration alone"
                );
                assert_eq!(
                    segments, base_segments,
                    "{side} carries the one certificate its component was admitted with"
                );
            }
            let &(_, (ref top, _), ..) = find("top");
            assert_eq!(
                top.matches("data Point").count(),
                1_usize,
                "a base reached by two paths is laid out once"
            );
            let &(_, (ref apart, own), ref declared, ref apart_segments) = find("apart");
            assert_eq!(
                (usize::from(own), declared.as_slice(), apart_segments.len()),
                (0_usize, ["apart".to_owned()].as_slice(), 1_usize),
                "a source joined to no other is judged alone"
            );
            assert!(!apart.contains("data Point"));
        }
    }

    /// #617: an import made its importer dearer to judge by a second parse of
    /// the importer — once alone to read its imports, again inside its
    /// component — which cost 23 M of a 7 KB importer's 152 M instructions
    /// while every later phase stayed within 1 %. Two rows: a source of that
    /// size with a one-declaration sibling's text laid in front of it, and the
    /// same source importing that sibling. The importing walk parses within
    /// 2 % of the flat one's bytes; read whole, it parsed twice as many.
    #[test]
    fn an_import_parses_its_importer_once_617()
    {
        let scratch = Scratch::new(Path::new("parsed-once"));
        let floor = "/// One.\n@[ checks ]\ndata One : Type {\n  It : One;\n}\n";
        let body = (0_usize .. 150_usize).fold(String::new(), |mut body, n| {
            let _written = write!(
                body,
                "\n@[ checks ]\ndef n{n} : Integer ;\ndef n{n} = {n} ;\n"
            );
            body
        });
        scratch.file(
            Path::new("fixture/flat/flat.gandr"),
            SourceText::from(format!("{floor}\n{body}").as_str()),
        );
        scratch.file(
            Path::new("fixture/import/floor.gandr"),
            SourceText::from(floor),
        );
        scratch.file(
            Path::new("fixture/import/importer.gandr"),
            SourceText::from(format!("import \"./floor.gandr\" ;\n{body}").as_str()),
        );
        let parsed = |directory: &str| {
            let ControlFlow::Continue(report) =
                Walk::new(vec![scratch.0.join("fixture").join(directory)])
                    .visit(Width::SERIAL, |_| -> ControlFlow<Infallible> {
                        ControlFlow::Continue(())
                    });
            usize::from(report.parsed())
        };
        let (flat, importing) = (parsed("flat"), parsed("import"));
        assert!(
            flat > 7000_usize,
            "the source is the size of the issue's: {flat} bytes"
        );
        assert!(
            importing.saturating_mul(100) <= flat.saturating_mul(102),
            "the importing walk parses {importing} bytes against the flat walk's {flat}"
        );
    }

    /// #617: a walk reads an importer's imports from its import forms and
    /// confirms them on its component's parse. An import inside a module is
    /// read from the forms but written by no root: the component's parse does
    /// not confirm it, and the walk lays the sources out again as each one's
    /// own parse reads it — the nested source alone, judged over its own bytes.
    #[test]
    fn an_import_its_parse_does_not_read_is_grouped_again()
    {
        let scratch = Scratch::new(Path::new("regrouped"));
        let base = "@[ checks ]\ndef one : Integer ;\ndef one = 1 ;\n";
        let nested = "module inner {\n  import \"./base.gandr\" ;\n}\n\n@[ checks ]\ndef three : \
                      Integer ;\ndef three = 3 ;\n";
        scratch.file(Path::new("fixture/base.gandr"), SourceText::from(base));
        scratch.file(Path::new("fixture/nested.gandr"), SourceText::from(nested));
        for width in widths() {
            let mut walked = Vec::new();
            let ControlFlow::Continue(report) = Walk::new(vec![scratch.0.join("fixture")]).visit(
                width,
                |step| -> ControlFlow<Infallible> {
                    let Step::Source {
                        path, text, base, ..
                    } = step
                    else {
                        panic!("each source is judged: {step:?}");
                    };
                    walked.push((
                        path.file_name()
                            .map(|name| name.to_string_lossy().into_owned())
                            .unwrap_or_default(),
                        <&str>::from(text).to_owned(),
                        usize::from(base),
                    ));
                    ControlFlow::Continue(())
                },
            );
            assert_eq!(
                walked,
                [
                    (String::from("base.gandr"), String::from(base), 0_usize),
                    (String::from("nested.gandr"), String::from(nested), 0_usize),
                ],
                "at {width:?}, each source is judged over its own bytes alone"
            );
            assert_eq!(
                usize::from(report.lowerings()),
                2_usize,
                "at {width:?}, each source is lowered once, in the grouping its own \
                 parse reads"
            );
        }
    }

    /// #596: two members of one component that write one attributed form
    /// byte for byte — their documentation apart, which no key reads — each
    /// settle under their own expectation. Keyed by content alone, the two
    /// forms shared a key, each declaration read both `checks`, and both
    /// stated no verdict.
    #[test]
    fn one_form_in_two_members_keeps_its_own_expectation_596()
    {
        let scratch = Scratch::new(Path::new("one-form-two-members"));
        scratch.file(
            Path::new("fixture/base.gandr"),
            SourceText::from("@[ checks ]\ndata One : Type {\n  Pt : One;\n}\n"),
        );
        for (side, documentation) in [("left", "The left two."), ("right", "The right two.")] {
            scratch.file(
                Path::new(&format!("fixture/{side}.gandr")),
                SourceText::from(
                    format!(
                        "import \"./base.gandr\" ;\n\n/// {documentation}\n@[ checks ]\ndata Two \
                         : Type {{\n  L : Two;\n  R : Two;\n}}\n"
                    )
                    .as_str(),
                ),
            );
        }
        for width in widths() {
            let mut judged = Vec::new();
            let ControlFlow::Continue(report) = Walk::new(vec![scratch.0.join("fixture")]).visit(
                width,
                |step| -> ControlFlow<Infallible> {
                    let Step::Source {
                        path,
                        composed: crate::compose::Composed::Settled { ref report, .. },
                        standing,
                        ..
                    } = step
                    else {
                        panic!("each source is judged: {step:?}");
                    };
                    let name = path
                        .file_stem()
                        .map(|stem| stem.to_string_lossy().into_owned())
                        .unwrap_or_default();
                    let settlements: Vec<(String, gandr_surface_corpus::Settlement)> = report
                        .declarations()
                        .iter()
                        .map(|declaration| {
                            (declaration.name().to_string(), declaration.settlement())
                        })
                        .collect();
                    judged.push((name, standing, settlements));
                    ControlFlow::Continue(())
                },
            );
            judged.sort();
            let settled =
                |name: &str| vec![(name.to_owned(), gandr_surface_corpus::Settlement::Settled)];
            assert_eq!(
                judged,
                [
                    ("base".to_owned(), Standing::Settled, settled("One")),
                    ("left".to_owned(), Standing::Settled, settled("Two")),
                    ("right".to_owned(), Standing::Settled, settled("Two")),
                ],
                "at {width:?}, each member's `Two` settles under its own `checks`"
            );
            assert_eq!(usize::from(report.lowerings()), 3_usize);
        }
    }
}
