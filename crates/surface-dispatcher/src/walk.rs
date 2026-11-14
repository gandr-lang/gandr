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
//! # Components fork; the steps keep walk order
//!
//! At a width above one, `Walk::visit` forks by component: one job per
//! component, its text's byte length the estimate, the jobs sorted largest
//! first behind one atomic cursor that each thread — the calling thread among
//! them — advances to take the next. A job parses and lowers its component
//! into an arena of its own, then judges and readmits it, so no component's
//! state is shared. The grammar, the prelude's judged closure and its
//! readmission record are the values every thread reads. The calling thread
//! settles and counts each component when the first of its sources comes up in
//! walk order and its judgement has arrived over a channel. It holds a
//! judgement that arrives early until its turn, and it takes a job itself
//! whenever the next component in walk order has not arrived. A visitor that
//! stops the visit stops the cursor, so no thread starts another component.
//! Every count, verdict and printed byte is the serial visit's: the walk tests
//! compare rows and reports at widths one and three, the corpus suite compares
//! every composition at two, seven and the host's width with the serial
//! visit's, and the driver's suite compares both streams and the exit at
//! several widths, set by flag and by environment. `Width::SERIAL` is that
//! serial visit, which lowers and judges each component on the calling thread
//! when its first source comes up, and the reference every wider visit is
//! tested against.
//!
//! **Largest first.** A component is the unit because it is one parse and one
//! lowering, and the largest bounds the tail: started first, it ends while the
//! small ones fill the other threads, so the last thread to finish ends on a
//! small one. The alternatives were the walk's own order, which can leave the
//! largest for last, and recursive halving of the list, which balances counts
//! rather than bytes. The estimate reverses to a measured cost per component
//! if byte length stops predicting it.
//!
//! **Judgement on the pool.** The checker and the kernel's readmission run in
//! the job that lowers the component. Each component is judged alone, in a
//! kernel environment of its own, so no judgement reads another's. The
//! settle comparison, the counts and the visitor stay on the calling thread,
//! in walk order. The alternative was judgement in walk order on the calling
//! thread, which held a check of the standard library near one core: its
//! judgement was two fifths of the run. The choice reverses if a checker
//! consults what earlier components admitted, which needs the walk order.
//!
//! **On the driver's pool.** The walk hands its component jobs to the
//! driver's [`Pool`], whose workers start once per process, and keeps the
//! cursor and the in-order consumer on the calling thread. Before, the pool was
//! `std::thread::scope` threads started for each visit. On the corpus, with
//! the same cursor and the same consumer, a shared pool measured the same as
//! scoped threads, since one shared cursor leaves nothing to steal. One pool
//! held by the driver serves the walk and the stage verb, so a process starts
//! its threads once. Each helper sends a stop when it ends, by its return or
//! by a panic, so the consumer knows when no helper can send a judgement. The
//! choice reverses if the walk measures slower on the shared pool than on
//! threads of its own.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::collections::btree_map;
use alloc::sync::Arc;
use core::cmp::Reverse;
use core::ops::ControlFlow;
use core::sync::atomic::AtomicUsize;
use core::sync::atomic::Ordering;
use std::ffi::OsStr;
use std::path::Path;
use std::path::PathBuf;
use std::sync::OnceLock;

use anodized::spec;
use gandr_core_checker::HostGrant;
use gandr_surface_corpus::CorpusRoot;
use gandr_surface_corpus::Settlement;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::PbgError;
use gandr_surface_grammar::built_in;
use gandr_surface_lowering::ClosureLowering;
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
use crate::component::Unshadowed;
use crate::component::group;
use crate::compose::Admission;
use crate::compose::Checking;
use crate::compose::ComposeFault;
use crate::compose::Composed;
use crate::compose::JudgedClosure;
use crate::compose::Keeping;
use crate::compose::Lowering;
use crate::compose::LoweringCount;
use crate::compose::Positioning;
use crate::compose::SpellingCount;
use crate::compose::judge_component;
use crate::compose::kept;
use crate::compose::lower_onto_closure;
use crate::compose::lower_parsed_unit;
use crate::compose::lower_prelude;
use crate::compose::lower_unit_source;
use crate::engine::Engine;
use crate::entry::report::RunReport;
use crate::entry::report::SourceCount;
use crate::pool::Helped;
use crate::pool::Pool;
use crate::reader::Reader;
use crate::root::Descent;
use crate::root::SourceRoot;
use crate::root::classify;
use crate::root::descent;

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
    /// - witness: `tests::walk::each_root_stands_its_sources`
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
    grammar: Result<Arc<Pbg>, PbgError>,
    /// Where the walk is among the paths it was given.
    traversal: Traversal,
    /// What the walk has counted so far.
    report: RunReport,
    /// The host operations every source's held capabilities are bounded by.
    grant: HostGrant,
    /// The reader every source of the walk is read through.
    reader: Reader,
    /// Whether each admission records where each declaration stands in its
    /// artifact, which a measure reads.
    positioning: Positioning,
}

/// Where a walk is among the paths it was given.
#[derive(Debug)]
pub struct Traversal
{
    /// The paths not yet started, the next on top.
    arguments: Vec<PathBuf>,
    /// How many paths were given.
    count: usize,
    /// Each path given, canonical, in the order given, or `None` for one that
    /// does not canonicalize; read when the first path starts, so a tree
    /// written after the traversal is built is read as it stands then.
    given: Vec<Option<PathBuf>>,
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

/// What a thread made of one component: its lowering, how it is checked, and
/// the sources it lowered.
#[derive(Debug)]
struct Job<'text>
{
    /// What parsing and lowering the component came to; `None` when its parse
    /// does not confirm how [`group`] read its imports
    /// ([`Component::confirms`]), and it is grouped again ([`regroup`]).
    lowering: Option<Result<Lowering<'text>, ComposeFault<'text>>>,
    /// How the lowering is checked: after the walk's judged prelude when it
    /// was lowered onto it, whole otherwise.
    checking: Checking<'text>,
    /// The sources lowered: the component's, unless its parse failed or did
    /// not confirm its reading.
    lowerings: LoweringCount,
    /// The bytes parsed: the component's own, past the prelude, when it was
    /// laid after the walk's prelude; its whole text otherwise.
    parsed: ParsedBytes,
}

/// The work one component's job counts: the sources it lowered, the bytes it
/// parsed and the spelling passes it made. The calling thread adds it to the
/// run's report when the component's first source comes up in walk order.
#[derive(Clone, Copy, Debug, Default)]
struct Work
{
    /// The sources lowered.
    lowerings: LoweringCount,
    /// The bytes parsed.
    parsed: ParsedBytes,
    /// The spelling passes made.
    spellings: SpellingCount,
}

/// What a thread made of one component: the held composition of each of its
/// sources, in member order, and the work it counted.
#[derive(Debug)]
struct Judgement<'text>
{
    /// Each source's composition, in member order: none for a source that no
    /// part of a regrouping holds.
    held: Vec<Option<Held<'text>>>,
    /// The work that the lowering and the judgement counted.
    work: Work,
}

/// The prelude every component lays first, lowered once per walk and its
/// declarations judged once under each root a component is judged under:
/// each component is parsed past it, lowered onto its judged arena and
/// judged after it, so the prelude is parsed, lowered and judged once per walk
/// rather than once per component (#2331).
///
/// - Choice: the closure an editor holds for a document's imports
///   ([`lower_closure`](crate::compose::lower_closure), [`JudgedClosure`],
///   [`lower_onto_closure`]), held for the prelude alone, which every
///   component's unit begins with whatever it imports.
/// - Alternatives: a closure per component's whole import closure, which two
///   components share only when they import alike; a cache across walks keyed
///   by the grammar and the prelude's text, which a process walking once does
///   not need.
/// - Reversal: a component's own sources costing less to judge whole than to
///   resume, which the corpus walk's wall time measures.
struct Prelude
{
    /// The prelude's lowering: `None` when its text is not held as a closure.
    lowering: Option<Arc<ClosureLowering>>,
    /// The grant every component is judged under.
    grant: HostGrant,
    /// Its declarations judged and settled under the strict root, made the
    /// first time a component under it is lowered.
    strict: OnceLock<Option<JudgedClosure>>,
    /// Its declarations judged and settled under the fixture root, likewise.
    fixture: OnceLock<Option<JudgedClosure>>,
}

impl Prelude
{
    /// The prelude laid before no source, lowered as a closure under `grammar`
    /// when one is given, its judgements under `grant` not yet made.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: with `grammar`, the prelude's text and the newline after it
    ///   lowered as [`lower_prelude`] lowers it, `None` when that closure is
    ///   not held; without one, no lowering. No judgement is made.
    /// - provides: what every component of a walk is lowered onto and judged
    ///   after, made once.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a walk of several components parses the prelude once.
    /// - witness: `tests::walk::a_walk_parses_the_prelude_once_for_every_component_2331`
    #[spec(ensures: |ref ret| ret.strict.get().is_none() && ret.fixture.get().is_none()
        && (grammar.is_some() || ret.lowering.is_none())
        && ret.lowering.as_ref().is_none_or(|lowering| lowering.unit().sources().len() == 1_usize))]
    fn new(
        grammar: Option<&Arc<Pbg>>,
        grant: &HostGrant,
    ) -> Self
    {
        let lowering = grammar.and_then(|grammar| lower_prelude(grammar).map(Arc::new));
        Self {
            lowering,
            grant: grant.clone(),
            strict: OnceLock::new(),
            fixture: OnceLock::new(),
        }
    }

    /// The bytes parsing the prelude read: its closure's text when it is held,
    /// none otherwise.
    ///
    /// # Specification
    /// trivial.
    fn parsed(&self) -> ParsedBytes
    {
        ParsedBytes::from(
            self.lowering
                .as_ref()
                .map_or(0_usize, |lowering| <&str>::from(lowering.text()).len()),
        )
    }

    /// The prelude's declarations judged under the walk's grant and settled
    /// under `root`, judged the first time any thread asks for them.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `None` when the prelude is not held or its lowering did not
    ///   reach its end; otherwise [`JudgedClosure::new`] of its lowering under
    ///   the walk's grant and `root`, the same judgement on every call.
    /// - provides: the state each component under `root` is judged after.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the corpus walked under both roots composes as each
    ///   source composes laid after the prelude whole.
    /// - witness: `tests::corpus::sweeps::every_width_composes_the_corpus_alike`
    #[spec(ensures: |ret| ret.is_none() || self.lowering.is_some())]
    fn judged<E>(
        &self,
        root: CorpusRoot,
    ) -> Option<&JudgedClosure>
    where
        E: Engine,
    {
        let lowering = self.lowering.as_ref()?;
        match root {
            CorpusRoot::Strict => &self.strict,
            CorpusRoot::Fixture => &self.fixture,
        }
        .get_or_init(|| JudgedClosure::new::<E>(Arc::clone(lowering), &self.grant, root))
        .as_ref()
    }
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
    /// Its component's admission, when the walk keeps them.
    admission: Maybe<Arc<Admission>, kept::Absent>,
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
    /// - witness: `tests::walk::every_path_answers_in_order`
    /// - witness: `tests::walk::a_tree_is_read_when_visited`
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
            grammar: built_in().map(Arc::new),
            traversal: Traversal::new(paths),
            report: RunReport::default(),
            grant: HostGrant::UNBOUNDED,
            reader: Reader::new(),
            positioning: Positioning::Unpositioned,
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
    /// - witness: `tests::walk::a_grant_bounds_every_source_the_walk_judges`
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

    /// The walk recording, at each admission, where each declaration stands
    /// in its artifact, so [`crate::measure()`] reads each source's rows.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the walk, unchanged but for its positioning; a walk records
    ///   no positions until asked, and pays nothing for them.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a measuring walk over `library/std/src/math` reads
    ///   each source's rows, and a walk not asked answers that it recorded
    ///   none.
    /// - witness: `tests::measure::a_source_measures_the_declarations_it_writes_and_none_it_imports`
    #[inline]
    #[must_use]
    #[spec(ensures: |ref ret| ret.positioning == Positioning::Positioned)]
    pub fn measuring(mut self) -> Self
    {
        self.positioning = Positioning::Positioned;
        self
    }

    /// How many sources the paths of this walk reach, counted up to `bound`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the smaller of `bound` and the sources that a visit of the
    ///   walk's paths reaches, as [`Self::visit`] reaches them. The walk itself
    ///   does not change.
    /// - fails: never; a path that cannot be listed counts no source.
    /// - panics: none.
    /// - intension: lists each directory at most one time, reads no source, and
    ///   stops when the count reaches `bound`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a tree of five sources, a skipped link and a file
    ///   that is not a source counts five under a larger bound and the bound
    ///   under a smaller one.
    /// - witness: `tests::walk::a_tree_is_walked_in_order`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret <= bound)]
    pub fn sources_up_to(
        &self,
        bound: SourceCount,
    ) -> SourceCount
    {
        let mut traversal =
            Traversal::new(self.traversal.arguments.iter().rev().cloned().collect());
        let mut count = SourceCount::default();
        while count < bound
            && let Maybe::Present(reached) = traversal.reach()
        {
            if matches!(reached, Reached::Source) {
                count = SourceCount::from(usize::from(count).saturating_add(1));
            }
        }
        count
    }

    /// Hand every step of the walk to `visitor`, in walk order, lowering the
    /// components on `pool`, and answer the walk's report.
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
    ///   starts another component. As many threads as the pool's width answers,
    ///   never more than the components, the calling thread among them, lower
    ///   and judge the components, each taking the largest component by bytes
    ///   that no thread has taken. The calling thread meanwhile hands over the
    ///   sources in walk order, and it lowers and judges a component itself
    ///   whenever the next one in walk order has not arrived. One component is
    ///   lowered and judged on the calling thread alone, and the pool starts
    ///   its threads only when there are two or more. At
    ///   [`Width::SERIAL`](crate::Width::SERIAL) the calling thread lowers and
    ///   judges each component when its first source comes up. A pool the host
    ///   refuses to start leaves every component to the calling thread.
    /// - provides: the pass `check` and `test` run, on the driver's pool.
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
    /// - witness: `tests::walk::a_tree_is_walked_in_order`
    /// - witness: `tests::walk::every_path_answers_in_order`
    /// - witness: `tests::walk::each_root_stands_its_sources`
    /// - witness: `tests::walk::a_stopped_visit_hands_over_nothing_more`
    /// - witness: `tests::walk::an_importer_is_judged_over_its_sibling`
    /// - witness: `tests::corpus::sweeps::every_width_composes_the_corpus_alike`
    /// - witness: `tests::walk::a_source_given_twice_answers_twice_from_one_judgement`
    #[inline]
    pub fn visit<E, Stop, Visitor>(
        self,
        pool: &Pool,
        mut visitor: Visitor,
    ) -> ControlFlow<Stop, RunReport>
    where
        E: Engine,
        Visitor: FnMut(Step<'_>) -> ControlFlow<Stop>,
    {
        self.visiting::<E, _, _, _>(pool, Keeping::Composed, |step, _unkept| visitor(step))
    }

    /// [`Self::visit`], handing each step beside the admission of the
    /// component its source was judged in, as it stood before the kernel was
    /// offered anything: the arena the component was judged over and the
    /// checker's verdicts.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the steps [`Self::visit`] hands over, in its order, each
    ///   beside its component's admission, or [`kept::Absent::Unjudged`] for a
    ///   fault and for a source whose component's lowering faulted or refused
    ///   it whole; the sources of one component share one copy.
    /// - provides: the corpus walk a differential evaluates the checked core
    ///   of, apart from the program each composition carries.
    /// - fails: never; as [`Self::visit`].
    /// - panics: as [`Self::visit`].
    /// - executable: none — as [`Self::visit`]; the witness evaluates every
    ///   handed admission's `runs` items.
    /// - intension: one copy of each judged component's arena and verdicts,
    ///   held until its last source is handed over.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every `runs` item of the corpus is read from the
    ///   admission handed beside its source.
    /// - witness: `tests::differential::the_corpus_runs_items_agree_with_normalisation_by_evaluation`
    #[inline]
    pub fn visit_admitting<E, Stop, Visitor>(
        self,
        pool: &Pool,
        visitor: Visitor,
    ) -> ControlFlow<Stop, RunReport>
    where
        E: Engine,
        Visitor: FnMut(Step<'_>, Maybe<&Admission, kept::Absent>) -> ControlFlow<Stop>,
    {
        self.visiting::<E, _, _, _>(pool, Keeping::Admission, visitor)
    }

    /// [`Self::visit`], with each lowering job marked by `recording`: the
    /// helpers' jobs on the rings of the pool's threads, and the calling
    /// thread's on the last ring.
    ///
    /// # Specification
    /// - requires: as [`Pool::recording`].
    /// - ensures: the steps [`Self::visit`] hands over, in its order; each
    ///   lowering of a component runs between a start mark and an end mark on
    ///   the ring of the thread that lowers it.
    /// - fails: never; as [`Self::visit`].
    /// - panics: as [`Self::visit`].
    /// - executable: none — as [`Self::visit`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a recorded walk hands over the steps of an unrecorded
    ///   one, and marks each lowering once.
    /// - witness: `tests::walk::a_recorded_walk_marks_each_lowering_and_hands_over_the_same_steps`
    #[cfg(feature = "instrument")]
    #[inline]
    pub fn visit_recording<E, Stop, Visitor, Declares>(
        self,
        recording: &crate::ActivityFork<'_, Declares>,
        mut visitor: Visitor,
    ) -> ControlFlow<Stop, RunReport>
    where
        E: Engine,
        Visitor: FnMut(Step<'_>) -> ControlFlow<Stop>,
        Declares: Sync,
    {
        self.visiting::<E, _, _, _>(recording, Keeping::Composed, |step, _unkept| visitor(step))
    }

    /// [`Self::visit`], each step handed beside its component's admission
    /// when `keeping` asks for one.
    ///
    /// # Specification
    /// - ensures: as [`Self::visit_admitting`] under [`Keeping::Admission`]; as
    ///   [`Self::visit`] under [`Keeping::Composed`], each step beside
    ///   [`kept::Absent::Unasked`] and no admission copied.
    /// - executable: none — as [`Self::visit`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::visit`]'s witnesses under
    ///   [`Keeping::Composed`], and as [`Self::visit_admitting`]'s under
    ///   [`Keeping::Admission`].
    /// - witness: `tests::walk::an_importer_is_judged_over_its_sibling`
    /// - witness: `tests::corpus::sweeps::every_width_composes_the_corpus_alike`
    /// - witness: `tests::differential::the_corpus_runs_items_agree_with_normalisation_by_evaluation`
    fn visiting<E, Stop, Visitor, Jobs>(
        mut self,
        pool: &Jobs,
        keeping: Keeping,
        mut visitor: Visitor,
    ) -> ControlFlow<Stop, RunReport>
    where
        E: Engine,
        Visitor: FnMut(Step<'_>, Maybe<&Admission, kept::Absent>) -> ControlFlow<Stop>,
        Jobs: Helped,
    {
        let unkept = match keeping {
            Keeping::Composed => kept::Absent::Unasked,
            Keeping::Admission => kept::Absent::Unjudged,
        };
        let mut paths = Vec::new();
        let mut slots = Vec::new();
        let mut given = Vec::new();
        while let Maybe::Present(reached) = self.traversal.reach() {
            let path = self.traversal.take_path();
            slots.push(match reached {
                Reached::NoSource => Slot::NoSource,
                Reached::Unreadable(error) => Slot::Unreadable(error),
                Reached::Source => match read_given(&self.reader, &path) {
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
                    visitor(Step::Fault { path, fault }, Maybe::Absent(unkept))?;
                }
                return ControlFlow::Continue(self.report);
            },
        };
        let grant = &self.grant;
        let positioning = self.positioning;
        let grouped = group(
            grammar,
            given,
            Reading::ImportForms,
            &BTreeSet::new(),
            &Unshadowed,
        );
        self.report.parsed_mut().absorb(grouped.parsed);
        // The prelude every component lays first, parsed and lowered here once
        // and judged once under each root it is asked for.
        let prelude = Prelude::new((!grouped.components.is_empty()).then_some(grammar), grant);
        self.report.parsed_mut().absorb(prelude.parsed());
        let prelude = &prelude;
        // Each component its parse did not confirm, grouped again by its own
        // job.
        let regrouped: Vec<OnceLock<Grouped>> =
            grouped.components.iter().map(|_| OnceLock::new()).collect();
        // Each component the lowering refused as a whole within one of its
        // sources, grouped again by its own job with that source set apart.
        let parted: Vec<OnceLock<Grouped>> =
            grouped.components.iter().map(|_| OnceLock::new()).collect();
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
        let cursor = AtomicUsize::new(0);
        // The component at `position`, lowered and judged.
        let work = |position: usize| {
            let component = grouped.components.get(position)?;
            let cells = (regrouped.get(position)?, parted.get(position)?);
            Some(pool.job(|| {
                judgement::<E>(
                    grammar,
                    prelude,
                    component,
                    cells,
                    (grant, keeping, positioning),
                )
            }))
        };
        // The largest component no thread has taken, lowered and judged.
        let take = || {
            let &(_, position) = order.get(cursor.fetch_add(1, Ordering::Relaxed))?;
            Some((position, work(position)?))
        };
        let (sender, receiver) = std::sync::mpsc::channel();
        // The calling thread's share: hand each component's steps over in walk
        // order as its judgement arrives from `helpers` pool threads, lowering
        // and judging one itself whenever the next in walk order has not
        // arrived.
        let consume = |helpers: usize| -> ControlFlow<Stop> {
            // Judgements that arrived ahead of their turn in walk order.
            let mut early = BTreeMap::new();
            // The helpers that have not sent their stop.
            let mut running = helpers;
            // Each judged component's compositions, by source, taken as the
            // last step standing at each is handed over.
            let mut judged: BTreeMap<usize, Vec<Option<Held<'_>>>> = BTreeMap::new();
            for (path, slot) in paths.iter().zip(slots) {
                let (step, admission) = match slot {
                    Slot::NoSource => {
                        self.report.faulted();
                        (
                            Step::Fault {
                                path,
                                fault: SourceFault::NoSource,
                            },
                            Maybe::Absent(unkept),
                        )
                    },
                    Slot::Unreadable(error) => {
                        self.report.faulted();
                        (
                            Step::Fault {
                                path,
                                fault: SourceFault::Unreadable(error),
                            },
                            Maybe::Absent(unkept),
                        )
                    },
                    Slot::Given { given, root } => {
                        let Some(&placed) = grouped.placed.get(given)
                        else {
                            continue;
                        };
                        if let btree_map::Entry::Vacant(unjudged) = judged.entry(placed.component) {
                            let job = loop {
                                if helpers == 0 {
                                    break work(placed.component);
                                }
                                if let Some(job) = early.remove(&placed.component) {
                                    break Some(job);
                                }
                                match receiver.try_recv() {
                                    Ok(Arrival::Judged(arrived, job)) => {
                                        early.insert(arrived, job);
                                        continue;
                                    },
                                    Ok(Arrival::Stopped) => {
                                        running = running.saturating_sub(1);
                                        continue;
                                    },
                                    Err(_) => {},
                                }
                                if let Some((taken, job)) = take() {
                                    if taken == placed.component {
                                        break Some(job);
                                    }
                                    early.insert(taken, job);
                                    continue;
                                }
                                // Every helper has stopped without it: one
                                // panicked, and the fork will say so.
                                if running == 0 {
                                    break work(placed.component);
                                }
                                match receiver.recv() {
                                    Ok(Arrival::Judged(arrived, job)) => {
                                        early.insert(arrived, job);
                                    },
                                    Ok(Arrival::Stopped) => {
                                        running = running.saturating_sub(1);
                                    },
                                    Err(_) => {
                                        break work(placed.component);
                                    },
                                }
                            };
                            let Some(job) = job
                            else {
                                continue;
                            };
                            self.report.lowerings_mut().absorb(job.work.lowerings);
                            self.report.parsed_mut().absorb(job.work.parsed);
                            self.report.spellings_mut().absorb(job.work.spellings);
                            unjudged.insert(job.held);
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
                        (
                            settled(
                                &mut self.report,
                                path,
                                root,
                                (held.text, held.start),
                                held.composed,
                            ),
                            held.admission,
                        )
                    },
                };
                let admission = match admission {
                    Maybe::Present(ref admission) => Maybe::Present(&**admission),
                    Maybe::Absent(reason) => Maybe::Absent(reason),
                };
                if let ControlFlow::Break(stop) = visitor(step, admission) {
                    cursor.store(order.len(), Ordering::Relaxed);
                    return ControlFlow::Break(stop);
                }
            }
            ControlFlow::Continue(())
        };
        match pool.pool().helpers(&order) {
            Maybe::Present(helpers) => {
                // A helper takes the largest component left and sends its
                // judgement, then sends its stop as it ends.
                let helper = || {
                    let _stop = Stopping(&sender);
                    while let Some((position, job)) = take() {
                        if sender.send(Arrival::Judged(position, job)).is_err() {
                            break;
                        }
                    }
                };
                helpers.help(&helper, |posts| consume(posts.0))?;
            },
            Maybe::Absent(_) => {
                drop(sender);
                consume(0)?;
            },
        }
        ControlFlow::Continue(self.report)
    }
}

/// What a helper of the walk's fork sends the calling thread.
///
/// # Specification
/// trivial.
enum Arrival<Job>
{
    /// The judgement of the component at a place in the walk's order.
    Judged(usize, Job),
    /// The helper stopped: it sends nothing more.
    Stopped,
}

/// The stop of one helper of the walk's fork, which it sends as it ends, by
/// its return or by a panic.
///
/// # Specification
/// trivial.
#[repr(transparent)]
struct Stopping<'channel, Job>(&'channel std::sync::mpsc::Sender<Arrival<Job>>);

impl<Job> Drop for Stopping<'_, Job>
{
    /// Send the helper's stop. A send fails only once the calling thread has
    /// dropped its receiver, when no stop is needed.
    ///
    /// # Specification
    /// trivial.
    fn drop(&mut self)
    {
        drop(self.0.send(Arrival::Stopped));
    }
}

impl Traversal
{
    /// A traversal of `paths`, in the order given, nothing yet reached.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new(paths: Vec<PathBuf>) -> Self
    {
        let mut arguments = paths;
        arguments.reverse();
        Self {
            count: arguments.len(),
            arguments,
            given: Vec::new(),
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
    #[inline]
    #[must_use]
    pub fn path(&self) -> &Path
    {
        &self.path
    }

    /// The source or directory last reached, taken, leaving an empty path.
    ///
    /// # Specification
    /// trivial.
    #[inline]
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
    ///   entry another path given names, by its canonical path, is not reached
    ///   under this path: that path reaches it in its turn, and the entry
    ///   answers this path (#3889), so a path every entry of which another path
    ///   names reaches nothing of its own. A path given twice is reached twice.
    ///   An explicit path may be a link; a non-directory argument is one
    ///   source, whatever its name. A path that cannot be listed, or whose kind
    ///   cannot be read, is [`Reached::Unreadable`]; a path that reached no
    ///   source and no fault is [`Reached::NoSource`] after its last entry, at
    ///   that path. Anything reached marks the path given answered. Nothing is
    ///   read and nothing is counted. Exhaustion leaves no path and no entry
    ///   pending, and is stable.
    /// - fails: never; a fault is reached like a source.
    /// - panics: none.
    /// - intension: lists each directory once within one path given, and a
    ///   directory another path given names under none but that one;
    ///   recursion-free, the pending entries an explicit stack.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the walk's ordered rows observe every outcome reached
    ///   here; a tree written after the walk is built is listed when it is
    ///   visited, an empty directory in it listing nothing; a package root
    ///   given beside its sources, and a directory given beside a source in it,
    ///   reach each source once.
    /// - witness: `tests::walk::a_tree_is_walked_in_order`
    /// - witness: `tests::walk::every_path_answers_in_order`
    /// - witness: `tests::walk::a_tree_is_read_when_visited`
    /// - witness: `tests::walk::a_path_another_path_names_is_walked_once_3889`
    #[spec(
        captures: [pending_arguments = self.arguments.len(), was_answered = self.answered == Answered::Yes],
        ensures: |ref ret| match *ret {
            Maybe::Absent(walk_step::Absent::Exhausted) => self.arguments.is_empty() && self.entries.is_empty(),
            Maybe::Present(Reached::NoSource) => !was_answered || pending_arguments != 0,
            Maybe::Present(Reached::Source | Reached::Unreadable(_)) => self.answered == Answered::Yes,
        },
    )]
    #[inline]
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
                if self.given.is_empty() && self.count > 1 {
                    self.given = core::iter::once(&argument)
                        .chain(self.arguments.iter().rev())
                        .map(|path| path.canonicalize().ok())
                        .collect();
                }
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
    /// so they pop in byte order of their names. The sketch set is left out
    /// (`root` § The sketch set).
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: success appends the selected children in descending path
    ///   order, leaving earlier pending entries in place, none of them a sketch
    ///   set, and marks the path given answered when it leaves out a child
    ///   another path given names; failure leaves the pending entries
    ///   unchanged.
    /// - fails: the I/O error listing the path or reading an entry's type.
    /// - panics: none.
    ///
    /// # Errors
    /// The I/O error listing the directory or reading an entry's type met.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nested ordered files, an empty directory and an
    ///   ignored link observe filtering and stack order; a package root given
    ///   beside its sources, and a directory given beside a source in it,
    ///   observe the children another path names left out; errors partway
    ///   through directory iteration are outside these witnesses.
    /// - witness: `tests::walk::a_tree_is_walked_in_order`
    /// - witness: `tests::walk::a_tree_is_read_when_visited`
    /// - witness: `tests::walk::a_path_another_path_names_is_walked_once_3889`
    /// - witness: `tests::walk::a_sketch_set_is_walked_only_when_named_4560`
    #[spec(
        captures: [before = self.entries.len()],
        ensures: |ref ret| if ret.is_err() {
            self.entries.len() == before
        } else {
            self.entries.get(before..).is_some_and(|added|
                added.iter().all(|entry| match *entry {
                    Entry::Directory(ref path) => path.parent() == Some(self.path.as_path())
                        && descent(path) == Descent::Walked,
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
        // Another path given may name a child (#3889): that path walks it,
        // so this one leaves it out. A child's canonical path is the path
        // being walked's, joined with the child's path below it, since the
        // listing follows no link.
        let walking = self
            .count
            .saturating_sub(self.arguments.len())
            .saturating_sub(1);
        let canonical = self.given.get(walking).and_then(Option::as_deref);
        for listed in listing {
            let listed = listed?;
            let kind = listed.file_type()?;
            let path = listed.path();
            let entry = if kind.is_dir() {
                if descent(&path) == Descent::Sketch {
                    continue;
                }
                Entry::Directory(path)
            }
            else if !kind.is_symlink() && path.extension() == Some(OsStr::new(EXTENSION)) {
                Entry::Source(path)
            }
            else {
                continue;
            };
            let named = canonical.is_some_and(|canonical| {
                entry_path(&entry)
                    .strip_prefix(&self.argument)
                    .is_ok_and(|below| {
                        self.given.iter().enumerate().any(|(index, other)| {
                            index != walking
                                && other.as_deref().is_some_and(|other| {
                                    other
                                        .strip_prefix(canonical)
                                        .is_ok_and(|rest| rest == below)
                                })
                        })
                    })
            });
            if named {
                self.answered = Answered::Yes;
                continue;
            }
            found.push(entry);
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
/// - witness: `tests::walk::each_root_stands_its_sources`
/// - witness: `tests::walk::a_tree_is_walked_in_order`
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

/// Parse and lower `component` once: the first step of [`judgement`].
///
/// # Specification
/// - requires: `component` was laid out by `component::group`.
/// - ensures: what [`lower_after`] makes of the component after `prelude`, when
///   it lays it there. Otherwise, when the component's text parses and its tree
///   confirms how its imports were read ([`Component::confirms`]), what
///   [`lower_parsed_unit`] makes of that tree and the unit, checked whole, and
///   every source of the component lowered. A text read [`Reading::Whole`] that
///   does not parse is its [`ComposeFault::Parse`], no source lowered; under
///   [`Reading::ImportForms`], a text that does not parse or does not confirm
///   comes to no lowering, no source lowered, for the walk to group again. The
///   bytes parsed are counted either way.
/// - fails: never; a fault is carried in the answer.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the corpus at several widths composes equal to the serial
///   visit source by source; a diamond's base is lowered once; an import its
///   component's parse does not read is judged as each source's own parse reads
///   it; an importer is parsed whole once.
/// - witness: `tests::corpus::sweeps::every_width_composes_the_corpus_alike`
/// - witness: `tests::walk::an_importer_is_judged_over_its_sibling`
/// - witness: `tests::walk::an_import_its_parse_does_not_read_is_grouped_again`
/// - witness: `tests::walk::an_import_parses_its_importer_once_617`
#[spec(ensures: |ref ret| usize::from(ret.lowerings) <= component.members.len()
    && usize::from(ret.parsed) <= component.text.len())]
fn lower<'text, E>(
    grammar: &Pbg,
    prelude: &'text Prelude,
    component: &'text Component,
) -> Job<'text>
where
    E: Engine,
{
    if let Some(job) = lower_after::<E>(grammar, prelude, component) {
        return job;
    }
    let mut lowerings = LoweringCount::default();
    let lowering = match parse(grammar, SourceText::from(component.text.as_str())) {
        Ok(parsed)
            if component.confirms(
                grammar,
                parsed.tree(),
                gandr_surface_syntax::ByteLength::from(0_usize),
            ) == Confirmation::Confirmed =>
        {
            Some(lower_parsed_unit(
                grammar,
                parsed,
                &component.unit,
                &mut lowerings,
                &mut gandr_surface_lowering::coincide::Decisions::none(),
            ))
        },
        Ok(_) => None,
        Err(_) if component.reading == Reading::ImportForms => None,
        Err(error) => Some(Err(ComposeFault::Parse(error))),
    };
    Job {
        lowering,
        checking: Checking::Whole,
        lowerings,
        parsed: ParsedBytes::from(component.text.len()),
    }
}

/// Parse `component`'s own bytes past `prelude`, lay them after the prelude's
/// tree and lower them onto its judged arena.
///
/// # Specification
/// - requires: `component` was laid out by `component::group`.
/// - ensures: `None`, for the component to be lowered whole, when the prelude
///   is not judged under the root of the component's first source, the
///   component's text does not begin with the prelude's, or its own bytes do
///   not parse or do not lay after the prelude's tree. Otherwise, when its own
///   parse confirms how its imports were read, what [`lower_onto_closure`]
///   makes of the joined tree onto the judged prelude's arena and how that is
///   checked; when it does not, no lowering, for the walk to group again. Its
///   own bytes are counted parsed.
/// - provides: a component's lowering at the cost of its own sources.
/// - fails: never; a fault is carried in the answer.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the corpus walked after the prelude composes as each
///   source does laid after it whole; a walk of several components parses the
///   prelude once.
/// - witness: `tests::corpus::sweeps::every_width_composes_the_corpus_alike`
/// - witness: `tests::walk::a_walk_parses_the_prelude_once_for_every_component_2331`
#[spec(ensures: |ref ret| ret.as_ref().is_none_or(|job|
    usize::from(job.lowerings) <= component.members.len()
        && usize::from(job.parsed) < component.text.len()))]
fn lower_after<'text, E>(
    grammar: &Pbg,
    prelude: &'text Prelude,
    component: &'text Component,
) -> Option<Job<'text>>
where
    E: Engine,
{
    // The prelude's declarations settle under the first source's root, the
    // root `judge_members` continues a closure under.
    let judged = prelude.judged::<E>(component.members.first()?.root)?;
    let closure = judged.lowering();
    let own = component.text.strip_prefix(<&str>::from(closure.text()))?;
    let alone = parse(grammar, SourceText::from(own)).ok()?;
    // The join's first root is the prelude's: the component's own imports are
    // read from its own parse, moved past the prelude's text.
    let confirmation = component.confirms(
        grammar,
        alone.tree(),
        gandr_surface_syntax::ByteLength::from(<&str>::from(closure.text()).len()),
    );
    let parsed = alone
        .after(closure.tree(), SourceText::from(component.text.as_str()))
        .ok()?;
    let mut lowerings = LoweringCount::default();
    let (lowering, checking) = if confirmation == Confirmation::Confirmed {
        match lower_onto_closure(
            judged,
            judged.arena(),
            parsed,
            &component.unit,
            &mut lowerings,
            &mut gandr_surface_lowering::coincide::Decisions::none(),
        ) {
            Ok((lowering, checking)) => (Some(Ok(lowering)), checking),
            Err(fault) => (Some(Err(fault)), Checking::Whole),
        }
    }
    else {
        (None, Checking::Whole)
    };
    Some(Job {
        lowering,
        checking,
        lowerings,
        parsed: ParsedBytes::from(own.len()),
    })
}

/// Lower `component` and judge it: one thread's share of a visit.
///
/// # Specification
/// - requires: `component` was laid out by `component::group`. `regrouped` and
///   `parted` are the component's own cells of the visit, and only this
///   judgement sets them.
/// - ensures: one held composition per member, in member order, beside the work
///   counted. The component is lowered as [`lower`] lowers it. A lowering that
///   refuses the component as a whole within one of its sources is judged as
///   [`judge_regrouped`] judges what [`part`] makes of it, kept in `parted`. A
///   component that its parse did not confirm is judged as [`judge_regrouped`]
///   judges what [`regroup`] makes of it, kept in `regrouped`. Any other
///   lowering is judged as [`judge`] judges it. The work holds what the
///   lowering and each of these steps count.
/// - fails: never; a fault is carried in the answer.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — every width composes the corpus as the serial visit does,
///   source by source, with the same report. A source refused whole and an
///   import that its parse does not read are judged as before.
/// - witness: `tests::corpus::sweeps::every_width_composes_the_corpus_alike`
/// - witness: `tests::walk::a_tree_is_walked_in_order`
/// - witness: `tests::walk::a_source_refused_whole_refuses_only_itself_and_its_importers_1027`
/// - witness: `tests::walk::an_import_its_parse_does_not_read_is_grouped_again`
#[spec(ensures: |ref ret| ret.held.len() == component.members.len())]
fn judgement<'text, E>(
    grammar: &Pbg,
    prelude: &'text Prelude,
    component: &'text Component,
    (regrouped, parted): (&'text OnceLock<Grouped>, &'text OnceLock<Grouped>),
    judging: (&HostGrant, Keeping, Positioning),
) -> Judgement<'text>
where
    E: Engine,
{
    let job = lower::<E>(grammar, prelude, component);
    let mut work = Work {
        lowerings: job.lowerings,
        parsed: job.parsed,
        spellings: SpellingCount::default(),
    };
    let held = if let Some(lowering) = job.lowering {
        let refused = lowering
            .as_ref()
            .ok()
            .and_then(|lowering| refused_member(lowering, component));
        if let Some(first) = refused {
            let again = parted.get_or_init(|| part(grammar, &mut work, component, first));
            judge_regrouped::<E>(&mut work, grammar, judging, again)
        }
        else {
            judge::<E>(
                &mut work.spellings,
                judging,
                component,
                (lowering, job.checking),
            )
            .into_iter()
            .map(Some)
            .collect()
        }
    }
    else {
        let again = regrouped.get_or_init(|| regroup(grammar, component));
        judge_regrouped::<E>(&mut work, grammar, judging, again)
    };
    Judgement { held, work }
}

/// Judge `component` from what lowering it came to and how it is checked,
/// under `grant`, each source settled under its own root: each source's
/// composition beside its unit's text up to the source's own end and where
/// its bytes start.
///
/// # Specification
/// - requires: `lowering` is what [`lower`] or [`lower_unit_source`] made of
///   `component`, beside the checking it came with.
/// - ensures: one held composition per member, in member order: what
///   [`judge_component`] makes of a lowering under `keeping` and `positioning`,
///   each beside the component's one kept admission, or the lowering's fault at
///   every source, with no admission. `spelled` advances as [`judge_component`]
///   says.
/// - fails: never; a fault is carried in the answer.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`lower`].
/// - witness: `tests::walk::an_importer_is_judged_over_its_sibling`
/// - witness: `tests::walk::an_import_its_parse_does_not_read_is_grouped_again`
#[spec(ensures: |ref ret| ret.len() == component.members.len())]
fn judge<'text, E>(
    spelled: &mut SpellingCount,
    (grant, keeping, positioning): (&HostGrant, Keeping, Positioning),
    component: &'text Component,
    (lowering, checking): (
        Result<Lowering<'text>, ComposeFault<'text>>,
        Checking<'text>,
    ),
) -> Vec<Held<'text>>
where
    E: Engine,
{
    let (composed, admission) = match lowering {
        Ok(lowering) => judge_component::<E>(
            (lowering, SourceText::from(component.text.as_str())),
            (grant, checking),
            (&component.members, spelled),
            (keeping, positioning),
        ),
        Err(fault) => (
            component
                .members
                .iter()
                .map(|_| Err(fault.clone()))
                .collect(),
            Maybe::Absent(match keeping {
                Keeping::Composed => kept::Absent::Unasked,
                Keeping::Admission => kept::Absent::Unjudged,
            }),
        ),
    };
    let admission = match admission {
        Maybe::Present(admission) => Maybe::Present(Arc::new(admission)),
        Maybe::Absent(reason) => Maybe::Absent(reason),
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
            admission: admission.clone(),
        })
        .collect()
}

/// Lower and judge each component of `again`, under `grant`, keeping each
/// one's admission when `keeping` asks for it, and hand back each given
/// source's held composition in the order given.
///
/// # Specification
/// - requires: `again` is what [`regroup`] made of one component.
/// - ensures: each component of `again` parsed and lowered once with
///   [`lower_unit_source`] and judged with [`judge`], its sources counted
///   lowered and its text and `again`'s grouping counted parsed into `work`;
///   one held composition per given source, in the order given, none for a
///   source no component holds.
/// - fails: never; a fault is carried in the answer.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`regroup`].
/// - witness: `tests::walk::an_import_its_parse_does_not_read_is_grouped_again`
#[spec(ensures: |ref ret| ret.len() == again.placed.len())]
fn judge_regrouped<'text, E>(
    work: &mut Work,
    grammar: &Pbg,
    (grant, keeping, positioning): (&HostGrant, Keeping, Positioning),
    again: &'text Grouped,
) -> Vec<Option<Held<'text>>>
where
    E: Engine,
{
    work.parsed.absorb(again.parsed);
    let mut parts: Vec<Vec<Option<Held<'text>>>> = Vec::with_capacity(again.components.len());
    for part in &again.components {
        let mut lowerings = LoweringCount::default();
        let lowering = lower_unit_source(
            grammar,
            SourceText::from(part.text.as_str()),
            &part.unit,
            &mut lowerings,
        );
        work.lowerings.absorb(lowerings);
        work.parsed.absorb(ParsedBytes::from(part.text.len()));
        parts.push(
            judge::<E>(
                &mut work.spellings,
                (grant, keeping, positioning),
                part,
                (lowering, Checking::Whole),
            )
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
/// - witness: `tests::walk::an_import_its_parse_does_not_read_is_grouped_again`
#[spec(ensures: |ref ret| ret.placed.len() == component.members.len())]
fn regroup(
    grammar: &Pbg,
    component: &Component,
) -> Grouped
{
    group(
        grammar,
        given_of(component),
        Reading::Whole,
        &BTreeSet::new(),
        &Unshadowed,
    )
}

/// `component`'s sources, in member order, each with its path, root and own
/// text, as a grouping is given them.
///
/// # Specification
/// trivial.
fn given_of(component: &Component) -> Vec<Given>
{
    component
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
        .collect()
}

/// The path of the source of `component` whose bytes hold the refusal by
/// which `lowering` refused the component as a whole.
///
/// # Specification
/// - requires: `lowering` is what the lowering made of `component`'s text.
/// - ensures: the path of the member whose bytes hold the start of the
///   refusal's span, when the component has more than one member and the
///   lowering refused it as a whole at a span; none otherwise.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`part`].
/// - witness: `tests::walk::a_source_refused_whole_refuses_only_itself_and_its_importers_1027`
/// - witness: `tests::walk::a_pair_refused_whole_in_its_importer_settles_its_base`
#[spec(ensures: |ref ret| ret.is_none() || (component.members.len() > 1_usize
    && component.sources.iter().any(|source| Some(&source.path) == ret.as_ref())))]
fn refused_member(
    lowering: &Lowering<'_>,
    component: &Component,
) -> Option<PathBuf>
{
    if component.members.len() < 2_usize {
        return None;
    }
    let Maybe::Present(span) = lowering.refused()?.span()
    else {
        return None;
    };
    let at = span.start();
    component
        .members
        .iter()
        .zip(&component.sources)
        .find(|&(member, _)| member.start <= at && at < member.end)
        .map(|(_, source)| source.path.clone())
}

/// `component`'s sources grouped again with the source at `first` set
/// apart, and with it each source a regrouped part's lowering refuses as a
/// whole, until no part of more than one source is refused within one of
/// them.
///
/// # Specification
/// - requires: `component` was laid out by `component::group`, and its lowering
///   refused it as a whole within the bytes of the source at `first`.
/// - ensures: [`group`] under [`Reading::Whole`] of the component's sources, in
///   member order, apart from `first` and from each source [`refused_member`]
///   finds in a part of a round's grouping; `placed` holds each member's place,
///   in member order. Each part of more than one source is lowered once per
///   round to find them, counted into `work` with its text counted parsed, as
///   is each round's grouping but the last.
/// - fails: never.
/// - panics: none.
/// - intension: one round per source set apart, at most one per member;
///   recursion-free.
///
/// # Adequacy
/// - hypothesis: L3 — a base, a source refused whole that imports it, a sibling
///   that imports it too and a source that imports the refused one: the refused
///   source stands alone, its importer refuses its import, and the others
///   settle as they do alone.
/// - witness: `tests::walk::a_source_refused_whole_refuses_only_itself_and_its_importers_1027`
/// - witness: `tests::walk::two_sources_refused_whole_are_each_set_apart`
#[spec(ensures: |ref ret| ret.placed.len() == component.members.len())]
fn part(
    grammar: &Pbg,
    work: &mut Work,
    component: &Component,
    first: PathBuf,
) -> Grouped
{
    let mut apart = BTreeSet::from([first]);
    loop {
        let again = group(
            grammar,
            given_of(component),
            Reading::Whole,
            &apart,
            &Unshadowed,
        );
        let before = apart.len();
        for piece in again
            .components
            .iter()
            .filter(|piece| piece.members.len() > 1_usize)
        {
            let mut lowerings = LoweringCount::default();
            let lowering = lower_unit_source(
                grammar,
                SourceText::from(piece.text.as_str()),
                &piece.unit,
                &mut lowerings,
            );
            work.lowerings.absorb(lowerings);
            work.parsed.absorb(ParsedBytes::from(piece.text.len()));
            if let Some(found) = lowering
                .as_ref()
                .ok()
                .and_then(|lowering| refused_member(lowering, piece))
            {
                let _fresh = apart.insert(found);
            }
        }
        if apart.len() == before {
            return again;
        }
        work.parsed.absorb(again.parsed);
    }
}

/// Classify the source at `path` by its canonical path and read it through
/// `reader`, as a source given to `component::group`.
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
/// - witness: `tests::walk::every_path_answers_in_order`
/// - witness: `tests::walk::an_explicit_link_uses_its_target_root_and_keeps_its_path`
#[spec(ensures: |ref ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|given| given.path.is_absolute()))]
fn read_given(
    reader: &Reader,
    path: &Path,
) -> std::io::Result<Given>
{
    let mut text = String::new();
    let root = read_source(reader, path, &mut text)?;
    let canonical = std::fs::canonicalize(path)?;
    Ok(Given {
        path: canonical,
        root,
        text,
    })
}

/// Classify the source at `path` by its canonical path, and read its text
/// through `reader` into `text`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: success replaces `text` with the complete UTF-8 file, as
///   [`Reader::read`] reads it under its canonical path, and returns that
///   path's root. On any error, the previous text is unchanged.
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
/// - witness: `tests::walk::a_tree_is_read_when_visited`
/// - witness: `tests::walk::an_explicit_link_uses_its_target_root_and_keeps_its_path`
#[spec(
    captures: [before = text.len()],
    ensures: |ref ret| ret.is_ok() || text.len() == before,
)]
pub fn read_source(
    reader: &Reader,
    path: &Path,
    text: &mut String,
) -> std::io::Result<SourceRoot>
{
    let canonical = std::fs::canonicalize(path)?;
    let read = reader.read(&canonical)?;
    text.clear();
    text.push_str(read.text().as_ref());
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
/// - witness: `tests::walk::a_tree_is_walked_in_order`
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
mod tests
{
    use std::io;
    use std::path::Path;

    use crate::fixture::Scratch;
    use crate::reader::Reader;

    #[test]
    fn failed_reads_preserve_the_previous_source()
    {
        let scratch = Scratch::new(Path::new("failed-reads"));
        let absent = scratch.0.join("absent.gandr");
        let invalid = scratch.0.join("invalid.gandr");
        std::fs::write(&invalid, [0xff_u8]).expect("the invalid UTF-8 file is written");
        let previous = "previous λ\r\n";
        let mut text = previous.to_owned();
        let reader = Reader::new();
        for (path, expected_kind) in [
            (absent.as_path(), Some(io::ErrorKind::NotFound)),
            (scratch.0.as_path(), None),
            (invalid.as_path(), Some(io::ErrorKind::InvalidData)),
        ] {
            let error = super::read_source(&reader, path, &mut text)
                .expect_err("the path is not a readable source");
            if let Some(kind) = expected_kind {
                assert_eq!(error.kind(), kind);
            }
            assert_eq!(
                text, previous,
                "an unsuccessful read leaves the previous source intact"
            );
        }
    }
}
