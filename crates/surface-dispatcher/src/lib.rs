//! Routes a driver invocation into the gandr surface pipeline, and composes
//! that pipeline: parse, lower, check, settle, and run.
//!
//! The driver (`gandr-lang`) owns the argument surface and the process
//! boundary; this crate owns what happens after an invocation is understood.
//! An invocation enters as an [`Invocation`] and leaves as an [`Outcome`] the
//! driver renders.
//!
//! # Routing performs no I/O; the walk is the verb's
//!
//! [`dispatch`] reads no file and writes nothing. The `check` and `test` verbs
//! route to a [`Walk`] over the paths they were given and the [`Width`] to
//! visit it at, and the walk's I/O — listing a directory, reading a source —
//! happens as the driver hands it its [`Pool`] and a visitor with
//! [`Walk::visit`]. The `run`
//! verb routes to a [`Script`], which reads its one source when the driver
//! runs it. The `stage` verb routes to a [`Staging`], which reads nothing: it
//! builds its programs when the driver runs it. The `fmt` verb routes to a
//! [`Formatting`], which reaches its paths as a walk does, and reads, lays out
//! and rewrites each source as the driver advances it with
//! [`Formatting::step`]. The `ledger` verb routes to a [`LedgerTask`], which
//! builds its ledger and writes its files, or verifies its exemplars, when the
//! driver runs it.
//!
//! `dispatch` reads no file and writes nothing: it builds the grammar the walk
//! parses with, which is computation, and returns. The walk's I/O happens as
//! the driver calls `Walk::visit`. Directories are walked depth-first in byte
//! order of their entries' names. Discovered symbolic links are skipped; other
//! non-directory `.gandr` entries are selected without a regular-file check.
//! A path given explicitly is read as a source whatever its name, following
//! symbolic links.
//!
//! # Every source is read before any is judged
//!
//! A source may import a sibling the walk reaches before it or after it, and
//! the sources joined by imports are judged once, together, as one component
//! (the `component` module). So [`Walk::visit`] reaches every path and reads
//! every source before it judges any, and holds the tree's text until the
//! visit ends. The alternative was a walk stepping through one source at a
//! time, holding one text in memory and printing the first line after the
//! first read; it can judge an importer only over its own import closure, so
//! a source imported by several is lowered once per importer. The choice
//! reverses for a tree whose text does not fit in memory, when the walk reads
//! the import graph first and each component's texts again to lower it.
//!
//! # Components fork; judgement keeps walk order
//!
//! [`Walk::visit`] parses and lowers the components on the driver's
//! [`Pool`], largest first, and judges, settles and reports their sources in
//! walk order on the calling thread, so every count, verdict and diagnostic
//! is the serial visit's at every width. A pool at [`Width::SERIAL`] is that
//! serial visit, and the reference every wider one is tested against. The
//! `stage` verb forks each program's stages on the same pool, so a process
//! starts its threads once (the `pool` module).
//!
//! # One composition serves both verbs
//!
//! [`compose()`] carries one source through the whole pipeline: it parses the
//! source, lowers the tree once, adapts the lowered declarations to the
//! checker's input, judges them, has the kernel re-derive every acceptance,
//! and settles each declaration against what it states. `check` and `test`
//! run that same function over the same walk and differ only in what they
//! print, so a source has one verdict per run whichever verb ran it.
//!
//! Its two halves are public: [`lower_source`] parses and lowers, and
//! [`judge_module`] judges, settles and readmits what the lowering read.
//! [`compose()`] is exactly the one then the other; the halves exist for the
//! session, which keeps the lowered module to hand the incremental checker
//! beside the verdicts. [`lower_parsed`] is [`lower_source`] past its parse,
//! for the session, which parses through its form store. [`judge_module`] is
//! itself [`judge`] then [`Judged::admit`]: a face renders the settled
//! composition before the kernel has been offered anything, and the
//! [`Admission`] completes it with its kernel artifact.
//!
//! # The run stage follows the check
//!
//! [`judge_module`] also focuses every accepted declaration into the command
//! IL, and the [`Program`] it builds runs any declaration on the L machine and
//! reads its terminal back: the settle comparison runs the declarations that
//! state a `runs` outcome, the session runs what the user entered, and `gandr
//! run` runs a source's `main`. Nothing runs that no
//! caller asked for, so `check` performs no run beyond the outcomes its sources
//! state.
//!
//! # Staged programs check on the driver's pool
//!
//! The `stage` verb builds staging observer programs and checks each through
//! the checker's program entry, which forks every stage — normalization,
//! readmission, family admission — through the fork the verb hands it: a
//! work-stealing pool of the invocation's width, or the calling thread at one.
//! Every program of a run shares one memo, in order.
//!
//! # Membership is location
//!
//! [`classify`] decides from a source's path alone which root it sits under:
//! the strict root, which holds every declaration to *checks, owing nothing*;
//! the fixture root, where expectations are admitted; or the fixture root's
//! pending set, whose sources carry a refusal no expectation can state.
//! A path under no root is strict.
//!
//! # The corpus runs through the walk
//!
//! The corpus's two roots are run through the walk:
//! `tests::corpus::the_strict_root_checks_owing_nothing`,
//! `tests::corpus::the_fixture_root_settles_every_fixture`,
//! `tests::corpus::the_two_roots_exercise_every_row`,
//! `tests::corpus::a_run_lowers_each_source_once`; the identity subject's base
//! is lowered once in its importers' component:
//! `tests::corpus::the_identity_base_is_lowered_once_for_its_importers`; every
//! run outcome they state, and the focusing of every declaration they accept:
//! `tests::corpus::l_machine_matches_the_outcome_snapshots_on_the_model_corpus`,
//! `tests::corpus::l_machine_matches_the_outcome_snapshots_on_the_pathological_corpus`,
//! `tests::corpus::focusing_is_total_on_the_model_corpus`,
//! `tests::corpus::focusing_is_total_on_the_pathological_corpus`; and the
//! registration witness (`gandr-surface-corpus`'s `root` module, § One walk
//! registers every source): `tests::corpus::every_corpus_source_is_registered`,
//! `tests::corpus::a_planted_orphan_is_not_registered`.
//!
//! Each decision, with the alternative it was chosen over and what would
//! reverse it, is in the module that owns it.
//!
//! # Specification evidence
//!
//! Each nontrivial operation states a contract or an exemption, and an
//! adequacy claim naming its witnesses. The boundary evidence includes:
//!
//! | Surface | Observed boundary |
//! | ------- | ----------------- |
//! | Reports (`report`) and exercised rows (`exercised`) | Saturating counts preserve unrelated fields; repeated row assignments retain the last value. |
//! | Corpus registration (`tests/corpus.rs`) | A directory with a source extension is traversed rather than registered as a source. |
//!
//! # Optional tracing
//!
//! Enable `tracing` for an INFO span around `dispatch`. It records no argument
//! or outcome payload and installs no subscriber. The driver, `gandr-lang`,
//! owns output; the evaluator, `gandr-core-nbe`, uses the same diagnostics
//! interface independently. The dependency is optional and off by default, so
//! ordinary routing has no instrumentation.
//!
//! The choice is caller-owned structured diagnostics. Printing from this
//! library would seize an output destination; installing a global subscriber
//! would seize process policy. Revisit only when a library-owned diagnostic
//! destination becomes an explicit API requirement, rather than an incidental
//! side effect of dispatch.

// Module documentation that predates the shape lint: 50 headings outside the
// vocabulary, 12 decision records, 7 issue references and 12 budgets exceeded.
// Each allow leaves with the rewrite that clears its count.
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    allow(
        module_doc_heading,
        doc_decision_record,
        doc_issue_reference,
        module_doc_budget,
        reason = "module documentation that predates the shape lint"
    )
)]

extern crate alloc;

mod cells;
mod component;
mod compose;
mod entry;
mod evaluate;
mod exercised;
mod format;
mod generation;
mod ledger;
mod manifold;
mod measure;
mod package;
mod pool;
mod presentation;
mod reader;
mod report;
mod root;
mod schedule;
mod script;
mod stage;
mod tier;
mod typed;
mod verdicts;
mod walk;
mod width;
mod workspace;

use std::path::PathBuf;

use anodized::spec;
pub use gandr_core_checker::Demand;
pub use gandr_core_checker::HostGrant;
pub use gandr_core_checker::Polled;
pub use gandr_core_checker::Retirement;
pub use gandr_core_checker::Unretired;
pub use gandr_core_checker::worlds::WorldName;
pub use gandr_core_term::effect::OperationName;
pub use gandr_core_term::effect::host::AuthorityError;

pub use crate::cells::CellRow;
pub use crate::cells::Census;
pub use crate::cells::CensusFault;
pub use crate::cells::CensusStep;
pub use crate::component::Freshness;
pub use crate::component::ImportBase;
pub use crate::component::ImportPath;
pub use crate::component::Laid;
pub use crate::component::Named;
pub use crate::component::ParsedBytes;
pub use crate::component::Shadows;
pub use crate::component::Unshadowed;
pub use crate::component::forget;
pub use crate::component::imports_named;
pub use crate::component::laid;
pub use crate::component::lay_out;
pub use crate::component::lay_out_shadowed;
pub use crate::component::lay_out_written;
pub use crate::component::named_path;
pub use crate::component::path_imports;
pub use crate::component::written;
pub use crate::compose::Admission;
pub use crate::compose::ArtifactPositions;
pub use crate::compose::Checking;
pub use crate::compose::ComposeFault;
pub use crate::compose::Composed;
pub use crate::compose::Elaborating;
pub use crate::compose::Judged;
pub use crate::compose::JudgedClosure;
pub use crate::compose::Lowered;
pub use crate::compose::Lowering;
pub use crate::compose::LoweringCount;
pub use crate::compose::Positioning;
pub use crate::compose::Recorded;
pub use crate::compose::Recording;
pub use crate::compose::Resumption;
pub use crate::compose::SpellingCount;
pub use crate::compose::Unheld;
pub use crate::compose::adapt;
pub use crate::compose::admitted;
pub use crate::compose::compose;
pub use crate::compose::compose_on;
pub use crate::compose::item_program;
pub use crate::compose::judge;
pub use crate::compose::judge_member;
pub use crate::compose::judge_member_after;
pub use crate::compose::judge_member_after_retiring;
pub use crate::compose::judge_member_tabled;
pub use crate::compose::judge_member_tabled_retiring;
pub use crate::compose::judge_module;
pub use crate::compose::kept;
pub use crate::compose::lower_closure;
pub use crate::compose::lower_onto_closure;
pub use crate::compose::lower_parsed;
pub use crate::compose::lower_parsed_unit;
pub use crate::compose::lower_resumed_unit;
pub use crate::compose::lower_source;
pub use crate::compose::lower_unit_source;
pub use crate::compose::positioned;
pub use crate::compose::tabled;
pub use crate::entry::Entries;
pub use crate::entry::Refusals;
pub use crate::entry::entries;
pub use crate::evaluate::Captured;
pub use crate::evaluate::Console;
pub use crate::evaluate::Engine;
pub use crate::evaluate::Entered;
pub use crate::evaluate::Entry;
pub use crate::evaluate::Evaluation;
pub use crate::evaluate::ExitStatus;
pub use crate::evaluate::Hosted;
pub use crate::evaluate::Input;
pub use crate::evaluate::Line;
pub use crate::evaluate::MigrationCount;
pub use crate::evaluate::Printed;
pub use crate::evaluate::Program;
pub use crate::evaluate::ProgramKey;
pub use crate::evaluate::RunStatus;
pub use crate::evaluate::SealedRun;
pub use crate::evaluate::Terminal;
pub use crate::evaluate::Unfinished;
pub use crate::evaluate::Unrunnable;
pub use crate::evaluate::ValueSpelling;
pub use crate::evaluate::WorldBinding;
pub use crate::evaluate::WorldBindingError;
pub use crate::evaluate::WorldBindings;
pub use crate::evaluate::Worlds;
pub use crate::evaluate::declaration_name;
pub use crate::evaluate::hole_site;
pub use crate::evaluate::last_declared;
pub use crate::evaluate::program_entry;
pub use crate::exercised::Exercised;
pub use crate::exercised::Row;
pub use crate::format::FormatFault;
pub use crate::format::FormatStep;
pub use crate::format::Formatting;
pub use crate::format::Kept;
pub use crate::format::Rewrite;
pub use crate::generation::Delivered;
pub use crate::generation::Generations;
pub use crate::generation::Retired;
pub use crate::generation::Submitted;
pub use crate::generation::Watch;
pub use crate::generation::delivery;
pub use crate::ledger::Area;
pub use crate::ledger::ExemplarFault;
pub use crate::ledger::ExemplarFinding;
pub use crate::ledger::ExemplarReport;
pub use crate::ledger::Feature;
pub use crate::ledger::FeatureId;
pub use crate::ledger::FeatureLedger;
pub use crate::ledger::LedgerFault;
pub use crate::ledger::LedgerRun;
pub use crate::ledger::LedgerTask;
pub use crate::ledger::Malformed;
pub use crate::ledger::RecoveryFinding;
pub use crate::ledger::RecoveryReport;
pub use crate::ledger::ShownFeature;
pub use crate::ledger::Status;
pub use crate::ledger::SyntaxLedger;
pub use crate::manifold::Manifold;
pub use crate::manifold::Secreted;
pub use crate::manifold::Secrets;
pub use crate::manifold::Site;
pub use crate::manifold::Stated;
pub use crate::manifold::Undeployed;
pub use crate::measure::Measure;
pub use crate::measure::measure;
pub use crate::measure::measured;
pub use crate::package::Absence;
pub use crate::package::Body;
pub use crate::package::Differing;
pub use crate::package::Field;
pub use crate::package::Held;
pub use crate::package::Identity;
pub use crate::package::LIBRARY;
pub use crate::package::MANIFEST;
pub use crate::package::Manifest;
pub use crate::package::ManifestFault;
pub use crate::package::Package;
pub use crate::package::PackageAddress;
pub use crate::package::Reconciled;
pub use crate::package::Unaddressed;
pub use crate::package::Unmanifested;
pub use crate::package::Unpathed;
pub use crate::package::export::Export;
pub use crate::package::export::Exporting;
pub use crate::package::export::Unexported;
pub use crate::package::export::Unreadmitted;
pub use crate::package::export::exported_source;
pub use crate::package::lock::Alias;
pub use crate::package::lock::Coordinate;
pub use crate::package::lock::Dependency;
pub use crate::package::lock::LOCK;
pub use crate::package::lock::Lock;
pub use crate::package::lock::LockFault;
pub use crate::package::lock::Locked;
pub use crate::package::lock::SignatureKey;
pub use crate::package::lock::Unresolved;
pub use crate::package::lock::lock_file;
pub use crate::package::lock::relock;
pub use crate::package::package_root;
pub use crate::package::packaged;
pub use crate::package::reconcile;
pub use crate::package::toolchain::Running;
pub use crate::package::toolchain::Separated;
pub use crate::package::toolchain::Toolchain;
pub use crate::package::toolchain::Unconstrained;
pub use crate::package::toolchain::Unmet;
pub use crate::package::toolchain::Version;
pub use crate::pool::Pool;
pub use crate::pool::PoolFault;
pub use crate::presentation::Presentation;
pub use crate::presentation::PresentationFault;
pub use crate::presentation::presented;
pub use crate::presentation::read_presentation;
pub use crate::report::Goals;
pub use crate::report::Lints;
pub use crate::report::Reach;
pub use crate::report::RunReport;
pub use crate::report::RunVerdict;
pub use crate::report::Shown;
pub use crate::report::SourceCount;
pub use crate::report::SourceCounts;
pub use crate::report::Verb;
pub use crate::report::shown;
pub use crate::root::SourceRoot;
pub use crate::root::classify;
pub use crate::schedule::Scheduling;
pub use crate::script::Ran;
pub use crate::script::Script;
pub use crate::script::ScriptRun;
pub use crate::script::execute;
pub use crate::script::host;
pub use crate::script::run_source;
pub use crate::stage::ProgramSpec;
pub use crate::stage::RunDigest;
pub use crate::stage::SpecError;
pub use crate::stage::StageFault;
pub use crate::stage::StageRun;
pub use crate::stage::StageVerdict;
pub use crate::stage::Staged;
pub use crate::stage::Staging;
pub use crate::typed::Applied;
pub use crate::typed::Binding;
pub use crate::typed::ChosenDirection;
pub use crate::typed::Declared;
pub use crate::typed::DeclaredHalf;
pub use crate::typed::NameKind;
pub use crate::typed::Polarity;
pub use crate::typed::ReadBack;
pub use crate::typed::ReadSite;
pub use crate::typed::Reading;
pub use crate::typed::Referent;
pub use crate::typed::RoundTrip;
pub use crate::typed::Subject;
pub use crate::typed::TypeTable;
pub use crate::typed::TypedSpan;
pub use crate::typed::checked_against;
pub use crate::typed::crossed;
pub use crate::typed::referred;
pub use crate::typed::reprinted;
pub use crate::typed::signed;
pub use crate::typed::typing;
pub use crate::typed::wholly;
pub use crate::verdicts::AlreadyInstalled;
pub use crate::verdicts::VerdictCache;
pub use crate::verdicts::VerdictTally;
pub use crate::verdicts::install_verdict_cache;
pub use crate::verdicts::tallied;
pub use crate::verdicts::verdict_tally;
pub use crate::walk::Reached;
pub use crate::walk::SourceFault;
pub use crate::walk::Standing;
pub use crate::walk::Step;
pub use crate::walk::Traversal;
pub use crate::walk::Walk;
pub use crate::walk::walk_step;
pub use crate::width::Threads;
pub use crate::width::Width;
pub use crate::workspace::Unmembered;
pub use crate::workspace::WORKSPACE;
pub use crate::workspace::Workspace;
pub use crate::workspace::workspace_root;

/// One understood driver invocation, ready to route.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Invocation
{
    /// A bare invocation: report the toolchain-management status.
    Status,
    /// `check`: settle every declaration of the sources under `paths`.
    Check
    {
        /// Whether an unsettled obligation fails the run or is reported as a
        /// goal.
        goals: Goals,
        /// Where each lint reports its findings: within its attributes, or
        /// everywhere for a lint the run enables.
        lints: Lints,
        /// The host operations every held capability is bounded by.
        grant: HostGrant,
        /// The sources and directories of sources to check, in order.
        paths: Vec<PathBuf>,
        /// The threads the sources are parsed and lowered on.
        width: Width,
    },
    /// `test`: the same pass as `check`, reporting every fixture.
    Test
    {
        /// The sources and directories of sources to test, in order.
        paths: Vec<PathBuf>,
        /// The threads the sources are parsed and lowered on.
        width: Width,
    },
    /// `run`: run the program the source at `path` holds, its entry given
    /// `arguments`.
    Run
    {
        /// The source file.
        path: PathBuf,
        /// The arguments the program's entry reads, in order.
        arguments: Vec<String>,
    },
    /// `stage`: check staging observer programs, in order, through one
    /// memo.
    Stage
    {
        /// The programs, in order.
        programs: Vec<ProgramSpec>,
        /// The threads each program's stages fork onto.
        width: Width,
    },
    /// `fmt`: lay out the sources under `paths` at a page width.
    Format
    {
        /// The sources and directories of sources to lay out, in order.
        paths: Vec<PathBuf>,
        /// The page each source is laid out at.
        options: gandr_surface_format::FormatOptions,
        /// What a source whose layout changes becomes.
        rewrite: Rewrite,
        /// The threads the sources are laid out on.
        width: Width,
    },
    /// `ledger`: generate a ledger of the language surface and write it, or
    /// verify its exemplars.
    Ledger(LedgerTask),
    /// `cells`: report the rewriting cells of the sources under `paths`, each
    /// hole with how many times its cell's right-hand side writes it.
    Cells
    {
        /// The sources and directories of sources to read, in order.
        paths: Vec<PathBuf>,
    },
}

/// What an invocation routed to, for the driver to render.
#[derive(Debug)]
pub enum Outcome
{
    /// The toolchain-management status report.
    Status(StatusReport),
    /// A walk over sources, run by `verb`.
    Run
    {
        /// The verb whose output and gate the walk is rendered under.
        verb: Verb,
        /// Where each lint reports its findings.
        lints: Lints,
        /// The walk, not yet started.
        walk: Walk,
        /// The width to visit the walk at.
        width: Width,
    },
    /// A source file to run as a program, not yet read.
    Script(Script),
    /// Staging observer programs to check, not yet built.
    Stage(Staging),
    /// Sources to lay out, not yet read.
    Format(Formatting),
    /// A ledger to generate and write, or whose exemplars to verify, not yet
    /// run.
    Ledger(LedgerTask),
    /// Sources whose cells to report, not yet read.
    Cells(Census),
}

/// The toolchain-management status, rendered by the driver.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StatusReport;

impl core::fmt::Display for StatusReport
{
    /// Render the status line's message body.
    ///
    /// # Specification
    /// - requires: nothing; the report carries no state to render.
    /// - ensures: writes one sentence and no line terminator, so the driver
    ///   owns the line the message sits on.
    /// - provides: the body of the status line the driver prints on a bare
    ///   invocation.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    /// - executable: none — the formatter exposes write status, not emitted
    ///   text, so the absence of a line terminator cannot be checked here.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the parameterless report is rendered without CR or
    ///   LF, distinguishing an extra line break. The wording and arbitrary
    ///   rejecting sinks are outside this observation.
    /// - witness: `tests::status_routes_to_the_status_report`
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        f.write_str(
            "toolchain management is not yet implemented; see https://github.com/gandr-lang/gandr",
        )
    }
}

/// Route one invocation to its outcome.
///
/// # Specification
/// - requires: nothing; every [`Invocation`] variant routes.
/// - ensures: each variant maps to exactly one [`Outcome`] variant: a bare
///   invocation to the status report, `check` to a walk run under
///   [`Verb::Check`] with the same goals and lints settings, under its grant,
///   and `test` to a walk run under [`Verb::Test`] with every lint at its
///   attributes and no grant, each walk over the invocation's paths in order at
///   the invocation's width; `run` to a [`Script`] of its path; `stage` to a
///   [`Staging`] of its programs, in order, at its width; `fmt` to a
///   [`Formatting`] of its paths, in order, at its page and rewrite; `ledger`
///   to its [`LedgerTask`] unchanged; `cells` to a [`Census`] of its paths, in
///   order. Routing performs no I/O of its own: a walk, a script, a formatting
///   or a census reads nothing until it is advanced, a staging builds nothing
///   until it runs, a ledger task builds and writes nothing until it runs, and
///   building the grammar a walk parses with is computation. The optional
///   `tracing` feature reports a span to the caller's subscriber.
/// - provides: the outcome the driver renders.
/// - fails: never; routing is total over the invocation vocabulary.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — all eight invocation variants and both goals policies
///   have exact outcomes. Missing-path fixtures observe the first routed path
///   and the script, formatting and census paths; they do not enumerate
///   arbitrary path lists or prove the complete walk order, which has its own
///   witnesses.
/// - witness: `tests::status_routes_to_the_status_report`
/// - witness: `tests::check_routes_to_a_walk_under_the_check_verb`
/// - witness: `tests::the_test_verb_routes_to_a_walk`
/// - witness: `tests::the_run_verb_routes_to_a_script`
/// - witness: `tests::the_stage_verb_routes_to_a_staging`
/// - witness: `tests::the_format_verb_routes_to_a_formatting`
/// - witness: `tests::the_ledger_verb_routes_to_its_task`
/// - witness: `tests::the_cells_verb_routes_to_a_census`
#[cfg_attr(feature = "tracing", tracing::instrument(skip_all))]
#[inline]
#[must_use]
#[spec(
    captures: [
        status = matches!(invocation, Invocation::Status),
        censused = matches!(invocation, Invocation::Cells { .. }),
        verb = match &invocation {
            &Invocation::Check { goals, lints, width, .. } => Some((Verb::Check(goals), lints, width)),
            &Invocation::Test { width, .. } => Some((Verb::Test, Lints::default(), width)),
            &Invocation::Status | &Invocation::Run { .. } | &Invocation::Stage { .. }
                | &Invocation::Format { .. } | &Invocation::Ledger(_) | &Invocation::Cells { .. } => None,
        },
        staged = match &invocation {
            &Invocation::Stage { ref programs, width } => Some((programs.clone(), width)),
            &Invocation::Status | &Invocation::Check { .. } | &Invocation::Test { .. }
                | &Invocation::Run { .. } | &Invocation::Format { .. } | &Invocation::Ledger(_)
                | &Invocation::Cells { .. } => None,
        },
        formatted = match &invocation {
            &Invocation::Format { options, rewrite, width, .. } => Some((options, rewrite, width)),
            &Invocation::Status | &Invocation::Check { .. } | &Invocation::Test { .. }
                | &Invocation::Run { .. } | &Invocation::Stage { .. } | &Invocation::Ledger(_)
                | &Invocation::Cells { .. } => None,
        },
        ledgered = match &invocation {
            &Invocation::Ledger(ref task) => Some(task.clone()),
            &Invocation::Status | &Invocation::Check { .. } | &Invocation::Test { .. }
                | &Invocation::Run { .. } | &Invocation::Stage { .. } | &Invocation::Format { .. }
                | &Invocation::Cells { .. } => None,
        },
    ],
    ensures: |ref ret| match *ret {
        Outcome::Status(_) => status,
        Outcome::Run { verb: routed, lints, width, .. } => Some((routed, lints, width)) == verb,
        Outcome::Script(_) => !status && !censused && verb.is_none() && staged.is_none()
            && formatted.is_none() && ledgered.is_none(),
        Outcome::Stage(ref staging) =>
            staged.as_ref().is_some_and(|&(ref programs, width)|
                staging.programs() == programs.as_slice() && staging.width() == width),
        Outcome::Format(ref formatting) =>
            formatted == Some((formatting.options(), formatting.rewrite(), formatting.width())),
        Outcome::Ledger(ref task) => ledgered.as_ref() == Some(task),
        Outcome::Cells(_) => censused,
    },
)]
pub fn dispatch(invocation: Invocation) -> Outcome
{
    match invocation {
        Invocation::Status => Outcome::Status(StatusReport),
        Invocation::Check {
            goals,
            lints,
            grant,
            paths,
            width,
        } => Outcome::Run {
            verb: Verb::Check(goals),
            lints,
            walk: Walk::new(paths).granting(grant),
            width,
        },
        Invocation::Test { paths, width } => Outcome::Run {
            verb: Verb::Test,
            lints: Lints::default(),
            walk: Walk::new(paths),
            width,
        },
        Invocation::Run { path, arguments } => {
            let mut script = Script::new(path);
            script.pass(arguments);
            Outcome::Script(script)
        },
        Invocation::Stage { programs, width } => Outcome::Stage(Staging::new(programs, width)),
        Invocation::Format {
            paths,
            options,
            rewrite,
            width,
        } => Outcome::Format(Formatting::new(paths, options, rewrite, width)),
        Invocation::Ledger(task) => Outcome::Ledger(task),
        Invocation::Cells { paths } => Outcome::Cells(Census::new(paths)),
    }
}

#[cfg(test)]
mod tests
{
    use core::ops::ControlFlow;
    use std::path::PathBuf;

    use anodized::spec;
    use gandr_surface_diagnostics::Lint;
    use quenchant_shape::shape::Maybe;

    use super::Goals;
    use super::HostGrant;
    use super::Invocation;
    use super::Lints;
    use super::Outcome;
    use super::Pool;
    use super::ScriptRun;
    use super::StatusReport;
    use super::Step;
    use super::Threads;
    use super::Verb;
    use super::Width;
    use super::dispatch;

    /// The first fault a walk over `paths` reports, which names the first path
    /// it visited when no path exists.
    ///
    /// # Specification
    /// - requires: a run outcome whose first step is a fault.
    /// - ensures: the path carried by that first fault.
    /// - fails: never on the admitted domain.
    /// - panics: a non-run outcome or non-fault first step violates the
    ///   precondition.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — missing paths distinguish the first routed path under
    ///   both check policies and test. Other outcomes and successful first
    ///   steps are outside this helper's admitted domain.
    /// - witness: `tests::check_routes_to_a_walk_under_the_check_verb`
    /// - witness: `tests::the_test_verb_routes_to_a_walk`
    #[spec(requires: matches!(outcome, Outcome::Run { .. }))]
    fn first_fault_path(outcome: Outcome) -> PathBuf
    {
        let Outcome::Run { walk, .. } = outcome
        else {
            panic!("a verb routes to a walk");
        };
        let ControlFlow::Break(path) = walk.visit(&Pool::new(Width::SERIAL), |step| match step {
            Step::Fault { path, .. } => ControlFlow::Break(path.to_path_buf()),
            Step::Source { .. } => panic!("an absent path faults"),
        })
        else {
            panic!("an absent path faults");
        };
        path
    }

    /// A bare invocation routes to the status report.
    #[test]
    fn status_routes_to_the_status_report()
    {
        let outcome = dispatch(Invocation::Status);
        assert!(
            matches!(outcome, Outcome::Status(StatusReport)),
            "a bare invocation reports the status"
        );
        let rendered = std::format!("{StatusReport}");
        assert!(!rendered.contains(['\n', '\r']));
    }

    /// `check` keeps its goals and lints settings, its width and its paths'
    /// order.
    #[test]
    fn check_routes_to_a_walk_under_the_check_verb()
    {
        let three = Width::Threads(Threads::from(
            core::num::NonZeroUsize::MIN.saturating_add(2),
        ));
        for (goals, lints, width) in [
            (Goals::Gated, Lints::default(), Width::SERIAL),
            (
                Goals::Reported,
                Lints::enabling([Lint::ExplicitExits]),
                three,
            ),
        ] {
            let paths = vec![
                PathBuf::from("no/such/first.gandr"),
                PathBuf::from("no/such/second.gandr"),
            ];
            let outcome = dispatch(Invocation::Check {
                goals,
                lints,
                grant: HostGrant::UNBOUNDED,
                paths,
                width,
            });
            assert!(
                matches!(outcome, Outcome::Run { verb: Verb::Check(routed), lints: routed_lints, width: routed_width, .. }
                    if routed == goals && routed_lints == lints && routed_width == width),
                "check routes under its own goals and lints settings and width"
            );
            assert_eq!(
                first_fault_path(outcome),
                PathBuf::from("no/such/first.gandr"),
                "the walk starts at the first path given"
            );
        }
    }

    /// `test` routes to a walk under the test verb, at its width.
    #[test]
    fn the_test_verb_routes_to_a_walk()
    {
        let outcome = dispatch(Invocation::Test {
            paths: vec![PathBuf::from("no/such/only.gandr")],
            width: Width::PerformanceCores,
        });
        assert!(
            matches!(outcome, Outcome::Run {
                verb: Verb::Test,
                width: Width::PerformanceCores,
                ..
            }),
            "test routes under the test verb at its width"
        );
        assert_eq!(
            first_fault_path(outcome),
            PathBuf::from("no/such/only.gandr"),
            "the walk visits the path given"
        );
    }

    /// `run` routes to a script of its one path.
    #[test]
    fn the_run_verb_routes_to_a_script()
    {
        let outcome = dispatch(Invocation::Run {
            path: PathBuf::from("no/such/script.gandr"),
            arguments: Vec::new(),
        });
        let Outcome::Script(mut script) = outcome
        else {
            panic!("run routes to a script");
        };
        let ScriptRun::Fault { path, .. } = script.run(&mut crate::Captured::default())
        else {
            panic!("an absent script faults");
        };
        assert_eq!(
            path,
            PathBuf::from("no/such/script.gandr"),
            "the script reads the path given"
        );
    }

    /// `stage` routes to a staging of its programs, in order, at its width.
    #[test]
    fn the_stage_verb_routes_to_a_staging()
    {
        let programs: Vec<super::ProgramSpec> = ["double:0..4", "pow:2..3"]
            .iter()
            .map(|spelling| spelling.parse().expect("a program spelling"))
            .collect();
        let outcome = dispatch(Invocation::Stage {
            programs: programs.clone(),
            width: Width::PerformanceCores,
        });
        let Outcome::Stage(staging) = outcome
        else {
            panic!("stage routes to a staging");
        };
        assert_eq!(staging.programs(), programs.as_slice());
        assert_eq!(staging.width(), Width::PerformanceCores);
    }

    /// `fmt` routes to a formatting of its paths, in order, at its page and
    /// rewrite.
    #[test]
    fn the_format_verb_routes_to_a_formatting()
    {
        let options = gandr_surface_format::FormatOptions {
            page: gandr_surface_format::PageWidth::from(40_u32),
            ..gandr_surface_format::FormatOptions::default()
        };
        let outcome = dispatch(Invocation::Format {
            paths: vec![
                PathBuf::from("no/such/first.gandr"),
                PathBuf::from("no/such/second.gandr"),
            ],
            options,
            rewrite: super::Rewrite::Check,
            width: Width::PerformanceCores,
        });
        let Outcome::Format(mut formatting) = outcome
        else {
            panic!("fmt routes to a formatting");
        };
        assert_eq!(formatting.options(), options);
        assert_eq!(formatting.rewrite(), super::Rewrite::Check);
        assert_eq!(formatting.width(), Width::PerformanceCores);
        let Maybe::Present(super::FormatStep::Fault { path, .. }) = formatting.step()
        else {
            panic!("an absent path faults");
        };
        assert_eq!(
            path,
            PathBuf::from("no/such/first.gandr"),
            "the formatting starts at the first path given"
        );
    }

    /// `ledger` routes to its task unchanged, building and writing nothing.
    #[test]
    fn the_ledger_verb_routes_to_its_task()
    {
        let task = super::LedgerTask::Syntax {
            directory: PathBuf::from("no/such/ledger"),
            exemplars: PathBuf::from("no/such/ledger/exemplars"),
        };
        let outcome = dispatch(Invocation::Ledger(task.clone()));
        let Outcome::Ledger(routed) = outcome
        else {
            panic!("ledger routes to its task");
        };
        assert_eq!(routed, task);
        assert!(
            !std::path::Path::new("no/such/ledger").exists(),
            "routing writes nothing"
        );
    }

    /// `cells` routes to a census of its paths, in order, reading nothing
    /// until it steps.
    #[test]
    fn the_cells_verb_routes_to_a_census()
    {
        let outcome = dispatch(Invocation::Cells {
            paths: vec![
                PathBuf::from("no/such/first.gandr"),
                PathBuf::from("no/such/second.gandr"),
            ],
        });
        let Outcome::Cells(mut census) = outcome
        else {
            panic!("cells routes to a census");
        };
        let Maybe::Present(super::CensusStep::Fault { path, .. }) = census.step()
        else {
            panic!("an absent path faults");
        };
        assert_eq!(
            path,
            PathBuf::from("no/such/first.gandr"),
            "the census starts at the first path given"
        );
    }
}
