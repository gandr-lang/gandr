//! The session: one call per revision that lowers, judges, resumes and
//! persists, and the submission it reports.
//!
//! # Lowered once, judged whole, resumed beside it
//!
//! A submission lowers its revision once. The lowered module goes two ways:
//! the dispatcher's [`judge_module`] judges, readmits and settles it, which is
//! the report — the same verdicts `gandr check` gives the text — and the item
//! source's [`program`] offers the same declarations to the incremental
//! checker, which adopts every checkpoint that still answers, judges the rest
//! and persists the set. A revision the lowering refuses as a whole is
//! reported and leaves the session as it was.
//!
//! # The parse's repairs ride beside the step
//!
//! The step a face renders carries the composition, which holds no trace of
//! the repairs the parser made to reach a tree. The submission carries them:
//! the parse's completion obligations, taken from the lowering before it is
//! consumed, on every path, re-sorted from the parse's severity order into
//! source order because a reader meets them in the text.
//!
//! # The kernel checkpoint is records, trusted only through the decoder
//!
//! Each accepted revision's kernel artifact — what the dispatcher's
//! readmission let cross, exported once — is cut at the decoder's segment
//! boundaries and committed into the session's block store as records, and
//! the submission carries the manifest that names them. Reading it back,
//! from this session or one reopened over the same block store, re-seals the
//! stored tree against the manifest and hands the bytes to the kernel's
//! bounded decoder: a manifest whose identity matches never stands in for the
//! decoder's admission.

use core::fmt;
use std::path::Path;

use gandr_core_checker::CheckBudget;
use gandr_core_checker::Verdict;
use gandr_core_incremental::BackendArtifact;
use gandr_core_incremental::CheckpointObserver;
use gandr_core_incremental::CheckpointStore;
use gandr_core_incremental::CheckpointStoreError;
use gandr_core_incremental::IncrementalSession;
use gandr_core_incremental::ItemCount;
use gandr_core_incremental::ProgramError;
use gandr_core_incremental::Resume;
use gandr_core_incremental::ResumeCensus;
use gandr_core_incremental::ResumeError;
use gandr_core_incremental::SessionError;
use gandr_core_incremental::SynthesisStream;
use gandr_core_incremental::address_of;
use gandr_core_incremental::restore;
use gandr_core_incremental::restored;
use gandr_core_incremental::submitted;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DecodedArtifact;
use gandr_kernel_term::EncodedArtifact;
use gandr_storage_artifact::ArtifactError;
use gandr_storage_artifact::ArtifactManifest;
use gandr_storage_artifact::ArtifactRecordSet;
use gandr_storage_artifact::build;
use gandr_storage_records::BlockStore;
use gandr_storage_records::TreeParams;
use gandr_surface_corpus::DeclarationReport;
use gandr_surface_corpus::Produced;
use gandr_surface_dispatcher::ComposeFault;
use gandr_surface_dispatcher::Composed;
use gandr_surface_dispatcher::Evaluation;
use gandr_surface_dispatcher::Lowered;
use gandr_surface_dispatcher::LoweringCount;
use gandr_surface_dispatcher::Program;
use gandr_surface_dispatcher::SourceRoot;
use gandr_surface_dispatcher::Standing;
use gandr_surface_dispatcher::Step;
use gandr_surface_dispatcher::judge_module;
use gandr_surface_dispatcher::lower_source;
use gandr_surface_grammar::Pbg;
use gandr_surface_lowering::ImportIndex;
use gandr_surface_lowering::ImportUri;
use gandr_surface_lowering::LoweredModule;
use gandr_surface_lowering::namespace::NamePath;
use gandr_surface_lowering::namespace::Scope;
use gandr_surface_parser::ObligationInstance;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::edit::EditScript;
use crate::edit::Snapshot;
use crate::edit::diff;
use crate::item_source::program;

quenchant_shape::reason_enum! {
    /// Why a submission carries no resume.
    pub mod resumed {
        /// The reason none is carried.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The lowering refused the revision as a whole, so it offered no
            /// items to resume over.
            RefusedWhole,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a session declines to evaluate an item.
    pub mod evaluation {
        /// The reason nothing runs.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The declaration is owed its body: a hole, which declines
            /// evaluation.
            Holed,
            /// No declaration the checker accepted sits at the position: it
            /// was refused, the position holds none, or the revision was
            /// refused as a whole.
            Unaccepted,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a path resolves to no import.
    pub mod import {
        /// The reason none resolves.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The latest accepted revision binds no import at the path.
            Unbound,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a reopened session restored no checkpoints.
    pub mod reopened {
        /// The reason none was restored.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The lowering refused the revision as a whole, so it has no
            /// program to restore checkpoints for.
            RefusedWhole,
            /// The store holds no checkpoints for the revision's program.
            NotStored,
            /// The checkpoints held for it were judged by another backend.
            OtherBackend,
            /// The address restored at is not the revision's program's.
            AddressMismatch,
        }
    }
}

/// An observer that takes no part: the session reports persistence through
/// the submission, not through events.
struct Quiet;

impl CheckpointObserver for Quiet
{
}

/// One import of the latest accepted revision, owned so it outlives the text
/// that declared it.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct ImportRow
{
    /// The address the import names.
    uri: ImportUri,
    /// The bytes the import declaration covered in its revision.
    span: ByteSpan,
}

impl ImportRow
{
    /// The address the import names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn uri(&self) -> &ImportUri
    {
        &self.uri
    }

    /// The bytes the import declaration covered in its revision.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn span(&self) -> ByteSpan
    {
        self.span
    }
}

/// The import scope of one revision: its rows and the namespace binding each
/// alias to its row.
#[derive(Clone, Debug)]
struct Imports
{
    /// The imports, in source order.
    rows: Vec<ImportRow>,
    /// Each alias bound to its row's position.
    scope: Scope<ImportIndex, ByteSpan>,
}

impl Imports
{
    /// The scope of a revision that declared no import.
    ///
    /// # Specification
    /// trivial.
    fn empty() -> Self
    {
        Self {
            rows: Vec::new(),
            scope: Scope::new(),
        }
    }

    /// The import scope `module` declared.
    ///
    /// # Specification
    /// trivial.
    fn of(module: &LoweredModule<'_>) -> Self
    {
        Self {
            rows: module
                .imports()
                .iter()
                .map(|declaration| ImportRow {
                    uri: declaration.uri().clone(),
                    span: declaration.span(),
                })
                .collect(),
            scope: module.import_scope().clone(),
        }
    }

    /// The row `path` resolves to.
    ///
    /// # Specification
    /// trivial.
    fn resolve(
        &self,
        path: &NamePath,
    ) -> Maybe<&ImportRow, import::Absent>
    {
        match self.scope.resolve(path) {
            // The scope and the rows are the same module's, so every position
            // the scope binds has its row.
            | Maybe::Present(binding) => match self.rows.get(usize::from(binding.data)) {
                | Some(row) => Maybe::Present(row),
                | None => Maybe::Absent(import::Absent::Unbound),
            },
            | Maybe::Absent(_) => Maybe::Absent(import::Absent::Unbound),
        }
    }
}

/// Whether a submission's checkpoints reached the store.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Persistence
{
    /// The store holds the submission's checkpoints at its program's address.
    Stored,
    /// The store refused them and holds what it held before; the session still
    /// resumes from the submission.
    Failed(CheckpointStoreError),
}

/// What the incremental checker made of an accepted submission.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Resumed
{
    /// The census of the pass: items encoded, recalled, adopted and judged.
    census: ResumeCensus,
    /// Whether the checkpoints were persisted.
    persistence: Persistence,
}

impl Resumed
{
    /// The census of the pass.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn census(&self) -> ResumeCensus
    {
        self.census
    }

    /// Whether the checkpoints were persisted.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn persistence(&self) -> Persistence
    {
        self.persistence
    }
}

/// Whether a submission's kernel checkpoint reached the block store.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum KernelCheckpoint
{
    /// The block store holds the revision's kernel artifact as records under
    /// this manifest, which [`Session::read_kernel`] reads back.
    Stored(ArtifactManifest),
    /// The artifact was not committed: its records did not form or the block
    /// store refused a node. No manifest names what reached the store, and the
    /// session still resumes from the submission.
    Failed(ArtifactError),
}

/// What one submitted revision became: the dispatcher's composition of its
/// text, its standing, and what the incremental checker made of it.
#[derive(Clone, Debug)]
pub struct Submission<'text>
{
    /// The root the session's source sits under.
    root: SourceRoot,
    /// The revision's text, which every span of `composed` is measured
    /// against.
    text: SourceText<'text>,
    /// What the revision became: the composition `gandr check` gives the same
    /// text.
    composed: Composed<'text>,
    /// How it stands against its root.
    standing: Standing,
    /// What the incremental checker made of it.
    resumed: Maybe<Resumed, resumed::Absent>,
    /// The edits from the latest accepted revision before it.
    edits: Maybe<EditScript, resumed::Absent>,
    /// Whether the revision's kernel checkpoint reached the block store.
    kernel: Maybe<KernelCheckpoint, resumed::Absent>,
    /// The parse's completion obligations, in source order.
    obligations: Vec<ObligationInstance>,
}

impl<'text> Submission<'text>
{
    /// The root the session's source sits under.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn root(&self) -> SourceRoot
    {
        self.root
    }

    /// The revision's text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn text(&self) -> SourceText<'text>
    {
        self.text
    }

    /// What the revision became.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn composed(&self) -> &Composed<'text>
    {
        &self.composed
    }

    /// How the revision stands against its root.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn standing(&self) -> Standing
    {
        self.standing
    }

    /// What the incremental checker made of the revision.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn resumed(&self) -> Maybe<Resumed, resumed::Absent>
    {
        self.resumed
    }

    /// The edits from the latest accepted revision before this one to this
    /// one: from no items at all when none was accepted before.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn edits(&self) -> Maybe<&EditScript, resumed::Absent>
    {
        match self.edits {
            | Maybe::Present(ref edits) => Maybe::Present(edits),
            | Maybe::Absent(reason) => Maybe::Absent(reason),
        }
    }

    /// Whether the revision's kernel checkpoint reached the block store, and
    /// the manifest naming it when it did.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn kernel(&self) -> Maybe<&KernelCheckpoint, resumed::Absent>
    {
        match self.kernel {
            | Maybe::Present(ref kernel) => Maybe::Present(kernel),
            | Maybe::Absent(reason) => Maybe::Absent(reason),
        }
    }

    /// The completion obligations the parse of the revision recorded, in
    /// source order: the repairs it made to reach a tree.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: exactly the obligations the parse buffered for this revision,
    ///   each class and span unchanged, ordered by span — start, then end —
    ///   rather than by the parse's severity, equal spans keeping the parse's
    ///   order; empty for a clean parse. A revision the lowering refuses as a
    ///   whole carries its obligations too.
    /// - provides: the parser's repairs, which the step a face renders does not
    ///   carry.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the surfaces are the carried set, its order and its
    ///   lifetime, separated by a clean source, a recovering source whose
    ///   severity order and source order disagree, a source refused whole, and
    ///   a clean revision after a recovering one, each asserted at its exact
    ///   rows against the parse's own buffer.
    /// - witness: `tests::diag_obligations::lowered_carries_the_parse_obligations_verbatim`
    /// - witness: `tests::diag_obligations::rows_are_in_source_order_not_severity_order`
    /// - witness: `tests::diag_obligations::a_clean_source_reports_no_obligations`
    #[inline]
    #[must_use]
    pub fn obligations(&self) -> &[ObligationInstance]
    {
        &self.obligations
    }

    /// The submission as the walk step of a source at `path`: the shape every
    /// renderer of a step reads.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a [`Step::Source`] at `path` carrying this submission's root,
    ///   text, composition and standing unchanged.
    /// - provides: the diagnostics a face renders, through the renderer the
    ///   batch verbs use.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every corpus source's submission is turned into a
    ///   step and compared field by field with the step the dispatcher's walk
    ///   yields for the same path.
    /// - witness: `tests::corpus::every_source_submits_as_the_walk_composes_it`
    #[inline]
    #[must_use]
    pub fn into_step<'step>(
        self,
        path: &'step Path,
    ) -> Step<'step>
    where
        'text: 'step,
    {
        Step::Source {
            path,
            root: self.root,
            text: self.text,
            composed: self.composed,
            standing: self.standing,
        }
    }

    /// Run the hole-free item at `constant` of this revision.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`evaluate`] over the declaration the revision's report
    ///   carries at `constant` and the program its composition built; a
    ///   position holding no declaration and a revision refused as a whole
    ///   decline with [`evaluation::Absent::Unaccepted`].
    /// - provides: the evaluation a face prints a value line from.
    /// - fails: as [`evaluate`], and the two absences the ensures clause names.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`evaluate`].
    /// - witness: `tests::session::integer_literal_types_and_evaluates`
    /// - witness: `tests::session::nullary_function_call_evaluates`
    /// - witness: `tests::session::holes_decline_evaluation`
    #[inline]
    pub fn evaluate(
        &mut self,
        constant: ConstantIndex,
    ) -> Maybe<Evaluation<'text>, evaluation::Absent>
    {
        let Composed::Settled {
            ref report,
            ref mut program,
            ..
        } = self.composed
        else {
            return Maybe::Absent(evaluation::Absent::Unaccepted);
        };
        match report
            .declarations()
            .iter()
            .find(|declaration| declaration.constant() == constant)
        {
            | Some(declaration) => evaluate(declaration, program),
            | None => Maybe::Absent(evaluation::Absent::Unaccepted),
        }
    }
}

/// Run `declaration` on `program` when it is a hole-free item: one the
/// checker accepted whole.
///
/// # Specification
/// - requires: `program` is the one the composition reporting `declaration`
///   built.
/// - ensures: a declaration whose produced verdict is checked or synthesised
///   runs as the dispatcher's run stage runs it, and what the run came to is
///   returned — a value, the blame of a goal it reaches, or why it stopped or
///   never ran. A declaration owed its body declines with
///   [`evaluation::Absent::Holed`]; one refused, by the lowering, the checker
///   or its root, declines with [`evaluation::Absent::Unaccepted`]. Nothing
///   runs for a declined item.
/// - provides: the one rule for what a session evaluates, shared by a
///   submission and by a face holding the submission's step.
/// - fails: the declining absences the ensures clause names.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an integer literal, a call of a nullary function and a
///   goal are submitted, and each asserted at its exact evaluation or absence.
/// - witness: `tests::session::integer_literal_types_and_evaluates`
/// - witness: `tests::session::nullary_function_call_evaluates`
/// - witness: `tests::session::holes_decline_evaluation`
#[inline]
pub fn evaluate<'text>(
    declaration: &DeclarationReport<'text>,
    program: &mut Program<'text>,
) -> Maybe<Evaluation<'text>, evaluation::Absent>
{
    match declaration.produced() {
        | Produced::Judged(Verdict::Checked { .. } | Verdict::Synthesised { .. }) => {
            Maybe::Present(program.evaluate(declaration.constant()))
        },
        | Produced::Judged(Verdict::Owed(_)) => Maybe::Absent(evaluation::Absent::Holed),
        | Produced::Judged(Verdict::Refused(_)) | Produced::Unlowered(_) | Produced::Guarded(_) => {
            Maybe::Absent(evaluation::Absent::Unaccepted)
        },
    }
}

/// Why a session could not take a revision, or could not reopen over one: an
/// engine fault, never a verdict about the revision.
#[derive(Clone, Debug)]
pub enum SessionFault<'text>
{
    /// The dispatcher's composition faulted.
    Compose(ComposeFault<'text>),
    /// The lowered declarations' admission positions do not ascend.
    Unordered(ProgramError),
    /// The incremental checker could not resume; the session judges its next
    /// revision whole.
    Resume(ResumeError),
    /// The checkpoint store failed while restoring, or while persisting with
    /// no resume left to report.
    Store(CheckpointStoreError),
}

impl fmt::Display for SessionFault<'_>
{
    /// Writes the fault and what it names.
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
            | Self::Compose(ref fault) => fault.fmt(f),
            | Self::Unordered(ref error) => error.fmt(f),
            | Self::Resume(ref error) => write!(f, "resume failed: {error}"),
            | Self::Store(ref error) => write!(f, "the checkpoint store failed: {error}"),
        }
    }
}

impl core::error::Error for SessionFault<'_>
{
}

/// A session reopened over a revision, and whether its checkpoints were
/// restored.
pub struct Reopened<Store, Blocks>
{
    /// The reopened session.
    session: Session<Store, Blocks>,
    /// How many items' checkpoints were restored.
    restored: Maybe<ItemCount, reopened::Absent>,
}

impl<Store, Blocks> fmt::Debug for Reopened<Store, Blocks>
{
    /// Writes the session and what was restored; the stores are opaque.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.debug_struct("Reopened")
            .field("session", &self.session)
            .field("restored", &self.restored)
            .finish()
    }
}

impl<Store, Blocks> Reopened<Store, Blocks>
{
    /// How many items' checkpoints were restored.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn restored(&self) -> Maybe<ItemCount, reopened::Absent>
    {
        self.restored
    }

    /// The reopened session.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn into_session(self) -> Session<Store, Blocks>
    {
        self.session
    }
}

/// The interactive session over successive revisions of one source.
pub struct Session<Store, Blocks>
{
    /// The grammar every revision is parsed under.
    grammar: Pbg,
    /// The root the source sits under, which decides what its expectations
    /// mean.
    root: SourceRoot,
    /// The incremental checker's latest resume and its checkpoint store.
    incremental: IncrementalSession<Store>,
    /// Where each accepted revision's kernel checkpoint is committed.
    blocks: Blocks,
    /// The import scope of the latest accepted revision.
    imports: Imports,
    /// The lowered core of the latest accepted revision.
    snapshot: Snapshot,
    /// Every lowering the session performed.
    lowerings: LoweringCount,
}

impl<Store, Blocks> fmt::Debug for Session<Store, Blocks>
{
    /// Writes the root, the latest resume and the import scope; the grammar
    /// and the stores are opaque.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.debug_struct("Session")
            .field("root", &self.root)
            .field("incremental", &self.incremental)
            .field("imports", &self.imports)
            .field("lowerings", &self.lowerings)
            .finish_non_exhaustive()
    }
}

impl<Store, Blocks> Session<Store, Blocks>
{
    /// A session with nothing submitted, parsing under `grammar` a source
    /// under `root`, persisting checkpoints into `store` as `backend` and
    /// kernel checkpoints into `blocks`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new(
        grammar: Pbg,
        root: SourceRoot,
        store: Store,
        blocks: Blocks,
        backend: BackendArtifact,
    ) -> Self
    {
        Self {
            grammar,
            root,
            incremental: IncrementalSession::new(store, backend, CheckBudget::DEFAULT),
            blocks,
            imports: Imports::empty(),
            snapshot: Snapshot::default(),
            lowerings: LoweringCount::default(),
        }
    }

    /// A session reopened over `revision`, resuming from the checkpoints
    /// `store` holds for it, its kernel checkpoints read from `blocks`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `revision` is lowered once. When the lowering reads a module
    ///   and `store` holds checkpoints `backend` judged for its program, the
    ///   session resumes from them and their item count is reported; otherwise
    ///   the session is fresh, as [`Self::new`] makes it, and the reason is
    ///   reported. Either way the session's import scope and snapshot are the
    ///   revision's, and it reads and commits kernel checkpoints in `blocks`.
    /// - provides: a session that outlives the process that wrote its
    ///   checkpoints: its next submission adopts every restored checkpoint that
    ///   still answers.
    /// - fails: [`SessionFault::Compose`] when the parser cannot commit the
    ///   revision's tree or the lowering faults; [`SessionFault::Unordered`]
    ///   when its admission positions do not ascend; [`SessionFault::Store`]
    ///   when the store fails to load; [`SessionFault::Resume`] when the
    ///   restored set holds no item order.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the surfaces are the restored resume, the fresh
    ///   fallback and the import scope, separated by a file store written by
    ///   one session, the session dropped, and a second session reopened over
    ///   the same directory whose next submission adopts every unchanged item;
    ///   and by a store that holds nothing for the revision.
    /// - witness: `tests::checkpoint::a_reopened_session_resumes_from_the_checkpoints_a_dropped_one_wrote`
    /// - witness: `tests::checkpoint::a_store_holding_nothing_reopens_fresh`
    #[inline]
    pub fn reopen(
        grammar: Pbg,
        root: SourceRoot,
        mut store: Store,
        blocks: Blocks,
        backend: BackendArtifact,
        revision: SourceText<'_>,
    ) -> Result<Reopened<Store, Blocks>, SessionFault<'_>>
    where
        Store: CheckpointStore,
    {
        let mut lowerings = LoweringCount::default();
        let lowering =
            lower_source(&grammar, revision, &mut lowerings).map_err(SessionFault::Compose)?;
        let (imports, snapshot, restored) = match lowering.into_lowered() {
            | Lowered::Refused(_) => (
                Imports::empty(),
                Snapshot::default(),
                Maybe::Absent(reopened::Absent::RefusedWhole),
            ),
            | Lowered::Module { module, arena } => {
                let program = program(&module, arena).map_err(SessionFault::Unordered)?;
                let address = address_of(&program).map_err(SessionFault::Store)?;
                let restored = match restore(&mut store, &program, address, backend, &mut Quiet)
                    .map_err(SessionFault::Store)?
                {
                    | Maybe::Present(checkpoints) => {
                        let count = ItemCount::from(checkpoints.items().len());
                        let resume =
                            Resume::from_checkpoints(checkpoints).map_err(SessionFault::Resume)?;
                        Maybe::Present((resume, count))
                    },
                    | Maybe::Absent(reason) => Maybe::Absent(unrestored(reason)),
                };
                (
                    Imports::of(&module),
                    Snapshot::of(&program, module.origins()),
                    restored,
                )
            },
        };
        let (incremental, restored) = match restored {
            | Maybe::Present((resume, count)) => (
                IncrementalSession::reopen(store, backend, resume),
                Maybe::Present(count),
            ),
            | Maybe::Absent(reason) => (
                IncrementalSession::new(store, backend, CheckBudget::DEFAULT),
                Maybe::Absent(reason),
            ),
        };
        Ok(Reopened {
            session: Self {
                grammar,
                root,
                incremental,
                blocks,
                imports,
                snapshot,
                lowerings,
            },
            restored,
        })
    }

    /// Submit one revision: lower it, judge it, resume the incremental checker
    /// over it and persist its checkpoints and its kernel checkpoint.
    ///
    /// # Specification
    /// - requires: `revision` is the whole text of the session's source.
    /// - ensures: `revision` is lowered exactly once, and the lowering count is
    ///   one more. A revision the lowering reads is judged by the dispatcher's
    ///   [`judge_module`] — the composition `gandr check` gives the same text
    ///   under the same root — and the same declarations are submitted to the
    ///   incremental checker, which resumes from the latest accepted revision
    ///   and persists the new checkpoints; the composition's kernel artifact is
    ///   committed into the block store as records; the submission carries the
    ///   [`diff`] of the latest accepted revision's snapshot and this one's,
    ///   and the session then holds the revision's resume, import scope and
    ///   snapshot. A revision the lowering refuses as a whole is reported as
    ///   [`Composed::Refused`] with no resume, no edits and no kernel
    ///   checkpoint, and the session is unchanged. Either way the submission
    ///   carries the parse's completion obligations, in source order.
    /// - provides: a report whose verdicts are the batch pipeline's, beside the
    ///   census of what the resume adopted, the manifest of the kernel
    ///   environment it leaves, the edits that led to it and the repairs the
    ///   parser made.
    /// - fails: [`SessionFault::Compose`] when the composition faults, with the
    ///   session unchanged; [`SessionFault::Unordered`] when the lowered
    ///   positions do not ascend, unchanged; [`SessionFault::Resume`] when the
    ///   resume fails, the incremental checker then holding no resume so the
    ///   next revision is judged whole.
    /// - panics: none.
    /// - economy: the lowered arena is cloned once per accepted revision, so
    ///   the judgement and the resume each check over their own copy; the
    ///   snapshot and its diff are each one walk of the revision's terms; the
    ///   kernel artifact is decoded, cut and hashed once, linear in its bytes.
    ///
    /// # Errors
    /// As above. A failure to persist is not an error: the submission
    /// reports it as [`Persistence::Failed`] or [`KernelCheckpoint::Failed`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 for the report — every source of both corpus roots is
    ///   submitted whole and its submission compared with the dispatcher's step
    ///   for the same path, field by field; L3 for the session state —
    ///   successive revisions asserted at the census, the synthesis stream and
    ///   the import scope they leave, a refused revision asserted to leave them
    ///   unchanged, and the kernel checkpoint read back as exactly the decoding
    ///   of the composition's artifact.
    /// - witness: `tests::corpus::every_source_submits_as_the_walk_composes_it`
    /// - witness: `tests::session::whole_file_submit_carries_definitions_forward`
    /// - witness: `tests::session::successful_submissions_publish_whole_program_synthesis`
    /// - witness: `tests::session::import_namespace_carries_across_lines_and_resolves_source_declarations`
    /// - witness: `tests::edit::a_submission_carries_the_edits_from_the_last_accepted_revision`
    /// - witness: `tests::diag_obligations::lowered_carries_the_parse_obligations_verbatim`
    /// - witness: `tests::checkpoint::a_reopened_session_reads_its_kernel_checkpoint_through_the_decoder`
    #[inline]
    pub fn submit<'text>(
        &mut self,
        revision: SourceText<'text>,
    ) -> Result<Submission<'text>, SessionFault<'text>>
    where
        Store: CheckpointStore,
        Blocks: BlockStore,
    {
        let lowering = lower_source(&self.grammar, revision, &mut self.lowerings)
            .map_err(SessionFault::Compose)?;
        let mut obligations = lowering.obligations().to_vec();
        obligations.sort_by_key(|obligation| obligation.span);
        let (module, arena) = match lowering.into_lowered() {
            | Lowered::Module { module, arena } => (module, arena),
            | Lowered::Refused(refusal) => {
                let composed = Composed::Refused(refusal);
                return Ok(Submission {
                    root: self.root,
                    text: revision,
                    standing: Standing::of(self.root, &composed),
                    composed,
                    resumed: Maybe::Absent(resumed::Absent::RefusedWhole),
                    edits: Maybe::Absent(resumed::Absent::RefusedWhole),
                    kernel: Maybe::Absent(resumed::Absent::RefusedWhole),
                    obligations,
                });
            },
        };
        // economy: one arena copy per accepted revision; the reversal is a
        // report assembled from the resume's own verdicts, which retires the
        // whole-module judgement and this copy with it.
        let mut items = program(&module, arena.clone()).map_err(SessionFault::Unordered)?;
        let imports = Imports::of(&module);
        let snapshot = Snapshot::of(&items, module.origins());
        let composed =
            judge_module(self.root.corpus_root(), module, arena).map_err(SessionFault::Compose)?;
        let (census, persistence) = match self.incremental.submit(&mut items, &mut Quiet) {
            | Ok(census) => (census, Persistence::Stored),
            | Err(SessionError::Resume(error)) => return Err(SessionFault::Resume(error)),
            // The incremental session keeps the new resume when persisting
            // fails; were it to hold none, there is no census to report, so
            // the store's failure fails the submission instead.
            | Err(SessionError::Store(error)) => match self.incremental.last() {
                | Maybe::Present(resume) => (resume.census(), Persistence::Failed(error)),
                | Maybe::Absent(_) => return Err(SessionFault::Store(error)),
            },
        };
        let kernel = match composed {
            | Composed::Settled { ref kernel, .. } => {
                Maybe::Present(checkpoint_kernel(kernel, &mut self.blocks))
            },
            | Composed::Refused(_) => Maybe::Absent(resumed::Absent::RefusedWhole),
        };
        let edits = diff(&self.snapshot, &snapshot);
        self.imports = imports;
        self.snapshot = snapshot;
        Ok(Submission {
            root: self.root,
            text: revision,
            standing: Standing::of(self.root, &composed),
            composed,
            resumed: Maybe::Present(Resumed {
                census,
                persistence,
            }),
            edits: Maybe::Present(edits),
            kernel,
            obligations,
        })
    }

    /// The root the session's source sits under.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn root(&self) -> SourceRoot
    {
        self.root
    }

    /// The grammar every revision is parsed under.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn grammar(&self) -> &Pbg
    {
        &self.grammar
    }

    /// Every lowering the session performed: one per submission.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn lowerings(&self) -> LoweringCount
    {
        self.lowerings
    }

    /// The resume of the latest accepted revision: its typings, adoptions and
    /// item order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn last(&self) -> Maybe<&Resume, submitted::Absent>
    {
        self.incremental.last()
    }

    /// The synthesis stream of the latest accepted revision.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn stream(&self) -> Maybe<SynthesisStream, submitted::Absent>
    {
        self.incremental.stream()
    }

    /// The import of the latest accepted revision `path` names.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the row of the import whose alias the latest accepted
    ///   revision bound at `path`, or [`import::Absent::Unbound`] when it bound
    ///   none there; before any accepted revision every path is unbound.
    /// - provides: the import scope persisting across submissions: a revision
    ///   the lowering refuses — among them one declaring an alias twice —
    ///   leaves the scope of the revision before it.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the surfaces are a bound alias, an unbound path and a
    ///   refused revision, separated by two accepted revisions each resolving
    ///   its own aliases and a third declaring an alias twice that leaves the
    ///   second's scope.
    /// - witness: `tests::session::import_namespace_carries_across_lines_and_resolves_source_declarations`
    #[inline]
    pub fn resolve_import(
        &self,
        path: &NamePath,
    ) -> Maybe<&ImportRow, import::Absent>
    {
        self.imports.resolve(path)
    }

    /// The lowered core of the latest accepted revision, empty before any:
    /// what a source range of that revision is localized against.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn snapshot(&self) -> &Snapshot
    {
        &self.snapshot
    }

    /// Reads the kernel checkpoint `manifest` names back from the block store,
    /// through the kernel's decoder.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: exactly [`ArtifactManifest::read_under`] over the session's
    ///   block store at the current tree parameters: the decoded artifact when
    ///   the manifest's profile and kernel format are the session's, the stored
    ///   tree seals to the manifest's root, every key and cut is the decoder's,
    ///   and the kernel's bounded decoder admits the bytes; otherwise the first
    ///   refusal, in that order.
    /// - provides: the one way a session trusts a kernel checkpoint: a manifest
    ///   whose identity matches never stands in for the decoder.
    /// - fails: as [`ArtifactManifest::read_under`].
    /// - panics: none.
    ///
    /// # Errors
    /// [`ArtifactError`], as [`ArtifactManifest::read_under`] names it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a kernel checkpoint one session wrote, its manifest
    ///   carried as bytes, reads back from a session reopened over the same
    ///   block store as exactly the decoding of the composition's artifact; and
    ///   a manifest minted over bytes the kernel refuses, whose identity its
    ///   own bytes reproduce and whose tree the block store holds and seals, is
    ///   refused by the decoder.
    /// - witness: `tests::checkpoint::a_reopened_session_reads_its_kernel_checkpoint_through_the_decoder`
    /// - witness: `tests::checkpoint::a_matching_identity_over_bytes_the_kernel_refuses_is_refused`
    #[inline]
    pub fn read_kernel(
        &self,
        manifest: &ArtifactManifest,
    ) -> Result<DecodedArtifact, ArtifactError>
    where
        Blocks: BlockStore,
    {
        manifest.read_under(&self.blocks, TreeParams::current())
    }

    /// The block store the session commits kernel checkpoints into.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn blocks(&self) -> &Blocks
    {
        &self.blocks
    }

    /// The checkpoint store, once the session is done.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn into_store(self) -> Store
    {
        self.incremental.into_store()
    }
}

/// Commits `kernel` into `blocks` as artifact records under the current tree
/// parameters.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`KernelCheckpoint::Stored`] with the manifest [`build`] mints
///   over the records [`ArtifactRecordSet::from_artifact`] cuts from `kernel`,
///   every node of their tree then in `blocks`; otherwise
///   [`KernelCheckpoint::Failed`] with the first refusal.
/// - provides: the kernel checkpoint an accepted submission carries.
/// - fails: never; a refusal is the checkpoint's own variant.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the checkpoint a submission carries reads back as exactly
///   the decoding of the composition's artifact.
/// - witness: `tests::checkpoint::a_reopened_session_reads_its_kernel_checkpoint_through_the_decoder`
fn checkpoint_kernel<Blocks>(
    kernel: &EncodedArtifact,
    blocks: &mut Blocks,
) -> KernelCheckpoint
where
    Blocks: BlockStore,
{
    let committed = ArtifactRecordSet::from_artifact(kernel.as_image())
        .and_then(|records| build(&records, TreeParams::current(), blocks));
    match committed {
        | Ok(manifest) => KernelCheckpoint::Stored(manifest),
        | Err(refusal) => KernelCheckpoint::Failed(refusal),
    }
}

/// The reason a restore's absence gives a reopened session.
///
/// # Specification
/// trivial.
const fn unrestored(reason: restored::Absent) -> reopened::Absent
{
    match reason {
        | restored::Absent::AddressMismatch => reopened::Absent::AddressMismatch,
        | restored::Absent::NotStored => reopened::Absent::NotStored,
        | restored::Absent::OtherBackend => reopened::Absent::OtherBackend,
    }
}
