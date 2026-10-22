//! The session: one call per revision that lowers, judges, resumes and
//! persists, and the submission it reports.
//!
//! # Lowered once, judged whole, resumed beside it
//!
//! A submission lowers its revision once. The lowered module goes two ways:
//! the dispatcher's [`judge`](gandr_surface_dispatcher::judge) judges and
//! settles it, which is the report — the same verdicts `gandr check` gives the
//! text — and the item source's [`program`] offers the same declarations to the
//! incremental checker, which adopts every checkpoint that still answers,
//! judges the rest and persists the set. A revision the lowering refuses as a
//! whole is reported and leaves the session as it was.
//!
//! # The kernel admission runs after the report exists
//!
//! [`Session::submit`] is [`Session::judge`] then [`Session::admit`]. The
//! judgement is the interactive half: parse, lowering, judgement, settle and
//! resume, everything a face renders. The admission offers the judged
//! revision's accepted declarations to the kernel, exports what crossed and
//! commits the export, the half whose cost grows with the whole module
//! whatever the edit. A face that judges, renders, and then admits shows its
//! reports before the kernel has re-derived them; a kernel disagreement found
//! afterwards is reported as the fault it is, the session holding the judged
//! revision.
//!
//! **Choice.** A submission is two calls. `Session::judge` parses, lowers,
//! judges and settles the revision and resumes the incremental checker over it:
//! everything a face renders. `Session::admit` then offers the judged
//! revision's accepted declarations to the kernel, exports the artifact of what
//! crossed and commits it. A face renders between the two, so its diagnostics
//! never wait on the kernel. A later `judge` drops an admission the earlier one
//! left unrun, so a face that falls behind admits only the latest revision.
//! `submit` is the two calls in order, and its submission equals the one-step
//! composition, kernel artifact included.
//!
//! **Why the admission is the half that waits.** The admission re-derives every
//! accepted declaration in a fresh kernel environment, and the export encodes
//! every declaration that crossed. Both are linear in the module whatever the
//! edit. The kernel's memo of acceptances has no authority and no persistence,
//! so a key that carried acceptances from one revision to the next would be
//! persistence under another name. The admission therefore stays whole, and
//! leaves the interactive path instead. The settle comparison and the program a
//! face evaluates on read only the judgement's verdicts, never what the
//! admission mints, so a judgement settled before the admission settles to the
//! same report. The dispatcher's `a_judged_module_renders_before_its_admission`
//! checks that order against the one-step composition.
//!
//! **Disagreement.** A kernel that does not re-derive an acceptance is a fault,
//! never a verdict. When the judgement's settle comparison refuses the
//! verdicts, `judge` runs the admission there and reports a disagreement first,
//! as the one-step composition does. When `admit` finds one later, it returns
//! the fault, and the session holds the judged revision.
//!
//! **Alternatives.** The admission could stay inside `submit` and get cheaper.
//! Skipping declarations an earlier revision admitted needs a cross-revision
//! acceptance key, which is ruled out above. Splitting the export by
//! declaration saves the encode but not the re-derivation. An admission on
//! another thread, abandoned when a newer revision arrives, would also take it
//! off the editor's next keystroke. It costs a session shared across threads,
//! and nothing has measured that the admission's wall, after publication,
//! blocks the next change.
//!
//! **Reversal.** If an editor's next change measurably waits on the admission,
//! the admission moves to a worker that the next judgement cancels.
//!
//! # The parse's repairs ride beside the step
//!
//! The step a face renders carries the composition, which holds no trace of
//! the repairs the parser made to reach a tree. The submission carries them:
//! the parse's completion obligations, taken from the lowering before it is
//! consumed, on every path, re-sorted from the parse's severity order into
//! source order because a reader meets them in the text.
//!
//! `Submission::obligations` carries the completion obligations the parse
//! recorded — each repair's class and the bytes held responsible — on both
//! paths, a revision judged and one refused whole. The step a face renders
//! holds the composition, which keeps no trace of the repairs, so the
//! submission takes them from the lowering before consuming it. The parse
//! orders them by severity, the order its minimization folds; the submission
//! orders them by span, the order a reader meets them, equal spans keeping the
//! parse's order. The rows are the revision's: a clean revision after a
//! recovering one carries none.
//!
//! The rows are the parser's own `ObligationInstance`s, not source-ordered rows
//! of a published vocabulary that a render bus turns into cards and a JSON
//! report serializes, since no face reads a published vocabulary yet; the
//! vocabulary, the cards and the codec arrive with the first face that consumes
//! them. The alternative was to add the obligations to the dispatcher's step,
//! which every batch verb would then carry unread. The choice reverses when the
//! step itself carries the parse's obligations; the submission then forwards
//! the step's.
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
//!
//! **Choice.** Every accepted submission commits the composition's kernel
//! artifact into the session's block store through `gandr-storage-artifact`:
//! one record per declaration segment, cut where the kernel's decoder ends
//! each, under a manifest whose identity binds the record plane's boundary
//! commitment, the record count, the root node and the kernel format version.
//! The submission carries the manifest, and the caller keeps it as it keeps
//! anything — `ArtifactManifest::encode` gives its bytes.
//! `Session::read_kernel` is the one way back: it refuses a manifest of another
//! profile or kernel format before loading anything, re-seals the stored tree
//! against the manifest, checks every key and cut, and hands the bytes to the
//! kernel's bounded decoder. A matching identity says which bytes these are,
//! never that the kernel admits them, so a manifest minted over bytes the
//! kernel refuses names a tree the store holds and seals, and is still refused.
//!
//! **Alternatives.** The encoded artifact as one opaque blob beside the
//! checkpoints would leave no record grain, so a reader could not take one
//! declaration's segment with its proof, and the blob would be trusted by its
//! hash. Keying it into the `CheckpointStore` under the program's address would
//! give that store a second kind of value its trait does not name. Restoring it
//! in `Session::reopen` needs a manifest to read by, and the manifest is the
//! caller's root of trust, not the session's.
//!
//! **Reversal.** A durable table of manifests by program address, owned by the
//! session, lets `Session::reopen` restore the kernel checkpoint itself; and a
//! face that never reads the kernel environment, measured paying for the
//! commit, moves it behind a choice the caller makes.
//!
//! # A submission is a whole revision the caller owns
//!
//! `submit` takes the full text of a revision and returns a `Submission`
//! borrowing it; the session keeps no text. A face that reads lines appends
//! them to its own buffer and submits the buffer, so a later "line" is the
//! earlier revision with the line added, and what carries across lines is what
//! the session keeps: the resume it adopts from and the import scope.
//!
//! The alternative is appending each submission to a transcript the session
//! owns. The lowering resolves a name only within its own module, so a line
//! alone could not see the definitions before it, and a report borrowing a
//! session-owned buffer would freeze the session until the report was dropped.
//! The choice reverses when the lowering takes a seed of earlier declarations:
//! the session then owns the line-append, and a submission is the line.
//!
//! # A trial judges candidates without submitting them
//!
//! **Choice.** `Session::trial` takes candidate revisions — whole texts of the
//! source, as a submission does — and judges each without submitting it: parsed
//! through the form store without changing it (`FormStore::parse_held`),
//! lowered, and judged and settled by the dispatcher's `judge`. Each `Trial`
//! carries the candidate's position and a `Submission` whose composition,
//! standing and repairs are the ones `Session::judge` gives the text in a
//! session that has accepted nothing; it resumes nothing and diffs nothing
//! (`resumed::Absent::Tried`), and the kernel is offered nothing. The method
//! takes `&self`, so the session — its form store, resume, snapshot, imports,
//! documentation, lowering count and admission — is unchanged by construction.
//! The candidates are judged on the session's width, each thread taking the
//! next candidate, and ranked: compositions the lowering read before those it
//! refused whole, both before a fault; then fewer refused declarations, so a
//! wrong fill ranks below one that leaves a goal; then fewer unsettled
//! declarations, fewer owed obligations and fewer parse repairs; then the
//! candidates' own order.
//!
//! A batch on one thread costs what the candidates cost one at a time; across
//! the performance cores it is six to seven times faster. Checking a candidate
//! by submitting it and then restoring the base costs two judgements and two
//! resumes per candidate, twice a trial's.
//!
//! **Alternatives.** A clone of the session per candidate would resume the
//! incremental checker from the latest resume, but the report a face renders is
//! the whole-module judgement, so the resume would cost a copy of the arena and
//! the checkpoints and change no verdict. A target span and a fill spliced into
//! the latest revision would need the session to hold its text, which it does
//! not; the splice belongs to the face that knows the buffer and the hole.
//! Molding a candidate through the store and then pruning the store back would
//! leave the store's contents to a second pass's correctness; a parse that only
//! reads the store cannot disturb it.
//!
//! **Reversal.** When a step can be assembled from adopted checkpoints (§ The
//! report is the dispatcher's composition), a trial resumes from a clone of the
//! latest resume and judges only the declarations the candidate changed. When
//! candidates are measured to share most of their changed forms, the trial
//! molds each distinct identity once across the batch.
//!
//! # The report is the dispatcher's composition
//!
//! The report a submission carries is the dispatcher's `judge`'s, the second
//! half of the composition `gandr check` runs, over the module `lower_source`
//! read — so a submission and a walk step agree by construction, and the corpus
//! agreement suite checks it source by source. The resume runs beside it over a
//! copy of the arena.
//!
//! The alternative was a report assembled from the resume's own verdicts. The
//! incremental checker keeps typings, not the checker's verdicts, and a settle
//! report is built from a judged module; assembling one from adopted
//! checkpoints would be a second judgement to keep in agreement with the first.
//! The cost of the choice is one arena copy and one whole-module judgement per
//! accepted revision. It reverses when a step can be assembled from adopted
//! checkpoints; the whole-module judgement and the copy retire then.
//!
//! # Refusals are the report
//!
//! A declaration the lowering refuses is reported as refused and offered to no
//! one; a declaration the checker refuses is reported as refused and resumed as
//! `Typing::Refused`. A whole-revision lowering refusal retains the accepted
//! state while recording another lowering attempt. A fault — a tree the parser
//! cannot commit, a lowering or kernel disagreement — is a `SessionFault`,
//! never a verdict about the source. There is no unknown former that could turn
//! an unlowerable term into an accepted one.
//!
//! # Checkpoints
//!
//! Every accepted submission attempts to persist its checkpoints under its
//! program's content address. A failed write need not leave an external store
//! unchanged. If the incremental session retains a resume, the submission
//! reports `Persistence::Failed` and the next submission can adopt from it;
//! otherwise the failure is `SessionFault::Store`. `Session::reopen` lowers its
//! supplied revision and restores checkpoints for that program and backend. An
//! absent or incompatible checkpoint set reopens fresh and says why. A restored
//! set is not trusted: the next resume validates each checkpoint as it
//! validates an in-memory one.
//!
//! # The import scope persists across submissions
//!
//! The session keeps the import rows and alias scope of the last revision the
//! lowering read, owned so they outlive its text. A revision the lowering
//! refuses — one that declares an alias twice among them — leaves the scope of
//! the revision before it, so a face resolving `parse` keeps its answer while
//! the author repairs the collision.
//!
//! # Diagnostics and goals are the renderer's
//!
//! A submission's diagnostics are the reports `gandr-surface-diagnostics`
//! renders from its step under the verb a face runs: a refusal at its own
//! locus, an unsettled declaration, and under `check --goals` a goal. A goal is
//! a declaration owed its body — a signature with no definition — which the
//! checker answers with the hole rule and the incremental checker marks as a
//! hole in the item's footprint; the goals suite checks that the two predicates
//! agree item by item.
//!
//! The surface has no hole term yet, so the goals here stand for whole bodies,
//! and goals over sub-term holes, each with its expected type and local
//! context, arrive with the hole surface; a malformed declaration is refused in
//! place, its report the refusal at the responsible bytes, and the declarations
//! after it lower intact. The lowering types an attribute payload against its
//! schema where it reads it, and refuses a mismatch as `IllTypedPayload`, in
//! the malformed-source class every type error takes.
//!
//! # A hole-free item is evaluated
//!
//! `Submission::evaluate` runs one declaration of the revision on the `Program`
//! the dispatcher's composition built, the same run `gandr run` makes, and
//! returns what it came to. The rule is `evaluate`, over a declaration and its
//! program, so a face holding the submission's step applies it without the
//! submission: a declaration the checker accepted — checked or synthesised —
//! runs; one owed its body is a hole and declines with
//! `evaluation::Absent::Holed`; one refused by the lowering, the checker or its
//! root declines with `evaluation::Absent::Unaccepted`, as does a position
//! holding no declaration and a revision refused whole. A declaration that runs
//! into a goal elsewhere is not a hole of its own: it runs, and the run is
//! blamed on the goal. Each evaluation is a fresh machine, so evaluating twice
//! runs twice and nothing is cached between revisions. A native data
//! declaration is not a runtime value and returns
//! `evaluation::Absent::DataUnrunnable`.
//!
//! The fragment has no top-level expression, so the item evaluated is a
//! declaration, and the loop prints a value line under each checked one. The
//! alternative was evaluating nothing until expressions exist, which leaves the
//! loop unable to show a value. The choice reverses when the surface gains a
//! top-level expression: that item is the one evaluated, and a definition
//! returns to its type line alone.

use alloc::collections::BTreeMap;
use alloc::sync::Arc;
use alloc::sync::Weak;
use core::fmt;
use core::num::NonZeroUsize;
use core::sync::atomic::AtomicUsize;
use core::sync::atomic::Ordering;
use std::path::Path;
use std::sync::OnceLock;
use std::thread;

use anodized::spec;
use gandr_core_checker::CheckBudget;
use gandr_core_checker::ObligationCount;
use gandr_core_checker::Polled;
use gandr_core_checker::Retirement;
use gandr_core_checker::Unretired;
use gandr_core_checker::Verdict;
use gandr_core_checker::bridge::LeadingCount;
use gandr_core_checker::bridge::Readmitted;
use gandr_core_checker::bridge::crossed;
use gandr_core_incremental::BackendArtifact;
use gandr_core_incremental::CheckpointObserver;
use gandr_core_incremental::CheckpointStore;
use gandr_core_incremental::CheckpointStoreError;
use gandr_core_incremental::IncrementalSession;
use gandr_core_incremental::ItemCheckpoint;
use gandr_core_incremental::ItemCount;
use gandr_core_incremental::ItemOrdinal;
use gandr_core_incremental::Keeping;
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
use gandr_surface_dispatcher::Admission;
use gandr_surface_dispatcher::Checking;
use gandr_surface_dispatcher::ComposeFault;
use gandr_surface_dispatcher::Composed;
use gandr_surface_dispatcher::Evaluation;
use gandr_surface_dispatcher::HostGrant;
use gandr_surface_dispatcher::Lowered;
use gandr_surface_dispatcher::LoweringCount;
use gandr_surface_dispatcher::Program;
use gandr_surface_dispatcher::Resumption;
use gandr_surface_dispatcher::SourceRoot;
use gandr_surface_dispatcher::Standing;
use gandr_surface_dispatcher::Step;
use gandr_surface_dispatcher::Threads;
use gandr_surface_dispatcher::TypeTable;
use gandr_surface_dispatcher::Width;
use gandr_surface_dispatcher::judge_member;
use gandr_surface_dispatcher::judge_member_after;
use gandr_surface_dispatcher::judge_member_tabled;
use gandr_surface_dispatcher::lower_closure;
use gandr_surface_dispatcher::lower_onto_closure;
use gandr_surface_dispatcher::lower_parsed;
use gandr_surface_dispatcher::lower_parsed_unit;
use gandr_surface_dispatcher::lower_resumed_unit;
use gandr_surface_dispatcher::tabled;
use gandr_surface_grammar::Pbg;
use gandr_surface_lowering::DeclarationCount;
use gandr_surface_lowering::DeclarationOutcome;
use gandr_surface_lowering::DocumentationText;
use gandr_surface_lowering::ImportIndex;
use gandr_surface_lowering::ImportUri;
use gandr_surface_lowering::LoweredModule;
use gandr_surface_lowering::SourceIndex;
use gandr_surface_lowering::Unit;
use gandr_surface_lowering::UnitSource;
use gandr_surface_lowering::coincide::Decisions;
use gandr_surface_lowering::documentation;
use gandr_surface_lowering::namespace::NamePath;
use gandr_surface_lowering::namespace::Scope;
use gandr_surface_parser::MeldError;
use gandr_surface_parser::ObligationInstance;
use gandr_surface_parser::ParseResult;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::NodeKey;
use gandr_surface_syntax::SourceText;
use gandr_surface_syntax::SyntaxTree;
use quenchant_shape::shape::Maybe;

use crate::closures;
use crate::closures::ClosureAdmission;
use crate::edit::EditScript;
use crate::edit::Snapshot;
use crate::edit::diff;
use crate::forms::FormCensus;
use crate::forms::FormStore;
use crate::item_source::program;
use crate::lowerings;
use crate::lowerings::Closure;
use crate::lowerings::Held;
use crate::lowerings::Led;

quenchant_shape::reason_enum! {
    /// Why a submission carries no resume.
    pub mod resumed {
        /// The reason none is carried.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The lowering refused the revision as a whole, so it offered no
            /// items to resume over.
            RefusedWhole,
            /// The revision was tried, not submitted: the incremental checker
            /// did not resume over it and the session kept nothing of it.
            Tried,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a submission carries no kernel checkpoint.
    pub mod admitted {
        /// The reason none is carried.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The lowering refused the revision as a whole, so it offered
            /// the kernel nothing.
            RefusedWhole,
            /// The revision was judged and its admission has not run: the
            /// submission came from [`Session::judge`](super::Session::judge).
            Pending,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a session runs no admission.
    pub mod admission {
        /// The reason none runs.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No judgement left one: none ran since the last admission, the
            /// latest faulted, or its revision was refused as a whole.
            Idle,
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
///
/// # Specification
/// - requires: the producing operation’s documented context.
/// - ensures: The URI and source extent belong to one import declaration.
/// - executable: none — The data record does not retain its module or source
///   text and has no callable boundary; `Imports::of` checks the ordered source
///   correspondence.
///
/// # Adequacy
/// - hypothesis: L3 — the cited accepted, refused or restored session
///   observations, at their exact fields or state transitions. These are
///   bounded concrete witnesses, not a universal proof of external store
///   behavior.
/// - witness: `tests::session::import_namespace_carries_across_lines_and_resolves_source_declarations`
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
///
/// # Specification
/// - requires: the producing operation’s documented context.
/// - ensures: Rows and alias bindings belong to the same accepted revision.
/// - executable: none — The aggregate has no runtime invocation; its producers
///   check row payloads and its resolver checks alias-to-row interpretation.
///
/// # Adequacy
/// - hypothesis: L3 — the cited accepted, refused or restored session
///   observations, at their exact fields or state transitions. These are
///   bounded concrete witnesses, not a universal proof of external store
///   behavior.
/// - witness: `tests::session::import_namespace_carries_across_lines_and_resolves_source_declarations`
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
    /// - requires: nothing.
    /// - ensures: contains no import rows or alias bindings.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — resolving an unbound alias before submission and
    ///   preserving the accepted import namespace after refusal. Row emptiness
    ///   is executable; alias absence is observed through the resolver.
    /// - witness: `tests::session::import_namespace_carries_across_lines_and_resolves_source_declarations`
    #[spec(
        ensures: |ret| ret.rows.is_empty(),
    )]
    fn empty() -> Self
    {
        Self {
            rows: Vec::new(),
            scope: Scope::new(),
        }
    }

    /// The import scope `module` declared in its source at `own`.
    ///
    /// # Specification
    /// - requires: the module’s import scope and declarations belong to the
    ///   same lowering; `own` is the revision's own source in its unit.
    /// - ensures: preserves every import URI and source span the source at
    ///   `own` writes, in declaration order, and copies the alias scope that
    ///   names those rows.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two accepted import namespaces and a refused
    ///   duplicate alias. Exact URIs and source declaration spans distinguish
    ///   binding the wrong row or retaining the old namespace after acceptance.
    /// - witness: `tests::session::import_namespace_carries_across_lines_and_resolves_source_declarations`
    #[spec(
        ensures: |ret| {
    ret.rows.len() == module.imports().iter().filter(|declaration| declaration.source() == own).count()
},
    )]
    fn of(
        module: &LoweredModule<'_>,
        own: SourceIndex,
    ) -> Self
    {
        Self {
            rows: module
                .imports()
                .iter()
                .filter(|declaration| declaration.source() == own)
                .map(|declaration| ImportRow {
                    uri: declaration.uri().clone(),
                    span: declaration.span(),
                })
                .collect(),
            scope: match module.import_scope(own) {
                Maybe::Present(scope) => scope.clone(),
                Maybe::Absent(_) => Scope::new(),
            },
        }
    }

    /// The row `path` resolves to.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: borrows the row named by the alias binding, or reports
    ///   Unbound when the path or row is absent.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — bound and unbound aliases across accepted and refused
    ///   revisions; exact declaration URIs and spans distinguish wrong bindings
    ///   from missing ones.
    /// - witness: `tests::session::import_namespace_carries_across_lines_and_resolves_source_declarations`
    #[spec(
        ensures: |ret| match self.scope.resolve(path) {
    Maybe::Present(binding) => {
        self.rows
            .get(usize::from(binding.data))
            .map_or(
                matches!(ret, Maybe::Absent(import::Absent::Unbound)),
                |row| {
                    matches!(
                        ret, Maybe::Present(found) if
                        core::ptr::eq(core::ptr::from_ref(found),
                        core::ptr::from_ref(row))
                    )
                },
            )
    }
    Maybe::Absent(_) => matches!(ret, Maybe::Absent(import::Absent::Unbound)),
},
    )]
    fn resolve(
        &self,
        path: &NamePath,
    ) -> Maybe<&ImportRow, import::Absent>
    {
        match self.scope.resolve(path) {
            // The scope and the rows are the same module's, so every position
            // the scope binds has its row.
            Maybe::Present(binding) => self
                .rows
                .get(usize::from(binding.data))
                .map_or(Maybe::Absent(import::Absent::Unbound), Maybe::Present),
            Maybe::Absent(_) => Maybe::Absent(import::Absent::Unbound),
        }
    }
}

/// Whether a submission's checkpoints reached the store.
///
/// # Specification
/// - requires: the producing operation’s documented context.
/// - ensures: Stored reports successful checkpoint persistence; Discarded a
///   store that keeps nothing, which was handed nothing; Failed carries the
///   store refusal while the session keeps its resume. External partial writes
///   follow the store’s contract.
/// - executable: none — The enum does not contain the store or the operation’s
///   earlier state; `Session::submit` and the persistence-failure witness
///   observe the transition.
///
/// # Adequacy
/// - hypothesis: L3 — the cited accepted, refused or restored session
///   observations, at their exact fields or state transitions. These are
///   bounded concrete witnesses, not a universal proof of external store
///   behavior.
/// - witness: `tests::checkpoint::a_store_failure_is_reported_and_the_session_still_resumes`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Persistence
{
    /// The store holds the submission's checkpoints at its program's address.
    Stored,
    /// The store keeps no checkpoint sets ([`Keeping::Discarded`]): nothing
    /// was addressed or written.
    Discarded,
    /// The store refused them; its own contract governs any partial writes.
    /// The session still resumes from the submission.
    Failed(CheckpointStoreError),
}

/// What the incremental checker made of an accepted submission.
///
/// # Specification
/// - requires: the producing operation’s documented context.
/// - ensures: The census describes the accepted revision’s incremental pass,
///   independently of whether persistence succeeded.
/// - executable: none — The data declaration has no invocation or input program
///   to compare; submission predicates and exact census witnesses provide that
///   context.
///
/// # Adequacy
/// - hypothesis: L3 — the cited accepted, refused or restored session
///   observations, at their exact fields or state transitions. These are
///   bounded concrete witnesses, not a universal proof of external store
///   behavior.
/// - witness: `tests::session::whole_file_submit_carries_definitions_forward`
/// - witness: `tests::checkpoint::a_store_failure_is_reported_and_the_session_still_resumes`
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
///
/// # Specification
/// - requires: the producing operation’s documented context.
/// - ensures: Stored carries the manifest naming the committed kernel records;
///   Discarded a session whose checkpoint store keeps nothing, which commits
///   nothing; Failed preserves the first artifact or block-store refusal
///   without discarding the accepted resume.
/// - executable: none — The enum has neither its originating artifact nor store
///   and no callable boundary; commit and readback operations check the
///   relation.
///
/// # Adequacy
/// - hypothesis: L3 — a healthy in-memory store read back after reopening, and
///   a store refusing its first insertion. Exact decoded declarations, refusal
///   variants, and subsequent adoption distinguish false persistence from loss
///   of the accepted resume; other store failures remain outside this bounded
///   domain.
/// - witness: `tests::checkpoint::a_reopened_session_reads_its_kernel_checkpoint_through_the_decoder`
/// - witness: `tests::checkpoint::a_kernel_store_failure_preserves_resume_and_edit_state`
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum KernelCheckpoint
{
    /// The block store holds the revision's kernel artifact as records under
    /// this manifest, which [`Session::read_kernel`] reads back.
    Stored(ArtifactManifest),
    /// The session's checkpoint store keeps nothing ([`Keeping::Discarded`]),
    /// so no session restores the kernel artifact either: nothing was cut or
    /// committed.
    Discarded,
    /// The artifact was not committed: its records did not form or the block
    /// store refused a node. No manifest names what reached the store, and the
    /// session still resumes from the submission.
    Failed(ArtifactError),
}

/// What one admission produced: the kernel artifact of every declaration that
/// crossed, whether it reached the block store, and how many declarations the
/// kernel was offered again.
///
/// # Specification
/// - requires: constructed by [`Session::settle`], which [`Session::admit`]
///   ends with.
/// - ensures: the checkpoint is the one committed for the artifact, or
///   [`KernelCheckpoint::Discarded`] when the session's store keeps nothing; no
///   more declarations crossed than were judged.
/// - panics: none.
/// - executable: none — this data type has no call boundary;
///   [`Session::settle`] carries the executable clauses.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Session::admit`].
/// - witness: `tests::session::a_judged_revision_reports_before_its_admission`
/// - witness: `tests::session::an_edit_to_its_own_text_readmits_the_document_alone_776`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Admitted
{
    /// The kernel artifact the admission exported.
    kernel: EncodedArtifact,
    /// Whether it reached the block store.
    checkpoint: KernelCheckpoint,
    /// How many declarations the readmission offered the kernel again; the
    /// rest of those judged it resumed from the process's readmission of the
    /// revision's import closure.
    crossed: DeclarationCount,
    /// How many declarations the checker judged.
    judged: DeclarationCount,
}

impl Admitted
{
    /// The kernel artifact the admission exported.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn kernel(&self) -> &EncodedArtifact
    {
        &self.kernel
    }

    /// Whether the artifact reached the block store, and the manifest naming
    /// it when it did.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn checkpoint(&self) -> &KernelCheckpoint
    {
        &self.checkpoint
    }

    /// How many declarations the readmission offered the kernel again, of
    /// [`judged`](Self::judged): the rest it resumed from the process's
    /// readmission of the revision's import closure.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn crossed(&self) -> DeclarationCount
    {
        self.crossed
    }

    /// How many declarations the checker judged.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn judged(&self) -> DeclarationCount
    {
        self.judged
    }
}

/// What one submitted revision became: the dispatcher's composition of its
/// text, its standing, and what the incremental checker made of it.
///
/// # Specification
/// - requires: the producing operation’s documented context.
/// - ensures: The source frame, composition and standing describe one revision;
///   accepted revisions carry resume, edits and kernel status, and every
///   revision carries its source-ordered completion obligations.
/// - executable: none — The result aggregate has no runtime invocation;
///   `Session::submit` checks its state and the observation methods check
///   source-frame and eligibility relations.
///
/// # Adequacy
/// - hypothesis: L3 — the cited accepted, refused or restored session
///   observations, at their exact fields or state transitions. These are
///   bounded concrete witnesses, not a universal proof of external store
///   behavior.
/// - witness: `tests::session::submission_owns_outcomes_after_session_advances`
/// - witness: `tests::diag_obligations::lowered_carries_the_parse_obligations_verbatim`
#[derive(Clone, Debug)]
pub struct Submission<'text>
{
    /// The root the session's source sits under.
    root: SourceRoot,
    /// The text judged, which every span of `composed` is measured against:
    /// the revision, laid after the siblings it imports when it imports any.
    text: SourceText<'text>,
    /// Where the revision's own text starts in `text`.
    base: ByteOffset,
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
    kernel: Maybe<KernelCheckpoint, admitted::Absent>,
    /// The parse's completion obligations, in source order.
    obligations: Vec<ObligationInstance>,
    /// How the parse was assembled from the form store.
    forms: FormCensus,
    /// The type table the judgement kept of the revision's own source, or why
    /// it holds none.
    table: Maybe<TypeTable, tabled::Absent>,
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

    /// The text judged: the revision, after the siblings it imports.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn text(&self) -> SourceText<'text>
    {
        self.text
    }

    /// Where the revision's own text starts in [`text`](Self::text): zero
    /// unless it imports a sibling.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn base(&self) -> ByteOffset
    {
        self.base
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
            Maybe::Present(ref edits) => Maybe::Present(edits),
            Maybe::Absent(reason) => Maybe::Absent(reason),
        }
    }

    /// Whether the revision's kernel checkpoint reached the block store, and
    /// the manifest naming it when it did.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn kernel(&self) -> Maybe<&KernelCheckpoint, admitted::Absent>
    {
        match self.kernel {
            Maybe::Present(ref kernel) => Maybe::Present(kernel),
            Maybe::Absent(reason) => Maybe::Absent(reason),
        }
    }

    /// How the revision's parse was assembled: its top-level forms, and how
    /// many were molded rather than taken up from the session's form store.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn forms(&self) -> FormCensus
    {
        self.forms
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
    /// - hypothesis: L3 — clean, recovering, severity-inverted and wholly
    ///   refused sources, followed by a clean revision. The exact parser rows
    ///   and their stable source order distinguish lost repairs and stale
    ///   obligations.
    /// - witness: `tests::diag_obligations::lowered_carries_the_parse_obligations_verbatim`
    /// - witness: `tests::diag_obligations::rows_are_in_source_order_not_severity_order`
    /// - witness: `tests::diag_obligations::a_clean_source_reports_no_obligations`
    #[spec(
        ensures: |ret| {
    core::ptr::eq(
        core::ptr::from_ref(ret),
        core::ptr::from_ref(self.obligations.as_slice()),
    )
        && ret
            .windows(2)
            .all(|pair| matches!(pair, [left, right] if left.span <= right.span))
},
    )]
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
    ///   text, base, composition and standing unchanged.
    /// - provides: the diagnostics a face renders, through the renderer the
    ///   batch verbs use.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every checked-in corpus source, compared field by
    ///   field with the batch step. This finite shared-pipeline agreement is
    ///   not an independent semantic proof; the predicate checks the moved
    ///   scalar observations without copying the composition.
    /// - witness: `tests::corpus::every_source_submits_as_the_walk_composes_it`
    #[spec(
        captures: before = (self.root, self.text, self.base, self.standing),
        ensures: |ret| {
    matches!(
        ret, Step::Source { path : found, root, text, base, standing, .. } if found == path &&
        root == before.0 && text == before.1 && base == before.2 && standing == before.3
    )
},
    )]
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
            base: self.base,
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
    /// - hypothesis: L3 — exact integer and function-call results, an owed
    ///   body, a missing constant, a checker refusal and a wholly refused
    ///   revision. These distinguish eligibility and evaluation; the predicate
    ///   observes eligibility without running the machine twice.
    /// - witness: `tests::session::integer_literal_types_and_evaluates`
    /// - witness: `tests::session::nullary_function_call_evaluates`
    /// - witness: `tests::session::holes_decline_evaluation`
    /// - witness: `tests::session::evaluation_declines_missing_and_refused_items`
    #[spec(
        ensures: |ret| match self.composed {
    Composed::Settled { ref report, .. } => {
        report
            .declarations()
            .iter()
            .find(|declaration| declaration.constant() == constant)
            .map_or(
                matches!(ret, Maybe::Absent(evaluation::Absent::Unaccepted)),
                |declaration| match declaration.produced() {
                    Produced::Judged(
                        Verdict::Data | Verdict::Checked { .. } | Verdict::Synthesised { .. },
                    ) => matches!(ret, Maybe::Present(_)),
                    Produced::Judged(Verdict::Owed(_) | Verdict::Suspended(_)) => {
                        matches!(ret, Maybe::Absent(evaluation::Absent::Holed))
                    }
                    Produced::Judged(Verdict::Refused(_))
                    | Produced::Unlowered(_)
                    | Produced::Guarded(_) => {
                        matches!(ret, Maybe::Absent(evaluation::Absent::Unaccepted))
                    }
                },
            )
    }
    Composed::Refused(_) => matches!(ret, Maybe::Absent(evaluation::Absent::Unaccepted)),
},
    )]
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
        report
            .declarations()
            .iter()
            .find(|declaration| declaration.constant() == constant)
            .map_or(
                Maybe::Absent(evaluation::Absent::Unaccepted),
                |declaration| evaluate(declaration, program),
            )
    }

    /// Hand on the type table the judgement kept of the revision's own
    /// source, leaving [`tabled::Absent::Taken`] in its place: the table
    /// [`TypeTable::of_parsed_after`] or [`TypeTable::of_parsed_unit`] types
    /// of the same text, made by the judgement's own run. A session asked to
    /// keep no tables ([`Session::keep`]) keeps none.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn take_table(&mut self) -> Maybe<TypeTable, tabled::Absent>
    {
        core::mem::replace(&mut self.table, Maybe::Absent(tabled::Absent::Taken))
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
///   never ran. A declaration owed its body, or waiting on holes that are,
///   declines with [`evaluation::Absent::Holed`]; one refused, by the lowering,
///   the checker or its root, declines with [`evaluation::Absent::Unaccepted`].
///   Nothing runs for a declined item.
/// - provides: the one rule for what a session evaluates, shared by a
///   submission and by a face holding the submission's step.
/// - fails: the declining absences the ensures clause names.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — exact integer and function-call results plus owed and
///   refused declarations. The result category is executable independently of
///   machine execution; no duplicate evaluation is performed.
/// - witness: `tests::session::integer_literal_types_and_evaluates`
/// - witness: `tests::session::nullary_function_call_evaluates`
/// - witness: `tests::session::holes_decline_evaluation`
/// - witness: `tests::session::evaluation_declines_missing_and_refused_items`
#[spec(
    ensures: |ret| match declaration.produced() {
    Produced::Judged(Verdict::Data | Verdict::Checked { .. } | Verdict::Synthesised { .. }) => {
        matches!(ret, Maybe::Present(_))
    }
    Produced::Judged(Verdict::Owed(_) | Verdict::Suspended(_)) => {
        matches!(ret, Maybe::Absent(evaluation::Absent::Holed))
    }
    Produced::Judged(Verdict::Refused(_))
    | Produced::Unlowered(_)
    | Produced::Guarded(_) => {
        matches!(ret, Maybe::Absent(evaluation::Absent::Unaccepted))
    }
},
)]
#[inline]
pub fn evaluate<'text>(
    declaration: &DeclarationReport<'text>,
    program: &mut Program<'text>,
) -> Maybe<Evaluation<'text>, evaluation::Absent>
{
    match declaration.produced() {
        Produced::Judged(Verdict::Data | Verdict::Checked { .. } | Verdict::Synthesised { .. }) => {
            Maybe::Present(program.evaluate(declaration.constant()))
        },
        Produced::Judged(Verdict::Owed(_) | Verdict::Suspended(_)) => {
            Maybe::Absent(evaluation::Absent::Holed)
        },
        Produced::Judged(Verdict::Refused(_)) | Produced::Unlowered(_) | Produced::Guarded(_) => {
            Maybe::Absent(evaluation::Absent::Unaccepted)
        },
    }
}

/// A candidate's position among the candidates a trial was given.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CandidateIndex(usize);

impl From<usize> for CandidateIndex
{
    /// The candidate at `index`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: usize) -> Self
    {
        Self(index)
    }
}

impl From<CandidateIndex> for usize
{
    /// The position `index` names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: CandidateIndex) -> Self
    {
        index.0
    }
}

/// One candidate revision as a trial judged it, beside its position among the
/// candidates.
///
/// # Specification
/// - requires: constructed by [`Session::trial`].
/// - ensures: the outcome is what [`Session::judge`] gives the candidate's text
///   in a session that has accepted nothing, except that it carries no resume
///   and no edits ([`resumed::Absent::Tried`]).
/// - panics: none.
/// - executable: none — this data type has no call boundary; the trial carries
///   the executable clauses.
///
/// # Adequacy
/// - hypothesis: L3 — candidates that settle, owe a goal, refuse a declaration
///   and are refused whole are each reported as a fresh session judges them.
/// - witness: `tests::trial::each_candidate_is_judged_as_a_fresh_session_judges_it`
#[derive(Clone, Debug)]
pub struct Trial<'text>
{
    /// The candidate's position among those the trial was given.
    candidate: CandidateIndex,
    /// What the candidate became.
    outcome: Result<Submission<'text>, SessionFault<'text>>,
}

impl<'text> Trial<'text>
{
    /// The candidate's position among those the trial was given.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn candidate(&self) -> CandidateIndex
    {
        self.candidate
    }

    /// What the candidate became.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn outcome(&self) -> &Result<Submission<'text>, SessionFault<'text>>
    {
        &self.outcome
    }

    /// What the candidate became, owned.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// The engine fault that stopped the candidate.
    #[inline]
    pub fn into_outcome(self) -> Result<Submission<'text>, SessionFault<'text>>
    {
        self.outcome
    }
}

/// Why a session could not take a revision, or could not reopen over one: an
/// engine fault, never a verdict about the revision.
///
/// # Specification
/// - requires: the producing operation’s documented context.
/// - ensures: Each variant names an engine or persistence failure, distinct
///   from a refused source revision.
/// - executable: none — The error enum has no runtime call boundary or
///   underlying operation to repeat; submission and reopen return the
///   originating typed error.
///
/// # Adequacy
/// - hypothesis: L3 — the cited accepted, refused or restored session
///   observations, at their exact fields or state transitions. These are
///   bounded concrete witnesses, not a universal proof of external store
///   behavior.
/// - witness: `tests::checkpoint::a_store_failure_is_reported_and_the_session_still_resumes`
/// - witness: `tests::session::formatters_propagate_sink_refusals`
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
    /// - requires: nothing.
    /// - ensures: formats the documented fault or state observations, leaving
    ///   opaque stores uninspected; preserves the formatter’s refusal.
    /// - panics: none.
    /// - executable: none — The formatter exposes neither its previous bytes
    ///   nor sink failure state. A postcondition cannot inspect the emitted
    ///   text or distinguish success from refusal without writing again.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a store fault and both session debug views written
    ///   into a refusing sink. The exact error result distinguishes swallowed
    ///   formatting failures; English wording and debug layout are
    ///   intentionally not pinned.
    /// - witness: `tests::session::formatters_propagate_sink_refusals`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Compose(ref fault) => fault.fmt(f),
            Self::Unordered(ref error) => error.fmt(f),
            Self::Resume(ref error) => write!(f, "resume failed: {error}"),
            Self::Store(ref error) => write!(f, "the checkpoint store failed: {error}"),
        }
    }
}

impl core::error::Error for SessionFault<'_>
{
}

/// A session reopened over a revision, and whether its checkpoints were
/// restored.
///
/// # Specification
/// - requires: the producing operation’s documented context.
/// - ensures: The restored item count corresponds to the session’s retained
///   resume; an absence identifies why no checkpoint set was restored.
/// - executable: none — The aggregate has no invocation; `Session::reopen`
///   checks restored cardinality and resume presence without repeating I/O.
///
/// # Adequacy
/// - hypothesis: L3 — the cited accepted, refused or restored session
///   observations, at their exact fields or state transitions. These are
///   bounded concrete witnesses, not a universal proof of external store
///   behavior.
/// - witness: `tests::checkpoint::a_reopened_session_resumes_from_the_checkpoints_a_dropped_one_wrote`
/// - witness: `tests::checkpoint::a_store_holding_nothing_reopens_fresh`
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
    /// - requires: nothing.
    /// - ensures: formats the documented fault or state observations, leaving
    ///   opaque stores uninspected; preserves the formatter’s refusal.
    /// - panics: none.
    /// - executable: none — The formatter exposes neither its previous bytes
    ///   nor sink failure state. A postcondition cannot inspect the emitted
    ///   text or distinguish success from refusal without writing again.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a store fault and both session debug views written
    ///   into a refusing sink. The exact error result distinguishes swallowed
    ///   formatting failures; English wording and debug layout are
    ///   intentionally not pinned.
    /// - witness: `tests::session::formatters_propagate_sink_refusals`
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
///
/// # Specification
/// - requires: the producing operation’s documented context.
/// - ensures: The root and grammar remain fixed, accepted state advances with
///   readable modules, whole-revision refusals retain it, and the counter
///   records every lowering attempt.
/// - executable: none — The state object has no callable type boundary and does
///   not retain every prior revision; constructor, reopen and submit predicates
///   check transitions, with exact-state witnesses.
///
/// # Adequacy
/// - hypothesis: L3 — the cited accepted, refused or restored session
///   observations, at their exact fields or state transitions. These are
///   bounded concrete witnesses, not a universal proof of external store
///   behavior.
/// - witness: `tests::session::failed_submission_retains_latest_synthesis`
/// - witness: `tests::session::import_namespace_carries_across_lines_and_resolves_source_declarations`
pub struct Session<Store, Blocks>
{
    /// The grammar every revision is parsed under, shared with the closure
    /// lowerings the session holds.
    grammar: Arc<Pbg>,
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
    /// The documentation of the latest accepted revision, by the documented
    /// form's cross-tree key.
    documentation: BTreeMap<NodeKey, DocumentationText>,
    /// Every lowering the session performed.
    lowerings: LoweringCount,
    /// The rule blocks' decisions kept across the session's lowerings, so
    /// that a revision deciding a block it left as it was answers it from the
    /// last decision.
    decisions: Decisions,
    /// Every form of the latest parsed revision, by identity.
    forms: FormStore,
    /// The threads a revision's changed forms are molded on.
    threads: Threads,
    /// The kernel admission the latest judgement left to run.
    admission: Maybe<Pending, admission::Absent>,
    /// Whether each judgement keeps the type table of its revision.
    tables: Tables,
}

/// Whether a session's judgements keep the type table of each revision.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Tables
{
    /// No judgement keeps a table: what a check that answers no position
    /// reads.
    Unkept,
    /// Each judgement types the revision's bodies as written beside checking
    /// them, and keeps the table ([`Submission::take_table`]).
    Kept,
}

/// A kernel admission a judgement left to run, beside the import closure its
/// revision was laid out after.
#[derive(Clone, Debug)]
struct Pending
{
    /// The admission.
    admission: Admission,
    /// How many of the judged declarations the closure holds: those written
    /// before the revision's own source.
    boundary: usize,
    /// The closure's text: the revision before its own source.
    closure: String,
}

/// A kernel admission taken off its session, to run on another thread.
///
/// It holds the admission, the checkpoints of the judgement that left it, and
/// the readmission the process holds for the items it leads with.
///
/// # Specification
/// - requires: constructed by [`Session::admission`].
/// - ensures: the checkpoints are those of the judgement that left the
///   admission, in item order.
/// - panics: none.
/// - executable: none — a carrier; [`Detached::run`] and [`Session::settle`]
///   carry the executable clauses.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Detached::run`].
/// - witness: `tests::session::a_retired_admission_leaves_what_it_crossed_to_the_next_1547`
#[derive(Debug)]
pub struct Detached
{
    /// The admission and the closure it resumes.
    pending: Pending,
    /// The checkpoint of each item the judgement judged, in order.
    checkpoints: Vec<ItemCheckpoint>,
    /// The readmission the process holds for the longest run of leading
    /// items whose checkpoints are these, when it holds one.
    found: Option<Arc<ClosureAdmission>>,
}

/// A detached admission that ran whole, to settle into its session.
///
/// # Specification
/// - requires: constructed by [`Detached::run`].
/// - ensures: carries the readmission's answer beside what settling it keeps.
/// - panics: none.
/// - executable: none — a carrier; [`Session::settle`] carries the executable
///   clauses.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Session::settle`].
/// - witness: `tests::session::a_retired_admission_leaves_what_it_crossed_to_the_next_1547`
#[derive(Debug)]
pub struct Ran
{
    /// What the readmission answered.
    resumption: Resumption,
    /// How many of the judged declarations the closure holds.
    boundary: usize,
    /// The closure's text.
    closure: String,
    /// The checkpoint of each item the judgement judged, in order.
    checkpoints: Vec<ItemCheckpoint>,
    /// The readmission it resumed from, when the process held one.
    found: Option<Arc<ClosureAdmission>>,
}

impl Detached
{
    /// Run the admission, polling `retirement` before each declaration it
    /// crosses.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: while every poll answers wanted, [`Polled::Whole`] with what
    ///   [`Admission::admit_resuming`] answers, resuming from the held
    ///   readmission; retired before a declaration, [`Polled::Retired`], and
    ///   the record of the declarations crossed before it, when the readmission
    ///   made one, is held in the process's store under the closure's text and
    ///   their checkpoints, for a later admission to resume.
    /// - provides: the half of an admission that runs off the session's thread.
    /// - fails: never; a disagreement is in the answer.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an admission retired part way leaves its record, and
    ///   the next admission of the same revision crosses only the declarations
    ///   after it.
    /// - witness: `tests::session::a_retired_admission_leaves_what_it_crossed_to_the_next_1547`
    #[inline]
    #[spec(
        captures: [boundary = self.pending.boundary],
        ensures: |ret| match ret {
            Polled::Whole(ref ran) => ran.boundary == boundary,
            Polled::Retired(..) => true,
        },
    )]
    pub fn run<Poll>(
        self,
        retirement: &Poll,
    ) -> Polled<Ran, Poll::Retired, ()>
    where
        Poll: Retirement,
    {
        let Self {
            pending:
                Pending {
                    admission,
                    boundary,
                    closure,
                },
            checkpoints,
            found,
        } = self;
        let resumed = found
            .as_deref()
            .map_or(Maybe::Absent(crossed::Absent::Unasked), |found| {
                Maybe::Present(found.crossed())
            });
        match admission.admit_retiring(LeadingCount::from(boundary), resumed, retirement) {
            Polled::Whole(resumption) => Polled::Whole(Ran {
                resumption,
                boundary,
                closure,
                checkpoints,
                found,
            }),
            Polled::Retired(retired, record) => {
                if let Maybe::Present(record) = record
                    && let Some(leading) = checkpoints.get(.. usize::from(record.boundary()))
                {
                    let _held = closures::keep(closure, leading.to_vec(), record);
                }
                Polled::Retired(retired, ())
            },
        }
    }
}

impl<Store, Blocks> fmt::Debug for Session<Store, Blocks>
{
    /// Writes the root, the latest resume and the import scope; the grammar
    /// and the stores are opaque.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: formats the documented fault or state observations, leaving
    ///   opaque stores uninspected; preserves the formatter’s refusal.
    /// - panics: none.
    /// - executable: none — The formatter exposes neither its previous bytes
    ///   nor sink failure state. A postcondition cannot inspect the emitted
    ///   text or distinguish success from refusal without writing again.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a store fault and both session debug views written
    ///   into a refusing sink. The exact error result distinguishes swallowed
    ///   formatting failures; English wording and debug layout are
    ///   intentionally not pinned.
    /// - witness: `tests::session::formatters_propagate_sink_refusals`
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
    /// - requires: nothing.
    /// - ensures: retains the supplied grammar, root and stores, with the
    ///   default checking budget, no accepted revision, imports or snapshot, an
    ///   empty form store molding on the host's performance cores
    ///   ([`Width::PerformanceCores`]), and zero lowering attempts.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a fresh session’s first revision, unbound import
    ///   resolution and subsequent accepted/refused revisions. Initial absence
    ///   and exact first census distinguish stale state or the wrong root.
    /// - witness: `tests::session::whole_file_submit_carries_definitions_forward`
    /// - witness: `tests::session::import_namespace_carries_across_lines_and_resolves_source_declarations`
    #[spec(
        ensures: |ret| {
    ret.root == root && usize::from(ret.lowerings) == 0_usize
        && ret.imports.rows.is_empty() && ret.snapshot.items().is_empty()
        && matches!(ret.incremental.last(), Maybe::Absent(_))
},
    )]
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
            grammar: Arc::new(grammar),
            root,
            incremental: IncrementalSession::new(store, backend, CheckBudget::DEFAULT),
            blocks,
            imports: Imports::empty(),
            snapshot: Snapshot::default(),
            documentation: BTreeMap::new(),
            lowerings: LoweringCount::default(),
            decisions: Decisions::held(),
            forms: FormStore::default(),
            threads: Width::PerformanceCores.threads(),
            admission: Maybe::Absent(admission::Absent::Idle),
            tables: Tables::Unkept,
        }
    }

    /// The session molding each revision's changed forms on the threads
    /// `width` answers.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the session unchanged but for the threads it molds on, asked
    ///   of `width` once, here.
    /// - provides: the driver's width, carried to the edit loop.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — generated edits submit to the walk's compositions at
    ///   one thread and at the host's width alike.
    /// - witness: `tests::forms::every_generated_edit_submits_as_the_walk_composes_it`
    /// - witness: `session::tests::a_session_molds_on_the_width_it_is_given`
    #[spec(ensures: |ret| ret.threads == width.threads())]
    #[inline]
    #[must_use]
    pub fn with_width(
        self,
        width: Width,
    ) -> Self
    {
        Self {
            threads: width.threads(),
            ..self
        }
    }

    /// A session reopened over `revision`, resuming from the checkpoints
    /// `store` holds for it, its kernel checkpoints read from `blocks`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `revision` is parsed through a fresh form store, which the
    ///   session keeps, and lowered once. When the lowering reads a module and
    ///   `store` holds checkpoints `backend` judged for its program, the
    ///   session resumes from them and their item count is reported; otherwise
    ///   the incremental session has no resume, and the reason is reported. The
    ///   lowering attempt is counted in either case. The import scope and
    ///   snapshot are the revision's, it molds on the host's performance cores,
    ///   and it reads and commits kernel checkpoints in `blocks`.
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
    /// - hypothesis: L3 — a file store reopened after dropping its writer and
    ///   an empty store, followed by an unchanged submission. Exact restored
    ///   counts and adopted items distinguish fresh fallback from a usable
    ///   checkpoint; no second store read occurs in the predicate.
    /// - witness: `tests::checkpoint::a_reopened_session_resumes_from_the_checkpoints_a_dropped_one_wrote`
    /// - witness: `tests::checkpoint::a_store_holding_nothing_reopens_fresh`
    #[spec(
        ensures: |ret| {
    ret
        .as_ref()
        .is_ok_and(|reopened| {
            reopened.session.root == root
                && usize::from(reopened.session.lowerings) == 1_usize
                && match reopened.restored {
                    Maybe::Present(count) => {
                        reopened.session.snapshot.items().len() == usize::from(count)
                            && matches!(
                                reopened.session.incremental.last(), Maybe::Present(resume)
                                if resume.handles().len() == usize::from(count)
                            )
                    }
                    Maybe::Absent(_) => {
                        matches!(reopened.session.incremental.last(), Maybe::Absent(_))
                    }
                }
        }) || ret.is_err()
},
    )]
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
        let mut decisions = Decisions::held();
        let mut forms = FormStore::default();
        let threads = Width::PerformanceCores.threads();
        let (parsed, _census) = forms
            .parse(&grammar, revision, threads)
            .map_err(|fault| SessionFault::Compose(ComposeFault::Parse(fault)))?;
        let lowering = lower_parsed(&grammar, parsed, &mut lowerings, &mut decisions)
            .map_err(SessionFault::Compose)?;
        let (imports, snapshot, documentation, restored) = match lowering.into_lowered() {
            Lowered::Refused(_) => (
                Imports::empty(),
                Snapshot::default(),
                BTreeMap::new(),
                Maybe::Absent(reopened::Absent::RefusedWhole),
            ),
            Lowered::Module { module, arena } => {
                let program = program(&module, arena).map_err(SessionFault::Unordered)?;
                let address = address_of(&program).map_err(SessionFault::Store)?;
                let restored = match restore(&mut store, &program, address, backend, &mut Quiet)
                    .map_err(SessionFault::Store)?
                {
                    Maybe::Present(checkpoints) => {
                        let count = ItemCount::from(checkpoints.items().len());
                        let resume =
                            Resume::from_checkpoints(checkpoints).map_err(SessionFault::Resume)?;
                        Maybe::Present((resume, count))
                    },
                    Maybe::Absent(reason) => Maybe::Absent(unrestored(reason)),
                };
                (
                    Imports::of(&module, SourceIndex::from(0_usize)),
                    Snapshot::of(&program, module.origins()),
                    documentation_of(&module, SourceIndex::from(0_usize)),
                    restored,
                )
            },
        };
        let (incremental, restored) = match restored {
            Maybe::Present((resume, count)) => (
                IncrementalSession::reopen(store, backend, resume),
                Maybe::Present(count),
            ),
            Maybe::Absent(reason) => (
                IncrementalSession::new(store, backend, CheckBudget::DEFAULT),
                Maybe::Absent(reason),
            ),
        };
        Ok(Reopened {
            session: Self {
                grammar: Arc::new(grammar),
                root,
                incremental,
                blocks,
                imports,
                snapshot,
                documentation,
                lowerings,
                decisions,
                forms,
                threads,
                admission: Maybe::Absent(admission::Absent::Idle),
                tables: Tables::Unkept,
            },
            restored,
        })
    }

    /// Submit one revision: [`judge`](Self::judge) it, then
    /// [`admit`](Self::admit) it.
    ///
    /// # Specification
    /// - requires: `revision` is the whole text of the session's source.
    /// - ensures: as [`judge`](Self::judge), and for a revision the lowering
    ///   reads, the composition then carries the kernel artifact its admission
    ///   exported and the submission the kernel checkpoint committed into the
    ///   block store: the composition `gandr check` gives the same text under
    ///   the same root, kernel artifact included. An accepted revision's
    ///   resumed checkpoints are those a fresh session records for its text,
    ///   its items judged exactly those whose content the latest resume does
    ///   not hold or whose recorded answers the fresh judgement does not
    ///   record; the latest accepted text submitted again judges no item, molds
    ///   no form and composes the same report and kernel checkpoint.
    /// - provides: a report whose verdicts are the batch pipeline's, beside the
    ///   census of what the resume adopted, the manifest of the kernel
    ///   environment it leaves, the edits that led to it and the repairs the
    ///   parser made.
    /// - fails: as [`judge`](Self::judge); and [`SessionFault::Compose`] with
    ///   [`ComposeFault::Readmission`] when the kernel does not re-derive an
    ///   acceptance of a revision the judgement accepted, the session then
    ///   holding that revision.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — finite corpus agreement with the batch pipeline;
    ///   accepted, refused and edited revisions; exact synthesis, import,
    ///   snapshot and lowering-count observations; and kernel readback.
    ///   Generated edit/replay and incremental/batch witnesses provide
    ///   independent bounded relational checks; L2 — generated edit chains
    ///   compare the resumed checkpoints and judged items with a from-scratch
    ///   session and resubmit each text.
    /// - witness: `tests::corpus::every_source_submits_as_the_walk_composes_it`
    /// - witness: `tests::session::whole_file_submit_carries_definitions_forward`
    /// - witness: `tests::incremental::an_edit_judges_exactly_the_items_its_support_logs_separate`
    /// - witness: `tests::incremental::a_retyped_definition_dirties_its_reader_and_nothing_else`
    /// - witness: `tests::checkpoint::a_reopened_session_reads_its_kernel_checkpoint_through_the_decoder`
    /// - witness: `tests::checkpoint::a_kernel_store_failure_preserves_resume_and_edit_state`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |submission| match submission.composed {
        Composed::Settled { ref kernel, .. } => matches!(kernel, Maybe::Present(_))
            && matches!(submission.kernel, Maybe::Present(_)),
        Composed::Refused(_) => matches!(submission.kernel, Maybe::Absent(admitted::Absent::RefusedWhole)),
    }) && matches!(self.admission, Maybe::Absent(admission::Absent::Idle)))]
    #[inline]
    pub fn submit<'text>(
        &mut self,
        revision: SourceText<'text>,
    ) -> Result<Submission<'text>, SessionFault<'text>>
    where
        Store: CheckpointStore,
        Blocks: BlockStore,
    {
        let submission = self
            .judge_with(
                revision,
                (&Unit::single(), ByteOffset::from(0_usize)),
                None,
                |_| (),
                &Unretired,
            )?
            .whole();
        self.admit_into(submission)
    }

    /// Submit `revision`, the text `unit` lays out with the document's own
    /// text from `base` on: [`judge_unit_reading`](Self::judge_unit_reading)
    /// it, the closure's lowering kept in `slot`, then [`admit`](Self::admit)
    /// it.
    ///
    /// # Specification
    /// - requires: as [`judge_unit_reading`](Self::judge_unit_reading).
    /// - ensures: as [`submit`](Self::submit), over the unit: the composition
    ///   `gandr check` gives the document's file, kernel artifact included.
    /// - provides: a document that imports a sibling, submitted as the walk
    ///   composes it.
    /// - fails: as [`submit`](Self::submit).
    /// - panics: none.
    /// - executable: none — [`submit`](Self::submit) states the clauses and
    ///   submits through the same judgement and admission.
    ///
    /// # Errors
    /// As [`submit`](Self::submit).
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every corpus source, an importer among them, submits
    ///   as the walk composes it.
    /// - witness: `tests::corpus::every_source_submits_as_the_walk_composes_it`
    #[inline]
    pub fn submit_unit<'text>(
        &mut self,
        revision: SourceText<'text>,
        unit: &Unit,
        base: ByteOffset,
        slot: &'text ClosureSlot,
    ) -> Result<Submission<'text>, SessionFault<'text>>
    where
        Store: CheckpointStore,
        Blocks: BlockStore,
    {
        let submission = self
            .judge_with(revision, (unit, base), Some(slot), |_| (), &Unretired)?
            .whole();
        self.admit_into(submission)
    }

    /// `submission`, the judgement the session holds the admission of, with
    /// the admission run: its composition carrying the kernel artifact and
    /// the submission the kernel checkpoint.
    ///
    /// # Specification
    /// - requires: `submission` is the session's latest judgement.
    /// - ensures: as [`submit`](Self::submit) past the judgement.
    /// - fails: [`SessionFault::Compose`] with [`ComposeFault::Readmission`]
    ///   when the kernel does not re-derive an acceptance.
    /// - panics: none.
    /// - executable: none — [`submit`](Self::submit) states the clauses.
    ///
    /// # Errors
    /// As the specification's fails clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`submit`](Self::submit).
    /// - witness: `tests::session::whole_file_submit_carries_definitions_forward`
    fn admit_into<'text>(
        &mut self,
        mut submission: Submission<'text>,
    ) -> Result<Submission<'text>, SessionFault<'text>>
    where
        Store: CheckpointStore,
        Blocks: BlockStore,
    {
        if let Maybe::Present(admitted) = self
            .admit()
            .map_err(|fault| SessionFault::Compose(ComposeFault::Readmission(fault)))?
        {
            let Admitted {
                kernel, checkpoint, ..
            } = admitted;
            submission.composed = submission.composed.admitted(kernel);
            submission.kernel = Maybe::Present(checkpoint);
        }
        Ok(submission)
    }

    /// Judge one revision: parse it through the form store, lower it, judge
    /// and settle it, and resume the incremental checker over it, keeping its
    /// kernel admission for [`admit`](Self::admit).
    ///
    /// # Specification
    /// - requires: `revision` is the whole text of the session's source.
    /// - ensures: any admission an earlier judgement left is dropped first.
    ///   `revision` is parsed through the session's form store — every form
    ///   whose identity the store holds taken up, the rest molded on the
    ///   session's threads — into the parse
    ///   [`parse`](gandr_surface_parser::parse) gives it, and the store then
    ///   holds the revision's forms; the submission carries how many forms were
    ///   molded. The parse is lowered exactly once, and the lowering count is
    ///   one more. A revision the lowering reads is judged and settled by the
    ///   dispatcher's [`judge`](gandr_surface_dispatcher::judge) — the
    ///   composition `gandr check` gives the same text under the same root, its
    ///   kernel artifact not yet exported — and the same declarations are
    ///   submitted to the incremental checker, which resumes from the latest
    ///   accepted revision and persists the new checkpoints; the submission
    ///   carries the [`diff`] of the latest accepted revision's snapshot and
    ///   this one's, and no kernel checkpoint yet
    ///   ([`admitted::Absent::Pending`]); the session then holds the revision's
    ///   resume, import scope and snapshot, and its admission. A revision the
    ///   lowering refuses as a whole is reported as [`Composed::Refused`] with
    ///   no resume, no edits and no kernel checkpoint, and leaves no admission.
    ///   Its accepted state is unchanged, but the lowering attempt is counted.
    ///   Either way the submission carries the parse's completion obligations,
    ///   in source order.
    /// - provides: the interactive half of a submission: everything a face
    ///   renders, before the kernel has been offered anything.
    /// - fails: [`SessionFault::Compose`] when the parse or the lowering
    ///   faults, and when the settle comparison refuses the verdicts — a kernel
    ///   disagreement, found by running the admission then, reported in its
    ///   place, as [`judge_module`](gandr_surface_dispatcher::judge_module)
    ///   reports it — each with the accepted state unchanged;
    ///   [`SessionFault::Unordered`] when the lowered positions do not ascend,
    ///   also retaining accepted state; each attempt remains counted.
    ///   [`SessionFault::Resume`] occurs when the resume fails, the incremental
    ///   checker then holding no resume so the next revision is judged whole.
    /// - panics: none.
    /// - economy: each taken-up form's checkpoint is cloned once into the join
    ///   and each molded form parked once; the lowered arena is cloned once per
    ///   accepted revision, so the judgement and the resume each check over
    ///   their own copy; the snapshot and its diff are each one walk of the
    ///   revision's terms.
    ///
    /// # Errors
    /// As above. A persistence failure with a retained resume is carried as
    /// [`Persistence::Failed`]; without a resume it is [`SessionFault::Store`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — finite corpus agreement with the batch pipeline;
    ///   accepted, refused and edited revisions; exact synthesis, import,
    ///   snapshot and lowering-count observations. Generated edit/replay and
    ///   incremental/batch witnesses provide independent bounded relational
    ///   checks; a judged revision renders the reports its submission renders.
    ///   The predicate avoids cloning prior session state or repeating parsing,
    ///   judgement, evaluation or storage.
    /// - witness: `tests::corpus::every_source_submits_as_the_walk_composes_it`
    /// - witness: `tests::session::whole_file_submit_carries_definitions_forward`
    /// - witness: `tests::session::failed_submission_retains_latest_synthesis`
    /// - witness: `tests::session::import_namespace_carries_across_lines_and_resolves_source_declarations`
    /// - witness: `tests::session::a_judged_revision_reports_before_its_admission`
    /// - witness: `tests::edit::a_submission_carries_the_edits_from_the_last_accepted_revision`
    /// - witness: `tests::diag_obligations::lowered_carries_the_parse_obligations_verbatim`
    /// - witness: `tests::checkpoint::a_store_failure_is_reported_and_the_session_still_resumes`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body composes and judges the whole revision; the check recomputes its standing from that composition once"
        )
    )]
    #[spec(
        captures: before = (
    usize::from(self.lowerings),
    self.snapshot.items().len(),
    self.imports.rows.len(),
),
        ensures: |ret| {
    usize::from(self.lowerings) == before.0.saturating_add(1_usize)
        && match ret {
            Ok(ref submission) => {
                submission.root == self.root && submission.text == revision
                    && submission.standing
                        == Standing::of(self.root, &submission.composed)
                    && submission
                        .obligations
                        .windows(2)
                        .all(|pair| {
                            matches!(pair, [left, right] if left.span <= right.span)
                        })
                    && match submission.composed {
                        Composed::Refused(_) => {
                            matches!(
                                submission.resumed,
                                Maybe::Absent(resumed::Absent::RefusedWhole)
                            )
                                && matches!(
                                    submission.edits,
                                    Maybe::Absent(resumed::Absent::RefusedWhole)
                                )
                                && matches!(
                                    submission.kernel,
                                    Maybe::Absent(admitted::Absent::RefusedWhole)
                                )
                                && matches!(self.admission, Maybe::Absent(admission::Absent::Idle))
                                && self.snapshot.items().len() == before.1
                                && self.imports.rows.len() == before.2
                        }
                        Composed::Settled { ref kernel, .. } => {
                            matches!(submission.resumed, Maybe::Present(_))
                                && matches!(submission.edits, Maybe::Present(_))
                                && matches!(kernel, Maybe::Absent(_))
                                && matches!(
                                    submission.kernel,
                                    Maybe::Absent(admitted::Absent::Pending)
                                )
                                && matches!(self.admission, Maybe::Present(_))
                                && matches!(
                                    self.incremental.last(), Maybe::Present(resume) if resume
                                    .handles().len() == self.snapshot.items().len()
                                )
                        }
                    }
            }
            Err(_) => {
                self.snapshot.items().len() == before.1
                    && self.imports.rows.len() == before.2
                    && matches!(self.admission, Maybe::Absent(admission::Absent::Idle))
            }
        }
},
    )]
    #[inline]
    pub fn judge<'text>(
        &mut self,
        revision: SourceText<'text>,
    ) -> Result<Submission<'text>, SessionFault<'text>>
    where
        Store: CheckpointStore,
    {
        self.judge_reading(revision, |_| ())
    }

    /// Judge `revision` as [`judge`](Self::judge) does, handing `read` the
    /// revision's tree before the lowering consumes it.
    ///
    /// A face that reads the revision's structure beside its judgement — an
    /// editor finding the form under its caret — reads the tree the judgement
    /// parsed, form by form from the store, instead of parsing the whole
    /// revision a second time on the path to its first publication.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: what [`judge`](Self::judge) ensures of `revision`; `read` is
    ///   called once with the revision's tree, whose source is `revision`, when
    ///   the parse commits, and never when it faults.
    /// - provides: the tree of a judged revision to a face, at no second parse.
    /// - fails: as [`judge`](Self::judge).
    /// - panics: only by propagating a panic of `read`.
    /// - executable: none — what `read` observes is the caller's to state; the
    ///   judgement's clauses are [`judge`](Self::judge)'s, which judges through
    ///   this.
    ///
    /// # Errors
    /// As [`judge`](Self::judge).
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a judged revision is read once, as the tree of its
    ///   own text, and reports what the plain judgement of it reports; a reader
    ///   called on a stale or second parse, or not at all, fails it.
    /// - witness: `tests::session::a_judged_revision_hands_its_tree_to_a_reader`
    #[inline]
    pub fn judge_reading<'text, Read>(
        &mut self,
        revision: SourceText<'text>,
        read: Read,
    ) -> Result<Submission<'text>, SessionFault<'text>>
    where
        Store: CheckpointStore,
        Read: FnOnce(&SyntaxTree<'text>),
    {
        self.judge_with(
            revision,
            (&Unit::single(), ByteOffset::from(0_usize)),
            None,
            read,
            &Unretired,
        )
        .map(Polled::whole)
    }

    /// [`judge_reading`](Self::judge_reading), polling `retirement` before each
    /// item the incremental pass adopts or judges.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: while every poll answers wanted, [`Polled::Whole`] with what
    ///   [`judge_reading`](Self::judge_reading) answers. Retired before an
    ///   item, [`Polled::Retired`]: the incremental session holds the resume it
    ///   held, and the imports, snapshot and documentation the session holds
    ///   are the last accepted revision's; the session holds no admission.
    /// - provides: an editor's judgement that a newer revision overtakes stops
    ///   at its next item, on whatever thread runs it.
    /// - fails: as [`judge`](Self::judge).
    /// - panics: only by propagating a panic of `read`.
    /// - executable: none — as [`judge_reading`](Self::judge_reading).
    ///
    /// # Errors
    /// As [`judge`](Self::judge).
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a judgement retired part way leaves the next one
    ///   judging what it would have with no retired one before it.
    /// - witness: `tests::session::a_retired_judgement_leaves_the_next_its_resume_1547`
    #[inline]
    pub fn judge_reading_retiring<'text, Read, Poll>(
        &mut self,
        revision: SourceText<'text>,
        read: Read,
        retirement: &Poll,
    ) -> Result<Polled<Submission<'text>, Poll::Retired, ()>, SessionFault<'text>>
    where
        Store: CheckpointStore,
        Read: FnOnce(&SyntaxTree<'text>),
        Poll: Retirement,
    {
        self.judge_with(
            revision,
            (&Unit::single(), ByteOffset::from(0_usize)),
            None,
            read,
            retirement,
        )
    }

    /// Judge `revision`, the text `unit` lays out — the document after the
    /// siblings it imports, its own text from `base` on — as
    /// [`judge_reading`](Self::judge_reading) judges a document alone, the
    /// closure's lowering the submission borrows kept in `slot`.
    ///
    /// A document that imports a sibling is judged over it, as the walk judges
    /// the source: the siblings are the prefix of the unit's constants, so the
    /// incremental checker resumes over them unchanged while the revision's
    /// own declarations change. The siblings — the closure — are parsed and
    /// lowered once per process for every document laid after them: the
    /// document's own text is parsed through the form store alone, laid after
    /// the closure's tree, and lowered on the closure's lowering.
    ///
    /// # Specification
    /// - requires: `revision` is the text `unit` lays out, its last source
    ///   starting at `base`; `slot` is the submission's own.
    /// - ensures: what [`judge_reading`](Self::judge_reading) ensures of a
    ///   revision, over the unit: `read` is called once with the tree of
    ///   `revision`; the submission's text is `revision` and its base `base`;
    ///   its composition reports the declarations, refusals, shadowed builtins,
    ///   inferred exits and runs written from `base` on, as the dispatcher's
    ///   [`judge_member`] projects it, and its completion obligations are those
    ///   from `base` on; the import scope held is the revision's own. Exactly
    ///   [`judge_reading`](Self::judge_reading) at offset zero of
    ///   [`Unit::single`]. When the closure's text is one a document can be
    ///   laid after, the tree is the document's parse laid after the closure's
    ///   ([`ParseResult::after`]), the closure's lowering is held in `slot` and
    ///   in the process's store, and the form census is the document's own;
    ///   when the closure's lowering reached its end, its declarations are
    ///   judged, and the incremental pass led over their items
    ///   ([`Closure::led`]), once per process and root; the document is lowered
    ///   onto the arena that pass left, which extends the judgement's
    ///   ([`lower_onto_closure`]), judged on a copy of the judgement's state
    ///   ([`judge_member_after`]) and submitted after the pass's state
    ///   ([`IncrementalSession::submit_after`]) — onto the judgement's own
    ///   arena and submitted whole when the pass holds no state — and otherwise
    ///   the module is the closure's lowering resumed over the tree
    ///   ([`lower_resumed_unit`]), judged whole.
    /// - provides: an editor's judgement of a document that imports a sibling,
    ///   whose diagnostics are those `gandr check` gives the file.
    /// - fails: as [`judge`](Self::judge).
    /// - panics: only by propagating a panic of `read`.
    /// - executable: none — the clauses are [`judge`](Self::judge)'s over the
    ///   unit, which judges through the same path.
    ///
    /// # Errors
    /// As [`judge`](Self::judge).
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every corpus source, an importer among them, submits
    ///   as the walk composes it; an importer submitted twice lowers its
    ///   closure once.
    /// - witness: `tests::corpus::every_source_submits_as_the_walk_composes_it`
    /// - witness: `tests::session::an_importer_lowers_its_closure_once_1033`
    #[inline]
    pub fn judge_unit_reading<'text, Read>(
        &mut self,
        revision: SourceText<'text>,
        unit: &Unit,
        base: ByteOffset,
        slot: &'text ClosureSlot,
        read: Read,
    ) -> Result<Submission<'text>, SessionFault<'text>>
    where
        Store: CheckpointStore,
        Read: FnOnce(&SyntaxTree<'text>),
    {
        self.judge_with(revision, (unit, base), Some(slot), read, &Unretired)
            .map(Polled::whole)
    }

    /// [`judge_unit_reading`](Self::judge_unit_reading), polling `retirement`
    /// before each item the incremental pass adopts or judges.
    ///
    /// # Specification
    /// - requires: as [`judge_unit_reading`](Self::judge_unit_reading).
    /// - ensures: while every poll answers wanted, [`Polled::Whole`] with what
    ///   [`judge_unit_reading`](Self::judge_unit_reading) answers; retired
    ///   before an item, as
    ///   [`judge_reading_retiring`](Self::judge_reading_retiring) states.
    /// - provides: as [`judge_reading_retiring`](Self::judge_reading_retiring),
    ///   for a document that imports a sibling.
    /// - fails: as [`judge`](Self::judge).
    /// - panics: only by propagating a panic of `read`.
    /// - executable: none — as
    ///   [`judge_unit_reading`](Self::judge_unit_reading).
    ///
    /// # Errors
    /// As [`judge`](Self::judge).
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as
    ///   [`judge_reading_retiring`](Self::judge_reading_retiring).
    /// - witness: `tests::session::a_retired_judgement_leaves_the_next_its_resume_1547`
    #[inline]
    pub fn judge_unit_reading_retiring<'text, Read, Poll>(
        &mut self,
        revision: SourceText<'text>,
        (unit, base): (&Unit, ByteOffset),
        slot: &'text ClosureSlot,
        read: Read,
        retirement: &Poll,
    ) -> Result<Polled<Submission<'text>, Poll::Retired, ()>, SessionFault<'text>>
    where
        Store: CheckpointStore,
        Read: FnOnce(&SyntaxTree<'text>),
        Poll: Retirement,
    {
        self.judge_with(revision, (unit, base), Some(slot), read, retirement)
    }

    /// Judge `revision` as
    /// [`judge_unit_reading_retiring`](Self::judge_unit_reading_retiring)
    /// does, its closure lowered whole without `slot`.
    ///
    /// # Specification
    /// - requires: as [`judge_unit_reading`](Self::judge_unit_reading).
    /// - ensures: as
    ///   [`judge_unit_reading_retiring`](Self::judge_unit_reading_retiring);
    ///   without a slot, the text is parsed through the form store and lowered
    ///   whole; with one, a session with nothing submitted resumes from the
    ///   checkpoints the closure's items hold, and the first submission over
    ///   the closure keeps its items' checkpoints there.
    /// - fails: as [`judge`](Self::judge).
    /// - panics: only by propagating a panic of `read`.
    /// - executable: none — as
    ///   [`judge_unit_reading`](Self::judge_unit_reading).
    ///
    /// # Errors
    /// As [`judge`](Self::judge).
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`judge_unit_reading`](Self::judge_unit_reading).
    /// - witness: `tests::corpus::every_source_submits_as_the_walk_composes_it`
    /// - witness: `tests::session::an_importer_lowers_its_closure_once_1033`
    /// - witness: `tests::session::a_retired_judgement_leaves_the_next_its_resume_1547`
    fn judge_with<'text, Read, Poll>(
        &mut self,
        revision: SourceText<'text>,
        (unit, base): (&Unit, ByteOffset),
        slot: Option<&'text ClosureSlot>,
        read: Read,
        retirement: &Poll,
    ) -> Result<Polled<Submission<'text>, Poll::Retired, ()>, SessionFault<'text>>
    where
        Store: CheckpointStore,
        Read: FnOnce(&SyntaxTree<'text>),
        Poll: Retirement,
    {
        let own = SourceIndex::from(unit.sources().len().saturating_sub(1_usize));
        self.admission = Maybe::Absent(admission::Absent::Idle);
        let parse_fault = |fault| SessionFault::Compose(ComposeFault::Parse(fault));
        let closure = slot.and_then(|slot| match self.closure_lowering(revision, unit, base) {
            Held::Lowered(lowered) => {
                let held = slot.0.get_or_init(|| Arc::clone(&lowered));
                Arc::ptr_eq(held, &lowered).then_some(&**held)
            },
            Held::Whole => None,
        });
        let (lowering, checking, led, forms) = if let Some(closure) = closure {
            let document = SourceText::from(
                <&str>::from(revision)
                    .get(usize::from(base) ..)
                    .unwrap_or_default(),
            );
            let (parsed, forms) = self
                .forms
                .parse(&self.grammar, document, self.threads)
                .map_err(parse_fault)?;
            let parsed = parsed
                .after(closure.lowering().tree(), revision)
                .map_err(|fault| parse_fault(MeldError::Build(fault)))?;
            read(parsed.tree());
            let root = self.root.corpus_root();
            let (lowering, checking, led) = match closure.judged(root) {
                Some(judged) => {
                    let led = closure.led(root);
                    let onto = led.map_or_else(|| judged.arena(), Led::arena);
                    lower_onto_closure(
                        judged,
                        onto,
                        parsed,
                        unit,
                        &mut self.lowerings,
                        &mut self.decisions,
                    )
                    .map(|(lowering, checking)| {
                        // The incremental pass starts after the closure's
                        // items only over the arena it left them in.
                        let led = match checking {
                            Checking::After(_) => led,
                            Checking::Whole => None,
                        };
                        (lowering, checking, led)
                    })
                },
                None => lower_resumed_unit(
                    closure.lowering(),
                    parsed,
                    unit,
                    &mut self.lowerings,
                    &mut self.decisions,
                )
                .map(|lowering| (lowering, Checking::Whole, None)),
            }
            .map_err(SessionFault::Compose)?;
            (lowering, checking, led, forms)
        }
        else {
            let (parsed, forms) = self
                .forms
                .parse(&self.grammar, revision, self.threads)
                .map_err(parse_fault)?;
            read(parsed.tree());
            let lowering = lower_parsed_unit(
                &self.grammar,
                parsed,
                unit,
                &mut self.lowerings,
                &mut self.decisions,
            )
            .map_err(SessionFault::Compose)?;
            (lowering, Checking::Whole, None, forms)
        };
        let mut obligations = lowering.obligations().to_vec();
        obligations.retain(|obligation| obligation.span.start() >= base);
        obligations.sort_by_key(|obligation| obligation.span);
        let (module, arena) = match lowering.into_lowered() {
            Lowered::Module { module, arena } => (module, arena),
            Lowered::Refused(refusal) => {
                let composed = Composed::Refused(refusal);
                return Ok(Polled::Whole(Submission {
                    root: self.root,
                    text: revision,
                    base,
                    standing: Standing::of(self.root, &composed),
                    composed,
                    resumed: Maybe::Absent(resumed::Absent::RefusedWhole),
                    edits: Maybe::Absent(resumed::Absent::RefusedWhole),
                    kernel: Maybe::Absent(admitted::Absent::RefusedWhole),
                    obligations,
                    forms,
                    table: Maybe::Absent(match self.tables {
                        Tables::Kept => tabled::Absent::RefusedWhole,
                        Tables::Unkept => tabled::Absent::Untabled,
                    }),
                }));
            },
        };
        // economy: one arena copy per accepted revision, of the revision's own
        // nodes when it lowered onto a judged closure's frozen arena; the
        // reversal is a report assembled from the resume's own verdicts, which
        // retires the whole-module judgement and this copy with it.
        let mut items = program(&module, arena.clone()).map_err(SessionFault::Unordered)?;
        let imports = Imports::of(&module, own);
        let documentation = documentation_of(&module, own);
        // The closure's declarations — those written before the revision's own
        // source — lead the judged ones, a declaration the lowering refused
        // being judged nowhere.
        let boundary = module
            .declarations()
            .iter()
            .filter(|declaration| !matches!(declaration.outcome(), DeclarationOutcome::Refused(_)))
            .take_while(|declaration| declaration.span().start() < base)
            .count();
        // The closure's items read alike in every revision laid after it, so
        // their images are read once and shared.
        let snapshot = closure.and_then(Closure::snapshot).map_or_else(
            || Snapshot::of(&items, module.origins()),
            |leading| Snapshot::of_after(&items, module.origins(), leading),
        );
        if let Some(closure) = closure {
            closure.keep_snapshot(|| snapshot.leading(ItemOrdinal::from(boundary)));
        }
        let ((settled, admission), table) = match self.tables {
            Tables::Kept => {
                let (judged, table) = judge_member_tabled(
                    self.root.corpus_root(),
                    (module, revision),
                    arena,
                    (&HostGrant::UNBOUNDED, checking),
                    (unit, base),
                );
                (judged.into_parts(), table)
            },
            Tables::Unkept => (
                judge_member_after(
                    self.root.corpus_root(),
                    (module, revision),
                    arena,
                    (&HostGrant::UNBOUNDED, checking),
                    base,
                )
                .into_parts(),
                Maybe::Absent(tabled::Absent::Untabled),
            ),
        };
        let composed = match settled {
            Ok(composed) => composed,
            // The readmission ran before the settle comparison once; a kernel
            // disagreement still takes precedence over a settle fault.
            Err(fault) => {
                return Err(SessionFault::Compose(match admission.admit() {
                    Ok(_) => ComposeFault::Settle(fault),
                    Err(disagreement) => ComposeFault::Readmission(disagreement),
                }));
            },
        };
        let submitted = match led {
            Some(led) => self.incremental.submit_after_retiring(
                &mut items,
                led.leading(),
                &mut Quiet,
                retirement,
            ),
            None => self
                .incremental
                .submit_retiring(&mut items, &mut Quiet, retirement),
        };
        let (census, persistence) = match submitted {
            Ok(Polled::Whole(census)) => (census, match Store::KEEPING {
                Keeping::Kept => Persistence::Stored,
                Keeping::Discarded => Persistence::Discarded,
            }),
            // Retired before an item: the incremental session holds the resume
            // it held, and the session keeps the imports, snapshot and
            // documentation of the revision it last accepted.
            Ok(Polled::Retired(retired, ())) => return Ok(Polled::Retired(retired, ())),
            Err(SessionError::Resume(error)) => return Err(SessionFault::Resume(error)),
            // The incremental session keeps the new resume when persisting
            // fails; were it to hold none, there is no census to report, so
            // the store's failure fails the submission instead.
            Err(SessionError::Store(error)) => match self.incremental.last() {
                Maybe::Present(resume) => (resume.census(), Persistence::Failed(error)),
                Maybe::Absent(_) => return Err(SessionFault::Store(error)),
            },
        };
        let edits = diff(&self.snapshot, &snapshot);
        self.imports = imports;
        self.snapshot = snapshot;
        self.documentation = documentation;
        self.admission = Maybe::Present(Pending {
            admission,
            boundary,
            closure: String::from(
                <&str>::from(revision)
                    .get(.. usize::from(base))
                    .unwrap_or_default(),
            ),
        });
        Ok(Polled::Whole(Submission {
            root: self.root,
            text: revision,
            base,
            standing: Standing::of(self.root, &composed),
            composed,
            resumed: Maybe::Present(Resumed {
                census,
                persistence,
            }),
            edits: Maybe::Present(edits),
            kernel: Maybe::Absent(admitted::Absent::Pending),
            obligations,
            forms,
            table,
        }))
    }

    /// Judge each of `candidates` — whole texts of the session's source, each
    /// a revision the caller might submit — without submitting any, and rank
    /// what they became.
    ///
    /// # Specification
    /// - requires: each candidate is the whole text of the session's source.
    /// - ensures: one trial per candidate. Each candidate is parsed through the
    ///   form store without changing it ([`FormStore::parse_held`]), lowered,
    ///   and judged and settled by the dispatcher's
    ///   [`judge`](gandr_surface_dispatcher::judge), so its composition,
    ///   standing and completion obligations are those [`judge`](Self::judge)
    ///   gives the same text in a session that has accepted nothing; it carries
    ///   no resume and no edits ([`resumed::Absent::Tried`]) and no kernel
    ///   checkpoint ([`admitted::Absent::Pending`], or
    ///   [`admitted::Absent::RefusedWhole`] for a revision refused as a whole).
    ///   The trials are ranked: a composition the lowering read before one it
    ///   refused whole, and both before a fault; then fewer refused
    ///   declarations, so a wrong fill ranks below one that leaves a goal; then
    ///   fewer unsettled declarations, fewer owed obligations and fewer parse
    ///   repairs; then the candidates' own order. The session is unchanged: its
    ///   form store, resume, snapshot, imports, documentation, lowering count
    ///   and admission are as they were.
    /// - provides: the batch a solving loop checks its drafts in — a model's
    ///   fills for a hole, a body's rewrites — with the latest accepted state
    ///   left for the edit that wins.
    /// - fails: never as a whole; a candidate's engine fault is its own trial's
    ///   [`SessionFault::Compose`]. The admission-order fault only the
    ///   incremental checker's item source raises is not reached, since a trial
    ///   offers it nothing.
    /// - panics: only by propagating a judging thread's panic.
    /// - economy: the candidates are judged on as many threads as the session's
    ///   width answers, never more than the candidates, the calling thread
    ///   among them, each thread taking the next candidate no thread has taken;
    ///   a lone candidate molds on the session's threads instead. Each
    ///   candidate reuses every form the store holds; nothing is copied out of
    ///   the session.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — candidates that settle, owe a goal, refuse a
    ///   declaration, are refused whole and repeat one another are each judged
    ///   as a fresh session judges them and ranked in that order, at one thread
    ///   and at several; the session's next submission resumes, molds and diffs
    ///   as if no trial had run. The receiver is shared, so the snapshot cannot
    ///   change through it; the predicate does not copy it, and the second
    ///   witness observes the session afterwards.
    /// - witness: `tests::trial::each_candidate_is_judged_as_a_fresh_session_judges_it`
    /// - witness: `tests::trial::a_trial_leaves_the_session_as_it_was`
    #[spec(
        captures: before = usize::from(self.lowerings),
        ensures: |ret| ret.len() == candidates.len()
            && usize::from(self.lowerings) == before
            && ret.iter().all(|trial| trial.outcome.as_ref().is_err()
                || trial.outcome.as_ref().is_ok_and(|submission|
                    candidates.get(usize::from(trial.candidate)) == Some(&submission.text)
                    && matches!(submission.resumed, Maybe::Absent(resumed::Absent::Tried))))
            && ret.windows(2).all(|pair| match *pair {
                [ref earlier, ref later] => trial_rank(earlier) <= trial_rank(later),
                _ => false,
            }),
    )]
    #[inline]
    #[must_use]
    pub fn trial<'text>(
        &self,
        candidates: &[SourceText<'text>],
    ) -> Vec<Trial<'text>>
    {
        let laid: Vec<(SourceText<'text>, Laying<'_>)> = candidates
            .iter()
            .map(|&candidate| (candidate, Laying::Alone))
            .collect();
        self.trial_unit(&laid)
    }

    /// Judge each of `candidates` — each a text its [`Laying`]'s unit lays
    /// out, a candidate document after the siblings it imports — as
    /// [`trial`](Self::trial) judges candidates alone.
    ///
    /// # Specification
    /// - requires: each candidate is laid out as its laying says.
    /// - ensures: what [`trial`](Self::trial) ensures, each candidate lowered
    ///   over its unit and its composition projected from its base on as
    ///   [`judge_unit_reading`](Self::judge_unit_reading) projects it.
    /// - provides: an editor's trial of fills in a document that imports a
    ///   sibling.
    /// - fails: as [`trial`](Self::trial).
    /// - panics: as [`trial`](Self::trial).
    /// - executable: none — [`trial`](Self::trial) states the clauses and
    ///   trials through this.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the trial witnesses, each candidate alone.
    /// - witness: `tests::trial::each_candidate_is_judged_as_a_fresh_session_judges_it`
    #[inline]
    #[must_use]
    pub fn trial_unit<'text>(
        &self,
        candidates: &[(SourceText<'text>, Laying<'_>)],
    ) -> Vec<Trial<'text>>
    {
        let (grammar, forms, root) = (&self.grammar, &self.forms, self.root);
        let threads = usize::from(NonZeroUsize::from(self.threads)).min(candidates.len());
        let molding = if candidates.len() == 1 {
            self.threads
        }
        else {
            Threads::ONE
        };
        let slots: Vec<OnceLock<Result<Submission<'text>, SessionFault<'text>>>> =
            candidates.iter().map(|_| OnceLock::new()).collect();
        let next = AtomicUsize::new(0);
        let work = || {
            loop {
                let index = next.fetch_add(1, Ordering::Relaxed);
                let (Some(&candidate), Some(slot)) = (candidates.get(index), slots.get(index))
                else {
                    break;
                };
                let _first = slot.set(try_candidate(grammar, forms, root, candidate, molding));
            }
        };
        thread::scope(|scope| {
            for _ in 1 .. threads {
                if thread::Builder::new().spawn_scoped(scope, work).is_err() {
                    break;
                }
            }
            work();
        });
        let mut trials: Vec<Trial<'text>> = slots
            .into_iter()
            .zip(candidates)
            .enumerate()
            .map(|(index, (slot, &candidate))| Trial {
                candidate: CandidateIndex(index),
                outcome: slot
                    .into_inner()
                    .unwrap_or_else(|| try_candidate(grammar, forms, root, candidate, molding)),
            })
            .collect();
        trials.sort_by_cached_key(trial_rank);
        trials
    }

    /// Run the admission the latest judgement left: offer its accepted
    /// declarations to the kernel, export what crossed and commit the export
    /// into the block store.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: with no admission held, [`admission::Absent::Idle`] and
    ///   nothing done. Otherwise the admission is taken and run: the kernel
    ///   artifact of every declaration that crossed, under its structured name
    ///   — the artifact
    ///   [`judge_module`](gandr_surface_dispatcher::judge_module) exports for
    ///   the same revision — beside the checkpoint [`build`] mints over the
    ///   records [`ArtifactRecordSet::from_artifact`] cuts from it, every node
    ///   of their tree then in the block store, or none when the checkpoint
    ///   store keeps nothing ([`KernelCheckpoint::Discarded`]); and how many
    ///   declarations the kernel was offered of how many were judged; or the
    ///   first refusal. The readmission of the import closure the revision was
    ///   laid out after is resumed from the one the process holds for the
    ///   closure's text whose declarations' checkpoints — content, consulted
    ///   answers and typing — are pointwise those of the latest resume, and is
    ///   held for the next admission otherwise
    ///   ([`readmit_resuming`](gandr_core_checker::bridge::readmit_resuming));
    ///   the closure's declarations then cross only when no such readmission is
    ///   held. Either way the session holds no admission after.
    /// - provides: the half of a submission that runs beside the interactive
    ///   loop: what the kernel re-derives, and the latency until the artifact
    ///   exists.
    /// - fails: the readmission of the first declaration the kernel did not
    ///   re-derive.
    /// - panics: none.
    ///
    /// # Errors
    /// The readmission of the first declaration the kernel did not re-derive.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a judged revision admitted afterwards carries the
    ///   kernel artifact and checkpoint its submission carries, a second
    ///   admission finds none held, and a refused revision leaves none; a
    ///   document laid out after its import closure offers the kernel its own
    ///   declarations alone once the closure was admitted, the artifact the
    ///   whole composition exports, and the whole closure again once a source
    ///   of it changed.
    /// - witness: `tests::session::a_judged_revision_reports_before_its_admission`
    /// - witness: `tests::session::an_edit_to_its_own_text_readmits_the_document_alone_776`
    /// - witness: `tests::checkpoint::a_reopened_session_reads_its_kernel_checkpoint_through_the_decoder`
    #[spec(ensures: |ret| matches!(self.admission, Maybe::Absent(admission::Absent::Idle))
        && ret.as_ref().is_ok_and(|admitted| match *admitted {
            Maybe::Present(ref admitted) => admitted.crossed() <= admitted.judged(),
            Maybe::Absent(_) => true,
        }) || ret.is_err())]
    #[inline]
    pub fn admit(&mut self) -> Result<Maybe<Admitted, admission::Absent>, Readmitted>
    where
        Store: CheckpointStore,
        Blocks: BlockStore,
    {
        let Maybe::Present(detached) = self.admission()
        else {
            return Ok(Maybe::Absent(admission::Absent::Idle));
        };
        self.settle(detached.run(&Unretired).whole())
    }

    /// Take the admission the latest judgement left, to run off the session.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: with no admission held, [`admission::Absent::Idle`];
    ///   otherwise the admission, the checkpoints of the latest resume, and the
    ///   readmission the process holds for the closure's text under the longest
    ///   run of them it holds one for. Either way the session holds no
    ///   admission after.
    /// - provides: what [`Detached::run`] runs on another thread, so the
    ///   session answers while the kernel works.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Detached::run`].
    /// - witness: `tests::session::a_retired_admission_leaves_what_it_crossed_to_the_next_1547`
    #[spec(ensures: matches!(self.admission, Maybe::Absent(admission::Absent::Idle)))]
    #[inline]
    pub fn admission(&mut self) -> Maybe<Detached, admission::Absent>
    {
        let held = core::mem::replace(&mut self.admission, Maybe::Absent(admission::Absent::Idle));
        let Maybe::Present(pending) = held
        else {
            return Maybe::Absent(admission::Absent::Idle);
        };
        let checkpoints = match self.incremental.last() {
            Maybe::Present(resume) => resume.checkpoints().items().to_vec(),
            Maybe::Absent(_) => Vec::new(),
        };
        let found = closures::find(SourceText::from(pending.closure.as_str()), &checkpoints);
        Maybe::Present(Detached {
            pending,
            checkpoints,
            found,
        })
    }

    /// Keep what an admission that ran whole made: the closure's readmission
    /// for the next admission, and the artifact's checkpoint in the block
    /// store.
    ///
    /// # Specification
    /// - requires: `ran` ran an admission [`Session::admission`] took from this
    ///   session, and no later judgement replaced the revision it judged.
    /// - ensures: as [`Session::admit`] for the admission `ran` ran.
    /// - provides: the half of an admission that writes the session's stores,
    ///   on the session's thread.
    /// - fails: the readmission of the first declaration the kernel did not
    ///   re-derive.
    /// - panics: none.
    ///
    /// # Errors
    /// The readmission of the first declaration the kernel did not re-derive.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Session::admit`].
    /// - witness: `tests::session::an_edit_to_its_own_text_readmits_the_document_alone_776`
    #[spec(ensures: |ret| ret.as_ref().is_ok_and(|admitted| match *admitted {
            Maybe::Present(ref admitted) => admitted.crossed() <= admitted.judged(),
            Maybe::Absent(_) => true,
        }) || ret.is_err())]
    #[inline]
    pub fn settle(
        &mut self,
        ran: Ran,
    ) -> Result<Maybe<Admitted, admission::Absent>, Readmitted>
    where
        Store: CheckpointStore,
        Blocks: BlockStore,
    {
        let Ran {
            resumption,
            boundary,
            closure,
            checkpoints,
            found,
        } = ran;
        let held = match (resumption.crossed, checkpoints.get(.. boundary)) {
            (Maybe::Present(crossed), Some(leading)) => {
                Some(closures::keep(closure, leading.to_vec(), crossed))
            },
            _ => found.filter(|found| {
                usize::from(resumption.resumed) == usize::from(found.crossed().boundary())
            }),
        };
        let kernel = resumption.artifact?;
        let checkpoint = match Store::KEEPING {
            Keeping::Kept => checkpoint_kernel(&kernel, &mut self.blocks, held.as_deref()),
            Keeping::Discarded => KernelCheckpoint::Discarded,
        };
        Ok(Maybe::Present(Admitted {
            kernel,
            checkpoint,
            crossed: DeclarationCount::from(
                usize::from(resumption.judged).saturating_sub(usize::from(resumption.resumed)),
            ),
            judged: DeclarationCount::from(usize::from(resumption.judged)),
        }))
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

    /// Have every judgement from here on keep the type table of its revision
    /// or not, as `tables` says: a table is what a client answering positions
    /// after a change reads, for the cost of typing the revision's bodies as
    /// written beside checking them.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn keep(
        &mut self,
        tables: Tables,
    )
    {
        self.tables = tables;
    }

    /// The grammar every revision is parsed under.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn grammar(&self) -> &Pbg
    {
        &self.grammar
    }

    /// Parse `revision` through the session's form store, leaving the store
    /// as it was: every form the latest submission molded is taken up and the
    /// rest molded on the session's threads.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// The commit's [`MeldError`], when its arena cannot be built.
    #[inline]
    pub fn parse_held<'text>(
        &self,
        revision: SourceText<'text>,
    ) -> Result<ParseResult<'text>, MeldError>
    {
        self.forms
            .parse_held(&self.grammar, revision, self.threads)
            .map(|(parsed, _census)| parsed)
    }

    /// Parse `revision`, the text `unit` lays out with the document's own
    /// text from `base` on, through the session's form store, leaving the
    /// store as it was: the document's own text laid after its closure's tree
    /// when the process holds the closure's lowering, as
    /// [`judge_unit_reading`](Self::judge_unit_reading) parses it, else the
    /// whole text as [`parse_held`](Self::parse_held) parses it.
    ///
    /// # Specification
    /// - requires: as [`judge_unit_reading`](Self::judge_unit_reading).
    /// - ensures: the tree the session's judgement of `revision` reads, its
    ///   obligations the document's.
    /// - provides: the parse a hover's typed run reads, the closure's forms
    ///   neither molded again nor looked up.
    /// - fails: the commit's [`MeldError`].
    /// - panics: none.
    ///
    /// # Errors
    /// The commit's [`MeldError`], when its arena cannot be built or the
    /// document's tree cannot be laid after the closure's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a corpus-shaped importer's held parse is the tree its
    ///   judgement read, laid after the closure the process holds.
    /// - witness: `tests::session::an_importer_lowers_its_closure_once_1033`
    #[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|parsed| parsed.tree().source() == revision))]
    #[inline]
    pub fn parse_held_unit<'text>(
        &self,
        revision: SourceText<'text>,
        unit: &Unit,
        base: ByteOffset,
    ) -> Result<ParseResult<'text>, MeldError>
    {
        parse_held_laid(
            &self.grammar,
            &self.forms,
            revision,
            Some((unit, base)),
            self.threads,
        )
        .map(|(parsed, _census, _closure)| parsed)
    }

    /// The type table of `revision`, the text `unit` lays out with the
    /// document's own text from `base` on, parsed as
    /// [`parse_held_unit`](Self::parse_held_unit) parses it, `read` handed its
    /// tree first, beside the key of the closure's lowering when the tree is
    /// laid after the lowering the process holds: typed after the closure's
    /// judgement under the session's root when the process holds the closure's
    /// lowering and the closure lowers to its end, else typed whole.
    ///
    /// # Specification
    /// - requires: as [`judge_unit_reading`](Self::judge_unit_reading).
    /// - ensures: [`TypeTable::of_parsed_after`] over the closure's judgement
    ///   ([`Closure::judged`]) under the session's root when the process holds
    ///   the closure's lowering and that judgement is made, else
    ///   [`TypeTable::of_parsed_unit`]; `None` when the text does not parse or
    ///   the lowering faults.
    /// - provides: the table a hover reads, typed in the document's size.
    /// - fails: never; a fault answers `None`.
    /// - panics: only by propagating a panic of `read` or a molding thread's.
    /// - executable: none — the table is the dispatcher's typed run, whose own
    ///   specification states what it holds.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an importer's hover answers its imported names at
    ///   their declarations' types.
    /// - witness: `tests::session::an_importer_lowers_its_closure_once_1033`
    #[inline]
    #[must_use]
    pub fn type_held_unit<'text, Read>(
        &self,
        revision: SourceText<'text>,
        (unit, base): (&Unit, ByteOffset),
        read: Read,
    ) -> Option<TypeTable>
    where
        Read: FnOnce(&SyntaxTree<'text>, Option<ClosureKey>),
    {
        let (parsed, _census, closure) = parse_held_laid(
            &self.grammar,
            &self.forms,
            revision,
            Some((unit, base)),
            self.threads,
        )
        .ok()?;
        read(
            parsed.tree(),
            closure
                .as_ref()
                .map(|closure| ClosureKey(Arc::downgrade(closure))),
        );
        match closure
            .as_deref()
            .and_then(|closure| closure.judged(self.root.corpus_root()))
        {
            Some(judged) => TypeTable::of_parsed_after(judged, parsed, unit, base).ok(),
            None => TypeTable::of_parsed_unit(&self.grammar, parsed, unit, base).ok(),
        }
    }

    /// Parse `revision` as [`type_held_unit`](Self::type_held_unit) does and
    /// hand `read` its tree and closure key, typing nothing: what a reader
    /// whose revision's table the judgement already kept
    /// ([`Submission::take_table`]) parses.
    ///
    /// # Specification
    /// - requires: as [`judge_unit_reading`](Self::judge_unit_reading).
    /// - ensures: `read` is called once, with the tree and key
    ///   [`type_held_unit`](Self::type_held_unit) hands it, when the text
    ///   parses.
    /// - fails: the parse's fault, `read` then not called.
    /// - panics: only by propagating a panic of `read` or a molding thread's.
    /// - executable: none — a parse handed to a reader.
    ///
    /// # Errors
    /// The [`MeldError`] the parse faulted with.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an importer's heads read off this parse are the heads
    ///   read off the parse its table is typed from.
    /// - witness: `tests::session::an_importer_lowers_its_closure_once_1033`
    #[inline]
    pub fn read_held_unit<'text, Read>(
        &self,
        revision: SourceText<'text>,
        (unit, base): (&Unit, ByteOffset),
        read: Read,
    ) -> Result<(), MeldError>
    where
        Read: FnOnce(&SyntaxTree<'text>, Option<ClosureKey>),
    {
        let (parsed, _census, closure) = parse_held_laid(
            &self.grammar,
            &self.forms,
            revision,
            Some((unit, base)),
            self.threads,
        )?;
        read(
            parsed.tree(),
            closure
                .as_ref()
                .map(|closure| ClosureKey(Arc::downgrade(closure))),
        );
        Ok(())
    }

    /// The lowering the process holds for `revision`'s closure — its text
    /// before `base`, `unit`'s sources before its last — lowered and kept
    /// when the process holds none.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Held::Whole`] when `unit` lays out one source, or `base` is
    ///   not where its last source starts; otherwise what the process holds for
    ///   the closure, or, when it holds nothing, the closure's lowering
    ///   ([`lower_closure`]) — [`Held::Whole`] when the closure is not one a
    ///   document can be laid after — kept in the process's store and counted
    ///   among the session's lowerings.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the clauses read the process's store, which the
    ///   call locks inside; the witness counts the lowerings a second judgement
    ///   makes.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an importer submitted twice lowers its closure once.
    /// - witness: `tests::session::an_importer_lowers_its_closure_once_1033`
    fn closure_lowering(
        &mut self,
        revision: SourceText<'_>,
        unit: &Unit,
        base: ByteOffset,
    ) -> Held
    {
        let Some((text, sources)) = closure_of(revision, unit, base)
        else {
            return Held::Whole;
        };
        let fingerprint = self.grammar.fingerprint();
        if let Some(held) = lowerings::find(text, sources, fingerprint) {
            return held;
        }
        let held = Unit::new(sources.to_vec())
            .ok()
            .and_then(|closure| {
                lower_closure(
                    Arc::clone(&self.grammar),
                    String::from(<&str>::from(text)),
                    closure,
                    &mut self.lowerings,
                )
                .ok()
            })
            .map_or(Held::Whole, |lowered| {
                Held::Lowered(Arc::new(Closure::new(lowered)))
            });
        lowerings::keep(
            String::from(<&str>::from(text)),
            sources.to_vec(),
            fingerprint,
            held.clone(),
        );
        held
    }

    /// Every source the session lowered: each source of a submission's unit,
    /// those of an import closure the process holds counted once, by the
    /// session that lowered the closure.
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

    /// The documentation of the latest accepted revision's declaration form
    /// whose key is `key`.
    ///
    /// # Specification
    /// - requires: nothing — any key is admissible input.
    /// - ensures: the text the lowering filed under `key` for the latest
    ///   accepted revision, or the undocumented absence when it filed none. A
    ///   key excludes documentation, so it is the same whichever spelling the
    ///   documentation took; a revision refused whole keeps the accepted one's.
    /// - provides: the documentation a hover shows beside a declaration.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a documented declaration answers its exact text, an
    ///   undocumented one the absence, and an edit to the documentation alone
    ///   answers the new text under the same key.
    /// - witness: `tests::session::documentation_is_kept_by_declaration_identity`
    #[spec(ensures: |ret| match ret {
        | Maybe::Present(found) => self.documentation.get(&key) == Some(found),
        | Maybe::Absent(_) => !self.documentation.contains_key(&key),
    })]
    #[inline]
    pub fn documentation(
        &self,
        key: NodeKey,
    ) -> Maybe<&DocumentationText, documentation::Absent>
    {
        self.documentation.get(&key).map_or(
            Maybe::Absent(documentation::Absent::Undocumented),
            Maybe::Present,
        )
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
    /// - hypothesis: L3 — bound and unbound aliases in two accepted revisions
    ///   and a duplicate-alias refusal retaining the previous scope. Exact URI
    ///   and source-span observations distinguish stale publication and wrong
    ///   row resolution.
    /// - witness: `tests::session::import_namespace_carries_across_lines_and_resolves_source_declarations`
    #[spec(
        ensures: |ret| match self.imports.scope.resolve(path) {
    Maybe::Present(binding) => {
        self.imports
            .rows
            .get(usize::from(binding.data))
            .map_or(
                matches!(ret, Maybe::Absent(import::Absent::Unbound)),
                |row| {
                    matches!(
                        ret, Maybe::Present(found) if
                        core::ptr::eq(core::ptr::from_ref(found),
                        core::ptr::from_ref(row))
                    )
                },
            )
    }
    Maybe::Absent(_) => matches!(ret, Maybe::Absent(import::Absent::Unbound)),
},
    )]
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
    /// - hypothesis: L3 — exact readback after reopening a real block store and
    ///   a manifest whose identity and tree are valid but whose kernel bytes
    ///   are refused. Format precedence and record/declaration cardinality are
    ///   executable; full byte, key and cut correspondence is witnessed without
    ///   repeating storage I/O.
    /// - witness: `tests::checkpoint::a_reopened_session_reads_its_kernel_checkpoint_through_the_decoder`
    /// - witness: `tests::checkpoint::a_matching_identity_over_bytes_the_kernel_refuses_is_refused`
    #[spec(
        ensures: |ret| match ret {
    Ok(ref decoded) => {
        manifest.kernel_format() == gandr_kernel_term::FORMAT_VERSION
            && u64::try_from(decoded.declarations().len().saturating_add(1_usize))
                == Ok(u64::from(manifest.record_count()))
    }
    Err(ArtifactError::UnsupportedKernelFormat { found }) => {
        found == manifest.kernel_format() && found != gandr_kernel_term::FORMAT_VERSION
    }
    Err(_) => manifest.kernel_format() == gandr_kernel_term::FORMAT_VERSION,
},
    )]
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
/// parameters, resuming the decode that cuts them after the closure's kernel
/// declarations `held` keeps, or keeping it there.
///
/// # Specification
/// - requires: `held`, when given, holds the readmission of the declarations
///   `kernel` leads with.
/// - ensures: [`KernelCheckpoint::Stored`] with the manifest [`build`] mints
///   over the records [`ArtifactRecordSet::from_artifact`] cuts from `kernel`,
///   every node of their tree then in `blocks`; otherwise
///   [`KernelCheckpoint::Failed`] with the first refusal. The records are cut
///   after the decode `held` keeps when it keeps one; otherwise `held`, when
///   given, keeps the decode of the declarations its readmission admitted.
/// - provides: the kernel checkpoint an accepted submission carries.
/// - fails: never; a refusal is the checkpoint's own variant.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a committed artifact read back after reopening is exactly
///   its independently decoded composition image. The predicate checks the
///   current format and mandatory header record; store mutation and full record
///   contents are observed by the readback witness rather than repeated in a
///   postcondition. A first-insertion refusal is checked by its exact variant
///   and continued resume/edit state, without assuming store rollback.
/// - witness: `tests::checkpoint::a_reopened_session_reads_its_kernel_checkpoint_through_the_decoder`
/// - witness: `tests::checkpoint::a_kernel_store_failure_preserves_resume_and_edit_state`
#[spec(
    ensures: |ret| match ret {
    KernelCheckpoint::Stored(ref manifest) => {
        manifest.kernel_format() == gandr_kernel_term::FORMAT_VERSION
            && u64::from(manifest.record_count()) >= 1_u64
    }
    KernelCheckpoint::Failed(_) => true,
    KernelCheckpoint::Discarded => false,
},
)]
fn checkpoint_kernel<Blocks>(
    kernel: &EncodedArtifact,
    blocks: &mut Blocks,
    held: Option<&ClosureAdmission>,
) -> KernelCheckpoint
where
    Blocks: BlockStore,
{
    let image = kernel.as_image();
    let records = held.map_or_else(
        || ArtifactRecordSet::from_artifact(image),
        |held| {
            held.decoded().map_or_else(
                || {
                    ArtifactRecordSet::from_artifact_keeping(image, held.crossed().kernel_end())
                        .map(|(records, decoded)| {
                            if let Maybe::Present(decoded) = decoded {
                                held.keep_decoded(decoded);
                            }
                            records
                        })
                },
                |decoded| ArtifactRecordSet::from_artifact_after(decoded, image),
            )
        },
    );
    let committed = records.and_then(|records| build(&records, TreeParams::current(), blocks));
    match committed {
        Ok(manifest) => KernelCheckpoint::Stored(manifest),
        Err(refusal) => KernelCheckpoint::Failed(refusal),
    }
}

/// Where a trial's candidate sits in the text it is judged in.
///
/// # Specification
/// - requires: nothing; a carrier.
/// - ensures: names the unit a candidate is the last source of and where its
///   own text starts, or that it is judged alone.
/// - provides: what [`Session::trial_unit`] judges each candidate under.
/// - fails: never.
/// - panics: none.
/// - executable: none — a carrier with no invariant of its own.
///
/// # Adequacy
/// - hypothesis: L3 — the trial witnesses judge each candidate alone.
/// - witness: `tests::trial::each_candidate_is_judged_as_a_fresh_session_judges_it`
#[derive(Clone, Copy, Debug)]
pub enum Laying<'unit>
{
    /// The candidate is the whole text judged.
    Alone,
    /// The candidate is the last source of `unit`, its own text from `base`
    /// on.
    Member
    {
        /// The unit the candidate is laid out in.
        unit: &'unit Unit,
        /// Where the candidate's own text starts.
        base: ByteOffset,
    },
}

impl Laying<'_>
{
    /// Where the candidate's own text starts: zero alone.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn base(self) -> ByteOffset
    {
        match self {
            Self::Alone => ByteOffset::from(0_usize),
            Self::Member { base, .. } => base,
        }
    }
}

/// Where a judgement of a document laid after its import closure keeps the
/// closure its submission borrows.
///
/// The slot holds the closure's lowering and its declarations' judgement: one
/// per submission, held as long as the submission is.
///
/// # Specification
/// trivial.
#[derive(Debug, Default)]
#[repr(transparent)]
pub struct ClosureSlot(OnceLock<Arc<Closure>>);

impl ClosureSlot
{
    /// An empty slot.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new() -> Self
    {
        Self(OnceLock::new())
    }
}

/// The name of a closure lowering the process holds.
///
/// A reader keeps what it makes of the closure's part of a tree under it, once
/// for every revision laid after the same lowering.
///
/// Two keys are equal exactly when they name the one lowering: the process
/// holds one lowering for each closure text, sources and grammar, so a key
/// stands for that content while the lowering is held. A key does not keep the
/// lowering alive, and no lowering made later is equal to it.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug)]
#[repr(transparent)]
pub struct ClosureKey(Weak<Closure>);

/// Whether anything still holds the lowering a [`ClosureKey`] names.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Holding
{
    /// The lowering is held, so a revision may yet be laid after it.
    Held,
    /// Nothing holds the lowering: no revision is laid after it again.
    Dropped,
}

impl ClosureKey
{
    /// Whether anything still holds the lowering the key names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn holding(&self) -> Holding
    {
        if self.0.strong_count() > 0 {
            Holding::Held
        }
        else {
            Holding::Dropped
        }
    }
}

impl PartialEq for ClosureKey
{
    /// Whether both keys name the one lowering. A key keeps its lowering's
    /// allocation, so no other lowering is made where it was.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn eq(
        &self,
        other: &Self,
    ) -> bool
    {
        Weak::ptr_eq(&self.0, &other.0)
    }
}

impl Eq for ClosureKey
{
}

/// The closure `revision` is laid out after: its text before `base`, and
/// `unit`'s sources before its last.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `None` when `unit` lays out one source or `base` is not where its
///   last source starts; otherwise the text before `base` and every source
///   before the last.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a document alone has no closure, and an importer's is its
///   siblings.
/// - witness: `tests::session::an_importer_lowers_its_closure_once_1033`
#[spec(ensures: |ret| ret.is_none_or(|(text, sources)| !sources.is_empty()
    && <&str>::from(text).len() == usize::from(base)))]
fn closure_of<'revision, 'unit>(
    revision: SourceText<'revision>,
    unit: &'unit Unit,
    base: ByteOffset,
) -> Option<(SourceText<'revision>, &'unit [UnitSource])>
{
    let (last, sources) = unit.sources().split_last()?;
    if sources.is_empty() || last.start() != base {
        return None;
    }
    let text = <&str>::from(revision).get(.. usize::from(base))?;
    Some((SourceText::from(text), sources))
}

/// Parse `revision` through `forms` without changing it, as the judgement of
/// a document laid out by `laid`'s unit with its own text from `laid`'s base
/// on reads it: the document's own text laid after its closure's tree when
/// the process holds the closure's lowering, else the whole text.
///
/// # Specification
/// - requires: `laid`, when given, lays `revision` out.
/// - ensures: the joined parse, the document's form census and the closure when
///   the process holds the closure's lowering, else [`FormStore::parse_held`]
///   of `revision` and no closure.
/// - fails: the commit's [`MeldError`], and a join the closure's tree refuses
///   as [`MeldError::Build`].
/// - panics: only by propagating a molding thread's panic.
///
/// # Errors
/// As the specification's fails clause.
///
/// # Adequacy
/// - hypothesis: L3 — a trial of a candidate and the held parse of an importer
///   read the tree a judgement of the same text reads.
/// - witness: `tests::trial::each_candidate_is_judged_as_a_fresh_session_judges_it`
/// - witness: `tests::session::an_importer_lowers_its_closure_once_1033`
#[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|&(ref parsed, _, _)| parsed.tree().source() == revision))]
fn parse_held_laid<'text>(
    grammar: &Pbg,
    forms: &FormStore,
    revision: SourceText<'text>,
    laid: Option<(&Unit, ByteOffset)>,
    threads: Threads,
) -> Result<(ParseResult<'text>, FormCensus, Option<Arc<Closure>>), MeldError>
{
    let held = laid
        .and_then(|(unit, base)| closure_of(revision, unit, base))
        .and_then(|(text, sources)| lowerings::find(text, sources, grammar.fingerprint()));
    match held {
        Some(Held::Lowered(closure)) => {
            let document = SourceText::from(
                <&str>::from(revision)
                    .get(<&str>::from(closure.lowering().text()).len() ..)
                    .unwrap_or_default(),
            );
            let (parsed, census) = forms.parse_held(grammar, document, threads)?;
            let joined = parsed
                .after(closure.lowering().tree(), revision)
                .map_err(MeldError::Build)?;
            Ok((joined, census, Some(closure)))
        },
        Some(Held::Whole) | None => forms
            .parse_held(grammar, revision, threads)
            .map(|(parsed, census)| (parsed, census, None)),
    }
}

/// One candidate of a trial, judged against the session's grammar, form store
/// and root and kept nowhere.
///
/// # Specification
/// - requires: `forms` is the session's form store and `root` its root;
///   `laid`'s candidate is laid out as its laying says.
/// - ensures: the candidate is parsed through `forms` without changing it, on
///   `threads` threads, as [`Session::parse_held_unit`] parses it, lowered
///   alone or over its laying's unit under a count of its own, and judged and
///   settled by the dispatcher's [`judge_member`] from its laying's base on;
///   the submission carries the composition, standing and completion
///   obligations [`Session::judge_unit_reading`] gives the text in a session
///   that has accepted nothing, no resume and no edits
///   ([`resumed::Absent::Tried`]), and no kernel checkpoint.
/// - fails: [`SessionFault::Compose`] when the parse or the lowering faults or
///   the settle comparison refuses the verdicts, the kernel disagreement taking
///   the settle fault's place as in [`Session::judge`].
/// - panics: only by propagating a molding thread's panic.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L3 — the trial's witnesses judge each candidate against a
///   fresh session's judgement of it.
/// - witness: `tests::trial::each_candidate_is_judged_as_a_fresh_session_judges_it`
#[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|submission|
    submission.root == root && submission.text == laid.0
        && submission.base == laid.1.base()
        && submission.standing == Standing::of(root, &submission.composed)
        && matches!(submission.resumed, Maybe::Absent(resumed::Absent::Tried))
        && matches!(submission.edits, Maybe::Absent(resumed::Absent::Tried))
        && matches!(submission.kernel, Maybe::Absent(_))))]
fn try_candidate<'text>(
    grammar: &Pbg,
    forms: &FormStore,
    root: SourceRoot,
    laid: (SourceText<'text>, Laying<'_>),
    threads: Threads,
) -> Result<Submission<'text>, SessionFault<'text>>
{
    let (candidate, laying) = laid;
    let base = laying.base();
    let laid_out = match laying {
        Laying::Alone => None,
        Laying::Member { unit, base: own } => Some((unit, own)),
    };
    let (parsed, census, _closure) = parse_held_laid(grammar, forms, candidate, laid_out, threads)
        .map_err(|fault| SessionFault::Compose(ComposeFault::Parse(fault)))?;
    let lowering = match laying {
        Laying::Alone => lower_parsed(
            grammar,
            parsed,
            &mut LoweringCount::default(),
            &mut Decisions::none(),
        ),
        Laying::Member { unit, .. } => lower_parsed_unit(
            grammar,
            parsed,
            unit,
            &mut LoweringCount::default(),
            &mut Decisions::none(),
        ),
    }
    .map_err(SessionFault::Compose)?;
    let mut obligations = lowering.obligations().to_vec();
    obligations.retain(|obligation| obligation.span.start() >= base);
    obligations.sort_by_key(|obligation| obligation.span);
    let (composed, kernel) = match lowering.into_lowered() {
        Lowered::Refused(refusal) => (
            Composed::Refused(refusal),
            Maybe::Absent(admitted::Absent::RefusedWhole),
        ),
        Lowered::Module { module, arena } => {
            let (settled, admission) = judge_member(
                root.corpus_root(),
                (module, candidate),
                arena,
                &HostGrant::UNBOUNDED,
                base,
            )
            .into_parts();
            let composed = settled.map_err(|fault| {
                SessionFault::Compose(match admission.admit() {
                    Ok(_) => ComposeFault::Settle(fault),
                    Err(disagreement) => ComposeFault::Readmission(disagreement),
                })
            })?;
            (composed, Maybe::Absent(admitted::Absent::Pending))
        },
    };
    Ok(Submission {
        root,
        text: candidate,
        base,
        standing: Standing::of(root, &composed),
        composed,
        resumed: Maybe::Absent(resumed::Absent::Tried),
        edits: Maybe::Absent(resumed::Absent::Tried),
        kernel,
        obligations,
        forms: census,
        table: Maybe::Absent(tabled::Absent::Untabled),
    })
}

/// Where a trial ranks among a trial's candidates: lower is better.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct TrialRank
{
    /// Whether the candidate was judged, refused whole or faulted.
    reached: Reached,
    /// The declarations refused.
    refused: DeclarationCount,
    /// The declarations left unsettled.
    unsettled: DeclarationCount,
    /// The obligations the verdicts owe.
    owed: ObligationCount,
    /// The parse's repairs.
    repairs: ObligationCount,
    /// The candidate's own position.
    candidate: CandidateIndex,
}

/// How far a candidate got, best first.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Reached
{
    /// The lowering read it and its declarations were judged.
    Judged,
    /// The lowering refused it as a whole.
    RefusedWhole,
    /// An engine fault stopped it.
    Faulted,
}

/// Where `trial` ranks.
///
/// # Specification
/// trivial.
fn trial_rank(trial: &Trial<'_>) -> TrialRank
{
    let (reached, refused, unsettled, owed, repairs) = trial.outcome.as_ref().map_or_else(
        |_| {
            (
                Reached::Faulted,
                0_usize,
                DeclarationCount::default(),
                ObligationCount::default(),
                0_usize,
            )
        },
        |submission| match submission.composed {
            Composed::Refused(_) => (
                Reached::RefusedWhole,
                0_usize,
                DeclarationCount::default(),
                ObligationCount::default(),
                submission.obligations.len(),
            ),
            Composed::Settled { ref report, .. } => {
                let tally = report.tally();
                (
                    Reached::Judged,
                    usize::from(tally.refusals().total()),
                    tally.declarations().unsettled(),
                    tally.ledger(),
                    submission.obligations.len(),
                )
            },
        },
    );
    TrialRank {
        reached,
        refused: DeclarationCount::from(refused),
        unsettled,
        owed,
        repairs: ObligationCount::from(repairs),
        candidate: trial.candidate,
    }
}

/// The reason a restore's absence gives a reopened session.
///
/// # Specification
/// - requires: nothing.
/// - ensures: preserves each restore absence’s meaning as the corresponding
///   reopen reason.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1 for the three-variant mapping by the exhaustive const
///   predicate; L3 for the externally observed missing-checkpoint branch when
///   reopening an empty store.
/// - witness: `tests::checkpoint::a_store_holding_nothing_reopens_fresh`
#[spec(
    ensures: |ret| {
    matches!(
        (reason, ret), (restored::Absent::AddressMismatch,
        reopened::Absent::AddressMismatch) | (restored::Absent::NotStored,
        reopened::Absent::NotStored) | (restored::Absent::OtherBackend,
        reopened::Absent::OtherBackend)
    )
},
)]
const fn unrestored(reason: restored::Absent) -> reopened::Absent
{
    match reason {
        restored::Absent::AddressMismatch => reopened::Absent::AddressMismatch,
        restored::Absent::NotStored => reopened::Absent::NotStored,
        restored::Absent::OtherBackend => reopened::Absent::OtherBackend,
    }
}

/// The text of each documentation `module` filed in the source at `own`, by
/// the documented form's key in that source's own tree: a sibling's, even one
/// documenting the same form byte for byte (#596), is not the document's.
///
/// # Specification
/// trivial.
fn documentation_of(
    module: &LoweredModule<'_>,
    own: SourceIndex,
) -> BTreeMap<NodeKey, DocumentationText>
{
    module
        .documentations()
        .iter()
        .filter(|&(key, _)| key.source() == own)
        .map(|(key, documented)| (key.form(), documented.text().clone()))
        .collect()
}

#[cfg(test)]
mod tests
{
    use core::num::NonZeroUsize;

    use gandr_core_incremental::BackendArtifact;
    use gandr_core_incremental::MemoryCheckpointStore;
    use gandr_storage_records::InMemoryBlockStore;
    use gandr_surface_dispatcher::SourceRoot;
    use gandr_surface_dispatcher::Threads;
    use gandr_surface_dispatcher::Width;
    use gandr_surface_grammar::built_in;

    use super::Session;

    /// Each width a session is given is the one its edit loop molds on,
    /// whatever width it held before.
    #[test]
    fn a_session_molds_on_the_width_it_is_given()
    {
        let fresh = Session::new(
            built_in().expect("the built-in grammar builds"),
            SourceRoot::Strict,
            MemoryCheckpointStore::default(),
            InMemoryBlockStore::default(),
            BackendArtifact::from(b"session width".as_slice()),
        );
        let two = Threads::from(NonZeroUsize::new(2_usize).expect("two is not zero"));
        let three = Threads::from(NonZeroUsize::new(3_usize).expect("three is not zero"));
        let widened = fresh.with_width(Width::Threads(two));
        assert_eq!(widened.threads, two);
        let rewidened = widened.with_width(Width::Threads(three));
        assert_eq!(
            rewidened.threads, three,
            "a second width replaces the first"
        );
    }
}
