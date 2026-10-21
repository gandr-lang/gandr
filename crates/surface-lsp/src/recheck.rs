//! The document recheck: every open document holds a session, and each
//! synchronisation judges the document's text in it and then admits it.
//!
//! The grammar and its role table are built once per process and shared. A
//! document's session keeps its forms between synchronisations, so a change
//! molds only the forms it touched; its report is the dispatcher's
//! composition of the whole text, which is what `gandr check` prints for it.
//! The diagnostics are read off the judgement, before the kernel is offered
//! the revision; [`admit`] runs the admission afterwards and names a kernel
//! disagreement, should it find one, as the diagnostic that replaces them.
//!
//! # Every synchronisation judges the document, publishes, then admits
//!
//! **Choice.** `didOpen` starts a session for the document and judges its text;
//! `didChange` applies each content change to the held text in order — a ranged
//! change replaces the bytes its two positions resolve to, an end before its
//! start read as the start, and a change naming no range replaces the whole
//! text — and judges the result in the same session. The session's form store
//! takes up every top-level form the change left unchanged and molds the rest,
//! and its judgement is the dispatcher's composition of the whole text, so the
//! published diagnostics are what `gandr check` prints for it. Once the
//! diagnostics are written, `serve` asks `Server::admit` to run the kernel
//! admission the judgement left, so the client reads the reports before the
//! kernel has re-derived the revision's acceptances. A disagreement the
//! admission finds is published at the document's version in place of the
//! reports, as one error at the origin naming the fault. A token request reads
//! the text's one [`Reading`](crate::reading::Reading), which parses it again
//! once per change.
//!
//! **The log.** Each synchronisation writes one line to the log `serve` is
//! given — `<uri> at version <n>: <molded>/<forms> forms molded,
//! <judged>/<items> items judged, <wall> ms, admitted in <wall> ms,
//! <crossed>/<declarations> declarations crossed` — naming the forms the parse
//! molded, the items the incremental checker judged, the recheck's wall from
//! the judgement to the diagnostics, the admission's wall after them, and the
//! declarations the admission offered the kernel again, the rest resumed from
//! the readmission of the document's import closure; a document refused whole
//! has nothing to admit, and its line ends at the recheck's wall. A line the
//! log refuses is dropped; the protocol never depends on it. Over a generated
//! document of two thousand forms, one edit molds one to eight forms and
//! publishes what opening the edited text publishes; an edit to a document's
//! own text after the first offers the kernel its own declarations alone.
//!
//! **Alternatives.** Full synchronisation alone ships the whole buffer per
//! keystroke and leaves the session nothing a change names; it stays as the
//! change that names no range. The timing line could go to `window/logMessage`,
//! which a client shows in its own channel, at the cost of a notification per
//! change on the protocol stream; the server's log is where an operator reads
//! it without touching the protocol. The admission runs on the serving thread
//! after the publication, so it delays the next frame's read but never the
//! diagnostics. Running it on a worker that the next change cancels would take
//! it off the next keystroke too, at the cost of a session shared across
//! threads.
//!
//! **Reversal.** A client sending many small changes per notification, measured
//! paying a line index per change, would batch them into one pass over the
//! text; a client that reads only the protocol stream moves the timing line to
//! `window/logMessage`; a measured wait of the next change on the admission
//! moves the admission to a cancellable worker.
//!
//! # Diagnostics are the model's
//!
//! The one input is the dispatcher's step, read by its `entries` under the
//! verb `check --goals`, each a diagnostic of `gandr-surface-diagnostics`. A
//! face that read refusals from a list kept beside the step could drop or
//! duplicate one; reading the step means the editor receives exactly the
//! diagnostics the terminal prints, in the order it prints them, with the
//! same loci, labels and contexts.
//!
//! | Diagnostic | Range | Code | Severity | Message | Related information |
//! | ---------- | ----- | ---- | -------- | ------- | ------------------- |
//! | a refusal | the primary annotation | the refusal's vocabulary name | error | the plain message, the primary label, each unlocated context, the note | each other annotation, with its label, then each located context, outermost first, with its judgement, `while` clause and binders |
//! | an unsettled declaration | the primary annotation | none | error | the message and the primary label | each other annotation, with its label |
//! | a goal | the primary annotation | none | information | the message and the primary label | none |
//! | a shadowing warning | the shadowing name | `ShadowedBuiltin` | warning | the message and the primary label | none |
//! | a diagnostic with no primary annotation | the document's origin | as its kind | as its kind | the message, each unlocated context, and the note of a refusal | each located context |
//! | a ledger line | the document's origin | none | error | the line | none |
//! | a fault before composition | the document's origin | none | error | the fault | none |
//!
//! The message carries every line the terminal prints around the snippet but
//! the snippet itself: the message, then the primary annotation's label on a
//! line of its own, then each context the refusal stood inside that marks no
//! bytes, as `while …` on a line of its own, then a refused declaration's note
//! after `note: `. The protocol gives a diagnostic one text field beside its
//! range and related locations, so a label the underline carries in the
//! terminal, and a context no location can carry, would otherwise never reach
//! the editor. The alternative is the first line alone, which leaves an editor
//! user without the one line that says what the span is. The choice reverses
//! when the protocol gains a field for the primary locus's label.
//!
//! The `gandr.diagnostics.verbosity` setting chooses how much of each report
//! the message carries, at the levels `gandr check --verbosity` names. Above
//! `user`, the detail lines the terminal closes a snippet with follow the note,
//! one `name: text` per line; at `json`, the message is the report's JSON
//! image, the line `gandr check --verbosity json` prints. The range, the code,
//! the severity and the related information do not change with the level. The
//! server reads the setting from the `initialize` parameters'
//! `initializationOptions.diagnostics.verbosity`, and from the `gandr` section
//! of each `workspace/didChangeConfiguration`; a change to another level
//! republishes every copy the connection holds, at its version, to that
//! connection alone. A value that names no level changes nothing.
//! Witnesses: `recheck::tests::one_refusal_is_published_at_every_verbosity`,
//! `server::tests::a_configuration_change_republishes_at_its_verbosity`.
//!
//! The verbosity is a connection's, not the workspace's: each editor attached
//! to one hub states its own, and since each connection is published only its
//! own copy's diagnostics, each editor sees its own level. The alternative was
//! a workspace-wide level, which would let one editor's setting rewrite
//! another's diagnostics. The setting is pushed, not pulled with
//! `workspace/configuration`: the server sends no request to the client, and a
//! client that only answers pulls keeps the level it initialised with.
//!
//! Every diagnostic's `source` is `gandr`. The code is the spelling a corpus
//! `refuses` attribute states and a snippet's first line carries, so a code
//! copied from the editor is an expectation a test can state. The alternative
//! was the renderer seam's `DiagnosticCode` registry; the pipeline maps no
//! refusal onto a registry code yet, and mapping refusals onto it here would be
//! a second decision made in a face. The choice reverses when the pipeline's
//! session report maps its refusals onto registry codes: the diagnostic's code
//! becomes that spelling.
//!
//! A goal is published at information severity because `check --goals` prints
//! it as a report that does not fail the run. The alternative was the verb
//! `check`, which withholds goals; an editor showing an open hole's goal beside
//! it is the use the goal report exists for.
//!
//! A builtin the document shadows is published at warning severity: the
//! source's binding wins under the default policy, the module checks, and
//! `check` prints the report without failing the run. Its code is
//! `ShadowedBuiltin`, the refusal the reject policy files for the same bytes.
//! Witness: `recheck::tests::a_shadowed_builtin_is_published_as_a_warning`.
//!
//! A declaration a refusal elsewhere leaves unsettled — one calling a
//! declaration the lowering refused — is published at hint severity: the
//! refusal it rests on is the error, and the author has nothing to fix at the
//! call. Information is the goal's severity and stays the goal's alone.
//!
//! The standing the renderer reads to choose what a pending source prints is
//! the dispatcher's `Standing::of`, carried into the step by the session's
//! submission: under the pending root, a source refused whole or carrying a
//! refusal no expectation can state is pending, any other lowered; under the
//! strict and fixture roots, a source refused whole is refused, any other
//! settled or unsettled as its report's tally is. The L2 witness over every
//! corpus source holds it to the walk's own reports.

use core::fmt;
use core::fmt::Write as _;
use core::time::Duration;
use std::path::Path;
use std::path::PathBuf;
use std::sync::OnceLock;
use std::time::Instant;

use anodized::spec;
use gandr_core_incremental::BackendArtifact;
use gandr_core_incremental::MemoryCheckpointStore;
use gandr_core_incremental::ResumeCensus;
use gandr_storage_records::InMemoryBlockStore;
use gandr_surface_diagnostics::AnnotationKind;
use gandr_surface_diagnostics::Severity as Seriousness;
use gandr_surface_diagnostics::Verbosity;
use gandr_surface_dispatcher::ComposeFault;
use gandr_surface_dispatcher::Composed;
use gandr_surface_dispatcher::Goals;
use gandr_surface_dispatcher::Laid;
use gandr_surface_dispatcher::Shadows;
use gandr_surface_dispatcher::SourceRoot;
use gandr_surface_dispatcher::Standing;
use gandr_surface_dispatcher::Step;
use gandr_surface_dispatcher::Verb;
use gandr_surface_dispatcher::classify;
use gandr_surface_dispatcher::entries;
use gandr_surface_dispatcher::laid;
use gandr_surface_dispatcher::lay_out_shadowed;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::PbgError;
use gandr_surface_grammar::RoleTable;
use gandr_surface_grammar::Spelling;
use gandr_surface_grammar::built_in;
use gandr_surface_render_remote::ByteOffset;
use gandr_surface_render_remote::LineIndex;
use gandr_surface_session::CandidateIndex;
use gandr_surface_session::ClosureSlot;
use gandr_surface_session::FormCensus;
use gandr_surface_session::Laying;
use gandr_surface_session::Session;
use gandr_surface_session::SessionFault;
use gandr_surface_session::Submission;
use gandr_surface_syntax::ByteOffset as SyntaxOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceText;
use gandr_surface_syntax::SyntaxTree;
use quenchant_shape::shape::Maybe;

use crate::inline::Forms;
use crate::position::Range;
use crate::protocol::Diagnostic;
use crate::protocol::DocumentUri;
use crate::protocol::Location;
use crate::protocol::RelatedInformation;
use crate::protocol::Severity;
use crate::quiet::caret_form;
use crate::quiet::formless;

/// The session one open document's revisions are submitted to, or the fault
/// that kept the grammar it parses under from building.
pub type DocumentSession =
    Result<Session<MemoryCheckpointStore, InMemoryBlockStore>, &'static PbgError>;

/// The built-in grammar, the role table read off it and the forms an inline
/// completion offers under it.
#[derive(Debug)]
struct Toolkit
{
    /// The grammar every document is parsed and composed under.
    grammar: Pbg,
    /// The roles its molds highlight as.
    roles: RoleTable,
    /// The forms a hole of each sort can open.
    forms: Forms,
}

/// The process's one toolkit, or the fault that kept it from building.
static TOOLKIT: OnceLock<Result<Toolkit, PbgError>> = OnceLock::new();

/// The process's one toolkit, built on first use.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the same toolkit, at the same address, on every call; the
///   grammar, its role table and its forms are built by the first call alone.
/// - provides: the grammar every recheck and every highlight reads.
/// - fails: the [`PbgError`] the first build met, on every call, since the
///   built-in grammar is the same on every call.
/// - panics: none.
///
/// # Errors
/// [`PbgError`], as above.
///
/// # Adequacy
/// - hypothesis: L3 — two calls are asserted to answer one address.
/// - witness: `recheck::tests::the_grammar_is_built_once_per_process`
#[spec(ensures: |ret| TOOLKIT.get().is_some_and(|stored|
    match (stored.as_ref(), ret) {
        (Ok(expected), Ok(actual)) => core::ptr::eq(core::ptr::from_ref(expected), core::ptr::from_ref(actual)),
        (Err(expected), Err(actual)) => core::ptr::eq(core::ptr::from_ref(expected), core::ptr::from_ref(actual)),
        _ => false,
    }))]
fn toolkit() -> Result<&'static Toolkit, &'static PbgError>
{
    TOOLKIT
        .get_or_init(|| {
            let grammar = built_in()?;
            let roles = RoleTable::build(&grammar)?;
            let forms = Forms::new(&grammar);
            Ok(Toolkit {
                grammar,
                roles,
                forms,
            })
        })
        .as_ref()
}

/// The process's one grammar, built on first use.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the grammar of [`toolkit`], at the same address on every call.
/// - provides: the grammar an inline completion and the outline mold under.
/// - fails: the [`PbgError`] the toolkit's first build met.
/// - panics: none.
///
/// # Errors
/// [`PbgError`], as above.
///
/// # Adequacy
/// - hypothesis: L3 — the grammar is asserted at the toolkit's address;
///   building a grammar of its own changes that address.
/// - witness: `recheck::tests::the_grammar_is_built_once_per_process`
#[spec(ensures: |ret| ret.is_ok() == toolkit().is_ok())]
pub fn grammar() -> Result<&'static Pbg, &'static PbgError>
{
    toolkit().map(|toolkit| &toolkit.grammar)
}

/// The forms of the process's one grammar, read off it with it.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the forms of [`toolkit`], at the same address on every call.
/// - provides: the forms an inline completion offers to fill a slot.
/// - fails: the [`PbgError`] the toolkit's first build met.
/// - panics: none.
///
/// # Errors
/// [`PbgError`], as above.
///
/// # Adequacy
/// - hypothesis: L3 — the server's inline witness answers forms at an open slot
///   only when they are read off the process's grammar.
/// - witness: `server::tests::inline_completion_answers_the_expected_closer`
#[spec(ensures: |ret| ret.is_ok() == toolkit().is_ok())]
pub fn forms() -> Result<&'static Forms, &'static PbgError>
{
    toolkit().map(|toolkit| &toolkit.forms)
}

/// The role table of the process's one grammar, built with it.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the role table of [`toolkit`], at the same address on every call.
/// - provides: the roles the outline reads a declaration's name by.
/// - fails: the [`PbgError`] the toolkit's first build met.
/// - panics: none.
///
/// # Errors
/// [`PbgError`], as above.
///
/// # Adequacy
/// - hypothesis: L3 — the outline witness names each declaration by the role
///   its name tile highlights as; a table of another grammar fails it.
/// - witness: `outline::tests::declarations_nest_as_symbols`
#[spec(ensures: |ret| ret.is_ok() == toolkit().is_ok())]
pub fn roles() -> Result<&'static RoleTable, &'static PbgError>
{
    toolkit().map(|toolkit| &toolkit.roles)
}

/// A fresh session for the document at `uri`, under the root its `file`
/// URI's path classifies as.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a session with nothing submitted, parsing under the process's
///   grammar, under the classified root, over memory stores; the grammar's
///   build fault when it did not build.
/// - provides: the session a document opened in the editor keeps.
/// - fails: the grammar's [`PbgError`], carried for the document's diagnostics.
/// - panics: none.
///
/// # Errors
/// [`PbgError`], as above.
///
/// # Adequacy
/// - hypothesis: L2 — over every corpus source, a document opened through it
///   publishes the reports the walk renders under the same root.
/// - witness: `tests::session::every_corpus_diagnostic_is_published_as_the_model_builds_it`
/// - witness: `recheck::tests::a_fault_is_published_at_the_origin`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |session| session.root() == classify(&uri.path())))]
pub fn open(uri: &DocumentUri) -> DocumentSession
{
    let toolkit = toolkit()?;
    Ok(Session::new(
        toolkit.grammar.clone(),
        classify(&uri.path()),
        MemoryCheckpointStore::default(),
        InMemoryBlockStore::default(),
        BackendArtifact::from(b"gandr-surface-lsp".as_slice()),
    ))
}

/// What one synchronisation cost: the forms its parse molded, the items the
/// incremental checker judged, the wall of the recheck and, once it ran, the
/// wall of the admission after it.
///
/// # Specification
/// - requires: constructed by [`recheck`], its admission's wall added by
///   [`admit`].
/// - ensures: names the census and the walls of one synchronisation.
/// - panics: none.
/// - executable: none — this data type has no call boundary; the recheck and
///   the admission carry the executable clauses.
///
/// # Adequacy
/// - hypothesis: L3 — an editor-shaped transcript over two thousand forms reads
///   one timing line per synchronisation, the open molding every form and the
///   edit a handful.
/// - witness: `tests::session::an_edit_to_a_large_document_rechecks_its_forms`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Timing
{
    /// The forms the parse molded, of the revision's forms.
    forms: FormCensus,
    /// What the incremental checker judged, when the revision was not
    /// refused whole.
    judged: Maybe<ResumeCensus, judged::Absent>,
    /// The recheck's wall: from the text to its diagnostics.
    wall: Duration,
    /// The admission's wall: from the diagnostics to the kernel artifact.
    admitted: Maybe<Duration, admitted::Absent>,
    /// How many declarations the admission offered the kernel again, of
    /// those judged.
    crossed: Maybe<Crossing, admitted::Absent>,
}

/// How many declarations an admission offered the kernel again, of those
/// the checker judged: the rest it resumed from the process's readmission of
/// the document's import closure.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Crossing
{
    /// The declarations offered again.
    crossed: usize,
    /// The declarations judged.
    judged: usize,
}

quenchant_shape::reason_enum! {
    /// Why a timing carries no judgement census.
    pub mod judged {
        /// The reason none is carried.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The revision was refused as a whole, so nothing was judged.
            RefusedWhole,
            /// The document has no session: its grammar did not build, or the
            /// session faulted.
            Unchecked,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a timing carries no admission wall.
    pub mod admitted {
        /// The reason none is carried.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The admission has not run yet.
            Pending,
            /// There was nothing to admit: the revision was refused whole or
            /// never judged.
            Unadmitted,
            /// The kernel did not re-derive a declaration the checker
            /// accepted, and the admission exported nothing.
            Disagreed,
        }
    }
}

impl fmt::Display for Timing
{
    /// Writes the forms molded, the items judged and the wall, one line.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `<molded>/<forms> forms molded, <judged>/<items> items
    ///   judged, <wall> ms`, the judgement replaced by why none was made, then
    ///   `, admitted in <wall> ms` when the admission ran and `,
    ///   <crossed>/<judged> declarations crossed` when it exported.
    /// - panics: none.
    /// - executable: none — the formatter exposes neither its written bytes nor
    ///   its sink's failure state.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the transcript reads the molded count back out of the
    ///   line it logged.
    /// - witness: `tests::session::an_edit_to_a_large_document_rechecks_its_forms`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(
            f,
            "{}/{} forms molded, ",
            usize::from(self.forms.molded()),
            usize::from(self.forms.forms())
        )?;
        match self.judged {
            Maybe::Present(census) => write!(
                f,
                "{}/{} items judged",
                usize::from(census.judged),
                usize::from(census.items)
            )?,
            Maybe::Absent(judged::Absent::RefusedWhole) => f.write_str("refused whole")?,
            Maybe::Absent(judged::Absent::Unchecked) => f.write_str("unchecked")?,
        }
        write!(f, ", {:.1} ms", self.wall.as_secs_f64() * 1_000.0_f64)?;
        match self.admitted {
            Maybe::Present(wall) => {
                write!(
                    f,
                    ", admitted in {:.1} ms",
                    wall.as_secs_f64() * 1_000.0_f64
                )?;
            },
            Maybe::Absent(
                admitted::Absent::Pending
                | admitted::Absent::Unadmitted
                | admitted::Absent::Disagreed,
            ) => {},
        }
        match self.crossed {
            Maybe::Present(crossing) => write!(
                f,
                ", {}/{} declarations crossed",
                crossing.crossed, crossing.judged
            ),
            Maybe::Absent(_) => Ok(()),
        }
    }
}

/// What one recheck produced: the diagnostics to publish, the form under the
/// caret it was asked about, the paths its closure named, and its timing.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Rechecked
{
    /// The diagnostics, in the order `gandr check --goals` prints them.
    pub diagnostics: Vec<Diagnostic>,
    /// The innermost form of the judged revision holding the caret, read
    /// off the tree the judgement parsed.
    pub form: Maybe<ByteSpan, formless::Absent>,
    /// Every path the document's closure's imports name, as `lay_out` names
    /// them, sorted; none for a document judged alone.
    pub named: Vec<PathBuf>,
    /// What the recheck cost.
    pub timing: Timing,
}

/// Judge `text`, the document at `uri`, in its `session`, each import of its
/// closure read as `shadows` holds it, read its diagnostics off the judgement
/// at `verbosity`, their types in `spelling`, and find the form holding `caret`
/// in the tree the judgement parsed.
///
/// # Specification
/// - requires: `session` was opened for `uri`; any text is admissible input.
/// - ensures: the text is judged once, and each diagnostic the dispatcher's
///   walk yields for the judgement's step under `gandr check --goals` becomes
///   one LSP diagnostic, in that order, as [`diagnostic`] writes it at
///   `verbosity`, every type it names in `spelling`: the range of its primary
///   annotation, else of its innermost located context, the refusal's
///   vocabulary name as its code, its message, primary label, unlocated
///   contexts and note as its message, each context annotation and then each
///   located context, outermost first, as a related location carrying its
///   label, then each mark it makes in an import at that import's file, and the
///   severity of a goal as information, of a warning as a warning, of a note as
///   a hint and of every other diagnostic as an error; a diagnostic locating
///   nothing in the document, and a ledger line, at the document's origin. A
///   fault that keeps the document from composing, and a grammar that did not
///   build, is one error at the origin naming it. The timing carries the
///   judgement's form census, the incremental checker's census, and the wall of
///   the whole recheck; its admission is pending when the judgement left one.
///   The form is [`caret_form`] of the judged tree at `caret`, `caret`'s own
///   reason when it is absent, and [`formless::Absent::Unparsed`] when the
///   judgement faulted or the grammar did not build. A text the session last
///   judged, submitted again, molds no form and judges no item, and its
///   diagnostics are the ones its previous recheck produced.
/// - provides: the one recheck every synchronisation publishes.
/// - fails: never; a fault is a diagnostic.
/// - panics: none.
/// - intension: one submission per call, and one projection per span end.
///
/// # Adequacy
/// - hypothesis: L2 — over every corpus source, the diagnostics are the ones
///   the dispatcher's walk yields for that source under `check --goals`, at the
///   same ranges and codes; L3 — a type mismatch and a duplicate signature are
///   asserted at their related locations, a mismatch under a function at its
///   annotations then its rules in order, an unlocated rule in its message, and
///   a pending source at its ledger line; L3 — a change to nothing, the whole
///   text replaced by itself and one character by itself, publishes the bytes
///   opening published and counts no form molded and no item judged.
/// - witness: `tests::session::every_corpus_diagnostic_is_published_as_the_model_builds_it`
/// - witness: `tests::session::an_edit_to_a_large_document_rechecks_its_forms`
/// - witness: `tests::session::an_edit_that_changes_nothing_republishes_the_same_bytes`
/// - witness: `recheck::tests::causal_contexts_become_lsp_related_information`
/// - witness: `recheck::tests::a_labeled_context_keeps_its_locus_and_cause_in_related_information`
/// - witness: `recheck::tests::related_information_is_the_annotations_then_the_located_contexts`
/// - witness: `recheck::tests::an_unlocated_context_is_appended_to_the_message`
/// - witness: `recheck::tests::a_shadowed_builtin_is_published_as_a_warning`
/// - witness: `recheck::tests::a_fault_is_published_at_the_origin`
#[spec(ensures: |ret| ret.diagnostics.iter().all(|diagnostic|
    diagnostic.source == "gandr" && diagnostic.range.start <= diagnostic.range.end
        && matches!(diagnostic.severity, Severity::ERROR | Severity::WARNING | Severity::INFORMATION | Severity::HINT)
        && diagnostic.related_information.iter().all(|related|
            related.location.range.start <= related.location.range.end)))]
#[must_use]
#[cfg_attr(feature = "hotpath", hotpath::measure)]
pub fn recheck(
    uri: &DocumentUri,
    session: &mut DocumentSession,
    text: SourceText<'_>,
    shadows: &dyn Shadows,
    verbosity: Verbosity,
    spelling: Spelling,
    caret: Maybe<gandr_surface_syntax::ByteOffset, formless::Absent>,
) -> Rechecked
{
    let started = Instant::now();
    let unchecked = |diagnostic: Diagnostic, named: Vec<PathBuf>| Rechecked {
        diagnostics: vec![diagnostic],
        form: Maybe::Absent(formless::Absent::Unparsed),
        named,
        timing: Timing {
            forms: FormCensus::default(),
            judged: Maybe::Absent(judged::Absent::Unchecked),
            wall: started.elapsed(),
            admitted: Maybe::Absent(admitted::Absent::Unadmitted),
            crossed: Maybe::Absent(admitted::Absent::Unadmitted),
        },
    };
    let session = match *session {
        Ok(ref mut session) => session,
        Err(fault) => {
            return unchecked(
                Diagnostic::at_origin(format!("the built-in grammar did not build: {fault}")),
                Vec::new(),
            );
        },
    };
    let mut form = Maybe::Absent(formless::Absent::Unparsed);
    // A document that imports a sibling is judged over it, laid out as the
    // walk lays its file out; the caret and the form it is in are measured
    // from the document's own start.
    let mut laid = laid_out(uri, session.root(), text, shadows);
    let (base, named) = match laid {
        Maybe::Present(ref mut laid) => (laid.base, core::mem::take(&mut laid.named)),
        Maybe::Absent(_) => (SyntaxOffset::from(0_usize), Vec::new()),
    };
    let read = |tree: &SyntaxTree<'_>| {
        form = match caret {
            Maybe::Present(at) => {
                let at = SyntaxOffset::from(usize::from(at).saturating_add(usize::from(base)));
                match caret_form(tree, at) {
                    Maybe::Present(span) => own(span, base),
                    Maybe::Absent(reason) => Maybe::Absent(reason),
                }
            },
            Maybe::Absent(reason) => Maybe::Absent(reason),
        };
    };
    let slot = ClosureSlot::new();
    let outcome = match laid {
        Maybe::Present(ref laid) => session.judge_unit_reading(
            SourceText::from(laid.text.as_str()),
            &laid.unit,
            laid.base,
            &slot,
            read,
        ),
        Maybe::Absent(_) => session.judge_reading(text, read),
    };
    let submission = match outcome {
        Ok(submission) => submission,
        Err(fault) => return unchecked(Diagnostic::at_origin(fault.to_string()), named),
    };
    let forms = submission.forms();
    let (judged, pending) = match submission.resumed() {
        Maybe::Present(resumed) => (Maybe::Present(resumed.census()), admitted::Absent::Pending),
        Maybe::Absent(_) => (
            Maybe::Absent(judged::Absent::RefusedWhole),
            admitted::Absent::Unadmitted,
        ),
    };
    let laid = match laid {
        Maybe::Present(ref laid) => Some(laid),
        Maybe::Absent(_) => None,
    };
    let diagnostics = diagnostics_of(submission, (uri, laid), text, verbosity, spelling);
    Rechecked {
        diagnostics,
        form,
        named,
        timing: Timing {
            forms,
            judged,
            wall: started.elapsed(),
            admitted: Maybe::Absent(pending),
            crossed: Maybe::Absent(pending),
        },
    }
}

/// What admitting a rechecked document produced: the diagnostic replacing the
/// published ones when the kernel disagreed, and the synchronisation's timing
/// with the admission's wall.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Admitted
{
    /// The diagnostic to publish in place of the recheck's, when the
    /// admission found a disagreement.
    pub fault: Maybe<Diagnostic, agreed::Absent>,
    /// The synchronisation's timing.
    pub timing: Timing,
}

quenchant_shape::reason_enum! {
    /// Why an admission publishes nothing.
    pub mod agreed {
        /// The reason nothing is published.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The kernel re-derived every acceptance, or there was nothing to
            /// admit: the diagnostics already published stand.
            Agreed,
        }
    }
}

/// Run the admission the document's latest recheck left in its `session`.
///
/// # Specification
/// - requires: `timing` is the timing of the recheck that judged the session's
///   latest revision.
/// - ensures: when the recheck left an admission pending, it runs, and the
///   timing carries its wall and, when it exported, how many declarations it
///   offered the kernel of those judged; a kernel disagreement is one error at
///   the origin naming the fault `submit` would have reported, to publish in
///   place of the recheck's diagnostics. Otherwise nothing runs and the timing
///   is returned as it was.
/// - provides: the second half of every synchronisation, run after its
///   diagnostics are published.
/// - fails: never; a disagreement is a diagnostic.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a synchronisation's timing line carries the admission's
///   wall after the recheck's, and a refused document's carries none; an
///   importer's line counts the closure's declarations at its opening and its
///   own alone after an edit to its own text.
/// - witness: `tests::session::an_edit_to_a_large_document_rechecks_its_forms`
/// - witness: `tests::session::an_importer_edit_offers_the_kernel_its_own_declarations_776`
/// - witness: `recheck::tests::an_admission_follows_the_published_diagnostics`
#[spec(ensures: |ret| ret.timing.forms == timing.forms && ret.timing.judged == timing.judged
    && ret.timing.wall == timing.wall
    && match timing.admitted {
        Maybe::Absent(admitted::Absent::Pending) => matches!(ret.timing.admitted, Maybe::Present(_)),
        Maybe::Present(_) | Maybe::Absent(admitted::Absent::Unadmitted | admitted::Absent::Disagreed) =>
            ret.timing.admitted == timing.admitted && ret.timing.crossed == timing.crossed
                && matches!(ret.fault, Maybe::Absent(_)),
    })]
#[must_use]
pub fn admit(
    session: &mut DocumentSession,
    timing: Timing,
) -> Admitted
{
    let unchanged = Admitted {
        fault: Maybe::Absent(agreed::Absent::Agreed),
        timing,
    };
    let (&mut Ok(ref mut session), Maybe::Absent(admitted::Absent::Pending)) =
        (session, timing.admitted)
    else {
        return unchanged;
    };
    let started = Instant::now();
    let (fault, crossed) = match session.admit() {
        Ok(Maybe::Present(admitted)) => (
            Maybe::Absent(agreed::Absent::Agreed),
            Maybe::Present(Crossing {
                crossed: usize::from(admitted.crossed()),
                judged: usize::from(admitted.judged()),
            }),
        ),
        Ok(Maybe::Absent(_)) => (
            Maybe::Absent(agreed::Absent::Agreed),
            Maybe::Absent(admitted::Absent::Unadmitted),
        ),
        Err(disagreement) => (
            Maybe::Present(Diagnostic::at_origin(
                SessionFault::Compose(ComposeFault::Readmission(disagreement)).to_string(),
            )),
            Maybe::Absent(admitted::Absent::Disagreed),
        ),
    };
    Admitted {
        fault,
        timing: Timing {
            admitted: Maybe::Present(started.elapsed()),
            crossed,
            ..timing
        },
    }
}

/// How far a tried candidate got, best first.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Reached
{
    /// The candidate was lowered and each of its declarations judged.
    Judged,
    /// The lowering refused the candidate whole.
    RefusedWhole,
    /// An engine fault stopped the candidate, or the grammar did not build.
    Faulted,
}

/// One candidate revision as a trial judged it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Tried
{
    /// The candidate's position among those the trial was given.
    pub candidate: CandidateIndex,
    /// How far it got.
    pub reached: Reached,
    /// The diagnostics a synchronisation to its text would publish.
    pub diagnostics: Vec<Diagnostic>,
}

/// Judge each of `candidates`, revisions of the document at `uri`, in its
/// `session` without submitting any, each import of their closures read as
/// `shadows` holds it, best first.
///
/// # Specification
/// - requires: `session` was opened for `uri`; any texts are admissible input.
/// - ensures: one result per candidate, in the order `Session::trial` ranks
///   them, each carrying the diagnostics [`recheck`] would publish at the user
///   verbosity for the candidate's text in a session that has accepted nothing;
///   a fault is one error at the origin naming it. The session is unchanged.
/// - provides: the language server's view of a batch of candidate fills.
/// - fails: never; a fault is a diagnostic.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a settling, a refused and a malformed candidate are
///   ranked in that order, each with the diagnostics a recheck of its text
///   publishes, and the session's next recheck is what it was before.
/// - witness: `recheck::tests::a_trial_ranks_candidates_with_their_diagnostics`
#[spec(ensures: |ret| ret.len() == candidates.len()
    && ret.is_sorted_by_key(|tried| tried.reached)
    && ret.iter().all(|tried| usize::from(tried.candidate) < candidates.len()))]
#[must_use]
pub fn trial(
    uri: &DocumentUri,
    session: &DocumentSession,
    candidates: &[SourceText<'_>],
    shadows: &dyn Shadows,
) -> Vec<Tried>
{
    let session = match *session {
        Ok(ref session) => session,
        Err(fault) => {
            let diagnostic =
                Diagnostic::at_origin(format!("the built-in grammar did not build: {fault}"));
            return (0_usize .. candidates.len())
                .map(|index| Tried {
                    candidate: CandidateIndex::from(index),
                    reached: Reached::Faulted,
                    diagnostics: vec![diagnostic.clone()],
                })
                .collect();
        },
    };
    let root = session.root();
    let laid: Vec<Maybe<Laid, laid::Absent>> = candidates
        .iter()
        .map(|&candidate| laid_out(uri, root, candidate, shadows))
        .collect();
    let members: Vec<(SourceText<'_>, Laying<'_>)> = candidates
        .iter()
        .zip(&laid)
        .map(|(&candidate, laid)| match *laid {
            Maybe::Present(ref laid) => (SourceText::from(laid.text.as_str()), Laying::Member {
                unit: &laid.unit,
                base: laid.base,
            }),
            Maybe::Absent(_) => (candidate, Laying::Alone),
        })
        .collect();
    session
        .trial_unit(&members)
        .into_iter()
        .map(|tried| {
            let candidate = tried.candidate();
            let text = candidates
                .get(usize::from(candidate))
                .copied()
                .unwrap_or_else(|| SourceText::from(""));
            match tried.into_outcome() {
                Ok(submission) => Tried {
                    candidate,
                    reached: match *submission.composed() {
                        Composed::Refused(_) => Reached::RefusedWhole,
                        Composed::Settled { .. } => Reached::Judged,
                    },
                    diagnostics: diagnostics_of(
                        submission,
                        (
                            uri,
                            laid.get(usize::from(candidate))
                                .and_then(|laid| match *laid {
                                    Maybe::Present(ref laid) => Some(laid),
                                    Maybe::Absent(_) => None,
                                }),
                        ),
                        text,
                        Verbosity::User,
                        Spelling::Unicode,
                    ),
                },
                Err(fault) => Tried {
                    candidate,
                    reached: Reached::Faulted,
                    diagnostics: vec![Diagnostic::at_origin(fault.to_string())],
                },
            }
        })
        .collect()
}

/// The import closure the document at `uri`, written as `text` under `root`,
/// is judged in: the dispatcher's [`lay_out_shadowed`] under the process's
/// grammar, each import read as `shadows` holds it.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`lay_out_shadowed`] of the document's path under `shadows`;
///   [`laid::Absent::Alone`] when the grammar did not build.
/// - provides: the unit a recheck and a trial judge a document in.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — every corpus source, an importer among them, publishes
///   the diagnostics the walk yields for its file.
/// - witness: `tests::session::every_corpus_diagnostic_is_published_as_the_model_builds_it`
#[spec(ensures: |ref ret| match *ret {
    Maybe::Present(ref laid) => laid.text.get(usize::from(laid.base) ..) == Some(text.as_ref()),
    Maybe::Absent(_) => true,
})]
fn laid_out(
    uri: &DocumentUri,
    root: SourceRoot,
    text: SourceText<'_>,
    shadows: &dyn Shadows,
) -> Maybe<Laid, laid::Absent>
{
    grammar().map_or(Maybe::Absent(laid::Absent::Alone), |grammar| {
        lay_out_shadowed(grammar, &uri.path(), root, text, shadows)
    })
}

/// `span`, a form of the unit a document is judged in, as the document's own
/// text measures it from `base`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `span` moved back by `base` bytes; [`formless::Absent::Between`]
///   for a form before the document, a sibling's.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — every corpus source, an importer among them, publishes
///   the diagnostics the walk yields for its file.
/// - witness: `tests::session::every_corpus_diagnostic_is_published_as_the_model_builds_it`
#[spec(ensures: |ret| match ret {
    Maybe::Present(moved) => usize::from(moved.start()).saturating_add(usize::from(base)) == usize::from(span.start()),
    Maybe::Absent(_) => usize::from(span.start()) < usize::from(base) || usize::from(span.end()) < usize::from(base),
})]
fn own(
    span: ByteSpan,
    base: SyntaxOffset,
) -> Maybe<ByteSpan, formless::Absent>
{
    let moved = |at: SyntaxOffset| usize::from(at).checked_sub(usize::from(base));
    match (moved(span.start()), moved(span.end())) {
        (Some(start), Some(end)) => {
            ByteSpan::new(SyntaxOffset::from(start), SyntaxOffset::from(end))
                .map_or(Maybe::Absent(formless::Absent::Between), Maybe::Present)
        },
        (Some(_) | None, _) => Maybe::Absent(formless::Absent::Between),
    }
}

/// The diagnostics `submission`, the judgement of `text` at `uri` laid out in
/// `laid` when it is judged after its imports, publishes at `verbosity` and in
/// `spelling`: each diagnostic `gandr check --goals` prints for its step as
/// [`reported`] stands it, in order.
///
/// # Specification
/// trivial.
fn diagnostics_of(
    submission: Submission<'_>,
    (uri, laid): (&DocumentUri, Option<&Laid>),
    text: SourceText<'_>,
    verbosity: Verbosity,
    spelling: Spelling,
) -> Vec<Diagnostic>
{
    let path = uri.path();
    let index = LineIndex::new(text.as_ref().into());
    let step = reported(submission.into_step(Path::new(&path)));
    entries(&step, Verb::Check(Goals::Reported))
        .spelling(spelling)
        .map(|found| match found.severity {
            Seriousness::Ledger => {
                Diagnostic::at_origin(format!("{}: {}", found.path.display(), found.message.text))
            },
            Seriousness::Error | Seriousness::Warning | Seriousness::Goal | Seriousness::Note => {
                diagnostic(&found, &index, uri, verbosity, laid)
            },
        })
        .collect()
}

/// `step` as an editor reports it: a pending source carrying the refusal the
/// pending set expects stands under the fixture root, which states it.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a step standing [`Standing::Pending`] under
///   [`SourceRoot::Fixture`], standing as [`Standing::of`] stands it there, its
///   path, text, base and composition unchanged; any other step — a pending
///   source the lowering reads whole among them — unchanged.
/// - provides: the step an editor's diagnostics are read off. The pending set
///   is the corpus runner's account of refusals it expects, which `check`
///   prints nothing for; an editor has no expectation to settle, so it shows
///   those refusals as the same text's anywhere else.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a pending source refused whole publishes its refusal at
///   its span, as the same text under the fixture root does, and a pending
///   source the lowering reads still publishes the note that it belongs under
///   the fixture root.
/// - witness: `recheck::tests::a_pending_source_publishes_its_refusal_1248`
/// - witness: `recheck::tests::a_fault_is_published_at_the_origin`
#[spec(ensures: |ref ret| !matches!(*ret, Step::Source { standing: Standing::Pending, .. }))]
fn reported(step: Step<'_>) -> Step<'_>
{
    match step {
        Step::Source {
            path,
            text,
            base,
            composed,
            standing: Standing::Pending,
            ..
        } => Step::Source {
            path,
            root: SourceRoot::Fixture,
            text,
            base,
            standing: Standing::of(SourceRoot::Fixture, &composed),
            composed,
        },
        other @ (Step::Source { .. } | Step::Fault { .. }) => other,
    }
}

/// The editor diagnostic `found` is published as at `verbosity`, the document
/// laid out in `laid` when it is judged after its imports.
///
/// # Specification
/// - requires: `index` was built from the text `found` is about; `found` is no
///   ledger line; `laid`, when given, is the unit `found` was judged in.
/// - ensures: as [`recheck`] states for one diagnostic. A span the model
///   locates lies inside the text on character boundaries, so it always
///   projects; the origin stands in for one that would not. The range is the
///   primary annotation's; with none in the text, the innermost located
///   context's; with none of those, the origin. At [`Verbosity::Json`] the
///   message is the diagnostic's JSON image; at every other level it is the
///   plain message, then the primary annotation's label on its own line when it
///   is located, then each unlocated context as `while …` on a line of its own,
///   then its note on a line of its own after `note: ` when it closes with one,
///   then each detail line the level adds: what the terminal prints, in the one
///   text field the protocol gives a diagnostic. The related information is
///   every annotation but the primary one, in order, then every located
///   context, outermost first, then each mark the diagnostic makes in an
///   import, at that import's file, in order.
/// - provides: the one map from a model diagnostic to an editor diagnostic.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a type mismatch and duplicate signature have exact
///   primary and causal locations, a refused declaration's message carries its
///   label and note, and a refusal whose refused node stands in an import is
///   published at its innermost context with the node at the import's file. L2
///   — every corpus diagnostic agrees with its wire ranges, code, message and
///   related labels, distinguishing omitted, misclassified or misprojected
///   fields without pinning wording.
/// - witness: `recheck::tests::causal_contexts_become_lsp_related_information`
/// - witness: `recheck::tests::a_labeled_context_keeps_its_locus_and_cause_in_related_information`
/// - witness: `recheck::tests::a_refusal_publishes_its_label_and_note`
/// - witness: `recheck::tests::an_unlocated_context_is_appended_to_the_message`
/// - witness: `recheck::tests::one_refusal_is_published_at_every_verbosity`
/// - witness: `recheck::tests::a_shadowed_builtin_is_published_as_a_warning`
/// - witness: `recheck::tests::a_refusal_in_an_import_is_published_where_the_document_reaches_it_1199`
/// - witness: `tests::session::every_corpus_diagnostic_is_published_as_the_model_builds_it`
#[spec(ensures: |ret| ret.source == "gandr"
    && ret.severity == match found.severity { Seriousness::Goal => Severity::INFORMATION, Seriousness::Warning => Severity::WARNING, Seriousness::Note => Severity::HINT, Seriousness::Error | Seriousness::Ledger => Severity::ERROR }
    && ret.code.is_some() == matches!(found.identifier, Maybe::Present(_))
    && (verbosity == Verbosity::Json || ret.message.starts_with(found.message.text.as_str()))
    && ret.related_information.len() >= found.annotations.iter()
        .filter(|annotation| annotation.kind == AnnotationKind::Context).count()
        .saturating_add(found.contexts.iter().filter(|context| matches!(context.locus, Maybe::Present(_))).count()))]
fn diagnostic(
    found: &gandr_surface_diagnostics::Diagnostic,
    index: &LineIndex<'_>,
    uri: &DocumentUri,
    verbosity: Verbosity,
    laid: Option<&Laid>,
) -> Diagnostic
{
    let range_of = |span: ByteSpan| {
        Range::of_bytes(
            index,
            ByteOffset::from(usize::from(span.start())),
            ByteOffset::from(usize::from(span.end())),
        )
        .unwrap_or_default()
    };
    let primary = found.primary();
    // A refusal whose refused node stands in an import is published where the
    // document reaches it: the innermost rule it locates.
    let innermost = found
        .contexts
        .iter()
        .rev()
        .find_map(|context| match context.locus {
            Maybe::Present(locus) => Some(locus.span),
            Maybe::Absent(_) => None,
        });
    let range = match primary {
        Maybe::Present(annotation) => range_of(annotation.locus.span),
        Maybe::Absent(_) => innermost.map_or_else(Range::default, range_of),
    };
    let severity = match found.severity {
        Seriousness::Goal => Severity::INFORMATION,
        Seriousness::Warning => Severity::WARNING,
        Seriousness::Note => Severity::HINT,
        Seriousness::Error | Seriousness::Ledger => Severity::ERROR,
    };
    let message = if verbosity == Verbosity::Json {
        found.json()
    }
    else {
        let mut message = found.message.text.clone();
        if let Maybe::Present(annotation) = primary {
            message.push('\n');
            message.push_str(&annotation.label);
        }
        for context in &found.contexts {
            if let Maybe::Absent(_) = context.locus {
                message.push('\n');
                message.push_str(&context.note());
            }
        }
        if let Maybe::Present(ref note) = found.note {
            message.push_str("\nnote: ");
            message.push_str(note);
        }
        for detail in found.details(verbosity) {
            let _written = write!(message, "\n{detail}");
        }
        message
    };
    let mut diagnostic = Diagnostic::new(range, severity, message);
    if let Maybe::Present(ref spelling) = found.identifier {
        diagnostic.code = Some(spelling.to_string());
    }
    let contexts = found
        .contexts
        .iter()
        .filter_map(|context| match context.locus {
            Maybe::Present(locus) => Some(RelatedInformation {
                location: Location {
                    uri: uri.clone(),
                    range: range_of(locus.span),
                },
                message: context.label(),
            }),
            Maybe::Absent(_) => None,
        });
    let imports = found.elsewhere.iter().filter_map(|mark| {
        Some(RelatedInformation {
            location: imported(laid?, mark.span)?,
            message: mark.label.clone(),
        })
    });
    diagnostic.related_information = found
        .annotations
        .iter()
        .filter(|annotation| annotation.kind == AnnotationKind::Context)
        .map(|annotation| RelatedInformation {
            location: Location {
                uri: uri.clone(),
                range: range_of(annotation.locus.span),
            },
            message: annotation.label.clone(),
        })
        .chain(contexts)
        .chain(imports)
        .collect();
    diagnostic
}

/// Where `span`, bytes of the text `laid` lays out, lies: the file of the
/// source holding them, and their range in that source's own text.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the URI of the path `laid` gives the source holding the span's
///   start, and the span measured from that source's start; none when the span
///   leaves the source, splits a character, or its path is no file URI.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the witness of [`diagnostic`] reads the refused node at
///   its import's line and column.
/// - witness: `recheck::tests::a_refusal_in_an_import_is_published_where_the_document_reaches_it_1199`
#[spec(ensures: |ret| ret.as_ref().is_none_or(|location| location.range.start <= location.range.end))]
fn imported(
    laid: &Laid,
    span: ByteSpan,
) -> Option<Location>
{
    let source = usize::from(laid.unit.source_at(span.start()));
    let sources = laid.unit.sources();
    let start = usize::from(sources.get(source)?.start());
    let end = sources
        .get(source.saturating_add(1_usize))
        .map_or(laid.text.len(), |next| usize::from(next.start()));
    let text = laid.text.get(start .. end)?;
    let index = LineIndex::new(text.into());
    let range = Range::of_bytes(
        &index,
        ByteOffset::from(usize::from(span.start()).checked_sub(start)?),
        ByteOffset::from(usize::from(span.end()).checked_sub(start)?),
    )
    .ok()?;
    Some(Location {
        uri: DocumentUri::of_path(laid.paths.get(source)?)?,
        range,
    })
}

#[cfg(test)]
mod tests
{
    use gandr_surface_diagnostics::Verbosity;
    use gandr_surface_grammar::Spelling;
    use gandr_surface_syntax::SourceText;
    use quenchant_shape::shape::Maybe;

    use super::Reached;
    use super::admit;
    use super::admitted;
    use super::grammar;
    use super::open;
    use super::recheck;
    use super::toolkit;
    use super::trial;
    use crate::position::Character;
    use crate::position::Line;
    use crate::position::Position;
    use crate::position::Range;
    use crate::protocol::Diagnostic;
    use crate::protocol::DocumentUri;
    use crate::protocol::Location;
    use crate::protocol::Severity;
    use crate::quiet::formless;
    use crate::reading::Reading;
    use crate::tokens::TokenStream;
    use crate::tokens::encode;

    /// A recheck asked about no caret.
    const UNCARETED: Maybe<gandr_surface_syntax::ByteOffset, formless::Absent> =
        Maybe::Absent(formless::Absent::Uncareted);

    /// The diagnostics a document opened at `uri` with `text` publishes.
    ///
    /// # Specification
    /// trivial.
    fn checked(
        uri: &DocumentUri,
        text: SourceText<'_>,
    ) -> Vec<Diagnostic>
    {
        recheck(
            uri,
            &mut open(uri),
            text,
            &gandr_surface_dispatcher::Unshadowed,
            Verbosity::User,
            Spelling::Unicode,
            UNCARETED,
        )
        .diagnostics
    }

    /// A range from one line and character to another.
    struct Span(u32, u32, u32, u32);

    /// The range a [`Span`] spells.
    ///
    /// # Specification
    /// trivial.
    fn range(Span(start_line, start_character, end_line, end_character): Span) -> Range
    {
        Range {
            start: Position {
                line: Line::from(start_line),
                character: Character::from(start_character),
            },
            end: Position {
                line: Line::from(end_line),
                character: Character::from(end_character),
            },
        }
    }

    #[test]
    fn the_grammar_is_built_once_per_process()
    {
        let first = toolkit().expect("the built-in grammar builds");
        let second = toolkit().expect("the built-in grammar builds");
        assert!(
            core::ptr::eq(core::ptr::from_ref(first), core::ptr::from_ref(second)),
            "each recheck reads one shared grammar rather than building its own"
        );
        let grammar = grammar().expect("the built-in grammar builds");
        assert!(
            core::ptr::eq(core::ptr::from_ref(grammar), &raw const first.grammar),
            "an inline completion molds under the toolkit's grammar"
        );
    }

    #[test]
    fn a_definition_produces_semantic_tokens()
    {
        let text = "def f = 42 ;\n";
        let reading = Reading::of(SourceText::from(text));
        let spans = reading.spans();
        let index = gandr_surface_render_remote::LineIndex::new(text.into());
        assert_eq!(
            encode(&index, spans),
            TokenStream::from(vec![0, 0, 3, 0, 0, 0, 4, 1, 2, 1, 0, 4, 2, 9, 0]),
            "`def` a keyword, `f` a declared function, `42` a number"
        );
    }

    #[test]
    fn causal_contexts_become_lsp_related_information()
    {
        let uri = DocumentUri::from("file:///strict/mismatch.gandr");
        let text = "def wrong : Integer ;\ndef wrong = \"text\" ;\n";
        let diagnostics = checked(&uri, SourceText::from(text));
        let [ref diagnostic] = *diagnostics.as_slice()
        else {
            panic!("one mismatch");
        };
        assert_eq!(
            (
                diagnostic.range,
                diagnostic.severity,
                diagnostic.code.as_deref(),
                diagnostic.source
            ),
            (
                range(Span(1, 12, 1, 18)),
                Severity::ERROR,
                Some("TypeMismatch"),
                "gandr"
            )
        );
        assert_eq!(
            diagnostic.message.lines().nth(1),
            Some("its type does not convert: expected `Integer`, found `String`"),
            "the editor's message spells both types under the message line: {:?}",
            diagnostic.message
        );
        let [ref related] = *diagnostic.related_information.as_slice()
        else {
            panic!("one causal location");
        };
        assert_eq!(related.location, Location {
            uri,
            range: range(Span(0, 12, 0, 19))
        });
    }

    #[test]
    fn related_information_is_the_annotations_then_the_located_contexts()
    {
        let uri = DocumentUri::from("file:///strict/returned.gandr");
        let text = "def g(v: Integer) -> -F String { return v }\n";
        let diagnostics = checked(&uri, SourceText::from(text));
        let [ref diagnostic] = *diagnostics.as_slice()
        else {
            panic!("one mismatch");
        };
        assert_eq!(
            (diagnostic.range, diagnostic.code.as_deref()),
            (range(Span(0, 40, 0, 41)), Some("TypeMismatch")),
            "the returned value is the lead range"
        );
        let related: Vec<(Range, &str)> = diagnostic
            .related_information
            .iter()
            .map(|related| (related.location.range, related.message.as_str()))
            .collect();
        assert_eq!(
            related,
            [
                (range(Span(0, 24, 0, 30)), "the type it is checked against"),
                (range(Span(0, 9, 0, 16)), "the type it synthesises"),
                (
                    range(Span(0, 0, 0, 43)),
                    "checked against `Integer => String`; while checking the body of this \
                     thunk"
                ),
                (
                    range(Span(0, 6, 0, 7)),
                    "checked against `Integer -> -F String`; while checking the body of this \
                     function; binds v : Integer"
                ),
                (
                    range(Span(0, 33, 0, 41)),
                    "checked against `-F String`; while checking the value this returns"
                ),
            ],
            "the refusal's own annotations, then every rule it stood inside, outermost first"
        );
    }

    #[test]
    fn an_unlocated_context_is_appended_to_the_message()
    {
        let uri = DocumentUri::from("file:///strict/force.gandr");
        let text =
            SourceText::from("def a : +U (-F Integer) ;\ndef a = thunk { become force 1 } ;\n");
        let pbg = gandr_surface_grammar::built_in().expect("the grammar builds");
        let root = gandr_surface_dispatcher::SourceRoot::Strict;
        let step = gandr_surface_dispatcher::Step::Source {
            path: std::path::Path::new("force.gandr"),
            root,
            text,
            base: gandr_surface_syntax::ByteOffset::from(0_usize),
            composed: gandr_surface_dispatcher::compose(
                &pbg,
                root.corpus_root(),
                text,
                &mut gandr_surface_dispatcher::LoweringCount::default(),
            )
            .expect("the source composes"),
            standing: gandr_surface_dispatcher::Standing::Unsettled,
        };
        let mut found: Vec<gandr_surface_diagnostics::Diagnostic> =
            super::entries(&step, super::Verb::Check(super::Goals::Reported)).collect();
        let [ref mut force] = *found.as_mut_slice()
        else {
            panic!("one shape mismatch");
        };
        let outermost = force.contexts.first_mut().expect("the thunk's rule");
        outermost.locus =
            Maybe::Absent(gandr_surface_diagnostics::context_locus::Absent::Unrecorded);
        let index = super::LineIndex::new(text.as_ref().into());
        let published = super::diagnostic(force, &index, &uri, Verbosity::User, None);
        assert_eq!(
            published.message.lines().collect::<Vec<_>>(),
            [
                "expected a thunk type `+U C`",
                "its type is not of the required shape: found `Integer`",
                "while checking the body of this thunk",
                "note: `a` is expected to check, and this refusal leaves it unsettled",
            ],
            "a context with no bytes to relate is a `while` line of the message, after the label"
        );
        assert_eq!(
            published
                .related_information
                .iter()
                .map(|related| (related.location.range, related.message.as_str()))
                .collect::<Vec<_>>(),
            [(
                range(Span(1, 23, 1, 30)),
                "checked against `-F Integer`; while forcing this"
            )],
            "the located context stays related information"
        );
    }

    #[test]
    fn a_shadowed_builtin_is_published_as_a_warning()
    {
        let uri = DocumentUri::from("file:///strict/shadow.gandr");
        let text = "def add : Integer ;\ndef add = 1 ;\n";
        let diagnostics = checked(&uri, SourceText::from(text));
        let [ref diagnostic] = *diagnostics.as_slice()
        else {
            panic!("one shadowing warning, and the module checks");
        };
        assert_eq!(
            (
                diagnostic.range,
                diagnostic.severity,
                diagnostic.code.as_deref()
            ),
            (
                range(Span(0, 4, 0, 7)),
                Severity::WARNING,
                Some("ShadowedBuiltin")
            ),
            "a warning at the shadowing name, never an error"
        );
        assert!(diagnostic.related_information.is_empty());
    }

    #[test]
    fn a_labeled_context_keeps_its_locus_and_cause_in_related_information()
    {
        let uri = DocumentUri::from("file:///strict/duplicate.gandr");
        let text = "def a : Integer ;\ndef a : Integer ;\ndef a = 1 ;\n";
        let diagnostics = checked(&uri, SourceText::from(text));
        let [ref diagnostic] = *diagnostics.as_slice()
        else {
            panic!("one duplicate signature");
        };
        let [ref related] = *diagnostic.related_information.as_slice()
        else {
            panic!("one original declaration");
        };
        assert_eq!(
            (&related.location, related.message.as_str()),
            (
                &Location {
                    uri,
                    range: range(Span(0, 0, 0, 17))
                },
                "first written here"
            ),
            "the first signature keeps its locus and says what it is"
        );
        assert_eq!(
            diagnostic.range,
            range(Span(1, 0, 1, 17)),
            "the duplicate is the lead range"
        );
    }

    #[test]
    fn a_refusal_publishes_its_label_and_note()
    {
        let uri = DocumentUri::from("file:///strict/head.gandr");
        let text = "def f(xs: Vec(Integer)) -> -F Integer {\n  pure 1\n}\n";
        let diagnostics = checked(&uri, SourceText::from(text));
        let [ref diagnostic] = *diagnostics.as_slice()
        else {
            panic!("one unresolved type head");
        };
        let lines: Vec<&str> = diagnostic.message.lines().collect();
        let [message, label, note] = *lines.as_slice()
        else {
            panic!("a message, a label and a note: {:?}", diagnostic.message);
        };
        assert!(message.contains("`Vec`"), "the message names the head");
        assert!(
            !message.contains(".."),
            "the range locates the head; the message repeats no byte range"
        );
        assert!(
            !label.is_empty() && label != "malformed source",
            "the label says what the span is, not its class"
        );
        assert!(
            note.starts_with("note: ") && note.contains("`f`"),
            "the note names the declaration the terminal names"
        );
    }

    #[test]
    fn one_refusal_is_published_at_every_verbosity()
    {
        let uri = DocumentUri::from("file:///strict/head.gandr");
        let text = SourceText::from("def f(xs: Vec(Integer)) -> -F Integer {\n  return 1\n}\n");
        let [user, detailed, debug, json] = [
            Verbosity::User,
            Verbosity::Detailed,
            Verbosity::Debug,
            Verbosity::Json,
        ]
        .map(|verbosity| {
            let diagnostics = recheck(
                &uri,
                &mut open(&uri),
                text,
                &gandr_surface_dispatcher::Unshadowed,
                verbosity,
                Spelling::Unicode,
                UNCARETED,
            )
            .diagnostics;
            let [ref diagnostic] = *diagnostics.as_slice()
            else {
                panic!("one unresolved type head at {verbosity:?}");
            };
            diagnostic.clone()
        });
        for other in [&detailed, &debug, &json] {
            assert_eq!(
                (
                    other.range,
                    other.code.as_deref(),
                    &other.related_information
                ),
                (user.range, user.code.as_deref(), &user.related_information),
                "a level changes the message alone"
            );
        }
        let names = |diagnostic: &Diagnostic| -> Vec<String> {
            diagnostic
                .message
                .lines()
                .skip(user.message.lines().count())
                .filter_map(|line| line.split_once(": ").map(|(name, _)| name.to_owned()))
                .collect()
        };
        assert_eq!(
            user.message.lines().count(),
            3_usize,
            "message, label, note"
        );
        assert!(
            detailed.message.starts_with(&user.message)
                && debug.message.starts_with(&detailed.message),
            "each level keeps the one below it"
        );
        assert_eq!(names(&detailed), ["class", "detail", "expression"]);
        assert!(
            detailed.message.ends_with("expression: `Vec`"),
            "the detailed level quotes the offending source: {:?}",
            detailed.message
        );
        assert_eq!(names(&debug), [
            "class",
            "detail",
            "expression",
            "spans",
            "refusal"
        ]);
        let image: serde_json::Value =
            serde_json::from_str(&json.message).expect("the json level publishes one JSON image");
        assert_eq!(
            (image["name"].as_str(), image["message"].as_str()),
            (user.code.as_deref(), user.message.lines().next()),
            "the image carries the refusal's name and plain message"
        );
    }

    #[test]
    fn a_fault_is_published_at_the_origin()
    {
        let lowered = DocumentUri::from("file:///corpus/fixture/pending/lowered.gandr");
        let diagnostics = checked(&lowered, SourceText::from("def a = 1 ;\n"));
        let [ref diagnostic] = *diagnostics.as_slice()
        else {
            panic!("one pending-root ledger line");
        };
        assert_eq!(diagnostic.range, Range::default());
        assert_eq!(diagnostic.severity, Severity::ERROR);
        assert_eq!(diagnostic.source, "gandr");
        assert_eq!(diagnostic.code, None);
        assert!(diagnostic.related_information.is_empty());
    }

    /// A pending source refused as a whole publishes its refusal as the same
    /// text under the fixture root does, where `check` prints nothing for it.
    #[test]
    fn a_pending_source_publishes_its_refusal_1248()
    {
        for text in ["nowhere\n", "pure 3\n", "{ }\n"] {
            let source = SourceText::from(text);
            let pending = checked(
                &DocumentUri::from("file:///corpus/fixture/pending/whole.gandr"),
                source,
            );
            let fixture = checked(
                &DocumentUri::from("file:///corpus/fixture/whole.gandr"),
                source,
            );
            let shown =
                |diagnostics: &[Diagnostic]| -> Vec<(Range, Severity, Option<String>, String)> {
                    diagnostics
                        .iter()
                        .map(|diagnostic| {
                            (
                                diagnostic.range,
                                diagnostic.severity,
                                diagnostic.code.clone(),
                                diagnostic.message.clone(),
                            )
                        })
                        .collect()
                };
            assert!(
                !pending.is_empty(),
                "`{}` under the pending set publishes its refusal",
                text.trim_end()
            );
            assert_eq!(
                shown(&pending),
                shown(&fixture),
                "`{}` publishes as the same text under the fixture root",
                text.trim_end()
            );
        }
    }

    #[test]
    fn a_refusal_in_an_import_is_published_where_the_document_reaches_it_1199()
    {
        let directory =
            std::env::temp_dir().join(format!("gandr-import-locus-{}", std::process::id()));
        let _cleared = std::fs::remove_dir_all(&directory);
        std::fs::create_dir_all(&directory).expect("the scratch directory is created");
        let directory =
            std::fs::canonicalize(&directory).expect("the scratch directory canonicalises");
        let base =
            "module P :> #{\n  type Spent = Cap[1] {write},\n  type Moving = ?Spent. end\n} {\n}\n";
        let user = "import \"./base.gandr\" ;\n@[ checks ]\ndef moved() -> -F Unit {\n  fork \
                    (kernel : P.Moving) {\n    recv(kernel) as held;\n    close(kernel)\n  } \
                    as ring;\n  close(ring)\n}\n";
        for (file, text) in [("base.gandr", base), ("user.gandr", user)] {
            std::fs::write(directory.join(file), text).expect("the source is written");
        }
        let uri = |file: &str| {
            DocumentUri::of_path(&directory.join(file)).expect("the path is a file URI")
        };
        let diagnostics = checked(&uri("user.gandr"), SourceText::from(user));
        let [ref diagnostic] = *diagnostics.as_slice()
        else {
            panic!("the importer publishes its one refusal: {diagnostics:?}");
        };
        assert_eq!(
            diagnostic.range,
            range(Span(3, 2, 3, 6)),
            "the refused payload is the import's, so the refusal stands at the fork whose \
             session type the importer forms, never at the origin"
        );
        let imported: Vec<(&DocumentUri, Range)> = diagnostic
            .related_information
            .iter()
            .filter(|related| related.location.uri != uri("user.gandr"))
            .map(|related| (&related.location.uri, related.location.range))
            .collect();
        assert_eq!(
            imported,
            [(&uri("base.gandr"), range(Span(1, 15, 1, 29)))],
            "the refused payload, at the import's own line"
        );
        let _removed = std::fs::remove_dir_all(&directory);
    }

    #[test]
    fn an_admission_follows_the_published_diagnostics()
    {
        let uri = DocumentUri::from("file:///strict/admitted.gandr");
        let mut session = open(&uri);
        let rechecked = recheck(
            &uri,
            &mut session,
            SourceText::from("def a : Integer ;\ndef a = 1 ;\n"),
            &gandr_surface_dispatcher::Unshadowed,
            Verbosity::User,
            Spelling::Unicode,
            UNCARETED,
        );
        assert_eq!(rechecked.diagnostics, Vec::new());
        assert_eq!(
            rechecked.timing.admitted,
            Maybe::Absent(admitted::Absent::Pending),
            "the diagnostics exist before the kernel is offered the revision"
        );
        let admission = admit(&mut session, rechecked.timing);
        assert!(
            matches!(admission.fault, Maybe::Absent(_)),
            "the kernel agrees"
        );
        assert!(matches!(admission.timing.admitted, Maybe::Present(_)));
        assert_eq!(
            (
                admission.timing.forms,
                admission.timing.judged,
                admission.timing.wall
            ),
            (
                rechecked.timing.forms,
                rechecked.timing.judged,
                rechecked.timing.wall
            ),
            "the admission adds its wall and keeps the recheck's"
        );
        assert_eq!(
            admit(&mut session, admission.timing).timing,
            admission.timing,
            "an admitted synchronisation is not admitted again"
        );
        let refused = recheck(
            &uri,
            &mut session,
            SourceText::from("pure 3\n"),
            &gandr_surface_dispatcher::Unshadowed,
            Verbosity::User,
            Spelling::Unicode,
            UNCARETED,
        );
        assert_eq!(
            refused.timing.admitted,
            Maybe::Absent(admitted::Absent::Unadmitted),
            "a revision refused whole leaves nothing to admit"
        );
        assert_eq!(admit(&mut session, refused.timing).timing, refused.timing);
    }

    #[test]
    fn a_trial_ranks_candidates_with_their_diagnostics()
    {
        let uri = DocumentUri::from("file:///strict/tried.gandr");
        let base = "def a = 1 ;\ndef f : Integer ;\n";
        let candidates = [
            "def a = 1 ;\ndef f : Integer ;\ndef f = \"one\" ;\n",
            "pure 3\n",
            "def a = 1 ;\ndef f : Integer ;\ndef f = a ;\n",
        ];
        let mut session = open(&uri);
        let before = recheck(
            &uri,
            &mut session,
            SourceText::from(base),
            &gandr_surface_dispatcher::Unshadowed,
            Verbosity::User,
            Spelling::Unicode,
            UNCARETED,
        )
        .diagnostics;
        let tried = trial(
            &uri,
            &session,
            &candidates.map(SourceText::from),
            &gandr_surface_dispatcher::Unshadowed,
        );
        assert_eq!(
            tried
                .iter()
                .map(|tried| (usize::from(tried.candidate), tried.reached))
                .collect::<Vec<_>>(),
            [
                (2_usize, Reached::Judged),
                (0_usize, Reached::Judged),
                (1_usize, Reached::RefusedWhole)
            ],
            "a settling candidate, then a refused declaration, then a revision refused whole"
        );
        for tried in &tried {
            let text = candidates[usize::from(tried.candidate)];
            assert_eq!(
                tried.diagnostics,
                checked(&uri, SourceText::from(text)),
                "each candidate's diagnostics are a fresh recheck's: {text}"
            );
        }
        assert!(tried[0_usize].diagnostics.is_empty());
        assert_eq!(
            recheck(
                &uri,
                &mut session,
                SourceText::from(base),
                &gandr_surface_dispatcher::Unshadowed,
                Verbosity::User,
                Spelling::Unicode,
                UNCARETED
            )
            .diagnostics,
            before,
            "the session judges its text as before the trial"
        );
    }
}
