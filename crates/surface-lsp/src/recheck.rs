//! The document recheck: every open document holds a session, each
//! synchronisation judges the document's text in it and then admits it, and
//! every token request highlights the text from scratch through the grammar's
//! role table.
//!
//! The grammar and its role table are built once per process and shared. A
//! document's session keeps its forms between synchronisations, so a change
//! molds only the forms it touched; its report is the dispatcher's
//! composition of the whole text, which is what `gandr check` prints for it.
//! The diagnostics are read off the judgement, before the kernel is offered
//! the revision; [`admit`] runs the admission afterwards and names a kernel
//! disagreement, should it find one, as the diagnostic that replaces them.

use core::fmt;
use core::time::Duration;
use std::path::Path;
use std::sync::OnceLock;
use std::time::Instant;

use anodized::spec;
use gandr_core_incremental::BackendArtifact;
use gandr_core_incremental::MemoryCheckpointStore;
use gandr_core_incremental::ResumeCensus;
use gandr_storage_records::InMemoryBlockStore;
use gandr_surface_diagnostics::Class;
use gandr_surface_diagnostics::Entry;
use gandr_surface_diagnostics::Report;
use gandr_surface_diagnostics::entries;
use gandr_surface_dispatcher::ComposeFault;
use gandr_surface_dispatcher::Goals;
use gandr_surface_dispatcher::Verb;
use gandr_surface_dispatcher::classify;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::PbgError;
use gandr_surface_grammar::RoleTable;
use gandr_surface_grammar::built_in;
use gandr_surface_parser::parse;
use gandr_surface_render_remote::ByteOffset;
use gandr_surface_render_remote::HlSpan;
use gandr_surface_render_remote::LineIndex;
use gandr_surface_session::FormCensus;
use gandr_surface_session::Session;
use gandr_surface_session::SessionFault;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::position::Range;
use crate::protocol::Diagnostic;
use crate::protocol::DocumentUri;
use crate::protocol::Location;
use crate::protocol::RelatedInformation;
use crate::protocol::Severity;

/// The session one open document's revisions are submitted to, or the fault
/// that kept the grammar it parses under from building.
pub type DocumentSession =
    Result<Session<MemoryCheckpointStore, InMemoryBlockStore>, &'static PbgError>;

/// The built-in grammar and the role table read off it.
#[derive(Debug)]
struct Toolkit
{
    /// The grammar every document is parsed and composed under.
    grammar: Pbg,
    /// The roles its molds highlight as.
    roles: RoleTable,
}

/// The process's one toolkit, or the fault that kept it from building.
static TOOLKIT: OnceLock<Result<Toolkit, PbgError>> = OnceLock::new();

/// The process's one toolkit, built on first use.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the same toolkit, at the same address, on every call; the grammar
///   and its role table are built by the first call alone.
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
            Ok(Toolkit { grammar, roles })
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
/// - witness: `session::session::every_corpus_report_is_published_where_the_walk_renders_it`
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
/// - witness: `session::session::an_edit_to_a_large_document_rechecks_its_forms`
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
    ///   `, admitted in <wall> ms` when the admission ran.
    /// - panics: none.
    /// - executable: none — the formatter exposes neither its written bytes nor
    ///   its sink's failure state.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the transcript reads the molded count back out of the
    ///   line it logged.
    /// - witness: `session::session::an_edit_to_a_large_document_rechecks_its_forms`
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
            | Maybe::Present(census) => write!(
                f,
                "{}/{} items judged",
                usize::from(census.judged),
                usize::from(census.items)
            )?,
            | Maybe::Absent(judged::Absent::RefusedWhole) => f.write_str("refused whole")?,
            | Maybe::Absent(judged::Absent::Unchecked) => f.write_str("unchecked")?,
        }
        write!(f, ", {:.1} ms", self.wall.as_secs_f64() * 1_000.0_f64)?;
        match self.admitted {
            | Maybe::Present(wall) => {
                write!(
                    f,
                    ", admitted in {:.1} ms",
                    wall.as_secs_f64() * 1_000.0_f64
                )
            },
            | Maybe::Absent(admitted::Absent::Pending | admitted::Absent::Unadmitted) => Ok(()),
        }
    }
}

/// What one recheck produced: the diagnostics to publish, and its timing.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Rechecked
{
    /// The diagnostics, in the order `gandr check --goals` prints them.
    pub diagnostics: Vec<Diagnostic>,
    /// What the recheck cost.
    pub timing: Timing,
}

/// Judge `text`, the document at `uri`, in its `session`, and read its
/// diagnostics off the judgement.
///
/// # Specification
/// - requires: `session` was opened for `uri`; any text is admissible input.
/// - ensures: the text is judged once, and each entry `gandr check --goals`
///   prints for the judgement's step becomes one diagnostic, in the order
///   printed: a report at the range its span projects to, with the refusal's
///   vocabulary name as its code, its title, primary label and note as its
///   message, each context locus as a related location carrying its label, then
///   each nested reason, outermost first, as a related location carrying the
///   judgement it stands for, and the severity of a goal as information and of
///   every other report as an error; a report the renderer leaves unlocated,
///   and a ledger line, at the document's origin. A fault that keeps the
///   document from composing, and a grammar that did not build, is one error at
///   the origin naming it. The timing carries the judgement's form census, the
///   incremental checker's census, and the wall of the whole recheck; its
///   admission is pending when the judgement left one.
/// - provides: the one recheck every synchronisation publishes.
/// - fails: never; a fault is a diagnostic.
/// - panics: none.
/// - intension: one submission per call, and one projection per span end.
///
/// # Adequacy
/// - hypothesis: L2 — over every corpus source, the diagnostics are the reports
///   the dispatcher's walk renders for that source under `check --goals`, at
///   the same ranges and codes; L3 — a type mismatch and a duplicate signature
///   are asserted at their related locations, a force refused inside a thunk at
///   its nested reasons, and a pending source at its ledger line.
/// - witness: `session::session::every_corpus_report_is_published_where_the_walk_renders_it`
/// - witness: `session::session::an_edit_to_a_large_document_rechecks_its_forms`
/// - witness: `recheck::tests::causal_contexts_become_lsp_related_information`
/// - witness: `recheck::tests::a_labeled_context_keeps_its_locus_and_cause_in_related_information`
/// - witness: `recheck::tests::nested_reasons_become_lsp_related_information`
/// - witness: `recheck::tests::a_fault_is_published_at_the_origin`
#[spec(ensures: |ret| ret.diagnostics.iter().all(|diagnostic|
    diagnostic.source == "gandr" && diagnostic.range.start <= diagnostic.range.end
        && matches!(diagnostic.severity, Severity::ERROR | Severity::INFORMATION)
        && diagnostic.related_information.iter().all(|related|
            related.location.uri == *uri && related.location.range.start <= related.location.range.end)))]
#[must_use]
pub fn recheck(
    uri: &DocumentUri,
    session: &mut DocumentSession,
    text: SourceText<'_>,
) -> Rechecked
{
    let started = Instant::now();
    let unchecked = |diagnostic: Diagnostic| Rechecked {
        diagnostics: vec![diagnostic],
        timing: Timing {
            forms: FormCensus::default(),
            judged: Maybe::Absent(judged::Absent::Unchecked),
            wall: started.elapsed(),
            admitted: Maybe::Absent(admitted::Absent::Unadmitted),
        },
    };
    let session = match *session {
        | Ok(ref mut session) => session,
        | Err(fault) => {
            return unchecked(Diagnostic::at_origin(format!(
                "the built-in grammar did not build: {fault}"
            )));
        },
    };
    let submission = match session.judge(text) {
        | Ok(submission) => submission,
        | Err(fault) => return unchecked(Diagnostic::at_origin(fault.to_string())),
    };
    let forms = submission.forms();
    let (judged, admission) = match submission.resumed() {
        | Maybe::Present(resumed) => (
            Maybe::Present(resumed.census()),
            Maybe::Absent(admitted::Absent::Pending),
        ),
        | Maybe::Absent(_) => (
            Maybe::Absent(judged::Absent::RefusedWhole),
            Maybe::Absent(admitted::Absent::Unadmitted),
        ),
    };
    let path = uri.path();
    let index = LineIndex::new(text.as_ref().into());
    let step = submission.into_step(Path::new(&path));
    let diagnostics = entries(&step, Verb::Check(Goals::Reported))
        .map(|entry| match entry {
            | Entry::Report(report) => diagnostic(&report, &index, uri),
            | Entry::Line(line) => Diagnostic::at_origin(line.to_string()),
        })
        .collect();
    Rechecked {
        diagnostics,
        timing: Timing {
            forms,
            judged,
            wall: started.elapsed(),
            admitted: admission,
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
///   timing carries its wall; a kernel disagreement is one error at the origin
///   naming the fault `submit` would have reported, to publish in place of the
///   recheck's diagnostics. Otherwise nothing runs and the timing is returned
///   as it was.
/// - provides: the second half of every synchronisation, run after its
///   diagnostics are published.
/// - fails: never; a disagreement is a diagnostic.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a synchronisation's timing line carries the admission's
///   wall after the recheck's, and a refused document's carries none.
/// - witness: `session::session::an_edit_to_a_large_document_rechecks_its_forms`
/// - witness: `recheck::tests::an_admission_follows_the_published_diagnostics`
#[spec(ensures: |ret| ret.timing.forms == timing.forms && ret.timing.judged == timing.judged
    && ret.timing.wall == timing.wall
    && match timing.admitted {
        Maybe::Absent(admitted::Absent::Pending) => matches!(ret.timing.admitted, Maybe::Present(_)),
        Maybe::Present(_) | Maybe::Absent(admitted::Absent::Unadmitted) =>
            ret.timing.admitted == timing.admitted && matches!(ret.fault, Maybe::Absent(_)),
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
    let fault = match session.admit() {
        | Ok(_) => Maybe::Absent(agreed::Absent::Agreed),
        | Err(disagreement) => Maybe::Present(Diagnostic::at_origin(
            SessionFault::Compose(ComposeFault::Readmission(disagreement)).to_string(),
        )),
    };
    Admitted {
        fault,
        timing: Timing {
            admitted: Maybe::Present(started.elapsed()),
            ..timing
        },
    }
}

/// The highlighter's spans over `text`.
///
/// # Specification
/// - requires: nothing; any text is admissible input.
/// - ensures: the spans the grammar's role table classifies the parsed text
///   into, sorted and pairwise disjoint; none when the grammar did not build or
///   the parser could not commit a tree, faults the document's diagnostics
///   name.
/// - provides: the spans every token request encodes.
/// - fails: never.
/// - panics: none.
/// - intension: one parse per call.
///
/// # Adequacy
/// - hypothesis: L2 — a definition has a pinned semantic-token stream; over
///   every corpus source, encoded coverage agrees with the highlighter. Runtime
///   checks distinguish out-of-text, split-character, unsorted and overlapping
///   spans without reparsing the source.
/// - witness: `recheck::tests::a_definition_produces_semantic_tokens`
/// - witness: `session::session::corpus_tokens_cover_the_highlighted_bytes`
#[spec(ensures: |ret| ret.iter().all(|span|
    usize::from(span.range.end()) <= text.as_ref().len()
        && text.as_ref().is_char_boundary(usize::from(span.range.start()))
        && text.as_ref().is_char_boundary(usize::from(span.range.end())))
    && ret.iter().zip(ret.iter().skip(1)).all(|(first, second)| first.range.end() <= second.range.start()))]
#[inline]
#[must_use]
pub fn highlight(text: SourceText<'_>) -> Vec<HlSpan>
{
    let Ok(toolkit) = toolkit()
    else {
        return Vec::new();
    };
    // economy: a token request parses the document again rather than keep the
    // tree its last synchronisation composed; the composition consumes the
    // tree, and keeping both would hold every open document's tree for the
    // one request that may never come.
    let Ok(parsed) = parse(&toolkit.grammar, text)
    else {
        return Vec::new();
    };
    toolkit
        .roles
        .highlight(&parsed.into_tree())
        .unwrap_or_default()
}

/// The diagnostic `report` is published as.
///
/// # Specification
/// - requires: `index` was built from the text `report` is about.
/// - ensures: as [`recheck`] states for one report. A span the renderer locates
///   lies inside the text on character boundaries, so it always projects; the
///   origin stands in for one that would not. The message is the report's
///   title, then the primary locus's label on its own line when the report is
///   located, then its note on a line of its own after `note: ` when it closes
///   with one: what the terminal prints, in the one text field the protocol
///   gives a diagnostic.
/// - provides: the one map from a renderer report to an editor diagnostic.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a type mismatch and duplicate signature have exact
///   primary and causal locations, and a refused declaration's message carries
///   its label and note. L2 — every corpus report agrees with its wire ranges,
///   code, message and related labels, distinguishing omitted, misclassified or
///   misprojected report fields without pinning wording.
/// - witness: `recheck::tests::causal_contexts_become_lsp_related_information`
/// - witness: `recheck::tests::a_labeled_context_keeps_its_locus_and_cause_in_related_information`
/// - witness: `recheck::tests::nested_reasons_become_lsp_related_information`
/// - witness: `recheck::tests::a_refusal_publishes_its_label_and_note`
/// - witness: `session::session::every_corpus_report_is_published_where_the_walk_renders_it`
#[spec(ensures: |ret| ret.source == "gandr"
    && ret.severity == match report.class() { Class::Goal => Severity::INFORMATION, _ => Severity::ERROR }
    && ret.code.is_some() == matches!(report.identifier(), Maybe::Present(_))
    && ret.message.starts_with(&report.title().to_string())
    && ret.related_information.len() == report.context().into_iter()
        .filter(|slot| matches!(slot, Maybe::Present(_))).count().saturating_add(report.reasons().len())
    && ret.related_information.iter().all(|related| related.location.uri == *uri))]
fn diagnostic(
    report: &Report<'_>,
    index: &LineIndex<'_>,
    uri: &DocumentUri,
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
    let range = match report.span() {
        | Maybe::Present(span) => range_of(span),
        | Maybe::Absent(_) => Range::default(),
    };
    let severity = match report.class() {
        | Class::Goal => Severity::INFORMATION,
        | Class::Refusal(_) | Class::Unsettled(_) => Severity::ERROR,
    };
    let mut message = report.title().to_string();
    if let Maybe::Present(label) = report.label() {
        message.push('\n');
        message.push_str(&label.to_string());
    }
    if let Maybe::Present(note) = report.note() {
        message.push_str("\nnote: ");
        message.push_str(&note.to_string());
    }
    let mut diagnostic = Diagnostic::new(range, severity, message);
    if let Maybe::Present(spelling) = report.identifier() {
        diagnostic.code = Some(spelling.to_string());
    }
    let reasons = report
        .reasons()
        .into_iter()
        .map(|reason| RelatedInformation {
            location: Location {
                uri: uri.clone(),
                range: range_of(reason.span),
            },
            message: reason.to_string(),
        });
    diagnostic.related_information = report
        .context()
        .into_iter()
        .filter_map(|slot| match slot {
            | Maybe::Present(annotation) => Some(RelatedInformation {
                location: Location {
                    uri: uri.clone(),
                    range: range_of(annotation.span),
                },
                message: annotation.label.to_string(),
            }),
            | Maybe::Absent(_) => None,
        })
        .chain(reasons)
        .collect();
    diagnostic
}

#[cfg(test)]
mod tests
{
    use gandr_surface_syntax::SourceText;
    use quenchant_shape::shape::Maybe;

    use super::admit;
    use super::admitted;
    use super::grammar;
    use super::highlight;
    use super::open;
    use super::recheck;
    use super::toolkit;
    use crate::position::Character;
    use crate::position::Line;
    use crate::position::Position;
    use crate::position::Range;
    use crate::protocol::Diagnostic;
    use crate::protocol::DocumentUri;
    use crate::protocol::Location;
    use crate::protocol::Severity;
    use crate::tokens::TokenStream;
    use crate::tokens::encode;

    /// The diagnostics a document opened at `uri` with `text` publishes.
    ///
    /// # Specification
    /// trivial.
    fn checked(
        uri: &DocumentUri,
        text: SourceText<'_>,
    ) -> Vec<Diagnostic>
    {
        recheck(uri, &mut open(uri), text).diagnostics
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
        let spans = highlight(SourceText::from(text));
        let index = gandr_surface_render_remote::LineIndex::new(text.into());
        assert_eq!(
            encode(&index, &spans),
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
            "the editor's message spells both types under the title: {:?}",
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
    fn nested_reasons_become_lsp_related_information()
    {
        let uri = DocumentUri::from("file:///strict/force.gandr");
        let text = "def a : +U (-F Integer) ;\ndef a = thunk { force 1 } ;\n";
        let diagnostics = checked(&uri, SourceText::from(text));
        let [ref diagnostic] = *diagnostics.as_slice()
        else {
            panic!("one shape mismatch");
        };
        assert_eq!(
            (diagnostic.range, diagnostic.code.as_deref()),
            (range(Span(1, 22, 1, 23)), Some("ShapeMismatch")),
            "the forced integer is the primary locus"
        );
        let related: Vec<(Range, &str)> = diagnostic
            .related_information
            .iter()
            .map(|related| (related.location.range, related.message.as_str()))
            .collect();
        assert_eq!(
            related,
            [
                (
                    range(Span(1, 8, 1, 25)),
                    "while checking this against `+U (-F Integer)`"
                ),
                (
                    range(Span(1, 16, 1, 23)),
                    "while checking this against `-F Integer`"
                ),
            ],
            "the thunk and the force it holds, outermost first"
        );
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
        assert_eq!(related.location, Location {
            uri,
            range: range(Span(0, 0, 0, 17))
        });
    }

    #[test]
    fn a_refusal_publishes_its_label_and_note()
    {
        let uri = DocumentUri::from("file:///strict/head.gandr");
        let text = "def f(xs: List(Integer)) -> -F Integer {\n  ret 1\n}\n";
        let diagnostics = checked(&uri, SourceText::from(text));
        let [ref diagnostic] = *diagnostics.as_slice()
        else {
            panic!("one unresolved type head");
        };
        let lines: Vec<&str> = diagnostic.message.lines().collect();
        let [title, label, note] = *lines.as_slice()
        else {
            panic!("a title, a label and a note: {:?}", diagnostic.message);
        };
        assert!(title.contains("`List`"), "the title names the head");
        assert!(
            !title.contains(".."),
            "the range locates the head; the title repeats no byte range"
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
        let pending = DocumentUri::from("file:///corpus/fixture/pending/whole.gandr");
        assert_eq!(
            checked(&pending, SourceText::from("ret 3\n")),
            Vec::new(),
            "a pending source refused as a whole stands as its root expects"
        );
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
        let refused = recheck(&uri, &mut session, SourceText::from("ret 3\n"));
        assert_eq!(
            refused.timing.admitted,
            Maybe::Absent(admitted::Absent::Unadmitted),
            "a revision refused whole leaves nothing to admit"
        );
        assert_eq!(admit(&mut session, refused.timing).timing, refused.timing);
    }
}
