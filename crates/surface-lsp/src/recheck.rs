//! The whole-document recheck: every synchronisation composes the document
//! from scratch through the dispatcher's composition, and every token request
//! highlights it from scratch through the grammar's role table.
//!
//! The grammar and its role table are built once per process and shared by
//! every recheck. Nothing else is kept between requests: an incremental
//! recheck is a later server's, and until then a document is exactly as
//! current as its last synchronisation.

use std::path::Path;
use std::sync::OnceLock;

use gandr_surface_corpus::Settlement;
use gandr_surface_diagnostics::Class;
use gandr_surface_diagnostics::Entry;
use gandr_surface_diagnostics::Report;
use gandr_surface_diagnostics::entries;
use gandr_surface_dispatcher::Composed;
use gandr_surface_dispatcher::Goals;
use gandr_surface_dispatcher::LoweringCount;
use gandr_surface_dispatcher::SourceRoot;
use gandr_surface_dispatcher::Standing;
use gandr_surface_dispatcher::Step;
use gandr_surface_dispatcher::Verb;
use gandr_surface_dispatcher::classify;
use gandr_surface_dispatcher::compose;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::PbgError;
use gandr_surface_grammar::RoleTable;
use gandr_surface_grammar::built_in;
use gandr_surface_parser::parse;
use gandr_surface_render_remote::ByteOffset;
use gandr_surface_render_remote::HlSpan;
use gandr_surface_render_remote::LineIndex;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::position::Range;
use crate::protocol::Diagnostic;
use crate::protocol::DocumentUri;
use crate::protocol::Location;
use crate::protocol::RelatedInformation;
use crate::protocol::Severity;

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

/// The diagnostics of the document at `uri`, whose text is `text`.
///
/// # Specification
/// - requires: nothing; any text is admissible input.
/// - ensures: the document is composed whole through the dispatcher's
///   composition, under the root its `file` URI's path classifies as, and each
///   entry `gandr check --goals` prints for it becomes one diagnostic, in the
///   order printed: a report at the range its span projects to, with the
///   refusal's vocabulary name as its code, its title as its message, each
///   context locus as a related location carrying its label, and the severity
///   of a goal as information and of every other report as an error; a report
///   the renderer leaves unlocated, and a ledger line, at the document's
///   origin. A fault that keeps the document from composing is one error at the
///   origin naming it.
/// - provides: the one recheck every synchronisation publishes.
/// - fails: never; a fault is a diagnostic.
/// - panics: none.
/// - intension: one composition per call, and one projection per span end.
///
/// # Adequacy
/// - hypothesis: L2 — over every corpus source, the diagnostics are the reports
///   the dispatcher's walk renders for that source under `check --goals`, at
///   the same ranges and codes; L3 — a type mismatch and a duplicate signature
///   are asserted at their related locations, and a pending source at its
///   ledger line.
/// - witness: `session::session::every_corpus_report_is_published_where_the_walk_renders_it`
/// - witness: `recheck::tests::causal_contexts_become_lsp_related_information`
/// - witness: `recheck::tests::a_labeled_context_keeps_its_locus_and_cause_in_related_information`
/// - witness: `recheck::tests::a_fault_is_published_at_the_origin`
#[inline]
#[must_use]
pub fn recheck(
    uri: &DocumentUri,
    text: SourceText<'_>,
) -> Vec<Diagnostic>
{
    let toolkit = match toolkit() {
        | Ok(toolkit) => toolkit,
        | Err(fault) => {
            return vec![Diagnostic::at_origin(format!(
                "the built-in grammar did not build: {fault}"
            ))];
        },
    };
    let path = uri.path();
    let root = classify(&path);
    let mut lowerings = LoweringCount::default();
    let composed = match compose(&toolkit.grammar, root.corpus_root(), text, &mut lowerings) {
        | Ok(composed) => composed,
        | Err(fault) => return vec![Diagnostic::at_origin(fault.to_string())],
    };
    let index = LineIndex::new(text.as_ref().into());
    let step = Step::Source {
        path: Path::new(&path),
        root,
        text,
        standing: standing(root, &composed),
        composed,
    };
    entries(&step, Verb::Check(Goals::Reported))
        .map(|entry| match entry {
            | Entry::Report(report) => diagnostic(&report, &index, uri),
            | Entry::Line(line) => Diagnostic::at_origin(line.to_string()),
        })
        .collect()
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
/// - hypothesis: L1 — a definition is asserted at its exact stream; L2 — over
///   every corpus source, the encoded stream covers the spans this answers.
/// - witness: `recheck::tests::a_definition_produces_semantic_tokens`
/// - witness: `session::session::corpus_tokens_cover_the_highlighted_bytes`
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

/// How `composed`, a source under `root`, stands against its root: the
/// standing the dispatcher's walk gives the same source.
///
/// # Specification
/// - requires: nothing.
/// - ensures: under the pending root, a source refused as a whole, or one
///   carrying a refusal no expectation can state, is pending, and any other
///   lowered; under the strict and fixture roots, a source refused as a whole
///   is refused, and any other settled or unsettled as its report's tally is.
/// - provides: the standing the renderer reads to choose what to print, so a
///   pending source publishes exactly what `gandr check` prints for it.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — over every corpus source, pending sources included, the
///   diagnostics published agree with the walk's own reports.
/// - witness: `session::session::every_corpus_report_is_published_where_the_walk_renders_it`
/// - witness: `recheck::tests::a_fault_is_published_at_the_origin`
fn standing(
    root: SourceRoot,
    composed: &Composed<'_>,
) -> Standing
{
    match (root, composed) {
        | (SourceRoot::Pending, &Composed::Refused(_)) => Standing::Pending,
        | (SourceRoot::Pending, &Composed::Settled { ref unstatable, .. }) => {
            if unstatable.is_empty() {
                Standing::Lowered
            }
            else {
                Standing::Pending
            }
        },
        | (SourceRoot::Strict | SourceRoot::Fixture, &Composed::Refused(_)) => Standing::Refused,
        | (SourceRoot::Strict | SourceRoot::Fixture, &Composed::Settled { ref report, .. }) => {
            match report.tally().settlement() {
                | Settlement::Settled => Standing::Settled,
                | Settlement::Unsettled => Standing::Unsettled,
            }
        },
    }
}

/// The diagnostic `report` is published as.
///
/// # Specification
/// - requires: `index` was built from the text `report` is about.
/// - ensures: as [`recheck`] states for one report. A span the renderer locates
///   lies inside the text on character boundaries, so it always projects; the
///   origin stands in for one that would not.
/// - provides: the one map from a renderer report to an editor diagnostic.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a type mismatch and a duplicate signature are each
///   asserted at their exact diagnostic.
/// - witness: `recheck::tests::causal_contexts_become_lsp_related_information`
/// - witness: `recheck::tests::a_labeled_context_keeps_its_locus_and_cause_in_related_information`
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
    let mut diagnostic = Diagnostic::new(range, severity, report.title().to_string());
    if let Maybe::Present(spelling) = report.identifier() {
        diagnostic.code = Some(spelling.to_string());
    }
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
        .collect();
    diagnostic
}

#[cfg(test)]
mod tests
{
    use gandr_surface_syntax::SourceText;

    use super::highlight;
    use super::recheck;
    use super::toolkit;
    use crate::position::Character;
    use crate::position::Line;
    use crate::position::Position;
    use crate::position::Range;
    use crate::protocol::Diagnostic;
    use crate::protocol::DocumentUri;
    use crate::protocol::Location;
    use crate::protocol::RelatedInformation;
    use crate::protocol::Severity;
    use crate::tokens::TokenStream;
    use crate::tokens::encode;

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
        let mut expected = Diagnostic::new(
            range(Span(1, 12, 1, 18)),
            Severity::ERROR,
            "the type this term synthesises does not convert to the type it is checked against"
                .to_owned(),
        );
        expected.code = Some("TypeMismatch".to_owned());
        expected.related_information = vec![RelatedInformation {
            location: Location {
                uri: uri.clone(),
                range: range(Span(0, 12, 0, 19)),
            },
            message: "the type it is checked against".to_owned(),
        }];
        assert_eq!(
            recheck(&uri, SourceText::from(text)),
            vec![expected],
            "the signature's type explains the mismatch from where it is written"
        );
    }

    #[test]
    fn a_labeled_context_keeps_its_locus_and_cause_in_related_information()
    {
        let uri = DocumentUri::from("file:///strict/duplicate.gandr");
        let text = "def a : Integer ;\ndef a : Integer ;\ndef a = 1 ;\n";
        let diagnostics = recheck(&uri, SourceText::from(text));
        assert_eq!(diagnostics.len(), 1_usize, "one duplicate, one diagnostic");
        let related = diagnostics
            .first()
            .map(|diagnostic| diagnostic.related_information.clone());
        assert_eq!(
            related,
            Some(vec![RelatedInformation {
                location: Location {
                    uri,
                    range: range(Span(0, 0, 0, 17)),
                },
                message: "first written here".to_owned(),
            }]),
            "the first signature is the related location, labelled as what it is"
        );
    }

    #[test]
    fn a_fault_is_published_at_the_origin()
    {
        let lowered = DocumentUri::from("file:///corpus/fixture/pending/lowered.gandr");
        assert_eq!(
            recheck(&lowered, SourceText::from("def a = 1 ;\n")),
            vec![Diagnostic::at_origin(
                "/corpus/fixture/pending/lowered.gandr: unsettled: a pending source whose every \
                 expectation can be stated; it belongs under the fixture root"
                    .to_owned()
            )],
            "a pending source the lowering reads is its ledger line, at the origin"
        );
        let pending = DocumentUri::from("file:///corpus/fixture/pending/whole.gandr");
        assert_eq!(
            recheck(&pending, SourceText::from("ret 3\n")),
            Vec::new(),
            "a pending source refused as a whole stands as its root expects"
        );
    }
}
