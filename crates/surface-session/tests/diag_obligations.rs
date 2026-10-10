//! The parser's completion obligations through a session: the parse's own
//! buffer, the submission that carries it, and the reports beside it.
//!
//! Three groups, after the engine suite they port: authority, the parse the
//! only source of a revision's obligations; rows, each class and exact span
//! in source order, deterministically; and recovery, a malformed declaration
//! followed by a valid one reported as the repair beside both declarations.

use std::path::Path;

use gandr_core_incremental::ItemKey;
use gandr_core_term::FailureClass;
use gandr_surface_diagnostics::Class;
use gandr_surface_diagnostics::Entry;
use gandr_surface_diagnostics::entries;
use gandr_surface_dispatcher::Goals;
use gandr_surface_dispatcher::SourceRoot;
use gandr_surface_dispatcher::Verb;
use gandr_surface_parser::Oblig;
use gandr_surface_parser::ObligationInstance;
use gandr_surface_parser::parse;
use gandr_surface_session::resumed;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::common::Text;
use crate::common::footprints;
use crate::common::grammar;
use crate::common::names;
use crate::common::session;
use crate::common::submit;

/// A malformed declaration — the stray `~` the melder cannot mold — followed
/// by a well-formed one: the recovery-continuation shape.
const MALFORMED_THEN_VALID: &str = "def bad = 1 ~ 2 ;\ndef good = 2 ;\n";

/// A source whose obligations disagree about order: the most severe, the
/// unmolded `~`, is the last in the source, behind two lower-severity repairs.
const SEVERITY_AND_SOURCE_ORDER_DISAGREE: &str = "def k = thunk { ret 1 ;\ndef b = 1 ~ 2 ;\n";

/// A recovering source the lowering refuses as a whole: an unterminated shell
/// block after a declaration.
const REFUSED_WHOLE: &str = "def answer = 42 ;\n#!{echo hello |";

/// A source that parses clean.
const CLEAN: &str = "def good = 2 ;\n";

/// The obligation of class `$class` over the bytes `$start..$end`.
macro_rules! at {
    ($class:expr, $start:literal.. $end:literal) => {
        ObligationInstance::new(
            $class,
            ByteSpan::new(ByteOffset::from($start), ByteOffset::from($end))
                .expect("the span is ordered"),
        )
    };
}

/// The text `span` covers in `source`.
///
/// # Specification
/// trivial.
fn spanned<'text>(
    source: impl Into<Text<'text>>,
    span: ByteSpan,
) -> Text<'text>
{
    let source = source.into().0;
    Text(
        source
            .get(usize::from(span.start()) .. usize::from(span.end()))
            .expect("the span lies on the source's character boundaries"),
    )
}

/// `obligations` as a multiset: ordered by span, then class, so two buffers
/// compare by content whatever order each keeps.
///
/// # Specification
/// trivial.
fn multiset(obligations: &[ObligationInstance]) -> Vec<(ByteSpan, Oblig)>
{
    let mut rows: Vec<(ByteSpan, Oblig)> = obligations
        .iter()
        .map(|obligation| (obligation.span, obligation.class))
        .collect();
    rows.sort_unstable();
    rows
}

#[test]
fn lowered_carries_the_parse_obligations_verbatim()
{
    // The melder decides what a revision's obligations are; the session
    // carries that buffer and re-derives nothing, on the path that judges the
    // revision and on the one that refuses it whole.
    let pbg = grammar();
    for source in [
        MALFORMED_THEN_VALID,
        SEVERITY_AND_SOURCE_ORDER_DISAGREE,
        REFUSED_WHOLE,
    ] {
        let parsed = parse(pbg, SourceText::from(source)).expect("the parse is total");
        assert!(
            !bool::from(parsed.is_clean()),
            "{source:?} must recover for the comparison to witness anything"
        );
        let submission = submit(&mut session(SourceRoot::Strict), source);
        assert_eq!(
            multiset(submission.obligations()),
            multiset(parsed.obligations()),
            "the submission carries the parse's obligations verbatim for {source:?}"
        );
    }
    let refused = submit(&mut session(SourceRoot::Strict), REFUSED_WHOLE);
    assert_eq!(
        refused.resumed().map(|_| ()),
        Maybe::Absent(resumed::Absent::RefusedWhole),
        "the shell block refuses the revision whole, so the refused path is the one witnessed"
    );
}

#[test]
fn a_clean_source_carries_no_obligations()
{
    let parsed = parse(grammar(), SourceText::from(CLEAN)).expect("the parse is total");
    assert!(
        bool::from(parsed.is_clean()),
        "the fixture must parse clean for this to witness anything"
    );
    let submission = submit(&mut session(SourceRoot::Strict), CLEAN);
    assert!(
        submission.obligations().is_empty(),
        "a clean parse carries no obligation"
    );
}

#[test]
fn rows_carry_the_class_and_the_exact_span()
{
    // One repair, one row: the class the melder assigned and the bytes it
    // held responsible — here the stray token itself.
    let submission = submit(&mut session(SourceRoot::Strict), MALFORMED_THEN_VALID);
    let rows = submission.obligations();
    assert_eq!(rows, &[at!(Oblig::UnmoldedTok, 12 .. 13)]);
    assert_eq!(spanned(MALFORMED_THEN_VALID, rows[0].span).0, "~");
}

#[test]
fn a_clean_source_reports_no_obligations()
{
    // The rows are the revision's, never the session's: a clean revision
    // after a recovering one reports none.
    let mut session = session(SourceRoot::Strict);
    let recovering = submit(&mut session, MALFORMED_THEN_VALID);
    assert_eq!(recovering.obligations(), &[at!(
        Oblig::UnmoldedTok,
        12 .. 13
    )]);
    let clean = submit(&mut session, CLEAN);
    assert!(
        clean.obligations().is_empty(),
        "the repaired revision reports no obligation of the one before it"
    );
}

#[test]
fn rows_are_in_source_order_not_severity_order()
{
    // The parse buffers by severity, its minimization order, which puts the
    // last obligation in the source first. The rows are read in source order,
    // so the submission sorts rather than inherits.
    let parsed = parse(
        grammar(),
        SourceText::from(SEVERITY_AND_SOURCE_ORDER_DISAGREE),
    )
    .expect("the parse is total");
    assert_eq!(
        parsed
            .obligations()
            .first()
            .map(|obligation| obligation.class),
        Some(Oblig::UnmoldedTok),
        "the parse buffers the most severe obligation first"
    );
    let submission = submit(
        &mut session(SourceRoot::Strict),
        SEVERITY_AND_SOURCE_ORDER_DISAGREE,
    );
    let rows = submission.obligations();
    assert_eq!(
        rows,
        &[
            at!(Oblig::MissingTile, 6 .. 7),
            at!(Oblig::MissingTile, 22 .. 23),
            at!(Oblig::UnmoldedTok, 34 .. 35),
        ],
        "the rows ascend by span"
    );
    assert_eq!(
        spanned(SEVERITY_AND_SOURCE_ORDER_DISAGREE, rows[2].span).0,
        "~"
    );
}

#[test]
fn rows_are_deterministic_across_lowerings()
{
    for source in [
        MALFORMED_THEN_VALID,
        SEVERITY_AND_SOURCE_ORDER_DISAGREE,
        REFUSED_WHOLE,
        CLEAN,
    ] {
        let mut resubmitted = session(SourceRoot::Strict);
        let first = submit(&mut resubmitted, source).obligations().to_vec();
        let again = submit(&mut resubmitted, source).obligations().to_vec();
        let fresh = submit(&mut session(SourceRoot::Strict), source)
            .obligations()
            .to_vec();
        assert_eq!(first, again, "{source:?} resubmitted to one session");
        assert_eq!(first, fresh, "{source:?} submitted to a fresh session");
    }
}

#[test]
fn recovery_then_a_valid_declaration_reports_the_repair_and_keeps_both()
{
    // The prior implementation holed the malformed declaration and reported
    // the hole as a goal. The reboot has no recovery hole: the lowering
    // refuses the malformed declaration in place, its one report the refusal
    // at the stray token, and the later declaration lowers, checks and
    // resumes intact.
    let mut session = session(SourceRoot::Strict);
    let submission = submit(&mut session, MALFORMED_THEN_VALID);
    assert_eq!(
        names(submission.composed()),
        ["bad", "good"],
        "both declarations are reported, in source order"
    );
    assert_eq!(
        submission.obligations(),
        &[at!(Oblig::UnmoldedTok, 12 .. 13)],
        "the repair is reported once, at the responsible bytes"
    );
    assert_eq!(
        footprints(&session)
            .into_iter()
            .map(|(key, _)| key)
            .collect::<Vec<_>>(),
        [ItemKey::from("good")],
        "the refused declaration is offered to no one; the valid one resumes"
    );
    let path = Path::new("recovery.gandr");
    let step = submission.into_step(path);
    let reports: Vec<_> = entries(&step, Verb::Check(Goals::Reported))
        .map(|entry| match entry {
            | Entry::Report(report) => (
                report.class(),
                report.identifier().map(|spelling| spelling.to_string()),
                report.span(),
            ),
            | Entry::Line(line) => panic!("a strict source prints no ledger line: {line}"),
        })
        .collect();
    assert_eq!(
        reports,
        [(
            Class::Refusal(FailureClass::MalformedSource),
            Maybe::Present(String::from("MalformedForm")),
            Maybe::Present(at!(Oblig::UnmoldedTok, 12 .. 13).span),
        )],
        "the malformed declaration's refusal is the one report; `good` settles and nothing is a goal"
    );
}

#[test]
fn a_clean_source_keeps_every_surface_empty()
{
    let submission = submit(&mut session(SourceRoot::Strict), CLEAN);
    assert!(
        submission.obligations().is_empty(),
        "a clean parse carries no obligation"
    );
    let step = submission.into_step(Path::new("clean.gandr"));
    for verb in [
        Verb::Check(Goals::Gated),
        Verb::Check(Goals::Reported),
        Verb::Test,
    ] {
        assert_eq!(
            entries(&step, verb).count(),
            0_usize,
            "{verb:?} prints nothing for a clean source: no refusal, no goal, no ledger line"
        );
    }
}
