//! Attribute refusals through a session: each misuse of an attribute reported
//! at its own bytes, with the refusal that names it.
//!
//! Every source sits under the fixture root, where expectations may be
//! written, so the refusal observed is the attribute's own and never the
//! strict root's guard against expectations.

use std::path::Path;

use gandr_core_term::FailureClass;
use gandr_surface_diagnostics::Class;
use gandr_surface_diagnostics::Entry;
use gandr_surface_diagnostics::Report;
use gandr_surface_diagnostics::entries;
use gandr_surface_dispatcher::Goals;
use gandr_surface_dispatcher::SourceRoot;
use gandr_surface_dispatcher::Verb;
use gandr_surface_syntax::ByteSpan;
use quenchant_shape::shape::Maybe;

use crate::common::Text;
use crate::common::footprints;
use crate::common::session;
use crate::common::submit;

/// What one report says: its class, the refusal it names, the text at its
/// primary span, its title, and the text at each context locus it marks.
#[derive(Debug, Eq, PartialEq)]
struct Seen
{
    /// The report's class.
    class: Class,
    /// The refusal's spelling.
    identifier: String,
    /// The text at the primary span.
    locus: String,
    /// The report's title.
    title: String,
    /// The text at each context locus.
    context: Vec<String>,
}

/// The text `span` covers in `source`.
///
/// # Specification
/// trivial.
fn spanned(
    source: Text<'_>,
    span: ByteSpan,
) -> String
{
    source
        .0
        .get(usize::from(span.start()) .. usize::from(span.end()))
        .expect("the span lies on the source's character boundaries")
        .to_owned()
}

/// What `report`, over `source`, says.
///
/// # Specification
/// trivial.
fn seen(
    source: Text<'_>,
    report: &Report<'_>,
) -> Seen
{
    let Maybe::Present(identifier) = report.identifier()
    else {
        panic!("an attribute misuse names a refusal: {}", report.title());
    };
    let Maybe::Present(span) = report.span()
    else {
        panic!("an attribute misuse is located: {}", report.title());
    };
    Seen {
        class: report.class(),
        identifier: identifier.to_string(),
        locus: spanned(source, span),
        title: report.title().to_string(),
        context: report
            .context()
            .into_iter()
            .filter_map(|annotation| match annotation {
                | Maybe::Present(annotation) => Some(spanned(source, annotation.span)),
                | Maybe::Absent(_) => None,
            })
            .collect(),
    }
}

/// The reports a fresh session's submission of `source` prints, under the
/// fixture root.
///
/// # Specification
/// trivial.
fn reports<'text>(source: impl Into<Text<'text>>) -> Vec<Seen>
{
    let source = source.into();
    let step =
        submit(&mut session(SourceRoot::Fixture), source.0).into_step(Path::new("attribute.gandr"));
    entries(&step, Verb::Check(Goals::Reported))
        .map(|entry| match entry {
            | Entry::Report(report) => seen(source, &report),
            | Entry::Line(line) => {
                panic!("a fixture source with no pending refusal prints no line: {line}")
            },
        })
        .collect()
}

/// The one report of `source`'s submission.
///
/// # Specification
/// trivial.
fn only<'text>(source: impl Into<Text<'text>>) -> Seen
{
    let source = source.into();
    let mut found = reports(source);
    assert_eq!(
        found.len(),
        1_usize,
        "one report for {:?}: {found:?}",
        source.0
    );
    found.remove(0)
}

#[test]
fn a_bare_marker_missing_its_payload_is_a_diagnostic()
{
    // `owes` takes an integer payload; written bare it is refused, and the
    // declaration it decorates is offered to no one.
    let source = "@[owes]\ndef f : Integer ;\n";
    assert_eq!(only(source), Seen {
        class: Class::Refusal(FailureClass::MalformedSource),
        identifier: String::from("MissingPayload"),
        locus: String::from("owes"),
        title: String::from("`owes` at 2..6 takes an integer payload and was given none"),
        context: Vec::new(),
    });
    let mut session = session(SourceRoot::Fixture);
    let _refused = submit(&mut session, source);
    assert!(
        footprints(&session).is_empty(),
        "the refused declaration is no item"
    );
}

#[test]
fn a_computation_payload_is_rejected_as_non_value()
{
    assert_eq!(only("@[owes(ret 1)]\ndef f : Integer ;\n"), Seen {
        class: Class::Refusal(FailureClass::MalformedSource),
        identifier: String::from("NonValuePayload"),
        locus: String::from("ret 1"),
        title: String::from("the payload of `owes` at 7..12 is `ret_expression`, not a value"),
        context: Vec::new(),
    });
}

#[test]
fn duplicate_single_valued_attribute_is_a_diagnostic()
{
    let duplicate = only("@[refuses(\"a\")]\n@[refuses(\"b\")]\ndef f = 42 ;\n");
    assert_eq!(
        duplicate,
        Seen {
            class: Class::Refusal(FailureClass::MalformedSource),
            identifier: String::from("DuplicateAttribute"),
            locus: String::from("refuses(\"b\")"),
            title: String::from(
                "the attribute `refuses` is already written at 2..14; a second at 18..30"
            ),
            context: vec![String::from("refuses(\"a\")")],
        },
        "the second writing is refused, the first marked as its context"
    );
}

#[test]
fn an_ill_typed_payload_becomes_an_ordinary_type_error()
{
    // The prior implementation handed an ill-typed payload to the checker,
    // which reported a plain type error. The reboot types a payload against
    // its schema where the lowering reads it, so the error is the lowering's
    // own refusal — reported as every type error is: a refusal of the
    // malformed-source class, located at the payload.
    let mismatch = only("def x : String ;\ndef x = 1 ;\n");
    assert_eq!(mismatch.identifier, "TypeMismatch");
    for (source, locus, title) in [
        (
            "@[refuses(42)]\ndef f = 42 ;\n",
            "42",
            "`refuses` at 10..12 takes a text payload and was given an integer payload",
        ),
        (
            "@[owes(thunk { ret 1 })]\ndef f : Integer ;\n",
            "thunk { ret 1 }",
            "`owes` at 7..22 takes an integer payload and was given a non-literal payload",
        ),
    ] {
        assert_eq!(
            only(source),
            Seen {
                class: mismatch.class,
                identifier: String::from("IllTypedPayload"),
                locus: String::from(locus),
                title: String::from(title),
                context: Vec::new(),
            },
            "{source:?} is refused at its payload, in the class of a type mismatch"
        );
    }
}

#[test]
fn an_unknown_attribute_reports_with_and_without_a_suggestion()
{
    // A near miss of a registered name suggests it; a distant one suggests
    // nothing. Both are the same refusal.
    assert_eq!(only("@[owe(1)]\ndef f : Integer ;\n"), Seen {
        class: Class::Refusal(FailureClass::MalformedSource),
        identifier: String::from("UnknownAttribute"),
        locus: String::from("owe(1)"),
        title: String::from("no attribute is registered as `owe` at 2..8; the nearest is `owes`"),
        context: Vec::new(),
    });
    assert_eq!(only("@[zzzzzzzz(1)]\ndef f : Integer ;\n"), Seen {
        class: Class::Refusal(FailureClass::MalformedSource),
        identifier: String::from("UnknownAttribute"),
        locus: String::from("zzzzzzzz(1)"),
        title: String::from("no attribute is registered as `zzzzzzzz` at 2..13"),
        context: Vec::new(),
    });
}
