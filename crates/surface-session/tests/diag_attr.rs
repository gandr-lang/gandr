//! Attribute refusals through a session: each misuse of an attribute reported
//! at its own bytes, with the refusal that names it.
//!
//! Every source sits under the fixture root, where expectations may be
//! written, so the refusal observed is the attribute's own and never the
//! strict root's guard against expectations.

use std::path::Path;

use anodized::spec;
use gandr_core_term::FailureClass;
use gandr_surface_diagnostics::AnnotationKind;
use gandr_surface_diagnostics::Class;
use gandr_surface_diagnostics::Diagnostic;
use gandr_surface_diagnostics::Severity;
use gandr_surface_dispatcher::Goals;
use gandr_surface_dispatcher::SourceRoot;
use gandr_surface_dispatcher::Verb;
use gandr_surface_dispatcher::entries;
use gandr_surface_syntax::ByteSpan;
use quenchant_shape::shape::Maybe;

use crate::common::Text;
use crate::common::footprints;
use crate::common::session;
use crate::common::submit;

/// What one report says: its class, the refusal it names, the text at its
/// primary span, and the text at each context locus it marks.
///
/// # Specification
/// - requires: the producing report and source supply the fields’ context.
/// - ensures: holds the report’s class, stable identifier and source fragments,
///   excluding presentation prose.
/// - executable: none — The record declaration has no invocation and retains
///   neither the originating report nor its source spans. The seen function
///   states their executable relation while that context is available.
///
/// # Adequacy
/// - hypothesis: L3 — the recorded attribute-refusal cases and type-error
///   control, compared field by field with literal expectations. Context
///   coverage includes the first occurrence of a duplicate attribute.
/// - witness: `tests::diag_attr::a_bare_marker_missing_its_payload_is_a_diagnostic`
/// - witness: `tests::diag_attr::a_computation_payload_is_rejected_as_non_value`
/// - witness: `tests::diag_attr::duplicate_single_valued_attribute_is_a_diagnostic`
/// - witness: `tests::diag_attr::an_ill_typed_payload_becomes_an_ordinary_type_error`
/// - witness: `tests::diag_attr::an_unknown_attribute_is_located_at_its_application`
#[derive(Debug, Eq, PartialEq)]
struct Seen
{
    /// The report's class.
    class: Class,
    /// The refusal's spelling.
    identifier: String,
    /// The text at the primary span.
    locus: String,

    /// The text at each context locus.
    context: Vec<String>,
}

/// The text `span` covers in `source`.
///
/// # Specification
/// - requires: the span lies within the source on UTF-8 character boundaries.
/// - ensures: returns exactly the covered source characters, without clamping
///   or substituting a nearby occurrence.
/// - panics: when the required range is invalid.
///
/// # Adequacy
/// - hypothesis: L3 — the recorded attribute misuse and ordinary type-error
///   sources, observed as literal primary and contextual source fragments. The
///   predicate checks the complete slice rather than only its length.
/// - witness: `tests::diag_attr::a_bare_marker_missing_its_payload_is_a_diagnostic`
/// - witness: `tests::diag_attr::a_computation_payload_is_rejected_as_non_value`
/// - witness: `tests::diag_attr::duplicate_single_valued_attribute_is_a_diagnostic`
/// - witness: `tests::diag_attr::an_ill_typed_payload_becomes_an_ordinary_type_error`
/// - witness: `tests::diag_attr::an_unknown_attribute_is_located_at_its_application`
#[spec(
    requires: source
    .0
    .get(usize::from(span.start())..usize::from(span.end()))
    .is_some(),
    ensures: |ret| {
    source.0.get(usize::from(span.start())..usize::from(span.end()))
        == Some(ret.as_str())
},
)]
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

/// What `diagnostic`, over `source`, says.
///
/// # Specification
/// - requires: a named, located refusal whose annotations address complete
///   characters in this source.
/// - ensures: preserves the class and stable identifier and projects each
///   annotated locus exactly, the primary one as the locus and the context ones
///   in order.
/// - panics: if the required identifier, location or source range is absent.
///
/// # Adequacy
/// - hypothesis: L3 — the recorded attribute misuses, including the second
///   duplicate attribute with the first as its context, plus an ordinary type
///   mismatch. Exact class, identifier and source fragments distinguish the
///   decision surfaces without constraining title prose.
/// - witness: `tests::diag_attr::a_bare_marker_missing_its_payload_is_a_diagnostic`
/// - witness: `tests::diag_attr::a_computation_payload_is_rejected_as_non_value`
/// - witness: `tests::diag_attr::duplicate_single_valued_attribute_is_a_diagnostic`
/// - witness: `tests::diag_attr::an_ill_typed_payload_becomes_an_ordinary_type_error`
/// - witness: `tests::diag_attr::an_unknown_attribute_is_located_at_its_application`
#[spec(
    requires: matches!(diagnostic.identifier, Maybe::Present(_))
    && matches!(diagnostic.span, Maybe::Present(_))
    && diagnostic.annotations.iter().all(|annotation| {
        source
            .0
            .get(usize::from(annotation.locus.span.start())..usize::from(annotation.locus.span.end()))
            .is_some()
    }),
    ensures: |ret| {
    ret.class == diagnostic.detail.class
        && matches!(
            diagnostic.identifier, Maybe::Present(ref identifier) if ret.identifier ==
            identifier.to_string()
        )
        && matches!(
            diagnostic.span, Maybe::Present(span) if source.0.get(usize::from(span.start())
            ..usize::from(span.end())) == Some(ret.locus.as_str())
        )
        && ret.context.len() == diagnostic.annotations.iter().filter(|annotation| annotation.kind == AnnotationKind::Context).count()
},
)]
fn seen(
    source: Text<'_>,
    diagnostic: &Diagnostic,
) -> Seen
{
    let Maybe::Present(ref identifier) = diagnostic.identifier
    else {
        panic!(
            "an attribute misuse names a refusal: {}",
            diagnostic.detail.title
        );
    };
    let Maybe::Present(span) = diagnostic.span
    else {
        panic!(
            "an attribute misuse is located: {}",
            diagnostic.detail.title
        );
    };
    Seen {
        class: diagnostic.detail.class,
        identifier: identifier.to_string(),
        locus: spanned(source, span),

        context: diagnostic
            .annotations
            .iter()
            .filter(|annotation| annotation.kind == AnnotationKind::Context)
            .map(|annotation| spanned(source, annotation.locus.span))
            .collect(),
    }
}

/// The reports a fresh session's submission of `source` prints, under the
/// fixture root.
///
/// # Specification
/// - requires: the source submits under the fixture root and every emitted
///   entry is a named, located refusal with valid source ranges.
/// - ensures: returns the semantic projection of those refusals in emission
///   order. No goal or unsettled-declaration category is returned.
/// - panics: on an invocation fault, ledger line, unnamed report or invalid
///   source range.
///
/// # Adequacy
/// - hypothesis: L3 — the recorded missing, non-value, duplicate, ill-typed and
///   unknown attribute cases, with ordinary type mismatch as the classification
///   control. The category predicate excludes goals and unsettlements; literal
///   field expectations observe the remaining projection without a second
///   pipeline run.
/// - witness: `tests::diag_attr::a_bare_marker_missing_its_payload_is_a_diagnostic`
/// - witness: `tests::diag_attr::a_computation_payload_is_rejected_as_non_value`
/// - witness: `tests::diag_attr::duplicate_single_valued_attribute_is_a_diagnostic`
/// - witness: `tests::diag_attr::an_ill_typed_payload_becomes_an_ordinary_type_error`
/// - witness: `tests::diag_attr::an_unknown_attribute_is_located_at_its_application`
#[spec(
    ensures: |ret| {
    ret.iter().all(|report| matches!(report.class, Class::Refusal(_)))
},
)]
fn reports<'text>(source: impl Into<Text<'text>>) -> Vec<Seen>
{
    let source = source.into();
    let step =
        submit(&mut session(SourceRoot::Fixture), source.0).into_step(Path::new("attribute.gandr"));
    entries(&step, Verb::Check(Goals::Reported))
        .map(|diagnostic| {
            assert_ne!(
                diagnostic.severity,
                Severity::Ledger,
                "a fixture source with no pending refusal prints no line: {}",
                diagnostic.message.text
            );
            seen(source, &diagnostic)
        })
        .collect()
}

/// The one report of `source`'s submission.
///
/// # Specification
/// - requires: the fixture source yields exactly one named and located refusal
///   through reports.
/// - ensures: returns that refusal’s semantic projection; the internal
///   cardinality assertion rejects both missing and extra reports.
/// - panics: when the fixture does not meet that cardinality or reports refuses
///   it.
///
/// # Adequacy
/// - hypothesis: L3 — the recorded one-refusal attribute cases, with each
///   caller comparing the full class, identifier, primary fragment and
///   contextual fragments. The body’s cardinality assertion is the observer for
///   dropped or additional reports; the postcondition checks the returned
///   category.
/// - witness: `tests::diag_attr::a_bare_marker_missing_its_payload_is_a_diagnostic`
/// - witness: `tests::diag_attr::a_computation_payload_is_rejected_as_non_value`
/// - witness: `tests::diag_attr::duplicate_single_valued_attribute_is_a_diagnostic`
/// - witness: `tests::diag_attr::an_ill_typed_payload_becomes_an_ordinary_type_error`
/// - witness: `tests::diag_attr::an_unknown_attribute_is_located_at_its_application`
#[spec(
    ensures: |ret| matches!(ret.class, Class::Refusal(_)),
)]
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
    assert_eq!(only("@[owes(pure 1)]\ndef f : Integer ;\n"), Seen {
        class: Class::Refusal(FailureClass::MalformedSource),
        identifier: String::from("NonValuePayload"),
        locus: String::from("pure 1"),

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
    for (source, locus) in [
        ("@[refuses(42)]\ndef f = 42 ;\n", "42"),
        (
            "@[owes(thunk { return 1 })]\ndef f : Integer ;\n",
            "thunk { return 1 }",
        ),
    ] {
        assert_eq!(
            only(source),
            Seen {
                class: mismatch.class,
                identifier: String::from("IllTypedPayload"),
                locus: String::from(locus),

                context: Vec::new(),
            },
            "{source:?} is refused at its payload, in the class of a type mismatch"
        );
    }
}

#[test]
fn an_unknown_attribute_is_located_at_its_application()
{
    assert_eq!(
        only(
            r#"@[zzzzzzzz(1)]
def f : Integer ;
"#
        ),
        Seen {
            class: Class::Refusal(FailureClass::MalformedSource),
            identifier: String::from("UnknownAttribute"),
            locus: String::from("zzzzzzzz(1)"),
            context: Vec::new(),
        }
    );
}
