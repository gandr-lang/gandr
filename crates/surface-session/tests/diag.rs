//! The diagnostics face of a session: every refusal a declaration of the
//! fragment reaches, identified by its stable refusal name and exact locus.
//! Human-readable report prose is not a compatibility boundary.
//!
//! Each source is submitted to a fresh session under the strict root and its
//! submission turned into the step a face renders; the reports are the ones
//! `gandr check --goals` prints for the same text.

use std::path::Path;

use anodized::spec;
use gandr_surface_corpus::RefusalName;
use gandr_surface_corpus::RefusalSpelling;
use gandr_surface_diagnostics::Entry;
use gandr_surface_diagnostics::entries;
use gandr_surface_diagnostics::report_span;
use gandr_surface_dispatcher::Goals;
use gandr_surface_dispatcher::SourceRoot;
use gandr_surface_dispatcher::Step;
use gandr_surface_dispatcher::Verb;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use quenchant_shape::shape::Maybe;

use crate::common::Text;
use crate::common::session;
use crate::common::submit;

/// One error-corpus row.
///
/// # Specification
/// - requires: the recorded source contains its expected primary locus.
/// - ensures: the fixture pairs a source with a stable refusal category and the
///   exact occurrence responsible for that refusal.
/// - executable: none — The data declaration has no invocation at which to
///   compare the fields. The corpus observer submits each source and compares
///   the resulting identifier and byte span against this independent table.
///
/// # Adequacy
/// - hypothesis: L3 — the thirteen recorded fragment refusals, including three
///   shape-mismatch rules and whole-source refusal; the primary-locus observer
///   catches category changes, missing reports and shifted occurrences.
///   Excluded invocation faults and other suites are named beside the table.
/// - witness: `tests::diag::error_corpus_has_exact_primary_loci`
/// - witness: `tests::diag::repeated_equal_subterms_point_to_the_failing_occurrence`
struct Case
{
    /// The row's name.
    name: &'static str,
    /// The stable refusal category the source must drive.
    identifier: RefusalName,
    /// The source.
    source: &'static str,
    /// The text the report's primary span covers: its last occurrence in the
    /// source.
    locus: &'static str,
}

/// The error corpus: one row per refusal a declaration of the fragment
/// reaches, the checker's shape mismatch once per former its rules require,
/// and the lowering's refusal of a source as a whole.
///
/// Not represented: the attribute refusals, which their own suite drives; the
/// strict root's guard against expectations; a duplicate import alias, which
/// refuses the revision whole and which the session suite drives; a shadowed
/// builtin, refused only under a policy the dispatcher does not set; and the
/// engine faults — an exhausted allowance, a foreign grammar or mold, an
/// unbound index, a dangling node, an admission out of order, a machine
/// invariant — which no lowering of a surface source reaches.
///
/// # Specification
/// - requires: the recorded source contains its expected primary locus.
/// - ensures: the fixture pairs a source with a stable refusal category and the
///   exact occurrence responsible for that refusal.
/// - executable: none — The data declaration has no invocation at which to
///   compare the fields. The corpus observer submits each source and compares
///   the resulting identifier and byte span against this independent table.
///
/// # Adequacy
/// - hypothesis: L3 — the thirteen recorded fragment refusals, including three
///   shape-mismatch rules and whole-source refusal; the primary-locus observer
///   catches category changes, missing reports and shifted occurrences.
///   Excluded invocation faults and other suites are named beside the table.
/// - witness: `tests::diag::error_corpus_has_exact_primary_loci`
/// - witness: `tests::diag::repeated_equal_subterms_point_to_the_failing_occurrence`
const ERROR_CORPUS: [Case; 13] = [
    Case {
        name: "type-mismatch",
        identifier: RefusalName::TypeMismatch,
        source: "def x : String ;\ndef x = 1 ;\n",
        locus: "1",
    },
    Case {
        name: "shape-arrow",
        identifier: RefusalName::ShapeMismatch,
        source: "def h : +U (-F Integer) ;\ndef h = thunk { ret 1 } ;\ndef g : +U (-F Integer) ;\ndef g \
             = thunk { (force h)(1) } ;\n",
        locus: "force h",
    },
    Case {
        name: "shape-thunk",
        identifier: RefusalName::ShapeMismatch,
        source: "def y : +U (-F Integer) ;\ndef y = thunk { force 1 } ;\n",
        locus: "1",
    },
    Case {
        name: "shape-returner",
        identifier: RefusalName::ShapeMismatch,
        source: "def f : +U (Integer -> -F Integer) ;\ndef f = thunk { ret 1 } ;\n",
        locus: "ret 1",
    },
    Case {
        name: "not-synthesisable",
        identifier: RefusalName::NotSynthesisable,
        source: "def a = thunk { ret 1 } ;\n",
        locus: "thunk { ret 1 }",
    },
    Case {
        name: "unknown-constant",
        identifier: RefusalName::UnknownConstant,
        source: "def a = thunk { ret 1 } ;\ndef b = a ;\n",
        locus: "a",
    },
    Case {
        name: "unresolved-name",
        identifier: RefusalName::UnresolvedName,
        source: "def x = nonesuch ;\n",
        locus: "nonesuch",
    },
    Case {
        name: "unresolved-type-head",
        identifier: RefusalName::UnresolvedTypeHead,
        source: "def a : Intgr ;\n",
        locus: "Intgr",
    },
    Case {
        name: "duplicate-signature",
        identifier: RefusalName::DuplicateSignature,
        source: "def a : Integer ;\ndef a : Integer ;\ndef a = 1 ;\n",
        locus: "def a : Integer ;",
    },
    Case {
        name: "duplicate-definition",
        identifier: RefusalName::DuplicateDefinition,
        source: "def a = 3 ;\ndef a = 4 ;\n",
        locus: "def a = 4 ;",
    },
    Case {
        name: "out-of-fragment",
        identifier: RefusalName::OutOfFragment,
        source: "def a : -F Integer & -F Integer ;\n",
        locus: "-F Integer & -F Integer",
    },
    Case {
        name: "malformed-form",
        identifier: RefusalName::MalformedForm,
        source: "def bad = 1 ~ 2 ;\n",
        locus: "~",
    },
    Case {
        name: "refused-whole",
        identifier: RefusalName::OutOfFragment,
        source: "def answer = 42 ;\n#!{echo hello |",
        locus: "#!{echo hello |",
    },
];

/// The step a fresh strict session's submission of `source` becomes, at
/// `path`.
///
/// # Specification
/// - requires: the source submits without an invocation fault.
/// - ensures: returns a strict source step at the supplied path, borrowing the
///   supplied text and carrying its fresh-session composition.
/// - panics: if the fixture’s submission fails.
///
/// # Adequacy
/// - hypothesis: L3 — thirteen named-refusal fixtures and a
///   repeated-equal-literal case, observed by stable identifiers and exact
///   primary source spans. The predicate separately fixes the step variant,
///   root, path and text without submitting twice.
/// - witness: `tests::diag::error_corpus_has_exact_primary_loci`
/// - witness: `tests::diag::repeated_equal_subterms_point_to_the_failing_occurrence`
#[spec(
    ensures: |ret| {
    matches!(
        ret, Step::Source { path : found_path, root : SourceRoot::Strict, text, .. } if
        found_path == path && text.as_ref() == source.0
    )
},
)]
fn step<'text>(
    path: &'text Path,
    source: Text<'text>,
) -> Step<'text>
{
    submit(&mut session(SourceRoot::Strict), source.0).into_step(path)
}

/// The stable identifier and primary span of every named refusal a fresh
/// strict session prints under `check --goals`; unnamed goal reports are
/// omitted.
///
/// # Specification
/// - requires: the source submits without an invocation fault through a strict
///   session.
/// - ensures: preserves each named refusal’s identifier and primary span, in
///   report order, while omitting unnamed goals. Every present span addresses
///   complete source characters.
/// - panics: if submission fails or the strict step emits a fixture ledger
///   line.
///
/// # Adequacy
/// - hypothesis: L3 — thirteen refusal fixtures and two equal literals checked
///   at different types. The table fixes the category and exact failing
///   occurrence independently of report prose; the predicate checks source
///   bounds and character boundaries without rerunning the pipeline.
/// - witness: `tests::diag::error_corpus_has_exact_primary_loci`
/// - witness: `tests::diag::repeated_equal_subterms_point_to_the_failing_occurrence`
#[spec(
    ensures: |ret| {
    ret
        .iter()
        .all(|&(_, span)| match span {
            Maybe::Present(span) => {
                source
                    .0
                    .get(usize::from(span.start())..usize::from(span.end()))
                    .is_some()
            }
            Maybe::Absent(_) => true,
        })
},
)]
fn located(source: Text<'_>) -> Vec<(RefusalSpelling, Maybe<ByteSpan, report_span::Absent>)>
{
    let step = step(Path::new("located.gandr"), source);
    entries(&step, Verb::Check(Goals::Reported))
        .filter_map(|entry| match entry {
            | Entry::Report(report) => match report.identifier() {
                | Maybe::Present(identifier) => Some((identifier, report.span())),
                | Maybe::Absent(_) => None,
            },
            | Entry::Line(line) => panic!("a strict source prints no ledger line: {line}"),
        })
        .collect()
}

#[test]
fn corpus_covers_each_reachable_variant()
{
    for case in &ERROR_CORPUS {
        let got: Vec<RefusalSpelling> = located(Text(case.source))
            .into_iter()
            .map(|(descriptor, _)| descriptor)
            .collect();
        assert!(
            got.iter().any(|found| *found == case.identifier.spelling()),
            "{}: expected a {} report, got {got:?}",
            case.name,
            case.identifier.spelling()
        );
    }
}

#[test]
fn error_corpus_has_exact_primary_loci()
{
    // Every report keeps the smallest surface term or token its refusal
    // justifies as its primary span.
    for case in &ERROR_CORPUS {
        let start = case
            .source
            .rfind(case.locus)
            .expect("the locus is written in the source");
        let end = start
            .checked_add(case.locus.len())
            .expect("the locus ends inside the source");
        let expected = ByteSpan::new(ByteOffset::from(start), ByteOffset::from(end))
            .expect("the locus is ordered");
        let found: Vec<Maybe<ByteSpan, report_span::Absent>> = located(Text(case.source))
            .into_iter()
            .filter(|found| found.0 == case.identifier.spelling())
            .map(|(_, span)| span)
            .collect();
        assert_eq!(
            found,
            [Maybe::Present(expected)],
            "{}: one {} report, at {:?}",
            case.name,
            case.identifier.spelling(),
            case.locus
        );
    }
}

#[test]
fn repeated_equal_subterms_point_to_the_failing_occurrence()
{
    // Equal literals keep their occurrence: the second `1`, the one checked
    // against `String`, is the report's locus.
    const SOURCE: &str = "def a : Integer ;\ndef a = 1 ;\ndef b : String ;\ndef b = 1 ;\n";
    let start = SOURCE.rfind('1').expect("the source writes a `1`");
    let end = start
        .checked_add(1)
        .expect("the literal ends inside the source");
    let expected = ByteSpan::new(ByteOffset::from(start), ByteOffset::from(end))
        .expect("the literal is ordered");
    assert_eq!(located(Text(SOURCE)), [(
        RefusalName::TypeMismatch.spelling(),
        Maybe::Present(expected)
    )]);
}
