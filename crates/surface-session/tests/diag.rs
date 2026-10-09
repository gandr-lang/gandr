//! The diagnostics face of a session: every refusal a declaration of the
//! fragment reaches, reported at its exact locus and rendered as its golden,
//! and the goals beside them.
//!
//! Each source is submitted to a fresh session under the strict root and its
//! submission turned into the step a face renders; the reports are the ones
//! `gandr check --goals` prints for the same text.

use std::path::Path;
use std::path::PathBuf;

use gandr_surface_diagnostics::Entry;
use gandr_surface_diagnostics::RenderStyle;
use gandr_surface_diagnostics::Report;
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
struct Case
{
    /// The row's name.
    name: &'static str,
    /// The report the source must drive: the refusal's name, refined for a
    /// shape mismatch by the former the rule required.
    descriptor: &'static str,
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
const ERROR_CORPUS: [Case; 13] = [
    Case {
        name: "type-mismatch",
        descriptor: "TypeMismatch",
        source: "def x : String ;\ndef x = 1 ;\n",
        locus: "1",
    },
    Case {
        name: "shape-arrow",
        descriptor: "ShapeMismatch:an arrow `A → C`",
        source: "def h : +U (-F Integer) ;\ndef h = thunk { ret 1 } ;\ndef g : +U (-F Integer) ;\ndef g \
                 = thunk { (force h)(1) } ;\n",
        locus: "force h",
    },
    Case {
        name: "shape-thunk",
        descriptor: "ShapeMismatch:a thunk type `+U C`",
        source: "def y : +U (-F Integer) ;\ndef y = thunk { force 1 } ;\n",
        locus: "1",
    },
    Case {
        name: "shape-returner",
        descriptor: "ShapeMismatch:a returner `-F A`",
        source: "def f : +U (Integer -> -F Integer) ;\ndef f = thunk { ret 1 } ;\n",
        locus: "ret 1",
    },
    Case {
        name: "not-synthesisable",
        descriptor: "NotSynthesisable",
        source: "def a = thunk { ret 1 } ;\n",
        locus: "thunk { ret 1 }",
    },
    Case {
        name: "unknown-constant",
        descriptor: "UnknownConstant",
        source: "def a = thunk { ret 1 } ;\ndef b = a ;\n",
        locus: "a",
    },
    Case {
        name: "unresolved-name",
        descriptor: "UnresolvedName",
        source: "def x = nonesuch ;\n",
        locus: "nonesuch",
    },
    Case {
        name: "unresolved-type-head",
        descriptor: "UnresolvedTypeHead",
        source: "def a : Intgr ;\n",
        locus: "Intgr",
    },
    Case {
        name: "duplicate-signature",
        descriptor: "DuplicateSignature",
        source: "def a : Integer ;\ndef a : Integer ;\ndef a = 1 ;\n",
        locus: "def a : Integer ;",
    },
    Case {
        name: "duplicate-definition",
        descriptor: "DuplicateDefinition",
        source: "def a = 3 ;\ndef a = 4 ;\n",
        locus: "def a = 4 ;",
    },
    Case {
        name: "out-of-fragment",
        descriptor: "OutOfFragment",
        source: "def a : Integer * Integer ;\n",
        locus: "Integer * Integer",
    },
    Case {
        name: "malformed-form",
        descriptor: "MalformedForm",
        source: "def bad = 1 ~ 2 ;\n",
        locus: "~",
    },
    Case {
        name: "refused-whole",
        descriptor: "OutOfFragment",
        source: "def answer = 42 ;\n#!{echo hello |",
        locus: "#!{echo hello |",
    },
];

/// The goal corpus, `(name, source)`: a declaration owed at a value type and
/// at a thunk type, and a goal beside a refusal in one source.
///
/// A goal here is a declaration whose body is owed: a hole standing for the
/// whole body. A hole inside a body has no surface yet.
const GOAL_CORPUS: [(&str, &str); 3] = [
    ("goal-value", "def owed : Integer ;\ndef answer = 42 ;\n"),
    (
        "goal-thunk",
        "def later : +U (Integer -> -F Integer) ;\ndef answer = 42 ;\n",
    ),
    (
        "goal-beside-a-refusal",
        "def owed : Integer ;\ndef answer = 42 ;\ndef broken = 1 ~ 2 ;\n",
    ),
];

/// The descriptor of `report`, as [`ERROR_CORPUS`] spells it; a goal is
/// `goal:` and its title.
///
/// # Specification
/// trivial.
fn descriptor(report: &Report<'_>) -> String
{
    let title = report.title().to_string();
    match report.identifier() {
        | Maybe::Present(spelling) => {
            let name = spelling.to_string();
            match title.strip_prefix("the rule here requires ") {
                | Some(required) if name == "ShapeMismatch" => format!("{name}:{required}"),
                | Some(_) | None => name,
            }
        },
        | Maybe::Absent(_) => format!("goal:{title}"),
    }
}

/// The step a fresh strict session's submission of `source` becomes, at
/// `path`.
///
/// # Specification
/// trivial.
fn step<'text>(
    path: &'text Path,
    source: Text<'text>,
) -> Step<'text>
{
    submit(&mut session(SourceRoot::Strict), source.0).into_step(path)
}

/// The descriptor and primary span of every report a fresh strict session's
/// submission of `source` prints under `check --goals`.
///
/// # Specification
/// trivial.
fn located(source: Text<'_>) -> Vec<(String, Maybe<ByteSpan, report_span::Absent>)>
{
    let step = step(Path::new("located.gandr"), source);
    entries(&step, Verb::Check(Goals::Reported))
        .map(|entry| match entry {
            | Entry::Report(report) => (descriptor(&report), report.span()),
            | Entry::Line(line) => panic!("a strict source prints no ledger line: {line}"),
        })
        .collect()
}

/// Every source of `corpus` rendered as `check --goals` prints it, each
/// under a header naming its row, the step at `<name>.gandr`.
///
/// # Specification
/// trivial.
fn rendered<'corpus>(corpus: impl Iterator<Item = (Text<'corpus>, Text<'corpus>)>) -> String
{
    corpus
        .map(|(name, source)| {
            let path = PathBuf::from(format!("{}.gandr", name.0));
            let step = step(&path, source);
            let printed: Vec<String> = entries(&step, Verb::Check(Goals::Reported))
                .map(|entry| match entry {
                    | Entry::Report(report) => report.render(RenderStyle::Plain).to_string(),
                    | Entry::Line(line) => line.to_string(),
                })
                .collect();
            format!("=== {} ===\n{}\n", name.0, printed.join("\n\n"))
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// The error corpus, rendered.
///
/// # Specification
/// trivial.
fn rendered_errors() -> String
{
    rendered(
        ERROR_CORPUS
            .iter()
            .map(|case| (Text(case.name), Text(case.source))),
    )
}

/// The goal corpus, rendered.
///
/// # Specification
/// trivial.
fn rendered_goals() -> String
{
    rendered(
        GOAL_CORPUS
            .iter()
            .map(|&(name, source)| (Text(name), Text(source))),
    )
}

#[test]
fn corpus_covers_each_reachable_variant()
{
    for case in &ERROR_CORPUS {
        let got: Vec<String> = located(Text(case.source))
            .into_iter()
            .map(|(descriptor, _)| descriptor)
            .collect();
        assert!(
            got.iter().any(|found| found == case.descriptor),
            "{}: expected a {} report, got {got:?}",
            case.name,
            case.descriptor
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
            .filter(|found| found.0 == case.descriptor)
            .map(|(_, span)| span)
            .collect();
        assert_eq!(
            found,
            [Maybe::Present(expected)],
            "{}: one {} report, at {:?}",
            case.name,
            case.descriptor,
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
        String::from("TypeMismatch"),
        Maybe::Present(expected)
    )]);
}

#[test]
fn error_corpus_reports_match_goldens()
{
    assert_eq!(
        rendered_errors(),
        include_str!("golden/error-corpus.txt"),
        "the terminal layout of every error-corpus report is a public surface"
    );
}

#[test]
fn goal_corpus_reports_match_goldens()
{
    assert_eq!(
        rendered_goals(),
        include_str!("golden/goal-corpus.txt"),
        "the terminal layout of every goal-corpus report is a public surface"
    );
}
