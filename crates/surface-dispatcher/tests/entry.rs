//! Entry policy through real composition and the walk's fault boundary. Each
//! composition names the run stage's engine, so these tests stand in the
//! `tests` target (#7048).

use core::convert::Infallible;
use core::ops::ControlFlow;
use std::path::Path;
use std::path::PathBuf;

use gandr_core_term::effect::Purity;
use gandr_surface_diagnostics::Class;
use gandr_surface_diagnostics::Lint;
use gandr_surface_diagnostics::Severity;
use gandr_surface_dispatcher::Entries;
use gandr_surface_dispatcher::Goals;
use gandr_surface_dispatcher::Lints;
use gandr_surface_dispatcher::LoweringCount;
use gandr_surface_dispatcher::Pool;
use gandr_surface_dispatcher::Refusals;
use gandr_surface_dispatcher::Repairs;
use gandr_surface_dispatcher::SourceRoot;
use gandr_surface_dispatcher::Standing;
use gandr_surface_dispatcher::Step;
use gandr_surface_dispatcher::Verb;
use gandr_surface_dispatcher::Walk;
use gandr_surface_dispatcher::Width;
use gandr_surface_dispatcher::compose;
use gandr_surface_dispatcher::entries;
use gandr_surface_dispatcher::fixture;
use gandr_surface_dispatcher::fixture::Scratch;
use gandr_surface_evaluate::Evaluator;
use gandr_surface_grammar::built_in;
use gandr_surface_pretty::Spelling;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

/// The step a source at `path` under `root` with `standing` makes.
///
/// # Specification
/// trivial.
fn step<'text>(
    path: &'text Path,
    root: SourceRoot,
    text: SourceText<'text>,
    standing: Standing,
    grammar: &'text gandr_surface_grammar::Pbg,
) -> Step<'text>
{
    Step::Source {
        path,
        root,
        text,
        base: ByteOffset::from(0_usize),
        composed: compose::<Evaluator>(
            grammar,
            root.corpus_root(),
            text,
            &mut LoweringCount::default(),
        )
        .expect("the source composes"),
        standing,
    }
}

#[test]
fn each_verb_prints_its_entries()
{
    let grammar = built_in().expect("the grammar builds");
    let fixture = SourceText::from(include_str!(
        "entry/unformatted/each-verb-prints-its-entries-fixture.gandr"
    ));
    let settled = step(
        Path::new("fixtures/pair.gandr"),
        SourceRoot::Fixture,
        fixture,
        Standing::Settled,
        &grammar,
    );
    let lines: Vec<String> = entries::<Evaluator>(&settled, Verb::Test)
        .map(|diagnostic| {
            assert_eq!(diagnostic.severity, Severity::Ledger);
            diagnostic.message.text
        })
        .collect();
    assert_eq!(
        lines,
        [
            "settled `bad` at 46..65: states refuses UnresolvedName; produced refuses \
              UnresolvedName (malformed source)"
        ],
        "test prints a line for the fixture that states a verdict, and counts the rest"
    );
    assert!(
        entries::<Evaluator>(&settled, Verb::Check(Goals::Gated))
            .next()
            .is_none(),
        "check prints nothing for a settled fixture"
    );

    let strict = SourceText::from("def bad = missing ;\n");
    let refused = step(
        Path::new("bad.gandr"),
        SourceRoot::Strict,
        strict,
        Standing::Unsettled,
        &grammar,
    );
    let printed: Vec<_> = entries::<Evaluator>(&refused, Verb::Check(Goals::Gated)).collect();
    assert_eq!(printed.len(), 1_usize);
    assert_eq!(printed[0].severity, Severity::Error);
    assert!(matches!(printed[0].detail.class, Class::Refusal(_)));
    let start = strict.as_ref().find("missing").expect("the name");
    assert_eq!(
        printed[0].span,
        Maybe::Present(
            ByteSpan::new(ByteOffset::from(start), ByteOffset::from(start + 7_usize))
                .expect("ordered")
        )
    );

    let goal = SourceText::from("def hole : Integer ;\n");
    let owing = step(
        Path::new("owed.gandr"),
        SourceRoot::Strict,
        goal,
        Standing::Unsettled,
        &grammar,
    );
    let goals: Vec<_> = entries::<Evaluator>(&owing, Verb::Check(Goals::Reported))
        .map(|diagnostic| diagnostic.severity)
        .collect();
    assert_eq!(goals, [Severity::Goal]);

    let pending = SourceText::from("def bad = missing ;\n");
    let held = step(
        Path::new("fixtures/pending/held.gandr"),
        SourceRoot::Pending,
        pending,
        Standing::Lowered,
        &grammar,
    );
    let ledger: Vec<_> = entries::<Evaluator>(&held, Verb::Test)
        .map(|diagnostic| (diagnostic.severity, diagnostic.message.text))
        .collect();
    assert_eq!(ledger.first().map(|line| line.0), Some(Severity::Ledger));
    assert!(
        ledger
            .first()
            .is_some_and(|line| line.1.starts_with("unsettled: a pending source")),
        "{ledger:?}"
    );
}

#[test]
fn an_expected_refusal_prints_as_an_unexpected_one_when_every_refusal_is_asked()
{
    let grammar = built_in().expect("the grammar builds");
    let expected = SourceText::from(include_str!(
        "entry/fixtures/each-verb-prints-its-entries-fixture.gandr"
    ));
    let settled = step(
        Path::new("fixtures/pair.gandr"),
        SourceRoot::Fixture,
        expected,
        Standing::Settled,
        &grammar,
    );
    let unexpected = SourceText::from(include_str!(
        "entry/fixtures/an-expected-refusal-prints-as-an-unexpected-one-when-every-refusal-is-asked-unexpected.gandr"
    ));
    let refused = step(
        Path::new("fixtures/pair.gandr"),
        SourceRoot::Strict,
        unexpected,
        Standing::Unsettled,
        &grammar,
    );
    let check = Verb::Check(Goals::Gated);
    assert!(
        entries::<Evaluator>(&settled, check).next().is_none(),
        "check prints no refusal its expectation states"
    );
    for verb in [check, Verb::Test] {
        let every: Vec<_> = entries::<Evaluator>(&settled, verb)
            .refusals(Refusals::Every)
            .map(|diagnostic| (diagnostic.severity, diagnostic.message.text))
            .collect();
        let printed: Vec<_> = entries::<Evaluator>(&refused, check)
            .map(|diagnostic| (diagnostic.severity, diagnostic.message.text))
            .collect();
        assert_eq!(
            every, printed,
            "{verb:?}: the expected refusal prints as the unexpected one does"
        );
    }
}

/// #582: a source laid after its import prints its fixture line at bytes
/// of its own file, the bytes its diagnostic is located at.
#[test]
fn an_importer_s_ledger_line_names_its_own_bytes()
{
    let scratch = Scratch::new(Path::new("ledger-own-bytes"));
    scratch.file(
        Path::new("corpus/fixture/base.gandr"),
        SourceText::from("def one = 1 ;\n"),
    );
    let importer = include_str!(
        "entry/unformatted/an-importer-s-ledger-line-names-its-own-bytes-importer.gandr"
    );
    scratch.file(
        Path::new("corpus/fixture/importer.gandr"),
        SourceText::from(importer),
    );
    let start = importer.find("def bad").expect("the declaration");
    let end = start + "def bad = missing ;".len();
    let own = ByteSpan::new(ByteOffset::from(start), ByteOffset::from(end)).expect("ordered");

    let mut printed = Vec::new();
    let ControlFlow::Continue(_report) =
        Walk::new(vec![scratch.root().join("corpus/fixture/importer.gandr")])
            .visit::<Evaluator, _, _>(
                &Pool::new(Width::SERIAL),
                |step| -> ControlFlow<Infallible> {
                    printed.extend(
                        entries::<Evaluator>(&step, Verb::Test)
                            .map(|diagnostic| (diagnostic.message.text, diagnostic.span)),
                    );
                    ControlFlow::Continue(())
                },
            );
    assert_eq!(
        printed,
        [(
            format!(
                "settled `bad` at {start}..{end}: states refuses UnresolvedName; produced \
                     refuses UnresolvedName (malformed source)"
            ),
            Maybe::Present(own)
        )],
        "the line names the bytes of the importer's own file, where its diagnostic stands"
    );
}

#[test]
fn a_shadowed_builtin_is_warned_of_under_check_alone()
{
    let grammar = built_in().expect("the grammar builds");
    let text = SourceText::from(include_str!(
        "entry/unformatted/a-shadowed-builtin-is-warned-of-under-check-alone.gandr"
    ));
    let shadowing = step(
        Path::new("shadow.gandr"),
        SourceRoot::Strict,
        text,
        Standing::Settled,
        &grammar,
    );
    let warned: Vec<_> = entries::<Evaluator>(&shadowing, Verb::Check(Goals::Gated))
        .map(|diagnostic| (diagnostic.severity, diagnostic.span))
        .collect();
    assert_eq!(warned, [(
        Severity::Warning,
        Maybe::Present(
            ByteSpan::new(ByteOffset::from(4_usize), ByteOffset::from(7_usize)).expect("ordered")
        )
    )]);
    assert!(
        entries::<Evaluator>(&shadowing, Verb::Test)
            .next()
            .is_none()
    );
}

#[test]
fn each_use_of_a_deprecated_declaration_is_a_finding()
{
    let grammar = built_in().expect("the grammar builds");
    let written = include_str!(
        "entry/unformatted/each-use-of-a-deprecated-declaration-is-a-finding-written.gandr"
    );
    let text = SourceText::from(written);
    let at = |needle: &str, length: usize| {
        let start = written.find(needle).expect("written").saturating_add(2);
        Maybe::Present(
            ByteSpan::new(
                ByteOffset::from(start),
                ByteOffset::from(start.saturating_add(length)),
            )
            .expect("ordered"),
        )
    };
    let source = step(
        Path::new("deprecated.gandr"),
        SourceRoot::Strict,
        text,
        Standing::Unsettled,
        &grammar,
    );
    assert_eq!(
        entries::<Evaluator>(&source, Verb::Check(Goals::Gated))
            .map(|diagnostic| (diagnostic.detail.class, diagnostic.span))
            .collect::<Vec<_>>(),
        [
            (
                Class::Warning,
                Maybe::Present(
                    ByteSpan::new(ByteOffset::from(4_usize), ByteOffset::from(7_usize))
                        .expect("ordered")
                )
            ),
            (Class::Lint(Lint::Deprecated), at("= add", 3)),
            (
                Class::Refusal(gandr_core_term::FailureClass::MalformedSource),
                at("= missing", 7)
            ),
        ],
        "with no lint enabled, the use is a finding after the warnings and before the \
             declarations"
    );
    assert!(
        entries::<Evaluator>(&source, Verb::Test)
            .all(|diagnostic| diagnostic.severity != Severity::Warning),
        "`test` prints settlements alone"
    );
}

#[test]
fn a_declaration_naming_a_refused_one_is_a_note()
{
    let grammar = built_in().expect("the grammar builds");
    let text = SourceText::from(include_str!(
        "entry/fixtures/a-declaration-naming-a-refused-one-is-a-note.gandr"
    ));
    let cascade = step(
        Path::new("cascade.gandr"),
        SourceRoot::Strict,
        text,
        Standing::Unsettled,
        &grammar,
    );
    let at = |needle: &str, from: usize| {
        let start = text
            .as_ref()
            .get(from ..)
            .and_then(|rest| rest.find(needle))
            .expect("the needle")
            .saturating_add(from);
        Maybe::Present(
            ByteSpan::new(
                ByteOffset::from(start),
                ByteOffset::from(start.saturating_add(1)),
            )
            .expect("ordered"),
        )
    };
    let body = text.as_ref().find("return a ()").expect("the call");
    assert_eq!(
        entries::<Evaluator>(&cascade, Verb::Check(Goals::Gated))
            .map(|diagnostic| (diagnostic.severity, diagnostic.span))
            .collect::<Vec<_>>(),
        [
            (Severity::Error, at("^", 0)),
            (Severity::Note, at("a ()", body))
        ],
        "the refused declaration is the one error; the one calling it is a note at the call, \
             and the one calling a declaration that checks prints nothing"
    );
}

/// A signature whose definition is written with its keyword misspelt owes
/// its body because the lowering refused that form: it is a note, and the
/// first error is the misspelt keyword (#2339). A signature beside no
/// refused form of its name stays an error.
#[test]
fn a_declaration_whose_other_half_is_refused_is_a_note_2339()
{
    let grammar = built_in().expect("the grammar builds");
    let written = include_str!(
        "entry/unformatted/a-declaration-whose-other-half-is-refused-is-a-note-2339-written.gandr"
    );
    let unread = step(
        Path::new("unread.gandr"),
        SourceRoot::Strict,
        SourceText::from(written),
        Standing::Unsettled,
        &grammar,
    );
    let printed: Vec<_> = entries::<Evaluator>(&unread, Verb::Check(Goals::Gated))
        .map(|diagnostic| {
            (
                diagnostic.severity,
                diagnostic.span,
                diagnostic.message.text,
            )
        })
        .collect();
    let signature = written.find("def pair :").expect("the signature");
    assert!(
        printed
            .iter()
            .any(|&(severity, span, _)| severity == Severity::Note
                && matches!(span, Maybe::Present(span) if usize::from(span.start()) == signature)),
        "the signature is a note: {printed:?}"
    );
    let first = printed
        .iter()
        .find(|&&(severity, ..)| severity == Severity::Error)
        .map(|&(_, span, _)| span);
    let at = written.find("de pair").expect("the definition");
    assert!(
        matches!(first, Some(Maybe::Present(span)) if usize::from(span.start()) == at),
        "the first error is the misspelt keyword: {printed:?}"
    );
    let text = SourceText::from(include_str!(
        "entry/unformatted/a-declaration-whose-other-half-is-refused-is-a-note-2339.gandr"
    ));
    let lone = step(
        Path::new("lone.gandr"),
        SourceRoot::Strict,
        text,
        Standing::Unsettled,
        &grammar,
    );
    assert_eq!(
        entries::<Evaluator>(&lone, Verb::Check(Goals::Gated))
            .map(|diagnostic| diagnostic.severity)
            .collect::<Vec<_>>(),
        [Severity::Error],
        "a signature owing its body beside no refused form is its own error"
    );
}

/// A declaration whose keyword is misspelt reads as a stray word and a
/// declaration that owes its keyword at its name (#5199). The declaration
/// admitted before it, calling the name the misspelling took out of scope,
/// is refused because of it. Under `check` the refusals of form print
/// first, so the first error is the misspelt keyword, and the call resting
/// on them follows (#2875).
#[test]
fn a_refusal_of_form_prints_before_one_resting_on_it_2875()
{
    let grammar = built_in().expect("the grammar builds");
    let written = include_str!(
        "entry/unformatted/a-refusal-of-form-prints-before-one-resting-on-it-2875-written.gandr"
    );
    let misspelt = step(
        Path::new("misspelt.gandr"),
        SourceRoot::Strict,
        SourceText::from(written),
        Standing::Unsettled,
        &grammar,
    );
    let at = |needle: &str| written.find(needle).expect("the needle");
    assert_eq!(
        entries::<Evaluator>(&misspelt, Verb::Check(Goals::Gated))
            .filter(|diagnostic| diagnostic.severity == Severity::Error)
            .map(|diagnostic| match diagnostic.span {
                Maybe::Present(span) => usize::from(span.start()),
                Maybe::Absent(_) => usize::MAX,
            })
            .collect::<Vec<_>>(),
        [at("de g"), at("g() ->"), at("g ()")],
        "the refusals of form print first in admission order, then the unresolved call \
             admitted before them"
    );
}

/// The note of a declaration calling a refused one names the declaration
/// it calls, not another the lowering refused before it.
#[test]
fn a_note_names_the_refused_declaration_it_rests_on()
{
    let grammar = built_in().expect("the grammar builds");
    let text = SourceText::from(include_str!(
        "entry/fixtures/a-note-names-the-refused-declaration-it-rests-on.gandr"
    ));
    let cascade = step(
        Path::new("named.gandr"),
        SourceRoot::Strict,
        text,
        Standing::Unsettled,
        &grammar,
    );
    let notes: Vec<String> = entries::<Evaluator>(&cascade, Verb::Check(Goals::Gated))
        .filter(|diagnostic| diagnostic.severity == Severity::Note)
        .filter_map(|diagnostic| match diagnostic.note {
            Maybe::Present(note) => Some(note),
            Maybe::Absent(_) => None,
        })
        .collect();
    assert!(
        matches!(notes.as_slice(), [note] if note.contains("`x`") && !note.contains("`a`")),
        "one note, naming `x`, the declaration `b` calls: {notes:?}"
    );
}

#[test]
fn a_rules_refusal_reads_its_parting_pair_and_no_other_refusal_does()
{
    let grammar = built_in().expect("the grammar builds");
    let text = SourceText::from(include_str!(
        "entry/fixtures/a-rules-refusal-reads-its-parting-pair-and-no-other-refusal-does.gandr"
    ));
    let Ok(gandr_surface_dispatcher::Composed::Settled {
        ref report,
        ref parted,
        ..
    }) = compose::<Evaluator>(
        &grammar,
        SourceRoot::Strict.corpus_root(),
        text,
        &mut LoweringCount::default(),
    )
    else {
        panic!("the source settles");
    };
    let refusals: Vec<gandr_surface_corpus::Refusal<'_>> = report
        .declarations()
        .iter()
        .filter_map(|declaration| match declaration.produced().refusal() {
            Maybe::Present(refusal) => Some(refusal),
            Maybe::Absent(_) => None,
        })
        .collect();
    let [
        diverging @ gandr_surface_corpus::Refusal::Lowering(
            gandr_surface_lowering::LoweringRefusal::RulesDiverge { span, first },
        ),
        unresolved,
    ] = *refusals.as_slice()
    else {
        panic!("the block diverges and the name is unresolved: {refusals:?}");
    };
    let Maybe::Present(pair) = fixture::obstruction(diverging, parted)
    else {
        panic!("the divergent block reads its pair");
    };
    assert_eq!(
        (pair.cells.later, pair.cells.earlier),
        (span, first),
        "the later rule, then the earlier one"
    );
    assert_eq!(
        [
            pair.cells.peak.to_string(),
            pair.witness.earlier.to_string(),
            pair.witness.later.to_string(),
        ],
        ["add(Zero, Zero)", "Zero", "Succ(Zero)"],
        "the peak, then the earlier rule's normal form, then the later one's"
    );
    assert!(
        matches!(
            fixture::obstruction(unresolved, parted),
            Maybe::Absent(gandr_surface_diagnostics::obstructed::Absent::Unparted)
        ),
        "an unresolved name holds no parting pair"
    );
    assert!(
        matches!(
            fixture::obstruction(diverging, &[]),
            Maybe::Absent(gandr_surface_diagnostics::obstructed::Absent::Unparted)
        ),
        "a divergent refusal reads no pair the composition does not hold"
    );
}

/// #782: a refusal names the types it compares in the spelling its
/// entries are asked for, Unicode unless asked otherwise.
#[test]
fn a_refusal_names_its_types_in_the_spelling_asked_782()
{
    let grammar = built_in().expect("the grammar builds");
    let refused = step(
        Path::new("relation.gandr"),
        SourceRoot::Strict,
        SourceText::from(include_str!(
            "entry/unformatted/a-refusal-names-its-types-in-the-spelling-asked-782-refused.gandr"
        )),
        Standing::Unsettled,
        &grammar,
    );
    let compared = |printed: Entries<'_, Evaluator>| {
        printed
            .map(|diagnostic| diagnostic.detail.compared.to_string())
            .collect::<Vec<_>>()
    };
    let expected = |relation: &str| [format!("expected `{relation}`, found `Integer`")];
    assert_eq!(
        compared(entries::<Evaluator>(&refused, Verb::Check(Goals::Gated))),
        expected("Integer ≃ String"),
        "Unicode by default"
    );
    assert_eq!(
        compared(
            entries::<Evaluator>(&refused, Verb::Check(Goals::Gated)).spelling(Spelling::Ascii)
        ),
        expected("Integer <~> String"),
        "ASCII when asked"
    );
}

#[test]
fn an_inferred_exit_is_reported_where_a_lint_reaches()
{
    let grammar = built_in().expect("the grammar builds");
    let text = SourceText::from(include_str!(
        "entry/unformatted/an-inferred-exit-is-reported-where-a-lint-reaches.gandr"
    ));
    let at = |start: usize| {
        Maybe::Present(
            ByteSpan::new(
                ByteOffset::from(start),
                ByteOffset::from(start.saturating_add(1_usize)),
            )
            .expect("ordered"),
        )
    };
    let shadowed = Maybe::Present(
        ByteSpan::new(ByteOffset::from(4_usize), ByteOffset::from(7_usize)).expect("ordered"),
    );
    let asked = at(text
        .as_ref()
        .find("{ n }")
        .expect("asked")
        .saturating_add(2_usize));
    let unasked = at(text
        .as_ref()
        .rfind("{ n }")
        .expect("unasked")
        .saturating_add(2_usize));
    let finding = |diagnostic: gandr_surface_diagnostics::Diagnostic| {
        (diagnostic.detail.class, diagnostic.span)
    };
    let lint = Class::Lint(Lint::ExplicitExits);
    let source = step(
        Path::new("exits.gandr"),
        SourceRoot::Strict,
        text,
        Standing::Settled,
        &grammar,
    );
    assert_eq!(
        entries::<Evaluator>(&source, Verb::Check(Goals::Gated))
            .map(finding)
            .collect::<Vec<_>>(),
        [(Class::Warning, shadowed), (lint, asked)],
        "by default a lint reaches the forms its attribute marks, after the warnings"
    );
    assert_eq!(
        entries::<Evaluator>(&source, Verb::Check(Goals::Reported))
            .linting(Lints::enabling([Lint::ExplicitExits]))
            .map(finding)
            .collect::<Vec<_>>(),
        [(Class::Warning, shadowed), (lint, asked), (lint, unasked)],
        "a lint the run enables reaches every inferred exit, in source order"
    );
    assert!(
        entries::<Evaluator>(&source, Verb::Test)
            .linting(Lints::enabling([Lint::ExplicitExits]))
            .next()
            .is_none(),
        "`test` prints settlements alone"
    );
}

#[test]
fn an_inferred_run_is_reported_where_a_lint_reaches()
{
    let grammar = built_in().expect("the grammar builds");
    let text = SourceText::from(include_str!(
        "entry/fixtures/an-inferred-run-is-reported-where-a-lint-reaches.gandr"
    ));
    let nested = |declaration: &str| {
        let context = text.as_ref().find(declaration).expect("declared");
        let start = text
            .as_ref()
            .get(context ..)
            .and_then(|rest| rest.find("{ id (id n) }"))
            .expect("nested")
            .saturating_add(context)
            .saturating_add(6_usize);
        Maybe::Present(
            ByteSpan::new(
                ByteOffset::from(start),
                ByteOffset::from(start.saturating_add(4_usize)),
            )
            .expect("ordered"),
        )
    };
    let (effects, every, unasked) = (
        nested("def effects"),
        nested("def every"),
        nested("def unasked"),
    );
    let finding = |diagnostic: gandr_surface_diagnostics::Diagnostic| {
        (diagnostic.detail.class, diagnostic.span)
    };
    let lint = Class::Lint(Lint::ExplicitRuns);
    let mut source = step(
        Path::new("runs.gandr"),
        SourceRoot::Strict,
        text,
        Standing::Settled,
        &grammar,
    );
    assert_eq!(
        entries::<Evaluator>(&source, Verb::Check(Goals::Gated))
            .map(finding)
            .collect::<Vec<_>>(),
        [(lint, every)],
        "by default the lint reaches the forms its attribute marks, and the `effects` option \
             leaves a pure run silent"
    );
    assert_eq!(
        entries::<Evaluator>(&source, Verb::Check(Goals::Gated))
            .linting(Lints::enabling([Lint::ExplicitRuns]))
            .map(finding)
            .collect::<Vec<_>>(),
        [(lint, effects), (lint, every), (lint, unasked)],
        "the lint the run enables reaches every inferred run, in source order"
    );
    // The lowering reads no effect rows yet, so a surface source cannot
    // perform one; the run the checker decided for `unasked` is marked
    // effectful here, which is what an effectful returner decides.
    if let Step::Source {
        composed: gandr_surface_dispatcher::Composed::Settled { ref mut runs, .. },
        ..
    } = source
    {
        for run in runs.iter_mut() {
            if Maybe::Present(run.span) == unasked {
                run.purity = Purity::Effectful;
            }
        }
    }
    assert_eq!(
        entries::<Evaluator>(&source, Verb::Check(Goals::Gated))
            .linting(Lints::default().asking_effects())
            .map(finding)
            .collect::<Vec<_>>(),
        [(lint, every), (lint, unasked)],
        "under the run's `effects` option an effectful run is a finding everywhere, and a \
             pure one only where an attribute asks for every run"
    );
    assert!(
        entries::<Evaluator>(&source, Verb::Test)
            .linting(Lints::enabling([Lint::ExplicitRuns]))
            .next()
            .is_none(),
        "`test` prints settlements alone"
    );
}

#[test]
fn a_second_run_refusal_is_located_where_its_bound_spelling_is_380()
{
    let grammar = built_in().expect("the grammar builds");
    let data = include_str!(
        "entry/unformatted/a-second-run-refusal-is-located-where-its-bound-spelling-is-380-data.gandr"
    );
    let fold = |arm: &str| {
        format!(
            "{data}def rec tell(n : Int) -> -F Int {{\n  match n {{\n    | Z => Z\n    | S(x) => \
                 {arm}\n    | P(x) => {arm}\n  }}\n}}\n"
        )
    };
    // The nested call is judged by the second run, over the bind the
    // first run elaborated it to; the bound twin by the first run alone.
    for written in [fold("S (tell[<] x)"), fold("{ let t = tell[<] x; S t }")] {
        let text = SourceText::from(written.as_str());
        let start = written.find("match n").expect("the match");
        let end = written.rfind("  }\n}").expect("the case's close") + "  }".len();
        let case = Maybe::Present(
            ByteSpan::new(ByteOffset::from(start), ByteOffset::from(end)).expect("ordered"),
        );
        let fold = step(
            Path::new("fold.gandr"),
            SourceRoot::Strict,
            text,
            Standing::Unsettled,
            &grammar,
        );
        assert_eq!(
            entries::<Evaluator>(&fold, Verb::Check(Goals::Gated))
                .map(|diagnostic| {
                    let code = diagnostic.identifier.map(|code| code.to_string());
                    (diagnostic.severity, code, diagnostic.span)
                })
                .collect::<Vec<_>>(),
            [(
                Severity::Error,
                Maybe::Present(String::from("RuleNotRespected")),
                case
            )],
            "the fold is refused at the case block whichever run judged it:\n{written}"
        );
    }
}

#[test]
fn counted_declarations_preserve_visible_order_and_exhaustion()
{
    let text = SourceText::from(include_str!(
        "entry/fixtures/counted-declarations-preserve-visible-order-and-exhaustion.gandr"
    ));
    let grammar = built_in().expect("the grammar builds");
    let step = step(
        Path::new("ordered.gandr"),
        SourceRoot::Strict,
        text,
        Standing::Unsettled,
        &grammar,
    );
    let expected = [
        text.as_ref().find("missing").expect("the first refusal"),
        text.as_ref().rfind("missing").expect("the last refusal"),
    ]
    .map(|start| {
        Maybe::Present(
            ByteSpan::new(
                ByteOffset::from(start),
                ByteOffset::from(start + "missing".len()),
            )
            .expect("an ordered ASCII token"),
        )
    });
    let mut stream = entries::<Evaluator>(&step, Verb::Check(Goals::Gated));
    let actual = stream
        .by_ref()
        .map(|diagnostic| {
            assert_ne!(
                diagnostic.severity,
                Severity::Ledger,
                "strict counted declarations are not ledger lines"
            );
            diagnostic.span
        })
        .collect::<Vec<_>>();
    assert_eq!(actual.as_slice(), &expected);
    assert!(
        stream.next().is_none(),
        "exhaustion cannot resurrect a skipped declaration"
    );
}

#[test]
fn faults_and_empty_sources_stay_exhausted()
{
    let verbs = [
        Verb::Check(Goals::Gated),
        Verb::Check(Goals::Reported),
        Verb::Test,
    ];
    let exhausted = |step: &Step<'_>| {
        for verb in verbs {
            let mut stream = entries::<Evaluator>(step, verb);
            assert!(stream.next().is_none());
            assert!(
                stream.next().is_none(),
                "an exhausted stream stays exhausted"
            );
        }
    };
    let faulted = Walk::new(vec![PathBuf::new()]).visit::<Evaluator, _, _>(
        &Pool::new(Width::SERIAL),
        |fault| {
            assert!(
                matches!(fault, Step::Fault { .. }),
                "an empty path is a fault, not an empty walk"
            );
            exhausted(&fault);
            ControlFlow::Break(())
        },
    );
    assert_eq!(faulted, ControlFlow::Break(()), "the fault is handed over");
    let text = SourceText::from("");
    let grammar = built_in().expect("the grammar builds");
    exhausted(&step(
        Path::new("empty.gandr"),
        SourceRoot::Strict,
        text,
        Standing::Unsettled,
        &grammar,
    ));
}

/// #5474: a refusal proposes its repair as its fix only once the source
/// the repair writes settles the declaration, and only when its entries
/// check repairs. The list is the corpus's, with the `,` its line 44
/// writes deleted.
#[test]
fn a_repair_is_proposed_as_a_fix_once_it_checks_5474()
{
    let scratch = Scratch::new(Path::new("checked-repair"));
    let listed = include_str!("../../../corpus/model/builtins/list-patterns.gandr").replacen(
        "  shortLength (#[7, 8])\n",
        "  shortLength (#[7 8])\n",
        1,
    );
    let sources = [
        (
            "laid.gandr",
            include_str!(
                "entry/unformatted/a-repair-is-proposed-as-a-fix-once-it-checks-5474-sources.gandr"
            ),
        ),
        ("corpus/model/builtins/list-patterns.gandr", listed.as_str()),
    ];
    for (name, text) in sources {
        scratch.file(Path::new(name), SourceText::from(text));
    }
    let fixes = |repairs: Repairs| {
        let mut printed = Vec::new();
        let ControlFlow::Continue(_report) = Walk::new(
            sources
                .iter()
                .map(|&(name, _)| scratch.root().join(name))
                .collect(),
        )
        .visit::<Evaluator, _, _>(
            &Pool::new(Width::SERIAL),
            |step| -> ControlFlow<Infallible> {
                printed.extend(
                    entries::<Evaluator>(&step, Verb::Check(Goals::Gated))
                        .repairing(repairs)
                        .map(|diagnostic| {
                            (
                                diagnostic.path.file_name().map(PathBuf::from),
                                matches!(diagnostic.repair, Maybe::Present(_)),
                                match diagnostic.fix {
                                    Maybe::Present(fix) => Some(fix.replacement),
                                    Maybe::Absent(_) => None,
                                },
                            )
                        }),
                );
                ControlFlow::Continue(())
            },
        );
        printed.sort();
        printed
    };
    let named =
        |name: &str, fix: Option<&str>| (Some(PathBuf::from(name)), true, fix.map(String::from));
    assert_eq!(
        fixes(Repairs::Checked),
        [
            named("laid.gandr", None),
            named("list-patterns.gandr", Some(","))
        ],
        "the `,` settles the list and is proposed; the moved line still refuses, so it is \
             named alone"
    );
    assert_eq!(
        fixes(Repairs::Named),
        [
            named("laid.gandr", None),
            named("list-patterns.gandr", None)
        ],
        "entries that check no repair name each and propose none"
    );
}
