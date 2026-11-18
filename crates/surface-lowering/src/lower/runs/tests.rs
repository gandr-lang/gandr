use alloc::format;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_checker::ModuleReport;
use gandr_core_checker::Nesting;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_core_term::effect::Purity;
use gandr_surface_syntax::SourceText;

use super::AskedRuns;
use super::InferredRun;
use super::LinearRun;
use super::NestedSite;
use super::RunOperand;
use super::RunSpelling;
use crate::attribute::AttributeSchema;
use crate::attribute::PayloadForm;
use crate::attribute::RegisteredAttribute;
use crate::error::LoweringRefusal;
use crate::lower::exits::tests::spelled_within;
use crate::lower::native::tests::assert_accepted;
use crate::lower::native::tests::judged;
use crate::lower::native::tests::lowered;
use crate::lower::native::tests::refusal_of;
use crate::resolve::SurfaceName;

/// The naturals every witness builds on, and a function to nest.
const NAT: &str = include_str!("tests/unformatted/nat.gandr");

#[test]
fn an_explicit_runs_attribute_asks_within_its_form()
{
    let source = format!(
        include_str!("tests/unformatted/an-explicit-runs-attribute-asks-within-its-form.gandr"),
        NAT = NAT
    );
    let text = SourceText::from(source.as_str());
    let mut arena = CoreArena::new();
    let module = lowered(text, &mut arena);
    let report = judged(&module, &mut arena);
    assert_accepted(&report);
    let at = |context: &str, needle: &str| {
        spelled_within(text, SourceText::from(context), SourceText::from(needle))
    };
    let inferred = |span, asked| InferredRun {
        span,
        purity: Purity::Pure,
        site: NestedSite {
            asked,
            spelling: RunSpelling::Bare,
            operand: RunOperand::Tight,
        },
    };
    assert_eq!(
        module.inferred_runs(ran(&report)),
        [
            inferred(at("{ Succ (twice n) }", "twice n"), AskedRuns::Every),
            inferred(
                at("{ Succ (twice (Succ n)) }", "twice (Succ n)"),
                AskedRuns::Every
            ),
            inferred(
                at("{ Succ (twice Zero) }", "twice Zero"),
                AskedRuns::Effectful
            ),
            inferred(
                at("{ Succ (twice (Succ Zero)) }", "twice (Succ Zero)"),
                AskedRuns::Unasked
            ),
        ],
        "a module's attribute asks for its members' runs, a declaration's for its own and the \
         wider of two for a member asked both ways; a written run is no inferred one, and a \
         refused declaration lists none"
    );
    assert_eq!(
        refusal_of(&module, SurfaceName::from("misspelled")),
        LoweringRefusal::IllTypedPayload {
            span: at("explicit_runs(\"effect\")", "\"effect\""),
            name: RegisteredAttribute::EXPLICIT_RUNS,
            expected: AttributeSchema::MarkerOr("effects"),
            written: PayloadForm::OtherText,
        },
        "a text spelling no option is refused at the payload"
    );
}

#[test]
fn a_nested_run_is_spelled_as_its_written_run_reads_back()
{
    let text = SourceText::from(include_str!(
        "tests/fixtures/a-nested-run-is-spelled-as-its-written-run-reads-back.gandr"
    ));
    let mut arena = CoreArena::new();
    let module = lowered(text, &mut arena);
    let report = judged(&module, &mut arena);
    assert_accepted(&report);
    let at = |context: &str, needle: &str| {
        spelled_within(text, SourceText::from(context), SourceText::from(needle))
    };
    let site = |spelling, operand| NestedSite {
        asked: AskedRuns::Unasked,
        spelling,
        operand,
    };
    assert_eq!(
        module
            .inferred_runs(ran(&report))
            .into_iter()
            .map(|run| (run.span, run.site))
            .collect::<Vec<_>>(),
        [
            (
                at("{ return id n }", "id n"),
                site(RunSpelling::Bare, RunOperand::Tight)
            ),
            (
                at("{ id n + 1 }", "id n"),
                site(RunSpelling::Bare, RunOperand::Tight)
            ),
            (
                at("{ return n + 1 }", "n + 1"),
                site(RunSpelling::Bare, RunOperand::Grouped)
            ),
        ],
        "a call after `return` and one that begins a block's tail are spelled bare, and an \
         operator call is grouped after `run`"
    );
    let written = SourceText::from(include_str!(
        "tests/fixtures/a-nested-run-is-spelled-as-its-written-run-reads-back-written.gandr"
    ));
    let mut rewritten = CoreArena::new();
    let fixed = lowered(written, &mut rewritten);
    let rechecked = judged(&fixed, &mut rewritten);
    assert_accepted(&rechecked);
    assert_eq!(
        fixed.inferred_runs(ran(&rechecked)),
        [],
        "each run written as its site spells it reads back as the written run of the whole \
         computation, so the checker infers none"
    );
}

/// A call written where a function is read runs when it returns one, and is
/// spelled grouped, since `run f(n)(1)` reads as the run of the whole
/// application; a curried call there stays in place (#3935).
#[test]
fn a_call_returning_a_function_runs_where_it_is_applied_3935()
{
    let text = SourceText::from(include_str!(
        "tests/fixtures/a-call-returning-a-function-runs-where-it-is-applied-3935.gandr"
    ));
    let mut arena = CoreArena::new();
    let module = lowered(text, &mut arena);
    let report = judged(&module, &mut arena);
    assert_accepted(&report);
    let at = |context: &str, needle: &str| {
        spelled_within(text, SourceText::from(context), SourceText::from(needle))
    };
    let site = NestedSite {
        asked: AskedRuns::Unasked,
        spelling: RunSpelling::Parenthesised,
        operand: RunOperand::Tight,
    };
    assert_eq!(
        module
            .inferred_runs(ran(&report))
            .into_iter()
            .map(|run| (run.span, run.site))
            .collect::<Vec<_>>(),
        [
            (at("let h = (plus n) 1", "plus n"), site),
            (at("{ (dependent A) x }", "dependent A"), site),
        ],
        "a head call returning a function runs, spelled grouped where a bound statement \
         reads it as at a tail's start; a curried call runs nothing"
    );
    let written = SourceText::from(include_str!(
        "tests/fixtures/a-call-returning-a-function-runs-where-it-is-applied-3935-written.gandr"
    ));
    let mut rewritten = CoreArena::new();
    let fixed = lowered(written, &mut rewritten);
    let rechecked = judged(&fixed, &mut rewritten);
    assert_accepted(&rechecked);
    assert_eq!(
        fixed.inferred_runs(ran(&rechecked)),
        [],
        "each head run written as its site spells it reads back, so the checker infers none"
    );
}

#[test]
fn a_run_read_once_first_is_linear()
{
    let source = format!(
        include_str!("tests/unformatted/a-run-read-once-first-is-linear.gandr"),
        NAT = NAT
    );
    let text = SourceText::from(source.as_str());
    let mut arena = CoreArena::new();
    let module = lowered(text, &mut arena);
    assert_accepted(&judged(&module, &mut arena));
    let at = |context: &str, needle: &str| {
        spelled_within(text, SourceText::from(context), SourceText::from(needle))
    };
    let linear = |bound: (&str, &str), read: (&str, &str)| LinearRun {
        bound: at(bound.0, bound.1),
        read: at(read.0, read.1),
    };
    assert_eq!(
        module.linear_runs(),
        [
            linear(("let m = twice n", "twice n"), ("Succ m }", "m")),
            linear(("let b = twice a", "twice a"), ("twice b }", "b")),
            linear(("let c = twice n", "twice n"), ("d c (", "c")),
            linear(("let h = twice g", "twice g"), ("g h }", "h")),
            linear(("let p = twice n", "twice n"), ("second p", "p")),
            linear(("let q = twice Zero", "twice Zero"), ("p q }", "q")),
            linear(("let s = twice Zero", "twice Zero"), ("s r }", "s")),
        ],
        "the runs ending a block whose binders its tail reads once each, first and in their \
         order, are linear, a chain's last link, one before a later run and a pair among them; \
         one read in a later statement, out of order, twice, after another run, as the tail's \
         whole value or under `explicit_runs` is not"
    );
}

/// A run in a match's branch, whose statements the branch's copies each
/// hold, is linear where every copy reads it once and first, as it is
/// outside a match (#1935).
#[test]
fn a_run_in_a_match_branch_is_linear_1935()
{
    let source = format!(
        include_str!("tests/unformatted/a-run-in-a-match-branch-is-linear-1935.gandr"),
        NAT = NAT
    );
    let text = SourceText::from(source.as_str());
    let mut arena = CoreArena::new();
    let module = lowered(text, &mut arena);
    assert_accepted(&judged(&module, &mut arena));
    let at = |context: &str, needle: &str| {
        spelled_within(text, SourceText::from(context), SourceText::from(needle))
    };
    let linear = |bound: (&str, &str), read: (&str, &str)| LinearRun {
        bound: at(bound.0, bound.1),
        read: at(read.0, read.1),
    };
    assert_eq!(
        module.linear_runs(),
        [
            linear(("let d = twice b", "twice b"), ("Succ d }", "d")),
            linear(("let f = twice e", "twice e"), ("Succ f }", "f")),
        ],
        "a branch's run read once and first is linear, a chain's last link among them; one \
         read twice is not"
    );
}

/// The nested values the checker decided to run in `report`'s elaborated
/// bodies, with the purity of each.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one pair per run decision of every elaboration; a suspension
///   gives none.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the runs witnesses join exactly these decisions with the
///   lowering's record.
/// - witness: `lower::runs::tests::an_explicit_runs_attribute_asks_within_its_form`
/// - witness: `lower::runs::tests::a_nested_run_is_spelled_as_its_written_run_reads_back`
#[spec(ensures: |ret| ret.len() == report.nested_elaborations().values().map(|elaboration| elaboration.decisions().values().filter(|decided| matches!(decided, Nesting::Ran(_) | Nesting::Returned)).count()).sum::<usize>())]
fn ran(report: &ModuleReport) -> Vec<(ValueId, Purity)>
{
    report
        .nested_elaborations()
        .values()
        .flat_map(|elaboration| {
            elaboration
                .decisions()
                .iter()
                .filter_map(|(&at, &decided)| match decided {
                    Nesting::Ran(purity) => Some((at, purity)),
                    Nesting::Returned => Some((at, Purity::Pure)),
                    Nesting::Suspended | Nesting::Filled(_) => None,
                })
        })
        .collect()
}
