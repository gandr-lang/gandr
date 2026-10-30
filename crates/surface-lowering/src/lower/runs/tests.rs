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
const NAT: &str = "data Nat : Type { Zero : Nat; Succ : (n : Nat) --> Nat; }\n\
                   def twice(n : Nat) -> -F Nat { Succ(Succ(n)) }\n";

#[test]
fn an_explicit_runs_attribute_asks_within_its_form()
{
    let source = format!(
        "{NAT}@[ explicit_runs ]\n\
         module Asked {{\n\
         def every(n : Nat) -> -F Nat {{ Succ(twice(n)) }}\n\
         @[ explicit_runs(\"effects\") ]\n\
         def wider(n : Nat) -> -F Nat {{ Succ(twice(Succ(n))) }}\n\
         }}\n\
         @[ explicit_runs(\"effects\") ]\n\
         def effects(n : Nat) -> -F Nat {{ Succ(twice(Zero)) }}\n\
         def unasked(n : Nat) -> -F Nat {{ Succ(twice(Succ(Zero))) }}\n\
         def written(n : Nat) -> -F Nat {{ Succ(run twice(Succ(Succ(n)))) }}\n\
         @[ explicit_runs(\"effect\") ]\n\
         def misspelled(n : Nat) -> -F Nat {{ Succ(Succ(twice(n))) }}\n"
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
            inferred(at("{ Succ(twice(n)) }", "twice(n)"), AskedRuns::Every),
            inferred(
                at("{ Succ(twice(Succ(n))) }", "twice(Succ(n))"),
                AskedRuns::Every
            ),
            inferred(
                at("{ Succ(twice(Zero)) }", "twice(Zero)"),
                AskedRuns::Effectful
            ),
            inferred(
                at("{ Succ(twice(Succ(Zero))) }", "twice(Succ(Zero))"),
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
    let text = SourceText::from(
        "def id(n: Integer) -> -F Integer { n }\n\
         def returned(n: Integer) -> -F Integer { return id(n) }\n\
         def leading(n: Integer) -> -F Integer { id(n) + 1 }\n\
         def grouped(n: Integer) -> -F Integer { return n + 1 }\n",
    );
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
                at("{ return id(n) }", "id(n)"),
                site(RunSpelling::Bare, RunOperand::Tight)
            ),
            (
                at("{ id(n) + 1 }", "id(n)"),
                site(RunSpelling::Parenthesised, RunOperand::Tight)
            ),
            (
                at("{ return n + 1 }", "n + 1"),
                site(RunSpelling::Bare, RunOperand::Grouped)
            ),
        ],
        "a call after `return` is spelled bare, one that begins a block's tail parenthesised, \
         and an operator call is grouped after `run`"
    );
    let written = SourceText::from(
        "def id(n: Integer) -> -F Integer { n }\n\
         def returned(n: Integer) -> -F Integer { return run id(n) }\n\
         def leading(n: Integer) -> -F Integer { (run id(n)) + 1 }\n\
         def grouped(n: Integer) -> -F Integer { return run (n + 1) }\n",
    );
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
    let text = SourceText::from(
        "def plus(n : Integer) -> Integer => Integer { thunk { fn (m : Integer) { m + n } } }\n\
         def applied(n : Integer) -> Integer { run h <- plus(n)(1) ; h }\n\
         def dependent(A : Type) -> A => A { thunk { fn (x : A) { x } } }\n\
         def picked(A : Type, x : A) -> A { dependent(A)(x) }\n\
         def curried(n : Integer, m : Integer) -> Integer { n + m }\n\
         def partial(n : Integer) -> Integer { curried(n)(1) }\n",
    );
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
            (at("run h <- plus(n)(1)", "plus(n)"), site),
            (at("{ dependent(A)(x) }", "dependent(A)"), site),
        ],
        "a head call returning a function runs, spelled grouped where a bound statement \
         reads it as at a tail's start; a curried call runs nothing"
    );
    let written = SourceText::from(
        "def plus(n : Integer) -> Integer => Integer { thunk { fn (m : Integer) { m + n } } }\n\
         def applied(n : Integer) -> Integer { run h <- (run plus(n))(1) ; h }\n\
         def dependent(A : Type) -> A => A { thunk { fn (x : A) { x } } }\n\
         def picked(A : Type, x : A) -> A { (run dependent(A))(x) }\n",
    );
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
        "{NAT}def second(a : Nat, b : Nat) -> -F Nat {{ b }}\n\
         def field(n : Nat) -> -F Nat {{ run m <- twice(n) ; Succ(m) }}\n\
         def chained(n : Nat) -> -F Nat {{ run a <- twice(n) ; run b <- twice(a) ; become twice(b) }}\n\
         def later(n : Nat) -> -F Nat {{ run c <- twice(n) ; second(c, twice(n)) }}\n\
         def doubled(n : Nat) -> -F Nat {{ run d <- twice(n) ; second(d, d) }}\n\
         def after(n : Nat) -> -F Nat {{ run e <- twice(n) ; second(twice(n), e) }}\n\
         def whole(n : Nat) -> -F Nat {{ run f <- twice(n) ; f }}\n\
         def reread(n : Nat) -> -F Nat {{ run g <- twice(n) ; run h <- twice(g) ; second(g, h) }}\n\
         def paired(n : Nat) -> -F Nat {{ run p <- twice(n) ; run q <- twice(Zero) ; second(p, q) }}\n\
         def swapped(n : Nat) -> -F Nat {{ run r <- twice(n) ; run s <- twice(Zero) ; second(s, r) }}\n\
         @[ explicit_runs ]\n\
         def asked(n : Nat) -> -F Nat {{ run k <- twice(n) ; Succ(k) }}\n"
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
            linear(("run m <- twice(n)", "twice(n)"), ("Succ(m) }", "m")),
            linear(("run b <- twice(a)", "twice(a)"), ("twice(b) }", "b")),
            linear(("run c <- twice(n)", "twice(n)"), ("(c,", "c")),
            linear(("run h <- twice(g)", "twice(g)"), ("g, h) }", "h")),
            linear(("run p <- twice(n)", "twice(n)"), ("(p,", "p")),
            linear(("run q <- twice(Zero)", "twice(Zero)"), ("p, q) }", "q")),
            linear(("run s <- twice(Zero)", "twice(Zero)"), ("(s,", "s")),
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
        "{NAT}def second(a : Nat, b : Nat) -> -F Nat {{ b }}\n\
         def armed(a : Nat) -> -F Nat {{ case a {{ Zero => Zero, Succ(b) => {{ run d <- twice(b) ; Succ(d) }} }} }}\n\
         def chained(a : Nat) -> -F Nat {{ case a {{ Zero => Zero, Succ(b) => {{ run e <- twice(b) ; run f <- twice(e) ; Succ(f) }} }} }}\n\
         def reread(a : Nat) -> -F Nat {{ case a {{ Zero => Zero, Succ(b) => {{ run g <- twice(b) ; second(g, g) }} }} }}\n"
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
            linear(("run d <- twice(b)", "twice(b)"), ("Succ(d) }", "d")),
            linear(("run f <- twice(e)", "twice(e)"), ("Succ(f) }", "f")),
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
                    Nesting::Suspended => None,
                })
        })
        .collect()
}
