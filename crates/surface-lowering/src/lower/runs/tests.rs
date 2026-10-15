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
#[spec(ensures: |ret| ret.len() == report.nested_elaborations().values().map(|elaboration| elaboration.decisions().values().filter(|decided| matches!(decided, Nesting::Ran(_))).count()).sum::<usize>())]
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
                    Nesting::Suspended => None,
                })
        })
        .collect()
}
