//! Source-to-cell contracts, including the production module route.

use gandr_core_term::CoreArena;
use gandr_surface_parser::parse;
use gandr_surface_syntax::SourceText;
use gandr_theory_cell_complexes::Cell;
use gandr_theory_cell_complexes::CellCount;
use gandr_theory_cell_complexes::CellProvenance;
use gandr_theory_cell_complexes::ContinuationCount;
use gandr_theory_levitation::CircuitElaborationError;
use quenchant_shape::shape::Maybe;

use super::*;
use crate::LoweringBudget;
use crate::description::DescriptionReport;
use crate::description::elaborate_descriptions;
use crate::fixture::grammar;
use crate::lower_module;
use crate::namespace::Recognition;
use crate::unit::Unit;

/// Two frame-defining constructors and two operation laws.
const NAT_ADD: &str = r#"data NatAdd : Type {
    Zero : NatAdd;
    Succ : (n : NatAdd) --> NatAdd;
    oper add(m : NatAdd, n : NatAdd) -> NatAdd;
    rule add(Zero, n) ==> n;
    rule add(Succ(m), n) ==> Succ(add(m, n));
}"#;

/// Read descriptions through the production grammar.
///
/// # Specification
/// trivial.
fn descriptions<'source>(source: impl Into<SourceText<'source>>) -> DescriptionReport
{
    let grammar = grammar();
    let tree = parse(&grammar, source.into()).unwrap().into_tree();
    elaborate_descriptions(&grammar, &tree, &Unit::single()).unwrap()
}

/// Read a fixture cell by its insertion identity.
///
/// # Specification
/// trivial.
fn cell(
    store: &CellStore,
    index: CellId,
) -> &Cell
{
    let Maybe::Present(cell) = store.get(index)
    else {
        panic!("fixture cell exists")
    };
    cell
}

#[test]
fn a_declared_single_output_operation_lets_its_rule_become_a_cell()
{
    let descriptions = descriptions(NAT_ADD);
    assert_eq!(descriptions.diagnostics, []);
    let cells = elaborate_desc_cells(&descriptions.declarations);
    assert_eq!(cells.diagnostics, []);
    let [ref declaration] = *cells.declarations.as_slice()
    else {
        panic!("one store")
    };
    assert_eq!(declaration.store.len(), CellCount::from(4_usize));
    assert_eq!(
        cell(&declaration.store, CellId::from(0_usize)).provenance(),
        CellProvenance::FrameDefining
    );
    assert_eq!(
        cell(&declaration.store, CellId::from(1_usize)).provenance(),
        CellProvenance::FrameDefining
    );
    assert_eq!(
        cell(&declaration.store, CellId::from(2_usize)).provenance(),
        CellProvenance::SurfaceRule
    );
    assert_eq!(
        cell(&declaration.store, CellId::from(3_usize)).provenance(),
        CellProvenance::SurfaceRule
    );
}

#[test]
fn a_many_out_operation_rule_becomes_a_cell_with_a_continuation_per_output()
{
    let source = "data NatDiv : Type { Zero : NatDiv; oper divmod(m : NatDiv, n : NatDiv) -> (q : NatDiv, r : NatDiv); rule divmod(m, Zero) ==> (Zero, m); }";
    let descriptions = descriptions(source);
    assert_eq!(descriptions.diagnostics, []);
    assert_eq!(
        descriptions.declarations[0].description.opers[0]
            .arity
            .outputs
            .len(),
        2
    );
    let cells = elaborate_desc_cells(&descriptions.declarations);
    assert_eq!(cells.diagnostics, []);
    let store = &cells.declarations[0].store;
    assert_eq!(store.len(), CellCount::from(2_usize));
    let rule = cell(store, CellId::from(1_usize));
    assert_eq!(rule.provenance(), CellProvenance::SurfaceRule);
    let gandr_theory_cell_complexes::ConsView::Op { op, rets, .. } = rule.lhs().consumer().view()
    else {
        panic!("the rule cuts against the operation frame")
    };
    assert_eq!(op.as_ref(), "divmod");
    assert_eq!(rets.len(), 2, "one return continuation per output port");
}

#[test]
fn a_rule_returning_fewer_results_than_outputs_is_refused_rather_than_narrowed()
{
    let source = "data NatDiv2 : Type { Zero : NatDiv2; oper divmod(m : NatDiv2, n : NatDiv2) -> (q : NatDiv2, r : NatDiv2); rule divmod(Zero, n) ==> Zero; }";
    let descriptions = descriptions(source);
    assert_eq!(descriptions.diagnostics, []);
    let cells = elaborate_desc_cells(&descriptions.declarations);
    let [ref rule] = *cells.diagnostics.as_slice()
    else {
        panic!("the rule alone declines: {:?}", cells.diagnostics)
    };
    assert_eq!(
        rule.fault,
        CellFault::Rule(ElaborateError::ResultArity {
            outputs: ContinuationCount::from(2_usize),
            results: ContinuationCount::ONE,
        })
    );
    assert_eq!(
        source.get(usize::from(rule.span.start()) .. usize::from(rule.span.end())),
        Some("rule divmod(Zero, n) ==> Zero")
    );
    assert_eq!(cells.declarations[0].store.len(), CellCount::from(1_usize));
    assert_eq!(
        cells.declarations[0].coincidence,
        Coincidence::Unexamined,
        "a declaration with a declined rule is not decided as one system"
    );
}

#[test]
fn a_source_with_no_declarations_elaborates_to_no_stores()
{
    let cells = elaborate_desc_cells(&descriptions("pure ()").declarations);
    assert_eq!(cells, CellReport::default());
}

#[test]
fn cell_identities_are_a_deterministic_function_of_the_source()
{
    let first = elaborate_desc_cells(&descriptions(NAT_ADD).declarations);
    let second = elaborate_desc_cells(&descriptions(NAT_ADD).declarations);
    assert_eq!(first, second);
    assert!(
        first.declarations[0]
            .store
            .iter()
            .map(|(id, _cell)| id)
            .eq((0_usize .. 4).map(CellId::from))
    );
}

#[test]
fn declaration_order_is_the_cell_order()
{
    let original = elaborate_desc_cells(&descriptions(NAT_ADD).declarations);
    let swapped = elaborate_desc_cells(
        &descriptions(
            r#"data NatAdd : Type {
        Zero : NatAdd;
        Succ : (n : NatAdd) --> NatAdd;
        oper add(m : NatAdd, n : NatAdd) -> NatAdd;
        rule add(Succ(m), n) ==> Succ(add(m, n));
        rule add(Zero, n) ==> n;
    }"#,
        )
        .declarations,
    );
    let first = &original.declarations[0].store;
    let second = &swapped.declarations[0].store;
    assert_eq!(first.len(), CellCount::from(4_usize));
    assert_eq!(second.len(), CellCount::from(4_usize));
    let at = |index: usize| CellId::from(index);
    assert_eq!(cell(first, at(0)), cell(second, at(0)));
    assert_eq!(cell(first, at(1)), cell(second, at(1)));
    assert_eq!(cell(first, at(2)), cell(second, at(3)));
    assert_eq!(cell(first, at(3)), cell(second, at(2)));
}

#[test]
fn a_face_declared_twice_is_one_cell()
{
    let descriptions = descriptions(
        "data Idem : Type { Zero : Idem; oper f(x : Idem) -> Idem; rule f(Zero) ==> Zero; rule f(Zero) ==> Zero; }",
    );
    assert_eq!(descriptions.declarations[0].description.rules.len(), 2);
    let cells = elaborate_desc_cells(&descriptions.declarations);
    assert_eq!(cells.diagnostics, []);
    assert_eq!(cells.declarations[0].store.len(), CellCount::from(2_usize));
    assert_eq!(
        cell(&cells.declarations[0].store, CellId::from(1_usize)).provenance(),
        CellProvenance::SurfaceRule
    );
}

#[test]
fn a_single_redex_block_reaches_the_cell_layer_behind_the_gate()
{
    let descriptions = descriptions(
        r#"data Nat : Type { Zero : Nat; Succ : (n : Nat) --> Nat; }
        theory Nat { sort Nat : Type; oper add : (Nat, Nat) --> Nat;
            rule cong1 : (rule p : Nat ==> Nat, data x : Nat, data y : Nat) ==> (z : Nat) {
                node : p(x) ==> (xp); node : add(xp, y) --> (z);
            };
        }"#,
    );
    assert_eq!(descriptions.diagnostics, []);
    let cells = elaborate_desc_cells(&descriptions.declarations);
    assert_eq!(cells.diagnostics, []);
    assert_eq!(cells.declarations[0].store.len(), CellCount::from(2_usize));
    assert_eq!(cells.declarations[1].store.len(), CellCount::from(1_usize));
    let [
        CircuitCell::Admitted {
            ref cell,
            ref composite,
        },
    ] = *cells.declarations[1].circuits.as_slice()
    else {
        panic!("one admitted composite")
    };
    assert_eq!(*cell, CellId::from(0_usize));
    assert_eq!(
        composite.active_position(),
        Maybe::Present(alloc::vec![0_usize.into()])
    );
}

#[test]
fn a_two_redex_body_declines_with_both_occurrences()
{
    let descriptions = descriptions(
        r#"theory Nat { sort Nat : Type; oper add : (Nat, Nat) --> Nat;
        rule cong2 : (rule p : Nat ==> Nat, rule q : Nat ==> Nat, data x : Nat, data y : Nat) ==> (z : Nat) {
            node : p(x) ==> (xp); node : q(y) ==> (yp); node : add(xp, yp) --> (z);
        };
    }"#,
    );
    assert_eq!(descriptions.diagnostics, []);
    let cells = elaborate_desc_cells(&descriptions.declarations);
    let [CircuitCell::Refused(ref index)] = *cells.declarations[0].circuits.as_slice()
    else {
        panic!("the composite gate declines")
    };
    let CellFault::Rule(ElaborateError::NoCircuitComposite(
        CircuitElaborationError::ManyRedexOccurrences { ref occurrences },
    )) = cells.diagnostics[index.0].fault
    else {
        panic!("the two occurrences are retained")
    };
    assert_eq!(occurrences.len(), 2);
    assert_eq!(cells.declarations[0].store.len(), CellCount::from(0_usize));
    assert_eq!(
        cells.declarations[0].coincidence,
        Coincidence::Unexamined,
        "nor is one with a declined circuit"
    );
}

#[test]
fn ordinary_lowering_executes_the_cell_gate_and_preserves_later_values()
{
    let source = "data Flag : Type { Off : Flag; On : Flag; oper split(x : Flag) -> (a : Flag, b : Flag); rule split(Off) ==> On; } def later = 7;";
    let grammar = grammar();
    let tree = parse(&grammar, source.into()).unwrap().into_tree();
    let mut arena = CoreArena::new();
    let module = lower_module(
        &grammar,
        &tree,
        &mut arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
    )
    .unwrap();
    let [ref rule] = *module.cells().diagnostics.as_slice()
    else {
        panic!("the cell refusal reached ordinary lowering")
    };
    assert_eq!(
        rule.fault,
        CellFault::Rule(ElaborateError::ResultArity {
            outputs: ContinuationCount::from(2_usize),
            results: ContinuationCount::ONE,
        })
    );
    assert_eq!(
        module.cells().declarations[0].store.len(),
        CellCount::from(2_usize)
    );
    assert_eq!(module.declarations().len(), 3);
    for (declaration, expected) in module.declarations().iter().zip(["Flag", "Flag", "later"]) {
        assert_eq!(declaration.name().as_ref(), expected);
    }
    assert!(matches!(
        module.declarations()[0].outcome(),
        crate::DeclarationOutcome::Data(_)
    ));
    assert_eq!(module.declarations()[1].span(), rule.span);
    assert!(matches!(
        module.declarations()[1].outcome(),
        crate::DeclarationOutcome::Refused(_)
    ));
}
