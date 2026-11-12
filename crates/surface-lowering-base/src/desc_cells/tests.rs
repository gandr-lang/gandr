//! Source-to-cell contracts. The production module route is in the
//! integration target, `tests::desc_cells`.

use gandr_surface_parser::parse;
use gandr_surface_syntax::SourceText;
use gandr_theory_cell_complexes::Cell;
use gandr_theory_cell_complexes::CellCount;
use gandr_theory_cell_complexes::CellProvenance;
use gandr_theory_cell_complexes::ContinuationCount;
use gandr_theory_levitation::CircuitElaborationError;
use quenchant_shape::shape::Maybe;

use super::*;
use crate::description::DescriptionReport;
use crate::description::MemberFault;
use crate::description::elaborate_descriptions;
use crate::fixture::grammar;
use crate::unit::Unit;

/// Two frame-defining constructors and two operation laws.
const NAT_ADD: &str = include_str!("tests/unformatted/nat-add.gandr");

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
    let cells = elaborate_desc_cells(&descriptions.declarations, &mut Decisions::none());
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
    let source = "data NatDiv : Type where { | Zero : NatDiv oper divmod : (m : NatDiv, n : NatDiv) --> (q : NatDiv, r : NatDiv); rule : divmod m Zero ==> (Zero, m); }";
    let descriptions = descriptions(source);
    assert_eq!(descriptions.diagnostics, []);
    assert_eq!(
        descriptions.declarations[0].description.opers[0]
            .arity
            .outputs
            .len(),
        2
    );
    let cells = elaborate_desc_cells(&descriptions.declarations, &mut Decisions::none());
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
    let source = "data NatDiv2 : Type where { | Zero : NatDiv2 oper divmod : (m : NatDiv2, n : NatDiv2) --> (q : NatDiv2, r : NatDiv2); rule : divmod Zero n ==> Zero; }";
    let descriptions = descriptions(source);
    assert_eq!(descriptions.diagnostics, []);
    let cells = elaborate_desc_cells(&descriptions.declarations, &mut Decisions::none());
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
        Some("rule : divmod Zero n ==> Zero")
    );
    assert_eq!(cells.declarations[0].store.len(), CellCount::from(1_usize));
    assert_eq!(
        cells.declarations[0].coincidence,
        Coincidence::Unexamined,
        "a declaration with a declined rule is not decided as one system"
    );
}

/// #2375: a rule applying an operation the signature does not declare, once
/// on each side, is refused once by the description check, and its block is
/// not decided as one system.
#[test]
fn an_ill_formed_rule_is_refused_once_and_left_unexamined_2375()
{
    let report = descriptions(
        "theory Undeclared where { sort S : Type+; sort C : Type; oper get : (k : pi+ (s : S) . C) --> C; oper put : (s : S, k : C) --> C; rule putPut : put s (put (f s) k) <=> put (f s) k; }",
    );
    let [ref refusal] = *report.diagnostics.as_slice()
    else {
        panic!("the rule is refused once: {:?}", report.diagnostics)
    };
    assert!(
        matches!(refusal.fault, crate::description::DescriptionFault::IllFormed(ref ill)
            if ill.kind == gandr_theory_levitation::WfKind::OutOfSignatureRule
                && ill.subjects.iter().map(AsRef::<str>::as_ref).eq(["f"])),
        "the refusal names the undeclared operation: {refusal:?}"
    );
    assert!(
        report.declarations[0].ill_formed,
        "the declaration is marked as refused"
    );
    let cells = elaborate_desc_cells(&report.declarations, &mut Decisions::none());
    assert_eq!(
        cells.diagnostics,
        [],
        "the overlap check runs over no rule the description check refused"
    );
    assert_eq!(cells.declarations[0].coincidence, Coincidence::Unexamined);
}

/// A rule or a circuit that applies an operation with no output takes no
/// refusal of its own: the operation's `NoOutput` states the fault once, and
/// no later check reads the block.
#[test]
fn a_rule_over_a_declined_operation_owes_no_refusal_of_its_own_2666()
{
    let source = "theory Spill where { sort M : Type; oper unit : () --> M; oper drain : (m : M) --> (); rule gone : drain unit ==> unit; rule spill : (rule p : M ==> M, data x : M) ==> (z : M) { node : p(x) ==> (xp); node : drain(xp) --> (z); }; }";
    let report = descriptions(source);
    assert_eq!(
        report.diagnostics,
        [],
        "both rules pass the description route"
    );
    let cells = elaborate_desc_cells(&report.declarations, &mut Decisions::none());
    let [ref diagnostic] = *cells.diagnostics.as_slice()
    else {
        panic!("the operation alone is refused: {:?}", cells.diagnostics)
    };
    assert_eq!(
        diagnostic.lowering_refusal(),
        crate::error::LoweringRefusal::UndescribedMember {
            span: diagnostic.span,
            fault: MemberFault::NoOutput,
        },
        "the refusal is the operation's own fault"
    );
    assert!(
        source
            .get(usize::from(diagnostic.span.start()) .. usize::from(diagnostic.span.end()))
            .is_some_and(|written| written.starts_with("oper drain")),
        "the refusal stands at the operation"
    );
    let [ref declaration] = *cells.declarations.as_slice()
    else {
        panic!("one declaration")
    };
    assert_eq!(
        declaration.declined_faces,
        [DeclinedFaceIndex::from(0_usize)],
        "the rule stays out of the sequent reading"
    );
    assert_eq!(
        declaration.circuits,
        [CircuitCell::Excluded],
        "the circuit stays out with no diagnostic"
    );
    assert_eq!(
        declaration.coincidence,
        Coincidence::Unexamined,
        "no later check reads the block"
    );
}

/// #1450: a rule whose left side copies a variable, in a data block, a theory
/// law or a circuit, is refused by name at the copy's second occurrence.
#[test]
fn a_copied_variable_is_refused_at_its_second_occurrence()
{
    for (source, member, second) in [
        (
            "data NatSub : Type where { | Zero : NatSub oper minus : (m : NatSub, n : NatSub) --> NatSub; rule : minus x x ==> Zero; }",
            "rule : minus x x ==> Zero",
            "rule : minus x ".len(),
        ),
        (
            "theory Idem where { sort M : Type; oper mul : (x : M, y : M) --> M; rule idem : mul x x ==> x; }",
            "rule idem : mul x x ==> x",
            "rule idem : mul x ".len(),
        ),
        (
            "theory Copy where { sort Nat : Type; oper add : (l : Nat, r : Nat) --> (s : Nat); rule copy2 : (data x : Nat) ==> (z : Nat) { node : add(x, x) --> (z); }; }",
            "rule copy2 : (data x : Nat) ==> (z : Nat) { node : add(x, x) --> (z); }",
            "rule copy2 : (data x : Nat) ==> (z : Nat) { node : add(x, ".len(),
        ),
    ] {
        let descriptions = descriptions(source);
        assert_eq!(descriptions.diagnostics, [], "{source}");
        let cells = elaborate_desc_cells(&descriptions.declarations, &mut Decisions::none());
        let [ref refusal] = *cells.diagnostics.as_slice()
        else {
            panic!("one refusal in {source}: {:?}", cells.diagnostics)
        };
        let CellFault::NonLinear { ref pattern, copy } = refusal.fault
        else {
            panic!("{source} is refused as a copy: {:?}", refusal.fault)
        };
        assert_eq!(pattern.copied().hole().as_ref(), "x", "{source}");
        let start = source.find(member).unwrap();
        assert_eq!(
            (
                usize::from(refusal.span.start()),
                usize::from(refusal.span.end())
            ),
            (start, start + member.len()),
            "{source}: the refusal stands at the rule"
        );
        assert_eq!(
            (usize::from(copy.start()), usize::from(copy.end())),
            (start + second, start + second + 1),
            "{source}: the copy is the second `x`"
        );
        assert!(
            matches!(
                refusal.lowering_refusal(),
                crate::error::LoweringRefusal::RulesNonLinear { span, copy: named }
                    if span == refusal.span && named == copy
            ),
            "{source}"
        );
    }
}

#[test]
fn a_source_with_no_declarations_elaborates_to_no_stores()
{
    let cells = elaborate_desc_cells(
        &descriptions("pure ()").declarations,
        &mut Decisions::none(),
    );
    assert_eq!(cells, CellReport::default());
}

#[test]
fn cell_identities_are_a_deterministic_function_of_the_source()
{
    let first = elaborate_desc_cells(&descriptions(NAT_ADD).declarations, &mut Decisions::none());
    let second = elaborate_desc_cells(&descriptions(NAT_ADD).declarations, &mut Decisions::none());
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
    let original =
        elaborate_desc_cells(&descriptions(NAT_ADD).declarations, &mut Decisions::none());
    let swapped = elaborate_desc_cells(
        &descriptions(include_str!(
            "tests/unformatted/declaration-order-is-the-cell-order-swapped.gandr"
        ))
        .declarations,
        &mut Decisions::none(),
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
        "data Idem : Type where { | Zero : Idem oper f : (x : Idem) --> Idem; rule : f Zero ==> Zero; rule : f Zero ==> Zero; }",
    );
    assert_eq!(descriptions.declarations[0].description.rules.len(), 2);
    let cells = elaborate_desc_cells(&descriptions.declarations, &mut Decisions::none());
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
    let descriptions = descriptions(include_str!(
        "tests/fixtures/a-single-redex-block-reaches-the-cell-layer-behind-the-gate-descriptions.gandr"
    ));
    assert_eq!(descriptions.diagnostics, []);
    let cells = elaborate_desc_cells(&descriptions.declarations, &mut Decisions::none());
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
    let descriptions = descriptions(include_str!(
        "tests/fixtures/a-two-redex-body-declines-with-both-occurrences-descriptions.gandr"
    ));
    assert_eq!(descriptions.diagnostics, []);
    let cells = elaborate_desc_cells(&descriptions.declarations, &mut Decisions::none());
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
fn each_cell_fault_is_refused_by_its_own_member_fault()
{
    // One source per fault the corpus reaches: the cell gate's cause becomes
    // the member fault the refusal carries, at the member it stops.
    let rows = [
        (
            "data NatDiv2 : Type where { | Zero : NatDiv2 oper divmod : (m : NatDiv2, n : NatDiv2) --> (q : NatDiv2, r : NatDiv2); rule : divmod Zero n ==> Zero; }",
            "rule : divmod Zero n ==> Zero",
            MemberFault::ResultArity,
        ),
        (
            include_str!("tests/fixtures/each-cell-fault-is-refused-by-its-own-member-fault.gandr"),
            "rule stray",
            MemberFault::LhsNotOperation,
        ),
        (
            include_str!(
                "tests/fixtures/a-two-redex-body-declines-with-both-occurrences-descriptions.gandr"
            ),
            "rule cong2",
            MemberFault::ParallelRedexes,
        ),
    ];
    for (source, member, expected) in rows {
        let descriptions = descriptions(source);
        assert_eq!(
            descriptions.diagnostics,
            [],
            "{member} passes the description route"
        );
        let cells = elaborate_desc_cells(&descriptions.declarations, &mut Decisions::none());
        let [ref diagnostic] = *cells.diagnostics.as_slice()
        else {
            panic!("{member} alone declines: {:?}", cells.diagnostics)
        };
        let refusal = diagnostic.lowering_refusal();
        assert_eq!(
            refusal,
            crate::error::LoweringRefusal::UndescribedMember {
                span: diagnostic.span,
                fault: expected,
            },
            "{member} is refused by its own fault"
        );
        assert!(
            source
                .get(usize::from(diagnostic.span.start()) .. usize::from(diagnostic.span.end()))
                .is_some_and(|written| written.starts_with(member)),
            "{member} is refused at its own span"
        );
    }
}
