//! Consumer-visible ruled-signature boundaries.

use core::fmt::Write as _;

use gandr_surface_parser::parse;
use gandr_surface_syntax::SourceText;
use gandr_theory_levitation::PortFace;

use super::*;
use crate::description::DescriptionReport;
use crate::description::elaborate_descriptions;
use crate::fixture::grammar;

/// Read repaired and complete trees through the same declaration route.
///
/// # Specification
/// trivial.
fn described<'source>(source: impl Into<SourceText<'source>>) -> DescriptionReport
{
    let grammar = grammar();
    let tree = parse(&grammar, source.into()).unwrap().into_tree();
    elaborate_descriptions(&grammar, &tree).unwrap()
}

#[test]
fn a_ruled_sign_block_lowers_its_members_into_a_description()
{
    let report = described(
        r#"data Nat : Type {
        Zero : Nat;
        Succ : (n : Nat) --> Nat;
    }
    sign Nat {
        sort Nat : Type;
        oper add : (Nat, Nat) --> Nat;
        rule cong1 : (rule p : Nat ==> Nat, data x : Nat, data y : Nat) ==> (z : Nat) {
            node : p(x) ==> (x′);
            node : add(x′, y) --> (z);
        };
    }"#,
    );
    assert_eq!(report.diagnostics, []);
    let [ref data, ref sign] = *report.declarations.as_slice()
    else {
        panic!("data and signature")
    };
    assert_eq!(
        data.description
            .ctors
            .iter()
            .map(|ctor| ctor.name.as_ref())
            .collect::<Vec<_>>(),
        ["Zero", "Succ"]
    );
    assert_eq!(
        sign.classifier,
        Maybe::Absent(family_classifier::Absent::Signature)
    );
    let [ref rule] = *sign.description.circuits.as_ref()
    else {
        panic!("one circuit")
    };
    assert_eq!(rule.name.as_ref(), "cong1");
    let [ref port] = *rule.ports.as_ref()
    else {
        panic!("one rewrite port")
    };
    assert_eq!(port.name.as_ref(), "p");
    assert_eq!(port.face, PortFace::Sorted("Nat".into()));
    assert!(matches!(rule.body.nodes.as_ref(), [
        CircuitNode::Redex(_),
        CircuitNode::Frame(_)
    ]));
    assert_eq!(rule.body.out.as_ref(), "z");
    assert_eq!(
        rule.sphere.lhs,
        FreeTerm::op("add", [FreeTerm::var("x"), FreeTerm::var("y")])
    );
    assert_eq!(
        rule.sphere.rhs,
        FreeTerm::op("add", [FreeTerm::var("x′"), FreeTerm::var("y")])
    );
}

#[test]
fn an_expression_kind_signature_endpoint_is_refused_by_the_description_route()
{
    let source = "sign Wrong { sort Nat : Type; oper f : (a : Nat) --> (b : Nat); rule face : (f) ==> (z : Nat) { node : f(f) --> (z); }; }";
    let report = described(source);
    let [ref sign] = *report.declarations.as_slice()
    else {
        panic!("retained signature")
    };
    assert_eq!(sign.description.opers[0].name.as_ref(), "f");
    assert_eq!(sign.description.circuits.as_ref(), []);
    let refusal = report
        .diagnostics
        .iter()
        .find(|diagnostic| {
            matches!(
                diagnostic.fault,
                DescriptionFault::Signature(SignatureFault::ExpressionEndpoint)
            )
        })
        .unwrap();
    assert_eq!(
        source.get(usize::from(refusal.span.start()) .. usize::from(refusal.span.end())),
        Some("(f)")
    );
}

#[test]
fn an_item_level_data_member_declines_with_the_nested_block_respelling()
{
    let report = described(
        "sign Stale { sort Nat : Type; data Zero : Nat; oper add : (Nat, Nat) --> Nat; }",
    );
    assert!(report.diagnostics.iter().any(|diagnostic| diagnostic.fault
        == DescriptionFault::Signature(SignatureFault::RetiredDataMember)));
    assert_eq!(report.declarations[0].description.ctors.as_ref(), []);
    assert_eq!(
        report.declarations[0].description.opers[0].name.as_ref(),
        "add"
    );
}

#[test]
fn a_many_out_node_declines_naming_the_cell_alphabet_question()
{
    let report = described(
        "sign Wide { sort Nat : Type; oper f : Nat --> Nat; rule split : (data x : Nat) ==> (z : Nat) { node : f(x) --> (z, w); }; }",
    );
    assert!(report.diagnostics.iter().any(|diagnostic| diagnostic.fault
        == DescriptionFault::Signature(SignatureFault::MultipleOutputs(OutputCount(2)))));
    assert_eq!(report.declarations[0].description.circuits.as_ref(), []);
    assert_eq!(
        report.declarations[0].description.opers[0].name.as_ref(),
        "f"
    );
}

#[test]
fn a_many_out_interface_declines_naming_the_cell_alphabet_question()
{
    let report = described(
        "sign Wide { sort Nat : Type; oper f : Nat --> Nat; rule pair : (data x : Nat) ==> (y : Nat, z : Nat) { node : f(x) --> (y); }; }",
    );
    assert!(report.diagnostics.iter().any(|diagnostic| diagnostic.fault
        == DescriptionFault::Signature(SignatureFault::MultipleOutputs(OutputCount(2)))));
    assert_eq!(report.declarations[0].description.circuits.as_ref(), []);
}

#[test]
fn a_feed_statement_declines_naming_the_wheel_obligation()
{
    let report = described(
        "sign Wheel { sort Nat : Type; oper zip : (s : Nat, t : Nat) --> (u : Nat); rule spin : (data stream : Nat) ==> (out : Nat) { node : zip(stream, state) --> (out); feed : (out) --> (state); }; }",
    );
    assert!(
        report.diagnostics.iter().any(
            |diagnostic| diagnostic.fault == DescriptionFault::Signature(SignatureFault::Wheel)
        ),
        "{:?}",
        report.diagnostics
    );
    assert_eq!(report.declarations[0].description.circuits.as_ref(), []);
}

#[test]
fn an_oper_filler_stays_declined_and_names_its_own_rung()
{
    let report = described(
        "sign Filled { sort Nat : Type; oper f : Nat --> Nat { node : f(x) --> (z); }; oper g : Nat --> Nat; }",
    );
    assert!(report.diagnostics.iter().any(|diagnostic| diagnostic.fault
        == DescriptionFault::Signature(SignatureFault::OperationFiller)));
    assert_eq!(
        report.declarations[0]
            .description
            .opers
            .iter()
            .map(|operation| operation.name.as_ref())
            .collect::<Vec<_>>(),
        ["g"]
    );
}

#[test]
fn a_fillerless_rule_member_declines_to_the_higher_cells_lane()
{
    let report =
        described("sign Higher { sort Nat : Type; rule r : (data x : Nat) ==> (z : Nat); }");
    assert!(
        report.diagnostics.iter().any(|diagnostic| diagnostic.fault
            == DescriptionFault::Signature(SignatureFault::HigherCell))
    );
    assert_eq!(report.declarations[0].description.circuits.as_ref(), []);
}

#[test]
fn a_written_face_in_a_sign_block_declines_naming_the_block_form_that_holds_it()
{
    let source = "sign Written { sort Nat : Type; rule unit ==> add; oper neg : Nat --> Nat; }";
    let report = described(source);
    let refusal = report
        .diagnostics
        .iter()
        .find(|diagnostic| {
            diagnostic.fault == DescriptionFault::Signature(SignatureFault::WrittenFace)
        })
        .unwrap();
    assert_eq!(
        source.get(usize::from(refusal.span.start()) .. usize::from(refusal.span.end())),
        Some("rule unit ==> add")
    );
    assert_eq!(
        report.declarations[0].description.opers[0].name.as_ref(),
        "neg"
    );
}

#[test]
fn a_data_spelled_sign_oper_declines_before_no_output_can_be_fabricated()
{
    let report =
        described("sign Old { sort Nat : Type; oper f(x : Nat) -> Nat; oper g : Nat --> Nat; }");
    assert!(report.diagnostics.iter().any(|diagnostic| diagnostic.fault
        == DescriptionFault::Signature(SignatureFault::MissingJudgment)));
    assert_eq!(
        report.declarations[0]
            .description
            .opers
            .iter()
            .map(|operation| operation.name.as_ref())
            .collect::<Vec<_>>(),
        ["g"]
    );
}

#[test]
fn a_declined_rule_member_leaves_the_members_after_it_intact()
{
    let source = "sign Adder { sort Nat : Type; oper add : (Nat, Nat) --> Nat; rule unit ==> add; rule swap ==> mul; oper neg : Nat --> Nat; }";
    let report = described(source);
    let refused: Vec<_> = report
        .diagnostics
        .iter()
        .filter(|diagnostic| {
            diagnostic.fault == DescriptionFault::Signature(SignatureFault::WrittenFace)
        })
        .filter_map(|diagnostic| {
            source.get(usize::from(diagnostic.span.start()) .. usize::from(diagnostic.span.end()))
        })
        .collect();
    assert_eq!(refused, ["rule unit ==> add", "rule swap ==> mul"]);
    assert_eq!(
        report.declarations[0]
            .description
            .opers
            .iter()
            .map(|operation| operation.name.as_ref())
            .collect::<Vec<_>>(),
        ["add", "neg"]
    );
}

#[test]
fn node_arrow_resolution_distinguishes_declared_and_unknown_heads()
{
    let declared = described(
        "sign Scope { sort Nat : Type; rule r : (data x : Nat) ==> (z : Nat) { node : f(x) ==> (z); }; oper f : Nat --> Nat; }",
    );
    assert!(
        declared
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.fault
                == DescriptionFault::Signature(SignatureFault::ArrowMismatch {
                    expected: ArrowRow::Mapping,
                    actual: ArrowRow::Face
                }))
    );
    let unknown = described(
        "sign Scope { sort Nat : Type; rule r : (data x : Nat) ==> (z : Nat) { node : missing(x) ==> (z); }; }",
    );
    assert!(unknown.diagnostics.iter().any(|diagnostic| diagnostic.fault
        == DescriptionFault::Signature(SignatureFault::UndeclaredRewrite("missing".into()))));
    assert!(!unknown.diagnostics.iter().any(|diagnostic| matches!(
        diagnostic.fault,
        DescriptionFault::Signature(SignatureFault::ArrowMismatch { .. })
    )));
}

#[test]
fn an_out_of_signature_frame_head_earns_the_declaration_tables_refusal()
{
    let report = described(
        "sign Stray {\n  sort Nat : Type;\n  rule stray : (data x : Nat) ==> (z : Nat) {\n    node : mystery(x) --> (z);\n  };\n}\n",
    );
    assert!(report.diagnostics.iter().any(|diagnostic| matches!(
        diagnostic.fault,
        DescriptionFault::IllFormed(ref reason)
            if reason.kind == gandr_theory_levitation::WfKind::OutOfSignatureRule
                && reason.message.as_ref().contains("circuit rule `stray`")
                && reason.message.as_ref().contains("`mystery`")
    )));
}

#[test]
fn a_redex_applying_an_undeclared_rewrite_earns_its_own_refusal()
{
    let report = described(
        "sign NoPort {\n  sort Nat : Type;\n  oper f : (a : Nat) --> (b : Nat);\n\n  rule stray : (rule p : Nat ==> Nat, data x : Nat) ==> (z : Nat) {\n    node : p(x) ==> (m);\n    node : f(m) --> (z);\n  };\n}\n",
    );
    assert_eq!(report.diagnostics, []);
    assert_eq!(report.declarations[0].description.circuits.len(), 1);
}

#[test]
fn a_wiring_that_closes_a_cycle_earns_the_declaration_tables_refusal()
{
    let report = described(
        "sign Loop {\n  sort Nat : Type;\n  oper f : (a : Nat) --> (b : Nat);\n  oper g : (a : Nat) --> (b : Nat);\n\n  rule spin : (data x : Nat) ==> (z : Nat) {\n    node : f(w) --> (z);\n    node : g(z) --> (w);\n  };\n}\n",
    );
    let [ref diagnostic] = *report.diagnostics.as_slice()
    else {
        panic!("one cyclic wiring")
    };
    assert!(matches!(
        diagnostic.fault,
        DescriptionFault::Signature(SignatureFault::Derivation(
            gandr_theory_levitation::CircuitDerivationError::CyclicWiring(_)
        ))
    ));
    assert_eq!(report.declarations[0].description.circuits.as_ref(), []);
}

#[test]
fn a_repeated_argument_name_reaches_the_linearity_refusal()
{
    let report = described(
        "sign Copy {\n  sort Nat : Type;\n  oper add : (l : Nat, r : Nat) --> (s : Nat);\n  rule copy2 : (data x : Nat) ==> (z : Nat) {\n    node : add(x, x) --> (z);\n  };\n}\n",
    );
    let cells = crate::desc_cells::elaborate_desc_cells(&report.declarations);
    let [ref refusal] = *cells.diagnostics.as_slice()
    else {
        panic!("one cell refusal")
    };
    assert!(matches!(
        refusal.fault,
        crate::desc_cells::CellFault::Rule(gandr_theory_computads::ElaborateError::NonLinear(_))
    ));
}

#[test]
fn a_doubling_body_declines_on_the_derivation_node_budget()
{
    let mut source = alloc::string::String::from(
        "sign Doubling {\n  sort Nat : Type;\n  oper l : (a : Nat) --> (b : Nat);\n  oper r : (a : Nat) --> (b : Nat);\n  oper add : (a : Nat, b : Nat) --> (c : Nat);\n  rule blow : (data w0 : Nat) ==> (w12 : Nat) {\n",
    );
    for level in 1 ..= 12_u32 {
        let below = level.saturating_sub(1);
        write!(
            source,
            "    node : l(w{below}) --> (a{level});\n    node : r(w{below}) --> (b{level});\n    node : add(a{level}, b{level}) --> (w{level});\n"
        )
        .unwrap();
    }
    source.push_str("  };\n}\n");
    let report = described(source.as_str());
    assert!(report.diagnostics.iter().any(|diagnostic| matches!(
        diagnostic.fault,
        DescriptionFault::Signature(SignatureFault::Derivation(
            gandr_theory_levitation::CircuitDerivationError::NodeBudget { .. }
        ))
    )));
    assert_eq!(report.declarations[0].description.circuits.as_ref(), []);
}

#[test]
fn a_sign_block_is_a_declaration_rather_than_an_unsupported_item()
{
    let grammar = grammar();
    let tree = parse(
        &grammar,
        SourceText::from("sign Nat { sort Nat : Type; oper add : (Nat, Nat) --> Nat; }"),
    )
    .unwrap()
    .into_tree();
    let mut arena = gandr_core_term::CoreArena::new();
    let module = crate::lower_module(
        &grammar,
        &tree,
        &mut arena,
        crate::LoweringBudget::DEFAULT,
        crate::namespace::Recognition::default(),
    )
    .unwrap();
    assert_eq!(module.declarations(), []);
    assert_eq!(module.descriptions().declarations.len(), 1);
    assert_eq!(module.descriptions().diagnostics, []);
}

#[test]
fn a_member_with_no_judgment_head_declines_rather_than_vanishing()
{
    let source = "sign Broken {\n  sort Nat : Type;\n  rule ;\n}\n";
    let report = described(source);
    assert!(report.diagnostics.iter().any(|diagnostic| {
        diagnostic.fault == DescriptionFault::Signature(SignatureFault::WrittenFace)
            && source
                .get(usize::from(diagnostic.span.start()) .. usize::from(diagnostic.span.end()))
                .is_some_and(|text| text.starts_with("rule"))
    }));
}

#[test]
fn a_terminated_block_is_not_told_it_lacks_terminators()
{
    let report = described(
        "sign S {\n  sort Ob : Type;\n  sort Hom(dom : Ob, cod : Ob) : Type;\n  oper id : (a : Ob) --> Ob;\n}\n",
    );
    assert_eq!(report.diagnostics, []);
    assert_eq!(report.declarations[0].description.sorts.len(), 2);
    assert_eq!(report.declarations[0].description.opers.len(), 1);
}

#[test]
fn unseparated_members_are_declined_rather_than_dropped()
{
    let source = "sign S {\n  sort Ob : Type\n  sort Ar : Type\n}\n";
    let report = described(source);
    assert!(report.diagnostics.iter().any(|diagnostic| {
        diagnostic.fault == DescriptionFault::Malformed
            && source
                .get(usize::from(diagnostic.span.start()) .. usize::from(diagnostic.span.end()))
                .is_some_and(|text| text.contains("sort Ob") && text.contains("sort Ar"))
    }));
    assert!(
        report.declarations[0]
            .description
            .sorts
            .iter()
            .all(|sort| sort.name.as_ref() != "Ob" && sort.name.as_ref() != "Ar")
    );
}

#[test]
fn terminated_members_are_all_presented()
{
    let report = described(
        "sign S {\n  sort Ob : Type;\n  sort Ar : Type;\n  oper f : (a : Ob) --> Ob;\n}\n",
    );
    assert_eq!(report.diagnostics, []);
    assert_eq!(report.declarations[0].description.sorts.len(), 2);
    assert_eq!(report.declarations[0].description.opers.len(), 1);
}

#[test]
fn an_unreadable_member_keeps_its_own_report()
{
    let source = "sign Adder {\n  sort Nat : Type;\n  oper add : (Nat, Nat) --> Nat;\n  rule unit ==> add;\n}\n";
    let report = described(source);
    let [ref diagnostic] = *report.diagnostics.as_slice()
    else {
        panic!("one member-local refusal")
    };
    assert_eq!(
        diagnostic.fault,
        DescriptionFault::Signature(SignatureFault::WrittenFace)
    );
    assert_eq!(
        source.get(usize::from(diagnostic.span.start()) .. usize::from(diagnostic.span.end())),
        Some("rule unit ==> add")
    );
}
