//! Consumer-visible ruled-signature boundaries.

use alloc::vec;
use core::fmt::Write as _;

use gandr_surface_parser::parse;
use gandr_surface_syntax::SourceText;
use gandr_theory_levitation::PortFace;

use super::*;
use crate::circuit::JoinFault;
use crate::description::DescriptionReport;
use crate::description::elaborate_descriptions;
use crate::fixture::grammar;
use crate::unit::Unit;

/// Read repaired and complete trees through the same declaration route.
///
/// # Specification
/// trivial.
fn described<'source>(source: impl Into<SourceText<'source>>) -> DescriptionReport
{
    let grammar = grammar();
    let tree = parse(&grammar, source.into()).unwrap().into_tree();
    elaborate_descriptions(&grammar, &tree, &Unit::single()).unwrap()
}

#[test]
fn a_ruled_theory_block_lowers_its_members_into_a_description()
{
    let report = described(
        r#"data Nat : Type {
        Zero : Nat;
        Succ : (n : Nat) --> Nat;
    }
    theory Nat {
        sort Nat : Type;
        oper add : (Nat, Nat) --> Nat;
        rule cong1 : (rule p : Nat ==> Nat, data x : Nat, data y : Nat) ==> (z : Nat) {
            node : p(x) ==> (x′);
            node : add(x′, y) --> (z);
        };
    }"#,
    );
    assert_eq!(report.diagnostics, []);
    let [ref data, ref theory] = *report.declarations.as_slice()
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
        theory.classifier,
        Maybe::Absent(family_classifier::Absent::Signature)
    );
    let [ref rule] = *theory.description.circuits.as_ref()
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
    assert!(matches!(*rule.body.outs, [ref out] if out.as_ref() == "z"));
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
    let source = "theory Wrong { sort Nat : Type; oper f : (a : Nat) --> (b : Nat); rule face : (f) ==> (z : Nat) { node : f(f) --> (z); }; }";
    let report = described(source);
    let [ref theory] = *report.declarations.as_slice()
    else {
        panic!("retained signature")
    };
    assert_eq!(theory.description.opers[0].name.as_ref(), "f");
    assert_eq!(theory.description.circuits.as_ref(), []);
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
        "theory Stale { sort Nat : Type; data Zero : Nat; oper add : (Nat, Nat) --> Nat; }",
    );
    assert!(report.diagnostics.iter().any(|diagnostic| diagnostic.fault
        == DescriptionFault::Signature(SignatureFault::RetiredDataMember)));
    assert_eq!(report.declarations[0].description.ctors.as_ref(), []);
    assert_eq!(
        report.declarations[0].description.opers[0].name.as_ref(),
        "add"
    );
}

/// The rewrite node of a two-output congruence: `p` rewrites the dividend
/// before `divmod` reads it, and both of `divmod`'s ports leave the body.
const DIVMOD_CONGRUENCE: &str = "theory Div {
  sort Nat : Type;
  oper divmod : (m : Nat, n : Nat) --> (q : Nat, r : Nat);
  rule pass : (rule p : Nat ==> Nat, data m : Nat, data n : Nat) ==> (q : Nat, r : Nat) {
    node : p(m) ==> (m′);
    node : divmod(m′, n) --> (q, r);
  };
}";

#[test]
fn a_many_out_frame_binds_every_port_and_roots_the_body()
{
    let report = described(DIVMOD_CONGRUENCE);
    assert_eq!(report.diagnostics, []);
    let [ref rule] = *report.declarations[0].description.circuits.as_ref()
    else {
        panic!("one circuit rule")
    };
    let names = |ports: &[Name]| {
        ports
            .iter()
            .map(|port| port.as_ref().into())
            .collect::<Vec<alloc::string::String>>()
    };
    assert_eq!(
        names(&rule.body.outs),
        ["q", "r"],
        "one root per declared output, in order"
    );
    let [CircuitNode::Redex(_), CircuitNode::Frame(ref frame)] = *rule.body.nodes
    else {
        panic!("a redex and the many-out frame")
    };
    assert_eq!(
        names(&frame.outs),
        ["q", "r"],
        "the frame binds every port, in order"
    );
    assert_eq!(
        (rule.sphere.lhs.clone(), rule.sphere.rhs.clone()),
        (
            FreeTerm::op("divmod", [FreeTerm::var("m"), FreeTerm::var("n")]),
            FreeTerm::op("divmod", [FreeTerm::var("m′"), FreeTerm::var("n")]),
        ),
        "the frame leaving whole is its application"
    );
}

#[test]
fn one_port_of_a_many_out_frame_is_refused_by_the_derivation()
{
    let report = described(
        "theory Wide { sort Nat : Type; oper tee : (a : Nat) --> (b : Nat, c : Nat); rule split : (data x : Nat) ==> (z : Nat) { node : tee(x) --> (z, w); }; }",
    );
    assert!(
        report.diagnostics.iter().any(|diagnostic| matches!(
            diagnostic.fault,
            DescriptionFault::Signature(SignatureFault::Derivation(_))
        )),
        "{:?}",
        report.diagnostics
    );
    assert_eq!(report.declarations[0].description.circuits.as_ref(), []);
}

#[test]
fn a_two_output_operation_keeps_both_ports_in_order()
{
    let report = described(
        "theory Div { sort Nat : Type; oper divmod : (m : Nat, n : Nat) --> (q : Nat, r : Nat); }",
    );
    assert_eq!(report.diagnostics, []);
    let [ref operation] = *report.declarations[0].description.opers
    else {
        panic!("one operation")
    };
    assert_eq!(
        operation
            .arity
            .outputs
            .iter()
            .map(|port| port.name.as_ref())
            .collect::<Vec<_>>(),
        ["q", "r"]
    );
    assert_eq!(
        operation.arity.factors.as_ref(),
        [2_u32, 2_u32],
        "one monomial per output"
    );
}

#[test]
fn a_port_name_on_both_sides_is_two_ports()
{
    let report = described(
        "theory S { sort Nat : Type; sort Bit : Type; oper narrow : (v : Nat) --> (v : Bit); oper split : (b : Bit) --> (_ : Bit, _ : Bit); }",
    );
    assert_eq!(
        report
            .diagnostics
            .iter()
            .map(|diagnostic| diagnostic.fault.clone())
            .collect::<Vec<_>>(),
        [DescriptionFault::Signature(SignatureFault::SharedPort(
            "v".into()
        ))]
    );
    assert_eq!(
        report.declarations[0]
            .description
            .opers
            .iter()
            .map(|operation| operation.name.as_ref())
            .collect::<Vec<_>>(),
        ["split"],
        "two unnamed ports are two fresh wires"
    );
}

#[test]
fn a_reversible_map_is_reserved_and_an_equation_is_a_face()
{
    let source = "theory R { sort Bit : Type; oper negate : (b : Bit) <-> (c : Bit); rule involutive : (b : Bit) <=> (c : Bit); rule face : b <=> c; }";
    let report = described(source);
    let reserved: Vec<_> = report
        .diagnostics
        .iter()
        .filter(|diagnostic| {
            diagnostic.fault == DescriptionFault::Signature(SignatureFault::Reversible)
        })
        .filter_map(|diagnostic| {
            source.get(usize::from(diagnostic.span.start()) .. usize::from(diagnostic.span.end()))
        })
        .collect();
    assert_eq!(reserved, ["<->"]);
    assert!(
        report.declarations[0]
            .written
            .faces
            .iter()
            .any(|face| face.orientation == crate::description::written::RuleOrientation::Unpinned),
        "a term equation lowers unpinned"
    );
}

#[test]
fn the_cat_shape_laws_are_written_faces()
{
    let report = described(
        "theory CatShape {
  sort Ob : Type;
  sort Hom(dom: Ob, cod: Ob) : Type;
  oper id : (a : Ob) --> Hom(a, a);
  oper comp : (f : Hom(a, b), g : Hom(b, c)) --> Hom(a, c);
  rule unitL : comp(id(a), f) ==> f;
  rule unitR : comp(f, id(b)) ==> f;
  rule assoc : comp(comp(f, g), h) ==> comp(f, comp(g, h));
}",
    );
    assert_eq!(report.diagnostics, []);
    let description = &report.declarations[0].description;
    assert_eq!(
        description
            .sorts
            .iter()
            .map(|sort| (sort.name.as_ref(), sort.indices.len()))
            .collect::<Vec<_>>(),
        [("Ob", 0_usize), ("Hom", 2_usize)]
    );
    assert_eq!(
        description
            .opers
            .iter()
            .map(|operation| operation.name.as_ref())
            .collect::<Vec<_>>(),
        ["id", "comp"]
    );
    let op = |name: &str, args: [FreeTerm; 2]| FreeTerm::op(name, args);
    let id = |name: &str| FreeTerm::op("id", [FreeTerm::var(name)]);
    let var = FreeTerm::var;
    assert_eq!(
        description
            .rules
            .iter()
            .map(|face| (face.lhs.clone(), face.rhs.clone()))
            .collect::<Vec<_>>(),
        [
            (op("comp", [id("a"), var("f")]), var("f")),
            (op("comp", [var("f"), id("b")]), var("f")),
            (
                op("comp", [op("comp", [var("f"), var("g")]), var("h")]),
                op("comp", [var("f"), op("comp", [var("g"), var("h")])]),
            ),
        ],
        "each law is a face between the terms it writes, in order"
    );
    let cells = crate::desc_cells::elaborate_desc_cells(&report.declarations);
    assert_eq!(
        cells
            .diagnostics
            .iter()
            .map(|diagnostic| diagnostic.fault.clone())
            .collect::<Vec<_>>(),
        [const {
            crate::desc_cells::CellFault::Rule(
                gandr_theory_computads::ElaborateError::UnsupportedShape,
            )
        }; 3],
        "an operation application where the cut reads a value has no cell yet"
    );
}

#[test]
fn a_pinned_rewrite_endpoint_reads_as_a_variable()
{
    let report = described(
        "theory Labelled {
  sort Nat : Type;
  oper step : (i : Nat) --> (o : Nat);
  rule twice : (rule p : x ==> x′, data x : Nat) ==> (o : Nat) {
    node w1 : p(x) ==> (m);
    node w2 : step(m) --> (o);
  };
}",
    );
    assert_eq!(report.diagnostics, []);
    let [ref rule] = *report.declarations[0].description.circuits.as_ref()
    else {
        panic!("one circuit rule")
    };
    let [ref port] = *rule.ports.as_ref()
    else {
        panic!("one rewrite port")
    };
    assert_eq!(port.face, PortFace::Pinned {
        source: FreeTerm::var("x"),
        target: FreeTerm::var("x′"),
    });
    let fixed = described(
        "theory Labelled {
  sort Nat : Type;
  oper step : (i : Nat) --> (o : Nat);
  rule twice : (rule p : x ==> x, data x : Nat) ==> (o : Nat) {
    node w1 : p(x) ==> (m);
    node w2 : step(m) --> (o);
  };
}",
    );
    let [ref rule] = *fixed.declarations[0].description.circuits.as_ref()
    else {
        panic!("one circuit rule: {:?}", fixed.diagnostics)
    };
    let [ref port] = *rule.ports.as_ref()
    else {
        panic!("one rewrite port")
    };
    assert_eq!(
        port.face,
        PortFace::Pinned {
            source: FreeTerm::var("x"),
            target: FreeTerm::var("x"),
        },
        "an endpoint written twice is a variable unless a sort carries its name"
    );
}

#[test]
fn a_top_level_operation_declines_its_filler_by_name()
{
    let source =
        "oper split : (b : Bit) --> (_ : Bit, _ : Bit) {\n  node : tee(b) --> (_, _);\n}\n";
    let report = described(source);
    let [ref declaration] = *report.declarations.as_slice()
    else {
        panic!("the operation is a described declaration")
    };
    assert_eq!(
        source.get(
            usize::from(declaration.named.span.start())
                .. usize::from(declaration.named.span.end())
        ),
        Some("split")
    );
    assert_eq!(
        declaration.classifier,
        Maybe::Absent(family_classifier::Absent::Circuit)
    );
    assert_eq!(declaration.description.opers.as_ref(), []);
    assert_eq!(
        report
            .diagnostics
            .iter()
            .map(|diagnostic| (diagnostic.fault.clone(), diagnostic.span))
            .collect::<Vec<_>>(),
        [(
            DescriptionFault::Signature(SignatureFault::OperationFiller),
            declaration.at.span
        )]
    );
}

#[test]
fn theory_declines_and_malformed_wiring_are_refused_apart()
{
    let span = ByteSpan::new(0_usize.into(), 1_usize.into()).unwrap();
    let refusal = |fault| DescriptionDiagnostic { span, fault }.lowering_refusal();
    for fault in [SignatureFault::OperationFiller, SignatureFault::HigherCell] {
        assert!(matches!(
            refusal(DescriptionFault::Signature(fault)),
            crate::LoweringRefusal::OutOfFragment {
                boundary: crate::FragmentBoundary::Unadmitted,
                ..
            }
        ));
    }
    assert!(matches!(
        refusal(DescriptionFault::Signature(SignatureFault::Reversible)),
        crate::LoweringRefusal::OutOfFragment {
            boundary: crate::FragmentBoundary::Reserved,
            ..
        }
    ));
    let rule = ByteSpan::new(2_usize.into(), 3_usize.into()).unwrap();
    assert_eq!(
        refusal(DescriptionFault::Signature(SignatureFault::BareFeedback {
            rule
        })),
        crate::LoweringRefusal::BareFeedback { span, rule },
        "an unguarded feed is its own refusal, at its occurrence, naming its rule"
    );
    for fault in [
        SignatureFault::SharedPort("v".into()),
        SignatureFault::MultipleOutputs(OutputCount(2_usize)),
        SignatureFault::MissingOutput,
    ] {
        assert!(matches!(
            refusal(DescriptionFault::Signature(fault)),
            crate::LoweringRefusal::MalformedForm { .. }
        ));
    }
}

#[test]
fn a_refused_theory_block_states_its_refusal()
{
    let source = r#"@[ refuses("BareFeedback") ]
theory Wheel {
  sort Nat : Type;
  oper zip : (s : Nat, t : Nat) --> (u : Nat);
  rule spin : (data stream : Nat) ==> (out : Nat) {
    node : zip(stream, state) --> (out);
    feed : (out) --> (state);
  };
}
"#;
    let grammar = grammar();
    let tree = parse(&grammar, SourceText::from(source))
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
    let [ref wheel] = *module.declarations()
    else {
        panic!(
            "the refused block is one declaration, and mints no `Theory`: {:?}",
            module.declarations()
        )
    };
    assert_eq!(wheel.name().as_ref(), "Wheel");
    assert_eq!(
        wheel.role(),
        crate::module::Role::Declared,
        "its name is a declaration"
    );
    let text = |at: ByteSpan| source.get(usize::from(at.start()) .. usize::from(at.end()));
    assert!(
        matches!(
            wheel.outcome(),
            crate::DeclarationOutcome::Refused(crate::LoweringRefusal::BareFeedback { span, rule })
                if text(span) == Some("state")
                    && source.find("state)") == Some(usize::from(span.start()))
                    && text(rule) == Some("spin")
        ),
        "refused at the bare occurrence in `zip`, naming the rule: {:?}",
        wheel.outcome()
    );
    assert!(
        source
            .get(usize::from(wheel.span().start()) .. usize::from(wheel.span().end()))
            .is_some_and(|block| block.starts_with("theory Wheel")),
        "the declaration is the block, refused at its member"
    );
    let Maybe::Present(key) = wheel.definition()
    else {
        panic!("the block is the declaration's definition")
    };
    assert_eq!(
        module.attributes().entries(key).len(),
        1_usize,
        "the decoration states the block's refusal"
    );
}

#[test]
fn a_refused_top_level_operation_states_its_refusal()
{
    let source = "@[ refuses(\"OutOfFragment\") ]\noper split : (b : Bit) --> (_ : Bit, _ : Bit) {\n  node : tee(b) --> (_, _);\n}\n";
    let grammar = grammar();
    let tree = parse(&grammar, SourceText::from(source))
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
    let [ref split] = *module.declarations()
    else {
        panic!(
            "the refused operation is one declaration: {:?}",
            module.declarations()
        )
    };
    assert_eq!(split.name().as_ref(), "split");
    assert_eq!(
        split.role(),
        crate::module::Role::Held,
        "its name enters no namespace"
    );
    assert!(matches!(
        split.outcome(),
        crate::DeclarationOutcome::Refused(crate::LoweringRefusal::OutOfFragment {
            boundary: crate::FragmentBoundary::Unadmitted,
            ..
        })
    ));
    let Maybe::Present(key) = split.signature()
    else {
        panic!("the operation is the declaration's half")
    };
    assert_eq!(
        module.attributes().entries(key).len(),
        1_usize,
        "the decoration states the operation's refusal"
    );
}

#[test]
fn a_fed_port_no_node_reads_is_refused_at_the_feed()
{
    let source = "theory Wheel { sort Nat : Type; oper zip : (s : Nat, t : Nat) --> (u : Nat); rule spin : (data stream : Nat, data seed : Nat) ==> (out : Nat) { node : zip(stream, seed) --> (out); feed : (out) --> (state); }; }";
    let report = described(source);
    let [ref diagnostic] = *report.diagnostics.as_slice()
    else {
        panic!("one refusal: {:?}", report.diagnostics)
    };
    let DescriptionFault::Signature(SignatureFault::BareFeedback { rule }) = diagnostic.fault
    else {
        panic!("a bare feedback: {:?}", diagnostic.fault)
    };
    let text = |at: ByteSpan| source.get(usize::from(at.start()) .. usize::from(at.end()));
    assert_eq!(text(rule), Some("spin"));
    assert_eq!(
        (text(diagnostic.span), source.rfind("state")),
        (Some("state"), Some(usize::from(diagnostic.span.start()))),
        "with no occurrence to name, the feed's own port"
    );
    assert_eq!(report.declarations[0].description.circuits.as_ref(), []);
}

#[test]
fn an_observed_feed_is_kept_beside_its_cut_open_wiring()
{
    let report = described(
        "theory Wheel { sort Nat : Type; oper zip : (s : Nat, t : Nat) --> (u : Nat); obs emit : (s : Nat, x : Nat) --> (y : Nat); rule spin : (data stream : Nat) ==> (out : Nat) { node : emit(state, stream) --> (out); feed : (out) --> (state); }; }",
    );
    assert_eq!(report.diagnostics, []);
    let [ref theory] = *report.declarations.as_slice()
    else {
        panic!("one theory")
    };
    let [ref rule] = *theory.description.circuits.as_ref()
    else {
        panic!("one circuit")
    };
    assert_eq!(*rule.body.feeds, [CircuitFeed {
        source: "out".into(),
        port: "state".into(),
    }]);
    let read = FreeTerm::op("emit", [FreeTerm::var("state"), FreeTerm::var("stream")]);
    assert_eq!(
        (&rule.sphere.lhs, &rule.sphere.rhs),
        (&read, &read),
        "the fed port is a boundary variable of the cut-open wiring"
    );
    assert_eq!(
        crate::desc_cells::elaborate_desc_cells(&report.declarations).diagnostics,
        [],
        "the cut-open wiring is a cell the layer admits"
    );
    let Maybe::Present(ref presentation) = theory.presentation
    else {
        panic!("the block presents a theory")
    };
    let parts = presentation.value.decode().unwrap();
    assert_eq!(
        parts
            .operations
            .iter()
            .map(|operation| (operation.name.as_ref(), operation.kind))
            .collect::<Vec<_>>(),
        [
            ("zip", OperationKind::Operation),
            ("emit", OperationKind::Observation)
        ]
    );
}

#[test]
fn an_oper_filler_stays_declined_and_names_its_own_rung()
{
    let report = described(
        "theory Filled { sort Nat : Type; oper f : Nat --> Nat { node : f(x) --> (z); }; oper g : Nat --> Nat; }",
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
        described("theory Higher { sort Nat : Type; rule r : (data x : Nat) ==> (z : Nat); }");
    assert!(
        report.diagnostics.iter().any(|diagnostic| diagnostic.fault
            == DescriptionFault::Signature(SignatureFault::HigherCell))
    );
    assert_eq!(report.declarations[0].description.circuits.as_ref(), []);
}

#[test]
fn a_written_face_in_a_theory_block_declines_naming_the_block_form_that_holds_it()
{
    let source = "theory Written { sort Nat : Type; rule ident ==> add; oper neg : Nat --> Nat; }";
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
        Some("rule ident ==> add")
    );
    assert_eq!(
        report.declarations[0].description.opers[0].name.as_ref(),
        "neg"
    );
}

#[test]
fn a_data_spelled_theory_oper_declines_before_no_output_can_be_fabricated()
{
    let report =
        described("theory Old { sort Nat : Type; oper f(x : Nat) -> Nat; oper g : Nat --> Nat; }");
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
    let source = "theory Adder { sort Nat : Type; oper add : (Nat, Nat) --> Nat; rule ident ==> add; rule swap ==> mul; oper neg : Nat --> Nat; }";
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
    assert_eq!(refused, ["rule ident ==> add", "rule swap ==> mul"]);
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
        "theory Scope { sort Nat : Type; rule r : (data x : Nat) ==> (z : Nat) { node : f(x) ==> (z); }; oper f : Nat --> Nat; }",
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
        "theory Scope { sort Nat : Type; rule r : (data x : Nat) ==> (z : Nat) { node : missing(x) ==> (z); }; }",
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
        "theory Stray {\n  sort Nat : Type;\n  rule stray : (data x : Nat) ==> (z : Nat) {\n    node : mystery(x) --> (z);\n  };\n}\n",
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
        "theory NoPort {\n  sort Nat : Type;\n  oper f : (a : Nat) --> (b : Nat);\n\n  rule stray : (rule p : Nat ==> Nat, data x : Nat) ==> (z : Nat) {\n    node : p(x) ==> (m);\n    node : f(m) --> (z);\n  };\n}\n",
    );
    assert_eq!(report.diagnostics, []);
    assert_eq!(report.declarations[0].description.circuits.len(), 1);
}

#[test]
fn a_wiring_that_closes_a_cycle_earns_the_declaration_tables_refusal()
{
    let report = described(
        "theory Loop {\n  sort Nat : Type;\n  oper f : (a : Nat) --> (b : Nat);\n  oper g : (a : Nat) --> (b : Nat);\n\n  rule spin : (data x : Nat) ==> (z : Nat) {\n    node : f(w) --> (z);\n    node : g(z) --> (w);\n  };\n}\n",
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
        "theory Copy {\n  sort Nat : Type;\n  oper add : (l : Nat, r : Nat) --> (s : Nat);\n  rule copy2 : (data x : Nat) ==> (z : Nat) {\n    node : add(x, x) --> (z);\n  };\n}\n",
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
        "theory Doubling {\n  sort Nat : Type;\n  oper l : (a : Nat) --> (b : Nat);\n  oper r : (a : Nat) --> (b : Nat);\n  oper add : (a : Nat, b : Nat) --> (c : Nat);\n  rule blow : (data w0 : Nat) ==> (w12 : Nat) {\n",
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

/// The constructor tree `value` holds, each constructor by its name in `Theory`
/// and each name quoted.
///
/// # Specification
/// trivial.
fn spelled(
    arena: &gandr_core_term::CoreArena,
    value: gandr_core_term::ValueId,
) -> alloc::string::String
{
    /// One piece of the rendering.
    enum Piece
    {
        /// A value to render.
        Term(gandr_core_term::ValueId),
        /// Fixed text.
        Text(&'static str),
    }
    let mut out = alloc::string::String::new();
    let mut pending = alloc::vec![Piece::Term(value)];
    while let Some(piece) = pending.pop() {
        match piece {
            Piece::Text(text) => out.push_str(text),
            Piece::Term(id) => match arena.value(id) {
                Some(&gandr_core_term::Value::Constructor {
                    tag, ref fields, ..
                }) => {
                    out.push_str(
                        gandr_theory_levitation::THEORY_CONSTRUCTORS
                            .get(usize::from(tag))
                            .copied()
                            .unwrap_or("?"),
                    );
                    if fields.is_empty() {
                        continue;
                    }
                    pending.push(Piece::Text(")"));
                    for (at, &field) in fields.iter().enumerate().rev() {
                        pending.push(Piece::Term(field));
                        if at > 0 {
                            pending.push(Piece::Text(", "));
                        }
                    }
                    pending.push(Piece::Text("("));
                },
                Some(&gandr_core_term::Value::Literal(gandr_kernel_term::Literal::Text(
                    ref text,
                ))) => {
                    write!(out, "\"{}\"", AsRef::<str>::as_ref(text)).unwrap();
                },
                other => panic!("not a presentation node: {other:?}"),
            },
        }
    }
    out
}

#[test]
fn a_theory_block_defines_its_presentation()
{
    let grammar = grammar();
    let tree = parse(
        &grammar,
        SourceText::from(
            "theory Nat { sort Nat : Type; oper add : (Nat, Nat) --> Nat; }\ntheory Pointed { sort One : Type; oper pt : () --> (p : One); }\n",
        ),
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
    assert_eq!(module.descriptions().diagnostics, []);
    let [ref code, ref nat, ref pointed] = *module.declarations()
    else {
        panic!(
            "`Theory` once, then each theory: {:?}",
            module.declarations()
        )
    };
    assert_eq!(
        [code, nat, pointed]
            .map(|declaration| alloc::string::String::from(declaration.name().as_ref())),
        ["Theory", "Nat", "Pointed"]
    );
    let crate::DeclarationOutcome::Data(index) = code.outcome()
    else {
        panic!("`Theory` is a data family: {:?}", code.outcome())
    };
    let Maybe::Present(signature) = module.data(index)
    else {
        panic!("its signature is minted")
    };
    assert_eq!(
        signature
            .constructors()
            .iter()
            .map(alloc::vec::Vec::len)
            .collect::<alloc::vec::Vec<_>>(),
        [3, 0, 3, 4, 4, 4, 1, 2, 2, 1, 2, 3, 5, 4, 3, 4, 4, 6, 3],
        "each constructor's names, then its recursions"
    );
    let mut declarations = alloc::vec![gandr_core_checker::Declaration::data(
        code.constant(),
        alloc::sync::Arc::clone(signature),
        gandr_core_checker::OriginToken::from(0_usize),
    )];
    let mut bodies = alloc::vec::Vec::new();
    for (origin, theory) in [nat, pointed].into_iter().enumerate() {
        let crate::DeclarationOutcome::Completed {
            declared_type,
            body,
        } = theory.outcome()
        else {
            panic!("a theory defines a value: {:?}", theory.outcome())
        };
        assert_eq!(
            arena.value_type(declared_type),
            Some(&gandr_core_term::ValueType::Data {
                declaration: code.constant(),
                arguments: alloc::vec::Vec::new(),
            }),
            "of type `Theory`"
        );
        bodies.push(spelled(&arena, body));
        declarations.push(gandr_core_checker::Declaration::new(
            theory.constant(),
            Maybe::Present(declared_type),
            Maybe::Present(body),
            gandr_core_checker::OriginToken::from(origin.saturating_add(1)),
        ));
    }
    assert_eq!(
        bodies,
        [
            r#"Presents(Sort("Nat", End, End), Oper("add", Port("", "Nat", End, Port("", "Nat", End, End)), Port("", "Nat", End, End), End), End)"#,
            r#"Presents(Sort("One", End, End), Oper("pt", End, Port("p", "One", End, End), End), End)"#,
        ],
        "each value read node for node, an unnamed port at the empty name"
    );
    let report = gandr_core_checker::check_module(
        &mut gandr_core_checker::CheckingContext::new(
            &mut arena,
            gandr_core_checker::CheckBudget::DEFAULT,
        ),
        &declarations,
    );
    let verdicts: alloc::vec::Vec<_> = report
        .judged()
        .iter()
        .map(gandr_core_checker::Judged::verdict)
        .collect();
    assert!(
        matches!(verdicts.as_slice(), [
            gandr_core_checker::Verdict::Data,
            gandr_core_checker::Verdict::Checked { .. },
            gandr_core_checker::Verdict::Checked { .. }
        ]),
        "the checker forms `Theory` and checks each value at it: {verdicts:?}"
    );
}

#[test]
fn a_rule_bearing_theory_defines_its_presentation_with_its_laws()
{
    let grammar = grammar();
    let tree = parse(
        &grammar,
        SourceText::from(
            "theory CircleShape { sort Pt : Type; oper base : Pt; oper turn : (x : Pt) --> Pt; oper unturn : (x : Pt) --> Pt; rule turnUnturn : turn(unturn(x)) ==> x; rule unturnTurn : unturn(turn(x)) ==> x; }\ntheory CatShape { sort Ob : Type; sort Hom(dom: Ob, cod: Ob) : Type; oper id : (a : Ob) --> Hom(a,a); oper comp : (f : Hom(a, b), g : Hom(b, c)) --> Hom(a, c); rule unitL : comp(id(a), f) ==> f; }\n",
        ),
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
    let [ref code, ref circle, ref cat] = *module.declarations()
    else {
        panic!(
            "`Theory` once, then each theory: {:?}",
            module.declarations()
        )
    };
    let crate::DeclarationOutcome::Data(index) = code.outcome()
    else {
        panic!("`Theory` is a data family: {:?}", code.outcome())
    };
    let Maybe::Present(signature) = module.data(index)
    else {
        panic!("its signature is minted")
    };
    let crate::DeclarationOutcome::Completed {
        declared_type,
        body,
    } = circle.outcome()
    else {
        panic!(
            "laws over an unindexed sort are read over terms, so the block is clean: {:?}",
            circle.outcome()
        )
    };
    assert_eq!(
        spelled(&arena, body),
        r#"Presents(Sort("Pt", End, End), Oper("base", End, Port("", "Pt", End, End), Oper("turn", Port("x", "Pt", End, End), Port("", "Pt", End, End), Oper("unturn", Port("x", "Pt", End, End), Port("", "Pt", End, End), End))), Rule("turnUnturn", App("turn", Arg(App("unturn", Arg(Var("x"), End)), End)), Var("x"), Rule("unturnTurn", App("unturn", Arg(App("turn", Arg(Var("x"), End)), End)), Var("x"), Rank("turn", "1", Rank("unturn", "1", End)))))"#,
        "the value carries each law as a `Rule`, read node for node, then the rank of each operation a law applies"
    );
    assert!(
        matches!(
            cat.outcome(),
            crate::DeclarationOutcome::Refused(crate::LoweringRefusal::OutOfFragment { .. })
        ),
        "a law over an indexed sort stays declined, so its block defines no value: {:?}",
        cat.outcome()
    );
    let declarations = [
        gandr_core_checker::Declaration::data(
            code.constant(),
            alloc::sync::Arc::clone(signature),
            gandr_core_checker::OriginToken::from(0_usize),
        ),
        gandr_core_checker::Declaration::new(
            circle.constant(),
            Maybe::Present(declared_type),
            Maybe::Present(body),
            gandr_core_checker::OriginToken::from(1_usize),
        ),
    ];
    let report = gandr_core_checker::check_module(
        &mut gandr_core_checker::CheckingContext::new(
            &mut arena,
            gandr_core_checker::CheckBudget::DEFAULT,
        ),
        &declarations,
    );
    let verdicts: alloc::vec::Vec<_> = report
        .judged()
        .iter()
        .map(gandr_core_checker::Judged::verdict)
        .collect();
    assert!(
        matches!(verdicts.as_slice(), [
            gandr_core_checker::Verdict::Data,
            gandr_core_checker::Verdict::Checked { .. }
        ]),
        "the checker checks the rule-bearing value at `Theory`: {verdicts:?}"
    );
}

#[test]
fn the_description_is_read_off_the_value()
{
    let source = "theory CatShape {\n  sort Ob : Type;\n  sort Hom(dom: Ob, cod: Ob) : Type;\n  oper id : (a : Ob) --> Hom(a,a);\n  oper comp : (f : Hom(a, b), g : Hom(b, c)) --> Hom(a, c);\n  rule unitL : comp(id(a), f) ==> f;\n}\n";
    let report = described(source);
    assert_eq!(report.diagnostics, []);
    let [ref theory] = *report.declarations.as_slice()
    else {
        panic!("one theory")
    };
    let Maybe::Present(ref presentation) = theory.presentation
    else {
        panic!("a theory presents")
    };
    let parts = presentation.value.decode().unwrap();
    let description = &theory.description;
    assert_eq!(
        description
            .sorts
            .iter()
            .map(|sort| (sort.name.clone(), sort.indices.to_vec()))
            .collect::<Vec<_>>(),
        [
            (Name::from("Ob"), Vec::new()),
            (Name::from("Hom"), vec![
                SortIndex::new("dom", "Ob"),
                SortIndex::new("cod", "Ob")
            ]),
        ],
        "each sort the value codes, over its index telescope"
    );
    assert_eq!(
        description
            .opers
            .iter()
            .map(|operation| operation.name.clone())
            .collect::<Vec<_>>(),
        parts
            .operations
            .iter()
            .map(|operation| operation.name.clone())
            .collect::<Vec<_>>()
    );
    let [ref id, _] = *description.opers.as_ref()
    else {
        panic!("two operations")
    };
    assert_eq!(
        (id.arity.inputs.to_vec(), id.arity.outputs.to_vec()),
        (vec![SortRef::new("a", "Ob")], vec![SortRef::new(
            "_1",
            "Hom(a, a)"
        )]),
        "an unnamed port at its placeholder, its sort spelled from the value"
    );
    let [ref face] = *description.rules.as_ref()
    else {
        panic!("one face")
    };
    let [ref rule] = *parts.rules.as_slice()
    else {
        panic!("one rule")
    };
    let [span] = *presentation.placement.faces.as_slice()
    else {
        panic!("one placed face")
    };
    assert_eq!(
        (&face.lhs, &face.rhs, face.provenance),
        (&rule.left, &rule.right, surface_span(span)),
        "the face is the value's rule at its member's span"
    );
    assert!(
        source
            .get(usize::from(span.start()) .. usize::from(span.end()))
            .is_some_and(|member| member.starts_with("rule unitL"))
    );
    let mut short = presentation.clone();
    let _dropped = short.placement.faces.pop();
    assert_eq!(
        super::described(&short, theory.description.id.clone()),
        Err(crate::model::PresentationFault::Unplaced),
        "a rule the placement does not place"
    );
}

/// A single-output operation built by hand.
///
/// # Specification
/// trivial.
fn operation<Named>(
    name: Named,
    inputs: Vec<SortRef>,
    output: SortRef,
) -> OperDesc
where
    Named: Into<Name>,
{
    OperDesc::new(
        name.into(),
        BridgeArity::single_output(inputs, output),
        Attrs::empty(),
    )
}

/// A signature built by hand: sorts and operations, no rule.
///
/// # Specification
/// trivial.
fn signature<Named>(
    name: Named,
    sorts: Vec<SortDesc>,
    operations: Vec<OperDesc>,
) -> TheoryDesc<()>
where
    Named: Into<Name>,
{
    TheoryDesc::new(
        NominalId::new(NominalSerial::from(0_u64), name.into()),
        [],
        [],
        operations,
        [],
        DeclPolarity::Data,
        Attrs::empty(),
    )
    .with_sorts(sorts)
}

#[test]
fn a_rendered_signature_reparses_to_itself()
{
    // Pure λ-calculus syntax, Kaposi and Xie's identity-return signature and
    // the naturals: a representable sort with a binder over it, an indexed
    // representable sort with a binder at an index term, and a first-order
    // signature.
    let lambda = signature(
        "LC",
        vec![SortDesc::new("Tm", DeclPolarity::Data).representable()],
        vec![
            operation(
                "lam",
                vec![SortRef::new("t", "Tm").pi_plus([SortIndex::new("x", "Tm")])],
                SortRef::new("", "Tm"),
            ),
            operation(
                "app",
                vec![SortRef::new("t", "Tm"), SortRef::new("u", "Tm")],
                SortRef::new("", "Tm"),
            ),
        ],
    );
    let a = FreeTerm::var("a");
    let b = FreeTerm::var("b");
    let identity_return = signature(
        "IdentityReturn",
        vec![
            SortDesc::new("VTy", DeclPolarity::Data),
            SortDesc::new("CTy", DeclPolarity::Data),
            SortDesc::family("VTm", DeclPolarity::Data, [SortIndex::new("a", "VTy")])
                .representable(),
            SortDesc::family("CTm", DeclPolarity::Data, [SortIndex::new("b", "CTy")]),
        ],
        vec![
            operation("f", vec![SortRef::new("a", "VTy")], SortRef::new("", "CTy")),
            operation(
                "arrow",
                vec![SortRef::new("a", "VTy"), SortRef::new("b", "CTy")],
                SortRef::new("", "CTy"),
            ),
            operation(
                "ret",
                vec![
                    SortRef::new("a", "VTy"),
                    SortRef::new("t", "VTm").applied([a.clone()]),
                ],
                SortRef::new("", "CTm").applied([FreeTerm::op("f", [a.clone()])]),
            ),
            operation(
                "lam",
                vec![
                    SortRef::new("a", "VTy"),
                    SortRef::new("b", "CTy"),
                    SortRef::new("t", "CTm")
                        .applied([b.clone()])
                        .pi_plus([SortIndex::new("x", "VTm").applied([a.clone()])]),
                ],
                SortRef::new("", "CTm").applied([FreeTerm::op("arrow", [a, b])]),
            ),
        ],
    );
    let naturals = signature("Nat", vec![SortDesc::new("Nat", DeclPolarity::Data)], vec![
        operation("zero", vec![], SortRef::new("", "Nat")),
        operation(
            "succ",
            vec![SortRef::new("n", "Nat")],
            SortRef::new("", "Nat"),
        ),
    ]);
    // A square's cells over two of its sides, with a face of no point: the
    // shape renders first and its faces their points ascending.
    let points = |raw: &[usize]| {
        raw.iter()
            .copied()
            .map(ShapePoint::from)
            .collect::<Vec<_>>()
    };
    let square = signature("Cells", vec![SortDesc::new("A", DeclPolarity::Data)], vec![
        operation("cell", vec![], SortRef::new("", "A")),
    ])
    .with_shape(TheoryShape::new("Square", ShapeSize::from(4_usize), [
        ShapeFace::new("left", points(&[0, 2])),
        ShapeFace::new("right", points(&[3, 1])),
        ShapeFace::new("none", []),
    ]));
    // An unnamed port under a binder renders as `_ : pi+ (x : S) . T`, which
    // an input port does not read yet (#718); every port here is named or
    // binds nothing.
    for original in [lambda, identity_return, naturals, square] {
        let rendered = gandr_theory_levitation::serialize_desc(&original);
        let report = described(rendered.as_ref());
        assert_eq!(report.diagnostics, [], "{rendered:?} lowers whole");
        let [ref theory] = *report.declarations.as_slice()
        else {
            panic!("{rendered:?} declares one theory")
        };
        assert_eq!(
            gandr_theory_levitation::serialize_desc(&theory.description),
            rendered,
            "the reparsed description renders as the text it was read from"
        );
        let representability = |desc_sorts: &[SortDesc]| {
            desc_sorts
                .iter()
                .map(|sort| (sort.name.clone(), sort.representability))
                .collect::<Vec<_>>()
        };
        assert_eq!(
            representability(&theory.description.sorts),
            representability(&original.sorts),
            "every sort keeps its representability"
        );
        let binders = |opers: &[OperDesc]| {
            opers
                .iter()
                .flat_map(|oper| oper.arity.inputs.iter().chain(&oper.arity.outputs))
                .map(|port| port.bindings.to_vec())
                .collect::<Vec<_>>()
        };
        assert_eq!(
            binders(&theory.description.opers),
            binders(&original.opers),
            "every port keeps its binders, each domain a sort over its index terms"
        );
        assert_eq!(
            theory.description.shape, original.shape,
            "the shape keeps its size and its faces"
        );
    }
}

#[test]
fn a_face_past_its_shape_is_refused_by_name()
{
    for (source, kind, written) in [
        (
            "theory Cells { shape Square : 4 { far = {1, 4}; }; sort A : Type; }",
            gandr_theory_levitation::WfKind::FaceOutsideShape,
            "a face holding a point past its shape",
        ),
        (
            "theory Cells { shape Square : 4 { left = {0}; left = {2}; }; sort A : Type; }",
            gandr_theory_levitation::WfKind::DuplicateFaceName,
            "a face named twice",
        ),
    ] {
        let report = described(source);
        let [ref diagnostic] = *report.diagnostics.as_slice()
        else {
            panic!("{written}: one refusal: {:?}", report.diagnostics)
        };
        assert!(
            matches!(
                diagnostic.fault,
                DescriptionFault::IllFormed(ref reason) if reason.kind == kind
            ),
            "{written} is the description check's: {diagnostic:?}"
        );
    }
    let report =
        described("theory Cells { shape Square : 4 { }; shape Line : 2 { }; sort A : Type; }");
    let [ref diagnostic] = *report.diagnostics.as_slice()
    else {
        panic!("a signature states one shape: {:?}", report.diagnostics)
    };
    assert!(
        matches!(diagnostic.fault, DescriptionFault::Malformed),
        "a second shape is malformed: {diagnostic:?}"
    );
}

#[test]
fn the_corpus_signatures_evaluate_and_read_back_their_closed_terms()
{
    use gandr_theory_levitation::BindingJudgement;
    use gandr_theory_levitation::BindingTerm;
    use gandr_theory_levitation::SimplySorted;
    use gandr_theory_levitation::VariableIndex;

    // The corpus's own blocks, read as every `theory` block is: the naturals and
    // the λ-calculus are simply sorted, so both views serve their descriptions.
    let report = described(include_str!(
        "../../../../surface-corpus/fixture/model/desc/second-order-signatures.gandr"
    ));
    assert_eq!(report.diagnostics, [], "the corpus's blocks lower whole");
    let theory = |name: &str| {
        report
            .declarations
            .iter()
            .find(|declaration| declaration.description.id.name.as_ref() == name)
            .map_or_else(
                || panic!("the corpus declares `{name}`"),
                |declaration| &declaration.description,
            )
    };
    let both_views = |semantics: &SimplySorted<'_, _>, judgement: BindingJudgement| {
        let mut evaluation = semantics
            .evaluate(&judgement)
            .expect("a closed term evaluates");
        assert_eq!(
            evaluation.readback(),
            Ok(judgement.clone()),
            "reading the value back is the identity"
        );
        let first_order = semantics
            .to_first_order(&judgement)
            .expect("the first-order view");
        assert_eq!(
            semantics.from_first_order(&first_order),
            Ok(judgement),
            "the two views identify the term"
        );
    };
    let naturals = SimplySorted::new(theory("Nat")).expect("the naturals are simply sorted");
    let mut numeral = BindingTerm::operation(Name::from("zero"), []);
    for _ in 0_usize .. 3_usize {
        both_views(&naturals, BindingJudgement {
            context: Vec::new(),
            sort: Name::from("Nat"),
            term: numeral.clone(),
        });
        numeral = BindingTerm::operation(Name::from("succ"), [numeral]);
    }
    let lambda = SimplySorted::new(theory("Lambda")).expect("the λ-calculus is simply sorted");
    let bound = || BindingTerm::variable(VariableIndex::from(0_usize));
    let identity = BindingTerm::operation(Name::from("lam"), [bound()]);
    let doubling = BindingTerm::operation(Name::from("lam"), [BindingTerm::operation(
        Name::from("app"),
        [bound(), bound()],
    )]);
    for term in [
        identity.clone(),
        doubling.clone(),
        BindingTerm::operation(Name::from("app"), [doubling, identity]),
    ] {
        both_views(&lambda, BindingJudgement {
            context: Vec::new(),
            sort: Name::from("Tm"),
            term,
        });
    }
}

#[test]
fn a_binder_over_an_ordinary_sort_is_refused_by_name()
{
    let report =
        described("theory Bad { sort Tm : Type; oper lam : (t : pi+ (x : Tm) . Tm) --> Tm; }");
    let [ref diagnostic] = *report.diagnostics.as_slice()
    else {
        panic!("one refusal: {:?}", report.diagnostics)
    };
    assert!(
        matches!(
            diagnostic.fault,
            DescriptionFault::IllFormed(ref reason)
                if reason.kind == gandr_theory_levitation::WfKind::NonRepresentableBinder
        ),
        "a variable of an ordinary sort is not bound: {diagnostic:?}"
    );
    // A binder belongs to an operation's input port: a domain, a result, a
    // sort's index and a circuit's wire bind nothing.
    for (source, refused, written) in [
        (
            "theory Nested { sort Tm : Type+; oper lam : (t : pi+ (x : pi+ (y : Tm) . Tm) . Tm) --> Tm; }",
            "Repaired",
            "a binder whose domain binds",
        ),
        (
            "theory Result { sort Tm : Type+; oper lam : (t : Tm) --> (u : pi+ (x : Tm) . Tm); }",
            "Repaired",
            "a result that binds",
        ),
        (
            "theory Indexed { sort Tm : Type+; sort S(i : pi+ (x : Tm) . Tm) : Type; }",
            "Malformed",
            "an index that binds",
        ),
        (
            "theory Wired { sort Tm : Type+; oper f : (t : Tm) --> Tm; rule r : (t : pi+ (x : Tm) . Tm) ==> (u : Tm) { node n : f(t) --> (u); }; }",
            "Repaired",
            "a circuit port that binds",
        ),
    ] {
        let report = described(source);
        assert!(
            report.diagnostics.iter().any(|diagnostic| {
                (refused == "Repaired"
                    && matches!(diagnostic.fault, DescriptionFault::Repaired { .. }))
                    || (refused == "Malformed" && diagnostic.fault == DescriptionFault::Malformed)
            }),
            "{written} is refused as {refused}: {:?}",
            report.diagnostics
        );
    }
}

#[test]
fn a_member_with_no_judgment_head_declines_rather_than_vanishing()
{
    let source = "theory Broken {\n  sort Nat : Type;\n  rule ;\n}\n";
    let report = described(source);
    let [ref diagnostic] = *report.diagnostics.as_slice()
    else {
        panic!(
            "the repaired block is refused once: {:?}",
            report.diagnostics
        )
    };
    assert!(
        matches!(diagnostic.fault, DescriptionFault::Repaired { .. })
            && diagnostic.span.start()
                >= gandr_surface_syntax::ByteOffset::from(source.find("rule").unwrap()),
        "the parser's repair of the headless member is the block's refusal: {diagnostic:?}"
    );
}

#[test]
fn a_terminated_block_is_not_told_it_lacks_terminators()
{
    let report = described(
        "theory S {\n  sort Ob : Type;\n  sort Hom(dom : Ob, cod : Ob) : Type;\n  oper id : (a : Ob) --> Ob;\n}\n",
    );
    assert_eq!(report.diagnostics, []);
    assert_eq!(report.declarations[0].description.sorts.len(), 2);
    assert_eq!(report.declarations[0].description.opers.len(), 1);
}

#[test]
fn unseparated_members_are_declined_rather_than_dropped()
{
    let source = "theory S {\n  sort Ob : Type\n  sort Ar : Type\n}\n";
    let report = described(source);
    let [ref diagnostic] = *report.diagnostics.as_slice()
    else {
        panic!(
            "the repaired block is refused once: {:?}",
            report.diagnostics
        )
    };
    assert!(
        matches!(diagnostic.fault, DescriptionFault::Repaired { .. }),
        "the missing separator is the block's refusal: {diagnostic:?}"
    );
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
        "theory S {\n  sort Ob : Type;\n  sort Ar : Type;\n  oper f : (a : Ob) --> Ob;\n}\n",
    );
    assert_eq!(report.diagnostics, []);
    assert_eq!(report.declarations[0].description.sorts.len(), 2);
    assert_eq!(report.declarations[0].description.opers.len(), 1);
}

#[test]
fn an_unreadable_member_keeps_its_own_report()
{
    let source = "theory Adder {\n  sort Nat : Type;\n  oper add : (Nat, Nat) --> Nat;\n  rule ident ==> add;\n}\n";
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
        Some("rule ident ==> add")
    );
}

#[test]
fn a_coherence_between_composites_is_a_higher_cell()
{
    let source = "theory C {
  sort Ob : Type;
  oper id : (a : Ob) --> Ob;
  rule unitL : id(a) ==> a;
  rule triangle : (unitL(a) then unitL(a)) ==> unitL(a);
  rule face : (f) ==> (z : Ob) { node : id(f) --> (z); };
}";
    let report = described(source);
    let faults: Vec<_> = report
        .diagnostics
        .iter()
        .map(|diagnostic| {
            (
                diagnostic.fault.clone(),
                source
                    .get(usize::from(diagnostic.span.start()) .. usize::from(diagnostic.span.end()))
                    .is_some_and(|member| member.starts_with("rule triangle")),
            )
        })
        .collect();
    assert_eq!(
        faults,
        [
            (
                DescriptionFault::Signature(SignatureFault::HigherCell),
                true
            ),
            (
                DescriptionFault::Signature(SignatureFault::ExpressionEndpoint),
                false
            ),
        ],
        "the bodiless composite is a higher cell; a bodied expression endpoint stays refused"
    );
    assert_eq!(report.declarations[0].description.rules.len(), 1_usize);
}

/// The presentation the theory block `declaration` presents.
///
/// # Specification
/// trivial.
fn presented(declaration: &DescribedDeclaration) -> &Presentation
{
    let Maybe::Present(ref presentation) = declaration.presentation
    else {
        panic!("a theory presents")
    };
    presentation
}

#[test]
fn an_included_theory_is_the_extension_restricted()
{
    let source = "theory Mag {\n  sort M : Type;\n  oper mul : (x : M, y : M) --> M;\n  rule assoc : mul(mul(x, y), z) ==> mul(x, mul(y, z));\n}\ntheory Pointed {\n  include Mag;\n  oper one : () --> M;\n  rule unitL : mul(one(), x) ==> x;\n}\ntheory Comm {\n  include Mag;\n  oper zero : () --> M;\n}\ntheory Both {\n  include Pointed;\n  include Comm;\n}\n";
    let report = described(source);
    assert_eq!(report.diagnostics, []);
    let magma = presented(&report.declarations[0]).value.decode().unwrap();
    let pointed = presented(&report.declarations[1]);
    let [ref included] = *pointed.inclusions.as_slice()
    else {
        panic!("one inclusion")
    };
    assert_eq!(included.theory, report.declarations[0].description.id);
    let pointed_parts = pointed.value.decode().unwrap();
    assert_eq!(pointed_parts.restrict(&included.inclusion), magma);
    assert_eq!(
        report.declarations[1]
            .description
            .opers
            .iter()
            .map(|operation| operation.name.as_ref())
            .collect::<Vec<_>>(),
        ["mul", "one"],
        "the included operation comes first"
    );
    let [mul_tile, _] = *pointed.placement.operations.as_slice()
    else {
        panic!("two placed operations")
    };
    assert_eq!(
        mul_tile,
        presented(&report.declarations[0]).placement.operations[0],
        "an included member keeps the tile of the block that wrote it"
    );
    let both = presented(&report.declarations[3]);
    let both_parts = both.value.decode().unwrap();
    assert_eq!(both_parts.sorts.len(), 1, "the shared sort is one sort");
    assert_eq!(
        both_parts
            .operations
            .iter()
            .map(|operation| operation.name.as_ref())
            .collect::<Vec<_>>(),
        ["mul", "one", "zero"],
        "two inclusions meet along the magma they share"
    );
    assert_eq!(
        both.inclusions
            .iter()
            .map(|included| both_parts.restrict(&included.inclusion))
            .collect::<Vec<_>>(),
        [
            pointed_parts,
            presented(&report.declarations[2]).value.decode().unwrap()
        ]
    );
}

#[test]
fn an_include_is_refused_at_its_member()
{
    let source = "theory Pointed {\n  include Mag;\n  sort M : Type;\n}\ntheory Mag {\n  sort M : Type;\n  oper e : () --> M;\n}\ntheory Unary {\n  sort M : Type;\n  oper e : (x : M) --> M;\n}\ntheory Both {\n  include Mag;\n  include Unary;\n}\n";
    let report = described(source);
    let faults = report
        .diagnostics
        .iter()
        .map(|diagnostic| {
            (
                diagnostic.fault.clone(),
                source
                    .get(usize::from(diagnostic.span.start()) .. usize::from(diagnostic.span.end()))
                    .unwrap_or_default(),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(faults, [
        (
            DescriptionFault::Signature(SignatureFault::UnknownInclude(Name::from("Mag"))),
            "include Mag"
        ),
        (
            DescriptionFault::Signature(SignatureFault::IncludeClash(
                gandr_theory_levitation::IncludeClash::Operation(Name::from("e"))
            )),
            "include Unary"
        ),
    ]);
    assert_eq!(
        presented(&report.declarations[0])
            .value
            .decode()
            .unwrap()
            .sorts
            .len(),
        1,
        "a block included before its declaration is unknown, and the rest reads"
    );
}

/// #1225: a second theory including a pair another already joins leaves the
/// pair two incomparable joins, refused at the second naming the pair and
/// both; a block above both joins, and a diamond over one base, are not.
#[test]
fn two_joins_of_one_pair_are_refused_by_name()
{
    let source = "theory Pointed {\n  sort M : Type;\n  oper point : () --> M;\n}\ntheory Magma {\n  sort M : Type;\n  oper mul : (x : M, y : M) --> M;\n}\ntheory UnitalMagma {\n  include Pointed;\n  include Magma;\n}\ntheory MagmaWithUnit {\n  include Pointed;\n  include Magma;\n}\ntheory Above {\n  include UnitalMagma;\n}\n";
    let report = described(source);
    let faults = report
        .diagnostics
        .iter()
        .map(|diagnostic| {
            (
                diagnostic.fault.clone(),
                source
                    .get(usize::from(diagnostic.span.start()) .. usize::from(diagnostic.span.end()))
                    .unwrap_or_default()
                    .lines()
                    .next()
                    .unwrap_or_default(),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(faults, [(
        DescriptionFault::Signature(SignatureFault::AmbiguousJoin(JoinFault {
            pair: [Name::from("Pointed"), Name::from("Magma")],
            joins: Vec::from([Name::from("UnitalMagma"), Name::from("MagmaWithUnit")]),
        })),
        "theory MagmaWithUnit {"
    )]);
    let diamond = described(
        "theory Base {\n  sort M : Type;\n}\ntheory Left {\n  include Base;\n  oper l : () --> M;\n}\ntheory Right {\n  include Base;\n  oper r : () --> M;\n}\ntheory Both {\n  include Left;\n  include Right;\n}\n",
    );
    assert_eq!(diamond.diagnostics, [], "one join over one base reads");
}

#[test]
fn an_extension_generates_its_signature()
{
    let generated = described(
        "theory Gen {\n  shape Two : 2 {\n    left = {0};\n  };\n  sort Val : Type;\n  oper zero : Val;\n  oper one : Val;\n  ext Cell = Val on left is zero;\n}\n",
    );
    let written = described(
        "theory Gen {\n  shape Two : 2 {\n    left = {0};\n  };\n  sort Val : Type;\n  sort Cell : Type;\n  oper zero : Val;\n  oper one : Val;\n  oper inCell : (y1 : Val) --> Cell;\n  oper outCell0 : (e : Cell) --> Val;\n  oper outCell1 : (e : Cell) --> Val;\n  rule boundaryCell0 : outCell0(e) ==> zero();\n  rule betaCell1 : outCell1(inCell(y1)) ==> y1;\n  rule etaCell : inCell(outCell1(e)) ==> e;\n}\n",
    );
    assert_eq!(generated.diagnostics, []);
    assert_eq!(written.diagnostics, []);
    assert_eq!(
        presented(&generated.declarations[0])
            .value
            .decode()
            .unwrap(),
        presented(&written.declarations[0]).value.decode().unwrap(),
        "the member generates the signature written by hand"
    );
}

#[test]
fn an_extension_is_refused_by_name()
{
    let shaped = "  shape Two : 2 {\n    left = {0};\n    both = {0, 1};\n  };\n";
    let refused = |fault| DescriptionFault::Signature(SignatureFault::Extension(fault));
    for (shape, member, fault) in [
        (
            "",
            "ext Cell = Val on left is zero",
            refused(crate::circuit::ExtensionFault::Unshaped),
        ),
        (
            shaped,
            "ext Cell = Val on right is zero",
            refused(crate::circuit::ExtensionFault::UnknownFace(Name::from(
                "right",
            ))),
        ),
        (
            shaped,
            "ext Cell = Val on both is zero",
            refused(crate::circuit::ExtensionFault::CoveringFace(Name::from(
                "both",
            ))),
        ),
        (
            shaped,
            "ext Cell = Nat on left is zero",
            refused(crate::circuit::ExtensionFault::Carrier(Name::from("Nat"))),
        ),
        (
            shaped,
            "ext Cell = Val on left is twice",
            refused(crate::circuit::ExtensionFault::Boundary(Name::from(
                "twice",
            ))),
        ),
    ] {
        let source = format!(
            "theory T {{\n{shape}  sort Val : Type;\n  oper zero : Val;\n  oper twice : (v : Val) --> Val;\n  {member};\n}}\n"
        );
        let report = described(source.as_str());
        let faults = report
            .diagnostics
            .iter()
            .map(|diagnostic| {
                (
                    diagnostic.fault.clone(),
                    source
                        .get(
                            usize::from(diagnostic.span.start())
                                .. usize::from(diagnostic.span.end()),
                        )
                        .unwrap_or_default(),
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(faults, [(fault, member)], "{source}");
    }
}
