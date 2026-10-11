//! Description reader observations over the public grammar.

use gandr_surface_syntax::SourceText;
use gandr_theory_levitation::CodeView;
use gandr_theory_levitation::ValueTypeView;

use super::*;
use crate::fixture::grammar;
use crate::fixture::parsed;

#[test]
fn data_lowering_preserves_constructor_fields()
{
    let grammar = grammar();
    let source = r#"data List(a : Type) : Type {
        Nil : List(a);
        Cons : (head : a, tail : List(a)) --> List(a);
    }"#;
    let tree = parsed(&grammar, source.into());
    let report = elaborate_descriptions(&grammar, &tree).unwrap();
    assert_eq!(report.diagnostics, Vec::new());
    let [ref entry] = *report.declarations.as_slice()
    else {
        panic!("one family")
    };
    assert_eq!(entry.description.id.name.as_ref(), "List");
    let [ref nil, ref cons] = *entry.description.ctors.as_ref()
    else {
        panic!("two generators")
    };
    assert_eq!(nil.name.as_ref(), "Nil");
    assert!(matches!(nil.code.view(), CodeView::Unit));
    let CodeView::Prod(mut fields) = cons.code.view()
    else {
        panic!("two fields")
    };
    assert!(
        matches!(fields.next().unwrap().view(), CodeView::Field { ty, .. } if matches!(ty.view(), ValueTypeView::Param(name) if name.as_ref() == "a"))
    );
    assert!(
        matches!(fields.next().unwrap().view(), CodeView::Var(name) if name.as_ref() == "List")
    );
}

#[test]
fn codata_observations_preserve_their_codes()
{
    let grammar = grammar();
    let tree = parsed(
        &grammar,
        r#"codata Stream(a : Type) : Type {
        1 head : a;
        ω tail : Stream(a);
    }"#
        .into(),
    );
    let report = elaborate_descriptions(&grammar, &tree).unwrap();
    assert_eq!(report.diagnostics, Vec::new());
    let [ref entry] = *report.declarations.as_slice()
    else {
        panic!("one family")
    };
    assert_eq!(entry.description.polarity, DeclPolarity::Codata);
    let [ref head, ref tail] = *entry.description.ctors.as_ref()
    else {
        panic!("two observations")
    };
    assert_eq!(head.name.as_ref(), "head");
    assert!(matches!(head.code.view(), CodeView::Field {
        grade: DescriptionGrade::Finite(Multiplicity(1)),
        ..
    }));
    assert_eq!(tail.name.as_ref(), "tail");
    assert!(matches!(tail.code.view(), CodeView::Var(name) if name.as_ref() == "Stream"));
}

#[test]
fn operations_and_rules_preserve_their_boundaries()
{
    let grammar = grammar();
    let tree = parsed(
        &grammar,
        r#"data Nat : Type {
        Zero : Nat;
        Succ : Nat --> Nat;
        oper add(m : Nat, n : Nat) -> Nat;
        rule add(Zero, n) ==> n;
        rule add(Succ(m), n) ==> Succ(add(m, n));
    }"#
        .into(),
    );
    let report = elaborate_descriptions(&grammar, &tree).unwrap();
    assert_eq!(report.diagnostics, Vec::new());
    let [ref entry] = *report.declarations.as_slice()
    else {
        panic!("one family")
    };
    let [ref operation] = *entry.description.opers.as_ref()
    else {
        panic!("one operation")
    };
    assert_eq!(operation.name.as_ref(), "add");
    assert_eq!(
        operation
            .arity
            .inputs
            .iter()
            .map(|port| port.name.as_ref())
            .collect::<Vec<_>>(),
        ["m", "n"]
    );
    let [ref zero, ref succ] = *entry.description.rules.as_ref()
    else {
        panic!("two rules")
    };
    assert_eq!(
        zero.lhs,
        gandr_theory_levitation::FreeTerm::op("add", [
            gandr_theory_levitation::FreeTerm::ctor("Zero", []),
            gandr_theory_levitation::FreeTerm::var("n")
        ])
    );
    assert_eq!(zero.rhs, gandr_theory_levitation::FreeTerm::var("n"));
    assert_eq!(
        succ.vars
            .iter()
            .map(|variable| variable.var.as_ref())
            .collect::<Vec<_>>(),
        ["m", "n"]
    );
}

#[test]
fn native_data_keeps_telescope_and_nominal_heads()
{
    use gandr_core_checker::CheckBudget;
    use gandr_core_checker::CheckingContext;
    use gandr_core_checker::Declaration;
    use gandr_core_checker::OriginToken;
    use gandr_core_checker::Verdict;
    use gandr_core_checker::check_module;
    use gandr_core_term::CoreArena;
    use gandr_core_term::Value;
    use gandr_core_term::ValueType;
    use gandr_core_term::Zone;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::DeBruijnIndex;

    use crate::DeclarationOutcome;
    use crate::LoweringBudget;
    use crate::lower_module;
    use crate::namespace::Recognition;

    let grammar = grammar();
    let source = "data Box(a : Type) : Type { Vacant : Box(a); Packed : a --> Box(a); } def xs : Box(Integer);";
    let tree = parsed(&grammar, source.into());
    let mut arena = CoreArena::new();
    let preexisting = arena.value_unit();
    let module = lower_module(
        &grammar,
        &tree,
        &mut arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
    )
    .unwrap();
    assert_eq!(module.descriptions().diagnostics, Vec::new());
    let [ref family, ref xs] = *module.declarations()
    else {
        panic!("family and its consumer")
    };
    let DeclarationOutcome::Data(index) = family.outcome()
    else {
        panic!("native declaration")
    };
    let Maybe::Present(signature) = module.data(index)
    else {
        panic!("the module holds the family's signature")
    };
    let [ref vacant, ref packed] = *signature.constructors()
    else {
        panic!("two native tags")
    };
    assert_eq!(vacant, &Vec::new());
    let &[head] = packed.as_slice()
    else {
        panic!("one constructor field")
    };
    let Some(&ValueType::Element { code, .. }) = arena.value_type(head)
    else {
        panic!("parameter code")
    };
    assert_eq!(
        arena.value(code),
        Some(&Value::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(0_u32)
        })
    );
    let DeclarationOutcome::Uncompleted { declared_type } = xs.outcome()
    else {
        panic!("declared consumer")
    };
    let Some(&ValueType::Data {
        declaration,
        ref arguments,
    }) = arena.value_type(declared_type)
    else {
        panic!("nominal application")
    };
    assert_eq!(declaration, ConstantIndex::from(0_usize));
    let &[argument] = arguments.as_slice()
    else {
        panic!("one explicit type argument")
    };
    let Some(&Value::Quote(integer)) = arena.value(argument)
    else {
        panic!("quoted type argument")
    };
    assert_eq!(
        arena.value_type(integer),
        Some(&ValueType::Base(gandr_kernel_term::BaseType::Integer))
    );
    assert!(matches!(
        module.origins().value(preexisting),
        Maybe::Absent(_)
    ));
    let declarations = [
        Declaration::data(
            family.constant(),
            alloc::sync::Arc::clone(signature),
            OriginToken::from(0_usize),
        ),
        Declaration::new(
            xs.constant(),
            Maybe::Present(declared_type),
            Maybe::Absent(gandr_core_checker::body::Absent::Hole),
            OriginToken::from(1_usize),
        ),
    ];
    let report = check_module(
        &mut CheckingContext::new(&mut arena, CheckBudget::DEFAULT),
        &declarations,
    );
    let [ref first, ref second] = *report.judged()
    else {
        panic!("two judgments")
    };
    assert_eq!(first.verdict(), Verdict::Data);
    assert!(matches!(second.verdict(), Verdict::Owed(_)));
}

/// Read a declaration through the public parser and description route.
///
/// # Specification
/// - ensures: returns the report for exactly the supplied source.
/// - panics: the witness source must parse and use its own grammar.
///
/// # Adequacy
/// - hypothesis: L3 — distinct family names and member boundaries expose an
///   unrelated report.
/// - witness: `description::tests::the_data_corpus_fixture_elaborates_to_its_descriptions`
#[spec(ensures: |report| report.declarations.iter().all(|entry| entry.at.span.end() <= source.end()))]
fn elaborated(source: SourceText<'_>) -> DescriptionReport
{
    let grammar = grammar();
    let tree = gandr_surface_parser::parse(&grammar, source)
        .unwrap()
        .into_tree();
    elaborate_descriptions(&grammar, &tree).unwrap()
}

#[test]
fn the_data_corpus_fixture_elaborates_to_its_descriptions()
{
    let report = elaborated(SourceText::from(
        r#"
    data Color : Type { Red : Color; Green : Color; Blue : Color; }
    data Maybe(a : Type) : Type { None : Maybe(a); Some : (x : a) --> Maybe(a); }
    data Tree(a : Type) : Type { Leaf : Tree(a); Node : (l : Tree(a), x : a, r : Tree(a)) --> Tree(a); }
    data Vec(a : Type) : Nat -> Type { Nil : Vec(a, 0); Cons : (n : Nat, x : a, xs : Vec(a, n)) --> Vec(a, 1 + n); }
    data Empty : Type {}
        "#,
    ));
    assert_eq!(report.diagnostics, []);
    let actual: Vec<_> = report
        .declarations
        .iter()
        .map(|entry| {
            (
                entry.description.id.name.as_ref(),
                entry
                    .description
                    .ctors
                    .iter()
                    .map(|ctor| ctor.name.as_ref())
                    .collect::<Vec<_>>(),
            )
        })
        .collect();
    assert_eq!(actual, [
        ("Color", vec!["Red", "Green", "Blue"]),
        ("Maybe", vec!["None", "Some"]),
        ("Tree", vec!["Leaf", "Node"]),
        ("Vec", vec!["Nil", "Cons"]),
        ("Empty", vec![]),
    ]);
    let indexed = &report.declarations[3].description;
    assert_eq!(
        indexed
            .params
            .iter()
            .map(|parameter| parameter.name.as_ref())
            .collect::<Vec<_>>(),
        ["a"]
    );
    assert!(bool::from(indexed.is_recursive()));
}

#[test]
fn the_generator_ladder_elaborates_bare_sides_and_telescopes()
{
    let report = elaborated(SourceText::from(
        "data Nat : Type { Zero : Nat; Succ : Nat --> Nat; Pred : (n : Nat) --> Nat; }",
    ));
    assert_eq!(report.diagnostics, []);
    let [ref entry] = *report.declarations.as_slice()
    else {
        panic!("one family")
    };
    let [ref zero, ref succ, ref pred] = *entry.description.ctors.as_ref()
    else {
        panic!("three generators")
    };
    assert!(matches!(zero.code.view(), CodeView::Unit));
    assert!(matches!(succ.code.view(), CodeView::Var(name) if name.as_ref() == "Nat"));
    assert!(matches!(pred.code.view(), CodeView::Var(name) if name.as_ref() == "Nat"));
}

#[test]
fn a_declared_datatype_drives_the_generic_consumer_end_to_end()
{
    use gandr_theory_levitation::ConstructorTag;
    use gandr_theory_levitation::DescValue;
    use gandr_theory_levitation::Payload;
    use gandr_theory_levitation::generic_eq;
    let report = elaborated(SourceText::from(
        "data Maybe(a : Type) : Type { None : Maybe(a); Some : (x : a) --> Maybe(a); }",
    ));
    assert_eq!(report.diagnostics, []);
    let [ref entry] = *report.declarations.as_slice()
    else {
        panic!("one family")
    };
    let a = DescValue::new(ConstructorTag::from(1_usize), Payload::leaf(&b"a"[..]));
    let same = DescValue::new(ConstructorTag::from(1_usize), Payload::leaf(&b"a"[..]));
    let different = DescValue::new(ConstructorTag::from(1_usize), Payload::leaf(&b"b"[..]));
    let none = DescValue::new(ConstructorTag::from(0_usize), Payload::unit());
    assert!(bool::from(generic_eq(&entry.description, &a, &same)));
    assert!(!bool::from(generic_eq(&entry.description, &a, &different)));
    assert!(!bool::from(generic_eq(&entry.description, &a, &none)));
}

#[test]
fn description_wrapper_boundaries_stay_observable_to_pipeline_consumers()
{
    use gandr_theory_levitation::ConstructorTag;
    use gandr_theory_levitation::DescValue;
    use gandr_theory_levitation::Payload;
    use gandr_theory_levitation::generic_eq;
    use gandr_theory_levitation::serialize_desc;
    let report = elaborated(SourceText::from(
        "data Maybe(a : Type) : Type { None : Maybe(a); Some : (x : a) --> Maybe(a); }",
    ));
    let [ref entry] = *report.declarations.as_slice()
    else {
        panic!("one family")
    };
    let none = DescValue::new(ConstructorTag::from(0_usize), Payload::unit());
    assert_eq!(entry.description.id.name.as_ref(), "Maybe");
    assert_eq!(
        serialize_desc(&entry.description).as_ref(),
        "sign Maybe(a) { sort Maybe : Type; }"
    );
    assert!(bool::from(generic_eq(&entry.description, &none, &none)));
}

#[test]
fn operation_and_rule_members_elaborate_with_arities_and_faces()
{
    let report = elaborated(SourceText::from(
        r#"
    data NatOp : Type { Zero : NatOp; Succ : (n : NatOp) --> NatOp; oper add(m : NatOp, n : NatOp) -> NatOp; }
    data NatRule : Type { Zero : NatRule; Succ : (n : NatRule) --> NatRule; rule id(Zero) ==> Zero; }
    data NatDiv : Type { Zero : NatDiv; oper divmod(m : NatDiv, n : NatDiv) -> (q : NatDiv, r : NatDiv); }
        "#,
    ));
    let [ref operation, ref rule, ref division] = *report.declarations.as_slice()
    else {
        panic!("three declarations")
    };
    let [ref add] = *operation.description.opers.as_ref()
    else {
        panic!("one operation")
    };
    assert_eq!(add.name.as_ref(), "add");
    assert_eq!(
        add.arity
            .inputs
            .iter()
            .map(|port| port.name.as_ref())
            .collect::<Vec<_>>(),
        ["m", "n"]
    );
    let [ref face] = *rule.description.rules.as_ref()
    else {
        panic!("one face")
    };
    assert_eq!(
        face.lhs,
        gandr_theory_levitation::FreeTerm::op("id", [gandr_theory_levitation::FreeTerm::ctor(
            "Zero",
            []
        )])
    );
    assert_eq!(
        face.rhs,
        gandr_theory_levitation::FreeTerm::ctor("Zero", [])
    );
    let [ref divmod] = *division.description.opers.as_ref()
    else {
        panic!("one multi-output operation")
    };
    assert_eq!(
        divmod
            .arity
            .outputs
            .iter()
            .map(|port| (port.name.as_ref(), port.sort.as_ref()))
            .collect::<Vec<_>>(),
        [("q", "NatDiv"), ("r", "NatDiv")]
    );
}

#[test]
fn the_ruled_face_arrow_elaborates_and_the_retired_one_declines_with_its_respelling()
{
    let ruled = elaborated(SourceText::from(
        "data NatFace : Type { Zero : NatFace; oper id(x : NatFace) -> NatFace; rule id(Zero) ==> Zero; }",
    ));
    assert_eq!(ruled.diagnostics, []);
    assert_eq!(ruled.declarations[0].description.rules.len(), 1);
    let source = "data NatFace : Type { Zero : NatFace; oper id(x : NatFace) -> NatFace; rule id(Zero) ~> Zero; }";
    let retired = elaborated(SourceText::from(source));
    assert!(retired.declarations[0].description.rules.is_empty());
    let [ref diagnostic] = *retired.diagnostics.as_slice()
    else {
        panic!("one arrow refusal")
    };
    assert_eq!(diagnostic.fault, DescriptionFault::RetiredRuleArrow);
    assert_eq!(
        source.get(usize::from(diagnostic.span.start()) .. usize::from(diagnostic.span.end())),
        Some("~>")
    );
}

#[test]
fn the_retired_op_member_lead_declines_with_its_respelling()
{
    let source =
        "data NatRetired : Type { Zero : NatRetired; op stale(x : NatRetired) -> NatRetired; }";
    let report = elaborated(SourceText::from(source));
    assert!(report.declarations[0].description.opers.is_empty());
    let [ref diagnostic] = *report.diagnostics.as_slice()
    else {
        panic!("one retired member")
    };
    assert_eq!(diagnostic.fault, DescriptionFault::RetiredOperation);
    assert_eq!(
        source.get(usize::from(diagnostic.span.start()) .. usize::from(diagnostic.span.end())),
        Some("op stale(x : NatRetired) -> NatRetired")
    );
}

#[test]
fn codata_declarations_elaborate_with_codata_polarity()
{
    let report = elaborated(SourceText::from(
        "codata Stream(a : Type) : Type { head : a; tail : Stream(a); }",
    ));
    assert_eq!(report.diagnostics, []);
    let [ref entry] = *report.declarations.as_slice()
    else {
        panic!("one codata family")
    };
    assert_eq!(entry.description.polarity, DeclPolarity::Codata);
    let [ref head, ref tail] = *entry.description.ctors.as_ref()
    else {
        panic!("two observations")
    };
    assert_eq!([head.name.as_ref(), tail.name.as_ref()], ["head", "tail"]);
    assert!(matches!(head.code.view(), CodeView::Field { .. }));
    assert!(matches!(tail.code.view(), CodeView::Var(name) if name.as_ref() == "Stream"));
}

#[test]
fn a_higher_order_field_is_declined_at_elaboration()
{
    let source = "data Cell(a : Type) : Type { Mk : (get : a -> a) --> Cell(a); }";
    let report = elaborated(SourceText::from(source));
    assert!(report.declarations[0].description.ctors.is_empty());
    let [ref diagnostic] = *report.diagnostics.as_slice()
    else {
        panic!("one higher-order field")
    };
    assert_eq!(diagnostic.fault, DescriptionFault::HigherOrderField);
    assert_eq!(
        source.get(usize::from(diagnostic.span.start()) .. usize::from(diagnostic.span.end())),
        Some("a -> a")
    );
}

#[test]
fn the_declined_metadata_golden_is_declined()
{
    let report = elaborated(SourceText::from(
        "data Declared : Type { Mk : Declared [variance]; }",
    ));
    let [ref diagnostic] = *report.diagnostics.as_slice()
    else {
        panic!("one reserved attribute")
    };
    assert!(
        matches!(diagnostic.fault, DescriptionFault::IllFormed(ref reason) if reason.kind == gandr_theory_levitation::WfKind::DeclaresDerivedMetadata)
    );
}

#[test]
fn a_bare_parameter_head_declines_the_whole_declaration_with_its_respelling()
{
    let report = elaborated(SourceText::from("data Maybe(a) { None : Maybe(a); }"));
    assert!(report.declarations.is_empty());
    assert!(
        report
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.fault == DescriptionFault::FamilyHead)
    );
}

#[test]
fn a_missing_head_annotation_declines_the_whole_declaration_with_its_respelling()
{
    let report = elaborated(SourceText::from("data Color { Red : Color; }"));
    assert!(report.declarations.is_empty());
    assert!(
        report
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.fault == DescriptionFault::FamilyHead)
    );
}

#[test]
fn the_retired_field_tuple_member_declines_with_the_generator_respelling()
{
    let report = elaborated(SourceText::from(
        "data Maybe(a : Type) : Type { None, Some(x : a) }",
    ));
    assert!(report.declarations[0].description.ctors.is_empty());
    assert_eq!(
        report
            .diagnostics
            .iter()
            .map(|diagnostic| &diagnostic.fault)
            .collect::<Vec<_>>(),
        [
            &DescriptionFault::GeneratorJudgment,
            &DescriptionFault::GeneratorJudgment
        ]
    );
}

#[test]
fn an_instantiated_result_head_declines_as_uninferable()
{
    let source = "data Bad(a : Type) : Type { Mk : Bad(Integer); }";
    let report = elaborated(SourceText::from(source));
    assert!(report.declarations[0].description.ctors.is_empty());
    let [ref diagnostic] = *report.diagnostics.as_slice()
    else {
        panic!("one instantiated parameter")
    };
    assert_eq!(diagnostic.fault, DescriptionFault::NonUniformResult);
    assert_eq!(
        source.get(usize::from(diagnostic.span.start()) .. usize::from(diagnostic.span.end())),
        Some("Bad(Integer)")
    );
}

#[test]
fn a_result_head_of_the_wrong_arity_declines()
{
    let report = elaborated(SourceText::from("data Bad : Type { Mk : Bad(0); }"));
    assert!(report.declarations[0].description.ctors.is_empty());
    let [ref diagnostic] = *report.diagnostics.as_slice()
    else {
        panic!("one arity refusal")
    };
    assert_eq!(diagnostic.fault, DescriptionFault::NonUniformResult);
}

#[test]
fn a_bare_result_head_over_a_parameterized_family_declines()
{
    let report = elaborated(SourceText::from("data Bad(a : Type) : Type { Mk : Bad; }"));
    assert!(report.declarations[0].description.ctors.is_empty());
    let [ref diagnostic] = *report.diagnostics.as_slice()
    else {
        panic!("one missing parameter")
    };
    assert_eq!(diagnostic.fault, DescriptionFault::NonUniformResult);
}

#[test]
fn a_foreign_result_head_declines()
{
    let report = elaborated(SourceText::from("data Bad : Type { Mk : Other; }"));
    assert!(report.declarations[0].description.ctors.is_empty());
    let [ref diagnostic] = *report.diagnostics.as_slice()
    else {
        panic!("one foreign result")
    };
    assert_eq!(diagnostic.fault, DescriptionFault::NonUniformResult);
}

#[test]
fn a_constructor_led_member_of_a_codata_block_declines()
{
    let data = elaborated(SourceText::from("data Boxed : Type { Mk : Boxed; }"));
    assert_eq!(data.diagnostics, []);
    assert_eq!(
        data.declarations[0]
            .description
            .ctors
            .iter()
            .map(|ctor| ctor.name.as_ref())
            .collect::<Vec<_>>(),
        ["Mk"]
    );
    let report = elaborated(SourceText::from("codata Boxed : Type { Mk : Boxed; }"));
    assert!(report.declarations[0].description.ctors.is_empty());
    assert!(report.diagnostics.iter().any(|diagnostic| matches!(
        diagnostic.fault,
        DescriptionFault::MemberPolarity | DescriptionFault::Malformed
    )));
}

#[test]
fn a_codata_oper_declines_without_swallowing_observation_and_rule_siblings()
{
    let source = "codata S : Type { head : Nat; oper tail(s : S) -> S; rule head ==> head; }";
    let report = elaborated(SourceText::from(source));
    let [ref entry] = *report.declarations.as_slice()
    else {
        panic!("one codata family")
    };
    assert_eq!(
        entry
            .description
            .ctors
            .iter()
            .map(|ctor| ctor.name.as_ref())
            .collect::<Vec<_>>(),
        ["head"]
    );
    assert_eq!(entry.description.rules.len(), 1);
    assert!(entry.description.opers.is_empty());
    let [ref diagnostic] = *report.diagnostics.as_slice()
    else {
        panic!("one member-local refusal")
    };
    assert_eq!(diagnostic.fault, DescriptionFault::MemberPolarity);
    assert_eq!(
        source.get(usize::from(diagnostic.span.start()) .. usize::from(diagnostic.span.end())),
        Some("oper tail(s : S) -> S")
    );
}

#[test]
fn member_refusals_keep_their_spans_and_other_declarations()
{
    use crate::DeclarationOutcome;
    use crate::LoweringBudget;
    use crate::lower_module;
    use crate::namespace::Recognition;
    let grammar = grammar();
    let source = "data Flag : Type { Off : Flag; rule bad(x) ~> x; On : Flag; } def later = 7;";
    let tree = parsed(&grammar, source.into());
    let mut arena = gandr_core_term::CoreArena::new();
    let module = lower_module(
        &grammar,
        &tree,
        &mut arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
    )
    .unwrap();
    let [ref family, ref refused, ref later] = *module.declarations()
    else {
        panic!("family, held member refusal and later declaration")
    };
    let DeclarationOutcome::Data(index) = family.outcome()
    else {
        panic!("readable generators remain native")
    };
    let Maybe::Present(signature) = module.data(index)
    else {
        panic!("the module holds the family's signature")
    };
    assert_eq!(signature.constructors(), [vec![], vec![]]);
    let DeclarationOutcome::Refused(refusal) = refused.outcome()
    else {
        panic!("the member refusal reaches consumers")
    };
    let Maybe::Present(span) = refusal.span()
    else {
        panic!("located member")
    };
    assert_eq!(
        source.get(usize::from(span.start()) .. usize::from(span.end())),
        Some("~>")
    );
    assert!(matches!(later.outcome(), DeclarationOutcome::Bodied { .. }));
    assert_eq!(later.name().as_ref(), "later");
}

#[test]
fn codata_is_refused_by_the_decoder_and_data_beside_it_is_native()
{
    use gandr_core_term::description::DecodeError;

    use crate::DeclarationOutcome;
    use crate::LoweringBudget;
    use crate::lower_module;
    use crate::namespace::Recognition;
    let grammar = grammar();
    let source = "data Flag : Type { Off : Flag; On : Flag; }\ncodata Stream(a : Type) : Type { head : a; tail : Stream(a); }\ndef later = 7;";
    let tree = parsed(&grammar, source.into());
    let mut arena = gandr_core_term::CoreArena::new();
    let module = lower_module(
        &grammar,
        &tree,
        &mut arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
    )
    .unwrap();
    let [ref flag, ref stream, ref later] = *module.declarations()
    else {
        panic!("data, codata and a later declaration")
    };
    let DeclarationOutcome::Data(index) = flag.outcome()
    else {
        panic!("the data family is read natively")
    };
    let Maybe::Present(signature) = module.data(index)
    else {
        panic!("the module holds the data family's signature")
    };
    assert_eq!(signature.constructors(), [vec![], vec![]]);
    assert_eq!(stream.name().as_ref(), "Stream");
    let DeclarationOutcome::Refused(refusal) = stream.outcome()
    else {
        panic!("the codata family is refused")
    };
    let Maybe::Present(span) = refusal.span()
    else {
        panic!("located family")
    };
    assert_eq!(
        source.get(usize::from(span.start()) .. usize::from(span.end())),
        Some("codata Stream(a : Type) : Type { head : a; tail : Stream(a); }")
    );
    assert_eq!(
        module
            .descriptions()
            .diagnostics
            .iter()
            .map(|diagnostic| &diagnostic.fault)
            .collect::<Vec<_>>(),
        [&DescriptionFault::NativeDecode(DecodeError::CodataNu)]
    );
    assert!(matches!(later.outcome(), DeclarationOutcome::Bodied { .. }));
}

#[test]
fn an_attribute_block_decorates_the_codata_declaration_after_it()
{
    use quenchant_shape::shape::Maybe;

    use crate::DeclarationOutcome;
    use crate::LoweringBudget;
    use crate::fixture::registered;
    use crate::lower_module;
    use crate::namespace::Recognition;
    use crate::resolve::SurfaceName;
    let grammar = grammar();
    let source = "@[ refuses(\"OutOfFragment\") ]\ncodata Stream(a : Type) : Type { head : a; tail : Stream(a); }\ndef later = 7;";
    let tree = parsed(&grammar, source.into());
    let mut arena = gandr_core_term::CoreArena::new();
    let module = lower_module(
        &grammar,
        &tree,
        &mut arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
    )
    .unwrap();
    let [ref stream, ref later] = *module.declarations()
    else {
        panic!("the codata family and the later declaration are declared")
    };
    assert!(matches!(stream.outcome(), DeclarationOutcome::Refused(_)));
    let Maybe::Present(written) = stream.signature()
    else {
        panic!("the codata family keeps its digest")
    };
    let [ref entry] = *module.attributes().entries(written)
    else {
        panic!("one attribute is filed under the codata family")
    };
    assert_eq!(entry.name(), registered(SurfaceName::from("refuses")));
    assert!(matches!(later.outcome(), DeclarationOutcome::Bodied { .. }));
}

#[test]
fn parameterized_observations_retain_both_port_boundaries()
{
    use gandr_theory_levitation::SortRef;
    let report = elaborated(SourceText::from(
        "codata Fun(a : Type, b : Type) : Type { get : b; ap(x : a) : b; }",
    ));
    assert_eq!(report.diagnostics, []);
    let [ref entry] = *report.declarations.as_slice()
    else {
        panic!("one codata family")
    };
    assert_eq!(entry.description.polarity, DeclPolarity::Codata);
    assert_eq!(
        entry
            .description
            .ctors
            .iter()
            .map(|ctor| ctor.name.as_ref())
            .collect::<Vec<_>>(),
        ["get"]
    );
    let [ref observation] = *entry.description.opers.as_ref()
    else {
        panic!("one parameterized observation")
    };
    assert_eq!(observation.name.as_ref(), "ap");
    assert_eq!(observation.arity.inputs.as_ref(), [SortRef::new("x", "a")]);
    assert_eq!(observation.arity.outputs.as_ref(), [SortRef::new(
        "ap", "b"
    )]);
}
