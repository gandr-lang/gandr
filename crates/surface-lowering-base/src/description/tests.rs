//! Description reader observations over the public grammar.

use alloc::string::String;

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
    let source = include_str!("tests/fixtures/data-lowering-preserves-constructor-fields.gandr");
    let tree = parsed(&grammar, source.into());
    let report = elaborate_descriptions(&grammar, &tree, &Unit::single()).unwrap();
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

/// #1295: a constructor field written at grade `1` keeps that grade in its
/// code, and one at `ω` keeps `ω`.
#[test]
fn a_graded_field_keeps_its_grade_in_the_code_1295()
{
    let grammar = grammar();
    let source =
        include_str!("tests/fixtures/a-graded-field-keeps-its-grade-in-the-code-1295.gandr");
    let tree = parsed(&grammar, source.into());
    let report = elaborate_descriptions(&grammar, &tree, &Unit::single()).unwrap();
    assert_eq!(report.diagnostics, Vec::new());
    let [ref entry] = *report.declarations.as_slice()
    else {
        panic!("one family")
    };
    let [ref both] = *entry.description.ctors.as_ref()
    else {
        panic!("one generator")
    };
    let CodeView::Prod(mut fields) = both.code.view()
    else {
        panic!("two fields")
    };
    assert!(
        matches!(fields.next().unwrap().view(), CodeView::Field { grade, .. }
        if *grade == DescriptionGrade::Finite(Multiplicity::from(1_u64)))
    );
    assert!(matches!(fields.next().unwrap().view(), CodeView::Field {
        grade: DescriptionGrade::Omega,
        ..
    }));
}

#[test]
fn codata_observations_preserve_their_codes()
{
    let grammar = grammar();
    let tree = parsed(
        &grammar,
        include_str!("tests/fixtures/codata-observations-preserve-their-codes-tree.gandr").into(),
    );
    let report = elaborate_descriptions(&grammar, &tree, &Unit::single()).unwrap();
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
    assert!(matches!(head.code.view(), CodeView::Field { grade, .. }
        if *grade == DescriptionGrade::Finite(Multiplicity::from(1_u64))));
    assert_eq!(tail.name.as_ref(), "tail");
    assert!(matches!(tail.code.view(), CodeView::Var(name) if name.as_ref() == "Stream"));
}

#[test]
fn operations_and_rules_preserve_their_boundaries()
{
    let grammar = grammar();
    let tree = parsed(
        &grammar,
        include_str!("tests/fixtures/operations-and-rules-preserve-their-boundaries-tree.gandr")
            .into(),
    );
    let report = elaborate_descriptions(&grammar, &tree, &Unit::single()).unwrap();
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
    elaborate_descriptions(&grammar, &tree, &Unit::single()).unwrap()
}

#[test]
fn the_data_corpus_fixture_elaborates_to_its_descriptions()
{
    let report = elaborated(SourceText::from(include_str!(
        "tests/fixtures/the-data-corpus-fixture-elaborates-to-its-descriptions-report.gandr"
    )));
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
        "data Nat : Type where { | Zero : Nat | Succ : (Nat) --> Nat | Pred : (n : Nat) --> Nat }",
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
        "data Maybe(a : Type) : Type where { | None : Maybe(a) | Some : (x : a) --> Maybe(a) }",
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
        "data Maybe(a : Type) : Type where { | None : Maybe(a) | Some : (x : a) --> Maybe(a) }",
    ));
    let [ref entry] = *report.declarations.as_slice()
    else {
        panic!("one family")
    };
    let none = DescValue::new(ConstructorTag::from(0_usize), Payload::unit());
    assert_eq!(entry.description.id.name.as_ref(), "Maybe");
    assert_eq!(
        serialize_desc(&entry.description).as_ref(),
        "theory Maybe(a) where { sort Maybe : Type; }"
    );
    assert!(bool::from(generic_eq(&entry.description, &none, &none)));
}

#[test]
fn operation_and_rule_members_elaborate_with_arities_and_faces()
{
    let report = elaborated(SourceText::from(include_str!(
        "tests/fixtures/operation-and-rule-members-elaborate-with-arities-and-faces-report.gandr"
    )));
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
fn a_parenthesized_result_list_reads_as_a_results_tuple()
{
    use gandr_theory_levitation::FreeTerm;
    let report = elaborated(SourceText::from(
        "data NatDiv : Type where { | Zero : NatDiv oper divmod : (m : NatDiv, n : NatDiv) --> (q : NatDiv, r : NatDiv); rule : divmod m Zero ==> (Zero, m); rule : divmod Zero n ==> (divmod n (n)); }",
    ));
    assert_eq!(report.diagnostics, []);
    let [ref delivered, ref grouped] = *report.declarations[0].description.rules
    else {
        panic!("two faces")
    };
    assert_eq!(
        delivered.rhs,
        FreeTerm::results([FreeTerm::ctor("Zero", []), FreeTerm::var("m")]),
        "two components in order are the results tuple"
    );
    assert_eq!(
        grouped.rhs,
        FreeTerm::op("divmod", [FreeTerm::var("n"), FreeTerm::var("n")]),
        "one parenthesized component is that component"
    );
}

#[test]
fn the_ruled_face_arrow_elaborates_and_the_retired_one_declines_with_its_respelling()
{
    let ruled = elaborated(SourceText::from(
        "data NatFace : Type where { | Zero : NatFace oper id : (x : NatFace) --> NatFace; rule : id Zero ==> Zero; }",
    ));
    assert_eq!(ruled.diagnostics, []);
    assert_eq!(ruled.declarations[0].description.rules.len(), 1);
    let source = "data NatFace : Type where { | Zero : NatFace oper id : (x : NatFace) --> NatFace; rule : id Zero ~> Zero; }";
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
fn an_equation_states_no_direction()
{
    let report = elaborated(SourceText::from(
        "data NatEq : Type where { | Zero : NatEq oper id : (x : NatEq) --> NatEq; rule : id Zero <=> Zero; }",
    ));
    assert_eq!(report.diagnostics, []);
    let rules: Vec<_> = report.declarations[0].rules().collect();
    let [ref rule] = *rules.as_slice()
    else {
        panic!("one equation")
    };
    assert_eq!(
        rule.written.orientation,
        crate::description::written::RuleOrientation::Unpinned
    );
    assert_eq!(rule.print_data(), "rule : id(Zero) <=> Zero");
    assert_eq!(
        rule.print_theory(&gandr_theory_levitation::Name::from("id")),
        "rule id : id(Zero) <=> Zero"
    );
}

#[test]
fn the_retired_op_member_lead_declines_with_its_respelling()
{
    let source = "data NatRetired : Type where { | Zero : NatRetired op stale : (x : NatRetired) --> NatRetired; }";
    let report = elaborated(SourceText::from(source));
    assert!(report.declarations[0].description.opers.is_empty());
    let [ref diagnostic] = *report.diagnostics.as_slice()
    else {
        panic!("one retired member")
    };
    assert_eq!(diagnostic.fault, DescriptionFault::RetiredOperation);
    assert_eq!(
        source.get(usize::from(diagnostic.span.start()) .. usize::from(diagnostic.span.end())),
        Some("op stale : (x : NatRetired) --> NatRetired")
    );
}

#[test]
fn codata_declarations_elaborate_with_codata_polarity()
{
    let report = elaborated(SourceText::from(
        "codata Stream(a : Type) : Type where { head : a; tail : Stream(a); }",
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
fn a_family_its_code_cannot_carry_is_left_to_the_native_reading()
{
    for (source, what, result) in [
        (
            "data Box : Type where { | Put : (a : Type) --> Box }",
            "a universe field",
            "Box",
        ),
        (
            "data Pack : Type where { | Mk : (c : Integer, v : c) --> Pack }",
            "a field naming the one before it",
            "Pack",
        ),
    ] {
        let report = elaborated(SourceText::from(source));
        assert!(
            report.declarations.is_empty() && report.diagnostics.is_empty(),
            "{what}: no description and no refusal, {:?}",
            report.diagnostics
        );
        let [ref native] = *report.natives.as_slice()
        else {
            panic!("{what}: the native reading owns the family")
        };
        let [ref generator] = *native.written.constructors.as_slice()
        else {
            panic!("{what}: its one generator is written")
        };
        let stated = &generator.result;
        assert_eq!(
            source.get(usize::from(stated.span.start()) .. usize::from(stated.span.end())),
            Some(result),
            "{what}: the result is kept past the field the code cannot carry"
        );
    }
    // An operation the description must carry keeps the refusal of a field
    // holding a box below its whole type.
    let source = "data Cell : Type where { | Mk : (get : List(Integer -> Integer)) --> Cell oper reset : (c : Cell) --> Cell; }";
    let report = elaborated(SourceText::from(source));
    let [ref diagnostic] = *report.diagnostics.as_slice()
    else {
        panic!("one higher-order field")
    };
    assert_eq!(diagnostic.fault, DescriptionFault::HigherOrderField);
    assert_eq!(
        source.get(usize::from(diagnostic.span.start()) .. usize::from(diagnostic.span.end())),
        Some("Integer -> Integer")
    );
}

#[test]
fn a_multi_output_constructor_describes_one_constructor_per_port()
{
    let source = "data Tree : Type where { | Leaf : (n : Integer) --> Tree | Split : (t : Tree) --> (l : Tree, r : Tree) oper prune : (t : Tree) --> Tree; }";
    let report = elaborated(SourceText::from(source));
    assert_eq!(report.diagnostics, [], "the description reads every port");
    let [ref entry] = *report.declarations.as_slice()
    else {
        panic!("one description")
    };
    let names: Vec<&str> = entry
        .description
        .ctors
        .iter()
        .map(|ctor| ctor.name.as_ref())
        .collect();
    assert_eq!(names, ["Leaf", "Split.l", "Split.r"]);
    let [_, ref left, ref right] = *entry.description.ctors.as_ref()
    else {
        panic!("three constructors")
    };
    assert_eq!(left.code, right.code, "the ports share the input `t`");
    let results: Vec<Option<&str>> = entry
        .written
        .constructors
        .iter()
        .map(|written| {
            source.get(
                usize::from(written.result.span.start()) .. usize::from(written.result.span.end()),
            )
        })
        .collect();
    assert_eq!(
        results,
        [Some("Tree"), Some("Tree"), Some("Tree")],
        "each port keeps its own result"
    );
}

/// #4853: a rule names a port through parentheses, `(Split t).l`, as it names
/// it with the constructor's argument glued, `(Split(t)).l`.
#[test]
fn a_rule_names_a_port_through_parentheses_4853()
{
    let rules = |side: &str| {
        let source = alloc::format!(
            "data Tree : Type where {{ | Leaf : (n : Integer) --> Tree | Split : (t : Tree) --> (l : \
             Tree, r : Tree) oper prune : (t : Tree) --> Tree; rule : prune ({side}) ==> prune t; }}"
        );
        let report = elaborated(SourceText::from(source.as_str()));
        assert_eq!(report.diagnostics, [], "`{side}` reads as a port");
        let [ref entry] = *report.declarations.as_slice()
        else {
            panic!("one description")
        };
        entry
            .description
            .rules
            .iter()
            .map(|face| (face.lhs.clone(), face.rhs.clone()))
            .collect::<alloc::vec::Vec<_>>()
    };
    assert_eq!(
        rules("(Split t).l"),
        rules("(Split(t)).l"),
        "a port written with its argument juxtaposed is the port written glued"
    );
}

#[test]
fn a_value_function_field_is_the_function_former()
{
    let source = "data Prog : Type where { | Done : (x : Integer) --> Prog | Get : (k : Integer -> Prog) --> Prog | \
                  Both : (k : (Integer, String) -> Prog) --> Prog | Twice : (k : Integer -> (Integer -> Prog)) --> Prog \
                  | Pure : (f : Integer -> Integer) --> Prog | Put : (s : Integer, k : Prog) --> Prog rule : Put s \
                  (Put u k) <=> Put u k; }";
    let report = elaborated(SourceText::from(source));
    assert_eq!(report.diagnostics, [], "every field is carried");
    assert!(
        report.natives.is_empty(),
        "so no native reading owns the family"
    );
    let [ref entry] = *report.declarations.as_slice()
    else {
        panic!("one description")
    };
    let integer = || ValueTypeRef::prim(PrimTy::Integer);
    let one = DescriptionGrade::Finite(Multiplicity::from(1_u64));
    let itself = || Code::var("Prog");
    let codes: Vec<_> = entry
        .description
        .ctors
        .iter()
        .map(|ctor| &ctor.code)
        .collect();
    assert_eq!(
        codes.get(1_usize).copied(),
        Some(&Code::fun(vec![integer()], itself())),
        "`Integer => Prog` is the function former into the recursive position"
    );
    assert_eq!(
        codes.get(2_usize).copied(),
        Some(&Code::fun(
            vec![integer(), ValueTypeRef::prim(PrimTy::StringTy)],
            itself()
        )),
        "a domain list is the former's domains in written order"
    );
    assert_eq!(
        codes.get(3_usize).copied(),
        Some(&Code::fun(
            vec![integer()],
            Code::fun(vec![integer()], itself())
        )),
        "`=>` nests to the right, one former per arrow"
    );
    assert_eq!(
        codes.get(4_usize).copied(),
        Some(&Code::fun(
            vec![integer()],
            Code::field(integer(), one, Attrs::empty())
        )),
        "a result that is not the family is a field"
    );
    assert_eq!(
        entry.description.rules.len(),
        1,
        "and the family keeps its rule"
    );
    // The thin arrow writes the same box, so the fields read as the same codes.
    let thin = "data Prog : Type where { | Done : (x : Integer) --> Prog | Get : (k : Integer -> Prog) --> Prog | \
                Both : (k : (Integer, String) -> Prog) --> Prog | Twice : (k : Integer -> (Integer -> Prog)) --> \
                Prog | Pure : (f : Integer -> Integer) --> Prog | Put : (s : Integer, k : Prog) --> Prog rule : \
                Put s (Put u k) <=> Put u k; }";
    let thin = elaborated(SourceText::from(thin));
    assert_eq!(thin.diagnostics, []);
    let [ref read] = *thin.declarations.as_slice()
    else {
        panic!("one description")
    };
    let read: Vec<_> = read
        .description
        .ctors
        .iter()
        .map(|ctor| &ctor.code)
        .collect();
    assert_eq!(read, codes);
}

/// #3194: the formatter spells `Ā => B` explicitly as the thunked arrow
/// `+U (Ā -> -F B)`, so a presented type written that way reads as the same
/// function formers, its rule kept, over one domain, two, none and nested.
#[test]
fn the_thunked_arrow_is_the_function_former_it_spells_3194()
{
    let fields = [
        ("One", "Integer -> Prog", "+U (Integer -> -F Prog)"),
        (
            "Two",
            "(Integer, String) -> Prog",
            "+U (Integer -> String -> -F Prog)",
        ),
        (
            "Nested",
            "Integer -> (Integer -> Prog)",
            "+U (Integer -> -F (+U (Integer -> -F Prog)))",
        ),
        ("Thunk", "() -> Prog", "+U (-F Prog)"),
        ("Pure", "Integer -> Integer", "+U (Integer -> -F Integer)"),
    ];
    let source = |thunked: bool| {
        let mut written = String::from("data Prog : Type where { | Done : (x : Integer) --> Prog ");
        for &(name, sugared, explicit) in &fields {
            for piece in [
                "| ",
                name,
                " : (k : ",
                if thunked { explicit } else { sugared },
                ") --> Prog ",
            ] {
                written.push_str(piece);
            }
        }
        written.push_str(
            "| Put : (s : Integer, k : Prog) --> Prog rule : Put s (Put u k) <=> Put u k; }",
        );
        written
    };
    let codes = |written: &str| {
        let report = elaborated(SourceText::from(written));
        assert_eq!(report.diagnostics, [], "every field is carried: {written}");
        let [ref entry] = *report.declarations.as_slice()
        else {
            panic!("one description of {written}")
        };
        assert_eq!(
            entry.description.rules.len(),
            1,
            "and the family keeps its rule"
        );
        entry
            .description
            .ctors
            .iter()
            .map(|ctor| ctor.code.clone())
            .collect::<Vec<_>>()
    };
    assert_eq!(
        codes(&source(true)),
        codes(&source(false)),
        "each thunked arrow is the former its `=>` spelling is"
    );
}

#[test]
fn the_declined_metadata_golden_is_declined()
{
    let report = elaborated(SourceText::from(
        "data Declared : Type where { | Mk : Declared [variance] }",
    ));
    let [ref diagnostic] = *report.diagnostics.as_slice()
    else {
        panic!("one reserved attribute")
    };
    assert!(
        matches!(diagnostic.fault, DescriptionFault::IllFormed(ref reason) if reason.kind == gandr_theory_levitation::WfKind::DeclaresDerivedMetadata),
        "the reserved attribute is declined as derived metadata, not {:?}",
        diagnostic.fault
    );
    let report = elaborated(SourceText::from(
        "data Declared : Type where { | Mk : Declared [variance, strictness] }",
    ));
    assert!(
        report.diagnostics.iter().all(|diagnostic| matches!(diagnostic.fault, DescriptionFault::IllFormed(ref reason) if reason.kind == gandr_theory_levitation::WfKind::DeclaresDerivedMetadata)),
        "two markers separated by a comma read as two markers, not a malformed slot: {:?}",
        report.diagnostics
    );
}

#[test]
fn a_block_left_open_keeps_the_member_before_its_missing_close()
{
    let report = elaborated(SourceText::from("data X : Type where { | A : X"));
    assert_eq!(
        report
            .declarations
            .iter()
            .map(|declaration| declaration.description.ctors.len())
            .collect::<Vec<_>>(),
        [1_usize],
        "the member the repair closes over is read, beside the repair's own report"
    );
}

#[test]
fn a_result_must_repeat_each_parameter_by_its_own_name()
{
    let report = elaborated(SourceText::from(
        "data List(a : Type) : Type where { | Nil : List(b) }",
    ));
    assert!(
        !report.diagnostics.is_empty(),
        "`List(b)` is not the family over its own parameter `a`"
    );
}

#[test]
fn a_bare_parameter_head_declines_the_whole_declaration_with_its_respelling()
{
    let report = elaborated(SourceText::from(
        "data Maybe(a) where { | None : Maybe(a) }",
    ));
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
    let report = elaborated(SourceText::from("data Color  where { | Red : Color }"));
    assert!(report.declarations.is_empty());
    assert!(
        report
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.fault == DescriptionFault::FamilyHead)
    );
}

#[test]
fn an_instantiated_result_head_declines_as_uninferable()
{
    let source = "data Bad(a : Type) : Type where { | Mk : Bad(Integer) }";
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
    let report = elaborated(SourceText::from("data Bad : Type where { | Mk : Bad(0) }"));
    assert!(report.declarations[0].description.ctors.is_empty());
    let [ref diagnostic] = *report.diagnostics.as_slice()
    else {
        panic!("one arity refusal")
    };
    assert_eq!(diagnostic.fault, DescriptionFault::NonUniformResult);
}

/// A named index telescope is read as a family head, its arity one index per
/// entry: a result stating both indices reads, and one stating one declines
/// as non-uniform at that result (#4022).
#[test]
fn a_named_index_telescope_counts_its_indices_4022()
{
    let source =
        include_str!("tests/fixtures/a-named-index-telescope-counts-its-indices-4022.gandr");
    let report = elaborated(SourceText::from(source));
    let [ref diagnostic] = *report.diagnostics.as_slice()
    else {
        panic!("only the short result declines: {:?}", report.diagnostics);
    };
    assert_eq!(diagnostic.fault, DescriptionFault::NonUniformResult);
    assert_eq!(
        source.get(usize::from(diagnostic.span.start()) .. usize::from(diagnostic.span.end())),
        Some("Short(n)")
    );
}

#[test]
fn a_bare_result_head_over_a_parameterized_family_declines()
{
    let report = elaborated(SourceText::from(
        "data Bad(a : Type) : Type where { | Mk : Bad }",
    ));
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
    let report = elaborated(SourceText::from("data Bad : Type where { | Mk : Other }"));
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
    let data = elaborated(SourceText::from("data Boxed : Type where { | Mk : Boxed }"));
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
    let report = elaborated(SourceText::from(
        "codata Boxed : Type where { Mk : Boxed; }",
    ));
    assert!(report.declarations[0].description.ctors.is_empty());
    let [ref diagnostic] = *report.diagnostics.as_slice()
    else {
        panic!(
            "the repaired block is refused once: {:?}",
            report.diagnostics
        )
    };
    assert!(
        matches!(diagnostic.fault, DescriptionFault::Repaired { .. }),
        "the parser's repair of the constructor-led member is the block's refusal"
    );
}

#[test]
fn a_codata_oper_declines_without_swallowing_observation_and_rule_siblings()
{
    let source =
        "codata S : Type where { head : Nat; oper tail : (s : S) --> S; rule : head ==> head; }";
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
        Some("oper tail : (s : S) --> S")
    );
}

#[test]
fn a_field_reads_each_primitive_and_each_applied_argument()
{
    let source =
        include_str!("tests/fixtures/a-field-reads-each-primitive-and-each-applied-argument.gandr");
    let report = elaborated(SourceText::from(source));
    assert_eq!(report.diagnostics, Vec::new());
    let [ref entry] = *report.declarations.as_slice()
    else {
        panic!("one family")
    };
    let [ref prims, ref nested] = *entry.description.ctors.as_ref()
    else {
        panic!("two generators")
    };
    let field_types = |code: &gandr_theory_levitation::Code<DescriptionGrade>| {
        let mut found = Vec::new();
        let mut pending = Vec::from([code.view()]);
        while let Some(view) = pending.pop() {
            match view {
                CodeView::Field { ty, .. } => found.push(ty.clone()),
                CodeView::Prod(parts) => {
                    let first = pending.len();
                    pending.extend(parts.map(gandr_theory_levitation::CodeNode::view));
                    if let Some(added) = pending.get_mut(first ..) {
                        added.reverse();
                    }
                },
                CodeView::Unit
                | CodeView::Var(_)
                | CodeView::Sum(_)
                | CodeView::Bind { .. }
                | CodeView::Fun { .. } => {},
            }
        }
        found
    };
    assert_eq!(field_types(&prims.code), [
        ValueTypeRef::prim(PrimTy::Integer),
        ValueTypeRef::prim(PrimTy::StringTy),
        ValueTypeRef::prim(PrimTy::Boolean),
        ValueTypeRef::prim(PrimTy::Unit),
    ]);
    assert_eq!(field_types(&nested.code), [ValueTypeRef::ctor("Pair", [
        ValueTypeRef::param("a"),
        ValueTypeRef::ctor("Pair", [ValueTypeRef::param("a"), ValueTypeRef::param("a")])
    ])]);
}

#[test]
fn parameterized_observations_retain_both_port_boundaries()
{
    use gandr_theory_levitation::SortRef;
    let report = elaborated(SourceText::from(
        "codata Fun(a : Type, b : Type) : Type where { get : b; ap : (x : a) --> b; }",
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

/// Every member fault renders a message no other renders, so a declined
/// member says which of the description route's limits it met.
#[test]
fn every_member_fault_renders_its_own_message()
{
    use alloc::string::ToString as _;

    let messages = [
        MemberFault::HigherOrderField,
        MemberFault::DependentField,
        MemberFault::TypeShape,
        MemberFault::NoUniverse,
        MemberFault::NativeDecode,
        MemberFault::OperationFiller,
        MemberFault::TopLevelOperation,
        MemberFault::HigherCell,
        MemberFault::Reversible,
        MemberFault::NoOutput,
        MemberFault::AggregatedOutput,
        MemberFault::LhsNotOperation,
        MemberFault::EmptyOperation,
        MemberFault::NestedOperation,
        MemberFault::ResultArity,
        MemberFault::MixedPolarity,
        MemberFault::IllSorted,
        MemberFault::RewrittenIndex,
        MemberFault::UnderivedWiring,
        MemberFault::UnwiredDiagram,
        MemberFault::SpiderBudget,
        MemberFault::ParallelRedexes,
        MemberFault::OffBoundary,
    ]
    .map(|fault| fault.to_string());
    for (position, message) in messages.iter().enumerate() {
        for other in messages.iter().skip(position.saturating_add(1)) {
            assert_ne!(
                message, other,
                "two member faults rendering alike read as one"
            );
        }
    }
}

/// The sorts a recursive occurrence in `code` targets, left to right, and
/// the heads of its fields at a named type.
///
/// # Specification
/// trivial.
fn occurrences(code: &gandr_theory_levitation::Code<DescriptionGrade>)
-> (Vec<String>, Vec<String>)
{
    let mut pending = alloc::vec![code.to_node()];
    let (mut sorts, mut heads) = (Vec::new(), Vec::new());
    while let Some(node) = pending.pop() {
        match node.view() {
            CodeView::Var(sort) => sorts.push(String::from(sort.as_ref())),
            CodeView::Field { ty, .. } => {
                if let ValueTypeView::Ctor { head, .. } = ty.view() {
                    heads.push(String::from(head.as_ref()));
                }
            },
            CodeView::Prod(children) | CodeView::Sum(children) => {
                let mut children: Vec<_> = children.collect();
                children.reverse();
                pending.extend(children);
            },
            CodeView::Unit | CodeView::Bind { .. } | CodeView::Fun { .. } => {},
        }
    }
    (sorts, heads)
}

/// #5018: the data families of one mutual block read as one description of
/// their sorts. A field at a sibling, applied to the shared parameters, is a
/// recursive occurrence at the sibling's sort, and the universe's check
/// admits the description.
#[test]
fn a_mutual_block_s_data_families_read_as_one_description_5018()
{
    let grammar = grammar();
    let source = include_str!(
        "tests/fixtures/a-mutual-block-s-data-families-read-as-one-description-5018.gandr"
    );
    let tree = parsed(&grammar, source.into());
    let report = elaborate_descriptions(&grammar, &tree, &Unit::single()).unwrap();
    assert_eq!(report.diagnostics, Vec::new());
    let [ref group] = *report.mutuals.as_slice()
    else {
        panic!("one group: {:?}", report.mutuals)
    };
    let described = &group.description;
    let sorts: Vec<&str> = described
        .sorts
        .iter()
        .map(|sort| sort.name.as_ref())
        .collect();
    assert_eq!(sorts, ["Rose", "Forest"]);
    let constructors: Vec<(&str, &str)> = described
        .ctors
        .iter()
        .map(|ctor| (ctor.name.as_ref(), ctor.result.as_ref()))
        .collect();
    assert_eq!(constructors, [
        ("Node", "Rose"),
        ("Empty", "Forest"),
        ("More", "Forest")
    ]);
    let [ref node, ref empty, ref more] = *described.ctors.as_ref()
    else {
        panic!("three constructors")
    };
    assert_eq!(
        occurrences(&node.code),
        (alloc::vec![String::from("Forest")], Vec::new())
    );
    assert!(matches!(empty.code.view(), CodeView::Unit));
    assert_eq!(
        occurrences(&more.code),
        (
            alloc::vec![String::from("Rose"), String::from("Forest")],
            Vec::new()
        ),
        "`head` is an occurrence at `Rose`, and `tail` one at `Forest`"
    );
    assert_eq!(
        gandr_theory_levitation::check_desc(described),
        Vec::new(),
        "the universe admits the description"
    );
    // Each family keeps its own description, a field at its sibling a field.
    let forest = report
        .declarations
        .iter()
        .find(|entry| entry.description.id.name.as_ref() == "Forest")
        .expect("`Forest` is read");
    let [_, ref own] = *forest.description.ctors.as_ref()
    else {
        panic!("two constructors")
    };
    assert_eq!(
        occurrences(&own.code),
        (alloc::vec![String::from("Forest")], alloc::vec![
            String::from("Rose")
        ])
    );
}

/// #5018: a mutual block with one data family, or with families whose
/// parameters differ, reads no group, and each family keeps its own
/// description.
#[test]
fn a_mutual_block_with_one_data_family_reads_no_group_5018()
{
    let grammar = grammar();
    let source = include_str!(
        "tests/fixtures/a-mutual-block-with-one-data-family-reads-no-group-5018.gandr"
    );
    let tree = parsed(&grammar, source.into());
    let report = elaborate_descriptions(&grammar, &tree, &Unit::single()).unwrap();
    assert_eq!(report.diagnostics, Vec::new());
    assert_eq!(report.mutuals, Vec::new());
    assert_eq!(report.declarations.len(), 3);
}
