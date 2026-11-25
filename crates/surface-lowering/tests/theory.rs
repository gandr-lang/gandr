//! A ruled signature where the lowering answers for it: a refused block and a
//! refused top-level operation state their refusals, an inner block decorates
//! its theory, a decoration out of shape refuses first, and a theory block
//! defines the value of its presentation. The cases that read the signature
//! alone are in the base crate, `description::theory::tests`.

use gandr_surface_lowering::DeclarationOutcome;
use gandr_surface_lowering::LoweringBudget;
use gandr_surface_lowering::LoweringRefusal;
use gandr_surface_lowering::Role;
use gandr_surface_lowering::description::MemberFault;
use gandr_surface_lowering::lower_module;
use gandr_surface_lowering::namespace::Recognition;
use gandr_surface_lowering_base::fixture::grammar;
use gandr_surface_lowering_base::fixture::presentation_text;
use gandr_surface_parser::parse;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

#[test]
fn a_refused_theory_block_states_its_refusal()
{
    let source = include_str!("theory/fixtures/a-refused-theory-block-states-its-refusal.gandr");
    let grammar = grammar();
    let tree = parse(&grammar, SourceText::from(source))
        .unwrap()
        .into_tree();
    let mut arena = gandr_core_term::CoreArena::new();
    let module = lower_module(
        &grammar,
        &tree,
        &mut arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
    )
    .unwrap();
    let [wheel] = *module.declarations().iter().collect::<Vec<_>>()
    else {
        panic!(
            "the refused block is one declaration, and mints no `Theory`: {:?}",
            module.declarations()
        )
    };
    assert_eq!(wheel.name().as_ref(), "Wheel");
    assert_eq!(wheel.role(), Role::Declared, "its name is a declaration");
    let text = |at: ByteSpan| source.get(usize::from(at.start()) .. usize::from(at.end()));
    assert!(
        matches!(
            wheel.outcome(),
            DeclarationOutcome::Refused(LoweringRefusal::BareFeedback { span, rule })
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

/// An inner block leading a theory's body, `@![ refuses("…") ]`, decorates
/// the theory as an outer block before it does: the refused block
/// states its refusal. One after a member decorates nothing and is refused
/// at itself under the theory's name, the theory lowering clean. One
/// writing an attribute an outer block writes is refused as doubled.
#[test]
fn an_inner_attribute_decorates_its_theory_3586()
{
    let source =
        include_str!("theory/unformatted/an-inner-attribute-decorates-its-theory-3586.gandr");
    let grammar = grammar();
    let tree = parse(&grammar, SourceText::from(source))
        .unwrap()
        .into_tree();
    let mut arena = gandr_core_term::CoreArena::new();
    let module = lower_module(
        &grammar,
        &tree,
        &mut arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
    )
    .unwrap();
    let text = |at: ByteSpan| source.get(usize::from(at.start()) .. usize::from(at.end()));
    let named = |name: &str| {
        module
            .declarations()
            .iter()
            .filter(|declaration| declaration.name().as_ref() == name)
            .collect::<Vec<_>>()
    };
    let [wheel] = *named("Wheel")
    else {
        panic!("`Wheel` is one declaration: {:?}", module.declarations())
    };
    assert!(
        matches!(
            wheel.outcome(),
            DeclarationOutcome::Refused(LoweringRefusal::BareFeedback { .. })
        ),
        "the block is refused at its member: {:?}",
        wheel.outcome()
    );
    let Maybe::Present(key) = wheel.definition()
    else {
        panic!("the block is the declaration's definition")
    };
    assert_eq!(
        module.attributes().entries(key).len(),
        1_usize,
        "the inner block states the block's refusal"
    );
    let late = named("Late");
    let declared = late
        .iter()
        .filter(|declaration| declaration.role() == Role::Declared)
        .collect::<Vec<_>>();
    let held = late
        .iter()
        .filter(|declaration| declaration.role() == Role::Held)
        .collect::<Vec<_>>();
    assert!(
        matches!(declared.as_slice(), [theory] if !matches!(theory.outcome(), DeclarationOutcome::Refused(_))),
        "`Late` lowers clean beside its late block: {late:?}"
    );
    assert!(
        matches!(
            held.as_slice(),
            [block] if matches!(
                block.outcome(),
                DeclarationOutcome::Refused(LoweringRefusal::MalformedForm { span, .. })
                    if text(span) == Some("@![ explicit_exits ]")
            )
        ),
        "the late block is refused at itself under `Late`: {late:?}"
    );
    let doubled = named("Doubled");
    assert!(
        doubled.iter().any(|declaration| matches!(
            declaration.outcome(),
            DeclarationOutcome::Refused(LoweringRefusal::DuplicateAttribute { name, .. })
                if name.as_ref() == "explicit_exits"
        )),
        "an attribute the outer and the inner block both write is refused as doubled: {doubled:?}"
    );
}

/// A block before a theory member reads through the general reader and
/// stands at the member. A name the registry places elsewhere is refused by
/// its place, naming the places it takes; a mark written twice is refused at
/// the second, and a mark with a payload at the payload. `format` before an
/// operation is read back at that operation and not at the theory (#6404).
#[test]
fn a_member_attribute_stands_at_its_member_6404()
{
    use gandr_surface_lowering::AttributeHolder;
    use gandr_surface_lowering::AttributePlace;
    use gandr_surface_lowering::AttributePlaces;
    use gandr_surface_lowering_base::attribute::AttributeSchema;
    use gandr_surface_lowering_base::attribute::DocumentFormat;
    use gandr_surface_lowering_base::attribute::PayloadForm;
    use gandr_surface_syntax::ByteOffset;

    /// `source` lowered, beside the arena its payloads are minted into.
    ///
    /// # Specification
    /// trivial.
    fn lowered(
        source: SourceText<'_>
    ) -> (
        gandr_surface_lowering::LoweredModule<'_>,
        gandr_core_term::CoreArena,
    )
    {
        let grammar = grammar();
        let tree = parse(&grammar, source).unwrap().into_tree();
        let mut arena = gandr_core_term::CoreArena::new();
        let module = lower_module(
            &grammar,
            &tree,
            &mut arena,
            LoweringBudget::DEFAULT,
            Recognition::default(),
        )
        .unwrap();
        (module, arena)
    }
    let format = "theory Monoid where { sort M : Type; \
                  @[format(*{.latex = \"\\\\varepsilon\", .md = \"ε\"})] oper unit : M; }";
    let (module, arena) = lowered(SourceText::from(format));
    let [monoid] = *module
        .declarations()
        .iter()
        .filter(|declaration| declaration.name().as_ref() == "Monoid")
        .collect::<Vec<_>>()
    else {
        panic!("`Monoid` is one declaration: {:?}", module.declarations())
    };
    assert!(
        !matches!(monoid.outcome(), DeclarationOutcome::Refused(_)),
        "`format` stands before an operation: {:?}",
        monoid.outcome()
    );
    let Maybe::Present(key) = monoid.definition()
    else {
        panic!("the block is the declaration's definition")
    };
    let start = format.find("unit :").unwrap_or_default();
    let unit = AttributeHolder::Member(
        ByteSpan::new(
            ByteOffset::from(start),
            ByteOffset::from(start.saturating_add(4)),
        )
        .unwrap(),
    );
    assert!(
        matches!(
            module.attributes().format(key, unit, DocumentFormat::Markdown, &arena),
            Maybe::Present(text) if text.as_ref() == "ε"
        ),
        "the operation reads its own text"
    );
    assert!(
        module.attributes().entries(key).is_empty(),
        "the theory holds no entry of its member"
    );
    for settled in [
        "theory Spiders where { @[frobenius] sort M : Type; @[inert] oper unit : M; }",
        "theory Documented where { sort M : Type; @[doc(\"the unit\")] oper unit : M; }",
    ] {
        let (module, _arena) = lowered(SourceText::from(settled));
        assert!(
            module.declarations().iter().all(|declaration| !matches!(
                declaration.outcome(),
                DeclarationOutcome::Refused(_)
            )),
            "`{settled}` settles: {:?}",
            module.declarations()
        );
    }
    for (refused, written, place, takes) in [
        (
            "theory Monoid where { sort M : Type; @[deprecated] oper unit : M; }",
            "deprecated",
            AttributePlace::Operation,
            AttributePlaces::DECLARATION,
        ),
        (
            "theory Monoid where { @[inert] sort M : Type; oper unit : M; }",
            "inert",
            AttributePlace::Sort,
            AttributePlaces::of(&[AttributePlace::Declaration, AttributePlace::Operation]),
        ),
        (
            "theory Monoid where { sort M : Type; @[frobenius] oper unit : M; }",
            "frobenius",
            AttributePlace::Operation,
            AttributePlaces::SORT,
        ),
    ] {
        let (module, _arena) = lowered(SourceText::from(refused));
        let start = refused.find(written).unwrap_or_default();
        assert!(
            module.declarations().iter().any(|declaration| matches!(
                declaration.outcome(),
                DeclarationOutcome::Refused(LoweringRefusal::MisplacedAttribute {
                    span,
                    name,
                    place: at,
                    takes: taken,
                }) if usize::from(span.start()) == start
                    && usize::from(span.end()) == start.saturating_add(written.len())
                    && name.as_ref() == written
                    && at == place
                    && taken == takes
            )),
            "`{refused}` is refused by its place: {:?}",
            module.declarations()
        );
    }
    for (doubled, mark) in [
        (
            "theory Monoid where { sort M : Type; @[inert, inert] oper unit : M; }",
            "inert",
        ),
        (
            "theory Monoid where { @[frobenius, frobenius] sort M : Type; oper unit : M; }",
            "frobenius",
        ),
    ] {
        let (module, _arena) = lowered(SourceText::from(doubled));
        let first = doubled.find(mark).unwrap_or_default();
        let again = doubled.rfind(mark).unwrap_or_default();
        assert!(
            module.declarations().iter().any(|declaration| matches!(
                declaration.outcome(),
                DeclarationOutcome::Refused(LoweringRefusal::DuplicateAttribute {
                    span,
                    name,
                    first: earlier,
                }) if usize::from(span.start()) == again
                    && usize::from(span.end()) == again.saturating_add(mark.len())
                    && usize::from(earlier.start()) == first
                    && name.as_ref() == mark
            )),
            "`{doubled}` is refused at its second mark: {:?}",
            module.declarations()
        );
    }
    let payload = "theory Monoid where { sort M : Type; @[inert(1)] oper unit : M; }";
    let (module, _arena) = lowered(SourceText::from(payload));
    let one = payload.find("(1)").unwrap_or_default().saturating_add(1);
    assert!(
        module.declarations().iter().any(|declaration| matches!(
            declaration.outcome(),
            DeclarationOutcome::Refused(LoweringRefusal::IllTypedPayload {
                span,
                name,
                expected: AttributeSchema::Marker,
                written: PayloadForm::Integer,
            }) if usize::from(span.start()) == one
                && usize::from(span.end()) == one.saturating_add(1)
                && name.as_ref() == "inert"
        )),
        "a mark with a payload is refused at the payload: {:?}",
        module.declarations()
    );
}

#[test]
fn a_refused_top_level_operation_states_its_refusal()
{
    let source =
        include_str!("theory/fixtures/a-refused-top-level-operation-states-its-refusal.gandr");
    let grammar = grammar();
    let tree = parse(&grammar, SourceText::from(source))
        .unwrap()
        .into_tree();
    let mut arena = gandr_core_term::CoreArena::new();
    let module = lower_module(
        &grammar,
        &tree,
        &mut arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
    )
    .unwrap();
    let [split] = *module.declarations().iter().collect::<Vec<_>>()
    else {
        panic!(
            "the refused operation is one declaration: {:?}",
            module.declarations()
        )
    };
    assert_eq!(split.name().as_ref(), "split");
    assert_eq!(split.role(), Role::Held, "its name enters no namespace");
    assert!(matches!(
        split.outcome(),
        DeclarationOutcome::Refused(LoweringRefusal::UndescribedMember {
            fault: MemberFault::OperationFiller,
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

/// A decoration out of shape before a refused top-level operation refuses it
/// at the decoration's stray tile, ahead of the operation's own refusal, so
/// the stray tile is where its first error stands (#4113, #4114).
#[test]
fn an_unreadable_decoration_refuses_a_refused_operation_first_4113()
{
    let operation = include_str!(
        "../../surface-lowering-base/src/description/theory/tests/unformatted/a-top-level-operation-declines-its-filler-by-name.gandr"
    );
    // The `(` deleted leaves the payload an operand after the name; the `)`
    // doubled leaves the second one an operand after the attribute.
    for (decoration, stray) in [
        ("@[ refuses\"OperationFiller\") ]\n", 10_usize .. 27_usize),
        ("@[ refuses(\"OperationFiller\")) ]\n", 29_usize .. 30_usize),
    ] {
        let source = alloc::format!("{decoration}{operation}");
        let grammar = grammar();
        let tree = parse(&grammar, SourceText::from(source.as_str()))
            .unwrap()
            .into_tree();
        let mut arena = gandr_core_term::CoreArena::new();
        let module = lower_module(
            &grammar,
            &tree,
            &mut arena,
            LoweringBudget::DEFAULT,
            Recognition::default(),
        )
        .unwrap();
        let [split] = *module.declarations().iter().collect::<Vec<_>>()
        else {
            panic!(
                "{decoration:?}: one declaration: {:?}",
                module.declarations()
            )
        };
        let DeclarationOutcome::Refused(LoweringRefusal::MalformedForm { span, .. }) =
            split.outcome()
        else {
            panic!(
                "{decoration:?}: the decoration refuses it: {:?}",
                split.outcome()
            )
        };
        assert_eq!(
            usize::from(span.start()) .. usize::from(span.end()),
            stray,
            "{decoration:?}: the refusal stands at the stray material"
        );
    }
}

#[test]
fn a_theory_block_defines_its_presentation()
{
    let grammar = grammar();
    let tree = parse(
        &grammar,
        SourceText::from(include_str!(
            "theory/fixtures/a-theory-block-defines-its-presentation-tree.gandr"
        )),
    )
    .unwrap()
    .into_tree();
    let mut arena = gandr_core_term::CoreArena::new();
    let module = lower_module(
        &grammar,
        &tree,
        &mut arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
    )
    .unwrap();
    assert_eq!(module.description_diagnostics(), []);
    // Each theory's forgetting map is derived from its block beside it.
    let declared: alloc::vec::Vec<_> = module
        .declarations()
        .iter()
        .filter(|declaration| declaration.role() == Role::Declared)
        .collect();
    let [code, nat, pointed] = *declared.as_slice()
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
    let DeclarationOutcome::Data(index) = code.outcome()
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
        [
            3, 0, 3, 4, 4, 4, 1, 2, 2, 1, 2, 3, 5, 4, 3, 4, 4, 6, 3, 4, 4, 2, 3, 6, 2, 3, 1, 2, 1,
            2, 1, 3
        ],
        "each constructor's names, then its recursions"
    );
    let mut declarations = alloc::vec![gandr_core_checker::Declaration::data(
        code.constant(),
        alloc::sync::Arc::clone(signature),
        gandr_core_checker::OriginToken::from(0_usize),
    )];
    let mut bodies = alloc::vec::Vec::new();
    for (origin, theory) in [nat, pointed].into_iter().enumerate() {
        let DeclarationOutcome::Completed {
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
        bodies.push(presentation_text(&arena, body));
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
