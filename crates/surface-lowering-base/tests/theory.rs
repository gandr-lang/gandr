//! A ruled signature read through the production lowering route of
//! `gandr-surface-lowering`: the check's reason for an ill-formed theory, a
//! top-level operation refused at itself, a rule-bearing theory's value and a
//! member refused at the `include` that brings it.

use gandr_surface_lowering::DeclarationOutcome;
use gandr_surface_lowering::LoweringBudget;
use gandr_surface_lowering::LoweringRefusal;
use gandr_surface_lowering::Role;
use gandr_surface_lowering::WfKind;
use gandr_surface_lowering::lower_module;
use gandr_surface_lowering_base::description::MemberFault;
use gandr_surface_lowering_base::fixture::grammar;
use gandr_surface_lowering_base::fixture::presentation_text;
use gandr_surface_lowering_base::namespace::Recognition;
use gandr_surface_parser::parse;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

#[test]
fn an_ill_formed_theory_is_refused_with_the_checks_reason_1553()
{
    let source = include_str!(
        "theory/fixtures/an-ill-formed-theory-is-refused-with-the-checks-reason-1553.gandr"
    );
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
    let [unbindable] = *module.declarations().iter().collect::<Vec<_>>()
    else {
        panic!("the block is one declaration: {:?}", module.declarations())
    };
    let DeclarationOutcome::Refused(
        refusal @ LoweringRefusal::IllFormedDescription {
            kind,
            subjects: [Maybe::Present(sort), Maybe::Present(port)],
            ..
        },
    ) = unbindable.outcome()
    else {
        panic!(
            "an unrepresentable binder is the description check's refusal, not a misplaced \
             tile: {:?}",
            unbindable.outcome()
        )
    };
    assert_eq!(kind, WfKind::NonRepresentableBinder);
    assert_eq!(
        (sort.as_ref(), port.as_ref()),
        ("Tm", "t"),
        "the refusal names the sort and the port as the block spells them"
    );
    assert_eq!(
        alloc::string::ToString::to_string(&refusal),
        "the port `t` binds a variable of the sort `Tm`, which is not representable",
        "the refusal states the check's reason"
    );
}

/// A top-level operation with no filler is refused at itself by its own name,
/// and the block before it decorates it rather than standing where a
/// declaration is expected (#3073).
#[test]
fn a_decorated_top_level_operation_is_refused_at_itself_3073()
{
    let source = include_str!(
        "theory/fixtures/a-decorated-top-level-operation-is-refused-at-itself-3073.gandr"
    );
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
    let [split, one] = *module.declarations().iter().collect::<Vec<_>>()
    else {
        panic!(
            "the operation and the definition are the two declarations: {:?}",
            module.declarations()
        )
    };
    assert_eq!(split.name().as_ref(), "split");
    assert_eq!(one.name().as_ref(), "one");
    let DeclarationOutcome::Refused(LoweringRefusal::UndescribedMember {
        span,
        fault: MemberFault::TopLevelOperation,
    }) = split.outcome()
    else {
        panic!(
            "the operation is refused by its own name: {:?}",
            split.outcome()
        )
    };
    assert_eq!(
        source.get(usize::from(span.start()) .. usize::from(span.end())),
        Some("oper split : (b : Bit) --> (_ : Bit, _ : Bit)"),
        "the refusal stands at the operation"
    );
    let Maybe::Present(key) = split.signature()
    else {
        panic!("the operation is the declaration's half")
    };
    assert_eq!(
        module.attributes().entries(key).len(),
        1_usize,
        "the block decorates the operation"
    );
    assert!(
        !matches!(one.outcome(), DeclarationOutcome::Refused(_)),
        "the definition after it is not refused: {:?}",
        one.outcome()
    );
}

#[test]
fn a_rule_bearing_theory_defines_its_presentation_with_its_laws()
{
    let grammar = grammar();
    let tree = parse(
        &grammar,
        SourceText::from(include_str!(
            "theory/fixtures/a-rule-bearing-theory-defines-its-presentation-with-its-laws-tree.gandr"
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
    let declared: alloc::vec::Vec<_> = module
        .declarations()
        .iter()
        .filter(|declaration| declaration.role() == Role::Declared)
        .collect();
    let [code, circle, cat] = *declared.as_slice()
    else {
        panic!(
            "`Theory` once, then each theory: {:?}",
            module.declarations()
        )
    };
    let DeclarationOutcome::Data(index) = code.outcome()
    else {
        panic!("`Theory` is a data family: {:?}", code.outcome())
    };
    let Maybe::Present(signature) = module.data(index)
    else {
        panic!("its signature is minted")
    };
    let DeclarationOutcome::Completed {
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
        presentation_text(&arena, body),
        r#"Presents(Sort("Pt", End, End), Const("base", End, Port("", "Pt", End, End), Oper("turn", Port("x", "Pt", End, End), Port("", "Pt", End, End), Oper("unturn", Port("x", "Pt", End, End), Port("", "Pt", End, End), End))), Rule("turnUnturn", App("turn", Arg(App("unturn", Arg(Var("x"), End)), End)), Var("x"), Rule("unturnTurn", App("unturn", Arg(App("turn", Arg(Var("x"), End)), End)), Var("x"), Rank("turn", "1", Rank("unturn", "1", End)))))"#,
        "the value carries the constant `base` as a `Const`, each law as a `Rule`, read node for node, then the rank of each operation a law applies"
    );
    let DeclarationOutcome::Completed {
        declared_type: cat_type,
        body: cat_body,
    } = cat.outcome()
    else {
        panic!(
            "a law over an indexed sort is read with the indices its sorting fixes, so its \
             block defines a value too: {:?}",
            cat.outcome()
        )
    };
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
        gandr_core_checker::Declaration::new(
            cat.constant(),
            Maybe::Present(cat_type),
            Maybe::Present(cat_body),
            gandr_core_checker::OriginToken::from(2_usize),
        ),
    ];
    let report = gandr_core_checker::check_module(
        &mut gandr_core_checker::CheckingContext::new(
            &mut arena,
            gandr_core_checker::CheckBudget::DEFAULT,
            &gandr_core_checker::Checker,
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
        "the checker checks each rule-bearing value at `Theory`: {verdicts:?}"
    );
}

/// #2752: a member the including block refuses, and the included one reads,
/// is refused at the `include` that brings it, in the including block; the
/// included block stays clean.
#[test]
fn an_included_member_is_refused_at_its_include_2752()
{
    let source =
        include_str!("theory/fixtures/an-included-member-is-refused-at-its-include-2752.gandr");
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
    let text = |span: ByteSpan| source.get(usize::from(span.start()) .. usize::from(span.end()));
    let refused: alloc::vec::Vec<_> = module
        .declarations()
        .iter()
        .filter_map(|declaration| {
            let DeclarationOutcome::Refused(refusal) = declaration.outcome()
            else {
                return None;
            };
            Some((
                text(declaration.span()).and_then(|block| block.split_whitespace().nth(1)),
                refusal,
            ))
        })
        .collect();
    let [(block, ref refusal)] = *refused.as_slice()
    else {
        panic!("one refusal: {refused:?}")
    };
    assert_eq!(
        block,
        Some("Ordered"),
        "the including block is refused, the included one reads"
    );
    let LoweringRefusal::UndescribedMember {
        span,
        fault: MemberFault::NestedOperation,
    } = *refusal
    else {
        panic!("the included rule is refused for its nesting: {refusal:?}")
    };
    assert_eq!(
        text(span),
        Some("include Monad"),
        "the refusal stands at the include"
    );
}
