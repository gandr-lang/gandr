//! The description route read where the lowering answers for it: a native
//! family's signature, a member the lowering holds apart, a refusal at a
//! family's close, a codata family's observations and the attribute block
//! written before it. The cases that read a description alone are in the base
//! crate, `description::tests`.

use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;

use gandr_surface_lowering::DeclarationOutcome;
use gandr_surface_lowering::FormFault;
use gandr_surface_lowering::LoweredDeclaration;
use gandr_surface_lowering::LoweringBudget;
use gandr_surface_lowering::LoweringRefusal;
use gandr_surface_lowering::Repair;
use gandr_surface_lowering::SurfaceName;
use gandr_surface_lowering::Unit;
use gandr_surface_lowering::description::elaborate_descriptions;
use gandr_surface_lowering::lower_module;
use gandr_surface_lowering::namespace::Recognition;
use gandr_surface_lowering_base::fixture::grammar;
use gandr_surface_lowering_base::fixture::parsed;
use gandr_surface_lowering_base::fixture::registered;
use gandr_surface_lowering_base::fixture::repaired;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

#[test]
fn native_data_keeps_telescope_and_nominal_heads()
{
    use gandr_core_checker::CheckBudget;
    use gandr_core_checker::Checker;
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
    let grammar = grammar();
    let source = "data Box(a : Type) : Type where { | Vacant : Box(a) | Packed : (x : a) --> Box(a) } def xs : Box(Integer);";
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
    assert_eq!(module.description_diagnostics(), []);
    let [family, xs] = *module.declarations().iter().collect::<Vec<_>>()
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
        &mut CheckingContext::new(&mut arena, CheckBudget::DEFAULT, &Checker),
        &declarations,
    );
    let [ref first, ref second] = *report.judged()
    else {
        panic!("two judgments")
    };
    assert_eq!(first.verdict(), Verdict::Data);
    assert!(matches!(second.verdict(), Verdict::Owed(_)));
}

#[test]
fn member_refusals_keep_their_spans_and_other_declarations()
{
    let grammar = grammar();
    let source =
        "data Flag : Type where { | Off : Flag rule : bad x ~> x; | On : Flag } def later = 7;";
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
    let [family, refused, later] = *module.declarations().iter().collect::<Vec<_>>()
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

/// #1462: a member held apart reads the attribute block written before it,
/// a member held apart without one reads none — the family's own attributes
/// state the family alone — and a block before a member that is not held
/// apart refuses the family at the block.
#[test]
fn a_held_member_states_its_own_expectation_1462()
{
    let grammar = grammar();
    let source = "@[ checks ] data Sub : Type where { | Zero : Sub oper minus : (m : Sub, n : Sub) --> Sub; \
                  @[ refuses(\"RulesNonLinear\") ] rule : minus x x ==> Zero; oper same : (m : Sub, \
                  n : Sub) --> Sub; rule : same y y ==> Zero; }";
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
    let stated = |declaration: &LoweredDeclaration<'_>| -> Vec<String> {
        module
            .attributes()
            .entries(declaration.introduced())
            .iter()
            .map(|entry| alloc::string::String::from(entry.name().as_ref()))
            .collect()
    };
    let [family, attributed, bare] = *module.declarations().iter().collect::<Vec<_>>()
    else {
        panic!(
            "the family and its two held rules: {:?}",
            module.declarations()
        )
    };
    assert!(matches!(family.outcome(), DeclarationOutcome::Data(_)));
    assert_eq!(
        stated(family),
        ["checks"],
        "the family's attribute states the family"
    );
    assert!(
        matches!(
            attributed.outcome(),
            DeclarationOutcome::Refused(LoweringRefusal::RulesNonLinear { .. })
        ),
        "the first rule is held apart"
    );
    assert_eq!(
        stated(attributed),
        ["refuses"],
        "and reads the block written before it"
    );
    assert!(
        matches!(
            bare.outcome(),
            DeclarationOutcome::Refused(LoweringRefusal::RulesNonLinear { .. })
        ),
        "the second rule is held apart"
    );
    assert!(
        stated(bare).is_empty(),
        "and, written without a block, reads none of the family's"
    );

    let stray = include_str!(
        "description/unformatted/a-held-member-states-its-own-expectation-1462-stray.gandr"
    );
    let tree = parsed(&grammar, stray.into());
    let module = lower_module(
        &grammar,
        &tree,
        &mut arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
    )
    .unwrap();
    let start = stray.find("@[").unwrap_or_default();
    assert!(
        module.declarations().iter().any(|declaration| matches!(
            declaration.outcome(),
            DeclarationOutcome::Refused(LoweringRefusal::MalformedForm { span, .. })
                if usize::from(span.start()) == start
        )),
        "a block before a member that is not held apart refuses the family at the block: {:?}",
        module.declarations()
    );
}

#[test]
fn an_unended_family_is_refused_once_at_its_close()
{
    let grammar = grammar();
    for (source, why) in [
        (
            include_str!(
                "description/unformatted/an-unended-family-is-refused-once-at-its-close-1.gandr"
            ),
            "a data family whose last member the cell gate refuses",
        ),
        (
            include_str!(
                "description/unformatted/an-unended-family-is-refused-once-at-its-close-2.gandr"
            ),
            "a codata family the decoder would refuse",
        ),
    ] {
        let tree = repaired(&grammar, source.into());
        let mut arena = gandr_core_term::CoreArena::new();
        let module = lower_module(
            &grammar,
            &tree,
            &mut arena,
            LoweringBudget::DEFAULT,
            Recognition::default(),
        )
        .unwrap();
        let refusals: Vec<_> = module
            .declarations()
            .iter()
            .filter_map(|declaration| match declaration.outcome() {
                DeclarationOutcome::Refused(refusal) => Some(refusal),
                DeclarationOutcome::Completed { .. }
                | DeclarationOutcome::Uncompleted { .. }
                | DeclarationOutcome::Bodied { .. }
                | DeclarationOutcome::Data(_)
                | DeclarationOutcome::Codata(_)
                | DeclarationOutcome::Abstract(_)
                | DeclarationOutcome::World => None,
            })
            .collect();
        let end = gandr_surface_syntax::ByteOffset::from(source.trim_end().len());
        let [
            LoweringRefusal::MalformedForm {
                span,
                fault: FormFault::Repaired(repair),
                ..
            },
        ] = refusals[..]
        else {
            panic!("{why}: one refusal, its parse error: {refusals:?}");
        };
        assert_eq!(
            (span, repair),
            (
                ByteSpan::new(end, end).unwrap(),
                Repair::GhostClose(gandr_surface_syntax::ClosingClass::Brace)
            ),
            "{why}: the refusal is the missing close, where it belongs"
        );
    }
}

/// A field that is no type is refused once, by the lowering where it reads
/// the field's type, though an operation makes the description read the
/// family. A type in parentheses reads as the type it groups, and a codata
/// observation that is no type is malformed (#2664).
#[test]
fn a_field_that_is_no_type_is_refused_once_by_the_lowering_2664()
{
    let grammar = grammar();
    let data = |ty: &str| {
        alloc::format!(
            "data G : Type where {{ | Mk : (p : {ty}) --> G oper keep : (g : G) --> G; }}"
        )
    };
    let mut rows: Vec<(String, &str)> =
        ["0", "\"a\"", "'a'", "?", "()", "(Integer, Integer)", "(0)"]
            .into_iter()
            .map(|ty| (data(ty), ty))
            .collect();
    rows.push((
        String::from("codata G : Type[-] where { held : 0; next : G; }"),
        "0",
    ));
    for &(ref source, ty) in &rows {
        let tree = parsed(&grammar, source.as_str().into());
        let mut arena = gandr_core_term::CoreArena::new();
        let module = lower_module(
            &grammar,
            &tree,
            &mut arena,
            LoweringBudget::DEFAULT,
            Recognition::default(),
        )
        .unwrap();
        let mut refusals = module
            .declarations()
            .iter()
            .filter_map(|declaration| match declaration.outcome() {
                DeclarationOutcome::Refused(refusal) => Some(refusal),
                DeclarationOutcome::Completed { .. }
                | DeclarationOutcome::Uncompleted { .. }
                | DeclarationOutcome::Bodied { .. }
                | DeclarationOutcome::Data(_)
                | DeclarationOutcome::Codata(_)
                | DeclarationOutcome::Abstract(_)
                | DeclarationOutcome::World => None,
            });
        let (Some(refusal), None) = (refusals.next(), refusals.next())
        else {
            panic!("`{source}`: one refusal")
        };
        assert!(
            !matches!(refusal, LoweringRefusal::UndescribedMember { .. }),
            "`{source}`: the refusal is no undescribed member: {refusal:?}"
        );
        let start = source.rfind(ty).unwrap();
        let Maybe::Present(span) = refusal.span()
        else {
            panic!("`{source}`: the refusal is located: {refusal:?}")
        };
        assert!(
            usize::from(span.start()) >= start
                && usize::from(span.end()) <= start.saturating_add(ty.len()),
            "`{source}`: the refusal is inside `{ty}`: {refusal:?}"
        );
    }
    let fields = |ty: &str| {
        let written = data(ty);
        let tree = parsed(&grammar, SourceText::from(written.as_str()));
        let report = elaborate_descriptions(&grammar, &tree, &Unit::single()).unwrap();
        assert_eq!(report.diagnostics, [], "`{ty}` reads");
        let [ref family] = *report.declarations.as_slice()
        else {
            panic!("`{ty}`: one description")
        };
        family.description.ctors.clone()
    };
    assert_eq!(
        fields("(Integer)"),
        fields("Integer"),
        "a type in parentheses reads as the type it groups"
    );
    assert_eq!(
        fields("((Integer))"),
        fields("Integer"),
        "each pair of parentheses is read through"
    );
}

#[test]
fn a_codata_declaration_lowers_to_its_signature()
{
    use gandr_core_term::CompType;
    let grammar = grammar();
    let source =
        include_str!("description/fixtures/a-codata-declaration-lowers-to-its-signature.gandr");
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
    let [flag, stream, ones, later] = *module.declarations().iter().collect::<Vec<_>>()
    else {
        panic!("data, codata, a stream and a later declaration")
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
    let DeclarationOutcome::Codata(index) = stream.outcome()
    else {
        panic!("the codata family lowers: {:?}", stream.outcome())
    };
    let Maybe::Present(codata) = module.codata(index)
    else {
        panic!("the module holds the codata family's signature")
    };
    assert_eq!(codata.parameters().len(), 1, "one parameter");
    let [head, tail] = *codata.observations()
    else {
        panic!("two observations")
    };
    assert!(
        matches!(arena.comp_type(head), Some(&CompType::Returner { .. })),
        "the head returns its value"
    );
    assert!(
        matches!(arena.comp_type(tail), Some(&CompType::Codata { declaration, .. }) if declaration == stream.constant()),
        "the tail is the family itself"
    );
    assert!(module.description_diagnostics().is_empty());
    let DeclarationOutcome::Uncompleted { declared_type } = ones.outcome()
    else {
        panic!("the stream is declared: {:?}", ones.outcome())
    };
    let Some(&gandr_core_term::ValueType::Thunk(answer)) = arena.value_type(declared_type)
    else {
        panic!("the stream is a thunk")
    };
    assert!(
        matches!(arena.comp_type(answer), Some(&CompType::Codata { declaration, .. }) if declaration == stream.constant()),
        "the stream's answer is the codata type at its argument: {:?}",
        arena.comp_type(answer)
    );
    assert!(matches!(later.outcome(), DeclarationOutcome::Bodied { .. }));
}

/// #2188: a codata family's self reference reaches the checker at the
/// arguments its source writes, so the occurrence guard sees a non-uniform
/// one: `Swap`'s tail at its parameters swapped, `Twisted`'s at the family
/// applied again, and `Stream`'s at its parameter, as the code alone said.
#[test]
fn a_codata_self_reference_keeps_its_written_arguments_2188()
{
    use gandr_core_term::CompType;
    use gandr_core_term::Value;
    use gandr_core_term::Zone;
    use gandr_kernel_term::DeBruijnIndex;
    let grammar = grammar();
    let source = include_str!(
        "description/fixtures/a-codata-self-reference-keeps-its-written-arguments-2188.gandr"
    );
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
    let tail = |declaration: &LoweredDeclaration<'_>| {
        let DeclarationOutcome::Codata(index) = declaration.outcome()
        else {
            panic!("the codata family lowers: {:?}", declaration.outcome())
        };
        let Maybe::Present(codata) = module.codata(index)
        else {
            panic!("the module holds the codata family's signature")
        };
        let [_, tail] = *codata.observations()
        else {
            panic!("two observations")
        };
        let Some(&CompType::Codata {
            declaration: applied,
            ref arguments,
        }) = arena.comp_type(tail)
        else {
            panic!(
                "the tail is a codata application: {:?}",
                arena.comp_type(tail)
            )
        };
        assert_eq!(
            applied,
            declaration.constant(),
            "the tail applies its own family"
        );
        arguments
            .iter()
            .map(|&argument| arena.value(argument).cloned())
            .collect::<Vec<_>>()
    };
    let variable = |index: u32| {
        Some(Value::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(index),
        })
    };
    let [swap, twisted, stream] = *module.declarations().iter().collect::<Vec<_>>()
    else {
        panic!("three codata families")
    };
    assert_eq!(
        tail(swap),
        [variable(0), variable(1)],
        "`Swap(b, a)` keeps its parameters swapped: `b` is the inner variable"
    );
    assert!(
        matches!(tail(twisted).as_slice(), [Some(Value::QuoteComputation(_))]),
        "`Twisted(Twisted(a))` applies the family to the family applied again"
    );
    assert_eq!(tail(stream), [variable(0)], "`Stream(a)` stays uniform");
}

/// #2665: a codata family reads each data family it names as the lowering
/// reads one. `Holder`'s observation returns `Small`, and `Stream`'s tail
/// applies the family to the code of `Small`, which the occurrence guard then
/// refuses as a non-uniform occurrence.
#[test]
fn a_codata_family_reads_a_data_family_as_the_lowering_does_2665()
{
    use gandr_core_term::CompType;
    use gandr_core_term::Value;
    use gandr_core_term::ValueType;
    let grammar = grammar();
    let source = include_str!(
        "description/fixtures/a-codata-family-reads-a-data-family-as-the-lowering-does-2665.gandr"
    );
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
    let [small, holder, stream] = *module.declarations().iter().collect::<Vec<_>>()
    else {
        panic!("a data family and two codata families")
    };
    let observations = |declaration: &LoweredDeclaration<'_>| {
        let DeclarationOutcome::Codata(index) = declaration.outcome()
        else {
            panic!("the codata family lowers: {:?}", declaration.outcome())
        };
        let Maybe::Present(codata) = module.codata(index)
        else {
            panic!("the module holds the codata family's signature")
        };
        codata.observations().to_vec()
    };
    let is_small = |ty| {
        matches!(arena.value_type(ty), Some(&ValueType::Data { declaration, ref arguments })
            if declaration == small.constant() && arguments.is_empty())
    };
    let [held] = *observations(holder)
    else {
        panic!("one observation")
    };
    let Some(&CompType::Returner { result, .. }) = arena.comp_type(held)
    else {
        panic!(
            "the observation returns its value: {:?}",
            arena.comp_type(held)
        )
    };
    assert!(
        is_small(result),
        "`held` returns `Small`: {:?}",
        arena.value_type(result)
    );
    let [_, tail] = *observations(stream)
    else {
        panic!("two observations")
    };
    let Some(&CompType::Codata {
        declaration,
        ref arguments,
    }) = arena.comp_type(tail)
    else {
        panic!(
            "the tail is a codata application: {:?}",
            arena.comp_type(tail)
        )
    };
    assert_eq!(
        declaration,
        stream.constant(),
        "the tail applies its own family"
    );
    let [argument] = *arguments.as_slice()
    else {
        panic!("the tail applies the family to one argument: {arguments:?}")
    };
    let Some(&Value::Quote(code)) = arena.value(argument)
    else {
        panic!("the argument is a code: {:?}", arena.value(argument))
    };
    assert!(is_small(code), "the tail is at the code of `Small`");
    assert!(module.description_diagnostics().is_empty());
}

#[test]
fn an_attribute_block_decorates_the_codata_declaration_after_it()
{
    let grammar = grammar();
    let source = include_str!(
        "description/fixtures/an-attribute-block-decorates-the-codata-declaration-after-it.gandr"
    );
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
    let [stream, later] = *module.declarations().iter().collect::<Vec<_>>()
    else {
        panic!("the codata family and the later declaration are declared")
    };
    assert!(matches!(stream.outcome(), DeclarationOutcome::Codata(_)));
    let Maybe::Present(written) = stream.signature()
    else {
        panic!("the codata family keeps its digest")
    };
    let [ref entry] = *module.attributes().entries(written)
    else {
        panic!("one attribute is filed under the codata family")
    };
    assert_eq!(entry.name(), registered(SurfaceName::from("checks")));
    assert!(matches!(later.outcome(), DeclarationOutcome::Bodied { .. }));
}
