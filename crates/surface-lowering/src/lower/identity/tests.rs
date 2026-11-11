use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_checker::CheckBudget;
use gandr_core_checker::CheckRefusal;
use gandr_core_checker::CheckingContext;
use gandr_core_checker::Declaration;
use gandr_core_checker::ModuleReport;
use gandr_core_checker::OriginToken;
use gandr_core_checker::Verdict;
use gandr_core_checker::body;
use gandr_core_checker::check_module;
use gandr_core_checker::signature;
use gandr_core_term::CertificateEquality;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueType;
use gandr_core_term::Zone;
use gandr_core_term::compose::CellCount;
use gandr_core_term::compose::Composite;
use gandr_core_term::compose::Pasting;
use gandr_core_term::equal_type_syntax;
use gandr_core_term::identity::Relation;
use gandr_core_term::session::DialogueMove;
use gandr_core_term::session::Endpoint;
use gandr_core_term::session::RecordedMove;
use gandr_core_term::session::SessionRelation;
use gandr_core_term::ua::Stratum;
use gandr_kernel_term::DeBruijnIndex;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::SourceText;
use gandr_theory_sites::Degree;
use gandr_theory_sites::ShapeSize;
use quenchant_shape::shape::Maybe;

use crate::error::FragmentBoundary;
use crate::error::LoweringRefusal;
use crate::fixture::grammar;
use crate::fixture::listed;
use crate::fixture::listing;
use crate::fixture::parsed;
use crate::fixture::span;
use crate::lower::LoweringBudget;
use crate::lower::lower_module;
use crate::module::DeclarationOutcome;
use crate::module::LoweredModule;
use crate::namespace::Recognition;
use crate::origin::ComponentName;
use crate::origin::Insertion;
use crate::origin::Provenance;
use crate::resolve::OperandCount;
use crate::resolve::SurfaceName;

/// The module the parser and the lowering make of `source`.
///
/// # Specification
/// - requires: the source parses cleanly within the default allowance.
/// - ensures: one declaration per declared name.
/// - fails: never on accepted fixtures.
/// - panics: if the lowering refuses the module.
///
/// # Adequacy
/// - hypothesis: L3 — every witness below reads its module through here.
/// - witness: `lower::identity::tests::a_path_type_and_reflexivity_lower_to_their_formers`
#[spec(ensures: |ret| ret.declarations().iter().next().is_some())]
pub(in crate::lower) fn lowered<'source>(
    source: SourceText<'source>,
    arena: &mut CoreArena,
) -> LoweredModule<'source>
{
    let pbg = grammar();
    let tree = parsed(&pbg, source);

    lower_module(
        &pbg,
        &tree,
        arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
    )
    .unwrap()
}

/// The checker's verdicts over every declaration of `module` the lowering
/// did not refuse.
///
/// # Specification
/// - requires: `module` was lowered over `arena` and declares no data and no
///   abstract type.
/// - ensures: one verdict per unrefused declaration, in admission order.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a derived operation is accepted only where its motive and
///   its base agree with the answer it was read off.
/// - witness: `lower::identity::tests::back_then_and_cong_unfold_to_transports`
#[spec(ensures: |ret| ret.judged().len() <= module.declarations().iter().len())]
pub(in crate::lower) fn judged(
    module: &LoweredModule<'_>,
    arena: &mut CoreArena,
) -> ModuleReport
{
    let declarations: Vec<Declaration> = module
        .declarations()
        .iter()
        .filter_map(|declaration| {
            let origin = OriginToken::from(usize::from(declaration.origin()));
            let (declared, defined) = match declaration.outcome() {
                DeclarationOutcome::Completed {
                    declared_type,
                    body,
                } => (Maybe::Present(declared_type), Maybe::Present(body)),
                DeclarationOutcome::Uncompleted { declared_type } => (
                    Maybe::Present(declared_type),
                    Maybe::Absent(body::Absent::Hole),
                ),
                DeclarationOutcome::Bodied { body } => (
                    Maybe::Absent(signature::Absent::Unsigned),
                    Maybe::Present(body),
                ),
                DeclarationOutcome::Data(_)
                | DeclarationOutcome::Codata(_)
                | DeclarationOutcome::Abstract(_)
                | DeclarationOutcome::World
                | DeclarationOutcome::Refused(_) => return None,
            };
            Some(Declaration::new(
                declaration.constant(),
                declared,
                defined,
                origin,
            ))
        })
        .collect();

    check_module(
        &mut CheckingContext::new(arena, CheckBudget::DEFAULT),
        &declarations,
    )
}

/// Assert that every verdict of `report` accepts its declaration.
///
/// # Specification
/// trivial.
pub(in crate::lower) fn assert_accepted(report: &ModuleReport)
{
    let accepted = report.judged().iter().all(|judged| {
        matches!(
            judged.verdict(),
            Verdict::Checked { .. } | Verdict::Synthesised { .. }
        )
    });
    assert!(accepted, "{report:?}");
}

/// The outcome of the declaration `name` in `module`.
///
/// # Specification
/// - requires: `module` declares `name`.
/// - ensures: that declaration's outcome.
/// - fails: never.
/// - panics: if the declaration is missing.
///
/// # Adequacy
/// - hypothesis: L3 — the witnesses read each outcome here.
/// - witness: `lower::identity::tests::a_path_type_and_reflexivity_lower_to_their_formers`
#[spec(ensures: |ret| module.declarations().iter().any(|declaration| declaration.outcome() == ret))]
pub(in crate::lower) fn outcome_of<'source>(
    module: &LoweredModule<'source>,
    name: SurfaceName<'_>,
) -> DeclarationOutcome<'source>
{
    let Some(declaration) = module
        .declarations()
        .iter()
        .find(|declaration| declaration.name() == name)
    else {
        panic!("`{name:?}` is declared");
    };

    declaration.outcome()
}

/// The computation a function body runs under its parameters.
///
/// # Specification
/// - requires: `name` lowers to a function's thunked lambda chain.
/// - ensures: the computation under the thunk and every lambda.
/// - fails: never.
/// - panics: if `name` lowers no body or its body is no thunk.
///
/// # Adequacy
/// - hypothesis: L3 — the witnesses read each operation's transport here.
/// - witness: `lower::identity::tests::back_then_and_cong_unfold_to_transports`
#[spec(ensures: |ret| !matches!(arena.computation(ret), Some(&Computation::Lambda(_))))]
fn tail_of(
    module: &LoweredModule<'_>,
    arena: &CoreArena,
    name: SurfaceName<'_>,
) -> ComputationId
{
    let body = match outcome_of(module, name) {
        DeclarationOutcome::Completed { body, .. } | DeclarationOutcome::Bodied { body } => body,
        other @ (DeclarationOutcome::Uncompleted { .. }
        | DeclarationOutcome::Data(_)
        | DeclarationOutcome::Codata(_)
        | DeclarationOutcome::Abstract(_)
        | DeclarationOutcome::World
        | DeclarationOutcome::Refused(_)) => panic!("`{name:?}` lowers a body: {other:?}"),
    };
    let Some(&Value::Thunk(mut computation)) = arena.value(body)
    else {
        panic!("a function body is a thunk");
    };
    while let Some(&Computation::Lambda(under)) = arena.computation(computation) {
        computation = under;
    }

    computation
}

/// The fold `Path.step` stands for: `Path.step(p, q)` returns the binary
/// composite, whose realisation is the transport.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the realisation when `id` returns a composite of the 2-chain at
///   its least stratum.
/// - fails: never.
/// - panics: if `id` returns no binary composite.
///
/// # Adequacy
/// - hypothesis: L3 — the witnesses read `Path.step`'s transport here.
/// - witness: `lower::identity::tests::back_then_and_cong_unfold_to_transports`
#[spec(ensures: |ret| matches!(arena.computation(id), Some(&Computation::Return(returned))
    if matches!(arena.value(returned), Some(&Value::Compose { realised, .. }) if realised == ret)))]
fn folded(
    arena: &CoreArena,
    id: ComputationId,
) -> ComputationId
{
    let Some(&Computation::Return(returned)) = arena.computation(id)
    else {
        panic!("`then` returns its composite: {:?}", arena.computation(id));
    };
    let Some(&Value::Compose {
        composite,
        realised,
        ..
    }) = arena.value(returned)
    else {
        panic!("`then` is a composite: {:?}", arena.value(returned));
    };
    assert_eq!(
        composite,
        gandr_core_term::compose::Composite::binary(),
        "`then` composes the 2-chain at its least stratum"
    );
    realised
}

/// The intuitionistic variable at `index`.
///
/// # Specification
/// trivial.
const fn variable(index: DeBruijnIndex) -> Value
{
    Value::Variable {
        zone: Zone::Intuitionistic,
        index,
    }
}

#[test]
fn a_path_type_and_reflexivity_lower_to_their_formers()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/unformatted/a-path-type-and-reflexivity-lower-to-their-formers-module.gandr"
        )),
        &mut arena,
    );
    let DeclarationOutcome::Completed {
        declared_type,
        body,
    } = outcome_of(&module, "p".into())
    else {
        panic!("the path and its reflexivity lower");
    };
    let Some(&ValueType::Path { left, right, .. }) = arena.value_type(declared_type)
    else {
        panic!("the signature is a path type");
    };
    assert!(
        matches!(arena.value(left), Some(&Value::Literal(_)))
            && matches!(arena.value(right), Some(&Value::Literal(_))),
        "a value endpoint stands bare"
    );
    let Some(&Value::Here(point)) = arena.value(body)
    else {
        panic!("`here(4)` is reflexivity");
    };
    assert!(
        matches!(arena.value(point), Some(&Value::Literal(_))),
        "reflexivity's point is the literal"
    );
    assert_accepted(&judged(&module, &mut arena));

    let mut arena = CoreArena::new();
    let source = "def p = Path.here 4 5;\n";
    let module = lowered(SourceText::from(source), &mut arena);
    assert!(
        matches!(
            outcome_of(&module, "p".into()),
            DeclarationOutcome::Refused(LoweringRefusal::OutOfFragment {
                boundary: FragmentBoundary::Arity(count),
                ..
            }) if count == OperandCount::from(2_usize)
        ),
        "reflexivity takes one point"
    );
}

#[test]
fn an_operation_answers_only_under_its_former()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/unformatted/an-operation-answers-only-under-its-former-module-1.gandr"
        )),
        &mut arena,
    );
    let DeclarationOutcome::Completed { body, .. } = outcome_of(&module, "held".into())
    else {
        panic!("`Path.here` lowers");
    };
    assert!(
        matches!(arena.value(body), Some(&Value::Here(_))),
        "`Path.here` is reflexivity"
    );
    let DeclarationOutcome::Completed { body, .. } = outcome_of(&module, "stayed".into())
    else {
        panic!("`Flow.stay` lowers");
    };
    assert!(
        matches!(arena.value(body), Some(&Value::Stay(_))),
        "`Flow.stay` is directed reflexivity"
    );
    assert!(
        matches!(
            outcome_of(&module, "bare".into()),
            DeclarationOutcome::Refused(LoweringRefusal::UnresolvedName { name, .. })
                if name == SurfaceName::from("here")
        ),
        "a bare spelling is an ordinary name no binder answers"
    );
    assert!(
        matches!(
            outcome_of(&module, "crossed".into()),
            DeclarationOutcome::Refused(_)
        ),
        "an operation under another former answers nothing"
    );

    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/unformatted/an-operation-answers-only-under-its-former-module-2.gandr"
        )),
        &mut arena,
    );
    assert!(
        !matches!(
            outcome_of(&module, "bound".into()),
            DeclarationOutcome::Refused(_)
        ),
        "a source binds a freed spelling as an ordinary name"
    );
}

#[test]
fn funext_lowers_to_its_former()
{
    let functions = include_str!("tests/fixtures/funext-lowers-to-its-former-functions.gandr");
    let mut arena = CoreArena::new();
    let source = format!(
        include_str!("tests/unformatted/funext-lowers-to-its-former-1.gandr"),
        functions = functions
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let DeclarationOutcome::Completed { body, .. } = outcome_of(&module, "same".into())
    else {
        panic!("the path and its extensionality lower");
    };
    let Some(&Value::Funext(left, right)) = arena.value(body)
    else {
        panic!("`Path.funext id again` is function extensionality");
    };
    assert!(
        matches!(arena.value(left), Some(&Value::Constant(constant)) if usize::from(constant) == 0)
            && matches!(arena.value(right), Some(&Value::Constant(constant)) if usize::from(constant) == 1),
        "both functions are read as values, in order"
    );
    assert_accepted(&judged(&module, &mut arena));

    let mut arena = CoreArena::new();
    let source = format!("{functions}def once = Path.funext id;\n");
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    assert!(
        matches!(
            outcome_of(&module, "once".into()),
            DeclarationOutcome::Refused(LoweringRefusal::OutOfFragment {
                boundary: FragmentBoundary::Arity(count),
                ..
            }) if count == OperandCount::from(1_usize)
        ),
        "function extensionality takes two functions"
    );

    let mut arena = CoreArena::new();
    let source = include_str!("tests/fixtures/funext-lowers-to-its-former-2.gandr");
    let module = lowered(SourceText::from(source), &mut arena);
    let Some(&Computation::Application(..)) =
        arena.computation(tail_of(&module, &arena, "call".into()))
    else {
        panic!("a declaration named `funext` is an ordinary name");
    };
}

#[test]
fn a_list_moves_along_a_universe_equivalence()
{
    let negation =
        include_str!("tests/fixtures/a-list-moves-along-a-universe-equivalence-negation.gandr");
    let mut arena = CoreArena::new();
    let source = format!(
        include_str!("tests/unformatted/a-list-moves-along-a-universe-equivalence-1.gandr"),
        negation = negation
    );
    let source = listing(&source);
    let module = listed(&source, &mut arena);
    let DeclarationOutcome::Completed { body, .. } = outcome_of(&module, "negation".into())
    else {
        panic!("the universe path and its equivalence lower");
    };
    let Some(&Value::Equiv(forward, backward)) = arena.value(body)
    else {
        panic!("`equiv not not` is a universe equivalence");
    };
    assert!(
        [forward, backward].iter().all(|&translator| {
            matches!(arena.value(translator), Some(&Value::Constant(constant)) if usize::from(constant) == 0)
        }),
        "both translators are read as values"
    );
    let Some(&Computation::PathTransport {
        motive,
        path,
        value,
    }) = arena.computation(tail_of(&module, &arena, "moved".into()))
    else {
        panic!("`transport` lowers to the element transport");
    };
    let Some(&ValueType::List(element)) = arena.value_type(motive)
    else {
        panic!("the motive is the abstraction's body");
    };
    assert!(
        matches!(
            arena.value_type(element),
            Some(&ValueType::Element { code, .. }) if arena.value(code) == Some(&variable(0_u32.into()))
        ) && matches!(arena.value(path), Some(&Value::Constant(constant)) if usize::from(constant) == 1)
            && arena.value(value) == Some(&variable(0_u32.into())),
        "the motive decodes its binder; the path and the value follow in order"
    );
    let mut written: Vec<(usize, Provenance)> = module
        .origins()
        .motives()
        .iter()
        .map(|&(_, origin)| (usize::from(origin.span().start()), origin.provenance()))
        .collect();
    written.sort_unstable_by_key(|&(at, _)| at);
    let expected: Vec<(usize, Provenance)> = source
        .match_indices("fun (X) { List X }")
        .map(|(at, _)| (at, Provenance::Written))
        .collect();
    assert_eq!(
        (written, expected.len()),
        (expected, 2_usize),
        "each written motive is recorded where it is written, though both denote one family"
    );
    let DeclarationOutcome::Completed { body, .. } = outcome_of(&module, "both".into())
    else {
        panic!("a list value lowers");
    };
    let Some(&Value::ListCons(_, tail)) = arena.value(body)
    else {
        panic!("`cons` is the list cell");
    };
    assert!(
        matches!(arena.value(tail), Some(&Value::ListCons(_, end)) if arena.value(end) == Some(&Value::ListNil)),
        "`nil` is the empty list"
    );
    assert_accepted(&judged(&module, &mut arena));

    let mut arena = CoreArena::new();
    let source = format!(
        include_str!("tests/unformatted/a-list-moves-along-a-universe-equivalence-2.gandr"),
        negation = negation
    );
    let source = listing(&source);
    let module = listed(&source, &mut arena);
    assert!(
        matches!(
            outcome_of(&module, "named".into()),
            DeclarationOutcome::Refused(LoweringRefusal::OutOfFragment {
                boundary: FragmentBoundary::Unannotated,
                ..
            })
        ),
        "a motive is written as a static abstraction"
    );
    assert!(
        matches!(
            outcome_of(&module, "half".into()),
            DeclarationOutcome::Refused(LoweringRefusal::OutOfFragment {
                boundary: FragmentBoundary::Arity(count),
                ..
            }) if count == OperandCount::from(1_usize)
        ),
        "a list cell takes a head and a tail"
    );

    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/a-list-moves-along-a-universe-equivalence-module.gandr"
        )),
        &mut arena,
    );
    assert!(
        matches!(
            arena.computation(tail_of(&module, &arena, "keep".into())),
            Some(&Computation::Return(returned)) if arena.value(returned) == Some(&variable(0_u32.into()))
        ),
        "a parameter named `nil` shadows the empty list"
    );
}

#[test]
fn a_path_product_lowers_to_its_former()
{
    let negation =
        include_str!("tests/fixtures/a-path-product-lowers-to-its-former-negation.gandr");
    let mut arena = CoreArena::new();
    let source = format!("{negation}def paired = Path.product (Path.here Unit) (equiv not not);\n");
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let DeclarationOutcome::Bodied { body } = outcome_of(&module, "paired".into())
    else {
        panic!("the product lowers");
    };
    let Some(&Value::PathProduct(first, second)) = arena.value(body)
    else {
        panic!("`Path.product p q` is the native product");
    };
    assert!(
        matches!(arena.value(first), Some(&Value::Here(_)))
            && matches!(arena.value(second), Some(&Value::Equiv(..))),
        "both paths are read as values, in order"
    );
    let report = judged(&module, &mut arena);
    assert_accepted(&report);
    assert!(
        report.natives().contains_key(&body),
        "the checker elaborates the product to its native path"
    );

    let mut arena = CoreArena::new();
    let source = format!("{negation}def half = Path.product (equiv not not);\n");
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    assert!(
        matches!(
            outcome_of(&module, "half".into()),
            DeclarationOutcome::Refused(LoweringRefusal::OutOfFragment {
                boundary: FragmentBoundary::Arity(count),
                ..
            }) if count == OperandCount::from(1_usize)
        ),
        "a path product takes two paths"
    );
}

#[test]
fn a_flow_product_lowers_to_its_former()
{
    let negation =
        include_str!("tests/fixtures/a-path-product-lowers-to-its-former-negation.gandr");
    let mut arena = CoreArena::new();
    let source = format!("{negation}def paired = Flow.product (Flow.stay Unit) (Flow.into not);\n");
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let DeclarationOutcome::Bodied { body } = outcome_of(&module, "paired".into())
    else {
        panic!("the product lowers");
    };
    let Some(&Value::FlowProduct(first, second)) = arena.value(body)
    else {
        panic!("`Flow.product p q` is the kernel's flow product");
    };
    assert!(
        matches!(arena.value(first), Some(&Value::Stay(_)))
            && matches!(arena.value(second), Some(&Value::Forward(_))),
        "both flows are read as values, in order"
    );
    assert_accepted(&judged(&module, &mut arena));

    let mut arena = CoreArena::new();
    let source = format!("{negation}def half = Flow.product (Flow.into not);\n");
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    assert!(
        matches!(
            outcome_of(&module, "half".into()),
            DeclarationOutcome::Refused(LoweringRefusal::OutOfFragment {
                boundary: FragmentBoundary::Arity(count),
                ..
            }) if count == OperandCount::from(1_usize)
        ),
        "a flow product takes two flows"
    );
}

#[test]
fn a_computation_endpoint_is_the_value_it_returns()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/a-computation-endpoint-is-the-value-it-returns-module.gandr"
        )),
        &mut arena,
    );
    let Some(&Computation::Return(reflexivity)) =
        arena.computation(tail_of(&module, &arena, "same".into()))
    else {
        panic!("the body returns reflexivity");
    };
    let Some(&Value::Here(point)) = arena.value(reflexivity)
    else {
        panic!("`here(dbl(dbl(x)))` is reflexivity");
    };
    let Some(&Value::Returned(computation)) = arena.value(point)
    else {
        panic!("a computation's point is the value it returns");
    };
    let Some(&Computation::Application(_, argument)) = arena.computation(computation)
    else {
        panic!("the compound endpoint keeps the call");
    };
    assert!(
        matches!(arena.value(argument), Some(&Value::Returned(_))),
        "a call standing as an argument at an endpoint is the value it returns"
    );
    let DeclarationOutcome::Completed { declared_type, .. } = outcome_of(&module, "same".into())
    else {
        panic!("`same` lowers both halves");
    };
    let Some(&ValueType::Thunk(signature)) = arena.value_type(declared_type)
    else {
        panic!("a function's signature is a thunk type");
    };
    let Some(&gandr_core_term::CompType::Pi { codomain, .. }) = arena.comp_type(signature)
    else {
        panic!("a parameter an endpoint names binds dependently");
    };
    assert!(
        matches!(
            arena.comp_type(codomain),
            Some(&gandr_core_term::CompType::Arrow { .. })
        ),
        "a parameter no type names binds nothing"
    );
    assert!(
        matches!(
            module.origins().value(point),
            Maybe::Present(origin) if origin.provenance() == Provenance::Inserted(Insertion::Endpoint)
        ),
        "the compound endpoint is the lowering's insertion"
    );
    assert_accepted(&judged(&module, &mut arena));
}

/// #3697: a lambda passed to a function inside a path type's endpoint was
/// the value it returns, so the checker had to infer it, refused
/// `NotSynthesisable`. It is its thunk, as the function's parameter checks a
/// lambda in a body, and a type elaborates no nested computation.
#[test]
fn a_lambda_argument_in_an_endpoint_is_its_thunk_3697()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/a-lambda-argument-in-an-endpoint-is-its-thunk-3697-module.gandr"
        )),
        &mut arena,
    );
    for name in ["inTypeAnnotated", "inTypeBare"] {
        let DeclarationOutcome::Completed { declared_type, .. } = outcome_of(&module, name.into())
        else {
            panic!("`{name}` lowers both halves");
        };
        let Some(&ValueType::Path { left, .. }) = arena.value_type(declared_type)
        else {
            panic!("`{name}`'s signature is a path type");
        };
        let Some(&Value::Returned(call)) = arena.value(left)
        else {
            panic!("`{name}`'s left endpoint is the value the call returns");
        };
        let Some(&Computation::Application(_, argument)) = arena.computation(call)
        else {
            panic!("`{name}`'s endpoint applies `atTrue`");
        };
        assert!(
            matches!(arena.value(argument), Some(&Value::Thunk(_))),
            "`{name}`'s lambda is its thunk: {:?}",
            arena.value(argument)
        );
        assert!(
            matches!(
                module.origins().value(argument),
                Maybe::Present(origin) if origin.provenance() == Provenance::Inserted(Insertion::Thunk)
            ),
            "`{name}`'s thunk is the lowering's insertion"
        );
    }
    assert_accepted(&judged(&module, &mut arena));
}

/// #3767: a lambda written bare as a path type's endpoint, or as
/// reflexivity's point, was the value it returns, so the checker had to infer
/// it, refused `NotSynthesisable`. It is its thunk, as one written strictly
/// inside an endpoint is (#3697): the endpoint's carrier is the thunk type it
/// checks at.
#[test]
fn a_lambda_endpoint_is_its_thunk_3767()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/a-lambda-endpoint-is-its-thunk-3767-module.gandr"
        )),
        &mut arena,
    );
    // Both check: the checker meets each lambda as its thunk, at the
    // endpoint's carrier.
    assert_accepted(&judged(&module, &mut arena));
    let thunked = |at: gandr_core_term::ValueId| {
        matches!(arena.value(at), Some(&Value::Thunk(body)) if matches!(arena.computation(body), Some(&Computation::Lambda(_))))
            && matches!(
                module.origins().value(at),
                Maybe::Present(origin) if origin.provenance() == Provenance::Inserted(Insertion::Thunk)
            )
    };
    for name in ["direct", "result"] {
        let DeclarationOutcome::Completed {
            declared_type,
            body,
        } = outcome_of(&module, name.into())
        else {
            panic!("`{name}` lowers both halves");
        };
        let mut signature = declared_type;
        while let Some(&ValueType::Thunk(computation)) = arena.value_type(signature) {
            let Some(
                &gandr_core_term::CompType::Pi { codomain, .. }
                | &gandr_core_term::CompType::Arrow { codomain, .. },
            ) = arena.comp_type(computation)
            else {
                panic!("`{name}`'s signature is a function's");
            };
            let Some(&gandr_core_term::CompType::Returner { result, .. }) =
                arena.comp_type(codomain)
            else {
                panic!("`{name}`'s function returns its path");
            };
            signature = result;
        }
        let Some(&ValueType::Path { left, right, .. }) = arena.value_type(signature)
        else {
            panic!("`{name}`'s type is a path type");
        };
        assert!(
            thunked(left) && thunked(right),
            "`{name}`'s endpoints are their lambdas' thunks: {:?} and {:?}",
            arena.value(left),
            arena.value(right)
        );
        // A value definition's body is reflexivity itself, and a function's
        // returns it.
        let reflexivity = if matches!(arena.value(body), Some(&Value::Here(_))) {
            body
        }
        else {
            let Some(&Computation::Return(returned)) =
                arena.computation(tail_of(&module, &arena, name.into()))
            else {
                panic!("`{name}`'s body returns reflexivity");
            };
            returned
        };
        let Some(&Value::Here(point)) = arena.value(reflexivity)
        else {
            panic!("`{name}`'s body is `here`");
        };
        assert!(
            thunked(point),
            "`{name}`'s point is its lambda's thunk: {:?}",
            arena.value(point)
        );
    }
}

/// #3787: `cong` lifts a suspended function into its motive, and only the
/// lift's root carried the function's bytes, so the editor had no entry in
/// the function. Each node of the lift carries the bytes of the node it
/// copies.
#[test]
fn a_suspended_function_cong_lifts_answers_at_its_own_bytes_3787()
{
    let source = include_str!(
        "tests/unformatted/a-suspended-function-cong-lifts-answers-at-its-own-bytes-3787.gandr"
    );
    let spanned = |text: &str| {
        let start = source.find(text).expect("the source writes the text");
        (start, start.saturating_add(text.len()))
    };
    let thunk = spanned("thunk { fun (q : Path[.A = A](x, y)) { Path.step q g } }");
    let function = spanned("fun (q : Path[.A = A](x, y)) { Path.step q g }");
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source), &mut arena);
    let at =
        |span: gandr_surface_syntax::ByteSpan| (usize::from(span.start()), usize::from(span.end()));
    let lambdas: Vec<_> = module
        .origins()
        .values()
        .iter()
        .filter(|&&(_, origin)| at(origin.span()) == thunk)
        .filter_map(|&(id, _)| match arena.value(id) {
            Some(&Value::Thunk(lambda)) => Some(lambda),
            _ => None,
        })
        .collect();
    assert!(
        lambdas.len() >= 2,
        "the written function and its lift both answer at the thunk's bytes: {lambdas:?}"
    );
    for lambda in lambdas {
        assert!(
            matches!(
                module.origins().computation(lambda),
                Maybe::Present(origin) if at(origin.span()) == function
                    && origin.provenance() != Provenance::Inserted(Insertion::Identity)
            ),
            "each lambda under the thunk answers at the function's bytes: {:?}",
            module.origins().computation(lambda)
        );
    }
    assert_accepted(&judged(&module, &mut arena));
}

/// #3801: an annotation inside a type reads its names in the type's
/// telescope, as the term it annotates does. A parameter no type names,
/// `u`, binds nothing there, so the thunk's ascription, its typed
/// parameter and its typed bind each count `A` past only the binders the
/// type has, never past `u`.
#[test]
fn an_annotation_inside_a_type_reads_in_the_type_s_telescope_3801()
{
    let source = "def t(A : Type, x : A, y : A, f : Path[.A = A](x, y), u : A, it : Path[.A = Path[.A = A](x, y)](\
                  f, (thunk { fun (q : Path[.A = A](x, y)) { let c : Path[.A = A](x, y) = q ; c } } : \
                  Path[.A = A](x, y) -> Path[.A = A](x, y)) f)) -> -F Unit { return *{} }\n";
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source), &mut arena);
    let DeclarationOutcome::Completed { declared_type, .. } = outcome_of(&module, "t".into())
    else {
        panic!("`t` lowers");
    };
    let Some(&ValueType::Thunk(mut at)) = arena.value_type(declared_type)
    else {
        panic!("the signature lowers to a thunked function type");
    };
    // The last parameter's type, the one whose codomain is the result.
    let it = loop {
        let Some(
            &(gandr_core_term::CompType::Pi { domain, codomain }
            | gandr_core_term::CompType::Arrow { domain, codomain }),
        ) = arena.comp_type(at)
        else {
            panic!("a parameter: {:?}", arena.comp_type(at));
        };
        if matches!(
            arena.comp_type(codomain),
            Some(&gandr_core_term::CompType::Returner { .. })
        ) {
            break domain;
        }
        at = codomain;
    };
    // The index of the binder a path type's carrier decodes.
    let carrier = |ty: gandr_core_term::ValueTypeId| {
        let &ValueType::Path { carrier, .. } = arena.value_type(ty)?
        else {
            return None;
        };
        let &ValueType::Element { code, .. } = arena.value_type(carrier)?
        else {
            return None;
        };
        let &Value::Variable { index, .. } = arena.value(code)?
        else {
            return None;
        };
        Some(u32::from(index))
    };
    let returned = |ty: gandr_core_term::CompTypeId| {
        let &gandr_core_term::CompType::Returner { result, .. } = arena.comp_type(ty)?
        else {
            return None;
        };
        Some(result)
    };
    let Some(&ValueType::Path { right, .. }) = arena.value_type(it)
    else {
        panic!("the parameter's type is the path type written");
    };
    let Some(&Value::Returned(applied)) = arena.value(right)
    else {
        panic!("the endpoint is the value its application returns");
    };
    let Some(&Computation::Application(forced, _)) = arena.computation(applied)
    else {
        panic!("the endpoint applies the thunk");
    };
    let Some(&Computation::Force(ascribed)) = arena.computation(forced)
    else {
        panic!("the application forces the thunk");
    };
    let Some(&Value::Ascribe { value, ty }) = arena.value(ascribed)
    else {
        panic!("the thunk is ascribed its written type");
    };
    let Some(&ValueType::Thunk(arrow)) = arena.value_type(ty)
    else {
        panic!("the ascription is a thunked arrow");
    };
    let Some(&gandr_core_term::CompType::Arrow { domain, codomain }) = arena.comp_type(arrow)
    else {
        panic!("the ascription's arrow binds nothing");
    };
    // `A` past `x`, `y` and `f`; `u` binds nothing in the type.
    assert_eq!(
        carrier(domain),
        Some(3),
        "the ascription's domain reads `A` past `f`"
    );
    assert_eq!(
        returned(codomain).and_then(carrier),
        Some(3),
        "the ascription's codomain reads `A` past `f`"
    );
    let Some(&Value::Thunk(suspended)) = arena.value(value)
    else {
        panic!("the ascribed value is the thunk");
    };
    let Some(&Computation::Lambda(under)) = arena.computation(suspended)
    else {
        panic!("the thunk suspends the lambda");
    };
    let Some(&Computation::Bind(parameter, rest)) = arena.computation(under)
    else {
        panic!("the typed parameter is bound over the body");
    };
    let Some(&Computation::Ascribe { ty: declared, .. }) = arena.computation(parameter)
    else {
        panic!("the argument is ascribed the parameter's written type");
    };
    assert_eq!(
        returned(declared).and_then(carrier),
        Some(4),
        "the typed parameter reads `A` past the lambda's own binder"
    );
    let Some(&Computation::Bind(bound, _)) = arena.computation(rest)
    else {
        panic!("the typed let is bound over the block's end");
    };
    let Some(&Computation::Return(returned_value)) = arena.computation(bound)
    else {
        panic!("the typed let returns its value");
    };
    let Some(&Value::Ascribe { ty: annotated, .. }) = arena.value(returned_value)
    else {
        panic!("the returned value is ascribed the annotation");
    };
    assert_eq!(
        carrier(annotated),
        Some(5),
        "the typed let reads `A` past the lambda's binder and the parameter's bind"
    );
}

#[test]
fn a_type_endpoint_is_quoted()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from("def t : Path[.A = Type](Integer, Integer);\n"),
        &mut arena,
    );
    let DeclarationOutcome::Uncompleted { declared_type } = outcome_of(&module, "t".into())
    else {
        panic!("the signature lowers");
    };
    let Some(&ValueType::Path { left, .. }) = arena.value_type(declared_type)
    else {
        panic!("the signature is a path type");
    };
    assert!(
        matches!(
            module.origins().value(left),
            Maybe::Present(origin) if origin.provenance() == Provenance::Inserted(Insertion::Quote)
        ),
        "a type standing as an endpoint is quoted"
    );
}

/// A path at a universe its own tiles spell reads each endpoint at the type
/// sort: a sum and a session protocol, neither of which reads as a value,
/// each stand as the quoted code of the type it spells.
#[test]
fn a_path_at_a_universe_reads_its_endpoints_as_types_402()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/a-path-at-a-universe-reads-its-endpoints-as-types-402-module.gandr"
        )),
        &mut arena,
    );
    for name in ["sums", "sessions"] {
        let DeclarationOutcome::Uncompleted { declared_type } = outcome_of(&module, name.into())
        else {
            panic!("{name}'s signature lowers");
        };
        let Some(&ValueType::Path { left, right, .. }) = arena.value_type(declared_type)
        else {
            panic!("{name}'s signature is a path type");
        };
        for endpoint in [left, right] {
            assert!(
                matches!(arena.value(endpoint), Some(&Value::Quote(_))),
                "{name}'s endpoint is a quoted code"
            );
        }
    }
}

#[test]
fn a_bridge_type_lowers_to_the_core_bridge_3427()
{
    // A bridge's endpoints are terms, as a path's are: a list stands as its
    // cells and, at a universe, a type as its quoted code. The lifting at a
    // list and a relation at the universe check at the fibres the core fold
    // reads; reflexivity is no bridge's introduction.
    let mut arena = CoreArena::new();
    let source = listing(include_str!(
        "tests/unformatted/a-bridge-type-lowers-to-the-core-bridge-3427.gandr"
    ));
    let module = listed(&source, &mut arena);
    for (name, endpoint) in [("lifted", "a list cell"), ("related", "a quoted code")] {
        let DeclarationOutcome::Completed { declared_type, .. } = outcome_of(&module, name.into())
        else {
            panic!("{name} lowers");
        };
        let Some(&ValueType::Bridge { left, right, .. }) = arena.value_type(declared_type)
        else {
            panic!("{name}'s signature is a bridge type");
        };
        for end in [left, right] {
            assert!(
                matches!(
                    (name, arena.value(end)),
                    ("lifted", Some(&Value::ListCons(..))) | ("related", Some(&Value::Quote(_)))
                ),
                "{name}'s endpoint is {endpoint}"
            );
        }
    }
    assert_accepted(&judged(&module, &mut arena));

    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/unformatted/a-bridge-type-lowers-to-the-core-bridge-3427-module.gandr"
        )),
        &mut arena,
    );
    let report = judged(&module, &mut arena);
    assert!(
        report.judged().iter().any(|judged| matches!(
            judged.verdict(),
            Verdict::Refused(CheckRefusal::ShapeMismatch { .. })
        )),
        "`here` is refused at a bridge, which has no reflexivity: {report:?}"
    );
}

#[test]
fn a_bound_name_shadows_an_identity_operation()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/a-bound-name-shadows-an-identity-operation-module.gandr"
        )),
        &mut arena,
    );
    assert!(
        matches!(
            arena.computation(tail_of(&module, &arena, "apply".into())),
            Some(&Computation::Application(..))
        ),
        "a parameter named `here` is applied, not taken for reflexivity"
    );
}

#[test]
fn back_then_and_cong_unfold_to_transports()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/back-then-and-cong-unfold-to-transports-module.gandr"
        )),
        &mut arena,
    );
    let transport = |name: &str| {
        let tail = tail_of(&module, &arena, name.into());
        let tail = if name == "join" {
            folded(&arena, tail)
        }
        else {
            tail
        };
        match arena.computation(tail) {
            Some(&Computation::PathTransport {
                motive,
                path,
                value,
            }) => (motive, path, value),
            other => panic!("`{name}` unfolds to a transport: {other:?}"),
        }
    };

    let (motive, path, value) = transport("flip");
    assert!(
        arena.value(path) == Some(&variable(0_u32.into())),
        "`back` transports along its path"
    );
    assert!(
        matches!(arena.value(value), Some(&Value::Here(_))),
        "`back` starts from reflexivity"
    );
    assert!(
        matches!(arena.value_type(motive), Some(&ValueType::Path { left, .. }) if arena.value(left) == Some(&variable(0_u32.into()))),
        "`back`'s motive moves its left endpoint"
    );
    assert!(
        matches!(
            module.origins().value_type(motive),
            Maybe::Present(origin) if origin.provenance() == Provenance::Inserted(Insertion::Identity)
        ),
        "the motive is the lowering's insertion"
    );

    let (motive, path, value) = transport("join");
    assert!(
        arena.value(path) == Some(&variable(0_u32.into()))
            && arena.value(value) == Some(&variable(1_u32.into())),
        "`p then q` transports `p` along `q`"
    );
    assert!(
        matches!(arena.value_type(motive), Some(&ValueType::Path { right, .. }) if arena.value(right) == Some(&variable(0_u32.into()))),
        "`then`'s motive moves its right endpoint"
    );

    let (motive, path, value) = transport("image");
    assert!(
        arena.value(path) == Some(&variable(0_u32.into())),
        "`cong` transports along its path"
    );
    let Some(&Value::Here(start)) = arena.value(value)
    else {
        panic!("`cong` starts from reflexivity");
    };
    assert!(
        matches!(arena.value(start), Some(&Value::Returned(_))),
        "`cong` starts at the image the answer writes"
    );
    assert!(
        matches!(
            arena.value_type(motive),
            Some(&ValueType::Path { right, .. })
                if matches!(arena.value(right), Some(&Value::Returned(_)))
        ),
        "`cong`'s moving endpoint is the map's image"
    );

    assert_accepted(&judged(&module, &mut arena));
}

/// #3772: `cong` and `then` inside a type were refused `Unannotated`,
/// though each operand's type is known. Each synthesises its type from its
/// operands, so every declaration of the fixture lowers and checks.
#[test]
fn then_and_cong_in_a_type_take_their_types_from_their_operands_3772()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "../../../../../corpus/model/identity/then-and-cong-in-a-type.gandr"
        )),
        &mut arena,
    );
    for name in [
        "congInAType",
        "thenCongInAType",
        "inductiveAssociator",
        "hereThenAssocInAType",
    ] {
        assert!(
            !matches!(
                outcome_of(&module, name.into()),
                DeclarationOutcome::Refused(_)
            ),
            "`{name}` lowers: {:?}",
            outcome_of(&module, name.into())
        );
    }
    assert_accepted(&judged(&module, &mut arena));
}

/// #3834: a reflexivity `Path.here(x)` read its type only when `x`'s binder wrote
/// a path type, so `then` refused one first as unannotated, and a composite
/// ending in one first too. `Path.here(x)` reads `Path[.A = A](x, x)` off a
/// binder written at `A`, so the fixture's declarations lower and check.
#[test]
fn a_reflexivity_composes_at_a_point_of_any_type_3834()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "../../../../../corpus/model/identity/reflexivity-composed-in-a-type.gandr"
        )),
        &mut arena,
    );
    for name in ["hereFirst", "endsInHere", "hereTwice"] {
        assert!(
            matches!(
                outcome_of(&module, name.into()),
                DeclarationOutcome::Completed { .. }
            ),
            "`{name}` lowers its type and its body: {:?}",
            outcome_of(&module, name.into())
        );
    }
    assert_accepted(&judged(&module, &mut arena));
}

/// #3773: a lambda `fun (q) { e }` as `cong`'s function was refused, its
/// binder with no type. The binder takes the type of the path's points, so
/// the fixture's declaration lowers and checks. The transport the printer
/// spells it as, `Path.step(b, g)` over its motive's binder, lowers and checks
/// too.
#[test]
fn a_lambda_as_congs_function_is_a_function_of_the_paths_points_3773()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "../../../../../corpus/model/identity/cong-over-a-lambda.gandr"
        )),
        &mut arena,
    );
    assert!(
        !matches!(
            outcome_of(&module, "whiskerRight".into()),
            DeclarationOutcome::Refused(_)
        ),
        "`whiskerRight` lowers: {:?}",
        outcome_of(&module, "whiskerRight".into())
    );
    assert_accepted(&judged(&module, &mut arena));
    let spelled = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/a-lambda-as-congs-function-is-a-function-of-the-paths-points-3773-spelled.gandr"
        )),
        &mut arena,
    );
    assert!(
        !matches!(
            outcome_of(&spelled, "whiskered".into()),
            DeclarationOutcome::Refused(_)
        ),
        "the motive's binder reads its path's type: {:?}",
        outcome_of(&spelled, "whiskered".into())
    );
    assert_accepted(&judged(&spelled, &mut arena));
}

/// #3829: `cong` over a lambda was refused `Unannotated` wherever its
/// position answered no path type. It reads its codomain off the path type
/// the lambda's body synthesises under the binder, so it stands under `then`
/// in a body and as an endpoint of a stated path type.
#[test]
fn a_lambda_cong_maps_synthesises_its_path_where_none_is_answered_3829()
{
    let telescope = "(A : Type, x : A, y : A, z : A, f1 : Path[.A = A](x, y), f2 : Path[.A = A](x, y), a : \
                     Path[.A = Path[.A = A](x, y)](f1, f2), g : Path[.A = A](y, z))";
    let whisker = "Path.ap (fun (q) { Path.step q g }) a";
    let source = format!(
        include_str!(
            "tests/unformatted/a-lambda-cong-maps-synthesises-its-path-where-none-is-answered-3829.gandr"
        ),
        telescope = telescope,
        whisker = whisker
    );
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    for name in ["underThen", "asEndpoint"] {
        assert!(
            !matches!(
                outcome_of(&module, name.into()),
                DeclarationOutcome::Refused(_)
            ),
            "`{name}` lowers: {:?}",
            outcome_of(&module, name.into())
        );
    }
    let Some(&Computation::PathTransport { value, .. }) =
        arena.computation(folded(&arena, tail_of(&module, &arena, "underThen".into())))
    else {
        panic!("`then` unfolds to a transport");
    };
    assert!(
        matches!(
            arena.value(value),
            Some(&Value::Returned(inner))
                if matches!(arena.computation(inner), Some(&Computation::PathTransport { .. }))
        ),
        "`then` transports the value `cong`'s transport returns: {:?}",
        arena.value(value)
    );
    assert_accepted(&judged(&module, &mut arena));
    let unwritten = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/a-lambda-cong-maps-synthesises-its-path-where-none-is-answered-3829-unwritten.gandr"
        )),
        &mut arena,
    );
    assert!(
        matches!(
            outcome_of(&unwritten, "unwritten".into()),
            DeclarationOutcome::Refused(LoweringRefusal::OutOfFragment {
                boundary: FragmentBoundary::Unannotated,
                ..
            })
        ),
        "a lambda over a path whose type the source does not write is unannotated: {:?}",
        outcome_of(&unwritten, "unwritten".into())
    );
}

/// #3919: `cong` over a lambda that states its binder's type faulted
/// `UnboundIndex` in a type, its codomain read one binder too deep. The
/// stated lambda reads the codomain the unstated one does, in a body and as
/// an endpoint of a stated path type.
#[test]
fn a_lambda_stating_its_binders_type_maps_as_the_unstated_one_3919()
{
    let telescope = "(A : Type, x : A, y : A, z : A, f1 : Path[.A = A](x, y), f2 : Path[.A = A](x, y), a : \
                     Path[.A = Path[.A = A](x, y)](f1, f2), g : Path[.A = A](y, z))";
    let whisker = "Path.ap (fun (q : Path[.A = A](x, y)) { Path.step q g }) a";
    let source = format!(
        include_str!(
            "tests/unformatted/a-lambda-cong-maps-synthesises-its-path-where-none-is-answered-3829.gandr"
        ),
        telescope = telescope,
        whisker = whisker
    );
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    for name in ["underThen", "asEndpoint"] {
        assert!(
            !matches!(
                outcome_of(&module, name.into()),
                DeclarationOutcome::Refused(_)
            ),
            "`{name}` lowers: {:?}",
            outcome_of(&module, name.into())
        );
    }
    assert_accepted(&judged(&module, &mut arena));
}

/// #3786: a transport through a family a parameter names, `P : A -> Type`,
/// was refused in a body and in a type when the motive named `P`, and in a
/// body when the motive called it, `fun (a) { P a }`. The named motive moves
/// through `a. ⟨force P a⟩`, and the called one reads `P` past every parameter
/// no type names.
#[test]
fn a_transport_moves_through_a_family_a_parameter_names_3786()
{
    let telescope = "(A : Type, P : A -> Type, x : A, y : A, p : Path[.A = A](x, y), v : P(x))";
    let source = format!(
        include_str!(
            "tests/unformatted/a-transport-moves-through-a-family-a-parameter-names-3786.gandr"
        ),
        telescope = telescope
    );
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    for name in ["movedNamed", "movedLambda", "statedNamed", "movedLate"] {
        assert!(
            !matches!(
                outcome_of(&module, name.into()),
                DeclarationOutcome::Refused(_)
            ),
            "`{name}` lowers: {:?}",
            outcome_of(&module, name.into())
        );
    }
    let Some(&Computation::PathTransport { motive, .. }) =
        arena.computation(tail_of(&module, &arena, "movedNamed".into()))
    else {
        panic!("`movedNamed` is a transport");
    };
    let called = match arena.value_type(motive) {
        Some(&ValueType::Element { code, .. }) => match arena.value(code) {
            Some(&Value::Returned(called)) => called,
            other => panic!("the family is the code a call returns: {other:?}"),
        },
        other => panic!("the family decodes a code: {other:?}"),
    };
    let Some(&Computation::Application(forced, point)) = arena.computation(called)
    else {
        panic!("the family calls `P` at its binder");
    };
    assert_eq!(
        arena.value(point),
        Some(&variable(DeBruijnIndex::from(0_u32))),
        "`P` is called at the family's binder"
    );
    let Some(&Computation::Force(head)) = arena.computation(forced)
    else {
        panic!("the family forces `P`");
    };
    assert_eq!(
        arena.value(head),
        Some(&variable(DeBruijnIndex::from(5_u32))),
        "`P` stands past the binder and the four parameters after it"
    );
    assert_accepted(&judged(&module, &mut arena));
    let typed = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/a-transport-moves-through-a-family-a-parameter-names-3786-typed.gandr"
        )),
        &mut arena,
    );
    assert!(
        matches!(
            outcome_of(&typed, "typed".into()),
            DeclarationOutcome::Refused(LoweringRefusal::OutOfFragment {
                boundary: FragmentBoundary::Unannotated,
                ..
            })
        ),
        "a parameter holding no family is no motive: {:?}",
        outcome_of(&typed, "typed".into())
    );
}

/// The transport `cong` unfolds to reads its map only lifted under the
/// motive's binder; a parameter map's lift is the written map's copy, so it
/// answers at the map's bytes (#443).
#[test]
fn a_parameter_map_under_cong_answers_at_its_bytes_443()
{
    let source =
        include_str!("tests/fixtures/a-parameter-map-under-cong-answers-at-its-bytes-443.gandr");
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source), &mut arena);
    let Some(&Computation::PathTransport { motive, .. }) =
        arena.computation(tail_of(&module, &arena, "mapped".into()))
    else {
        panic!("`cong` unfolds to a transport");
    };
    let lifted = match arena.value_type(motive) {
        Some(&ValueType::Path { right, .. }) => match arena.value(right) {
            Some(&Value::Returned(applied)) => match arena.computation(applied) {
                Some(&Computation::Application(forced, _)) => match arena.computation(forced) {
                    Some(&Computation::Force(lifted)) => lifted,
                    other => panic!("the image forces the map: {other:?}"),
                },
                other => panic!("the image applies the map: {other:?}"),
            },
            other => panic!("the moving endpoint is the map's image: {other:?}"),
        },
        other => panic!("the motive is a path type: {other:?}"),
    };
    let at = source
        .find("Path.ap f")
        .expect("the body writes `Path.ap f`")
        .saturating_add(8);
    assert_eq!(
        module
            .origins()
            .value(lifted)
            .map(|origin| (origin.span(), origin.provenance())),
        Maybe::Present((
            span(ByteOffset::from(at), ByteOffset::from(at.saturating_add(1))),
            Provenance::Written
        )),
        "the lifted map answers at the written `f`"
    );
    assert_accepted(&judged(&module, &mut arena));
}

#[test]
fn a_derived_operation_needs_a_written_path_answer()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/unformatted/a-derived-operation-needs-a-written-path-answer-module.gandr"
        )),
        &mut arena,
    );
    for name in ["g", "three"] {
        assert!(
            matches!(
                outcome_of(&module, name.into()),
                DeclarationOutcome::Refused(LoweringRefusal::OutOfFragment {
                    boundary: FragmentBoundary::Unannotated,
                    ..
                })
            ),
            "`back` reads its motive off a written path or flow answer, `Flow` at three \
             arguments, not `{name}`'s: {:?}",
            outcome_of(&module, name.into())
        );
    }
}

/// #985: a written transport read as a value is the value it returns, as the
/// derived composite's fold is, so `Path.step(loop, loop)` and its explicit
/// spelling lower to one transport; before, the written one nested a run that
/// no computation encloses.
#[test]
fn a_written_transport_read_as_a_value_is_the_value_it_returns_985()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/a-written-transport-read-as-a-value-is-the-value-it-returns-985-module.gandr"
        )),
        &mut arena,
    );
    for name in ["derived", "written"] {
        let body = match outcome_of(&module, name.into()) {
            DeclarationOutcome::Completed { body, .. } => body,
            other @ (DeclarationOutcome::Uncompleted { .. }
            | DeclarationOutcome::Bodied { .. }
            | DeclarationOutcome::Data(_)
            | DeclarationOutcome::Codata(_)
            | DeclarationOutcome::Abstract(_)
            | DeclarationOutcome::World
            | DeclarationOutcome::Refused(_)) => panic!("`{name}` lowers both halves: {other:?}"),
        };
        let Some(&Value::Returned(computation)) = arena.value(body)
        else {
            panic!("`{name}` is a returned value: {:?}", arena.value(body));
        };
        let computation = if name == "derived" {
            folded(&arena, computation)
        }
        else {
            computation
        };
        assert!(
            matches!(
                arena.computation(computation),
                Some(&Computation::PathTransport { .. })
            ),
            "`{name}` is the value its transport returns: {:?}",
            arena.computation(computation)
        );
    }
}

/// #1003: `Path.back(loop)` at the circle's point moves the empty word, as the
/// written transport's `Path.here(Base)` lowers there, so the two spellings
/// lower to one transport. Away from a looped point it moves `here`, as
/// `back_then_and_cong_unfold_to_transports` pins.
#[test]
fn back_at_a_looped_point_moves_its_empty_word_1003()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/back-at-a-looped-point-moves-its-empty-word-1003-module.gandr"
        )),
        &mut arena,
    );
    let moved = |name: &str| {
        let body = match outcome_of(&module, name.into()) {
            DeclarationOutcome::Completed { body, .. } => body,
            other @ (DeclarationOutcome::Uncompleted { .. }
            | DeclarationOutcome::Bodied { .. }
            | DeclarationOutcome::Data(_)
            | DeclarationOutcome::Codata(_)
            | DeclarationOutcome::Abstract(_)
            | DeclarationOutcome::World
            | DeclarationOutcome::Refused(_)) => panic!("`{name}` lowers both halves: {other:?}"),
        };
        // The derived inverse is returned; the written transport, in value
        // position, is nested.
        let Some(&(Value::Returned(computation) | Value::Nested(computation))) = arena.value(body)
        else {
            panic!("`{name}` is the value its transport returns");
        };
        let Some(&Computation::PathTransport { value, .. }) = arena.computation(computation)
        else {
            panic!("`{name}` is a transport");
        };
        value
    };
    let empty = |name: &str| match arena.value(moved(name)) {
        Some(&Value::Constructor {
            datatype,
            ref fields,
            ..
        }) if fields.is_empty() => arena.value_type(datatype).cloned(),
        other => panic!("`{name}` moves a nullary constructor: {other:?}"),
    };
    assert_eq!(
        empty("derived"),
        empty("written"),
        "the derived inverse moves the empty word the written `here(Base)` is"
    );
}

#[test]
fn a_derived_operation_synthesises_its_path_at_the_words()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/unformatted/a-derived-operation-synthesises-its-path-at-the-words-module.gandr"
        )),
        &mut arena,
    );
    let transport = |value, name: &str| {
        let Some(&Value::Returned(computation)) = arena.value(value)
        else {
            panic!("`{name}` is the value its transport returns");
        };
        // `then` returns its composite, whose fold is the transport.
        let computation = if matches!(
            arena.computation(computation),
            Some(&Computation::Return(_))
        ) {
            folded(&arena, computation)
        }
        else {
            computation
        };
        match arena.computation(computation) {
            Some(&Computation::PathTransport {
                motive,
                path,
                value,
            }) => (motive, path, value),
            other => panic!("`{name}` unfolds to a transport: {other:?}"),
        }
    };
    let body = |name: &str| match outcome_of(&module, name.into()) {
        DeclarationOutcome::Completed { body, .. } => body,
        other @ (DeclarationOutcome::Uncompleted { .. }
        | DeclarationOutcome::Bodied { .. }
        | DeclarationOutcome::Data(_)
        | DeclarationOutcome::Codata(_)
        | DeclarationOutcome::Abstract(_)
        | DeclarationOutcome::World
        | DeclarationOutcome::Refused(_)) => panic!("`{name}` lowers both halves: {other:?}"),
    };
    let moving = |at| arena.value(at) == Some(&variable(0_u32.into()));

    let (motive, path, value) = transport(body("two"), "two");
    assert!(
        matches!(arena.value(path), Some(&Value::Constant(_)))
            && matches!(arena.value(value), Some(&Value::Constant(_))),
        "`loop then loop` transports the loop along the loop"
    );
    assert!(
        matches!(
            arena.value_type(motive),
            Some(&ValueType::Path { left, right, .. })
                if matches!(arena.value(left), Some(&Value::Constructor { .. })) && moving(right)
        ),
        "the composite starts at the point the loop's words spell and moves its end"
    );

    let (motive, path, value) = transport(body("emptyFirst"), "emptyFirst");
    assert!(
        matches!(arena.value(path), Some(&Value::Constant(_)))
            && matches!(arena.value(value), Some(&Value::Constructor { .. }))
            && matches!(
                arena.value_type(motive),
                Some(&ValueType::Path { left, right, .. })
                    if matches!(arena.value(left), Some(&Value::Constructor { .. })) && moving(right)
            ),
        "the empty word first is a word too: its composite transports it along the loop, from \
         the point the words spell"
    );

    let (motive, path, _) = transport(body("undone"), "undone");
    let (inner, ..) = transport(path, "the composite under `back`");
    assert!(
        matches!(arena.value_type(motive), Some(&ValueType::Path { left, .. }) if moving(left))
            && matches!(arena.value_type(inner), Some(&ValueType::Path { right, .. }) if moving(right)),
        "`back` reads the composite's own path type, the composite standing as its value"
    );

    let DeclarationOutcome::Uncompleted { declared_type } = outcome_of(&module, "collapsed".into())
    else {
        panic!("`collapsed` lowers its signature");
    };
    let Some(&ValueType::Path { left, .. }) = arena.value_type(declared_type)
    else {
        panic!("`collapsed` states a path type");
    };
    let (motive, ..) = transport(left, "`cong(collapse, loop)`");
    assert!(
        matches!(
            arena.value_type(motive),
            Some(&ValueType::Path { left, right, .. })
                if matches!(arena.value(left), Some(&Value::Returned(_)))
                    && matches!(arena.value(right), Some(&Value::Returned(_)))
        ),
        "`cong` in a type maps the loop's point and its moving end through the collapse"
    );
    assert!(
        matches!(
            module.origins().value_type(motive),
            Maybe::Present(origin) if origin.provenance() == Provenance::Inserted(Insertion::Identity)
        ),
        "the synthesised motive is the lowering's insertion"
    );

    for (name, refused) in [
        ("unread", FragmentBoundary::Unannotated),
        ("pointed", FragmentBoundary::NotAFunction),
        ("over_broken", FragmentBoundary::Unannotated),
    ] {
        assert!(
            matches!(
                outcome_of(&module, name.into()),
                DeclarationOutcome::Refused(LoweringRefusal::OutOfFragment { boundary, .. })
                    if boundary == refused
            ),
            "`{name}` is refused as {refused:?}"
        );
    }
}

#[test]
fn a_derived_operation_reads_a_parameter_or_a_call()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/a-derived-operation-reads-a-parameter-or-a-call-module.gandr"
        )),
        &mut arena,
    );
    for name in [
        "inBody",
        "inType",
        "overCall",
        "inTypeCall",
        "later",
        "overSig",
        "descend",
        "mapped",
        "unjoined",
    ] {
        assert!(
            matches!(
                outcome_of(&module, name.into()),
                DeclarationOutcome::Completed { .. }
            ),
            "`{name}` reads its operand's path type"
        );
    }
    assert!(
        matches!(
            outcome_of(&module, "pointed".into()),
            DeclarationOutcome::Refused(LoweringRefusal::OutOfFragment {
                boundary: FragmentBoundary::Unannotated,
                ..
            })
        ),
        "a parameter of no path type gives no path to read"
    );
    assert!(
        matches!(
            outcome_of(&module, "joined".into()),
            DeclarationOutcome::Uncompleted { .. }
        ),
        "a signature reads its own parameters' path types"
    );
}

/// #2995: before the fix, `back` and `then` over a named path read no type
/// off the name, so a value declared as either was refused as unannotated
/// though its type and its operand's were stated.
#[test]
fn a_derived_operation_reads_a_named_paths_stated_type_2995()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/a-derived-operation-reads-a-named-paths-stated-type-2995-module.gandr"
        )),
        &mut arena,
    );
    for name in ["flipped", "round"] {
        assert!(
            matches!(
                outcome_of(&module, name.into()),
                DeclarationOutcome::Completed { .. }
            ),
            "`{name}` reads the path type `named` states: {:?}",
            outcome_of(&module, name.into())
        );
    }
    assert!(
        matches!(
            outcome_of(&module, "overUnstated".into()),
            DeclarationOutcome::Refused(LoweringRefusal::OutOfFragment {
                boundary: FragmentBoundary::Unannotated,
                ..
            })
        ),
        "a name stating no type gives no path to read"
    );
}

/// #812: before the fix, a call read its callee's dependent result through
/// the box `(a : A) -> B` but not through the thunk it stands for, `+U ((a
/// : A) -> -F B)`, so the explicit spelling refused the call as unannotated.
#[test]
fn a_call_reads_a_dependent_result_through_either_spelling_812()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/a-call-reads-a-dependent-result-through-either-spelling-812-module.gandr"
        )),
        &mut arena,
    );
    for name in ["overSugared", "overThunked", "overPair"] {
        assert!(
            matches!(
                outcome_of(&module, name.into()),
                DeclarationOutcome::Completed { .. }
            ),
            "`{name}` reads its call's path type"
        );
    }
}

/// A call reads a path result its callee's signature states with no binder,
/// through the box `A -> B` and through the plain arrow `+U (A -> -F B)` it
/// stands for.
#[test]
fn a_call_reads_a_non_dependent_result_through_either_spelling()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/a-call-reads-a-non-dependent-result-through-either-spelling-module.gandr"
        )),
        &mut arena,
    );
    for name in ["overSugared", "overThunked"] {
        assert!(
            matches!(
                outcome_of(&module, name.into()),
                DeclarationOutcome::Completed { .. }
            ),
            "`{name}` reads its call's path type: {:?}",
            outcome_of(&module, name.into())
        );
    }
}

/// A recursive call's descent reads its path result under a uniform leading
/// parameter, which the call passes through unchanged.
#[test]
fn a_descent_reads_its_path_result_past_a_leading_parameter()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/a-descent-reads-its-path-result-past-a-leading-parameter-module.gandr"
        )),
        &mut arena,
    );
    assert!(
        matches!(
            outcome_of(&module, "descend".into()),
            DeclarationOutcome::Completed { .. }
        ),
        "the descent's path type reads its own argument past `k`: {:?}",
        outcome_of(&module, "descend".into())
    );
}

/// #791: before the fix, a `cong` whose answer is synthesised read its map's
/// codomain only off `+U (A -> -F B)`, so a parameter stated as `A => B`, the
/// same type, refused the operation as unannotated.
#[test]
fn cong_reads_a_map_stated_as_a_value_function_791()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/cong-reads-a-map-stated-as-a-value-function-791-module.gandr"
        )),
        &mut arena,
    );
    for name in ["explicit", "sugared", "grouped"] {
        assert!(
            matches!(
                outcome_of(&module, name.into()),
                DeclarationOutcome::Completed { .. }
            ),
            "`{name}` reads its map's codomain: {:?}",
            outcome_of(&module, name.into())
        );
    }
}

/// #778: before the fix, a synthesised `cong` read a declaration's codomain
/// only off a function definition's written result, so a map declared by its
/// signature, `def f : A => B ;` or `def f : +U (A -> -F B) ;`, as the printer
/// writes every function, refused the operation as unannotated.
#[test]
fn cong_reads_a_map_its_signature_states_778()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/cong-reads-a-map-its-signature-states-778-module.gandr"
        )),
        &mut arena,
    );
    for name in ["overSugared", "overExplicit"] {
        assert!(
            matches!(
                outcome_of(&module, name.into()),
                DeclarationOutcome::Completed { .. }
            ),
            "`{name}` reads its map's codomain: {:?}",
            outcome_of(&module, name.into())
        );
    }
}

/// `Path.ap` of a map on a 2-cell parameter, one path type above the map's
/// domain, moves the cell by the map's action on the paths below: the
/// transport starts at `Path.ap` of the map at the reflexivity, which is
/// itself a transport. On a loop parameter at the map's domain no transport
/// stands below the start, as before.
#[test]
fn cong_on_a_cell_above_the_map_s_domain_takes_its_levels()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/cong-on-a-cell-above-the-map-s-domain-takes-its-levels-module.gandr"
        )),
        &mut arena,
    );
    let start = |name: &str| {
        let tail = tail_of(&module, &arena, name.into());
        let Some(&Computation::PathTransport { value, .. }) = arena.computation(tail)
        else {
            panic!(
                "`{name}` lowers to a transport: {:?}",
                arena.computation(tail)
            );
        };
        let Some(&Value::Here(start)) = arena.value(value)
        else {
            panic!("`{name}` transports the reflexivity at its start");
        };
        let Some(&Value::Returned(run)) = arena.value(start)
        else {
            return None;
        };
        arena.computation(run).cloned()
    };
    assert!(
        matches!(
            start("onCell"),
            Some(Computation::PathTransport { path, .. })
                if matches!(arena.value(path), Some(&Value::Here(_)))
        ),
        "on the 2-cell the start is `Path.ap` of the map along the reflexivity"
    );
    assert!(
        !matches!(start("onLoop"), Some(Computation::PathTransport { .. })),
        "on the loop no transport stands below the start"
    );
}

/// #6811: `Path.ap` of a bound map on a 2-cell read no domain off the map, so
/// it took no levels and spelled a tower one level short of the cell. A
/// binder whose written type states a map, as a value function or as a thunk
/// of an arrow, now gives that map's domain, and the start is `Path.ap` of the
/// map along the reflexivity, as for a named map.
#[test]
fn cong_at_a_bound_map_takes_its_levels_6811()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/cong-at-a-bound-map-takes-its-levels-6811-module.gandr"
        )),
        &mut arena,
    );
    for name in ["onBoundCell", "onThunkedCell"] {
        let tail = tail_of(&module, &arena, name.into());
        let Some(&Computation::PathTransport { value, .. }) = arena.computation(tail)
        else {
            panic!(
                "`{name}` lowers to a transport: {:?}",
                arena.computation(tail)
            );
        };
        let Some(&Value::Here(start)) = arena.value(value)
        else {
            panic!("`{name}` transports the reflexivity at its start");
        };
        let run = match arena.value(start) {
            Some(&Value::Returned(run)) => arena.computation(run),
            _ => None,
        };
        assert!(
            matches!(
                run,
                Some(&Computation::PathTransport { path, .. })
                    if matches!(arena.value(path), Some(&Value::Here(_)))
            ),
            "at `{name}` the start is `Path.ap` of the bound map along the reflexivity: {run:?}"
        );
    }
}

/// #6492: `Path.ap f (Path.here c)` in a type, `c` a point of a family with
/// no parameters, was refused `Unannotated`: the reflexivity read no type off
/// a constructor, and a reflexivity of a reflexivity read none either. The
/// printer writes the images of the spheres' cells so, so a printed type did
/// not read back. Each reflexivity stands at the paths from its point to
/// itself, the innermost at the point's family, so both declarations lower.
#[test]
fn an_action_on_a_constructor_s_reflexivity_reads_its_family_6492()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/an-action-on-a-constructor-s-reflexivity-reads-its-family-6492-module.gandr"
        )),
        &mut arena,
    );
    for name in ["apHere", "apHereTwice"] {
        assert!(
            matches!(
                outcome_of(&module, name.into()),
                DeclarationOutcome::Completed { .. }
            ),
            "`{name}` lowers its type and its body: {:?}",
            outcome_of(&module, name.into())
        );
    }
}

#[test]
fn a_motive_telescope_rebuilds_exactly_when_an_entry_is_an_arrow()
{
    let mut arena = CoreArena::new();
    let unit = arena.value_type_unit();
    let body = arena.comp_type_returner(unit);
    let rebuilt = |arena: &mut CoreArena, outer_arrow: bool, inner_arrow: bool| {
        let inner = if inner_arrow {
            arena.comp_type_arrow(unit, body)
        }
        else {
            arena.comp_type_pi(unit, body)
        };
        let written = if outer_arrow {
            arena.comp_type_arrow(unit, inner)
        }
        else {
            arena.comp_type_pi(unit, inner)
        };
        let mut copies = Vec::new();
        let read = super::telescope(arena, written, &mut copies);
        let dependent = matches!(
            arena.comp_type(read),
            Some(&gandr_core_term::CompType::Pi { codomain, .. })
                if matches!(arena.comp_type(codomain), Some(&gandr_core_term::CompType::Pi { .. }))
        );
        (read != written, dependent)
    };
    assert_eq!(
        rebuilt(&mut arena, false, false),
        (false, true),
        "a telescope dependent in both entries is read as written"
    );
    for (outer_arrow, inner_arrow) in [(false, true), (true, false), (true, true)] {
        assert_eq!(
            rebuilt(&mut arena, outer_arrow, inner_arrow),
            (true, true),
            "an arrow in either entry is rebuilt as a dependent telescope: outer {outer_arrow}, \
             inner {inner_arrow}"
        );
    }
}

#[test]
fn a_dependent_transport_lowers_to_its_telescope()
{
    let mut arena = CoreArena::new();
    let source =
        include_str!("tests/unformatted/a-dependent-transport-lowers-to-its-telescope.gandr");
    let module = lowered(SourceText::from(source), &mut arena);
    let telescope = |name: &str| {
        let Some(&Computation::TelescopeTransport {
            motive,
            path,
            start,
            over,
            value,
        }) = arena.computation(tail_of(&module, &arena, name.into()))
        else {
            panic!("`{name}` lowers to a telescope transport");
        };
        let Some(&gandr_core_term::CompType::Pi {
            domain: outer,
            codomain,
        }) = arena.comp_type(motive)
        else {
            panic!("`{name}`'s motive binds the endpoint");
        };
        let Some(&gandr_core_term::CompType::Pi {
            domain: inner,
            codomain,
        }) = arena.comp_type(codomain)
        else {
            panic!("`{name}`'s motive binds the element");
        };
        let Some(&gandr_core_term::CompType::Returner { result, .. }) = arena.comp_type(codomain)
        else {
            panic!("`{name}`'s motive returns its body");
        };
        (outer, inner, result, [path, start, over, value])
    };

    let (_, inner, body, operands) = telescope("moved");
    assert_eq!(
        operands.map(|operand| arena.value(operand).cloned()),
        [3_u32, 2, 1, 0].map(|index| Some(variable(index.into()))),
        "the path, the start, the identity over the path and the value, in order"
    );
    assert!(
        matches!(arena.value_type(inner), Some(&ValueType::Path { right, .. }) if arena.value(right) == Some(&variable(0_u32.into()))),
        "the family names the endpoint its entry binds"
    );
    assert!(
        matches!(
            arena.value_type(body),
            Some(&ValueType::Path { left, right, .. })
                if arena.value(left) == Some(&variable(0_u32.into()))
                    && arena.value(right) == Some(&variable(0_u32.into()))
        ),
        "the body names the element its second entry binds"
    );
    let (_, _, body, _) = telescope("plain");
    let Some(&ValueType::Path { left, .. }) = arena.value_type(body)
    else {
        panic!("`plain`'s motive returns a path");
    };
    assert_eq!(
        arena.value(left),
        Some(&variable(4_u32.into())),
        "an arrow entry becomes dependent, its codomain moved under the binder it now stands \
         under"
    );
    let written = source
        .find("Path[.A = Integer](n, n)")
        .map(|at| at.saturating_add("Path[.A = Integer](".len()));
    assert_eq!(
        match module.origins().value(left) {
            Maybe::Present(origin) =>
                Some((usize::from(origin.span().start()), origin.provenance())),
            Maybe::Absent(_) => None,
        },
        written.map(|at| (at, Provenance::Written)),
        "the moved endpoint answers where it is written"
    );

    assert!(
        matches!(
            outcome_of(&module, "short".into()),
            DeclarationOutcome::Refused(LoweringRefusal::OutOfFragment {
                boundary: FragmentBoundary::Arity(count),
                ..
            }) if count == OperandCount::from(4_usize)
        ),
        "`transport` takes a motive and two values, or a telescope motive and four"
    );
}

#[test]
fn matching_reflexivity_is_refused_as_k()
{
    let source = include_str!("tests/fixtures/matching-reflexivity-is-refused-as-k.gandr");
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source), &mut arena);
    let start = source.find("here =>").unwrap_or_default();
    assert_eq!(
        outcome_of(&module, "uip".into()),
        DeclarationOutcome::Refused(LoweringRefusal::WithoutK {
            span: span(
                ByteOffset::from(start),
                ByteOffset::from(start.saturating_add(4_usize))
            ),
        }),
        "a path is never matched against `here`"
    );
}

/// Two protocols, one widening the other's selection, and a copy of the
/// first, as module type members a statement names bare.
const PROTOCOLS: &str = include_str!("tests/unformatted/protocols.gandr");

#[test]
fn session_statements_lower_to_their_formers()
{
    let mut arena = CoreArena::new();
    let source = format!(
        include_str!("tests/unformatted/session-statements-lower-to-their-formers-1.gandr"),
        PROTOCOLS = PROTOCOLS
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let quoted = |at| matches!(arena.value(at), Some(&Value::Quote(code)) if matches!(arena.value_type(code), Some(&ValueType::Session(_))));
    let DeclarationOutcome::Completed {
        declared_type,
        body,
    } = outcome_of(&module, "sub".into())
    else {
        panic!("the flow and its statement lower");
    };
    assert!(
        matches!(
            arena.value_type(declared_type),
            Some(&ValueType::Flow { source, target, .. }) if quoted(source) && quoted(target)
        ),
        "`Flow[.A = Type](Old, New)` is the directed identity type over two quoted protocols"
    );
    assert!(
        matches!(
            arena.value(body),
            Some(&Value::SessionRelated { relation: SessionRelation::Subtyping, source, target, .. })
                if quoted(source) && quoted(target) && source != target
        ),
        "`sim` reads both protocols as values, in order"
    );
    let DeclarationOutcome::Completed { body, .. } = outcome_of(&module, "eq".into())
    else {
        panic!("the path and its statement lower");
    };
    assert!(
        matches!(
            arena.value(body),
            Some(&Value::SessionRelated {
                relation: SessionRelation::Equivalence,
                ..
            })
        ),
        "`bisim` states the equivalence"
    );
    let DeclarationOutcome::Completed { body, .. } = outcome_of(&module, "kept".into())
    else {
        panic!("the stay lowers");
    };
    assert!(
        matches!(arena.value(body), Some(&Value::Stay(point)) if quoted(point)),
        "`stay` is the identity flow at its point"
    );
    let Some(&Computation::Return(composite)) =
        arena.computation(tail_of(&module, &arena, "widened".into()))
    else {
        panic!("`then` at a flow answer returns the composite");
    };
    assert!(
        matches!(
            arena.value(composite),
            Some(&Value::Then(first, second))
                if matches!(arena.value(first), Some(&Value::Constant(_)))
                    && matches!(arena.value(second), Some(&Value::Constant(_)))
                    && first != second
        ),
        "the composite reads both flows in order"
    );
    assert!(
        matches!(
            module.origins().value(composite),
            Maybe::Present(origin) if origin.provenance() == Provenance::Inserted(Insertion::Identity)
        ),
        "the composite is the lowering's insertion"
    );
    assert_accepted(&judged(&module, &mut arena));

    let mut arena = CoreArena::new();
    let source = format!(
        include_str!("tests/unformatted/session-statements-lower-to-their-formers-2.gandr"),
        PROTOCOLS = PROTOCOLS
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let Some(&Computation::Ride {
        motive,
        flow,
        value,
    }) = arena.computation(tail_of(&module, &arena, "flip".into()))
    else {
        panic!("`back` at a flow answer lowers to the symmetry ride");
    };
    assert!(
        matches!(
            arena.value_type(motive),
            Some(&ValueType::Flow { source, .. }) if arena.value(source) == Some(&variable(0_u32.into()))
        ) && matches!(arena.value(flow), Some(&Value::Constant(_)))
            && matches!(arena.value(value), Some(&Value::Stay(_))),
        "the motive moves the source; the flow and the stay follow"
    );
    let report = judged(&module, &mut arena);
    assert!(
        report.judged().iter().any(|judged| matches!(
            judged.verdict(),
            Verdict::Refused(CheckRefusal::NonCovariantMotive { .. })
        )),
        "the checker refuses the symmetry by its motive: {report:?}"
    );
    assert!(
        matches!(
            outcome_of(&module, "half".into()),
            DeclarationOutcome::Refused(LoweringRefusal::OutOfFragment {
                boundary: FragmentBoundary::Arity(count),
                ..
            }) if count == OperandCount::from(1_usize)
        ),
        "a statement relates two protocols"
    );
}

#[test]
fn a_run_rides_a_flow_between_sessions()
{
    let mut arena = CoreArena::new();
    let source = format!(
        include_str!("tests/unformatted/a-run-rides-a-flow-between-sessions.gandr"),
        PROTOCOLS = PROTOCOLS
    );
    let source = crate::fixture::session_listing(source);
    let module = crate::fixture::listed(&source, &mut arena);
    let DeclarationOutcome::Completed {
        declared_type,
        body,
    } = outcome_of(&module, "served".into())
    else {
        panic!("the run and its literal lower");
    };
    assert!(
        matches!(
            arena.value_type(declared_type),
            Some(&ValueType::Run(code)) if matches!(arena.value(code), Some(&Value::Quote(_)))
        ),
        "`Run(S)` reads its protocol as a value"
    );
    let Some(found) = arena.value(body)
    else {
        panic!("the literal lowers");
    };
    let Value::Recorded(ref moves) = *found
    else {
        panic!("`recorded` is the run literal");
    };
    assert!(
        matches!(
            **moves,
            [
                RecordedMove::Selected(ref chosen),
                RecordedMove::Sent(payload),
                RecordedMove::Closed,
            ] if chosen.as_ref() == "report" && matches!(arena.value(payload), Some(&Value::Literal(_)))
        ),
        "each move keeps its label or its payload, in order: {moves:?}"
    );
    let Some(&Computation::Ride {
        motive,
        flow,
        value,
    }) = arena.computation(tail_of(&module, &arena, "forward".into()))
    else {
        panic!("`ride` lowers to the ride");
    };
    assert!(
        matches!(
            arena.value_type(motive),
            Some(&ValueType::Run(code)) if arena.value(code) == Some(&variable(0_u32.into()))
        ) && matches!(arena.value(flow), Some(&Value::Constant(_)))
            && arena.value(value) == Some(&variable(0_u32.into())),
        "the motive is the abstraction's body; the flow and the run follow in order"
    );
    assert_accepted(&judged(&module, &mut arena));
}

#[test]
fn directed_statements_lower_to_their_formers()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/directed-statements-lower-to-their-formers-module.gandr"
        )),
        &mut arena,
    );
    let DeclarationOutcome::Completed { body, .. } = outcome_of(&module, "upgrade".into())
    else {
        panic!("the forward flow lowers");
    };
    assert!(
        matches!(arena.value(body), Some(&Value::Forward(translator)) if matches!(arena.value(translator), Some(&Value::Constant(_)))),
        "`forward` reads its translator as a value"
    );
    let DeclarationOutcome::Completed { body, .. } = outcome_of(&module, "reader".into())
    else {
        panic!("the function flow lowers");
    };
    let Some(&Value::FunctionFlow(domain, codomain)) = arena.value(body)
    else {
        panic!("`arrow` is the function flow");
    };
    let named = |at, name: &str| {
        matches!(
            arena.value(at),
            Some(&Value::Constant(constant)) if module.declarations().iter().any(|declaration| {
                declaration.name() == SurfaceName::from(name) && declaration.constant() == constant
            })
        )
    };
    assert!(
        named(domain, "upgrade") && named(codomain, "kept"),
        "the domain flow is written first, the codomain flow second"
    );
    assert!(
        matches!(
            outcome_of(&module, "both".into()),
            DeclarationOutcome::Refused(LoweringRefusal::OutOfFragment {
                boundary: FragmentBoundary::Arity(count),
                ..
            }) if count == OperandCount::from(2_usize)
        ),
        "a forward flow has one translator"
    );
    assert_accepted(&judged(&module, &mut arena));
}

#[test]
fn a_move_out_of_shape_is_refused()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/a-move-out-of-shape-is-refused-module.gandr"
        )),
        &mut arena,
    );
    let boundary = |name: &str| match outcome_of(&module, name.into()) {
        DeclarationOutcome::Refused(LoweringRefusal::OutOfFragment { boundary, .. }) => {
            Some(boundary)
        },
        DeclarationOutcome::Completed { .. }
        | DeclarationOutcome::Uncompleted { .. }
        | DeclarationOutcome::Bodied { .. }
        | DeclarationOutcome::Data(_)
        | DeclarationOutcome::Codata(_)
        | DeclarationOutcome::Abstract(_)
        | DeclarationOutcome::World
        | DeclarationOutcome::Refused(_) => None,
    };
    assert_eq!(
        ["skipped", "bare", "twice", "called", "named"].map(boundary),
        [
            Some(FragmentBoundary::Unadmitted(crate::Unbuilt::RecordedMove)),
            Some(FragmentBoundary::Unadmitted(crate::Unbuilt::RecordedMove)),
            Some(FragmentBoundary::Arity(OperandCount::from(2_usize))),
            Some(FragmentBoundary::Unadmitted(crate::Unbuilt::RecordedMove)),
            Some(FragmentBoundary::Unannotated),
        ],
        "an unknown move, a bare send, a send of two, a label that is a call and a named motive"
    );
    let source = "def twice = recorded (sent 1 2);\n";
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source), &mut arena);
    let start = source.find("sent 1 2").expect("the move is written");
    assert!(
        matches!(
            outcome_of(&module, "twice".into()),
            DeclarationOutcome::Refused(LoweringRefusal::OutOfFragment { span, .. })
                if usize::from(span.start()) == start
                    && usize::from(span.end()) == start.saturating_add("sent 1 2".len())
        ),
        "a send of two is refused at the move, not the record around it: {:?}",
        outcome_of(&module, "twice".into())
    );
}

#[test]
fn a_dialogue_lowers_its_moves_beside_their_endpoints()
{
    let mut arena = CoreArena::new();
    let source = crate::fixture::session_listing(include_str!(
        "tests/fixtures/a-dialogue-lowers-its-moves-beside-their-endpoints.gandr"
    ));
    let module = crate::fixture::listed(&source, &mut arena);
    let DeclarationOutcome::Completed {
        declared_type,
        body,
    } = outcome_of(&module, "played".into())
    else {
        panic!("the dialogue type and its literal lower");
    };
    assert!(
        matches!(
            arena.value_type(declared_type),
            Some(&ValueType::Dialogue(code)) if matches!(arena.value(code), Some(&Value::Quote(_)))
        ),
        "`Dialogue(S)` reads its protocol as a value"
    );
    let Some(&Value::Dialogue(ref moves)) = arena.value(body)
    else {
        panic!("`dialogue` is the dialogue literal");
    };
    let literal = |payload| matches!(arena.value(payload), Some(&Value::Literal(_)));
    assert!(
        matches!(
            **moves,
            [
                DialogueMove { endpoint: Endpoint::Left, movement: RecordedMove::Sent(sent) },
                DialogueMove { endpoint: Endpoint::Right, movement: RecordedMove::Received(heard) },
                DialogueMove { endpoint: Endpoint::Right, movement: RecordedMove::Closed },
                DialogueMove { endpoint: Endpoint::Left, movement: RecordedMove::Closed },
            ] if literal(sent) && literal(heard)
        ),
        "each move keeps its endpoint and its payload, in log order: {moves:?}"
    );
    assert!(
        matches!(
            arena.computation(tail_of(&module, &arena, "web".into())),
            Some(&Computation::Decompose(dialogue)) if matches!(arena.value(dialogue), Some(&Value::Constant(_)))
        ),
        "`decompose` reads its dialogue as a value"
    );
    assert_accepted(&judged(&module, &mut arena));

    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/a-dialogue-lowers-its-moves-beside-their-endpoints-module.gandr"
        )),
        &mut arena,
    );
    let boundary = |name: &str| match outcome_of(&module, name.into()) {
        DeclarationOutcome::Refused(LoweringRefusal::OutOfFragment { boundary, .. }) => {
            Some(boundary)
        },
        DeclarationOutcome::Completed { .. }
        | DeclarationOutcome::Uncompleted { .. }
        | DeclarationOutcome::Bodied { .. }
        | DeclarationOutcome::Data(_)
        | DeclarationOutcome::Codata(_)
        | DeclarationOutcome::Abstract(_)
        | DeclarationOutcome::World
        | DeclarationOutcome::Refused(_) => None,
    };
    assert_eq!(
        ["untagged", "elsewhere", "twice", "inner", "both"].map(boundary),
        [
            Some(FragmentBoundary::Unadmitted(crate::Unbuilt::DialogueMove)),
            Some(FragmentBoundary::Unadmitted(crate::Unbuilt::DialogueMove)),
            Some(FragmentBoundary::Arity(OperandCount::from(2_usize))),
            Some(FragmentBoundary::Unadmitted(crate::Unbuilt::RecordedMove)),
            Some(FragmentBoundary::Arity(OperandCount::from(2_usize))),
        ],
        "an untagged move, an unknown endpoint, an endpoint of two moves, an unknown move and a decomposition of two"
    );
}

/// Each relation between types lowers to the type it abbreviates, in its
/// glyph and its ASCII alias alike: the quasi-inverse and the bi-invertible
/// map to the records written out, the flow to the flow at the universe. The
/// written relation records which one it is, for the printer; the same type
/// written out records nothing. The type is located at the relation as
/// written, and what the lowering minted below it as the relation's
/// insertion: the source wrote neither the record's fields nor the universe.
#[test]
fn a_relation_lowers_to_the_type_it_abbreviates()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/a-relation-lowers-to-the-type-it-abbreviates-module.gandr"
        )),
        &mut arena,
    );
    let declared = |name: &str| match outcome_of(&module, name.into()) {
        DeclarationOutcome::Uncompleted { declared_type } => declared_type,
        other @ (DeclarationOutcome::Completed { .. }
        | DeclarationOutcome::Bodied { .. }
        | DeclarationOutcome::Data(_)
        | DeclarationOutcome::Codata(_)
        | DeclarationOutcome::Abstract(_)
        | DeclarationOutcome::World
        | DeclarationOutcome::Refused(_)) => panic!("`{name}` is a signature: {other:?}"),
    };
    for (relation, former) in [
        (Relation::Isomorphism, "iso"),
        (Relation::Equivalence, "equiv"),
        (Relation::Flow, "flow"),
    ] {
        let written = declared(&format!("{former}Record"));
        for spelling in ["Glyph", "Alias"] {
            let id = declared(&format!("{former}{spelling}"));
            assert_eq!(
                equal_type_syntax(&arena, id, written),
                CertificateEquality::Equal,
                "`{former}{spelling}` lowers to the type it abbreviates"
            );
            assert!(
                module.origins().relations().contains(&(id, relation)),
                "`{former}{spelling}` records its relation"
            );
            let below = match arena.value_type(id) {
                Some(
                    &(ValueType::Sigma { first, .. } | ValueType::Flow { carrier: first, .. }),
                ) => first,
                other => panic!("`{former}{spelling}` is a record or a flow: {other:?}"),
            };
            assert_eq!(
                [id, below].map(|node| match module.origins().value_type(node) {
                    Maybe::Present(origin) => Some(origin.provenance()),
                    Maybe::Absent(_) => None,
                }),
                [
                    Some(Provenance::Written),
                    Some(Provenance::Inserted(Insertion::Relation))
                ],
                "`{former}{spelling}` is written, and what it abbreviates inserted"
            );
        }
        assert!(
            module
                .origins()
                .relations()
                .iter()
                .all(|&(id, _)| id != written),
            "`{former}Record` is written out and records nothing"
        );
    }
    let report = judged(&module, &mut arena);
    assert!(
        report
            .judged()
            .iter()
            .all(|judged| matches!(judged.verdict(), Verdict::Owed(_))),
        "every relation forms a type the signature owes: {report:?}"
    );
}

/// A pattern at a relation splits the record the relation abbreviates:
/// positionally, nested as the equivalence's inverses nest, and by label,
/// each part bound at its own type. A label read at the wrong inverse binds
/// that inverse, and the checker refuses the type it answers.
#[test]
fn a_pattern_at_a_relation_splits_its_record()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/a-pattern-at-a-relation-splits-its-record-module.gandr"
        )),
        &mut arena,
    );
    assert_accepted(&judged(&module, &mut arena));

    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(
            "def misread(e : Bool ≃ Integer) -> -F +U (Bool -> -F Integer) { match e { | *{.rinv = *{.from = h}} => return h } }\n",
        ),
        &mut arena,
    );
    let report = judged(&module, &mut arena);
    assert!(
        matches!(
            report.judged(),
            [judged] if matches!(judged.verdict(), Verdict::Refused(_))
        ),
        "the right inverse runs from `Integer` to `Bool`: {report:?}"
    );
}

/// Each component a pattern at a relation writes a variable for is named by
/// it, though the arm uses only one: the record's later fields mention the
/// earlier ones, so a type read inside the arm names them (#665). The rest of
/// the record each link holds is named by the label it starts at (#1515).
#[test]
fn a_relation_split_names_each_written_component_665()
{
    let source = SourceText::from(
        "def backOf(a : Type, b : Type, i : a ≅ b) -> -F +U (b -> -F a) { match i { | *{t, k, s, r} => k } }\n",
    );
    assert_eq!(
        component_names(source),
        ["from", "k", "r", "s", "sect", "t"],
        "every written component is named, the unused `t`, `s` and `r` with `k`, and each rest by \
         its first label"
    );
}

/// A pattern at a `let` binder splits the record the relation its callee
/// returns abbreviates, as one at a parameter does: the callee's signature is
/// minted before the caller's body is read, so its layout comes from the
/// written glyph. Positionally, nested as the equivalence's inverses nest,
/// and by label (#656).
#[test]
fn a_let_binder_splits_the_relation_its_call_returns_656()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/a-let-binder-splits-the-relation-its-call-returns-656-module.gandr"
        )),
        &mut arena,
    );
    assert_accepted(&judged(&module, &mut arena));
}

/// A callee whose result is written bare, `-> A`, returns `A` as one written
/// `-> -F A` does: the lowering inserts the returner, so a pattern at a `let`
/// binder of its call splits the record `A` abbreviates (#2255).
#[test]
fn a_let_binder_splits_the_relation_a_bare_result_returns_2255()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/a-let-binder-splits-the-relation-a-bare-result-returns-2255-module.gandr"
        )),
        &mut arena,
    );
    assert_accepted(&judged(&module, &mut arena));
}

/// A label pattern writes no variable for the fields it omits; each is named
/// by its label, the one name the record declares for it (#670), as is the
/// rest of the record each link holds, by the label it starts at (#1515).
#[test]
fn an_unwritten_field_is_named_by_its_label_670()
{
    let source = SourceText::from(
        "def backOf(a : Type, b : Type, i : a ≅ b) -> -F +U (b -> -F a) { match i { | *{.from = k} => k } }\n",
    );
    assert_eq!(
        component_names(source),
        ["from", "into", "k", "retr", "sect", "sect"],
        "the written `k` by its variable, the omitted fields and the rests by their labels"
    );
}

/// The names `source`'s splits record for their components, sorted: a
/// written one as the source spells it, a labelled one as its label.
///
/// # Specification
/// trivial.
fn component_names(source: SourceText<'_>) -> Vec<String>
{
    let text = <&str>::from(source);
    let mut arena = CoreArena::new();
    let module = lowered(source, &mut arena);
    let mut named: Vec<String> = module
        .origins()
        .components()
        .iter()
        .filter_map(|&(_, ref name)| match *name {
            ComponentName::Written(origin) => text
                .get(usize::from(origin.span().start()) .. usize::from(origin.span().end()))
                .map(String::from),
            ComponentName::Labelled(ref label) => Some(String::from(label.as_ref())),
        })
        .collect();
    named.sort_unstable();
    named
}

/// A call nested in a call's argument reads, as an endpoint, as the value
/// each call returns, at every level of the spine; a value with no nested
/// computation along its spine is itself.
#[test]
fn an_endpoint_reads_each_nested_call_along_its_spine_as_returned()
{
    use gandr_kernel_term::ConstantIndex;

    let mut arena = CoreArena::new();
    let variable = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let call = |arena: &mut CoreArena, head: usize, argument| {
        let constant = arena.value_constant(ConstantIndex::from(head));
        let forced = arena.computation_force(constant);
        arena.computation_application(forced, argument)
    };
    let inner = call(&mut arena, 1_usize, variable);
    let nested_inner = arena.value_nested(inner);
    let outer = call(&mut arena, 0_usize, nested_inner);
    let written = arena.value_nested(outer);

    let read = super::as_endpoint(&mut arena, written);
    let Some(&Value::Returned(spine)) = arena.value(read)
    else {
        panic!("the outer call reads as returned: {:?}", arena.value(read));
    };
    let Some(&Computation::Application(_, argument)) = arena.computation(spine)
    else {
        panic!("the spine stays an application");
    };
    let Some(&Value::Returned(argued)) = arena.value(argument)
    else {
        panic!(
            "the nested argument reads as returned: {:?}",
            arena.value(argument)
        );
    };
    assert_eq!(
        arena.computation(argued),
        arena.computation(inner),
        "the inner call itself is unchanged"
    );
    assert_eq!(
        super::as_endpoint(&mut arena, variable),
        variable,
        "a value with nothing nested is its own endpoint"
    );
    let returned = arena.value_returned(inner);
    assert_eq!(
        super::as_endpoint(&mut arena, returned),
        returned,
        "a returned call with nothing nested under it is kept as written"
    );
}

/// #3921: a lambda passed at a parameter of function type gave its binder no
/// path type the lowering read, so `then` and `back` in its body were refused
/// unannotated. A callee's capitalised parameters went unread, and a type
/// naming the parameters before it answered the lambda's body under the
/// callee's binders. The binder takes the parameter's domain, each parameter
/// it names replaced by the argument the call writes, so every declaration
/// lowers and checks, the binder written untyped, stated, or at a callee
/// whose parameters are lowercase.
#[test]
fn a_call_s_lambda_argument_reads_its_parameter_s_domain_3921()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/a-call-s-lambda-argument-reads-its-parameter-s-domain-3921-module.gandr"
        )),
        &mut arena,
    );
    for name in ["dependentThen", "statedThen", "reversed"] {
        assert!(
            !matches!(
                outcome_of(&module, name.into()),
                DeclarationOutcome::Refused(_)
            ),
            "`{name}` lowers: {:?}",
            outcome_of(&module, name.into())
        );
    }
    assert_accepted(&judged(&module, &mut arena));
}

/// #4005: two `ap` calls whose arguments reduce to one term were refused when
/// the source wrote them apart. Beneath an outer action, a call of
/// `whiskerRight` and the `ap` it unfolds to are one path argument, and so are
/// the outer action on the inner one and the nested `ap` written out. Each
/// outer action's motive holds the inner path as the endpoint a transport
/// along `fa` returns, once per writing.
#[test]
fn two_ap_calls_whose_arguments_reduce_alike_convert_4005()
{
    let telescope = "(A : Type, x : A, y : A, z : A, w : A, fm : Path[.A = A](x, y), fp : Path[.A = A](x, y), \
                     fa : Path[.A = Path[.A = A](x, y)](fm, fp), g : Path[.A = A](y, z), h : Path[.A = A](z, w))";
    let pre = "(fun (q : Path[.A = A](x, y)) { Path.step q g } : Path[.A = A](x, y) -> Path[.A = A](x, z))";
    let post = "(fun (r : Path[.A = A](x, z)) { Path.step r h } : Path[.A = A](x, z) -> Path[.A = A](x, w))";
    let square =
        "Path[.A = Path[.A = A](x, w)](Path.step (Path.step fm g) h, Path.step (Path.step fp g) h)";
    let inner_ap =
        format!("ap (type(Path[.A = A](x, y))) (type(Path[.A = A](x, z))) {pre} fm fp fa");
    let inner_whisker = "whiskerRight A x y z fm fp fa g";
    let outer_ap = |inner: &str| {
        format!(
            "ap (type(Path[.A = A](x, z))) (type(Path[.A = A](x, w))) {post} (Path.step fm g) (Path.step fp g) ({inner})"
        )
    };
    let outer_whisker =
        |inner: &str| format!("whiskerRight A x z w (Path.step fm g) (Path.step fp g) ({inner}) h");
    let at_lambdas = format!(
        " (type(Path[.A = A](x, y))) (type(Path[.A = A](x, z))) (type(Path[.A = A](x, w))) {pre} {post} fm fp fa"
    );
    let source = format!(
        include_str!(
            "tests/unformatted/two-ap-calls-whose-arguments-reduce-alike-convert-4005.gandr"
        ),
        under_ap_left = outer_ap(&inner_ap),
        under_ap_right = outer_ap(inner_whisker),
        under_whisker_left = outer_whisker(&inner_ap),
        under_whisker_right = outer_whisker(inner_whisker),
        at_lambdas = at_lambdas,
        pre = pre,
        square = square,
        telescope = telescope,
    );
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    for name in ["underAp", "underWhisker", "nestedAtLambdas"] {
        assert!(
            !matches!(
                outcome_of(&module, name.into()),
                DeclarationOutcome::Refused(_)
            ),
            "`{name}` lowers: {:?}",
            outcome_of(&module, name.into())
        );
    }
    assert_accepted(&judged(&module, &mut arena));
}

/// #4038: a composite typed by `join` was refused against `then` over the same
/// paths where the endpoints are stuck. `join`'s body is `Path.step(p, q)`, so
/// its call converts with the native composite at variable endpoints, at a
/// stuck composite and at an application of a variable function.
#[test]
fn a_composite_typed_by_join_over_stuck_endpoints_converts_with_then_4038()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/a-composite-typed-by-join-over-stuck-endpoints-converts-with-then-4038-module.gandr"
        )),
        &mut arena,
    );
    for name in ["atVariables", "atComposite", "atApplication"] {
        assert!(
            !matches!(
                outcome_of(&module, name.into()),
                DeclarationOutcome::Refused(_)
            ),
            "`{name}` lowers: {:?}",
            outcome_of(&module, name.into())
        );
    }
    assert_accepted(&judged(&module, &mut arena));
}

/// #4065: a stuck call passed to a parameter whose type writes `Path.step(p, q)` was
/// refused against the same call written in place. A variable passed there
/// converts, and so do one stuck call and two.
#[test]
fn a_stuck_call_passed_to_a_parameter_converts_with_the_call_written_in_its_type_4065()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/a-stuck-call-passed-to-a-parameter-converts-with-the-call-written-in-its-type-4065-module.gandr"
        )),
        &mut arena,
    );
    for name in ["junction", "junctionVariables", "junctionOneCall"] {
        assert!(
            !matches!(
                outcome_of(&module, name.into()),
                DeclarationOutcome::Refused(_)
            ),
            "`{name}` lowers: {:?}",
            outcome_of(&module, name.into())
        );
    }
    assert_accepted(&judged(&module, &mut arena));
}

/// #4073: a composite whose first path is typed at a stated lambda starts at
/// the lambda applied, which the code walk compared head to head with the
/// reduct passed through a parameter. The composite written in the body
/// converts, and so does the one passed with its start as the reduct or as the
/// application written again. So does a lambda whose body composes, its reduct
/// a composite written apart.
#[test]
fn a_stated_lambda_applied_in_a_motive_converts_with_its_reduct_4073()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/a-stated-lambda-applied-in-a-motive-converts-with-its-reduct-4073-module.gandr"
        )),
        &mut arena,
    );
    for name in [
        "composedAtLambda",
        "passedAtLambda",
        "passedRedex",
        "passedComposite",
    ] {
        assert!(
            !matches!(
                outcome_of(&module, name.into()),
                DeclarationOutcome::Refused(_)
            ),
            "`{name}` lowers: {:?}",
            outcome_of(&module, name.into())
        );
    }
    assert_accepted(&judged(&module, &mut arena));
}

/// #4179: two transports along one stuck path, at one operand, were refused
/// when their motives' fixed starts differ by a reduction. `then` after a
/// 2-path stated from a right unit converts with `then` after the 2-path, and
/// written transports whose starts differ by an unfolding, by transport along
/// a reflexivity and by a composite's right unit law convert.
#[test]
fn transports_whose_motive_starts_differ_by_a_reduction_convert_4179()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/transports-whose-motive-starts-differ-by-a-reduction-convert-4179-module.gandr"
        )),
        &mut arena,
    );
    for name in ["thenStart", "unfoldStart", "hereStart", "unitStart"] {
        assert!(
            !matches!(
                outcome_of(&module, name.into()),
                DeclarationOutcome::Refused(_)
            ),
            "`{name}` lowers: {:?}",
            outcome_of(&module, name.into())
        );
    }
    assert_accepted(&judged(&module, &mut arena));
}

/// The numbers `compose[n, k] (chain m) d` writes: `n`, `k` and `m`.
#[derive(Clone, Copy, Debug)]
struct Written(usize, usize, usize);

/// The composite `compose[n, k] (chain m) d` at the stratum and chain its
/// head and shape write.
///
/// # Specification
/// trivial.
fn chain_at(Written(degree, bound, cells): Written) -> Composite
{
    Composite {
        stratum: Stratum {
            degree: Degree::from(degree),
            bound: ShapeSize::from(bound),
        },
        pasting: Pasting::chain(CellCount::from(cells)).expect("the chain packs"),
    }
}

#[test]
fn a_composite_lowers_to_its_cells_and_their_fold()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/a-composite-lowers-to-its-cells-and-their-fold-module.gandr"
        )),
        &mut arena,
    );
    let composite = |name: &str| {
        let tail = arena.computation(tail_of(&module, &arena, name.into()));
        let Some(&Computation::Return(returned)) = tail
        else {
            panic!("`{name}` returns its composite: {tail:?}");
        };
        match arena.value(returned) {
            Some(&Value::Compose {
                composite,
                ref cells,
                realised,
            }) => (composite, cells.to_vec(), realised),
            other => panic!("`{name}` returns a composite: {other:?}"),
        }
    };
    let cells_of = |cells: &[gandr_core_term::ValueId]| -> Vec<Option<Value>> {
        cells
            .iter()
            .map(|&cell| arena.value(cell).cloned())
            .collect()
    };

    let (held, cells, realised) = composite("composed");
    assert_eq!(
        held,
        chain_at(Written(5, 7, 3)),
        "the head and the shape it writes"
    );
    assert!(
        cells_of(&cells) == [2_u32, 1_u32, 0_u32].map(|index| Some(variable(index.into()))),
        "the tuple's members are the cells in written order"
    );
    let Some(&Computation::PathTransport { path, value, .. }) = arena.computation(realised)
    else {
        panic!("three cells realise as a transport");
    };
    assert!(
        arena.value(path) == Some(&variable(0_u32.into())),
        "the fold transports along the last cell"
    );
    let Some(&Value::Returned(inner)) = arena.value(value)
    else {
        panic!("the fold transports the composite of the first two cells");
    };
    assert!(
        matches!(
            arena.computation(inner),
            Some(&Computation::PathTransport { path, value, .. })
                if arena.value(path) == Some(&variable(1_u32.into()))
                    && arena.value(value) == Some(&variable(2_u32.into()))
        ),
        "the first two cells compose as `p then q`"
    );

    let (held, cells, realised) = composite("single");
    assert_eq!(held, chain_at(Written(0, 0, 1)), "the chain of one cell");
    assert!(
        cells_of(&cells) == [Some(variable(0_u32.into()))],
        "a parenthesised cell is the one cell"
    );
    assert!(
        matches!(
            arena.computation(realised),
            Some(&Computation::Return(cell)) if arena.value(cell) == Some(&variable(0_u32.into()))
        ),
        "one cell realises as itself returned"
    );

    assert_accepted(&judged(&module, &mut arena));
}

#[test]
fn a_composite_the_syntax_cannot_read_is_refused()
{
    let telescope = "(A : Type, x : A, m : Integer, p : Path[.A = A](x, x))";
    let source = format!(
        include_str!("tests/unformatted/a-composite-the-syntax-cannot-read-is-refused.gandr"),
        telescope = telescope
    );
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let boundary = |name: &str| match outcome_of(&module, name.into()) {
        DeclarationOutcome::Refused(LoweringRefusal::OutOfFragment { boundary, .. }) => {
            Some(boundary)
        },
        DeclarationOutcome::Completed { .. }
        | DeclarationOutcome::Uncompleted { .. }
        | DeclarationOutcome::Bodied { .. }
        | DeclarationOutcome::Data(_)
        | DeclarationOutcome::Codata(_)
        | DeclarationOutcome::Abstract(_)
        | DeclarationOutcome::World
        | DeclarationOutcome::Refused(_) => None,
    };
    assert_eq!(
        ["unary", "cycled", "counted", "named"].map(boundary),
        [
            Some(FragmentBoundary::Arity(OperandCount::from(1_usize))),
            Some(FragmentBoundary::Unadmitted(crate::Unbuilt::ComposePasting)),
            Some(FragmentBoundary::Unadmitted(crate::Unbuilt::ComposePasting)),
            Some(FragmentBoundary::Unadmitted(crate::Unbuilt::UaCount)),
        ],
        "a call of one argument, a shape no chain, a bare count and a count named"
    );
}

#[test]
fn a_level_two_pasting_reads_its_columns()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/unformatted/a-level-two-pasting-reads-its-columns-module.gandr"
        )),
        &mut arena,
    );
    let pasting = |name: &str| {
        let tail = arena.computation(tail_of(&module, &arena, name.into()));
        let Some(&Computation::Return(returned)) = tail
        else {
            panic!("`{name}` returns its composite: {tail:?}");
        };
        match arena.value(returned) {
            Some(&Value::Compose { composite, .. }) => composite.pasting,
            other => panic!("`{name}` returns a composite: {other:?}"),
        }
    };
    let columns = |heights: &[usize]| {
        let heights: Vec<CellCount> = heights.iter().copied().map(CellCount::from).collect();
        Pasting::columns(&heights).expect("the columns pack")
    };
    assert_eq!(
        pasting("whiskered"),
        columns(&[1, 0]),
        "the whisker reads its two columns"
    );
    assert_eq!(
        pasting("stacked"),
        columns(&[2]),
        "one column's height reads through its parentheses"
    );
    assert!(
        matches!(
            outcome_of(&module, "miscounted".into()),
            DeclarationOutcome::Refused(LoweringRefusal::OutOfFragment {
                boundary: FragmentBoundary::Unadmitted(crate::Unbuilt::ComposePasting),
                ..
            })
        ),
        "three heights for two columns are refused"
    );
    let mut kept = CoreArena::new();
    let checked = lowered(
        SourceText::from(include_str!(
            "tests/unformatted/a-level-two-pasting-reads-its-columns-checked.gandr"
        )),
        &mut kept,
    );
    assert_accepted(&judged(&checked, &mut kept));
}

#[test]
fn a_fill_lowers_to_its_generator_and_cells()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/a-fill-lowers-to-its-generator-and-cells-module-1.gandr"
        )),
        &mut arena,
    );
    let tail = arena.computation(tail_of(&module, &arena, "firstLifted".into()));
    let Some(&Computation::Return(returned)) = tail
    else {
        panic!("`firstLifted` returns its fill: {tail:?}");
    };
    let Some(&Value::Fill {
        composite,
        generator,
        ref cells,
    }) = arena.value(returned)
    else {
        panic!("`firstLifted` returns a fill: {:?}", arena.value(returned));
    };
    assert_eq!(
        composite,
        chain_at(Written(5, 7, 2)),
        "the head and the shape it writes"
    );
    assert!(
        cells
            .iter()
            .map(|&cell| arena.value(cell).cloned())
            .eq([1_u32, 0_u32].map(|index| Some(variable(index.into())))),
        "the tuple's members are the cells in written order, the path of paths first"
    );
    assert!(
        matches!(
            arena.computation(generator),
            Some(&Computation::Application(..))
        ),
        "the generator lowers as the computation of its call: {:?}",
        arena.computation(generator)
    );
    assert_accepted(&judged(&module, &mut arena));

    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/a-fill-lowers-to-its-generator-and-cells-module-2.gandr"
        )),
        &mut arena,
    );
    assert!(
        matches!(
            outcome_of(&module, "short".into()),
            DeclarationOutcome::Refused(LoweringRefusal::OutOfFragment {
                boundary: FragmentBoundary::Arity(count),
                ..
            }) if count == OperandCount::from(2_usize)
        ),
        "a fill without its generator is refused by its count"
    );
}

#[test]
fn two_sites_of_one_fill_convert_at_the_same_entries_4180()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/two-sites-of-one-fill-convert-at-the-same-entries-4180-module.gandr"
        )),
        &mut arena,
    );
    assert_accepted(&judged(&module, &mut arena));
}

/// The declared type `name`'s signature lowers to.
///
/// # Specification
/// trivial.
fn declared_of(
    module: &LoweredModule<'_>,
    name: SurfaceName<'_>,
) -> gandr_core_term::ValueTypeId
{
    match outcome_of(module, name) {
        DeclarationOutcome::Completed { declared_type, .. }
        | DeclarationOutcome::Uncompleted { declared_type } => declared_type,
        other @ (DeclarationOutcome::Bodied { .. }
        | DeclarationOutcome::Data(_)
        | DeclarationOutcome::Codata(_)
        | DeclarationOutcome::Abstract(_)
        | DeclarationOutcome::World
        | DeclarationOutcome::Refused(_)) => panic!("{name} lowers its signature: {other:?}"),
    }
}

#[test]
fn a_carrier_supplied_by_name_is_the_type_it_names_4932()
{
    // `Path[.A = C](a, b)` carries `C` under each head, and `Path[.A](a, b)`
    // carries the variable `A` as `Path[.A = A](a, b)` does; a supply naming
    // another implicit is refused at its name.
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/unformatted/a-carrier-supplied-by-name-is-the-type-it-names-4932-module.gandr"
        )),
        &mut arena,
    );
    for name in ["named", "bridged", "flowed"] {
        let carrier = match arena.value_type(declared_of(&module, name.into())) {
            Some(
                &(ValueType::Path { carrier, .. }
                | ValueType::Bridge { carrier, .. }
                | ValueType::Flow { carrier, .. }),
            ) => carrier,
            other => panic!("`{name}` is a path-shaped type: {other:?}"),
        };
        assert_eq!(
            arena.value_type(carrier),
            Some(&ValueType::Base(gandr_kernel_term::BaseType::Integer)),
            "`{name}` carries the type its supply names"
        );
    }
    assert_eq!(
        equal_type_syntax(
            &arena,
            declared_of(&module, "bound".into()),
            declared_of(&module, "punned".into())
        ),
        CertificateEquality::Equal,
        "a carrier supplied from the variable `A` is `A` supplied by name"
    );
    assert!(
        matches!(
            outcome_of(&module, "stray".into()),
            DeclarationOutcome::Refused(LoweringRefusal::UnresolvedName { name, .. })
                if name == SurfaceName::from("B")
        ),
        "`B` names no implicit of `Path`"
    );
}

#[test]
fn an_omitted_carrier_is_a_nominated_hole_4932()
{
    // `Path(a, b)`, `Bridge(a, b)` and `Flow(a, b)` omit their carrier: the
    // carrier is the decoding of a hole the form nominates, which the
    // endpoints fix where the type forms, and which nothing fixes between two
    // lambdas.
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/unformatted/an-omitted-carrier-is-a-nominated-hole-4932-module.gandr"
        )),
        &mut arena,
    );
    let bridged = lowered(SourceText::from("def bridge : Bridge(4, 4);\n"), &mut arena);
    for (module, name) in [
        (&module, "path"),
        (&module, "directed"),
        (&bridged, "bridge"),
    ] {
        let carrier = match arena.value_type(declared_of(module, name.into())) {
            Some(
                &(ValueType::Path { carrier, .. }
                | ValueType::Bridge { carrier, .. }
                | ValueType::Flow { carrier, .. }),
            ) => carrier,
            other => panic!("`{name}` is a path-shaped type: {other:?}"),
        };
        assert!(
            matches!(
                arena.value_type(carrier),
                Some(&ValueType::Element { code, .. }) if matches!(
                    arena.value(code),
                    Some(&Value::Hole(hole)) if hole.origin() == gandr_core_term::hole::HoleOrigin::Nominated
                )
            ),
            "`{name}`'s omitted carrier decodes a nominated hole"
        );
    }
    let report = judged(&module, &mut arena);
    let verdicts: Vec<_> = report
        .judged()
        .iter()
        .map(gandr_core_checker::Judged::verdict)
        .collect();
    assert!(
        matches!(verdicts.as_slice(), [
            Verdict::Checked { .. },
            Verdict::Checked { .. },
            Verdict::Refused(CheckRefusal::ImplicitUnsolved { .. })
        ]),
        "the endpoints fix two carriers and leave the third unsolved: {verdicts:?}"
    );
}

#[test]
fn a_carrier_written_first_is_refused_5024()
{
    // A path-shaped type over three operands writes its carrier first, which
    // its head takes by name: the form is refused at its head, as a type and
    // where a value is read.
    for (source, head) in [
        (
            "def p : Path(Integer, 4, 4);\n",
            crate::form::TileName::PATH,
        ),
        (
            "def p : Bridge(Integer, 4, 4);\n",
            crate::form::TileName::BRIDGE,
        ),
        (
            "def p : Flow(Integer, 4, 4);\n",
            crate::form::TileName::FLOW_TYPE,
        ),
        ("def p = Path Integer 4 4;\n", crate::form::TileName::PATH),
    ] {
        let mut arena = CoreArena::new();
        let module = lowered(SourceText::from(source), &mut arena);
        assert!(
            matches!(
                outcome_of(&module, "p".into()),
                DeclarationOutcome::Refused(LoweringRefusal::MalformedForm {
                    fault: crate::FormFault::PositionalCarrier(refused),
                    span,
                    ..
                }) if refused == head && source.get(usize::from(span.start()) .. usize::from(span.end())) == Some(head.as_ref())
            ),
            "`{source}` is refused at its head: {:?}",
            outcome_of(&module, "p".into())
        );
    }
}

#[test]
fn a_carried_path_head_takes_its_endpoints_by_juxtaposition_6121()
{
    // A path or bridge type that supplies its carrier and leaves its endpoint
    // list out is the head that the juxtaposition applies to its endpoints:
    // `Path[.A = Integer] 4 4` is `Path[.A = Integer](4, 4)`. A spine of one
    // endpoint is refused as a form out of shape.
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/unformatted/a-carried-path-head-takes-its-endpoints-by-juxtaposition-6121-module.gandr"
        )),
        &mut arena,
    );
    for (spaced, listed) in [("spaced", "listed"), ("bridged", "called")] {
        assert_eq!(
            equal_type_syntax(
                &arena,
                declared_of(&module, spaced.into()),
                declared_of(&module, listed.into())
            ),
            CertificateEquality::Equal,
            "`{spaced}` lowers to the type its list form `{listed}` lowers to"
        );
    }
    assert!(
        matches!(
            outcome_of(&module, "short".into()),
            DeclarationOutcome::Refused(LoweringRefusal::MalformedForm { .. })
        ),
        "a carried head over one endpoint is refused: {:?}",
        outcome_of(&module, "short".into())
    );
}
