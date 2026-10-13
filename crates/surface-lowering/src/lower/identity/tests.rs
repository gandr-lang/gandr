use alloc::format;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_checker::CheckBudget;
use gandr_core_checker::CheckingContext;
use gandr_core_checker::Declaration;
use gandr_core_checker::ModuleReport;
use gandr_core_checker::OriginToken;
use gandr_core_checker::Verdict;
use gandr_core_checker::body;
use gandr_core_checker::check_module;
use gandr_core_checker::signature;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueType;
use gandr_core_term::Zone;
use gandr_kernel_term::DeBruijnIndex;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::error::FragmentBoundary;
use crate::error::LoweringRefusal;
use crate::fixture::grammar;
use crate::fixture::parsed;
use crate::fixture::span;
use crate::lower::LoweringBudget;
use crate::lower::lower_module;
use crate::module::DeclarationOutcome;
use crate::module::LoweredModule;
use crate::namespace::Recognition;
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
#[spec(ensures: |ret| !ret.declarations().is_empty())]
fn lowered<'source>(
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
/// - requires: `module` was lowered over `arena` and declares no data.
/// - ensures: one verdict per unrefused declaration, in admission order.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a derived operation is accepted only where its motive and
///   its base agree with the answer it was read off.
/// - witness: `lower::identity::tests::back_then_and_cong_unfold_to_transports`
#[spec(ensures: |ret| ret.judged().len() <= module.declarations().len())]
fn judged(
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
                | DeclarationOutcome::Completed {
                    declared_type,
                    body,
                } => (Maybe::Present(declared_type), Maybe::Present(body)),
                | DeclarationOutcome::Uncompleted { declared_type } => (
                    Maybe::Present(declared_type),
                    Maybe::Absent(body::Absent::Hole),
                ),
                | DeclarationOutcome::Bodied { body } => (
                    Maybe::Absent(signature::Absent::Unsigned),
                    Maybe::Present(body),
                ),
                | DeclarationOutcome::Data(_) | DeclarationOutcome::Refused(_) => return None,
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
fn assert_accepted(report: &ModuleReport)
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
fn outcome_of<'source>(
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
        | DeclarationOutcome::Completed { body, .. } | DeclarationOutcome::Bodied { body } => body,
        | other => panic!("`{name:?}` lowers a body: {other:?}"),
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
        SourceText::from("def p : Path(Integer, 4, 4);\ndef p = here(4);\n"),
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
    let source = "def p = here(4, 5);\n";
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
fn funext_lowers_to_its_former()
{
    let functions = "def id(b: +{Unit, Unit}) -> -F +{Unit, Unit} {\n  return b\n}\ndef again(b: +{Unit, Unit}) -> -F +{Unit, Unit} {\n  return b\n}\n";
    let mut arena = CoreArena::new();
    let source = format!(
        "{functions}def same : Path(+U[ω] (+{{Unit, Unit}} -> -F +{{Unit, Unit}}), id, again);\ndef same = funext(id, again);\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let DeclarationOutcome::Completed { body, .. } = outcome_of(&module, "same".into())
    else {
        panic!("the path and its extensionality lower");
    };
    let Some(&Value::Funext(left, right)) = arena.value(body)
    else {
        panic!("`funext(id, again)` is function extensionality");
    };
    assert!(
        matches!(arena.value(left), Some(&Value::Constant(constant)) if usize::from(constant) == 0)
            && matches!(arena.value(right), Some(&Value::Constant(constant)) if usize::from(constant) == 1),
        "both functions are read as values, in order"
    );
    assert_accepted(&judged(&module, &mut arena));

    let mut arena = CoreArena::new();
    let source = format!("{functions}def once = funext(id);\n");
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
    let source = "def funext(x: Integer, y: Integer) -> -F Integer {\n  return x\n}\ndef call : +U (-F Integer);\ndef call = thunk { become funext(1, 2) };\n";
    let module = lowered(SourceText::from(source), &mut arena);
    let Some(&Computation::Application(..)) =
        arena.computation(tail_of(&module, &arena, "call".into()))
    else {
        panic!("a declaration named `funext` shadows the operation");
    };
}

#[test]
fn a_list_moves_along_a_universe_equivalence()
{
    let negation = "def not(b: Bool) -> -F Bool {\n  case b {\n    true => return +{.1 = unit},\n    false => return +{.0 = unit}\n  }\n}\ndef negation : Path(Type, Bool, Bool);\ndef negation = equiv(not, not);\n";
    let mut arena = CoreArena::new();
    let source = format!(
        "{negation}def moved(xs: List(Bool)) -> -F List(Bool) {{\n  become transport(\\X. List(X), negation, xs)\n}}\ndef both : List(Bool);\ndef both = cons(+{{.0 = unit}}, cons(+{{.1 = unit}}, nil));\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let DeclarationOutcome::Completed { body, .. } = outcome_of(&module, "negation".into())
    else {
        panic!("the universe path and its equivalence lower");
    };
    let Some(&Value::Equiv(forward, backward)) = arena.value(body)
    else {
        panic!("`equiv(not, not)` is a universe equivalence");
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
        "{negation}def named(xs: List(Bool)) -> -F List(Bool) {{\n  become transport(negation, negation, xs)\n}}\ndef half = cons(unit);\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
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
        SourceText::from("def keep(nil: Integer) -> -F Integer {\n  return nil\n}\n"),
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
fn a_computation_endpoint_is_the_value_it_returns()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(
            "def dbl(x: Integer) -> -F Integer {\n  become x + x\n}\ndef same(x: Integer, y: Integer) -> -F Path(Integer, dbl(dbl(x)), dbl(dbl(x))) {\n  return here(dbl(dbl(x)))\n}\n",
        ),
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

#[test]
fn a_type_endpoint_is_quoted()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from("def t : Path(Type, Integer, Integer);\n"),
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

#[test]
fn a_bound_name_shadows_an_identity_operation()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(
            "def apply(here: Integer => Integer) -> -F Integer {\n  become here(1)\n}\n",
        ),
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
        SourceText::from(concat!(
            "def flip(a: Integer, b: Integer, p: Path(Integer, a, b)) -> -F Path(Integer, b, a) {\n  become back(p)\n}\n",
            "def join(a: Integer, b: Integer, c: Integer, p: Path(Integer, a, b), q: Path(Integer, b, c)) -> -F(Path(Integer, a, c)) {\n  become p then q\n}\n",
            "def dbl(x: Integer) -> -F Integer {\n  become x + x\n}\n",
            "def image(a: Integer, b: Integer, p: Path(Integer, a, b)) -> -F Path(Integer, dbl(a), dbl(b)) {\n  become cong(dbl, p)\n}\n",
        )),
        &mut arena,
    );
    let transport = |name: &str| match arena.computation(tail_of(&module, &arena, name.into())) {
        | Some(&Computation::PathTransport {
            motive,
            path,
            value,
        }) => (motive, path, value),
        | other => panic!("`{name}` unfolds to a transport: {other:?}"),
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

#[test]
fn a_derived_operation_needs_a_written_path_answer()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from("def g(p: Path(Integer, 1, 1)) -> -F Integer {\n  become back(p)\n}\n"),
        &mut arena,
    );
    assert!(
        matches!(
            outcome_of(&module, "g".into()),
            DeclarationOutcome::Refused(LoweringRefusal::OutOfFragment {
                boundary: FragmentBoundary::Unannotated,
                ..
            })
        ),
        "`back` reads its motive off a written path answer"
    );
}

#[test]
fn matching_reflexivity_is_refused_as_k()
{
    let source = "def uip(n: Integer, p: Path(Integer, n, n)) -> -F Integer {\n  case p { here => return 0 }\n}\n";
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
