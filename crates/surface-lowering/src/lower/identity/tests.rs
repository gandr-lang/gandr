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
use gandr_core_term::equal_type_syntax;
use gandr_core_term::identity::Relation;
use gandr_core_term::session::DialogueMove;
use gandr_core_term::session::Endpoint;
use gandr_core_term::session::RecordedMove;
use gandr_core_term::session::SessionRelation;
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
        "{negation}def moved(xs: List(Bool)) -> -F List(Bool) {{\n  become transport(\\X. List(X), negation, xs)\n}}\ndef again(xs: List(Bool)) -> -F List(Bool) {{\n  become transport(\\X. List(X), negation, xs)\n}}\ndef both : List(Bool);\ndef both = cons(+{{.0 = unit}}, cons(+{{.1 = unit}}, nil));\n"
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
    let mut written: Vec<(usize, Provenance)> = module
        .origins()
        .motives()
        .iter()
        .map(|&(_, origin)| (usize::from(origin.span().start()), origin.provenance()))
        .collect();
    written.sort_unstable_by_key(|&(at, _)| at);
    let expected: Vec<(usize, Provenance)> = source
        .match_indices("\\X. List(X)")
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
fn a_path_product_lowers_to_its_former()
{
    let negation = "def not(b: Bool) -> -F Bool {\n  case b {\n    true => return +{.1 = unit},\n    false => return +{.0 = unit}\n  }\n}\n";
    let mut arena = CoreArena::new();
    let source = format!("{negation}def paired = pathProduct(here(Unit), equiv(not, not));\n");
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let DeclarationOutcome::Bodied { body } = outcome_of(&module, "paired".into())
    else {
        panic!("the product lowers");
    };
    let Some(&Value::PathProduct(first, second)) = arena.value(body)
    else {
        panic!("`pathProduct(p, q)` is the native product");
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
    let source = format!("{negation}def half = pathProduct(equiv(not, not));\n");
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
    let negation = "def not(b: Bool) -> -F Bool {\n  case b {\n    true => return +{.1 = unit},\n    false => return +{.0 = unit}\n  }\n}\n";
    let mut arena = CoreArena::new();
    let source = format!("{negation}def paired = flowProduct(stay(Unit), forward(not));\n");
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let DeclarationOutcome::Bodied { body } = outcome_of(&module, "paired".into())
    else {
        panic!("the product lowers");
    };
    let Some(&Value::FlowProduct(first, second)) = arena.value(body)
    else {
        panic!("`flowProduct(p, q)` is the kernel's flow product");
    };
    assert!(
        matches!(arena.value(first), Some(&Value::Stay(_)))
            && matches!(arena.value(second), Some(&Value::Forward(_))),
        "both flows are read as values, in order"
    );
    assert_accepted(&judged(&module, &mut arena));

    let mut arena = CoreArena::new();
    let source = format!("{negation}def half = flowProduct(forward(not));\n");
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

/// A path at a universe its own tiles spell reads each endpoint at the type
/// sort: a sum and a session protocol, neither of which reads as a value,
/// each stand as the quoted code of the type it spells.
#[test]
fn a_path_at_a_universe_reads_its_endpoints_as_types_402()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(
            "def sums : Path(Type, +{Unit, Unit}, +{Unit, Unit});\ndef sessions : Path(Type, ?Integer. end, ?Integer. end);\n",
        ),
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
    let module = lowered(
        SourceText::from(
            "def lifted : Bridge(List(Integer), [1, 2], [1, 2]);\ndef lifted = (unit, (unit, unit));\ndef related : Bridge(Type, Unit, String);\ndef related = thunk { fn (x : Unit) { fn (y : String) { return Unit } } };\n",
        ),
        &mut arena,
    );
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
        SourceText::from("def four : Bridge(Integer, 4, 4);\ndef four = here(4);\n"),
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
        Some(&Computation::PathTransport {
            motive,
            path,
            value,
        }) => (motive, path, value),
        other => panic!("`{name}` unfolds to a transport: {other:?}"),
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

/// The transport `cong` unfolds to reads its map only lifted under the
/// motive's binder; a parameter map's lift is the written map's copy, so it
/// answers at the map's bytes (#443).
#[test]
fn a_parameter_map_under_cong_answers_at_its_bytes_443()
{
    let source = "def mapped(f: Integer => Integer, a: Integer, b: Integer, p: Path(Integer, a, b)) -> -F Path(Integer, f(a), f(b)) {\n  become cong(f, p)\n}\n";
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
        .find("cong(f")
        .expect("the body writes `cong(f`")
        .saturating_add(5);
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
        SourceText::from(concat!(
            "def g(p: Path(Integer, 1, 1)) -> -F Integer {\n  become back(p)\n}\n",
            "data Triple(a : Type, b : Type, c : Type) : Type {\n  Mk : Triple(a, b, c);\n}\n",
            "def three(p: Path(Integer, 1, 1)) -> -F Triple(Integer, Integer, Integer) {\n  become back(p)\n}\n",
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
/// derived composite's transport is, so `loop then loop` and its explicit
/// spelling lower alike; before, the written one nested a run that no
/// computation encloses.
#[test]
fn a_written_transport_read_as_a_value_is_the_value_it_returns_985()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(concat!(
            "data Circle : Type {\n  Base : Circle;\n  loop : Base <-> Base;\n}\n",
            "def derived : Path(Circle, Base, Base);\ndef derived = loop then loop;\n",
            "def written : Path(Circle, Base, Base);\ndef written = transport(\\a. Path(Circle, Base, a), loop, loop);\n",
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
        assert!(
            matches!(
                arena.value(body),
                Some(&Value::Returned(computation))
                    if matches!(arena.computation(computation), Some(&Computation::PathTransport { .. }))
            ),
            "`{name}` is the value its transport returns: {:?}",
            arena.value(body)
        );
    }
}

/// #1003: `back(loop)` at the circle's point moves the empty word, as the
/// written transport's `here(Base)` lowers there, so the two spellings lower
/// to one transport. Away from a looped point it moves `here`, as
/// `back_then_and_cong_unfold_to_transports` pins.
#[test]
fn back_at_a_looped_point_moves_its_empty_word_1003()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(concat!(
            "data Circle : Type {\n  Base : Circle;\n  loop : Base <-> Base;\n}\n",
            "def derived : Path(Circle, Base, Base);\ndef derived = back(loop);\n",
            "def written : Path(Circle, Base, Base);\ndef written = transport(\\a. Path(Circle, a, Base), loop, here(Base));\n",
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
        SourceText::from(concat!(
            "data Circle : Type {\n  Base : Circle;\n  loop : Base <-> Base;\n}\n",
            "def collapse(x : Circle) -> -F Circle {\n  case x {\n    Base => Base\n  }\n}\n",
            "def two : Path(Circle, Base, Base);\ndef two = loop then loop;\n",
            "def undone : Path(Circle, Base, Base);\ndef undone = back(loop then loop);\n",
            "def collapsed : Path(Path(Circle, Base, Base), cong(collapse, loop), here(Base));\n",
            "def unread : Path(Integer, 1, 1);\ndef unread = back(here(1));\n",
            "def pointed : Path(Circle, Base, Base);\ndef pointed = cong(Base, loop);\n",
            "def broken(x : Circle) -> -F Bogus {\n  case x {\n    Base => Base\n  }\n}\n",
            "def over_broken : Path(Circle, Base, Base);\ndef over_broken = cong(broken, loop);\n",
            "def emptyFirst : Path(Circle, Base, Base);\ndef emptyFirst = here(Base) then loop;\n",
        )),
        &mut arena,
    );
    let transport = |value, name: &str| {
        let Some(&Value::Returned(computation)) = arena.value(value)
        else {
            panic!("`{name}` is the value its transport returns");
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
        SourceText::from(concat!(
            "data Circle : Type {\n  Base : Circle;\n  loop : Base <-> Base;\n}\n",
            "data Int : Type {\n  Z : Int;\n  S : (x : Int) --> Int;\n}\n",
            "def up(n : Int) -> -F Int {\n  S(n)\n}\n",
            // A parameter, in a body and in a type.
            "def inBody(p : Path(Circle, Base, Base)) -> -F Path(Circle, Base, Base) {\n  back(p)\n}\n",
            "def inType(p : Path(Circle, Base, Base)) -> -F Path(Path(Circle, Base, Base), p then loop, p then loop) {\n  here(p then loop)\n}\n",
            // A call of a definition, in a body and in a type; a later call of
            // the one whose type holds the operation.
            "def twice(p : Path(Circle, Base, Base)) -> -F Path(Circle, Base, Base) {\n  p then p\n}\n",
            "def overCall(p : Path(Circle, Base, Base)) -> -F Path(Circle, Base, Base) {\n  back(twice(p))\n}\n",
            "def inTypeCall(p : Path(Circle, Base, Base)) -> -F Path(Path(Circle, Base, Base), twice(p) then p, twice(p) then p) {\n  here(twice(p) then p)\n}\n",
            "def later(p : Path(Circle, Base, Base)) -> -F Path(Path(Circle, Base, Base), twice(p) then p, twice(p) then p) {\n  back(inTypeCall(p))\n}\n",
            // A call of a signature, and a recursive call's descent.
            "def sig : (a : Int) => Path(Int, a, a) ;\n",
            "def overSig(a : Int) -> -F Path(Int, S(a), S(a)) {\n  cong(up, sig(a)) then here(S(a))\n}\n",
            "def rec descend(b : Int) -> -F Path(Int, b, b) {\n  case b {\n    Z => here(Z),\n    S(x) => cong(up, descend[<](x)) then here(S(x))\n  }\n}\n",
            // `cong` over a parameter function.
            "def mapped(f : +U[ω] (Circle -> -F Int)) -> -F Path(Int, f(Base), f(Base)) {\n  back(cong(f, loop))\n}\n",
            // A parameter of no path type.
            "def pointed(c : Circle) -> -F Path(Circle, Base, Base) {\n  back(c) then loop\n}\n",
            // A parameter composed in a signature's own type, under a call,
            // and a `cong` over a call of that signature: the signature's
            // result is minted after the parameter types the composite inside
            // it reads, though they stand deeper in the tree.
            "def size(p : Path(Circle, Base, Base)) -> -F Circle {\n  return Base\n}\n",
            "def same(c : Circle) -> -F Circle {\n  return c\n}\n",
            "def joined : (q : Path(Circle, Base, Base), p : Path(Circle, Base, Base)) => Path(Circle, size(p then q), size(p then q)) ;\n",
            "def unjoined(p : Path(Circle, Base, Base)) -> -F Path(Circle, same(size(p then p)), same(size(p then p))) {\n  back(cong(same, joined(p, p)))\n}\n",
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
        SourceText::from(concat!(
            "data Circle : Type {\n  Base : Circle;\n  loop : Base <-> Base;\n}\n",
            "def named : Path(Circle, Base, Base) = loop;\n",
            "def flipped : Path(Circle, Base, Base) = back(named);\n",
            "def round : Path(Circle, Base, Base) = named then back(named);\n",
            "def unstated = loop;\n",
            "def overUnstated : Path(Circle, Base, Base) = back(unstated);\n",
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
/// the alias `(a : A) => B` but not through the thunk it stands for, `+U ((a
/// : A) -> -F B)`, so the explicit spelling refused the call as unannotated.
#[test]
fn a_call_reads_a_dependent_result_through_either_spelling_812()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(concat!(
            "data Int : Type {\n  Z : Int;\n  S : (x : Int) --> Int;\n}\n",
            "def up(n : Int) -> -F Int {\n  S(n)\n}\n",
            "def sugared : (a : Int) => Path(Int, a, a) ;\n",
            "def thunked : +U ((a : Int) -> -F Path(Int, a, a)) ;\n",
            "def overSugared(a : Int) -> -F Path(Int, S(a), S(a)) {\n  cong(up, sugared(a)) then here(S(a))\n}\n",
            "def overThunked(a : Int) -> -F Path(Int, S(a), S(a)) {\n  cong(up, thunked(a)) then here(S(a))\n}\n",
            "def pair : +U ((a : Int) -> (b : Int) -> -F Path(Int, b, b)) ;\n",
            "def overPair(a : Int, b : Int) -> -F Path(Int, S(b), S(b)) {\n  cong(up, pair(a, b)) then here(S(b))\n}\n",
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
/// through the value-function alias `A => B` and through the plain arrow
/// `+U (A -> -F B)` it stands for.
#[test]
fn a_call_reads_a_non_dependent_result_through_either_spelling()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(concat!(
            "data Int : Type {\n  Z : Int;\n  S : (x : Int) --> Int;\n}\n",
            "def up(n : Int) -> -F Int {\n  S(n)\n}\n",
            "def sugared : Int => Path(Int, Z, Z) ;\n",
            "def thunked : +U (Int -> -F Path(Int, Z, Z)) ;\n",
            "def overSugared(a : Int) -> -F Path(Int, S(Z), S(Z)) {\n  cong(up, sugared(a)) then here(S(Z))\n}\n",
            "def overThunked(a : Int) -> -F Path(Int, S(Z), S(Z)) {\n  cong(up, thunked(a)) then here(S(Z))\n}\n",
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
        SourceText::from(concat!(
            "data Int : Type {\n  Z : Int;\n  S : (x : Int) --> Int;\n}\n",
            "def up(n : Int) -> -F Int {\n  S(n)\n}\n",
            "def rec descend(k : Int, b : Int) -> -F Path(Int, b, b) {\n  case b {\n    Z => here(Z),\n    S(x) => cong(up, descend[<](k, x)) then here(S(x))\n  }\n}\n",
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
        SourceText::from(concat!(
            "data Circle : Type {\n  Base : Circle;\n  loop : Base <-> Base;\n}\n",
            "data Int : Type {\n  Z : Int;\n}\n",
            "def explicit(f : +U (Circle -> -F Int)) -> -F Path(Int, f(Base), f(Base)) {\n  back(cong(f, loop))\n}\n",
            "def sugared(f : Circle => Int) -> -F Path(Int, f(Base), f(Base)) {\n  back(cong(f, loop))\n}\n",
            "def grouped(f : (Circle => Int)) -> -F Path(Int, f(Base), f(Base)) {\n  back(cong(f, loop))\n}\n",
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
        SourceText::from(concat!(
            "data Circle : Type {\n  Base : Circle;\n  loop : Base <-> Base;\n}\n",
            "def sugared : Circle => Circle ;\n",
            "def sugared = thunk { fn (a) { a } } ;\n",
            "def explicit : +U (Circle -> -F Circle) ;\n",
            "def explicit = thunk { fn (a) { return a } } ;\n",
            "def overSugared : Path(Path(Circle, Base, Base), cong(sugared, loop), loop) ;\n",
            "def overSugared = here(loop) ;\n",
            "def overExplicit : Path(Path(Circle, Base, Base), cong(explicit, loop), loop) ;\n",
            "def overExplicit = here(loop) ;\n",
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
    let source = concat!(
        "def moved(a: Integer, b: Integer, q: Path(Integer, a, b), z0: Path(Integer, a, a), o: Integer, v: Integer) -> -F Integer {\n",
        "  become transport(+U ((y : Integer) -> (z : Path(Integer, a, y)) -> -F Path(Path(Integer, a, y), z, z)), q, z0, o, v)\n",
        "}\n",
        "def plain(n: Integer, q: Path(Integer, 1, 2), v: Integer) -> -F Integer {\n",
        "  become transport(+U (Integer -> Integer -> -F Path(Integer, n, n)), q, v, v, v)\n",
        "}\n",
        "def short(q: Path(Integer, 1, 2), v: Integer) -> -F Integer {\n",
        "  become transport(+U (Integer -> Integer -> -F Integer), q, v, v)\n",
        "}\n",
    );
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
        .find("Path(Integer, n, n)")
        .map(|at| at.saturating_add("Path(Integer, ".len()));
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

/// Two protocols, one widening the other's selection, and a copy of the
/// first, as module type members a statement names bare.
const PROTOCOLS: &str = "module Evolution {\n  type Old = +{ report : !String. end };\n  type New = +{ report : !String. end, pause : end };\n  type Same = +{ report : !String. end };\n";

#[test]
fn session_statements_lower_to_their_formers()
{
    let mut arena = CoreArena::new();
    let source = format!(
        "{PROTOCOLS}  def sub : Flow(Type, Old, New);\n  def sub = sim(Old, New);\n  def eq : Path(Type, Old, Same);\n  def eq = bisim(Old, Same);\n  def kept : Flow(Type, Old, Old);\n  def kept = stay(Old);\n  def widened() -> -F Flow(Type, Old, New) {{\n    become kept then sub\n  }}\n}}\n"
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
        "`Flow(Type, Old, New)` is the directed identity type over two quoted protocols"
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
        "{PROTOCOLS}  def sub : Flow(Type, Old, New);\n  def sub = sim(Old, New);\n  def flip() -> -F Flow(Type, New, Old) {{\n    become back(sub)\n  }}\n  def half = sim(Old);\n}}\n"
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
        "{PROTOCOLS}  def sub : Flow(Type, Old, New);\n  def sub = sim(Old, New);\n}}\ndef served : Run(Evolution.Old);\ndef served = recorded(selected(report), sent(\"progress\"), closed);\ndef forward(receipt: Run(Evolution.Old)) -> -F Run(Evolution.New) {{\n  become ride(\\X. Run(X), Evolution.sub, receipt)\n}}\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
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
        SourceText::from(concat!(
            "module Schema {\n",
            "  type Old = #{String, Integer};\n",
            "  type New = #{Integer, String};\n",
            "  type ReadNew = +U (New -> -F Integer);\n",
            "  type ReadOld = +U (Old -> -F Integer);\n",
            "  def toNew(old: Old) -> -F New {\n    case old { #{name, age} => return #{age, name} }\n  }\n",
            "  def same(n: Integer) -> -F Integer {\n    return n\n  }\n",
            "  def upgrade : Flow(Type, Old, New);\n",
            "  def upgrade = forward(toNew);\n",
            "  def kept : Flow(Type, Integer, Integer);\n",
            "  def kept = forward(same);\n",
            "  def reader : Flow(Type, ReadNew, ReadOld);\n",
            "  def reader = arrow(upgrade, kept);\n",
            "  def both = forward(toNew, same);\n",
            "}\n",
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
        SourceText::from(concat!(
            "def skipped = recorded(skipped(1));\n",
            "def bare = recorded(sent);\n",
            "def twice = recorded(sent(1, 2));\n",
            "def called = recorded(selected(f(1)));\n",
            "def named(receipt: Integer) -> -F Integer {\n  become ride(receipt, receipt, receipt)\n}\n",
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
    let source = "def twice = recorded(sent(1, 2));\n";
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source), &mut arena);
    let start = source.find("sent(1, 2)").expect("the move is written");
    assert!(
        matches!(
            outcome_of(&module, "twice".into()),
            DeclarationOutcome::Refused(LoweringRefusal::OutOfFragment { span, .. })
                if usize::from(span.start()) == start
                    && usize::from(span.end()) == start.saturating_add("sent(1, 2)".len())
        ),
        "a send of two is refused at the move, not the record around it: {:?}",
        outcome_of(&module, "twice".into())
    );
}

#[test]
fn a_dialogue_lowers_its_moves_beside_their_endpoints()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(concat!(
            "module Ask {\n  type Asking = !String. end;\n}\n",
            "def played : Dialogue(Ask.Asking);\n",
            "def played = dialogue(left(sent(\"yes\")), right(received(\"yes\")), right(closed), left(closed));\n",
            "def web() -> -F Web {\n  become decompose(played)\n}\n",
        )),
        &mut arena,
    );
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
        SourceText::from(concat!(
            "def untagged = dialogue(sent(1));\n",
            "def elsewhere = dialogue(middle(closed));\n",
            "def twice = dialogue(left(closed, closed));\n",
            "def inner = dialogue(right(skipped(1)));\n",
            "def both(d: Integer) -> -F Integer {\n  become decompose(d, d)\n}\n",
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
        SourceText::from(concat!(
            "def isoGlyph : Bool ≅ Integer;\n",
            "def isoAlias : Iso(Bool, Integer);\n",
            "def isoRecord : #{to : +U (Bool -> -F Integer), back : +U (Integer -> -F Bool), sect : (a : Bool) => Path(Bool, back(to(a)), a), retr : (b : Integer) => Path(Integer, to(back(b)), b)};\n",
            "def equivGlyph : Bool ≃ Integer;\n",
            "def equivAlias : Bool <~> Integer;\n",
            "def equivRecord : #{to : +U (Bool -> -F Integer), linv : #{g : +U (Integer -> -F Bool), sect : (a : Bool) => Path(Bool, g(to(a)), a)}, rinv : #{h : +U (Integer -> -F Bool), retr : (b : Integer) => Path(Integer, to(h(b)), b)}};\n",
            "def flowGlyph : Bool ⇝ Integer;\n",
            "def flowAlias : Bool ~~> Integer;\n",
            "def flowRecord : Flow(Type, Bool, Integer);\n",
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
        SourceText::from(concat!(
            "def made(i : Bool ≅ Integer) -> -F (Bool ≃ Integer) { case i { #{t, k, s, r} => return #{t, #{#{k, s}, #{k, r}}} } }\n",
            "def forwardOf(e : Bool ≃ Integer) -> -F +U (Bool -> -F Integer) { case e { #{t, #{g, s}, #{h, r}} => return t } }\n",
            "def leftOf(e : Bool <~> Integer) -> -F +U (Integer -> -F Bool) { case e { #{.linv = #{.g = g, .sect = s}} => return g } }\n",
            "def backOf(i : Iso(Bool, Integer)) -> -F +U (Integer -> -F Bool) { case i { #{.back = k} => return k } }\n",
        )),
        &mut arena,
    );
    assert_accepted(&judged(&module, &mut arena));

    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(
            "def misread(e : Bool ≃ Integer) -> -F +U (Bool -> -F Integer) { case e { #{.rinv = #{.h = h}} => return h } }\n",
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
        "def backOf(a : Type, b : Type, i : a ≅ b) -> -F +U (b -> -F a) { case i { #{t, k, s, r} => k } }\n",
    );
    assert_eq!(
        component_names(source),
        ["back", "k", "r", "s", "sect", "t"],
        "every written component is named, the unused `t`, `s` and `r` with `k`, and each rest by \
         its first label"
    );
}

/// A pattern at a `run` binder splits the record the relation its callee
/// returns abbreviates, as one at a parameter does: the callee's signature is
/// minted before the caller's body is read, so its layout comes from the
/// written glyph. Positionally, nested as the equivalence's inverses nest,
/// and by label (#656).
#[test]
fn a_run_binder_splits_the_relation_its_call_returns_656()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(concat!(
            "def kept(i : Bool ≅ Integer) -> -F (Bool ≅ Integer) { return i }\n",
            "def made(i : Bool ≅ Integer) -> -F (Bool ≃ Integer) { case i { #{t, k, s, r} => return #{t, #{#{k, s}, #{k, r}}} } }\n",
            "def split(i : Bool ≅ Integer) -> -F (Bool ≃ Integer) { run j <- kept(i); case j { #{t, k, s, r} => return #{t, #{#{k, s}, #{k, r}}} } }\n",
            "def forwardOf(i : Bool ≅ Integer) -> -F +U (Bool -> -F Integer) { run e <- made(i); case e { #{t, #{g, s}, #{h, r}} => return t } }\n",
            "def backOf(i : Bool ≅ Integer) -> -F +U (Integer -> -F Bool) { run j <- kept(i); case j { #{.back = k} => return k } }\n",
        )),
        &mut arena,
    );
    assert_accepted(&judged(&module, &mut arena));
}

/// A callee whose result is written bare, `-> A`, returns `A` as one written
/// `-> -F A` does: the lowering inserts the returner, so a pattern at a `run`
/// binder of its call splits the record `A` abbreviates (#2255).
#[test]
fn a_run_binder_splits_the_relation_a_bare_result_returns_2255()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(concat!(
            "def kept(i : Bool ≅ Integer) -> Bool ≅ Integer { i }\n",
            "def made(i : Bool ≅ Integer) -> Bool ≃ Integer { case i { #{t, k, s, r} => #{t, #{#{k, s}, #{k, r}}} } }\n",
            "def forwardOf(i : Bool ≅ Integer) -> +U (Bool -> -F Integer) { run e <- made(i); case e { #{t, #{g, s}, #{h, r}} => t } }\n",
            "def backOf(i : Bool ≅ Integer) -> +U (Integer -> -F Bool) { run j <- kept(i); case j { #{.back = k} => k } }\n",
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
        "def backOf(a : Type, b : Type, i : a ≅ b) -> -F +U (b -> -F a) { case i { #{.back = k} => k } }\n",
    );
    assert_eq!(
        component_names(source),
        ["back", "k", "retr", "sect", "sect", "to"],
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
