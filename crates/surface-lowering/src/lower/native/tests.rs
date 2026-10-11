use alloc::sync::Arc;
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
use gandr_core_term::ConstructorTag;
use gandr_core_term::CoreArena;
use gandr_core_term::Sort;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::hole::HoleId;
use gandr_core_term::pattern::Pattern;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::GroundSort;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::error::FragmentBoundary;
use crate::error::FragmentSort;
use crate::error::LoweringRefusal;
use crate::fixture::grammar;
use crate::fixture::parsed;
use crate::fixture::registered;
use crate::form::FormName;
use crate::lower::LoweringBudget;
use crate::lower::lower_module;
use crate::module::DeclarationOutcome;
use crate::module::LoweredModule;
use crate::namespace::Recognition;
use crate::resolve::OperandCount;
use crate::resolve::SurfaceName;

/// Three nullary constructors.
const COLOR: &str = "data Color : Type { Red : Color; Green : Color; Blue : Color; }\n";

/// A family of one parameter.
const MAYBE: &str =
    "data Maybe(a : Type) : Type { None : Maybe(a); Some : (x : a) --> Maybe(a); }\n";

/// The module the parser and the lowering make of `source`.
///
/// # Specification
/// - requires: the source parses cleanly within the default allowance.
/// - ensures: one declaration per declared name, in admission order.
/// - fails: never on accepted fixtures.
/// - panics: if the lowering refuses the module.
///
/// # Adequacy
/// - hypothesis: L3 — every witness below reads its module through here.
/// - witness: `lower::native::tests::a_data_declaration_lowers_to_its_signature`
#[spec(ensures: |ret| ret.declarations().windows(2).all(|pair| match *pair {
    | [ref left, ref right] => left.constant() < right.constant(),
    | _ => false,
}))]
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
/// - requires: `module` was lowered over `arena`.
/// - ensures: one verdict per unrefused declaration, in admission order.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a data declaration and the matches over it are accepted,
///   which only a well-scoped tree with a well-formed motive is.
/// - witness: `lower::native::tests::nested_constructor_patterns_compile_to_nested_cases`
#[spec(ensures: |ret| ret.judged().len() == module.declarations().iter().filter(|declaration| !matches!(declaration.outcome(), DeclarationOutcome::Refused(_))).count())]
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
                | DeclarationOutcome::Data(index) => {
                    return match module.data(index) {
                        | Maybe::Present(held) => Some(Declaration::data(
                            declaration.constant(),
                            Arc::clone(held),
                            origin,
                        )),
                        | Maybe::Absent(_) => None,
                    };
                },
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
fn assert_accepted(report: &ModuleReport)
{
    let accepted = report.judged().iter().all(|judged| {
        matches!(
            judged.verdict(),
            Verdict::Data | Verdict::Checked { .. } | Verdict::Synthesised { .. }
        )
    });
    assert!(accepted, "{report:?}");
}

/// The refusal of the declaration `name` in `module`.
///
/// # Specification
/// - requires: `module` declares `name`.
/// - ensures: that declaration's refusal.
/// - fails: never.
/// - panics: if the declaration is missing or lowered.
///
/// # Adequacy
/// - hypothesis: L3 — the refusal witnesses read exact refusals here.
/// - witness: `lower::native::tests::a_non_exhaustive_match_is_refused`
#[spec(ensures: |ret| module.declarations().iter().any(|declaration| declaration.outcome() == DeclarationOutcome::Refused(ret)))]
fn refusal_of<'source>(
    module: &LoweredModule<'source>,
    name: SurfaceName<'_>,
) -> LoweringRefusal<'source>
{
    let Some(declaration) = module
        .declarations()
        .iter()
        .find(|declaration| declaration.name() == name)
    else {
        panic!("`{name}` is declared");
    };
    let DeclarationOutcome::Refused(refusal) = declaration.outcome()
    else {
        panic!("`{name}` is refused: {:?}", declaration.outcome());
    };

    refusal
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
/// - hypothesis: L3 — as [`refusal_of`].
/// - witness: `lower::native::tests::a_constructor_applies_to_its_fields`
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
        panic!("`{name}` is declared");
    };

    declaration.outcome()
}

/// The body of the declaration `name` in `module`.
///
/// # Specification
/// - requires: `module` lowers a body for `name`.
/// - ensures: that body.
/// - fails: never.
/// - panics: if the declaration lowers no body.
///
/// # Adequacy
/// - hypothesis: L3 — as [`refusal_of`].
/// - witness: `lower::native::tests::a_constructor_applies_to_its_fields`
#[spec(ensures: |ret| matches!(outcome_of(module, name), DeclarationOutcome::Completed { body, .. } | DeclarationOutcome::Bodied { body } if body == ret))]
fn body_named(
    module: &LoweredModule<'_>,
    name: SurfaceName<'_>,
) -> ValueId
{
    match outcome_of(module, name) {
        | DeclarationOutcome::Completed { body, .. } | DeclarationOutcome::Bodied { body } => body,
        | other => panic!("`{name}` lowers a body: {other:?}"),
    }
}

/// The computation a function body runs under its parameters.
///
/// # Specification
/// - requires: `body` is a function's thunked lambda chain.
/// - ensures: the computation under the thunk and every lambda.
/// - fails: never.
/// - panics: if `body` is no thunk.
///
/// # Adequacy
/// - hypothesis: L3 — the match witnesses read their tree from here.
/// - witness: `lower::native::tests::nested_constructor_patterns_compile_to_nested_cases`
#[spec(ensures: |ret| !matches!(arena.computation(ret), Some(&Computation::Lambda(_))))]
fn tail_of(
    arena: &CoreArena,
    body: ValueId,
) -> ComputationId
{
    let Some(&Value::Thunk(mut computation)) = arena.value(body)
    else {
        panic!("a function body is a thunk");
    };
    while let Some(&Computation::Lambda(under)) = arena.computation(computation) {
        computation = under;
    }

    computation
}

/// Every computation reachable from `root`, in a preorder walk.
///
/// # Specification
/// - requires: `root` is in `arena`.
/// - ensures: `root` first, then each reachable computation once per path.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the tree witnesses count the eliminations here.
/// - witness: `lower::native::tests::literal_patterns_compare_and_branch`
#[spec(ensures: |ret| ret.first() == Some(&root))]
fn reachable(
    arena: &CoreArena,
    root: ComputationId,
) -> Vec<ComputationId>
{
    let mut seen = Vec::new();
    let mut pending = Vec::from([root]);
    while let Some(next) = pending.pop() {
        seen.push(next);
        match arena.computation(next) {
            | Some(&Computation::Bind(first, second)) => pending.extend([second, first]),
            | Some(&Computation::Lambda(under)) => pending.push(under),
            | Some(&Computation::Case {
                on_left, on_right, ..
            }) => pending.extend([on_right, on_left]),
            | Some(&Computation::DataCase { ref branches, .. }) => {
                pending.extend(branches.iter().rev().copied());
            },
            | _ => {},
        }
    }

    seen
}

#[test]
fn a_data_declaration_lowers_to_its_signature()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(
            "data Pair(a : Type, b : Type) : Type { Mk : (x : a, y : b) --> Pair(a, b); }\ndata Flag : Type { On : Flag; Off : Flag; }\n",
        ),
        &mut arena,
    );
    let (DeclarationOutcome::Data(pair), DeclarationOutcome::Data(flag)) = (
        outcome_of(&module, SurfaceName::from("Pair")),
        outcome_of(&module, SurfaceName::from("Flag")),
    )
    else {
        panic!("both declarations lower to their signatures");
    };
    let (Maybe::Present(pair), Maybe::Present(flag)) = (module.data(pair), module.data(flag))
    else {
        panic!("each index names a signature");
    };
    assert_eq!(pair.parameters().len(), 2_usize);
    let [ref fields] = *pair.constructors()
    else {
        panic!("one constructor");
    };
    let [first, second] = **fields
    else {
        panic!("two fields");
    };
    assert_ne!(first, second, "each field names its own parameter");
    assert_eq!(flag.parameters().len(), 0_usize);
    assert_eq!(flag.constructors(), &[Vec::new(), Vec::new()]);
    assert!(matches!(
        arena.value_type(flag.kind()),
        Some(&ValueType::Universe {
            sort: Sort::Ground(GroundSort::Value),
            ..
        })
    ));
    let report = judged(&module, &mut arena);
    assert_eq!(report.judged().len(), 2_usize);
    assert!(
        report
            .judged()
            .iter()
            .all(|judged| judged.verdict() == Verdict::Data),
        "the checker forms both signatures: {report:?}"
    );
}

#[test]
fn an_indexed_generator_is_declined()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(
            "data Vec(n : Integer) : Type { Nil : Vec(0); }\ndata Bad(a : Type) : Type { Mk : Bad(Integer); }\ndata Two(a : Type, b : Type) : Type { Mk2 : Two(b, a); }\n",
        ),
        &mut arena,
    );
    for name in ["Vec", "Bad", "Two"].map(SurfaceName::from) {
        assert!(
            matches!(refusal_of(&module, name), LoweringRefusal::OutOfFragment {
                form: FormName::DATA_GENERATOR,
                sort: FragmentSort::Declaration,
                boundary: FragmentBoundary::Indexed,
                ..
            }),
            "`{name}` is declined as indexed"
        );
    }
}

#[test]
fn members_outside_the_fragment_are_declined_by_name()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(
            "data NatOp : Type { Zero : NatOp; oper add(m : NatOp, n : NatOp) -> NatOp; }\ndata NatRule : Type { Nil : NatRule; rule id(Nil) ==> Nil; }\ndata NatRetired : Type { Only : NatRetired; op stale(x : NatRetired) -> NatRetired; }\n",
        ),
        &mut arena,
    );
    for (name, form) in [
        (SurfaceName::from("NatOp"), FormName::OP_MEMBER),
        (SurfaceName::from("NatRule"), FormName::RULE_MEMBER),
        (SurfaceName::from("NatRetired"), FormName::OP_MEMBER),
    ] {
        assert!(
            matches!(
                refusal_of(&module, name),
                LoweringRefusal::OutOfFragment {
                    form: declined,
                    sort: FragmentSort::Declaration,
                    boundary: FragmentBoundary::Unadmitted,
                    ..
                } if declined == form
            ),
            "`{name}` declines its member by name: {:?}",
            refusal_of(&module, name)
        );
    }
}

#[test]
fn an_attribute_block_decorates_the_data_declaration_after_it()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(
            "@[ checks ]\ndata Flag : Type { On : Flag; Off : Flag; }\n@[ checks ]\ndef on = On;\n",
        ),
        &mut arena,
    );
    let [ref family, ref value] = *module.declarations()
    else {
        panic!("two names are declared");
    };
    assert!(matches!(family.outcome(), DeclarationOutcome::Data(_)));
    for declaration in [family, value] {
        let Maybe::Present(written) = declaration.definition()
        else {
            panic!("each declaration keeps its digest");
        };
        let [ref entry] = *module.attributes().entries(written)
        else {
            panic!("one attribute is filed under each declaration");
        };
        assert_eq!(entry.name(), registered(SurfaceName::from("checks")));
    }
}

#[test]
fn a_constructor_named_twice_is_refused()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(
            "data A : Type { X : A; Y : A; }\ndata B : Type { Z : B; X : B; }\ndata C : Type { W : C; W : C; }\n",
        ),
        &mut arena,
    );
    assert!(matches!(
        outcome_of(&module, SurfaceName::from("A")),
        DeclarationOutcome::Data(_)
    ));
    for name in ["B", "C"].map(SurfaceName::from) {
        assert!(
            matches!(
                refusal_of(&module, name),
                LoweringRefusal::DuplicateDefinition { .. }
            ),
            "`{name}` reuses a constructor name"
        );
    }
}

#[test]
fn a_constructor_applies_to_its_fields()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        "{COLOR}data Triple : Type {{ T : (a : Integer, b : Integer, c : Integer) --> Triple; }}\ndef green = Green;\ndef triple = T(1, 2, 3);\ndef short = T(1, 2);\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let Some(&Value::Constructor {
        datatype,
        tag,
        ref fields,
    }) = arena.value(body_named(&module, SurfaceName::from("green")))
    else {
        panic!("a bare constructor is a constructor value");
    };
    assert_eq!(tag, ConstructorTag::from(1_usize));
    assert!(fields.is_empty());
    assert_eq!(
        arena.value_type(datatype),
        Some(&ValueType::Data {
            declaration: ConstantIndex::from(0_usize),
            arguments: Vec::new(),
        })
    );
    assert!(matches!(
        module.origins().value_type(datatype),
        Maybe::Present(origin) if origin.provenance() == crate::origin::Provenance::Inserted(crate::origin::Insertion::Classifier)
    ));
    let Some(&Value::Constructor {
        tag, ref fields, ..
    }) = arena.value(body_named(&module, SurfaceName::from("triple")))
    else {
        panic!("an applied constructor is a constructor value");
    };
    assert_eq!(tag, ConstructorTag::from(0_usize));
    assert_eq!(fields.len(), 3_usize);
    assert!(matches!(
        refusal_of(&module, SurfaceName::from("short")),
        LoweringRefusal::OutOfFragment {
            boundary: FragmentBoundary::Arity(count),
            ..
        } if count == OperandCount::from(2_usize)
    ));
    let report = judged(&module, &mut arena);
    assert_accepted(&report);
}

#[test]
fn a_parameterized_constructor_needs_its_classifier()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        "{MAYBE}def bare = None;\ndef some = (Some(3) : Maybe(Integer));\ndef none = (None : Maybe(Integer));\ndef three = (3 : Integer);\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    assert!(matches!(
        refusal_of(&module, SurfaceName::from("bare")),
        LoweringRefusal::OutOfFragment {
            boundary: FragmentBoundary::Unannotated,
            ..
        }
    ));
    assert!(matches!(
        refusal_of(&module, SurfaceName::from("three")),
        LoweringRefusal::OutOfFragment {
            form: FormName::ANNOTATION,
            boundary: FragmentBoundary::Unadmitted,
            ..
        }
    ));
    let Some(&Value::Constructor { datatype, .. }) =
        arena.value(body_named(&module, SurfaceName::from("some")))
    else {
        panic!("an annotated constructor is a constructor value");
    };
    let Some(&ValueType::Data {
        declaration,
        ref arguments,
    }) = arena.value_type(datatype)
    else {
        panic!("its classifier is the annotation's family");
    };
    assert_eq!(declaration, ConstantIndex::from(0_usize));
    assert_eq!(arguments.len(), 1_usize);
    let report = judged(&module, &mut arena);
    assert_accepted(&report);
}

#[test]
fn a_data_family_applies_to_its_parameters()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        "{MAYBE}def keep(m : Maybe(Integer)) -> -F Integer {{ ret 0 }}\ndef wide : Maybe(Integer, Integer) ;\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let DeclarationOutcome::Completed { declared_type, .. } =
        outcome_of(&module, SurfaceName::from("keep"))
    else {
        panic!("the function lowers both halves");
    };
    let Some(&ValueType::Thunk(arrow)) = arena.value_type(declared_type)
    else {
        panic!("a thunked arrow");
    };
    let Some(&gandr_core_term::CompType::Arrow { domain, .. }) = arena.comp_type(arrow)
    else {
        panic!("an arrow");
    };
    assert!(matches!(
        arena.value_type(domain),
        Some(&ValueType::Data { declaration, ref arguments }) if declaration == ConstantIndex::from(0_usize) && arguments.len() == 1
    ));
    assert!(matches!(
        refusal_of(&module, SurfaceName::from("wide")),
        LoweringRefusal::OutOfFragment {
            boundary: FragmentBoundary::Arity(count),
            ..
        } if count == OperandCount::from(2_usize)
    ));
    let report = judged(&module, &mut arena);
    assert_accepted(&report);
}

#[test]
fn a_match_takes_its_answer_from_the_function_result()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        "{COLOR}def rank(c : Color) -> -F Integer {{ case c {{ Red => ret 0, _ => ret 1 }} }}\ndef stated(c : Color) -> -F Integer {{ run n <- case c -> -F Integer {{ Red => ret 0, _ => ret 1 }}; ret n }}\ndef typed(t : Type, x : t, c : Color) -> -F t {{ case c {{ Red => ret x, _ => ret x }} }}\ndef any(c : Color) -> -F Integer {{ case c {{ _ => ret 1 }} }}\ndef same(c : Color) -> -F Color {{ case c {{ d => ret d }} }}\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    for name in ["rank", "stated", "typed", "any", "same"].map(SurfaceName::from) {
        assert!(
            matches!(
                outcome_of(&module, name),
                DeclarationOutcome::Completed { .. }
            ),
            "`{name}` lowers: {:?}",
            outcome_of(&module, name)
        );
    }
    let root = tail_of(&arena, body_named(&module, SurfaceName::from("rank")));
    let Some(&Computation::DataCase {
        scrutinee,
        motive,
        ref branches,
    }) = arena.computation(root)
    else {
        panic!("the match is a data case on its scrutinee");
    };
    assert_eq!(branches.len(), 3_usize);
    assert!(matches!(
        arena.value(scrutinee),
        Some(&Value::Variable { index, .. }) if index == gandr_kernel_term::DeBruijnIndex::from(0_u32)
    ));
    let Some(&gandr_core_term::CompType::Returner(answer)) = arena.comp_type(motive)
    else {
        panic!("the motive is the function's result");
    };
    assert_eq!(
        arena.value_type(answer),
        Some(&ValueType::Base(gandr_kernel_term::BaseType::Integer))
    );
    let report = judged(&module, &mut arena);
    assert_accepted(&report);
}

#[test]
fn a_match_without_an_answer_is_unannotated()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        "{COLOR}def inner(c : Color) -> -F Integer {{ run n <- case c {{ Red => ret 0, _ => ret 1 }}; ret n }}\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    assert!(matches!(
        refusal_of(&module, SurfaceName::from("inner")),
        LoweringRefusal::OutOfFragment {
            form: FormName::CASE,
            boundary: FragmentBoundary::Unannotated,
            ..
        }
    ));
}

#[test]
fn nested_constructor_patterns_compile_to_nested_cases()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(
            "data Inner : Type { No : Inner; Yes : (n : Integer) --> Inner; }\ndata Outer : Type { Nothing : Outer; Just : (i : Inner) --> Outer; }\ndef depth(m : Outer) -> -F Integer { case m { Just(Yes(n)) => ret n, Just(No) => ret 0, other => ret 1 } }\ndef answer = (Just((Yes(41) : Inner)) : Outer);\n",
        ),
        &mut arena,
    );
    let root = tail_of(&arena, body_named(&module, SurfaceName::from("depth")));
    let cases = reachable(&arena, root)
        .into_iter()
        .filter(|&at| matches!(arena.computation(at), Some(&Computation::DataCase { .. })))
        .count();
    assert_eq!(
        cases, 2_usize,
        "the outer switch and the switch on its field"
    );
    let report = judged(&module, &mut arena);
    assert_accepted(&report);
}

#[test]
fn literal_patterns_compare_and_branch()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(
            "def small(n : Integer) -> -F Integer { case n { 0 => ret 10, 1 => ret 11, _ => ret 12 } }\ndef flip(b : Bool) -> -F Integer { case b { true => ret 1, false => ret 0 } }\n",
        ),
        &mut arena,
    );
    let compared = reachable(
        &arena,
        tail_of(&arena, body_named(&module, SurfaceName::from("small"))),
    )
    .into_iter()
    .filter(|&at| matches!(arena.computation(at), Some(&Computation::Primitive { .. })))
    .count();
    assert_eq!(compared, 2_usize, "one comparison per literal");
    let branched = reachable(
        &arena,
        tail_of(&arena, body_named(&module, SurfaceName::from("flip"))),
    )
    .into_iter()
    .filter(|&at| matches!(arena.computation(at), Some(&Computation::Case { .. })))
    .count();
    assert_eq!(branched, 1_usize, "one case on the boolean");
    let report = judged(&module, &mut arena);
    assert_accepted(&report);
}

#[test]
fn a_pattern_hole_leaves_its_leaf_stuck()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        "{COLOR}{MAYBE}def rank(c : Color) -> -F Integer {{ case c {{ Red => ret 0, ? => ret 1, Blue => ret 2 }} }}\ndef inside(m : Maybe(Integer)) -> -F Integer {{ case m {{ Some(?) => ret 100, None => ret 0 }} }}\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    for name in ["rank", "inside"] {
        let stuck = reachable(
            &arena,
            tail_of(&arena, body_named(&module, SurfaceName::from(name))),
        )
        .into_iter()
        .any(|at| matches!(arena.computation(at), Some(&Computation::Hole(_))));
        assert!(stuck, "`{name}` is stuck on its hole");
    }
}

#[test]
fn a_non_exhaustive_match_is_refused()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        "{COLOR}def partial(c : Color) -> -F Integer {{ case c {{ Red => ret 0, Green => ret 1 }} }}\ndef open(n : Integer) -> -F Integer {{ case n {{ 0 => ret 0 }} }}\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    for name in ["partial", "open"].map(SurfaceName::from) {
        assert!(
            matches!(
                refusal_of(&module, name),
                LoweringRefusal::NonExhaustiveMatch { .. }
            ),
            "`{name}` misses a case"
        );
    }
}

#[test]
fn patterns_outside_the_fragment_are_declined_by_name()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        "{COLOR}def text(s : String) -> -F Integer {{ case s {{ \"a\" => ret 0, _ => ret 1 }} }}\ndef mixed(c : Color) -> -F Integer {{ case c {{ Red => ret 0, 1 => ret 1, _ => ret 2 }} }}\ndef bound(c : Color) -> -F Integer {{ case c {{ Red | x => ret 0 }} }}\ndef absurd(c : Color) -> -F Integer {{ case c {{}} }}\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    assert!(matches!(
        refusal_of(&module, SurfaceName::from("text")),
        LoweringRefusal::OutOfFragment {
            boundary: FragmentBoundary::Unadmitted,
            ..
        }
    ));
    assert!(matches!(
        refusal_of(&module, SurfaceName::from("mixed")),
        LoweringRefusal::OutOfFragment {
            form: FormName::CASE,
            boundary: FragmentBoundary::WrongSort,
            ..
        }
    ));
    assert!(matches!(
        refusal_of(&module, SurfaceName::from("bound")),
        LoweringRefusal::OutOfFragment {
            form: FormName::OR_PATTERN,
            boundary: FragmentBoundary::Unadmitted,
            ..
        }
    ));
    assert!(matches!(
        refusal_of(&module, SurfaceName::from("absurd")),
        LoweringRefusal::OutOfFragment {
            form: FormName::CASE_WITH_VIEW,
            boundary: FragmentBoundary::Unadmitted,
            ..
        }
    ));
}

#[test]
fn an_or_pattern_settles_each_alternative()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        "{COLOR}def warm(c : Color) -> -F Integer {{ case c {{ Red | Green => ret 1, Blue => ret 0 }} }}\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let root = tail_of(&arena, body_named(&module, SurfaceName::from("warm")));
    let Maybe::Present(kept) = module.origins().case(root)
    else {
        panic!("the match keeps its arms");
    };
    let arms: Vec<usize> = kept.arms.iter().map(|arm| arm.arm).collect();
    assert_eq!(
        arms,
        [0_usize, 0, 1],
        "each alternative is one record of its arm"
    );
    let report = judged(&module, &mut arena);
    assert_accepted(&report);
}

#[test]
fn a_match_keeps_its_patterns_beside_its_tree()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        "{MAYBE}def pick(m : Maybe(Integer)) -> -F Integer {{ case m {{ Some(x) => ret x, ? => ret 0 }} }}\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let root = tail_of(&arena, body_named(&module, SurfaceName::from("pick")));
    let Maybe::Present(kept) = module.origins().case(root)
    else {
        panic!("the match keeps its arms");
    };
    let [ref some, ref hole] = *kept.arms
    else {
        panic!("two arms");
    };
    assert!(matches!(
        kept.patterns.pattern(some.pattern),
        Some(&Pattern::Constructor { tag, ref fields }) if tag == ConstructorTag::from(1_usize) && fields.len() == 1
            && matches!(fields.first().and_then(|&field| kept.patterns.pattern(field)), Some(&Pattern::Binder))
    ));
    let Some(&Pattern::Hole(identity)) = kept.patterns.pattern(hole.pattern)
    else {
        panic!("the second arm is a pattern hole");
    };
    assert_eq!(
        identity,
        HoleId::from(u32::try_from(usize::from(hole.written)).unwrap()),
        "a pattern hole is named by its syntax node"
    );
    assert!(
        reachable(&arena, root)
            .into_iter()
            .any(|at| arena.computation(at) == Some(&Computation::Hole(identity))),
        "the tree is stuck on the same hole"
    );
    assert!(usize::from(kept.scrutinee) > usize::from(kept.written));
    for at in reachable(&arena, root) {
        assert!(
            matches!(module.origins().computation(at), Maybe::Present(_)),
            "every node of the tree has an origin"
        );
    }
    let report = judged(&module, &mut arena);
    assert!(
        report
            .judged()
            .iter()
            .all(|judged| !matches!(judged.verdict(), Verdict::Refused(_))),
        "{report:?}"
    );
}
