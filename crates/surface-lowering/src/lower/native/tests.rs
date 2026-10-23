use alloc::string::String;
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
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FixpointEvidence;
use gandr_kernel_term::GroundSort;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use super::ParameterAt;
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
use crate::origin::PatternReading;
use crate::origin::Provenance;
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
/// - requires: `module` was lowered over `arena` and declares no abstract type.
/// - ensures: one verdict per unrefused declaration, in admission order.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a data declaration and the matches over it are accepted,
///   which only a well-scoped tree with a well-formed motive is.
/// - witness: `lower::native::tests::nested_constructor_patterns_compile_to_nested_cases`
#[spec(ensures: |ret| ret.judged().len() == module.declarations().iter().filter(|declaration| !matches!(declaration.outcome(), DeclarationOutcome::Refused(_))).count())]
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
                DeclarationOutcome::Data(index) => {
                    return match module.data(index) {
                        Maybe::Present(held) => Some(Declaration::data(
                            declaration.constant(),
                            Arc::clone(held),
                            origin,
                        )),
                        Maybe::Absent(_) => None,
                    };
                },
                DeclarationOutcome::Codata(index) => {
                    return match module.codata(index) {
                        Maybe::Present(held) => Some(Declaration::codata(
                            declaration.constant(),
                            Arc::clone(held),
                            origin,
                        )),
                        Maybe::Absent(_) => None,
                    };
                },
                DeclarationOutcome::World => {
                    return Some(Declaration::world(declaration.constant(), origin));
                },
                DeclarationOutcome::Abstract(_) | DeclarationOutcome::Refused(_) => return None,
            };
            Some(
                Declaration::new(declaration.constant(), declared, defined, origin)
                    .staged(module.stages(declaration).to_vec())
                    .supplied(module.supplies(declaration).to_vec()),
            )
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
pub(in crate::lower) fn refusal_of<'source>(
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
pub(in crate::lower) fn body_named(
    module: &LoweredModule<'_>,
    name: SurfaceName<'_>,
) -> ValueId
{
    match outcome_of(module, name) {
        DeclarationOutcome::Completed { body, .. } | DeclarationOutcome::Bodied { body } => body,
        other @ (DeclarationOutcome::Uncompleted { .. }
        | DeclarationOutcome::Data(_)
        | DeclarationOutcome::Codata(_)
        | DeclarationOutcome::Abstract(_)
        | DeclarationOutcome::World
        | DeclarationOutcome::Refused(_)) => panic!("`{name}` lowers a body: {other:?}"),
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
pub(in crate::lower) fn tail_of(
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
            Some(&Computation::Bind(first, second)) => pending.extend([second, first]),
            Some(&Computation::Lambda(under) | &Computation::Split { body: under, .. }) => {
                pending.push(under);
            },
            Some(&Computation::Case { ref branches, .. }) => {
                pending.extend(branches.iter().rev().copied());
            },
            Some(&Computation::DataCase { ref branches, .. }) => {
                pending.extend(branches.iter().rev().copied());
            },
            _ => {},
        }
    }

    seen
}

#[test]
fn an_annotation_at_a_statement_is_unadmitted()
{
    let source = alloc::format!(
        "{MAYBE}def f(n : Integer) -> -F Integer {{ (None : Maybe(Integer)); return 1 }}\n"
    );
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let written = "(None : Maybe(Integer))";
    let start = source.find(written).expect("the annotation is written");
    assert!(
        matches!(
            outcome_of(&module, "f".into()),
            DeclarationOutcome::Refused(LoweringRefusal::OutOfFragment {
                span,
                boundary: FragmentBoundary::Unadmitted(crate::Unbuilt::Annotation),
                ..
            }) if usize::from(span.start()) == start
                && usize::from(span.end()) == start.saturating_add(written.len())
        ),
        "an annotation is a value at a tail, never a statement before one: {:?}",
        outcome_of(&module, "f".into())
    );
}

#[test]
fn a_constructor_is_no_value_inside_its_own_family()
{
    let source = "data T : Type { A : T; B : (x : Path(T, A, A)) --> T; }\n";
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source), &mut arena);
    let start = source.find("A, A").expect("the endpoint is written");
    assert!(
        matches!(
            outcome_of(&module, "T".into()),
            DeclarationOutcome::Refused(LoweringRefusal::OutOfFragment {
                span,
                boundary: FragmentBoundary::Unadmitted(crate::Unbuilt::UnknownConstructor),
                ..
            }) if usize::from(span.start()) == start && usize::from(span.end()) == start.saturating_add(1)
        ),
        "a constructor names a value only after its family is declared: {:?}",
        outcome_of(&module, "T".into())
    );
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
fn a_presented_family_lowers_its_rules()
{
    use gandr_core_term::PresentedRule;
    use gandr_core_term::RuleNode;
    use gandr_core_term::RuleVariable;
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(
            "data Circle : Type {\n  Base : Circle;\n  Loop : (x : Circle) --> Circle;\n  Unloop : (x : Circle) --> Circle;\n  rule Loop(Unloop(x)) ==> x;\n  rule Unloop(Loop(y)) ==> y;\n}\ndata Flag : Type { On : Flag; Off : Flag; }\n",
        ),
        &mut arena,
    );
    let (DeclarationOutcome::Data(circle), DeclarationOutcome::Data(flag)) = (
        outcome_of(&module, SurfaceName::from("Circle")),
        outcome_of(&module, SurfaceName::from("Flag")),
    )
    else {
        panic!("both declarations lower to their signatures");
    };
    let (Maybe::Present(circle), Maybe::Present(flag)) = (module.data(circle), module.data(flag))
    else {
        panic!("each index names a signature");
    };
    let c = |tag: usize| RuleNode::Constructor(ConstructorTag::from(tag));
    let x = RuleNode::Variable(RuleVariable::from(0_u32));
    assert_eq!(
        circle.presentation().rules(),
        [
            PresentedRule::new([c(1), c(2), x].into(), [x].into()),
            PresentedRule::new([c(2), c(1), x].into(), [x].into()),
        ],
        "each cancellation over the constructors' tags, its variable by first occurrence"
    );
    assert!(
        flag.presentation().rules().is_empty(),
        "a family without rules is free"
    );
    let report = judged(&module, &mut arena);
    assert!(
        report
            .judged()
            .iter()
            .all(|judged| judged.verdict() == Verdict::Data),
        "the checker admits both families: {report:?}"
    );
}

#[test]
fn a_recursive_family_names_itself_in_its_fields()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(
            "data Nat : Type { Zero : Nat; Succ : (n : Nat) --> Nat; }\ndata List(a : Type) : Type { Nil : List(a); Cons : (head : a, tail : List(a)) --> List(a); }\ndata Bad : Type { MkBad : (f : +U (Bad -> -F Nat)) --> Bad; }\ndef self_named : Later ;\ndata Later : Type { Now : Later; }\n",
        ),
        &mut arena,
    );
    let (DeclarationOutcome::Data(nat), DeclarationOutcome::Data(list)) = (
        outcome_of(&module, SurfaceName::from("Nat")),
        outcome_of(&module, SurfaceName::from("List")),
    )
    else {
        panic!("both families lower to their signatures");
    };
    let (Maybe::Present(nat), Maybe::Present(list)) = (module.data(nat), module.data(list))
    else {
        panic!("each index names a signature");
    };
    let [ref zero, ref succ] = *nat.constructors()
    else {
        panic!("two constructors");
    };
    assert!(zero.is_empty());
    let [predecessor] = **succ
    else {
        panic!("one field");
    };
    assert_eq!(
        arena.value_type(predecessor),
        Some(&ValueType::Data {
            declaration: ConstantIndex::from(0_usize),
            arguments: Vec::new(),
        }),
        "the successor's field is the family at its own position"
    );
    let [_, ref cons] = *list.constructors()
    else {
        panic!("two constructors");
    };
    let [_, tail] = **cons
    else {
        panic!("two fields");
    };
    let Some(&ValueType::Data {
        declaration,
        ref arguments,
    }) = arena.value_type(tail)
    else {
        panic!("the tail is a nominal type");
    };
    assert_eq!(declaration, ConstantIndex::from(1_usize));
    assert!(
        matches!(
            arguments.as_slice(),
            [argument] if matches!(arena.value(*argument), Some(&Value::Variable { index, .. }) if index == gandr_kernel_term::DeBruijnIndex::from(1_u32))
        ),
        "the tail applies the family to its own parameter, one binder out past the head"
    );
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("self_named")),
            LoweringRefusal::UnresolvedTypeHead { .. }
        ),
        "a later family stays unresolved"
    );
    let report = judged(&module, &mut arena);
    let verdicts: Vec<Verdict> = report
        .judged()
        .iter()
        .map(gandr_core_checker::Judged::verdict)
        .collect();
    assert!(
        matches!(verdicts.as_slice(), [
            Verdict::Data,
            Verdict::Data,
            Verdict::Data,
            Verdict::Data,
        ]),
        "every family forms, the one under its own domain stratified: {verdicts:?}"
    );
}

/// The unary naturals every recursive-function witness recurses over.
const NAT: &str = "data Nat : Type { Zero : Nat; Succ : (n : Nat) --> Nat; }\n";

/// The variable `index` binders out.
///
/// # Specification
/// trivial.
fn variable(index: DeBruijnIndex) -> Value
{
    Value::Variable {
        zone: gandr_core_term::Zone::Intuitionistic,
        index,
    }
}

#[test]
fn a_recursive_function_closes_a_fixpoint_over_its_staged_parameter()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        "{NAT}def rec plus(n : Nat, m : Nat) -> -F Nat {{ case m {{ Zero => return n, Succ(p) => {{ run r <- plus[<](n, p); return Succ(r) }} }} }}\ndef rec idle(n : Nat) -> -F Nat {{ return n }}\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let opened = |name: &'static str| {
        let Some(&Value::Thunk(mut computation)) =
            arena.value(body_named(&module, SurfaceName::from(name)))
        else {
            panic!("`{name}` lowers to a thunk");
        };
        let mut lambdas = Vec::new();
        while let Some(&Computation::Lambda(under)) = arena.computation(computation) {
            lambdas.push(computation);
            computation = under;
        }
        (lambdas.len(), computation)
    };

    let (outside, fixpoint) = opened("plus");
    assert_eq!(
        outside, 1_usize,
        "the leading parameter is bound outside the fixpoint"
    );
    let Some(&Computation::Fixpoint {
        body,
        evidence: FixpointEvidence::StructuralDescent,
    }) = arena.computation(fixpoint)
    else {
        panic!("a claimed call makes the fixpoint claim descent");
    };
    assert_eq!(
        module
            .origins()
            .computation(fixpoint)
            .map(|origin| origin.provenance()),
        Maybe::Present(crate::origin::Provenance::Inserted(
            crate::origin::Insertion::Fixpoint
        )),
        "the fixpoint is the lowering's, not the source's"
    );
    let Some(&Computation::Lambda(cased)) = arena.computation(body)
    else {
        panic!("the fixpoint closes the staged parameter's lambda");
    };
    let Some(&Computation::DataCase {
        scrutinee,
        ref branches,
        ..
    }) = arena.computation(cased)
    else {
        panic!("the body cases on the staged parameter");
    };
    assert_eq!(
        arena.value(scrutinee),
        Some(&variable(DeBruijnIndex::from(0_u32)))
    );
    let [_, successor] = **branches
    else {
        panic!("one branch per constructor");
    };
    let calls: Vec<ComputationId> = reachable(&arena, successor)
        .into_iter()
        .filter(|&at| matches!(arena.computation(at), Some(&Computation::Application(..))))
        .collect();
    let [call] = *calls
    else {
        panic!("one recursive call: {calls:?}");
    };
    let Some(&Computation::Application(head, argument)) = arena.computation(call)
    else {
        panic!("the call is an application");
    };
    assert!(
        matches!(arena.computation(head), Some(&Computation::Force(forced)) if arena.value(forced) == Some(&variable(DeBruijnIndex::from(2_u32)))),
        "the head forces the fixpoint's own binder, past the field and the parameter"
    );
    assert_eq!(
        arena.value(argument),
        Some(&variable(DeBruijnIndex::from(0_u32))),
        "the call applies the field alone, the leading parameter left out"
    );
    let passed = source
        .find("plus[<](n")
        .map(|at| at.saturating_add(8_usize));
    assert!(
        module.origins().labels().iter().any(|label| {
            Some(usize::from(label.span.start())) == passed
                && matches!(label.labelled, crate::origin::Labelled::ValueType { .. })
        }),
        "the leading parameter, passed as itself, answers at its written type"
    );

    let (outside, fixpoint) = opened("idle");
    assert_eq!(outside, 0_usize);
    assert!(
        matches!(
            arena.computation(fixpoint),
            Some(&Computation::Fixpoint {
                evidence: FixpointEvidence::Partial,
                ..
            })
        ),
        "a recursive function claiming nothing is partial"
    );
    assert_accepted(&judged(&module, &mut arena));
}

/// The body of `name` in `module`, opened past the lambdas outside its
/// fixpoint: how many there are, and the fixpoint.
///
/// # Specification
/// trivial.
fn fixpoint_of(
    arena: &CoreArena,
    module: &LoweredModule<'_>,
    name: SurfaceName<'_>,
) -> (ParameterAt, ComputationId)
{
    let Some(&Value::Thunk(mut computation)) = arena.value(body_named(module, name))
    else {
        panic!("`{name:?}` lowers to a thunk");
    };
    let mut outside = ParameterAt(0);
    while let Some(&Computation::Lambda(under)) = arena.computation(computation) {
        outside = ParameterAt(outside.0.saturating_add(1));
        computation = under;
    }
    (outside, computation)
}

#[test]
fn a_parameterless_recursive_tail_binds_its_own_name_1499()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        "{NAT}codata Ones : Type[-] {{ head : Integer; tail : Ones; }}\n\
         def rec constant() -> -F Nat {{ return Zero }}\n\
         def rec ones() -> Ones {{ &{{ .head => 1, .tail => ones[>]() }} }}\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    for name in ["constant", "ones"].map(SurfaceName::from) {
        let (outside, fixpoint) = fixpoint_of(&arena, &module, name);
        assert_eq!(
            outside,
            ParameterAt(0),
            "`{name:?}` binds no lambda outside its fixpoint"
        );
        let Some(&Computation::Fixpoint {
            body,
            evidence: FixpointEvidence::Partial,
        }) = arena.computation(fixpoint)
        else {
            panic!(
                "`{name:?}` closes a partial fixpoint: {:?}",
                arena.computation(fixpoint)
            );
        };
        assert!(
            !matches!(arena.computation(body), Some(&Computation::Lambda(_))),
            "`{name:?}`'s fixpoint stands over its body, with no parameter's lambda"
        );
    }
    assert_accepted(&judged(&module, &mut arena));
}

#[test]
fn a_definition_descends_on_the_parameter_its_cases_scrutinise()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        "{NAT}def rec plus(m : Nat, n : Nat) -> -F Nat {{ case m {{ Zero => return n, Succ(p) => plus[<](p, Succ(n)) }} }}\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let (outside, fixpoint) = fixpoint_of(&arena, &module, SurfaceName::from("plus"));
    assert_eq!(
        outside,
        ParameterAt(0),
        "the scrutinised first parameter leaves none outside the fixpoint"
    );
    let Some(&Computation::Fixpoint {
        body,
        evidence: FixpointEvidence::StructuralDescent,
    }) = arena.computation(fixpoint)
    else {
        panic!("the fixpoint stages its first binder");
    };
    let Some(&Computation::Lambda(later)) = arena.computation(body)
    else {
        panic!("the fixpoint closes the scrutinised parameter's lambda");
    };
    let Some(&Computation::Lambda(cased)) = arena.computation(later)
    else {
        panic!("the accumulator's lambda stands under it");
    };
    let Some(&Computation::DataCase {
        scrutinee,
        ref branches,
        ..
    }) = arena.computation(cased)
    else {
        panic!("the body cases on the first parameter");
    };
    assert_eq!(
        arena.value(scrutinee),
        Some(&variable(DeBruijnIndex::from(1_u32))),
        "past the accumulator"
    );
    let [_, successor] = **branches
    else {
        panic!("one branch per constructor");
    };
    let calls: Vec<ComputationId> = reachable(&arena, successor)
        .into_iter()
        .filter(|&at| {
            matches!(arena.computation(at), Some(&Computation::Application(head, _)) if matches!(arena.computation(head), Some(Computation::Application(..))))
        })
        .collect();
    let [call] = *calls
    else {
        panic!("one recursive call over two arguments: {calls:?}");
    };
    let Some(&Computation::Application(inner, accumulated)) = arena.computation(call)
    else {
        panic!("the call applies the accumulator last");
    };
    let Some(&Computation::Application(head, field)) = arena.computation(inner)
    else {
        panic!("and the field first");
    };
    assert!(
        matches!(arena.computation(head), Some(&Computation::Force(forced)) if arena.value(forced) == Some(&variable(DeBruijnIndex::from(3_u32)))),
        "the head forces the fixpoint's binder, past the field and both parameters"
    );
    assert_eq!(
        arena.value(field),
        Some(&variable(DeBruijnIndex::from(0_u32)))
    );
    assert!(
        matches!(arena.value(accumulated), Some(Value::Constructor { fields, .. }) if fields.as_slice().len() == 1),
        "the accumulator varies: {:?}",
        arena.value(accumulated)
    );
    assert_accepted(&judged(&module, &mut arena));
}

/// A sum whose recursive calls grow its first parameter while they take its
/// second apart: the first is a leading binder of the fixpoint, which stages
/// its second binder, and each call applies the self binder to both arguments
/// (#626).
#[test]
fn a_varying_parameter_before_the_staged_one_is_a_leading_binder_626()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        "{NAT}def rec count(acc : Nat, b : Nat) -> -F Nat {{ case b {{ Zero => return acc, Succ(p) => count[<](Succ(acc), p) }} }}\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let (outside, fixpoint) = fixpoint_of(&arena, &module, SurfaceName::from("count"));
    assert_eq!(
        outside,
        ParameterAt(0),
        "the accumulator varies, so nothing stands outside the fixpoint"
    );
    let Some(&Computation::Fixpoint {
        body,
        evidence: FixpointEvidence::Staged { position },
    }) = arena.computation(fixpoint)
    else {
        panic!(
            "the fixpoint stages a later binder: {:?}",
            arena.computation(fixpoint)
        );
    };
    assert_eq!(
        usize::from(position),
        1_usize,
        "the second binder is staged"
    );
    let Some(&Computation::Lambda(staged)) = arena.computation(body)
    else {
        panic!("the accumulator's lambda opens the body");
    };
    let Some(&Computation::Lambda(cased)) = arena.computation(staged)
    else {
        panic!("the staged parameter's lambda stands under it");
    };
    let Some(&Computation::DataCase {
        scrutinee,
        ref branches,
        ..
    }) = arena.computation(cased)
    else {
        panic!("the body cases on the staged parameter");
    };
    assert_eq!(
        arena.value(scrutinee),
        Some(&variable(DeBruijnIndex::from(0_u32))),
        "the innermost binder"
    );
    let [_, successor] = **branches
    else {
        panic!("one branch per constructor");
    };
    let calls: Vec<ComputationId> = reachable(&arena, successor)
        .into_iter()
        .filter(|&at| {
            matches!(arena.computation(at), Some(&Computation::Application(head, _)) if matches!(arena.computation(head), Some(Computation::Application(..))))
        })
        .collect();
    let [call] = *calls
    else {
        panic!("one recursive call over two arguments: {calls:?}");
    };
    let Some(&Computation::Application(inner, field)) = arena.computation(call)
    else {
        panic!("the call applies the field last");
    };
    let Some(&Computation::Application(head, accumulated)) = arena.computation(inner)
    else {
        panic!("and the grown accumulator first");
    };
    assert!(
        matches!(arena.computation(head), Some(&Computation::Force(forced)) if arena.value(forced) == Some(&variable(DeBruijnIndex::from(3_u32)))),
        "the head forces the fixpoint's binder, past the field and both parameters"
    );
    assert_eq!(
        arena.value(field),
        Some(&variable(DeBruijnIndex::from(0_u32)))
    );
    assert!(
        matches!(arena.value(accumulated), Some(Value::Constructor { fields, .. }) if fields.as_slice().len() == 1),
        "the accumulator grows: {:?}",
        arena.value(accumulated)
    );
    assert_accepted(&judged(&module, &mut arena));
}

#[test]
fn a_rebuilt_argument_descends_on_the_same_position()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        "{NAT}def rec halve(n : Nat) -> -F Nat {{ case n {{ Zero => return Zero, Succ(m) => case m {{ Zero => return Zero, Succ(q) => {{ run h <- halve[<](Succ(q)); return Succ(h) }} }} }} }}\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let (outside, fixpoint) = fixpoint_of(&arena, &module, SurfaceName::from("halve"));
    assert_eq!(outside, ParameterAt(0));
    assert!(
        matches!(
            arena.computation(fixpoint),
            Some(&Computation::Fixpoint {
                evidence: FixpointEvidence::StructuralDescent,
                ..
            })
        ),
        "a match on the parameter's field keeps the parameter's position"
    );
    assert_accepted(&judged(&module, &mut arena));
}

#[test]
fn claims_under_cases_on_two_parameters_are_refused_by_name()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        "{NAT}def rec both(m : Nat, n : Nat) -> -F Nat {{ case m {{ Zero => case n {{ Zero => return Zero, Succ(q) => both[<](m, q) }}, Succ(p) => both[<](p, n) }} }}\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let start = source.rfind("both[<]").unwrap_or_default();
    assert_eq!(
        refusal_of(&module, SurfaceName::from("both")),
        LoweringRefusal::DescentOnSeveralParameters {
            span: crate::fixture::span(
                gandr_surface_syntax::ByteOffset::from(start),
                gandr_surface_syntax::ByteOffset::from(start.saturating_add(7_usize)),
            ),
            staged: SurfaceName::from("n"),
            claimed: SurfaceName::from("m"),
        },
        "the first claim stages `n`; the second, under the match on `m`, names both"
    );
}

#[test]
fn an_unapplied_claim_lowers_to_the_self_binder()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        "{NAT}def rec loose(n : Nat) -> -F Nat {{ run held <- pure loose[<]; return n }}\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let (outside, fixpoint) = fixpoint_of(&arena, &module, SurfaceName::from("loose"));
    assert_eq!(outside, ParameterAt(0));
    let Some(&Computation::Fixpoint {
        body,
        evidence: FixpointEvidence::StructuralDescent,
    }) = arena.computation(fixpoint)
    else {
        panic!("the claim makes the fixpoint claim descent");
    };
    let returned: Vec<ValueId> = reachable(&arena, body)
        .into_iter()
        .filter_map(|at| match arena.computation(at) {
            Some(&Computation::Return(value)) => Some(value),
            _ => None,
        })
        .collect();
    assert!(
        returned
            .iter()
            .any(|&value| arena.value(value) == Some(&variable(DeBruijnIndex::from(1_u32)))),
        "`pure loose[<]` returns the fixpoint's binder, past the parameter: {returned:?}"
    );
}

#[test]
fn a_definition_without_a_case_on_a_parameter_stages_its_last()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        "{NAT}def rec count(n : Nat, m : Nat) -> -F Nat {{ run k <- pure m; case k {{ Zero => return n, Succ(p) => count[<](n, p) }} }}\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let (outside, fixpoint) = fixpoint_of(&arena, &module, SurfaceName::from("count"));
    assert_eq!(
        outside,
        ParameterAt(1),
        "a match on no parameter stages the last; the first stays outside"
    );
    assert!(matches!(
        arena.computation(fixpoint),
        Some(&Computation::Fixpoint {
            evidence: FixpointEvidence::StructuralDescent,
            ..
        })
    ));
}

/// A rose tree's node and forest, one block, measured by two functions that
/// call each other: each member is one fixpoint over the sum of both domains,
/// read at its own summand, and a call through a sibling injects its argument
/// at the sibling's.
#[test]
fn a_mutual_blocks_recursive_functions_share_one_fixpoint()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        "{NAT}rec {{\n  data Rose : Type {{ Node : (kids : Forest) --> Rose; }}\n  data Forest : Type {{ Empty : Forest; More : (head : Rose, tail : Forest) --> Forest; }}\n  def rec size(t : Rose) -> -F Nat {{ case t {{ Node(kids) => {{ run s <- sizes[<](kids); return Succ(s) }} }} }}\n  def rec sizes(ts : Forest) -> -F Nat {{ case ts {{ Empty => return Zero, More(t, rest) => {{ run a <- size[<](t); sizes[<](rest) }} }} }}\n}}\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    // The joint a member applies, and the summand it injects its parameter at.
    let joint = |name: &'static str| {
        let Some(&Value::Thunk(lambda)) = arena.value(body_named(&module, SurfaceName::from(name)))
        else {
            panic!("`{name}` lowers to a thunk");
        };
        let Some(&Computation::Lambda(applied)) = arena.computation(lambda)
        else {
            panic!("`{name}` binds its parameter");
        };
        let Some(&Computation::Application(joint, injected)) = arena.computation(applied)
        else {
            panic!("`{name}` applies the joint");
        };
        let Some(&Value::Injection(summand, own)) = arena.value(injected)
        else {
            panic!("`{name}` injects its parameter");
        };
        assert_eq!(
            arena.value(own),
            Some(&variable(DeBruijnIndex::from(0_u32)))
        );
        (joint, usize::from(summand))
    };
    let (sized, at) = joint("size");
    assert_eq!(at, 0_usize, "the node's measure is the first summand");
    let (forested, at) = joint("sizes");
    assert_eq!(
        (forested, at),
        (sized, 1_usize),
        "the forest's measure is the same joint at the second"
    );
    let Some(&Computation::Ascribe { body: fixpoint, ty }) = arena.computation(sized)
    else {
        panic!("the joint is ascribed its type");
    };
    let Some(&gandr_core_term::CompType::Arrow { domain, .. }) = arena.comp_type(ty)
    else {
        panic!("the joint is a function");
    };
    assert!(
        matches!(arena.value_type(domain), Some(ValueType::Sum(summands)) if summands.len() == 2),
        "over the sum of both domains"
    );
    let Some(&Computation::Fixpoint {
        body,
        evidence: FixpointEvidence::StructuralDescent,
    }) = arena.computation(fixpoint)
    else {
        panic!("one fixpoint claims descent");
    };
    let Some(&Computation::Lambda(cased)) = arena.computation(body)
    else {
        panic!("the fixpoint closes the sum's lambda");
    };
    let Some(&Computation::Case { ref branches, .. }) = arena.computation(cased)
    else {
        panic!("the joint cases on the summand");
    };
    let [node, _] = **branches
    else {
        panic!("one branch per member");
    };
    // The node's measure calls the forest's: the self binder, past the
    // field, the summand the case bound and the sum's parameter, applied to
    // the field injected at the forest's summand.
    let calls: Vec<ComputationId> = reachable(&arena, node)
        .into_iter()
        .filter(|&at| matches!(arena.computation(at), Some(&Computation::Application(..))))
        .collect();
    let [call] = *calls
    else {
        panic!("one sibling call: {calls:?}");
    };
    let Some(&Computation::Application(head, argument)) = arena.computation(call)
    else {
        panic!("the call is an application");
    };
    assert!(
        matches!(arena.computation(head), Some(&Computation::Force(forced)) if arena.value(forced) == Some(&variable(DeBruijnIndex::from(3_u32)))),
        "the head forces the joint's own binder"
    );
    assert!(
        matches!(arena.value(argument), Some(&Value::Injection(summand, field)) if usize::from(summand) == 1 && arena.value(field) == Some(&variable(DeBruijnIndex::from(0_u32)))),
        "the field is injected at the forest's summand"
    );
    assert_accepted(&judged(&module, &mut arena));
}

#[test]
fn a_decoders_descent_in_its_returned_type_unquotes_the_fixpoint()
{
    let mut arena = CoreArena::new();
    let source = "rec {\n  data U : Type { NatC : U; PiC : (a : U, b : +U (el(a) -> -F U)) --> U; }\n  def rec el(u : U) -> -F Type { case u { NatC => return Integer, PiC(a, b) => return (+U ((x : el[<](a)) -> -F Integer)) } }\n}\n";
    let module = lowered(SourceText::from(source), &mut arena);
    let Some(&Value::Thunk(fixpoint)) = arena.value(body_named(&module, SurfaceName::from("el")))
    else {
        panic!("the decoder lowers to a thunk");
    };
    let Some(&Computation::Fixpoint { body, .. }) = arena.computation(fixpoint)
    else {
        panic!("the thunk closes the decoder's fixpoint");
    };
    let Some(&Computation::Lambda(cased)) = arena.computation(body)
    else {
        panic!("the fixpoint closes the decoded code's lambda");
    };
    let Some(&Computation::DataCase { ref branches, .. }) = arena.computation(cased)
    else {
        panic!("the decoder cases on its code");
    };
    let [_, pi] = **branches
    else {
        panic!("one branch per constructor");
    };
    let returned: Vec<ValueId> = reachable(&arena, pi)
        .into_iter()
        .filter_map(|at| match arena.computation(at) {
            Some(&Computation::Return(value)) => Some(value),
            _ => None,
        })
        .collect();
    let [code] = *returned
    else {
        panic!("the arm returns one code: {returned:?}");
    };
    let Some(&Value::Quote(quoted)) = arena.value(code)
    else {
        panic!("the arm returns a quoted type: {:?}", arena.value(code));
    };
    let Some(&ValueType::Thunk(arrow)) = arena.value_type(quoted)
    else {
        panic!("the quoted type is a thunk");
    };
    // The codomain names no `x`: a plain arrow.
    let Some(&gandr_core_term::CompType::Arrow { domain, .. }) = arena.comp_type(arrow)
    else {
        panic!("of an arrow: {:?}", arena.comp_type(arrow));
    };
    let Some(&ValueType::Element { code: decoded, .. }) = arena.value_type(domain)
    else {
        panic!("whose domain decodes: {:?}", arena.value_type(domain));
    };
    let Some(&Value::Returned(call)) = arena.value(decoded)
    else {
        panic!("what the descent returns");
    };
    let Some(&Computation::Application(forced, argument)) = arena.computation(call)
    else {
        panic!("the descent is an application");
    };
    assert!(
        matches!(arena.computation(forced), Some(&Computation::Force(head)) if arena.value(head) == Some(&variable(DeBruijnIndex::from(3_u32)))),
        "the head forces the fixpoint's own binder, past the two fields and the code"
    );
    assert_eq!(
        arena.value(argument),
        Some(&variable(DeBruijnIndex::from(1_u32))),
        "the descent applies the field it names"
    );
}

#[test]
fn an_unmarked_self_reference_is_refused_with_its_claim()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        "{NAT}def rec bare(n : Nat) -> -F Nat {{ case n {{ Zero => return n, Succ(p) => become bare(p) }} }}\ndef rec shadow(shadow : Nat) -> -F Nat {{ return shadow }}\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let Some(start) = source.find("bare(p)")
    else {
        panic!("the fixture writes the call");
    };
    let Some(end) = start.checked_add(4_usize)
    else {
        panic!("the span fits");
    };

    assert_eq!(
        refusal_of(&module, SurfaceName::from("bare")),
        LoweringRefusal::UnmarkedSelfReference {
            span: crate::fixture::span(
                gandr_surface_syntax::ByteOffset::from(start),
                gandr_surface_syntax::ByteOffset::from(end)
            ),
            name: SurfaceName::from("bare"),
        }
    );
    assert!(
        matches!(
            outcome_of(&module, SurfaceName::from("shadow")),
            DeclarationOutcome::Completed { .. }
        ),
        "a parameter of the function's own name shadows it"
    );
}

/// A kept parameter is passed as itself: a name that spells it but resolves to
/// an arm's binder varies it, and is refused. A parameter every call changes
/// is no kept one: it is a leading binder of the fixpoint (#626).
#[test]
fn a_recursive_call_passes_its_leading_parameters_unchanged()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        "{NAT}def rec varied(n : Nat, m : Nat) -> -F Nat {{ case m {{ Zero => return n, Succ(p) => become varied[<](p, p) }} }}\ndef rec shadowed(n : Nat, m : Nat) -> -F Nat {{ case m {{ Zero => return n, Succ(n) => become shadowed[<](n, n) }} }}\ndef rec short(n : Nat, m : Nat) -> -F Nat {{ case m {{ Zero => return n, Succ(p) => become short[<](p) }} }}\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let at = |text: &str, length: usize| {
        let start = source.find(text).unwrap_or_default();
        crate::fixture::span(
            gandr_surface_syntax::ByteOffset::from(start),
            gandr_surface_syntax::ByteOffset::from(start.saturating_add(length)),
        )
    };

    let (outside, fixpoint) = fixpoint_of(&arena, &module, SurfaceName::from("varied"));
    assert_eq!(outside, ParameterAt(0), "a varied parameter is not kept");
    assert!(
        matches!(
            arena.computation(fixpoint),
            Some(&Computation::Fixpoint {
                evidence: FixpointEvidence::Staged { position },
                ..
            }) if usize::from(position) == 1_usize
        ),
        "the fixpoint stages its second binder past the varied one"
    );
    assert_eq!(
        refusal_of(&module, SurfaceName::from("shadowed")),
        LoweringRefusal::OutOfFragment {
            span: at("n, n)", 1_usize),
            form: FormName::from(gandr_surface_grammar::NamedKind("call_expression")),
            sort: FragmentSort::Computation,
            boundary: FragmentBoundary::NonUniform,
        },
        "a kept parameter's spelling naming the arm's binder varies it"
    );
    assert_eq!(
        refusal_of(&module, SurfaceName::from("short")),
        LoweringRefusal::OutOfFragment {
            span: at("short[<](p)", 11_usize),
            form: FormName::from(gandr_surface_grammar::NamedKind("call_expression")),
            sort: FragmentSort::Computation,
            boundary: FragmentBoundary::Arity(OperandCount::from(1_usize)),
        },
        "a recursive call passes one argument per parameter"
    );
}

#[test]
fn a_productive_call_is_the_whole_arm_of_a_copattern_block()
{
    let mut arena = CoreArena::new();
    let stream = "codata Stream(a : Type) : Type[-] { head : a; tail : Stream(a); }\n";
    let source = alloc::format!(
        "{NAT}{stream}def rec upward(n : Nat, m : Nat) -> Stream(Nat) {{ &{{.head => return n, .tail => upward[>](m, Succ(n))}} }}\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let (outside, fixpoint) = fixpoint_of(&arena, &module, SurfaceName::from("upward"));

    assert_eq!(
        outside,
        ParameterAt(0),
        "a productive call varies every parameter"
    );
    assert!(
        matches!(
            arena.computation(fixpoint),
            Some(&Computation::Fixpoint {
                evidence: FixpointEvidence::Partial,
                ..
            })
        ),
        "a productive call claims nothing of termination"
    );
    assert_accepted(&judged(&module, &mut arena));

    let mut arena = CoreArena::new();
    let source = alloc::format!(
        "{NAT}{stream}def rec ahead(n : Nat) -> -F Nat {{ case n {{ Zero => return n, Succ(p) => become ahead[>](p) }} }}\ndef rec wrapped(n : Nat) -> Stream(Nat) {{ &{{.head => return n, .tail => become wrapped[>](n)}} }}\ndef rec both(n : Nat) -> -F Nat {{ case n {{ Zero => return n, Succ(p) => become both[<, >](p) }} }}\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let unguarded = |name: &'static str| {
        matches!(
            refusal_of(&module, SurfaceName::from(name)),
            LoweringRefusal::UnguardedCorecursion { name: called, .. } if called == SurfaceName::from(name)
        )
    };

    assert!(
        unguarded("ahead"),
        "a productive call outside a copattern block is unguarded: {:?}",
        refusal_of(&module, SurfaceName::from("ahead"))
    );
    assert!(
        unguarded("wrapped"),
        "and so is one under a `become` inside an arm: {:?}",
        refusal_of(&module, SurfaceName::from("wrapped"))
    );
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("both")),
            LoweringRefusal::OutOfFragment {
                form,
                boundary: FragmentBoundary::Reserved(crate::Unbuilt::RecursiveClaim),
                ..
            }
                if form == FormName::INSTANTIATION
        ),
        "combined claims are reserved"
    );
}

#[test]
fn a_descent_claim_names_its_own_function_873()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        "{NAT}def other(n : Nat) -> -F Nat {{ return n }}\ndef rec borrowed(n : Nat) -> -F Nat {{ case n {{ Zero => return n, Succ(p) => become other[<](p) }} }}\ndef rec primed(n : Nat) -> -F Nat {{ case n {{ Zero => return n, Succ(p) => become add[<](p) }} }}\ndef rec stray(n : Nat) -> -F Nat {{ case n {{ Zero => return n, Succ(p) => become nowhere[<](p) }} }}\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let at = |text: &str| {
        let start = source.find(text).unwrap_or_default();
        crate::fixture::span(
            gandr_surface_syntax::ByteOffset::from(start),
            gandr_surface_syntax::ByteOffset::from(start.saturating_add(text.len())),
        )
    };
    let foreign = |claim: &str| LoweringRefusal::OutOfFragment {
        span: at(claim),
        form: FormName::INSTANTIATION,
        sort: FragmentSort::Computation,
        boundary: FragmentBoundary::ForeignClaim,
    };

    assert_eq!(
        refusal_of(&module, SurfaceName::from("borrowed")),
        foreign("other[<]"),
        "a claim on an earlier declaration names the function it is not"
    );
    assert_eq!(
        refusal_of(&module, SurfaceName::from("primed")),
        foreign("add[<]"),
        "and so does a claim on a builtin"
    );
    assert_eq!(
        refusal_of(&module, SurfaceName::from("stray")),
        LoweringRefusal::UnresolvedName {
            span: at("nowhere"),
            name: SurfaceName::from("nowhere"),
        },
        "a claim's head that names nothing is unresolved before it is anything else"
    );
}

#[test]
fn a_data_family_named_where_a_value_is_read_is_quoted()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        "{NAT}{MAYBE}def code : Type ;\ndef code = Nat ;\ndef partial : Type ;\ndef partial = Maybe ;\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let Some(&Value::Quote(quoted)) = arena.value(body_named(&module, SurfaceName::from("code")))
    else {
        panic!("the family is quoted");
    };

    assert_eq!(
        arena.value_type(quoted),
        Some(&ValueType::Data {
            declaration: ConstantIndex::from(0_usize),
            arguments: Vec::new(),
        }),
        "the code is the family's own type"
    );
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("partial")),
            LoweringRefusal::OutOfFragment {
                boundary: FragmentBoundary::Arity(count),
                ..
            } if count == OperandCount::from(0_usize)
        ),
        "a family of parameters named alone is applied to none"
    );
    assert_accepted(&judged(&module, &mut arena));
}

/// Each family applied to an index is declined, and keeps its own form's key,
/// the form that carries its refusal (#1204).
#[test]
fn an_indexed_generator_is_declined()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(
            "data Vec(n : Integer) : Type { Nil : Vec(0); }\ndata Bad(a : Type) : Type { Mk : Bad(Integer); }\ndata Two(a : Type, b : Type) : Type { Mk2 : Two(b, a); }\ndata Ext(a : Type) : Type { Mk3 : Ext(a, a); }\n",
        ),
        &mut arena,
    );
    for name in ["Vec", "Bad", "Two", "Ext"].map(SurfaceName::from) {
        assert!(
            matches!(refusal_of(&module, name), LoweringRefusal::OutOfFragment {
                form: FormName::DATA_GENERATOR,
                sort: FragmentSort::Declaration,
                boundary: FragmentBoundary::Indexed,
                ..
            }),
            "`{name}` is declined as indexed"
        );
        assert!(
            module
                .declarations()
                .iter()
                .any(|declaration| declaration.name() == name
                    && matches!(declaration.signature(), Maybe::Present(_))),
            "`{name}` keeps its form's key"
        );
    }
}

#[test]
fn an_indexed_family_lowers_its_indices()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(
            "data Nat : Type { Z : Nat; S : (n : Nat) --> Nat; }\ndata Vec(a : Type) : Nat -> Type { Nil : Vec(a, Z); Cons : (n : Nat, x : a, xs : Vec(a, n)) --> Vec(a, S(n)); }\ndef one() -> -F Vec(Integer, S(Z)) { return Cons(Z, 3, (Nil : Vec(Integer, Z))) }\ndef two() -> -F Vec(Integer, S(S(Z))) { return Cons(Z, 3, (Nil : Vec(Integer, Z))) }\ndata Pt : Nat -> Type { P : Pt(Z); loop : P <-> P; }\n",
        ),
        &mut arena,
    );
    let DeclarationOutcome::Data(vector) = outcome_of(&module, SurfaceName::from("Vec"))
    else {
        panic!("the family lowers to its signature");
    };
    let Maybe::Present(vector) = module.data(vector)
    else {
        panic!("the index names a signature");
    };
    assert_eq!(vector.parameters().len(), 1_usize);
    assert_eq!(
        vector.indices().len(),
        1_usize,
        "`Nat -> Type` reads one index"
    );
    let [ref empty, ref consed] = *vector.results()
    else {
        panic!("one stated length per constructor");
    };
    let (&[zero], &[successor]) = (&**empty, &**consed)
    else {
        panic!("each constructor states its one index");
    };
    assert!(
        matches!(arena.value(zero), Some(&Value::Constructor { tag, ref fields, .. })
            if tag == ConstructorTag::from(0_usize) && fields.is_empty()),
        "`Nil` stands at `Z`"
    );
    let Some(&Value::Constructor {
        tag, ref fields, ..
    }) = arena.value(successor)
    else {
        panic!("`Cons` stands at a successor");
    };
    assert_eq!(tag, ConstructorTag::from(1_usize));
    let [length] = **fields
    else {
        panic!("`S` takes one field");
    };
    assert_eq!(
        arena.value(length),
        Some(&variable(DeBruijnIndex::from(2_u32))),
        "`Cons` stands at the successor of its first field, under its three"
    );
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("Pt")),
            LoweringRefusal::OutOfFragment {
                form: FormName::CELL_MEMBER,
                boundary: FragmentBoundary::Indexed,
                ..
            }
        ),
        "an indexed family presents no cell"
    );
    let report = judged(&module, &mut arena);
    let verdicts: Vec<Verdict> = report
        .judged()
        .iter()
        .map(gandr_core_checker::Judged::verdict)
        .collect();
    let [
        Verdict::Data,
        Verdict::Data,
        Verdict::Checked { .. },
        Verdict::Refused(ref stated),
    ] = *verdicts
    else {
        panic!("the family and the vector at its length check: {report:?}");
    };
    assert!(
        matches!(stated, gandr_core_checker::CheckRefusal::TypeMismatch(_)),
        "a vector one long is no vector two long: {stated:?}"
    );
}

#[test]
fn each_stated_index_is_framed_under_its_family_s_telescope_931()
{
    let source = "data Nat : Type { Z : Nat; S : (n : Nat) --> Nat; }\ndata Vec(a : Type) : Nat -> \
                  Type { Nil : Vec(a, Z); Cons : (n : Nat, x : a, xs : Vec(a, n)) --> Vec(a, \
                  S(n)); }\n";
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source), &mut arena);
    let framed: Vec<(&str, Vec<&str>)> = module
        .origins()
        .framed()
        .iter()
        .map(|&(span, ref names)| {
            (
                source
                    .get(usize::from(span.start()) .. usize::from(span.end()))
                    .unwrap_or(""),
                names.iter().map(String::as_str).collect(),
            )
        })
        .collect();
    assert_eq!(
        framed,
        [
            ("Z", Vec::from(["a"])),
            ("S(n)", Vec::from(["a", "n", "x", "xs"]))
        ],
        "each index is read under the family's parameters, then its constructor's fields"
    );
}

#[test]
fn operation_and_rule_members_are_left_to_the_description_route()
{
    let source = "data NatOp : Type { Zero : NatOp; One : NatOp; oper add(m : NatOp, n : NatOp) -> NatOp; rule add(Zero, n) ==> n; }\ndata NatRetired : Type { Only : NatRetired; op stale(x : NatRetired) -> NatRetired; }\n";
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source), &mut arena);
    let [ref operated, ref retired, ref held] = *module.declarations()
    else {
        panic!("two families and the retired member's refusal");
    };
    for (family, arities) in [(operated, &[0_usize, 0][..]), (retired, &[0][..])] {
        let DeclarationOutcome::Data(index) = family.outcome()
        else {
            panic!("`{}` keeps its native reading", family.name());
        };
        let Maybe::Present(signature) = module.data(index)
        else {
            panic!("`{}` holds its signature", family.name());
        };
        assert_eq!(
            signature
                .constructors()
                .iter()
                .map(Vec::len)
                .collect::<Vec<_>>(),
            arities,
            "`{}` keeps every generator beside its members",
            family.name()
        );
    }
    assert_eq!(held.name(), SurfaceName::from("NatRetired"));
    let DeclarationOutcome::Refused(refusal) = held.outcome()
    else {
        panic!("the retired member is held");
    };
    let Maybe::Present(span) = refusal.span()
    else {
        panic!("the held refusal is located");
    };
    assert_eq!(
        source.get(usize::from(span.start()) .. usize::from(span.end())),
        Some("op stale(x : NatRetired) -> NatRetired")
    );
    assert_eq!(module.cells().diagnostics, []);
    assert_accepted(&judged(&module, &mut arena));
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
fn a_data_family_named_as_a_builtin_type_is_refused_at_its_name()
{
    for (source, name) in [
        ("data Integer : Type { I : Integer; }\n", "Integer"),
        ("data Unit : Type { U : Unit; }\n", "Unit"),
    ] {
        let mut arena = CoreArena::new();
        let module = lowered(SourceText::from(source), &mut arena);
        let start = source.find(name).unwrap();
        assert_eq!(
            refusal_of(&module, SurfaceName::from(name)),
            LoweringRefusal::ShadowedBuiltin {
                span: crate::fixture::span(
                    gandr_surface_syntax::ByteOffset::from(start),
                    gandr_surface_syntax::ByteOffset::from(start.saturating_add(name.len())),
                ),
                name: SurfaceName::from(name),
            },
            "`{name}` is the grammar's own type, not a family to declare"
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
        "{MAYBE}def bare = None;\ndef some = (Some(3) : Maybe(Integer));\ndef none = (None : Maybe(Integer));\ndef three = (Some((3 : Integer)) : Maybe(Integer));\n"
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
            boundary: FragmentBoundary::Unadmitted(crate::Unbuilt::Annotation),
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

/// An unsigned definition whose whole value is an annotation is declared at
/// the annotation's type and checked against it, a value the annotation
/// misstates refused by the checker rather than by the lowering (#1107).
#[test]
fn an_annotated_definition_value_is_signed_by_its_annotation_1107()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        "{MAYBE}def three = (3 : Integer);\ndef some = ((Some(3)) : Maybe(Integer));\ndef grouped = (3);\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let DeclarationOutcome::Completed {
        declared_type,
        body,
    } = outcome_of(&module, SurfaceName::from("three"))
    else {
        panic!(
            "the annotation signs the definition: {:?}",
            outcome_of(&module, SurfaceName::from("three"))
        );
    };
    assert_eq!(
        arena.value_type(declared_type),
        Some(&ValueType::Base(BaseType::Integer))
    );
    assert!(matches!(arena.value(body), Some(&Value::Literal(_))));
    assert!(matches!(
        outcome_of(&module, SurfaceName::from("some")),
        DeclarationOutcome::Completed { .. }
    ));
    assert!(
        matches!(
            outcome_of(&module, SurfaceName::from("grouped")),
            DeclarationOutcome::Bodied { .. }
        ),
        "a grouping is no annotation, and its definition stays unsigned"
    );
    assert_accepted(&judged(&module, &mut arena));

    let mut arena = CoreArena::new();
    let source = alloc::format!("{MAYBE}def wrong = (3 : Maybe(Integer));\n");
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let report = judged(&module, &mut arena);
    assert!(
        report
            .judged()
            .iter()
            .any(|judged| matches!(judged.verdict(), Verdict::Refused(_))),
        "the checker refuses a value its annotation misstates: {report:?}"
    );
}

/// A `return` or a `pure` whose whole operand is an annotation returns the
/// value ascribed the returner of the annotation's type, which checks where
/// a type no signature states is expected; a tail's annotation takes the
/// same ascribed return, so a written `return` leaves the core unchanged
/// (#1107).
#[test]
fn an_annotated_return_is_ascribed_its_returner_1107()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        "{MAYBE}def ran() -> -F Integer {{\n  run n <- pure (3 : Integer);\n  return (n : Integer)\n}}\n\
         def tailed() -> -F Integer {{ (3 : Integer) }}\n\
         def tailed_by_hand() -> -F Integer {{ return (3 : Integer) }}\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let DeclarationOutcome::Completed { body, .. } = outcome_of(&module, SurfaceName::from("ran"))
    else {
        panic!("the function lowers both halves");
    };
    let Some(&Value::Thunk(mut at)) = arena.value(body)
    else {
        panic!("a function's body is thunked");
    };
    let mut ascribed = Vec::new();
    while let Some(&Computation::Bind(bound, rest)) = arena.computation(at) {
        ascribed.push(bound);
        at = rest;
    }
    ascribed.push(at);
    let returners: Vec<_> = ascribed
        .iter()
        .filter_map(|&node| match arena.computation(node) {
            Some(&Computation::Ascribe { body, ty })
                if matches!(arena.computation(body), Some(&Computation::Return(_))) =>
            {
                arena.comp_type(ty).cloned()
            },
            Some(_) | None => None,
        })
        .collect();
    assert_eq!(
        returners.len(),
        2_usize,
        "the bound `pure` and the tail `return` are each ascribed: {returners:?}"
    );
    crate::lower::exits::tests::assert_same_body(
        &module,
        &arena,
        (
            SurfaceName::from("tailed"),
            SurfaceName::from("tailed_by_hand"),
        ),
    );
    assert_accepted(&judged(&module, &mut arena));
}

#[test]
fn a_constructor_takes_its_classifier_from_the_type_it_answers_402()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        "{MAYBE}data Box(m : Maybe(Integer)) : Type {{ Boxed : Box(m); }}\n\
         def tail : +U (-F Maybe(Integer)) ;\ndef tail = thunk {{ Some(3) }} ;\n\
         def alias : () => Maybe(Integer) ;\ndef alias = thunk {{ None }} ;\n\
         def pured : +U (-F Maybe(Integer)) ;\ndef pured = thunk {{ pure Some(5) }} ;\n\
         def returned(n : Integer) -> -F Maybe(Integer) {{ return Some(n) }}\n\
         def nested : Maybe(Maybe(Integer)) ;\ndef nested = Some(None) ;\n\
         def boxed(b : Box(Some(1))) -> -F Integer {{ return 0 }}\n\
         def bare = None ;\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    for name in ["tail", "alias", "pured", "returned", "nested", "boxed"].map(SurfaceName::from) {
        assert!(
            matches!(
                outcome_of(&module, name),
                DeclarationOutcome::Completed { .. }
            ),
            "`{name}` lowers: {:?}",
            outcome_of(&module, name)
        );
    }
    assert!(matches!(
        refusal_of(&module, SurfaceName::from("bare")),
        LoweringRefusal::OutOfFragment {
            boundary: FragmentBoundary::Unannotated,
            ..
        }
    ));
    let Some(&Value::Constructor { ref fields, .. }) =
        arena.value(body_named(&module, SurfaceName::from("nested")))
    else {
        panic!("a signed constructor is a constructor value");
    };
    let Some(&Value::Constructor { datatype, .. }) =
        fields.first().and_then(|&field| arena.value(field))
    else {
        panic!("its parameter-typed field is a constructor value");
    };
    assert!(matches!(
        arena.value_type(datatype),
        Some(&ValueType::Data { declaration, ref arguments })
            if declaration == ConstantIndex::from(0_usize)
                && matches!(arguments.as_slice(), [argument] if matches!(arena.value(*argument), Some(&Value::Quote(quoted)) if arena.value_type(quoted) == Some(&ValueType::Base(gandr_kernel_term::BaseType::Integer))))
    ));
    let report = judged(&module, &mut arena);
    assert_accepted(&report);
}

/// #1833: a constructor written as a call's argument took no classifier from
/// the parameter it is passed to, so `count(Some(3))` was refused as
/// unannotated where `count((Some(3) : Maybe(Integer)))` checked. The
/// parameter's closed type classifies it. A binder's parameter classifies
/// nothing: the argument stays unannotated.
#[test]
fn a_constructor_argument_takes_its_parameter_s_type_1833()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        "{MAYBE}def count(m : Maybe(Integer)) -> -F Integer {{ return 0 }}\n\
         def passed : () => Integer ;\ndef passed = thunk {{ become count(Some(3)) }} ;\n\
         def bare : () => Integer ;\ndef bare = thunk {{ become count(None) }} ;\n\
         def annotated : () => Integer ;\n\
         def annotated = thunk {{ become count((Some(3) : Maybe(Integer))) }} ;\n\
         def local(g : Maybe(Integer) => Integer) -> -F Integer {{ g(None) }}\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    for name in ["passed", "bare", "annotated"].map(SurfaceName::from) {
        assert!(
            matches!(
                outcome_of(&module, name),
                DeclarationOutcome::Completed { .. }
            ),
            "`{name}` lowers: {:?}",
            outcome_of(&module, name)
        );
    }
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("local")),
            LoweringRefusal::OutOfFragment {
                boundary: FragmentBoundary::Unannotated,
                ..
            }
        ),
        "`local`'s argument stays unannotated: {:?}",
        outcome_of(&module, SurfaceName::from("local"))
    );
    assert_accepted(&judged(&module, &mut arena));
}

/// #1876: a constructor written as a call's argument at a parameter whose
/// type names a parameter before it took no classifier, though the arguments
/// before it fix the type: `pick(Integer, None)` was refused as unannotated.
/// The type, each parameter it names replaced by the argument the call writes
/// for it, classifies it — a recursive declaration's own binder standing
/// between them — and the argument is checked against that type.
#[test]
fn a_constructor_argument_reads_the_arguments_before_it_1876()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        "{MAYBE}data List(a : Type) : Type {{ Nil : List(a); Cons : (head : a, tail : List(a)) --> List(a); }}\n\
         def pick(a : Type, m : Maybe(a)) -> -F Integer {{ return 0 }}\n\
         def dependent : () => Integer ;\ndef dependent = thunk {{ become pick(Integer, None) }} ;\n\
         def filled : () => Integer ;\ndef filled = thunk {{ become pick(Integer, Some(3)) }} ;\n\
         def rec size(a : Type, xs : List(a)) -> -F Integer {{\n\
           case xs {{ Nil => 0, Cons(_, rest) => {{ run n <- size[<](a, rest); n + 1 }} }}\n\
         }}\n\
         def one : () => Integer ;\ndef one = thunk {{ become size(Integer, Cons(1, Nil)) }} ;\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    for name in ["dependent", "filled", "one"].map(SurfaceName::from) {
        assert!(
            matches!(
                outcome_of(&module, name),
                DeclarationOutcome::Completed { .. }
            ),
            "`{name}` lowers: {:?}",
            outcome_of(&module, name)
        );
    }
    assert_accepted(&judged(&module, &mut arena));

    let mut arena = CoreArena::new();
    let source = alloc::format!(
        "{MAYBE}def pick(a : Type, m : Maybe(a)) -> -F Integer {{ return 0 }}\n\
         def wrong : () => Integer ;\ndef wrong = thunk {{ become pick(Integer, Some(true)) }} ;\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let report = judged(&module, &mut arena);
    assert!(
        report.judged().iter().any(|judged| !matches!(
            judged.verdict(),
            Verdict::Data | Verdict::Checked { .. } | Verdict::Synthesised { .. }
        )),
        "`Some(true)` is checked at `Maybe(Integer)`: {report:?}"
    );
}

/// #1171: a constructor written in a field typed by another family took no
/// classifier from the field, so `Inline(Some(3))` was refused as
/// unannotated where `Inline((Some(3) : Maybe(Integer)))` checked. The field's
/// declared type, its family's parameters and the fields before it replaced,
/// classifies it.
#[test]
fn a_field_classifies_the_constructor_written_in_it_1171()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        "{MAYBE}data Repr : Type {{ Inline : (s : Maybe(Integer)) --> Repr; }}\n\
         data Box(a : Type) : Type {{ Wrap : (m : Maybe(a)) --> Box(a); }}\n\
         data Dep : Type[+, 1] {{ Dee : (a : Type, m : Maybe(a)) --> Dep; }}\n\
         def closed : Repr ;\ndef closed = Inline(Some(3)) ;\n\
         def annotated : Repr ;\ndef annotated = Inline((Some(3) : Maybe(Integer))) ;\n\
         def opened : Box(Integer) ;\ndef opened = Wrap(Some(3)) ;\n\
         def dependent : Dep ;\ndef dependent = Dee(Integer, Some(3)) ;\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    for name in ["closed", "annotated", "opened", "dependent"].map(SurfaceName::from) {
        let Some(&Value::Constructor { ref fields, .. }) = arena.value(body_named(&module, name))
        else {
            panic!(
                "`{name}` is a constructor value: {:?}",
                outcome_of(&module, name)
            );
        };
        let Some(&Value::Constructor { datatype, .. }) =
            fields.last().and_then(|&field| arena.value(field))
        else {
            panic!("`{name}`'s last field is a constructor value");
        };
        assert!(
            matches!(
                arena.value_type(datatype),
                Some(&ValueType::Data { ref arguments, .. })
                    if matches!(arguments.as_slice(), [argument] if matches!(arena.value(*argument), Some(&Value::Quote(quoted)) if arena.value_type(quoted) == Some(&ValueType::Base(gandr_kernel_term::BaseType::Integer))))
            ),
            "`{name}`'s field is classified `Maybe(Integer)`: {:?}",
            arena.value_type(datatype)
        );
    }
    assert_eq!(
        gandr_core_term::equal_certificate_syntax(
            &arena,
            body_named(&module, SurfaceName::from("closed")),
            body_named(&module, SurfaceName::from("annotated")),
        ),
        gandr_core_term::CertificateEquality::Equal,
        "the field classifies its constructor as the annotation does"
    );
    assert_accepted(&judged(&module, &mut arena));
}

#[test]
fn a_listed_constructor_takes_the_element_type_1544()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        "{MAYBE}def annotated = ([Some(3), None] : List(Maybe(Integer))) ;\n\
         def signed : List(Maybe(Integer)) ;\ndef signed = [Some(3), None] ;\n\
         def nested = ([[Some(3)], [], [None]] : List(List(Maybe(Integer)))) ;\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let integer = |argument| matches!(arena.value(argument), Some(&Value::Quote(quoted)) if arena.value_type(quoted) == Some(&ValueType::Base(gandr_kernel_term::BaseType::Integer)));
    for name in ["annotated", "signed", "nested"].map(SurfaceName::from) {
        let mut pending = Vec::from([body_named(&module, name)]);
        let mut constructed = 0_usize;
        while let Some(id) = pending.pop() {
            match arena.value(id) {
                Some(&Value::ListCons(head, tail)) => pending.extend([tail, head]),
                Some(&Value::ListNil) => {},
                Some(&Value::Constructor { datatype, .. }) => {
                    assert!(
                        matches!(
                            arena.value_type(datatype),
                            Some(&ValueType::Data { ref arguments, .. })
                                if matches!(arguments.as_slice(), [argument] if integer(*argument))
                        ),
                        "`{name}`'s element is classified `Maybe(Integer)`: {:?}",
                        arena.value_type(datatype)
                    );
                    constructed = constructed.saturating_add(1_usize);
                },
                other => panic!("`{name}` holds lists and constructors only: {other:?}"),
            }
        }
        assert_eq!(
            constructed,
            2_usize,
            "each of `{name}`'s constructors is minted: {:?}",
            outcome_of(&module, name)
        );
    }
    assert_accepted(&judged(&module, &mut arena));
}

/// #1602: a list ending a body gave its elements nothing of the type the body
/// answers, so a constructor of a family with parameters among them was
/// refused as unannotated. The answer's element type, read under the answer's
/// frame, classifies each, a nested list's included.
#[test]
fn a_listed_constructor_takes_the_answered_element_type_1602()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        "{MAYBE}def returned(n : Integer) -> -F List(Maybe(Integer)) {{ [Some(n), None] }}\n\
         def alias : () => List(Maybe(Integer)) ;\ndef alias = thunk {{ [None, Some(2)] }} ;\n\
         def nested() -> -F List(List(Maybe(Integer))) {{ [[Some(3)], [None]] }}\n\
         def polymorphic(a : Type, x : a) -> -F List(Maybe(a)) {{ [Some(x), None] }}\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    for name in ["returned", "alias", "nested", "polymorphic"].map(SurfaceName::from) {
        assert!(
            matches!(
                outcome_of(&module, name),
                DeclarationOutcome::Completed { .. }
            ),
            "`{name}` lowers: {:?}",
            outcome_of(&module, name)
        );
    }
    assert_accepted(&judged(&module, &mut arena));
}

/// #1877: a tuple gave its members nothing of the product it is written at, so
/// a constructor of a family with parameters among them was refused as
/// unannotated. Each member takes the product's component at its place, the
/// product written, answered or a list's element type.
#[test]
fn a_tuple_gives_its_members_the_product_s_components_1877()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        "{MAYBE}def annotated = ((Some(1), None) : Maybe(Integer) * Maybe(Integer)) ;\n\
         def returned(n : Integer) -> -F (Maybe(Integer) * Maybe(Integer)) {{ (None, Some(n)) }}\n\
         def listed() -> -F List(Maybe(Integer) * Maybe(Integer)) {{ [(Some(1), None)] }}\n\
         def nested = ((Some(1), (None, Some(2))) : Maybe(Integer) * (Maybe(Integer) * Maybe(Integer))) ;\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    for name in ["annotated", "returned", "listed", "nested"].map(SurfaceName::from) {
        assert!(
            matches!(
                outcome_of(&module, name),
                DeclarationOutcome::Completed { .. }
            ),
            "`{name}` lowers: {:?}",
            outcome_of(&module, name)
        );
    }
    assert_accepted(&judged(&module, &mut arena));
}

#[test]
fn a_constructor_takes_its_slot_as_a_family_argument_421()
{
    let families = "data SumOb(a : Type, b : Type) : Type { Inl : (x : a) --> SumOb(a, b); Inr : (y : b) --> SumOb(a, b); }\ndata Tagged(l : Type, r : Type, s : SumOb(l, r)) : Type { Tag : (n : Integer) --> Tagged(l, r, s); }\n";
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        "{COLOR}{families}def tagged = (Tag(1) : Tagged(Color, Integer, Inl(Red)));\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let Some(&Value::Constructor { datatype, .. }) =
        arena.value(body_named(&module, SurfaceName::from("tagged")))
    else {
        panic!("the annotated tag is a constructor value");
    };
    let Some(&ValueType::Data { ref arguments, .. }) = arena.value_type(datatype)
    else {
        panic!("its classifier is the annotation's family");
    };
    let Some(&Value::Constructor {
        datatype: summand, ..
    }) = arguments
        .get(2_usize)
        .and_then(|&argument| arena.value(argument))
    else {
        panic!("the family's third argument is a constructor value: {arguments:?}");
    };
    assert!(matches!(
        arena.value_type(summand),
        Some(&ValueType::Data { declaration, ref arguments })
            if declaration == ConstantIndex::from(1_usize) && arguments.len() == 2_usize
    ));
    let report = judged(&module, &mut arena);
    assert_accepted(&report);
    // The place's type is `SumOb(Color, Integer)`, so the right summand of a
    // colour is refused: read in the other order, it would be accepted.
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        "{COLOR}{families}def misplaced = (Tag(1) : Tagged(Color, Integer, Inr(Red)));\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let report = judged(&module, &mut arena);
    assert!(
        report
            .judged()
            .iter()
            .any(|judged| matches!(judged.verdict(), Verdict::Refused(_))),
        "{report:?}"
    );
}

#[test]
fn a_type_argument_names_the_type_its_constructor_shares_a_name_with_1855()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        "{MAYBE}data Box : Type {{ Box : (x : Integer) --> Box; }}\ndef kept(b : Box) -> -F Maybe(Box) {{ (Some(b) : Maybe(Box)) }}\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    assert_accepted(&judged(&module, &mut arena));
}

#[test]
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        linear_search_in_loop,
        reason = "bounded: the fixture's few binders, searched once per branch of one match"
    )
)]
fn a_pattern_variable_names_its_field_binder()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        "{MAYBE}def first(m : Maybe(Integer)) -> -F Integer {{ case m {{ Some(x) => return x, None => return 0 }} }}\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let root = tail_of(&arena, body_named(&module, SurfaceName::from("first")));
    let Some(&Computation::DataCase { ref branches, .. }) = arena.computation(root)
    else {
        panic!("the match is a data case");
    };
    let named: Vec<String> = branches
        .iter()
        .filter_map(|&branch| {
            module
                .origins()
                .binders()
                .iter()
                .find(|&&(opener, _)| opener == branch)
                .and_then(|&(_, origin)| {
                    source
                        .get(usize::from(origin.span().start()) .. usize::from(origin.span().end()))
                        .map(String::from)
                })
        })
        .collect();
    assert_eq!(named, Vec::from([String::from("x")]));
}

/// A record's field lambdas are minted innermost first and an arm body's
/// binder before them all, so naming them places each among the openers
/// already recorded: every field answers its own variable and the table stays
/// ascending.
#[test]
fn a_record_names_every_field_binder_in_order()
{
    let mut arena = CoreArena::new();
    let source = "data Rgb : Type {\n  RGB : (r : Integer, g : Integer, b : Integer) --> Rgb;\n}\ndef green(c : Rgb) -> -F Integer { case c { RGB(r, g, b) => { run n : Integer <- pure g ; return n } } }\n";
    let module = lowered(SourceText::from(source), &mut arena);
    let root = tail_of(&arena, body_named(&module, SurfaceName::from("green")));
    let Some(&Computation::DataCase { ref branches, .. }) = arena.computation(root)
    else {
        panic!("the match is a data case");
    };
    let binders = module.origins().binders();
    assert!(
        binders
            .windows(2)
            .all(|pair| matches!(pair, [left, right] if left.0 < right.0)),
        "{binders:?}"
    );
    let mut named = Vec::new();
    let mut lambda = *branches.first().expect("one branch");
    while let Some(&Computation::Lambda(body)) = arena.computation(lambda) {
        if let Ok(at) = binders.binary_search_by_key(&lambda, |&(opener, _)| opener)
            && let Some(&(_, origin)) = binders.get(at)
        {
            named.extend(
                source
                    .get(usize::from(origin.span().start()) .. usize::from(origin.span().end()))
                    .map(String::from),
            );
        }
        lambda = body;
    }
    assert_eq!(named, ["r", "g", "b"].map(String::from));
}

#[test]
fn a_data_family_applies_to_its_parameters()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        "{MAYBE}def keep(m : Maybe(Integer)) -> -F Integer {{ return 0 }}\ndef wide : Maybe(Integer, Integer) ;\n"
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
        "{COLOR}def rank(c : Color) -> -F Integer {{ case c {{ Red => return 0, _ => return 1 }} }}\ndef stated(c : Color) -> -F Integer {{ run n <- case c -> -F Integer {{ Red => pure 0, _ => pure 1 }}; return n }}\ndef typed(t : Type, x : t, c : Color) -> -F t {{ case c {{ Red => return x, _ => return x }} }}\ndef any(c : Color) -> -F Integer {{ case c {{ _ => return 1 }} }}\ndef same(c : Color) -> -F Color {{ case c {{ d => return d }} }}\n"
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
        ..
    }) = arena.computation(root)
    else {
        panic!("the match is a data case on its scrutinee");
    };
    assert_eq!(branches.len(), 3_usize);
    assert!(matches!(
        arena.value(scrutinee),
        Some(&Value::Variable { index, .. }) if index == gandr_kernel_term::DeBruijnIndex::from(0_u32)
    ));
    let Some(&gandr_core_term::CompType::Returner { result: answer, .. }) = arena.comp_type(motive)
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
        "{COLOR}def inner(c : Color) -> -F Integer {{ run n <- case c {{ Red => pure 0, _ => pure 1 }}; return n }}\n"
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
            "data Inner : Type { No : Inner; Yes : (n : Integer) --> Inner; }\ndata Outer : Type { Nothing : Outer; Just : (i : Inner) --> Outer; }\ndef depth(m : Outer) -> -F Integer { case m { Just(Yes(n)) => return n, Just(No) => return 0, other => return 1 } }\ndef answer = (Just((Yes(41) : Inner)) : Outer);\n",
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
fn a_data_case_names_the_family_it_eliminates_809()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        "{MAYBE}data Inner : Type {{ No : Inner; Yes : (n : Integer) --> Inner; }}\ndef depth(m : Maybe(Inner)) -> -F Integer {{ case m {{ Some(Yes(n)) => return n, Some(No) => return 0, None => return 1 }} }}\ndef nested(m : Maybe(Inner)) -> -F Integer {{ case m {{ None => return 1, Some(i) => case i {{ No => return 0, Yes(n) => return n }} }} }}\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let constant = |wanted: &str| {
        module
            .declarations()
            .iter()
            .find(|declaration| declaration.name().as_ref() == wanted)
            .map(|declaration| Maybe::Present(declaration.constant()))
    };
    for (name, expected) in [
        (
            "depth",
            "the switch on a family of parameters and the switch on its field each name their family",
        ),
        (
            "nested",
            "a match written in an arm binding a field names its family in the leaf's copy",
        ),
    ] {
        let root = tail_of(&arena, body_named(&module, SurfaceName::from(name)));
        let eliminated: Vec<_> = reachable(&arena, root)
            .into_iter()
            .filter(|&at| matches!(arena.computation(at), Some(&Computation::DataCase { .. })))
            .map(|at| Some(module.origins().elimination(at)))
            .collect();
        assert_eq!(
            eliminated,
            [constant("Maybe"), constant("Inner")],
            "{expected}"
        );
    }
}

#[test]
fn literal_patterns_compare_and_branch()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(
            "def small(n : Integer) -> -F Integer { case n { 0 => return 10, 1 => return 11, _ => return 12 } }\ndef flip(b : Bool) -> -F Integer { case b { true => return 1, false => return 0 } }\n",
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
fn literal_and_nullary_patterns_nest_under_a_constructor()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        "{COLOR}{MAYBE}def small(m : Maybe(Integer)) -> -F Integer {{ case m {{ Some(0) => return 10, Some(_) => return 11, None => return 12 }} }}\ndef flag(m : Maybe(Bool)) -> -F Integer {{ case m {{ Some(true) => return 1, Some(false) => return 0, None => return 2 }} }}\ndef hue(m : Maybe(Color)) -> -F Integer {{ case m {{ Some(Red) => return 1, Some(_) => return 2, None => return 3 }} }}\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let count = |name: &str, kind: fn(&Computation) -> bool| {
        reachable(
            &arena,
            tail_of(&arena, body_named(&module, SurfaceName::from(name))),
        )
        .into_iter()
        .filter(|&at| arena.computation(at).is_some_and(kind))
        .count()
    };
    let compares = |at: &Computation| matches!(*at, Computation::Primitive { .. });
    let cases = |at: &Computation| matches!(*at, Computation::Case { .. });
    let data_cases = |at: &Computation| matches!(*at, Computation::DataCase { .. });
    assert_eq!(
        count("small", compares),
        1_usize,
        "the nested literal compares once"
    );
    assert_eq!(
        count("flag", cases),
        1_usize,
        "the nested booleans branch on one case"
    );
    assert_eq!(
        count("hue", data_cases),
        2_usize,
        "the outer case on the option and the nested one on the colour"
    );
    let report = judged(&module, &mut arena);
    assert_accepted(&report);
}

#[test]
fn a_pattern_hole_leaves_its_leaf_stuck()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        "{COLOR}{MAYBE}def rank(c : Color) -> -F Integer {{ case c {{ Red => return 0, ? => return 1, Blue => return 2 }} }}\ndef inside(m : Maybe(Integer)) -> -F Integer {{ case m {{ Some(?) => return 100, None => return 0 }} }}\n"
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
        "{COLOR}def partial(c : Color) -> -F Integer {{ case c {{ Red => return 0, Green => return 1 }} }}\ndef open(n : Integer) -> -F Integer {{ case n {{ 0 => return 0 }} }}\n"
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
        "{COLOR}def text(s : String) -> -F Integer {{ case s {{ \"a\" => return 0, _ => return 1 }} }}\ndef mixed(c : Color) -> -F Integer {{ case c {{ Red => return 0, 1 => return 1, _ => return 2 }} }}\ndef bound(c : Color) -> -F Integer {{ case c {{ Red | x => return 0 }} }}\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    assert!(matches!(
        refusal_of(&module, SurfaceName::from("text")),
        LoweringRefusal::OutOfFragment {
            boundary: FragmentBoundary::Unadmitted(crate::Unbuilt::LiteralPattern),
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
            boundary: FragmentBoundary::Unadmitted(crate::Unbuilt::OrPattern),
            ..
        }
    ));
}

#[test]
fn a_misnamed_or_misshapen_pattern_is_refused_by_name()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        "{MAYBE}data Pair : Type {{ P : (a : Integer, b : Integer) --> Pair; }}\ndef twice(p : Pair) -> -F Integer {{ case p {{ P(a, a) => return a }} }}\ndef unknown(m : Maybe(Integer)) -> -F Integer {{ case m {{ Nope(x) => return x, _ => return 1 }} }}\ndef wide(m : Maybe(Integer)) -> -F Integer {{ case m {{ Some(x, y) => return x, None => return 1 }} }}\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("twice")),
            LoweringRefusal::DuplicateDefinition { name, .. } if name == SurfaceName::from("a")
        ),
        "a pattern binds each name once"
    );
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("unknown")),
            LoweringRefusal::UnresolvedName { name, .. } if name == SurfaceName::from("Nope")
        ),
        "a pattern's head names a constructor"
    );
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("wide")),
            LoweringRefusal::OutOfFragment {
                boundary: FragmentBoundary::Arity(count),
                ..
            } if count == OperandCount::from(2_usize)
        ),
        "a constructor pattern binds its constructor's fields, no more"
    );
}

#[test]
fn a_match_of_no_arms_eliminates_the_empty_sum()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(
            "def absurd(x : Void) -> -F Integer { case x {} }\ndef stated(x : Void) -> -F Integer { case x -> -F Integer {} }\n",
        ),
        &mut arena,
    );
    assert!(
        arena
            .computation(tail_of(&arena, body_named(&module, SurfaceName::from("absurd"))))
            .is_some_and(|held| matches!(*held, Computation::Case { ref branches, .. } if branches.is_empty()))
    );
    assert!(matches!(
        refusal_of(&module, SurfaceName::from("stated")),
        LoweringRefusal::OutOfFragment {
            form: FormName::CASE,
            boundary: FragmentBoundary::Unadmitted(crate::Unbuilt::EmptyCase),
            ..
        }
    ));
    assert_accepted(&judged(&module, &mut arena));
}

#[test]
fn a_match_of_no_arms_switches_on_empty_data_and_on_a_path()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        "data Empty : Type {{}}\ndata Nada(a : Type) : Type {{}}\n{COLOR}def absurd(v : Empty) -> -F Integer {{ case v {{}} }}\ndef stated(v : Empty) -> -F Integer {{ case v -> -F Integer {{}} }}\ndef apart(e : Path(Color, Red, Blue)) -> -F Empty {{ case e {{}} }}\ndef paren(v : (Empty)) -> -F Integer {{ case v {{}} }}\ndef wrapped(e : (Path(Color, Red, Blue))) -> -F Empty {{ case e {{}} }}\ndef applied(v : Nada(Integer)) -> -F Integer {{ case v {{}} }}\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    for name in ["absurd", "stated", "apart", "paren", "wrapped", "applied"] {
        assert!(
            arena
                .computation(tail_of(&arena, body_named(&module, SurfaceName::from(name))))
                .is_some_and(|held| matches!(*held, Computation::DataCase { ref branches, .. } if branches.is_empty())),
            "`{name}` switches on its scrutinee with no branch"
        );
    }
    assert_accepted(&judged(&module, &mut arena));

    let mut arena = CoreArena::new();
    let source = alloc::format!("{COLOR}def some(c : Color) -> -F Integer {{ case c {{}} }}\n");
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("some")),
            LoweringRefusal::NonExhaustiveMatch { .. }
        ),
        "a match of no arms over a type with constructors misses them"
    );
}

#[test]
fn a_match_of_no_arms_switches_on_a_lambda_binder_its_arrow_types()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(
            "data Empty : Type {}\ndef bare : +U (Empty -> -F Integer) ;\ndef bare = thunk { fn (x) { case x {} } } ;\ndef stated : +U (Empty -> -F Integer) ;\ndef stated = thunk { fn (x) { case x -> -F Integer {} } } ;\n",
        ),
        &mut arena,
    );
    for name in ["bare", "stated"] {
        assert!(
            arena
                .computation(tail_of(&arena, body_named(&module, SurfaceName::from(name))))
                .is_some_and(|held| matches!(*held, Computation::DataCase { ref branches, .. } if branches.is_empty())),
            "`{name}` switches on its binder with no branch"
        );
    }
    assert_accepted(&judged(&module, &mut arena));
}

/// A lambda a signed definition writes bare, the checker inserting its thunk,
/// types its binder by the signature's arrow as the thunked lambda does: a
/// match of no arms on it switches on the empty data, under an alias and
/// under the arrow, where the signature lies after the body in the arena, as
/// a decorated declaration's does (#1944).
#[test]
fn a_bare_signed_lambda_s_binder_is_typed_as_in_its_thunk_1944()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(
            "data Empty : Type {}\n@[ checks ]\ndef aliased : Empty => Integer ;\ndef aliased = fn (x) { case x {} } ;\n@[ checks ]\ndef bare : +U (Empty -> -F Integer) ;\ndef bare = fn (x) { case x {} } ;\n@[ checks ]\ndef stated : +U (Empty -> -F Integer) ;\ndef stated = fn (x) { case x -> -F Integer {} } ;\n",
        ),
        &mut arena,
    );
    assert_accepted(&judged(&module, &mut arena));
}

/// A lambda passed as an argument types its binder by the type its callee
/// writes for the parameter, as a signed definition's lambda does: a match of
/// no arms on it switches on the empty data, the lambda in a thunk and bare,
/// under an alias and under the arrow, and with the answer stated (#1948).
#[test]
fn an_argument_lambda_s_binder_is_typed_by_its_parameter_1948()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(
            "data Empty : Type {}\ndef aliased(f : Empty => Integer, v : Empty) -> -F Integer { f(v) }\ndef arrowed(f : +U (Empty -> -F Integer), v : Empty) -> -F Integer { f(v) }\n@[ checks ]\ndef thunked(v : Empty) -> -F Integer { aliased(thunk { fn (x) { case x {} } }, v) }\n@[ checks ]\ndef bare(v : Empty) -> -F Integer { aliased(fn (x) { case x {} }, v) }\n@[ checks ]\ndef stated(v : Empty) -> -F Integer { aliased(thunk { fn (x) { case x -> -F Integer {} } }, v) }\n@[ checks ]\ndef underArrow(v : Empty) -> -F Integer { arrowed(thunk { fn (x) { case x {} } }, v) }\n",
        ),
        &mut arena,
    );
    assert_accepted(&judged(&module, &mut arena));
}

#[test]
fn a_lambda_under_a_value_function_alias_lowers_as_under_its_thunked_arrow_808()
{
    for (alias, arrow, body) in [
        (
            "Empty => Integer",
            "+U (Empty -> -F Integer)",
            "thunk { fn (x) { case x {} } }",
        ),
        (
            "Empty => Integer",
            "+U (Empty -> -F Integer)",
            "thunk { fn (x) { case x -> -F Integer {} } }",
        ),
        (
            "(Empty, Integer) => Integer",
            "+U (Empty -> Integer -> -F Integer)",
            "thunk { fn (x) { fn (n) { case x {} } } }",
        ),
    ] {
        let mut arena = CoreArena::new();
        let source = alloc::format!(
            "data Empty : Type {{}}\ndef aliased : {alias} ;\ndef aliased = {body} ;\ndef thunked : {arrow} ;\ndef thunked = {body} ;\n"
        );
        let module = lowered(SourceText::from(source.as_str()), &mut arena);
        assert_eq!(
            gandr_core_term::equal_certificate_syntax(
                &arena,
                body_named(&module, SurfaceName::from("aliased")),
                body_named(&module, SurfaceName::from("thunked")),
            ),
            gandr_core_term::CertificateEquality::Equal,
            "`{body}` under `{alias}` lowers as under `{arrow}`"
        );
        assert_accepted(&judged(&module, &mut arena));
    }
}

#[test]
fn a_lambda_under_a_telescope_alias_lowers_as_under_its_dependent_arrows_815()
{
    for (alias, arrow, body) in [
        (
            "(a : Empty, b : Integer) => Integer",
            "+U ((a : Empty) -> (b : Integer) -> -F Integer)",
            "thunk { fn (a) { fn (b) { case a {} } } }",
        ),
        (
            "(a : One) => Path(One, a, a)",
            "+U ((a : One) -> -F Path(One, a, a))",
            "thunk { fn (a) { case a { Only => here(Only) } } }",
        ),
        (
            "(a : One, Integer) => Path(One, a, a)",
            "+U ((a : One) -> Integer -> -F Path(One, a, a))",
            "thunk { fn (x) { fn (n) { case x { Only => here(Only) } } } }",
        ),
    ] {
        let mut arena = CoreArena::new();
        let source = alloc::format!(
            "data Empty : Type {{}}\ndata One : Type {{\n  Only : One;\n}}\ndef aliased : {alias} ;\ndef aliased = {body} ;\ndef thunked : {arrow} ;\ndef thunked = {body} ;\n"
        );
        let module = lowered(SourceText::from(source.as_str()), &mut arena);
        assert_eq!(
            gandr_core_term::equal_certificate_syntax(
                &arena,
                body_named(&module, SurfaceName::from("aliased")),
                body_named(&module, SurfaceName::from("thunked")),
            ),
            gandr_core_term::CertificateEquality::Equal,
            "`{body}` under `{alias}` lowers as under `{arrow}`"
        );
        assert_accepted(&judged(&module, &mut arena));
    }
}

#[test]
fn an_or_pattern_settles_each_alternative()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        "{COLOR}def warm(c : Color) -> -F Integer {{ case c {{ Red | Green => return 1, Blue => return 0 }} }}\n"
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
    let spelled = |text: &str| -> Vec<_> {
        kept.spans
            .iter()
            .filter(|kept| {
                source.get(usize::from(kept.span.start()) .. usize::from(kept.span.end()))
                    == Some(text)
            })
            .map(|kept| (kept.pattern, kept.reading))
            .collect()
    };
    assert_eq!(
        spelled("Red | Green"),
        kept.arms
            .first()
            .map(|first| (first.pattern, PatternReading::Matched))
            .into_iter()
            .collect::<Vec<_>>(),
        "the whole or-pattern is kept once, against its first alternative"
    );
    let blue = kept.arms.get(2).map(|blue| blue.pattern);
    assert_eq!(
        spelled("Blue")
            .into_iter()
            .filter(
                |&(pattern, reading)| Some(pattern) == blue && reading == PatternReading::Matched
            )
            .count(),
        1_usize,
        "a pattern of one alternative is kept once, as itself"
    );
    let report = judged(&module, &mut arena);
    assert_accepted(&report);
}

#[test]
fn a_binary_injection_pattern_is_kept_at_its_side()
{
    let mut arena = CoreArena::new();
    let source = "def not(b : +{Unit, Unit}) -> -F +{Unit, Unit} { case b { +{.0 = u} => return \
                  +{.1 = u}, +{.1 = u} => return +{.0 = u} } }\n";
    let module = lowered(SourceText::from(source), &mut arena);
    let root = tail_of(&arena, body_named(&module, SurfaceName::from("not")));
    let Maybe::Present(kept) = module.origins().case(root)
    else {
        panic!("the match keeps its arms");
    };
    let sides: Vec<_> = kept
        .arms
        .iter()
        .map(|arm| match kept.patterns.pattern(arm.pattern) {
            Some(&Pattern::Injection(side, field)) => {
                Some((side, kept.patterns.pattern(field).cloned()))
            },
            _ => None,
        })
        .collect();
    assert_eq!(
        sides,
        [
            Some((gandr_kernel_term::Side::Left, Some(Pattern::Binder))),
            Some((gandr_kernel_term::Side::Right, Some(Pattern::Binder))),
        ],
        "a summand of a binary sum is kept as the injection at its side, over its field"
    );
    assert_accepted(&judged(&module, &mut arena));
}

#[test]
fn a_match_keeps_its_patterns_beside_its_tree()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        "{MAYBE}def pick(m : Maybe(Integer)) -> -F Integer {{ case m {{ Some(x) => return x, ? => return 0 }} }}\n"
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
        HoleId::from(0_u32),
        "a pattern hole is named by its place among the holes the text writes"
    );
    assert!(
        reachable(&arena, root)
            .into_iter()
            .any(|at| arena.computation(at) == Some(&Computation::Hole(identity))),
        "the tree is stuck on the same hole"
    );
    assert!(usize::from(kept.scrutinee) > usize::from(kept.written));
    assert!(
        matches!(kept.scrutinised, Maybe::Present(value) if matches!(arena.value(value), Some(&Value::Variable { .. }))),
        "the record names the value the tree eliminates"
    );
    let spelled: Vec<(&str, PatternReading)> = kept
        .spans
        .iter()
        .map(|kept| {
            (
                source
                    .get(usize::from(kept.span.start()) .. usize::from(kept.span.end()))
                    .expect("a kept span is in the source"),
                kept.reading,
            )
        })
        .collect();
    for written in [
        ("Some(x)", PatternReading::Matched),
        ("Some", PatternReading::Constructor),
        ("x", PatternReading::Matched),
        ("?", PatternReading::Matched),
    ] {
        assert!(
            spelled.contains(&written),
            "{written:?} is kept: {spelled:?}"
        );
    }
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

#[test]
fn a_leaf_keeps_its_arm_body_written()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        "{MAYBE}def pick(m : Maybe(Integer), d : Integer) -> -F Integer {{ case m {{ Some(x) => return x, None => return d }} }}\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let root = tail_of(&arena, body_named(&module, SurfaceName::from("pick")));
    let written = |span: ByteSpan| source.get(usize::from(span.start()) .. usize::from(span.end()));
    let mut returned = Vec::new();
    for at in reachable(&arena, root) {
        let Some(&Computation::Return(value)) = arena.computation(at)
        else {
            continue;
        };
        for origin in [
            module.origins().computation(at),
            module.origins().value(value),
        ] {
            let Maybe::Present(origin) = origin
            else {
                panic!("every node of the tree has an origin");
            };
            assert_eq!(
                origin.provenance(),
                Provenance::Written,
                "an arm's body is the source's, in its leaf's copy too"
            );
            returned.push(written(origin.span()));
        }
    }
    returned.sort_unstable();
    assert_eq!(
        returned,
        [Some("d"), Some("return d"), Some("return x"), Some("x")],
        "each return, and what it returns, at its own bytes"
    );
}

#[test]
fn a_relocated_annotation_keeps_its_bytes()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        "{MAYBE}def forget(b : Type, m : Maybe(b)) -> -F Maybe(b) {{ case m {{ Some(x) => return (None : Maybe(b)), None => return m }} }}\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let root = tail_of(&arena, body_named(&module, SurfaceName::from("forget")));
    let written = |span: ByteSpan| source.get(usize::from(span.start()) .. usize::from(span.end()));
    let annotated = source.find("(None").map(|at| at.saturating_add(14_usize));
    let mut arguments = Vec::new();
    for at in reachable(&arena, root) {
        let Some(&Computation::Return(value)) = arena.computation(at)
        else {
            continue;
        };
        let Some(&Value::Constructor { datatype, .. }) = arena.value(value)
        else {
            continue;
        };
        let Some(ValueType::Data {
            arguments: held, ..
        }) = arena.value_type(datatype).cloned()
        else {
            panic!("the classifier is the annotation's family");
        };
        for argument in held {
            let Maybe::Present(origin) = module.origins().value(argument)
            else {
                panic!("every node of the classifier has an origin");
            };
            arguments.push((
                origin.provenance(),
                written(origin.span()),
                usize::from(origin.span().start()),
            ));
        }
    }
    assert_eq!(
        arguments,
        [(
            Provenance::Written,
            Some("b"),
            annotated.unwrap_or_default()
        )],
        "the classifier under the arm's binder answers at the annotation's argument"
    );
}

#[test]
fn telescope_patterns_split_and_project()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(
            "def middle(t : #{Integer, String, Unit}) -> -F String { case t { #{x, y, z} => return y } }\ndef reordered(t : #{Integer, String}) -> -F Integer { case t { #{.1 = b, .0 = a} => return a } }\ndef tupled(t : #{Integer, String}) -> -F String { case t { (a, b) => return b } }\ndef punned(r : #{n : Integer, s : String}) -> -F String { case r { #{.n, .s} => return s } }\ndef renamed(r : #{n : Integer, s : String}) -> -F Integer { case r { #{.n = m} => return m } }\n",
        ),
        &mut arena,
    );
    let split = |name: &str| -> Vec<usize> {
        reachable(
            &arena,
            tail_of(&arena, body_named(&module, SurfaceName::from(name))),
        )
        .into_iter()
        .filter_map(|at| match arena.computation(at) {
            Some(&Computation::Split { arity, .. }) => Some(usize::from(arity)),
            _ => None,
        })
        .collect()
    };
    assert_eq!(
        split("middle"),
        [3_usize],
        "a telescope pattern of three splits once"
    );
    assert_eq!(
        split("reordered"),
        [2_usize],
        "an indexed one splits in index order"
    );
    assert_eq!(
        split("tupled"),
        [2_usize],
        "a tuple pattern splits as the telescope does"
    );
    let projected = |name: &str| -> Vec<String> {
        reachable(
            &arena,
            tail_of(&arena, body_named(&module, SurfaceName::from(name))),
        )
        .into_iter()
        .filter_map(|at| match arena.computation(at) {
            Some(&Computation::RecordProjection(_, ref label)) => {
                Some(String::from(label.as_ref()))
            },
            _ => None,
        })
        .collect()
    };
    assert_eq!(
        projected("punned"),
        ["n", "s"],
        "a record pattern projects each label it writes"
    );
    assert_eq!(projected("renamed"), ["n"], "and only the labels it writes");
    assert_accepted(&judged(&module, &mut arena));

    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(
            "def swapped(t : #{Integer, String}) -> -F Integer { case t { #{a, b} => return b } }\n",
        ),
        &mut arena,
    );
    assert!(
        judged(&module, &mut arena)
            .judged()
            .iter()
            .any(|judged| matches!(judged.verdict(), Verdict::Refused(_))),
        "the components are bound in written order, so the second is the string"
    );
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(
            "def ragged(t : #{Integer, String}) -> -F Integer { case t { (a, b) => return a, (a, b, c) => return a } }\n",
        ),
        &mut arena,
    );
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("ragged")),
            LoweringRefusal::OutOfFragment {
                boundary: FragmentBoundary::WrongSort,
                ..
            }
        ),
        "a tuple pattern wider than the tuple its column splits is refused: {:?}",
        refusal_of(&module, SurfaceName::from("ragged"))
    );
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(
            "def over(t : #{Integer, String}) -> -F Integer { case t { #{a, b, c} => return a } }\n",
        ),
        &mut arena,
    );
    let widths: Vec<usize> = reachable(
        &arena,
        tail_of(&arena, body_named(&module, SurfaceName::from("over"))),
    )
    .into_iter()
    .filter_map(|at| match arena.computation(at) {
        Some(&Computation::Split { arity, .. }) => Some(usize::from(arity)),
        _ => None,
    })
    .collect();
    assert_eq!(
        widths,
        [3_usize],
        "a telescope pattern splits at its own width, which the checker judges against the pair"
    );
}

/// A pattern at a scrutinee written with a dependent record splits it under
/// the match's answer with the scrutinee abstracted, so a rebuilt pair
/// answers the path at the scrutinee; a labelled pattern places its labels
/// by the record's order, and a record of three nests its links.
#[test]
fn a_pattern_at_a_dependent_record_splits_it_under_its_motive()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(concat!(
            "def eta(p : #{n : Integer, v : Path(Integer, n, n)}) -> -F Path(#{n : Integer, v : Path(Integer, n, n)}, p, p) { case p { #{m, w} => return here(#{m, w}) } }\n",
            "def rebuilt(p : #{n : Integer, v : Path(Integer, n, n)}) -> -F #{n : Integer, v : Path(Integer, n, n)} { case p { #{.v = w, .n = m} => return #{m, w} } }\n",
            "def last(t : #{a : Integer, b : Integer, c : Path(Integer, a, a)}) -> -F Path(Integer, t.a, t.a) { case t { #{.c = z} => return z } }\n",
        )),
        &mut arena,
    );
    let splits = |name: &str| -> Vec<(usize, bool)> {
        reachable(
            &arena,
            tail_of(&arena, body_named(&module, SurfaceName::from(name))),
        )
        .into_iter()
        .filter_map(|at| match arena.computation(at) {
            Some(&Computation::Split { arity, motive, .. }) => Some((
                usize::from(arity),
                matches!(motive, gandr_core_term::SplitMotive::Scrutinee(_)),
            )),
            _ => None,
        })
        .collect()
    };
    assert_eq!(
        splits("eta"),
        [(2_usize, true)],
        "the pair splits once, under a motive over the scrutinee"
    );
    assert_eq!(
        splits("rebuilt"),
        [(2_usize, true)],
        "labels in another order split it the same"
    );
    assert_eq!(
        splits("last"),
        [(2_usize, true), (2_usize, false)],
        "a record of three splits its first link dependently and its second, which nothing later reads, as a product"
    );
    assert_accepted(&judged(&module, &mut arena));
}

/// A call written as a scrutinee splits the record its function's result
/// states, as a `run` binder of the call does: a dependent record under a
/// motive over the scrutinee, so the checker reads the second component at
/// the first.
#[test]
fn a_call_as_the_scrutinee_splits_the_record_it_returns_1141()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(concat!(
            "def tagged(n : Integer) -> -F #{m : Integer, v : Path(Integer, m, m)} { return #{n, here(n)} }\n",
            "def tag() -> -F Integer { case tagged(5) { #{m, w} => return m } }\n",
            "def bound() -> -F Integer { run t <- tagged(5); case t { #{m, w} => return m } }\n",
        )),
        &mut arena,
    );
    let splits = |name: &str| -> Vec<(usize, bool)> {
        reachable(
            &arena,
            tail_of(&arena, body_named(&module, SurfaceName::from(name))),
        )
        .into_iter()
        .filter_map(|at| match arena.computation(at) {
            Some(&Computation::Split { arity, motive, .. }) => Some((
                usize::from(arity),
                matches!(motive, gandr_core_term::SplitMotive::Scrutinee(_)),
            )),
            _ => None,
        })
        .collect()
    };
    assert_eq!(
        splits("tag"),
        splits("bound"),
        "the call written as the scrutinee splits as the bound call does"
    );
    assert_eq!(
        splits("tag"),
        [(2_usize, true)],
        "under a motive over the scrutinee"
    );
    assert_accepted(&judged(&module, &mut arena));
}

/// A case over a variable whose answer names it answers its motive at each
/// constructor: the data case's motive reads its scrutinee, a leaf reads the
/// scrutinee as its branch's constructor over the branch's fields, and a
/// recursive call at a field answers the motive there, so a cong of it
/// answers the successor's branch. The words over a looped point are such a
/// family, so a case over a path at the point reads its empty-word leaf at
/// the empty word. A case whose answer names another variable keeps its
/// scrutinee in the leaves.
#[test]
fn a_case_over_a_variable_answers_its_motive_at_each_constructor()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        "{NAT}def next(n : Nat) -> -F Nat {{ return Succ(n) }}\ndef rec still(n : Nat) -> -F Path(Nat, n, n) {{ case n {{ Zero => return here(n), Succ(p) => {{ run q <- still[<](p); become cong(next, q) }} }} }}\ndef kept(n : Nat, m : Nat) -> -F Path(Nat, m, m) {{ case n {{ Zero => return here(m), Succ(p) => return here(m) }} }}\ndata Circle : Type {{ Base : Circle; loop : Base <-> Base; }}\ndef loopOn(p : Path(Circle, Base, Base)) -> -F Path(Circle, Base, Base) {{ return loop ∷ p }}\ndef unloopOn(p : Path(Circle, Base, Base)) -> -F Path(Circle, Base, Base) {{ return back(loop) ∷ p }}\ndef rec looped(p : Path(Circle, Base, Base)) -> -F Path(Path(Circle, Base, Base), p, p) {{ case p {{ here => return here(p), loop ∷ q => {{ run r <- looped[<](q); become cong(loopOn, r) }}, back(loop) ∷ q => {{ run r <- looped[<](q); become cong(unloopOn, r) }} }} }}\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let cased = |arena: &CoreArena, name: &str| {
        let mut tail = tail_of(arena, body_named(&module, SurfaceName::from(name)));
        while let Some(&(Computation::Fixpoint { body: under, .. } | Computation::Lambda(under))) =
            arena.computation(tail)
        {
            tail = under;
        }
        reachable(arena, tail)
            .into_iter()
            .find_map(|at| match arena.computation(at) {
                Some(&Computation::DataCase {
                    motive,
                    ref branches,
                    ..
                }) => Some((motive, branches.clone())),
                _ => None,
            })
            .expect("the body cases on its scrutinee")
    };
    let returned_at_zero = |arena: &CoreArena, branches: &[ComputationId]| {
        let zero = *branches.first().expect("a branch per constructor");
        reachable(arena, zero)
            .into_iter()
            .find_map(|at| match arena.computation(at) {
                Some(&Computation::Return(value)) => match arena.value(value) {
                    Some(&Value::Here(point)) => arena.value(point).cloned(),
                    _ => None,
                },
                _ => None,
            })
            .expect("the zero branch returns a reflexivity")
    };

    let (motive, branches) = cased(&arena, "still");
    assert!(
        matches!(
            gandr_core_term::strengthen_comp_type(&mut arena, motive),
            Maybe::Absent(_)
        ),
        "the motive reads the scrutinee it abstracts"
    );
    assert!(
        matches!(returned_at_zero(&arena, &branches), Value::Constructor { tag, .. } if tag == ConstructorTag::from(0_usize)),
        "the zero leaf reads the scrutinee as `Zero`"
    );

    let words = module
        .declarations()
        .iter()
        .find(|declaration| declaration.role() == crate::module::Role::Words)
        .map(crate::module::LoweredDeclaration::constant)
        .expect("the circle's loop mints its words");
    let (motive, branches) = cased(&arena, "looped");
    assert!(
        matches!(
            gandr_core_term::strengthen_comp_type(&mut arena, motive),
            Maybe::Absent(_)
        ),
        "the motive over a word reads the word it abstracts"
    );
    let Value::Constructor { datatype, tag, .. } = returned_at_zero(&arena, &branches)
    else {
        panic!("the empty-word leaf reads the scrutinee as a word");
    };
    assert!(
        tag == ConstructorTag::from(0_usize)
            && matches!(arena.value_type(datatype), Some(&ValueType::Data { declaration, ref arguments })
                if declaration == words && arguments.is_empty()),
        "the empty-word leaf reads the scrutinee as the empty word"
    );

    let (motive, branches) = cased(&arena, "kept");
    assert!(
        matches!(
            gandr_core_term::strengthen_comp_type(&mut arena, motive),
            Maybe::Present(_)
        ),
        "an answer over another variable reads no scrutinee"
    );
    assert!(
        matches!(returned_at_zero(&arena, &branches), Value::Variable { .. }),
        "a leaf under an independent case keeps its variables"
    );
    assert_accepted(&judged(&module, &mut arena));
}

#[test]
fn the_presentation_code_names_its_family_where_a_type_is_read()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(
            "theory Monoid { sort M : Type; }\ndef held : Theory ;\ndef held = Monoid ;\n",
        ),
        &mut arena,
    );
    let theory = module
        .declarations()
        .iter()
        .find(|declaration| declaration.name() == SurfaceName::from("Theory"))
        .map(crate::module::LoweredDeclaration::constant)
        .expect("a `theory` block declares the code it is a value of");
    let held = module
        .declarations()
        .iter()
        .find(|declaration| declaration.name() == SurfaceName::from("held"))
        .map(crate::module::LoweredDeclaration::outcome);
    let Some(DeclarationOutcome::Completed { declared_type, .. }) = held
    else {
        panic!("`held` lowers both halves: {held:?}");
    };
    assert_eq!(
        arena.value_type(declared_type),
        Some(&ValueType::Data {
            declaration: theory,
            arguments: Vec::new(),
        }),
        "`Theory` written as a type is the family of no parameters it codes"
    );
    assert_accepted(&judged(&module, &mut arena));
}

#[test]
fn a_case_over_a_family_of_parameters_reads_its_answer_unabstracted()
{
    let mut arena = CoreArena::new();
    let source = "data Box(a : Type) : Type { Put : (x : a) --> Box(a); }\ndef same(b : \
                  Box(Integer)) -> -F Path(Box(Integer), b, b) { case b { Put(x) => return \
                  here(b) } }\n";
    let module = lowered(SourceText::from(source), &mut arena);
    let tail = tail_of(&arena, body_named(&module, SurfaceName::from("same")));
    let reached = reachable(&arena, tail);
    let motives: Vec<_> = reached
        .iter()
        .filter_map(|&at| match arena.computation(at) {
            Some(&Computation::DataCase { motive, .. }) => Some(motive),
            _ => None,
        })
        .collect();
    let returned: Vec<Value> = reached
        .iter()
        .filter_map(|&at| match arena.computation(at) {
            Some(&Computation::Return(value)) => match arena.value(value) {
                Some(&Value::Here(point)) => arena.value(point).cloned(),
                _ => None,
            },
            _ => None,
        })
        .collect();
    let [motive] = *motives
    else {
        panic!("the body cases once: {motives:?}");
    };
    assert!(
        matches!(
            gandr_core_term::strengthen_comp_type(&mut arena, motive),
            Maybe::Present(_)
        ),
        "no arm is read at its constructor, so the motive reads no scrutinee (#616)"
    );
    assert!(
        matches!(*returned, [Value::Variable { .. }]),
        "and the leaf reads the scrutinee as itself: {returned:?}"
    );
    assert_accepted(&judged(&module, &mut arena));
}

/// A case on a vector one past `n` with no `VNil` arm lowers with one
/// equation per branch: `VCons` binds its three fields and the equation, and
/// the left-out `VNil` binds the equation alone and eliminates it by the case
/// of no branches. The checker admits it, `Zero` apart from `Succ(n)`.
#[test]
fn a_constructor_no_row_admits_at_one_index_is_pruned()
{
    let mut arena = CoreArena::new();
    let source = concat!(
        "data Nat : Type { Zero : Nat; Succ : (n : Nat) --> Nat; }\n",
        "data Vec(a : Type) : Nat -> Type { VNil : Vec(a, Zero); ",
        "VCons : (n : Nat, head : a, tail : Vec(a, n)) --> Vec(a, Succ(n)); }\n",
        "def vhead(n : Nat, v : Vec(Integer, Succ(n))) -> -F Integer ",
        "{ case v { VCons(m, h, t) => h } }\n",
    );
    let module = lowered(SourceText::from(source), &mut arena);
    let tail = tail_of(&arena, body_named(&module, SurfaceName::from("vhead")));
    let reached = reachable(&arena, tail);
    let cases: Vec<_> = reached
        .iter()
        .filter_map(|&at| match arena.computation(at) {
            Some(&Computation::DataCase {
                ref branches,
                equations,
                ..
            }) if !branches.is_empty() => Some((branches.clone(), equations)),
            _ => None,
        })
        .collect();
    let [(ref branches, equations)] = *cases
    else {
        panic!("the body cases once on the vector: {cases:?}");
    };
    assert_eq!(
        usize::from(equations),
        1,
        "each branch binds the one index's equation"
    );
    let lambdas = |mut at: ComputationId| {
        let mut count = 0_usize;
        while let Some(&Computation::Lambda(body)) = arena.computation(at) {
            count = count.saturating_add(1);
            at = body;
        }
        (count, at)
    };
    let [nil, cons] = **branches
    else {
        panic!("one branch per constructor: {branches:?}");
    };
    assert_eq!(
        lambdas(cons).0,
        4,
        "`VCons` binds its three fields, then its equation"
    );
    let (bound, absurd) = lambdas(nil);
    assert_eq!(bound, 1, "`VNil` binds its equation alone");
    let Some(&Computation::DataCase {
        scrutinee,
        ref branches,
        ..
    }) = arena.computation(absurd)
    else {
        panic!(
            "the left-out arm is a case: {:?}",
            arena.computation(absurd)
        );
    };
    assert!(branches.is_empty(), "of no branches");
    assert_eq!(
        arena.value(scrutinee),
        Some(&Value::Variable {
            zone: gandr_core_term::Zone::Intuitionistic,
            index: DeBruijnIndex::from(0_u32),
        }),
        "on its equation"
    );
    assert_accepted(&judged(&module, &mut arena));
}

/// A leaf's copy of an arm keeps each written use naming the pattern variable
/// that binds it, so a split's components are named where the arm reads them;
/// the swapped pair tells a copy bound at the wrong component apart. A
/// variable that binds the whole scrutinee stands for the scrutinee's own
/// node, which stays bound at its parameter.
#[test]
fn a_leaf_copy_keeps_each_use_naming_its_pattern_variable()
{
    let source = concat!(
        "def swap(p : #{Integer, Integer}) -> -F #{Integer, Integer} { case p { #{m, w} => return #{w, m} } }\n",
        "def whole(p : #{Integer, Integer}) -> -F #{Integer, Integer} { case p { q => return q } }\n",
    );
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source), &mut arena);
    let written = |anchor: &str, name: &str| {
        let at = source
            .find(anchor)
            .and_then(|from| {
                source
                    .get(from ..)
                    .and_then(|rest| rest.find(name))
                    .map(|offset| from.saturating_add(offset))
            })
            .expect("the anchor writes the name");
        Maybe::Present(crate::fixture::span(
            gandr_surface_syntax::ByteOffset::from(at),
            gandr_surface_syntax::ByteOffset::from(at.saturating_add(name.len())),
        ))
    };
    let returned = |name: &str| {
        reachable(
            &arena,
            tail_of(&arena, body_named(&module, SurfaceName::from(name))),
        )
        .into_iter()
        .find_map(|at| match arena.computation(at) {
            Some(&Computation::Return(value)) => Some(value),
            _ => None,
        })
        .expect("the arm's copy returns")
    };
    let swapped = arena
        .value(returned("swap"))
        .expect("the copy returns a value");
    let Value::Tuple(ref answered) = *swapped
    else {
        panic!("the copy returns a pair: {swapped:?}");
    };
    let [first, second] = answered[..]
    else {
        panic!("the copy returns a pair: {answered:?}");
    };
    assert_eq!(
        module.origins().binding(first),
        written("#{m, w}", "w"),
        "the copy's first component is the use of `w`"
    );
    assert_eq!(
        module.origins().binding(second),
        written("#{m, w}", "m"),
        "the copy's second component is the use of `m`"
    );
    assert_eq!(
        module.origins().binding(returned("whole")),
        written("whole(", "p"),
        "the scrutinee a whole-value pattern stands for stays bound at its parameter"
    );
}

/// The leaf under `S(x)` copies the arm's use of `a` and then copies that copy
/// into the `back` form, both in one rewrite; the second copy still names the
/// parameter the use was written against, and no variable the form carries
/// names another binder.
#[test]
fn a_leaf_copy_of_a_copy_keeps_the_use_naming_its_binder_451()
{
    let source = concat!(
        "data Int : Type { Z : Int; S : (x : Int) --> Int; }\n",
        "def r(n : Int) -> -F Path(Int, n, n) { here(n) }\n",
        "def f(a : Int, b : Int) -> -F Path(Int, a, a) { case b { Z => back(r(a)), S(x) => back(r(a)) } }\n",
    );
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source), &mut arena);
    let parameter = source.find("a : Int").expect("`f` declares `a`");
    let bound = Maybe::Present(crate::fixture::span(
        gandr_surface_syntax::ByteOffset::from(parameter),
        gandr_surface_syntax::ByteOffset::from(parameter.saturating_add(1)),
    ));
    let form = source
        .rfind("back(r(a))")
        .expect("the `S(x)` arm writes `back`");
    let carried: Vec<ValueId> = arena
        .values_since(gandr_core_term::ArenaWatermark::default())
        .filter(|&id| {
            matches!(arena.value(id), Some(&Value::Variable { .. }))
                && matches!(module.origins().value(id), Maybe::Present(origin)
                    if usize::from(origin.span().start()) == form)
        })
        .collect();
    assert!(
        carried
            .iter()
            .any(|&id| module.origins().binding(id) == bound),
        "the `back` form's copy of the use names `a`: {carried:?}"
    );
    assert!(
        carried.iter().all(
            |&id| matches!(module.origins().binding(id), Maybe::Absent(_))
                || module.origins().binding(id) == bound
        ),
        "no variable the `back` form carries names another binder: {carried:?}"
    );
}

#[test]
fn sum_patterns_case_on_the_stated_arity()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(
            "def pick(s : +{ok : Integer, err : String, gone : Unit}) -> -F String { case s { +{.ok = n} => return \"ok\", +{.err = e} => return e, +{.gone = u} => return \"gone\" } }\ndef indexed(s : +{String, String, Integer}) -> -F Integer { case s { +{.2 = n} => return n, _ => return 0 } }\ndef nested(t : #{Integer, +{ok : Integer, err : String}}) -> -F String { case t { #{n, +{.ok = m}} => return \"ok\", #{n, +{.err = e}} => return e } }\ndef single(s : +{only : Integer}) -> -F Integer { case s { +{.only = n} => return n } }\n",
        ),
        &mut arena,
    );
    let summands = |name: &str| -> Vec<usize> {
        reachable(
            &arena,
            tail_of(&arena, body_named(&module, SurfaceName::from(name))),
        )
        .into_iter()
        .filter_map(|at| match arena.computation(at) {
            Some(&Computation::Case { ref branches, .. }) => Some(branches.len()),
            _ => None,
        })
        .collect()
    };
    assert_eq!(
        summands("pick"),
        [3_usize],
        "one case over the three summands the type states"
    );
    assert_eq!(
        summands("indexed"),
        [3_usize],
        "an index past the binary sum names its summand"
    );
    assert_eq!(
        summands("nested"),
        [2_usize],
        "a sum inside a telescope reads its component's type"
    );
    assert_eq!(
        summands("single"),
        [1_usize],
        "a sum of one is a case of one branch"
    );
    assert_accepted(&judged(&module, &mut arena));

    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(
            "def unstated(n : Integer) -> -F Integer { case (+{.ok = n} : +{ok : Integer, err : String}) { +{.ok = m} => return m, +{.err = s} => return 0 } }\n",
        ),
        &mut arena,
    );
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("unstated")),
            LoweringRefusal::OutOfFragment {
                form: FormName::LABELLED_SUM_PATTERN,
                boundary: FragmentBoundary::Unannotated,
                ..
            }
        ),
        "a scrutinee no name types states no sum, so a label has no index"
    );
}

/// #791: before the fix, a match read a parameter's summands only off the
/// braced `+{A, B}`, so one stated as the chain `A + B`, the same type, refused
/// its labelled sum patterns as unannotated.
#[test]
fn a_sum_pattern_reads_a_sum_stated_as_a_chain_791()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(
            "def two(t : Integer + Integer) -> -F Integer { case t { +{.1 = x} => return x, _ => return 0 } }\ndef three(s : String + String + Integer) -> -F Integer { case s { +{.2 = n} => return n, _ => return 0 } }\ndef grouped(s : Integer + (String + Unit)) -> -F Integer { case s { +{.0 = n} => return n, +{.1 = r} => return 1 } }\ndef nested(t : (Integer + Integer) * Integer) -> -F Integer { case t { #{+{.1 = x}, y} => return x, #{_, y} => return y } }\n",
        ),
        &mut arena,
    );
    let summands = |name: &str| -> Vec<usize> {
        reachable(
            &arena,
            tail_of(&arena, body_named(&module, SurfaceName::from(name))),
        )
        .into_iter()
        .filter_map(|at| match arena.computation(at) {
            Some(&Computation::Case { ref branches, .. }) => Some(branches.len()),
            _ => None,
        })
        .collect()
    };
    assert_eq!(summands("two"), [2_usize], "a chain of two is a binary sum");
    assert_eq!(
        summands("three"),
        [3_usize],
        "a chain of three is one sum of three, as `+{{A, B, C}}`"
    );
    assert_eq!(
        summands("grouped"),
        [2_usize],
        "a parenthesized sum is one summand"
    );
    assert_eq!(
        summands("nested"),
        [2_usize],
        "a chain inside a product reads its component's type"
    );
    assert_accepted(&judged(&module, &mut arena));
}

/// #815: the printer writes `+{Unit, Unit}` as `Bool` and a match on it with
/// sum patterns; before the fix a match read summands only off a written
/// sum, so a sum pattern under a stated `Bool` was refused as unannotated
/// and the printed body did not read back.
#[test]
fn a_sum_pattern_reads_bool_as_its_sum_815()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(concat!(
            "def braced(b : +{Unit, Unit}) -> -F +{Unit, Unit} { case b { +{.0 = u} => return +{.1 = u}, +{.1 = u} => return +{.0 = u} } }\n",
            "def atom(b : Bool) -> -F Bool { case b { +{.0 = u} => return +{.1 = u}, +{.1 = u} => return +{.0 = u} } }\n",
            "def past(b : Bool) -> -F Integer { case b { +{.2 = u} => return 0, _ => return 1 } }\n",
            "def bracedLambda : +U (+{Unit, Unit} -> -F Bool) ;\n",
            "def bracedLambda = thunk { fn (b) { case b { +{.0 = u} => return +{.1 = u}, +{.1 = u} => return +{.0 = u} } } } ;\n",
            "def atomLambda : +U (Bool -> -F Bool) ;\n",
            "def atomLambda = thunk { fn (b) { case b { +{.0 = u} => return +{.1 = u}, +{.1 = u} => return +{.0 = u} } } } ;\n",
        )),
        &mut arena,
    );
    assert_eq!(
        gandr_core_term::equal_certificate_syntax(
            &arena,
            body_named(&module, SurfaceName::from("braced")),
            body_named(&module, SurfaceName::from("atom")),
        ),
        gandr_core_term::CertificateEquality::Equal,
        "a match cases on `Bool` as on the sum it stands for"
    );
    assert_eq!(
        gandr_core_term::equal_certificate_syntax(
            &arena,
            body_named(&module, SurfaceName::from("bracedLambda")),
            body_named(&module, SurfaceName::from("atomLambda")),
        ),
        gandr_core_term::CertificateEquality::Equal,
        "and a lambda under a separate signature reads its arrow's `Bool`"
    );
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("past")),
            LoweringRefusal::MalformedForm {
                form: FormName::LABELLED_SUM_PATTERN,
                ..
            }
        ),
        "an index past `Bool`'s two summands names none"
    );
}

/// #1169: the printer writes a case on a boolean as indexed sum patterns, and
/// a scrutinee bound by `run` states no type; before the fix such arms were
/// refused as unannotated, so the printed body did not read back. Indexed arms
/// covering every summand between them settle the sum they inject into.
#[test]
fn indexed_arms_settle_their_sum_1169()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(concat!(
            "def written(c : Integer) -> -F Integer { run b <- c < 128 ; case b { true => return 1, false => return 2 } }\n",
            "def printed(c : Integer) -> -F Integer { run b <- c < 128 ; case b { +{.0 = u} => return 1, +{.1 = u} => return 2 } }\n",
            "def pick(n : Integer) -> -F +{Unit, Unit, Unit} { return +{.2 = unit} }\n",
            "def three(c : Integer) -> -F Integer { run s <- pick(c) ; case s { +{.1 = u} => return 1, +{.0 = u} => return 0, +{.2 = u} => return 2 } }\n",
        )),
        &mut arena,
    );
    assert_eq!(
        gandr_core_term::equal_certificate_syntax(
            &arena,
            body_named(&module, SurfaceName::from("written")),
            body_named(&module, SurfaceName::from("printed")),
        ),
        gandr_core_term::CertificateEquality::Equal,
        "the printed arms read back as the case the boolean arms are"
    );
    assert_accepted(&judged(&module, &mut arena));

    let mut arena = CoreArena::new();
    let refused = lowered(
        SourceText::from(concat!(
            "def wild(c : Integer) -> -F Integer { run b <- c < 128 ; case b { +{.0 = u} => return 1, _ => return 2 } }\n",
            "def gap(c : Integer) -> -F Integer { run b <- c < 128 ; case b { +{.1 = u} => return 1 } }\n",
            "def nested(c : Integer) -> -F Integer { run b <- c < 128 ; case (b, c) { (+{.0 = u}, x) => return 1, (+{.1 = u}, x) => return 2 } }\n",
        )),
        &mut arena,
    );
    for name in ["wild", "gap", "nested"] {
        assert!(
            matches!(
                refusal_of(&refused, SurfaceName::from(name)),
                LoweringRefusal::OutOfFragment {
                    boundary: FragmentBoundary::Unannotated,
                    ..
                }
            ),
            "`{name}`: arms that do not settle the sum stay unannotated: {:?}",
            refusal_of(&refused, SurfaceName::from(name))
        );
    }
}

#[test]
fn a_loop_mints_the_words_at_its_point()
{
    use gandr_core_term::PresentedRule;
    use gandr_core_term::RuleNode;
    use gandr_core_term::RuleVariable;

    use crate::module::Role;
    let mut arena = CoreArena::new();
    let source = "data Circle : Type {\n  Base : Circle;\n  Next : (x : Circle) --> Circle;\n  loop : Next(Base) <-> Next(Base);\n  turn : Next(Base) <-> Next(Base);\n}\ndata Flag : Type { On : Flag; }\n";
    let module = lowered(SourceText::from(source), &mut arena);
    let [ref circle, ref words, ref looped, ref turned, ref flag] = *module.declarations()
    else {
        panic!(
            "the family, its words, a binding per loop, then the next family: {:?}",
            module.declarations()
        );
    };
    assert_eq!(words.role(), Role::Words);
    assert_eq!(
        [looped.name(), turned.name(), flag.name()],
        ["loop", "turn", "Flag"].map(SurfaceName::from),
        "each loop is bound by its name, after the words its letter is in"
    );
    let (DeclarationOutcome::Data(family), DeclarationOutcome::Data(minted)) =
        (circle.outcome(), words.outcome())
    else {
        panic!("the family and its words lower to signatures");
    };
    let (Maybe::Present(family), Maybe::Present(minted)) =
        (module.data(family), module.data(minted))
    else {
        panic!("each index names a signature");
    };
    assert!(
        family.presentation().rules().is_empty() && family.presentation().cells().is_none(),
        "the family itself stays free: its loops are no constructors"
    );
    assert_eq!(
        minted
            .constructors()
            .iter()
            .map(Vec::len)
            .collect::<Vec<_>>(),
        [0_usize, 1, 1, 1, 1],
        "the empty word, then a letter and its inverse per loop, each a cons"
    );
    assert_eq!(
        module.constructors(match words.outcome() {
            DeclarationOutcome::Data(index) => index,
            DeclarationOutcome::Completed { .. }
            | DeclarationOutcome::Uncompleted { .. }
            | DeclarationOutcome::Bodied { .. }
            | DeclarationOutcome::Codata(_)
            | DeclarationOutcome::Abstract(_)
            | DeclarationOutcome::World
            | DeclarationOutcome::Refused(_) => panic!("the words are data"),
        }),
        ["here", "loop", "back(loop)", "turn", "back(turn)"].map(String::from),
        "each constructor is named as the printer writes it"
    );
    let Some(cells) = minted.presentation().cells()
    else {
        panic!("the words carry their cells");
    };
    let c = |tag: usize| RuleNode::Constructor(ConstructorTag::from(tag));
    let x = RuleNode::Variable(RuleVariable::from(0_u32));
    assert_eq!(cells.sort(), circle.constant());
    assert_eq!(
        cells.point(),
        [c(1), c(0)],
        "both loops are at `Next(Base)`"
    );
    assert_eq!(
        minted.presentation().rules(),
        [
            PresentedRule::new([c(1), c(2), x].into(), [x].into()),
            PresentedRule::new([c(2), c(1), x].into(), [x].into()),
            PresentedRule::new([c(3), c(4), x].into(), [x].into()),
            PresentedRule::new([c(4), c(3), x].into(), [x].into()),
        ],
        "two cancellations per loop, the letter first in the first"
    );
    for (generator, bound) in [looped, turned].into_iter().enumerate() {
        let DeclarationOutcome::Completed {
            declared_type,
            body,
        } = bound.outcome()
        else {
            panic!("`{}` is bound with its type", bound.name());
        };
        let Some(&ValueType::Path { left, right, .. }) = arena.value_type(declared_type)
        else {
            panic!("`{}` is a path", bound.name());
        };
        assert_eq!(left, right, "a loop is a path from its point to itself");
        let Some(&Value::Constructor {
            tag, ref fields, ..
        }) = arena.value(body)
        else {
            panic!("`{}` is a word", bound.name());
        };
        assert_eq!(
            usize::from(tag),
            generator.saturating_mul(2).saturating_add(1),
            "`{}` is its own letter",
            bound.name()
        );
        let [rest] = **fields
        else {
            panic!("a letter conses onto one word");
        };
        assert!(
            matches!(arena.value(rest), Some(&Value::Constructor { tag, ref fields, .. }) if usize::from(tag) == 0 && fields.is_empty()),
            "the letter conses onto the empty word"
        );
    }
    let sides = module
        .origins()
        .labels()
        .iter()
        .filter(|label| {
            matches!(label.labelled, crate::origin::Labelled::ValueType { ty, .. }
                if matches!(arena.value_type(ty), Some(&ValueType::Data { declaration, .. }) if declaration == circle.constant()))
        })
        .count();
    assert_eq!(
        sides, 8_usize,
        "each written node of both sides of both cells, `Next(Base)` and `Base`, answers at the family"
    );
    for name in ["loop :", "turn :"] {
        let start = source.find(name).expect("the cell is declared");
        assert!(
            module.origins().labels().iter().any(|label| {
                usize::from(label.span.start()) == start
                    && usize::from(label.span.end()) == start.saturating_add(4)
                    && matches!(label.labelled, crate::origin::Labelled::ValueType { ty, .. }
                        if matches!(arena.value_type(ty), Some(&ValueType::Path { .. })))
            }),
            "`{name}` names its loop where the cell declares it, at the path type"
        );
    }
    assert_accepted(&judged(&module, &mut arena));
}

#[test]
fn a_cell_between_terms_is_a_loop_or_refused_by_name()
{
    let source = "data Directed : Type { One : Directed; loop : One --> One; }\ndata Segment : Type { Start : Segment; End : Segment; seg : Start <-> End; }\ndata Ruled : Type { Two : Ruled; cell : Two ==> Two; }\ndata Swapped : Type { Five : Swapped; cell : Five <=> Five; }\ndata Open : Type { Three : Open; Next : (x : Open) --> Open; cell : Next(x) <-> Next(x); }\ndata Indexed(a : Type) : Type { Four : Indexed(a); cell : Four <-> Four; }\n";
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source), &mut arena);
    let spelled = |refusal: &LoweringRefusal<'_>| {
        let Maybe::Present(span) = refusal.span()
        else {
            panic!("the refusal is located: {refusal:?}");
        };
        source
            .get(usize::from(span.start()) .. usize::from(span.end()))
            .unwrap_or_default()
    };
    let directed = refusal_of(&module, SurfaceName::from("Directed"));
    assert!(matches!(directed, LoweringRefusal::DirectedCell { .. }));
    assert_eq!(spelled(&directed), "-->", "at the directed arrow");
    let segment = refusal_of(&module, SurfaceName::from("Segment"));
    assert!(matches!(segment, LoweringRefusal::CellNotALoop { .. }));
    assert_eq!(
        spelled(&segment),
        "seg : Start <-> End",
        "at the whole cell"
    );
    for (name, at) in [
        ("Ruled", "==>"),
        ("Swapped", "<=>"),
        ("Open", "Next(x)"),
        ("Indexed", "cell"),
    ] {
        let refusal = refusal_of(&module, SurfaceName::from(name));
        assert!(
            matches!(refusal, LoweringRefusal::OutOfFragment {
                form: FormName::CELL_MEMBER,
                sort: FragmentSort::Declaration,
                boundary: FragmentBoundary::Unadmitted(crate::Unbuilt::CellMember),
                ..
            }),
            "`{name}` is declined by the cell member's name: {refusal:?}"
        );
        assert_eq!(spelled(&refusal), at, "`{name}` is declined at its fault");
    }
    assert!(
        !module.declarations().iter().any(|declaration| {
            ["loop", "seg", "cell"]
                .map(SurfaceName::from)
                .contains(&declaration.name())
        }),
        "a refused cell binds no name"
    );
}

#[test]
fn only_back_inverts_a_letter()
{
    let source = "data Circle : Type { Base : Circle; loop : Base <-> Base; }\ndef bad : Path(Circle, \
                  Base, Base) ;\ndef bad = here(loop) ∷ loop ;\n";
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source), &mut arena);
    let written = "here(loop) ∷ loop";
    let start = source.find(written).expect("the word is written");
    assert!(
        matches!(
            outcome_of(&module, "bad".into()),
            DeclarationOutcome::Refused(LoweringRefusal::OutOfFragment {
                span,
                boundary: FragmentBoundary::Unadmitted(crate::Unbuilt::InfixForm),
                ..
            }) if usize::from(span.start()) == start
                && usize::from(span.end()) == start.saturating_add(written.len())
        ),
        "a letter called by any head but `back` is no letter, so the cons is no word: {:?}",
        outcome_of(&module, "bad".into())
    );
}

#[test]
fn a_word_conses_its_letters_and_matches_them()
{
    let source = "data Circle : Type { Base : Circle; loop : Base <-> Base; }\ndef empty : Path(Circle, Base, Base) ;\ndef empty = here(Base) ;\ndef word : Path(Circle, Base, Base) ;\ndef word = back(loop) ∷ loop ;\ndef rec size(p : Path(Circle, Base, Base)) -> -F Integer {\n  case p {\n    here => return 0,\n    loop ∷ q => become size[<](q),\n    back(loop) ∷ q => become size[<](q)\n  }\n}\n";
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source), &mut arena);
    let words = module
        .declarations()
        .iter()
        .find(|declaration| declaration.role() == crate::module::Role::Words)
        .map(crate::module::LoweredDeclaration::constant)
        .expect("the circle's loop mints its words");
    let is_words = |datatype| {
        matches!(arena.value_type(datatype), Some(&ValueType::Data { declaration, ref arguments })
            if declaration == words && arguments.is_empty())
    };
    let Some(&Value::Constructor {
        datatype,
        tag,
        ref fields,
    }) = arena.value(body_named(&module, SurfaceName::from("empty")))
    else {
        panic!("`here(Base)` at the loop's point is a word");
    };
    assert!(is_words(datatype));
    assert_eq!(
        (usize::from(tag), fields.len()),
        (0_usize, 0_usize),
        "the empty word"
    );
    let Some(&Value::Constructor {
        datatype,
        tag,
        ref fields,
    }) = arena.value(body_named(&module, SurfaceName::from("word")))
    else {
        panic!("a cons is a word");
    };
    assert!(is_words(datatype));
    assert_eq!(
        (usize::from(tag), fields.len()),
        (2_usize, 1_usize),
        "`back(loop)` is the loop's inverse letter, consed onto one word"
    );
    // No core node holds a letter or the point of an empty word: each is
    // labelled at its type, the inverse letter's name inside it too.
    let labelled = |text: &str, from: usize| {
        let start = source
            .get(from ..)
            .and_then(|rest| rest.find(text))
            .map_or_else(
                || panic!("`{text}` is written"),
                |at| at.saturating_add(from),
            );
        module
            .origins()
            .labels()
            .iter()
            .find(|label| {
                usize::from(label.span.start()) == start
                    && usize::from(label.span.end()) == start.saturating_add(text.len())
            })
            .map(|label| match label.labelled {
                crate::origin::Labelled::ValueType { ty, .. } => arena.value_type(ty).cloned(),
                crate::origin::Labelled::CompType { .. }
                | crate::origin::Labelled::Value(_)
                | crate::origin::Labelled::Endpoint(_)
                | crate::origin::Labelled::Branch { .. }
                | crate::origin::Labelled::Bound(_) => None,
            })
    };
    let after_word = source.find("def word =").expect("the word is written");
    let after_empty = source
        .find("def empty =")
        .expect("the empty word is written");
    for (text, from) in [
        ("back(loop)", after_word),
        ("loop", after_word.saturating_add(16)),
    ] {
        assert!(
            matches!(labelled(text, from), Some(Some(ValueType::Path { left, right, .. })) if left == right),
            "`{text}` answers at the path type at the point"
        );
    }
    assert!(
        matches!(labelled("Base", after_empty), Some(Some(ValueType::Data { arguments, .. })) if arguments.is_empty()),
        "the point of the empty word answers at the family"
    );
    let Some(&Computation::Fixpoint { body, .. }) = arena.computation(tail_of(
        &arena,
        body_named(&module, SurfaceName::from("size")),
    ))
    else {
        panic!("a recursive function is a fixpoint");
    };
    let Some(&Computation::Lambda(cased)) = arena.computation(body)
    else {
        panic!("the fixpoint closes its parameter's lambda");
    };
    let Some(branches) =
        reachable(&arena, cased)
            .into_iter()
            .find_map(|id| match arena.computation(id) {
                Some(&Computation::DataCase { ref branches, .. }) => Some(branches),
                _ => None,
            })
    else {
        panic!("a case over a word is a data case");
    };
    assert_eq!(
        branches.len(),
        3_usize,
        "one branch per constructor: the empty word, the letter and its inverse"
    );
    assert_accepted(&judged(&module, &mut arena));
}

/// A case over the circle reads `loop => e` as the loop's arm, one branch
/// after the point's; a name no loop declares binds, even one a later member
/// of its module spells, which resolving it would refuse as a forward
/// reference; and a loop arm twice, or over a sort its loop is not at, is
/// refused by name.
#[test]
fn a_loop_arm_follows_the_constructors_branches()
{
    let source = "data Circle : Type { Base : Circle; loop : Base <-> Base; }\ndata Nat : Type { Z : Nat; S : (n : Nat) --> Nat; }\ndef invLooper(x : Circle) -> -F Circle {\n  case x {\n    Base => Base,\n    loop => back(loop)\n  }\n}\nmodule Late {\n  def kept(x : Circle) -> -F Circle {\n    case x {\n      later => later\n    }\n  }\n  def later : Circle ;\n  def later = Base ;\n}\ndef twice(x : Circle) -> -F Circle {\n  case x {\n    Base => Base,\n    loop => loop,\n    loop => back(loop)\n  }\n}\ndef astray(n : Nat) -> -F Nat {\n  case n {\n    Z => Z,\n    S(m) => m,\n    loop => Z\n  }\n}\n";
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source), &mut arena);
    let Some(Computation::DataCase { branches, .. }) = arena
        .computation(tail_of(
            &arena,
            body_named(&module, SurfaceName::from("invLooper")),
        ))
        .cloned()
    else {
        panic!("`invLooper` cases on its argument");
    };
    assert_eq!(
        branches.len(),
        2_usize,
        "the point's branch, then the loop's arm"
    );
    let Some(&Computation::PathTransport { value, .. }) = arena.computation(branches[1])
    else {
        panic!(
            "the arm binds nothing and answers `back(loop)`, the transport it derives: {:?}",
            arena.computation(branches[1])
        );
    };
    assert!(
        matches!(
            arena.value(value),
            Some(&Value::Here(at)) if matches!(arena.value(at), Some(Value::Constructor { fields, .. }) if fields.is_empty())
        ),
        "`back` starts from reflexivity at `Base`, the value the point's branch returns, not at the case at `Base`: {:?}",
        arena.value(value)
    );
    assert!(
        !matches!(
            module
                .declarations()
                .iter()
                .find(|declaration| declaration.name() == SurfaceName::from("kept"))
                .map(crate::module::LoweredDeclaration::outcome),
            Some(DeclarationOutcome::Refused(_)) | None
        ),
        "a pattern spelling a later member, which no loop declares, binds"
    );
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("twice")),
            LoweringRefusal::DuplicateDefinition { .. }
        ),
        "a loop's second arm is refused"
    );
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("astray")),
            LoweringRefusal::OutOfFragment {
                boundary: FragmentBoundary::WrongSort,
                ..
            }
        ),
        "an arm for a loop the scrutinee's sort does not carry is refused"
    );
    let source = "data Eight : Type { Mid : Eight; left : Mid <-> Mid; right : Mid <-> Mid; }\ndef swap(x : Eight) -> -F Eight {\n  case x {\n    Mid => Mid,\n    right => left,\n    left => right\n  }\n}\n";
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source), &mut arena);
    assert!(
        matches!(
            arena.computation(tail_of(&arena, body_named(&module, SurfaceName::from("swap")))),
            Some(Computation::DataCase { branches, .. }) if branches.len() == 3_usize
        ),
        "each loop of one point takes its own arm, the point's branch first"
    );
}
