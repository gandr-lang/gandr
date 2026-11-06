use alloc::string::String;
use alloc::sync::Arc;
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
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::ConstructorTag;
use gandr_core_term::CoreArena;
use gandr_core_term::Sort;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::hole::HoleOrigin;
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
use crate::fixture::listed;
use crate::fixture::listing;
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
use crate::unbuilt::Unbuilt;

/// Three nullary constructors.
const COLOR: &str = "data Color : Type where { | Red : Color | Green : Color | Blue : Color }\n";

/// A family of one parameter.
const MAYBE: &str =
    "data Maybe(a : Type) : Type where { | None : Maybe(a) | Some : (x : a) --> Maybe(a) }\n";

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
#[spec(ensures: |ret| ret
    .declarations()
    .iter()
    .zip(ret.declarations().iter().skip(1))
    .all(|(left, right)| left.constant() < right.constant()))]
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

/// `text`, which `unit` lays out after the prelude, lowered.
///
/// # Specification
/// trivial.
pub(in crate::lower) fn preluded<'source>(
    text: SourceText<'source>,
    unit: &crate::unit::Unit,
    arena: &mut CoreArena,
) -> LoweredModule<'source>
{
    let pbg = grammar();
    let tree = parsed(&pbg, text);
    crate::lower::lower_unit(
        &pbg,
        &tree,
        unit,
        arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
        &mut crate::coincide::Decisions::none(),
    )
    .unwrap()
}

/// Assert that every declaration of `module` checks, a theory forming as
/// data does and a law admitted on the host's word owed as its axiom.
///
/// # Specification
/// trivial.
pub(in crate::lower) fn assert_checked(
    module: &LoweredModule<'_>,
    arena: &mut CoreArena,
)
{
    let report = judged(module, arena);
    assert_eq!(
        report.judged().len(),
        module.declarations().iter().len(),
        "nothing is refused: {:?}",
        module.declarations()
    );
    for (declaration, verdict) in module.declarations().iter().zip(report.judged()) {
        let admitted = declaration.role() == crate::module::Role::Admitted
            && matches!(verdict.verdict(), Verdict::Owed(_));
        assert!(
            admitted || matches!(verdict.verdict(), Verdict::Checked { .. } | Verdict::Data),
            "every declaration checks: {report:?}"
        );
    }
}

/// The checker's verdicts over every declaration of `module` the lowering
/// did not refuse.
///
/// # Specification
/// - requires: `module` was lowered over `arena` and declares no abstract type.
/// - ensures: one verdict per unrefused declaration, in admission order; a law
///   admitted on the host's word stands hosted, as the dispatcher reads it.
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
                    Maybe::Absent(if declaration.role() == crate::module::Role::Admitted {
                        body::Absent::Hosted
                    }
                    else if declaration.role() == crate::module::Role::Discharged {
                        body::Absent::Discharged
                    }
                    else {
                        body::Absent::Hole
                    }),
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
                    .supplied(module.supplies(declaration).to_vec())
                    .resolving(module.models(declaration).to_vec())
                    .obliged(module.handler_laws(declaration).to_vec()),
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
/// - ensures: `root` first, then each reachable computation once per path, a
///   computation a return nests included.
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
            Some(&Computation::ListCase {
                on_nil, on_cons, ..
            }) => pending.extend([on_cons, on_nil]),
            Some(&Computation::Return(value)) => {
                if let Some(&Value::Nested(nested)) = arena.value(value) {
                    pending.push(nested);
                }
            },
            _ => {},
        }
    }

    seen
}

#[test]
fn an_annotation_at_a_statement_is_of_the_wrong_sort()
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
                boundary: FragmentBoundary::WrongSort,
                ..
            }) if usize::from(span.start()) == start
                && usize::from(span.end()) == start.saturating_add(written.len())
        ),
        "an annotation is a value, never a statement, refused as any value there: {:?}",
        outcome_of(&module, "f".into())
    );
}

#[test]
fn a_constructor_is_no_value_inside_its_own_family()
{
    let source = "data T : Type where { | A : T | B : (x : Path[.A = T](A, A)) --> T }\n";
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source), &mut arena);
    let start = source.find("A, A").expect("the endpoint is written");
    assert!(
        matches!(
            outcome_of(&module, "T".into()),
            DeclarationOutcome::Refused(LoweringRefusal::UnresolvedName {
                span,
                name,
            }) if usize::from(span.start()) == start
                && usize::from(span.end()) == start.saturating_add(1)
                && name == "A".into()
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
        SourceText::from(include_str!(
            "tests/fixtures/a-data-declaration-lowers-to-its-signature-module.gandr"
        )),
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
        SourceText::from(include_str!(
            "tests/fixtures/a-presented-family-lowers-its-rules-module.gandr"
        )),
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
        SourceText::from(include_str!(
            "tests/fixtures/a-recursive-family-names-itself-in-its-fields-module.gandr"
        )),
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
const NAT: &str = "data Nat : Type where { | Zero : Nat | Succ : (n : Nat) --> Nat }\n";

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
        include_str!(
            "tests/unformatted/a-recursive-function-closes-a-fixpoint-over-its-staged-parameter.gandr"
        ),
        NAT = NAT
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
        .find("plus[<] n")
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
        include_str!(
            "tests/unformatted/a-parameterless-recursive-tail-binds-its-own-name-1499.gandr"
        ),
        NAT = NAT
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
fn a_recursion_under_an_instance_row_binds_its_own_name_3699()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        include_str!(
            "tests/unformatted/a-recursion-under-an-instance-row-binds-its-own-name-3699.gandr"
        ),
        NAT = NAT
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let (outside, fixpoint) = fixpoint_of(&arena, &module, SurfaceName::from("quiet"));
    assert_eq!(
        outside,
        ParameterAt(0),
        "the scrutinised first parameter leaves none outside the fixpoint"
    );
    assert!(
        matches!(
            arena.computation(fixpoint),
            Some(&Computation::Fixpoint {
                evidence: FixpointEvidence::StructuralDescent,
                ..
            })
        ),
        "`quiet` closes a structural fixpoint over its first parameter: {:?}",
        arena.computation(fixpoint)
    );
    assert_accepted(&judged(&module, &mut arena));
}

#[test]
fn a_recursion_under_an_implicit_telescope_descends_on_its_matched_parameter_3828()
{
    let mut arena = CoreArena::new();
    let source = include_str!(
        "tests/fixtures/a-recursion-under-an-implicit-telescope-descends-on-its-matched-parameter-3828.gandr"
    );
    let module = lowered(SourceText::from(source), &mut arena);
    let (outside, fixpoint) = fixpoint_of(&arena, &module, SurfaceName::from("size"));
    assert_eq!(
        outside,
        ParameterAt(1),
        "the implicit, which the call omits and so passes as the function's own, stands outside \
         the fixpoint"
    );
    assert!(
        matches!(
            arena.computation(fixpoint),
            Some(&Computation::Fixpoint {
                evidence: FixpointEvidence::StructuralDescent,
                ..
            })
        ),
        "`size` closes a structural fixpoint over `xs`: {:?}",
        arena.computation(fixpoint)
    );
    assert_accepted(&judged(&module, &mut arena));
}

#[test]
fn a_definition_descends_on_the_parameter_its_cases_scrutinise()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        "{NAT}def rec plus(m : Nat, n : Nat) -> -F Nat {{ match m {{ | Zero => return n | Succ(p) => plus[<] p (Succ n) }} }}\n"
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
        "{NAT}def rec count(acc : Nat, b : Nat) -> -F Nat {{ match b {{ | Zero => return acc | Succ(p) => count[<] (Succ acc) p }} }}\n"
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
        "{NAT}def rec halve(n : Nat) -> -F Nat {{ match n {{ | Zero => return Zero | Succ(m) => match m {{ | Zero => return Zero | Succ(q) => {{ let h = halve[<] (Succ q); return Succ h }} }} }} }}\n"
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
        "{NAT}def rec both(m : Nat, n : Nat) -> -F Nat {{ match m {{ | Zero => match n {{ | Zero => return Zero | Succ(q) => both[<] m q }} | Succ(p) => both[<] p n }} }}\n"
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

/// #2135: a claim under a match on the staged parameter descends on it,
/// however many matches on other parameters stand between: `paired` walks
/// `xs` and consumes `ys` alongside it, its first call under `match ys`
/// passing `ys` back unchanged, so it stages `xs`, and its second call,
/// under the same match, descends on `xs` as the first does.
#[test]
fn a_claim_under_a_match_on_another_parameter_descends_on_the_staged_one_2135()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        include_str!(
            "tests/unformatted/a-claim-under-a-match-on-another-parameter-descends-on-the-staged-one-2135.gandr"
        ),
        NAT = NAT
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    for name in ["paired", "walked"].map(SurfaceName::from) {
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

/// #3680: a claim under a match on a parameter typed by a decode, inside a
/// match on the code it decodes, staged the decoded parameter, the innermost
/// match's. A decode carries no stage, and `x` is a field of the pair, never
/// below `v`: the case on `c` then left `v` unrefined, refused
/// `ShapeMismatch`. The claim descends on the code, so `size` stages `c`.
#[test]
fn a_claim_under_a_match_on_a_decode_stages_the_code_3680()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        include_str!(
            "tests/unformatted/a-claim-under-a-match-on-a-decode-stages-the-code-3680.gandr"
        ),
        NAT = NAT
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let name = SurfaceName::from("size");
    assert!(
        matches!(
            outcome_of(&module, name),
            DeclarationOutcome::Completed { .. }
        ),
        "`size` lowers: {:?}",
        outcome_of(&module, name)
    );
    assert_accepted(&judged(&module, &mut arena));
}

/// #3087: a descent written in a quoted record type's field stands under the
/// match on the parameter it takes apart, as a bare one does, so it stages
/// that parameter rather than the last, whatever follows it.
#[test]
fn a_descent_inside_a_record_type_stages_its_match_s_parameter_3087()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        include_str!(
            "tests/unformatted/a-descent-inside-a-record-type-stages-its-match-s-parameter-3087.gandr"
        ),
        NAT = NAT
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    for name in ["noPath", "twoParams"].map(SurfaceName::from) {
        assert!(
            matches!(
                outcome_of(&module, name),
                DeclarationOutcome::Completed { .. }
            ),
            "`{name}` lowers: {:?}",
            outcome_of(&module, name)
        );
        let (outside, _fixpoint) = fixpoint_of(&arena, &module, name);
        assert_eq!(outside, ParameterAt(0), "`{name}` stages `p`, its match's");
    }
    assert_accepted(&judged(&module, &mut arena));
}

/// #5291: a lambda among a descent's arguments in a quoted record type reads
/// its body inside the type. The call `h z` in that body stands as the value
/// it returns. So the checker finds no run without a computation around it.
#[test]
fn a_lambda_among_a_descent_s_arguments_reads_its_body_in_the_type_5291()
{
    let mut arena = CoreArena::new();
    let source = include_str!(
        "tests/fixtures/a-lambda-among-a-descent-s-arguments-reads-its-body-in-the-type-5291.gandr"
    );
    let module = lowered(SourceText::from(source), &mut arena);
    assert!(
        matches!(
            outcome_of(&module, SurfaceName::from("fields")),
            DeclarationOutcome::Completed { .. }
        ),
        "`fields` lowers: {:?}",
        outcome_of(&module, SurfaceName::from("fields"))
    );
    assert_accepted(&judged(&module, &mut arena));
}

#[test]
fn an_unapplied_claim_lowers_to_the_self_binder()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        "{NAT}def rec loose(n : Nat) -> -F Nat {{ let held = loose[<]; return n }}\n"
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
        "{NAT}def rec count(n : Nat, m : Nat) -> -F Nat {{ let k = m; match k {{ | Zero => return n | Succ(p) => count[<] n p }} }}\n"
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
        include_str!(
            "tests/unformatted/a-mutual-blocks-recursive-functions-share-one-fixpoint.gandr"
        ),
        NAT = NAT
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

/// #3722: the members of a mutual block each take a parameter after the one
/// they descend on. A call through a sibling stages the caller's matched
/// parameter as a call through itself does, and the joint passes the later
/// parameter on: `size` passes `k` unchanged, and `sizes` passes it an
/// accumulated count.
#[test]
fn a_mutual_block_member_takes_a_parameter_after_its_staged_one_3722()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        include_str!(
            "tests/unformatted/a-mutual-block-member-takes-a-parameter-after-its-staged-one-3722.gandr"
        ),
        NAT = NAT
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    for name in ["size", "sizes"].map(SurfaceName::from) {
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

/// #5036: the members of a mutual block take later parameters that differ,
/// and the first reads its staged parameter in its type. The joint is
/// ascribed a dependent arrow whose result decodes a case over the sum, and
/// the block checks: `count` passes `tally` no later parameter, and `tally`
/// passes `count` a value at the type its staged parameter reads.
#[test]
fn a_mutual_block_member_takes_later_parameters_its_sibling_does_not_5036()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        include_str!(
            "tests/unformatted/a-mutual-block-member-takes-later-parameters-its-sibling-does-not-5036.gandr"
        ),
        NAT = NAT
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    for name in ["count", "tally"].map(SurfaceName::from) {
        assert!(
            matches!(
                outcome_of(&module, name),
                DeclarationOutcome::Completed { .. }
            ),
            "`{name}` lowers: {:?}",
            outcome_of(&module, name)
        );
    }
    let Some(&Value::Thunk(member)) = arena.value(body_named(&module, SurfaceName::from("count")))
    else {
        panic!("the member lowers to a thunk");
    };
    let Some(&Computation::Lambda(call)) = arena.computation(member)
    else {
        panic!("the member is a lambda over its parameter");
    };
    let Some(&Computation::Application(joint, _)) = arena.computation(call)
    else {
        panic!("the member calls the joint");
    };
    let Some(&Computation::Ascribe { ty, .. }) = arena.computation(joint)
    else {
        panic!("the joint is ascribed");
    };
    assert!(
        matches!(arena.comp_type(ty), Some(&gandr_core_term::CompType::Pi { codomain, .. })
            if matches!(arena.comp_type(codomain), Some(&gandr_core_term::CompType::Element { code, .. })
                if matches!(arena.value(code), Some(&Value::Returned(_))))),
        "the joint's result decodes a case over the sum: {:?}",
        arena.comp_type(ty)
    );
    assert_accepted(&judged(&module, &mut arena));
    // A call through a sibling is held to the sibling's parameters, not the
    // caller's: `tally` passes `count` one argument, and `count` takes two.
    let mut arena = CoreArena::new();
    let short = alloc::format!(
        include_str!(
            "tests/unformatted/a-mutual-block-member-takes-later-parameters-its-sibling-does-not-5036-short.gandr"
        ),
        NAT = NAT
    );
    let module = lowered(SourceText::from(short.as_str()), &mut arena);
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("tally")),
            LoweringRefusal::OutOfFragment {
                boundary: FragmentBoundary::Arity(count),
                ..
            } if usize::from(count) == 1
        ),
        "a call passing its sibling too few arguments is refused: {:?}",
        refusal_of(&module, SurfaceName::from("tally"))
    );
    assert!(
        matches!(
            outcome_of(&module, SurfaceName::from("count")),
            DeclarationOutcome::Completed { .. }
        ),
        "the caller passing its sibling's parameters lowers: {:?}",
        outcome_of(&module, SurfaceName::from("count"))
    );
}

/// #3880: the members of a mutual block return different types. The tree's
/// copy returns a tree and the forest's returns a forest, so the joint is
/// ascribed a dependent arrow whose result decodes a case over the sum, and
/// the block checks.
#[test]
fn a_mutual_block_whose_members_return_different_types_checks_3880()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        include_str!(
            "tests/unformatted/a-mutual-block-whose-members-return-different-types-checks-3880.gandr"
        ),
        NAT = NAT
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    for name in ["bumpTree", "bumpForest"].map(SurfaceName::from) {
        assert!(
            matches!(
                outcome_of(&module, name),
                DeclarationOutcome::Completed { .. }
            ),
            "`{name}` lowers: {:?}",
            outcome_of(&module, name)
        );
    }
    let Some(&Value::Thunk(member)) =
        arena.value(body_named(&module, SurfaceName::from("bumpTree")))
    else {
        panic!("the member lowers to a thunk");
    };
    let Some(&Computation::Lambda(call)) = arena.computation(member)
    else {
        panic!("the member is a lambda over its parameter");
    };
    let Some(&Computation::Application(joint, _)) = arena.computation(call)
    else {
        panic!("the member calls the joint");
    };
    let Some(&Computation::Ascribe { ty, .. }) = arena.computation(joint)
    else {
        panic!("the joint is ascribed");
    };
    assert!(
        matches!(arena.comp_type(ty), Some(&gandr_core_term::CompType::Pi { codomain, .. })
            if matches!(arena.comp_type(codomain), Some(&gandr_core_term::CompType::Element { code, .. })
                if matches!(arena.value(code), Some(&Value::Returned(_))))),
        "the joint's result decodes a case over the sum: {:?}",
        arena.comp_type(ty)
    );
    assert_accepted(&judged(&module, &mut arena));
}

/// A member of a mutual block whose sibling the lowering refused calls the
/// sibling's declaration, so the checker meets a constant it has no type for
/// rather than an injection into a joint that never formed (#2340): refused
/// at its head or in its body, the sibling's refusal is the one reported, and
/// the member's is its consequence.
#[test]
fn a_member_beside_a_refused_sibling_calls_its_declaration_2340()
{
    let even = include_str!(
        "tests/unformatted/a-member-beside-a-refused-sibling-calls-its-declaration-2340-even.gandr"
    );
    for odd in [
        include_str!(
            "tests/unformatted/a-member-beside-a-refused-sibling-calls-its-declaration-2340-2.gandr"
        ),
        include_str!(
            "tests/unformatted/a-member-beside-a-refused-sibling-calls-its-declaration-2340-1.gandr"
        ),
    ] {
        let mut arena = CoreArena::new();
        let source = alloc::format!(
            include_str!(
                "tests/unformatted/a-member-beside-a-refused-sibling-calls-its-declaration-2340-3.gandr"
            ),
            NAT = NAT,
            even = even,
            odd = odd
        );
        let module = lowered(SourceText::from(source.as_str()), &mut arena);
        assert!(
            matches!(
                refusal_of(&module, SurfaceName::from("odd")),
                LoweringRefusal::MalformedForm { .. } | LoweringRefusal::UnresolvedName { .. }
            ),
            "the sibling is refused where it was written: {odd}"
        );
        let constant = |name: &str| {
            module
                .declarations()
                .iter()
                .find(|declaration| declaration.name() == SurfaceName::from(name))
                .map(crate::module::LoweredDeclaration::constant)
        };
        let refused = constant("odd");
        let report = judged(&module, &mut arena);
        let verdict = report
            .judged()
            .iter()
            .find(|judged| Some(judged.constant()) == constant("even"))
            .map(gandr_core_checker::Judged::verdict);
        assert!(
            matches!(
                verdict,
                Some(Verdict::Refused(CheckRefusal::UnknownConstant { constant, .. }))
                    if Some(constant) == refused
            ),
            "the member names its refused sibling's declaration: {verdict:?}"
        );
    }
}

#[test]
fn a_decoders_descent_in_its_returned_type_unquotes_the_fixpoint()
{
    let mut arena = CoreArena::new();
    let source = include_str!(
        "tests/fixtures/a-decoders-descent-in-its-returned-type-unquotes-the-fixpoint.gandr"
    );
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
        include_str!(
            "tests/unformatted/an-unmarked-self-reference-is-refused-with-its-claim.gandr"
        ),
        NAT = NAT
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let Some(start) = source.find("bare p")
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
        include_str!(
            "tests/unformatted/a-recursive-call-passes-its-leading-parameters-unchanged.gandr"
        ),
        NAT = NAT
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
            span: at("n n }", 1_usize),
            form: FormName::from(gandr_surface_grammar::NamedKind("call_expression")),
            sort: FragmentSort::Computation,
            boundary: FragmentBoundary::NonUniform,
        },
        "a kept parameter's spelling naming the arm's binder varies it"
    );
    assert_eq!(
        refusal_of(&module, SurfaceName::from("short")),
        LoweringRefusal::OutOfFragment {
            span: at("short[<] p", 10_usize),
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
    let stream = "codata Stream(a : Type) : Type[-] where { head : a; tail : Stream(a); }\n";
    let source = alloc::format!(
        "{NAT}{stream}def rec upward(n : Nat, m : Nat) -> Stream(Nat) {{ &{{.head => return n, .tail => upward[>] m (Succ n)}} }}\n"
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
        include_str!(
            "tests/unformatted/a-productive-call-is-the-whole-arm-of-a-copattern-block.gandr"
        ),
        NAT = NAT,
        stream = stream
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
        include_str!("tests/unformatted/a-descent-claim-names-its-own-function-873.gandr"),
        NAT = NAT
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
fn a_reserved_claim_under_a_head_that_is_no_name_marks_the_whole_instantiation_3811()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!("{NAT}def joined = #[1]  [2] ;\n");
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let start = source.find("#[1]  [2]").unwrap_or_default();

    assert_eq!(
        refusal_of(&module, SurfaceName::from("joined")),
        LoweringRefusal::OutOfFragment {
            span: crate::fixture::span(
                gandr_surface_syntax::ByteOffset::from(start),
                gandr_surface_syntax::ByteOffset::from(start.saturating_add("#[1]  [2]".len())),
            ),
            form: FormName::INSTANTIATION,
            sort: FragmentSort::Value,
            boundary: FragmentBoundary::Reserved(crate::Unbuilt::RecursiveClaim),
        },
        "an instantiation whose head is no name is refused whole, not at its resident"
    );
}

/// A head that names nothing is the mistake, whatever its resident. A keyword
/// misspelt before a bracket reads as a name over a resident, and the refusal
/// marks the name (#5303). Under a head that names a declaration, the resident
/// that is no claim keeps the refusal (#3811).
#[test]
fn a_head_naming_nothing_over_a_resident_is_unresolved_5303()
{
    let mut arena = CoreArena::new();
    let source = include_str!(
        "tests/fixtures/a-head-naming-nothing-over-a-resident-is-unresolved-5303.gandr"
    );
    let module = lowered(SourceText::from(source), &mut arena);
    let at = |text: &str, offset: usize, length: usize| {
        let start = source.find(text).unwrap_or_default().saturating_add(offset);
        crate::fixture::span(
            gandr_surface_syntax::ByteOffset::from(start),
            gandr_surface_syntax::ByteOffset::from(start.saturating_add(length)),
        )
    };

    assert_eq!(
        refusal_of(&module, SurfaceName::from("misspelt")),
        LoweringRefusal::UnresolvedName {
            span: at("migrat[2]", 0, "migrat".len()),
            name: SurfaceName::from("migrat"),
        },
        "a head that names nothing is unresolved before its resident is read"
    );
    assert_eq!(
        refusal_of(&module, SurfaceName::from("resolved")),
        LoweringRefusal::OutOfFragment {
            span: at("known[2]", "known[".len(), 1),
            form: FormName::INSTANTIATION,
            sort: FragmentSort::Value,
            boundary: FragmentBoundary::Reserved(crate::Unbuilt::RecursiveClaim),
        },
        "a head that names a declaration leaves the refusal at its resident"
    );
}

#[test]
fn a_data_family_named_where_a_value_is_read_is_quoted()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        include_str!("tests/unformatted/a-data-family-named-where-a-value-is-read-is-quoted.gandr"),
        MAYBE = MAYBE,
        NAT = NAT
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

/// A data family applied where a value is read is the family's type over its
/// arguments: passed for a type parameter and as a definition of `Type`,
/// never a constructor applied to nothing (#2512).
#[test]
fn a_data_family_applied_where_a_value_is_read_is_quoted_2512()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        include_str!(
            "tests/unformatted/a-data-family-applied-where-a-value-is-read-is-quoted-2512.gandr"
        ),
        MAYBE = MAYBE,
        NAT = NAT
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let Some(&Value::Quote(quoted)) = arena.value(body_named(&module, SurfaceName::from("row")))
    else {
        panic!("the applied family is quoted");
    };
    let Some(&ValueType::Data {
        declaration,
        ref arguments,
    }) = arena.value_type(quoted)
    else {
        panic!("the code is a data type");
    };
    assert_eq!(
        declaration,
        ConstantIndex::from(1_usize),
        "the code is the applied family's own type"
    );
    assert_eq!(arguments.len(), 1_usize, "over the one argument written");
    assert_accepted(&judged(&module, &mut arena));
}

/// Each family applied to an index is declined, and keeps its own form's key,
/// the form that carries its refusal (#1204).
#[test]
fn an_indexed_generator_is_declined()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/an-indexed-generator-is-declined-module.gandr"
        )),
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
        SourceText::from(include_str!(
            "tests/fixtures/an-indexed-family-lowers-its-indices-module.gandr"
        )),
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

/// A header's named index telescope lowers each index under the parameters
/// and the indices before it, so the type of a later index reads an earlier
/// one by its name; an unnamed kind reads its indices the same way. The
/// checker admits the family and refuses a constructor stating its indices
/// out of the telescope's order (#4022).
#[test]
fn a_named_index_telescope_lowers_its_dependencies_4022()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/a-named-index-telescope-lowers-its-dependencies-4022-module.gandr"
        )),
        &mut arena,
    );
    let signature = |name: &str| {
        let DeclarationOutcome::Data(index) = outcome_of(&module, SurfaceName::from(name))
        else {
            panic!("`{name}` lowers to its signature");
        };
        let Maybe::Present(signature) = module.data(index)
        else {
            panic!("`{name}`'s index names a signature");
        };
        signature
    };
    let sized = signature("Sized");
    let &[length, vector] = sized.indices()
    else {
        panic!("the telescope reads two indices: {:?}", sized.indices());
    };
    assert!(
        matches!(arena.value_type(length), Some(&ValueType::Data { declaration, ref arguments })
            if declaration == ConstantIndex::from(0_usize) && arguments.is_empty()),
        "the first index is a length"
    );
    let Some(&ValueType::Data {
        declaration,
        ref arguments,
    }) = arena.value_type(vector)
    else {
        panic!("the second index is a vector");
    };
    assert_eq!(declaration, ConstantIndex::from(1_usize));
    assert_eq!(
        arguments
            .iter()
            .map(|&argument| arena.value(argument).cloned())
            .collect::<Vec<_>>(),
        [
            Some(variable(DeBruijnIndex::from(1_u32))),
            Some(variable(DeBruijnIndex::from(0_u32)))
        ],
        "`Vec(a, n)` reads the parameter past the length, and the length by its name"
    );
    let twice = signature("Twice");
    let &[first, second] = twice.indices()
    else {
        panic!("two unnamed indices");
    };
    let read = |ty| match arena.value_type(ty) {
        Some(&ValueType::Element { code, .. }) => arena.value(code).cloned(),
        _ => None,
    };
    assert_eq!(
        (read(first), read(second)),
        (
            Some(variable(DeBruijnIndex::from(0_u32))),
            Some(variable(DeBruijnIndex::from(1_u32)))
        ),
        "`a -> a -> Type` reads `a` under the parameter, then past the first index"
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
        Verdict::Data,
        Verdict::Data,
        Verdict::Refused(ref turned),
    ] = *verdicts
    else {
        panic!("the families over a telescope and a kind check: {report:?}");
    };
    assert!(
        matches!(turned, gandr_core_checker::CheckRefusal::TypeMismatch(_)),
        "a vector stated where its length stands is refused: {turned:?}"
    );
}

/// A constructor written at a family's index takes the index's type as its
/// classifier: in a definition's signature, under the arguments before it,
/// and in a generator's result, under the indices the result states before it
/// and the family's own parameters past the generator's fields. The checker
/// admits each family and refuses the two whose stated index is not of the
/// index's type (#4027).
#[test]
fn a_constructor_at_a_family_s_index_takes_the_index_s_type_4027()
{
    let source = include_str!(
        "tests/fixtures/a-constructor-at-a-family-s-index-takes-the-index-s-type-4027.gandr"
    );
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source), &mut arena);
    let report = judged(&module, &mut arena);
    let verdicts: Vec<Verdict> = report
        .judged()
        .iter()
        .map(gandr_core_checker::Judged::verdict)
        .collect();
    let [
        Verdict::Data,
        Verdict::Data,
        Verdict::Data,
        Verdict::Checked { .. },
        Verdict::Data,
        Verdict::Data,
        Verdict::Refused(ref past),
        Verdict::Data,
        Verdict::Refused(ref field),
    ] = *verdicts
    else {
        panic!("each family and `r` check, the two misstated indices refuse: {report:?}");
    };
    assert!(
        matches!(past, gandr_core_checker::CheckRefusal::TypeMismatch(_)),
        "`FZ(n)` is no index below `n`: {past:?}"
    );
    assert!(
        matches!(field, gandr_core_checker::CheckRefusal::TypeMismatch(_)),
        "`FZ(k)` is no index below the parameter's successor: {field:?}"
    );
}

/// An indexed family presenting a rule over its constructors is declined over
/// that rule's two sides, before either checker reads it (#2865); a rule over
/// an operation rewrites a call, not the family's terms, and the family keeps
/// its indices.
#[test]
fn an_indexed_family_presents_no_rule_2865()
{
    let source = include_str!("tests/fixtures/an-indexed-family-presents-no-rule-2865.gandr");
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source), &mut arena);
    let written = |span: ByteSpan| source.get(usize::from(span.start()) .. usize::from(span.end()));
    let LoweringRefusal::OutOfFragment {
        span,
        form: FormName::RULE_MEMBER,
        sort: FragmentSort::Declaration,
        boundary: FragmentBoundary::Indexed,
    } = refusal_of(&module, SurfaceName::from("Prog"))
    else {
        panic!("a family indexed by `N` presents no rule over its constructors");
    };
    assert_eq!(
        written(span),
        Some("Tell s (Tell u k) <=> Tell u k"),
        "the refusal stands over the rule's two sides"
    );
    let DeclarationOutcome::Data(skip) = outcome_of(&module, SurfaceName::from("Skip"))
    else {
        panic!("a rule over an operation leaves the family to lower");
    };
    let Maybe::Present(skip) = module.data(skip)
    else {
        panic!("the index names a signature");
    };
    assert_eq!(skip.indices().len(), 1_usize, "`Skip` keeps its index");
    assert!(
        skip.presentation().rules().is_empty(),
        "the operation's rule rewrites a call, not the family's terms"
    );
}

#[test]
fn each_data_type_and_stated_index_is_framed_under_its_telescope_931()
{
    let source = include_str!(
        "tests/fixtures/each-data-type-and-stated-index-is-framed-under-its-telescope-931.gandr"
    );
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
            ("Nat", Vec::new()),
            ("Type", Vec::new()),
            ("Nat", Vec::from(["a"])),
            ("Z", Vec::from(["a"])),
            ("Nat", Vec::from(["a"])),
            ("a", Vec::from(["a", "n"])),
            ("Vec(a, n)", Vec::from(["a", "n", "x"])),
            ("S(n)", Vec::from(["a", "n", "x", "xs"]))
        ],
        "a parameter's type is read under the parameters before it, an index's \
         under the parameters, a field's under the parameters and the fields \
         before it, and each stated index under the parameters and all its \
         constructor's fields"
    );
}

#[test]
fn operation_and_rule_members_are_left_to_the_description_route()
{
    let source = include_str!(
        "tests/fixtures/operation-and-rule-members-are-left-to-the-description-route.gandr"
    );
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source), &mut arena);
    let [operated, retired, held] = *module.declarations().iter().collect::<Vec<_>>()
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
        Some("op stale : (x : NatRetired) --> NatRetired")
    );
    assert_eq!(module.cells().diagnostics, []);
    assert_accepted(&judged(&module, &mut arena));
}

#[test]
fn an_attribute_block_decorates_the_data_declaration_after_it()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/an-attribute-block-decorates-the-data-declaration-after-it-module.gandr"
        )),
        &mut arena,
    );
    let [family, value] = *module.declarations().iter().collect::<Vec<_>>()
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
        SourceText::from(include_str!(
            "tests/fixtures/a-constructor-named-twice-is-refused-module.gandr"
        )),
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
        ("data Integer : Type where { | I : Integer }\n", "Integer"),
        ("data Unit : Type where { | U : Unit }\n", "Unit"),
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
        include_str!("tests/unformatted/a-constructor-applies-to-its-fields.gandr"),
        COLOR = COLOR
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let Some(&Value::Constructor {
        datatype,
        tag,
        ref fields,
        ..
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

/// A multi-output constructor is one port per output, each an ordinary
/// constructor over the shared inputs at consecutive tags; `C(a).l` is the
/// port `l` applied to `a`, `C(a)` the record of its ports, and the two ports
/// of one input stay apart.
#[test]
fn a_multi_output_constructor_is_one_port_per_output()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!("fixture/ports.gandr")),
        &mut arena,
    );
    let port = |value: ValueId| match arena.value(value) {
        Some(&Value::Constructor {
            tag, ref fields, ..
        }) => (tag, fields.clone()),
        other => panic!("a port is a constructor value: {other:?}"),
    };
    let (tag, fields) = port(body_named(&module, SurfaceName::from("left")));
    assert_eq!(
        tag,
        ConstructorTag::from(1_usize),
        "`Share.left` follows `Lit`"
    );
    assert_eq!(
        fields.len(),
        1_usize,
        "a port takes the constructor's inputs"
    );
    let (grouped, grouped_fields) = port(body_named(&module, SurfaceName::from("grouped")));
    assert_eq!(
        (grouped, grouped_fields.len()),
        (ConstructorTag::from(1_usize), 1_usize),
        "a port selected through parentheses is the port selected without them"
    );
    let (tag, fields) = port(body_named(&module, SurfaceName::from("both")));
    assert_eq!(
        tag,
        ConstructorTag::from(3_usize),
        "`Add` follows both ports"
    );
    let tags: Vec<ConstructorTag> = fields.iter().map(|&field| port(field).0).collect();
    assert_eq!(
        tags,
        [1_usize, 2_usize].map(ConstructorTag::from),
        "`.left` and `.right` are the two ports"
    );
    let Some(&Value::Record(ref record)) =
        arena.value(body_named(&module, SurfaceName::from("whole")))
    else {
        panic!("a constructor with no output named is a record");
    };
    let labelled: Vec<(&str, ConstructorTag)> = record
        .iter()
        .map(|(label, &value)| (label.as_ref(), port(value).0))
        .collect();
    assert_eq!(
        labelled,
        [("left", 1_usize), ("right", 2_usize)]
            .map(|(label, tag)| (label, ConstructorTag::from(tag))),
        "the record holds each port at its output's label"
    );
    let report = judged(&module, &mut arena);
    for name in [
        "Expr",
        "left",
        "both",
        "apart",
        "whole",
        "unpacked",
        "measured",
        "Tree",
        "Pair",
        "first",
        "doubled",
        "mismatched",
    ] {
        let Some(declaration) = module
            .declarations()
            .iter()
            .find(|declaration| declaration.name() == SurfaceName::from(name))
        else {
            panic!("`{name}` is declared");
        };
        let Some(judged) = report
            .judged()
            .iter()
            .find(|judged| judged.constant() == declaration.constant())
        else {
            panic!("`{name}` is judged");
        };
        assert_eq!(
            matches!(
                judged.verdict(),
                Verdict::Data | Verdict::Checked { .. } | Verdict::Synthesised { .. }
            ),
            name != "apart" && name != "mismatched",
            "`{name}`: only the path between the two ports and a record type giving the ports \
             different arguments are rejected, {:?}",
            judged.verdict()
        );
    }
    assert!(matches!(
        refusal_of(&module, SurfaceName::from("middle")),
        LoweringRefusal::PartialField { field, .. } if field == SurfaceName::from("middle")
    ));
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("partial")),
            LoweringRefusal::NonExhaustiveMatch { .. }
        ),
        "a match missing the `right` port is refused"
    );
    for (name, feature) in [
        ("matched", Unbuilt::PortPattern),
        ("Buffer", Unbuilt::LinearPorts),
    ] {
        assert!(
            matches!(
                refusal_of(&module, SurfaceName::from(name)),
                LoweringRefusal::OutOfFragment {
                    boundary: FragmentBoundary::Unadmitted(refused),
                    ..
                } if refused == feature
            ),
            "`{name}` is refused by name"
        );
    }
    assert!(matches!(
        refusal_of(&module, SurfaceName::from("Twice")),
        LoweringRefusal::DuplicateDefinition { name, .. } if name == SurfaceName::from("out")
    ));
}

/// A constructor under a classifier of another family of one shape keeps its
/// own family and stands bare at the type written for it, which the checker
/// refuses: the found type is the constructor's own family, over the
/// classifier's arguments. Under its own family's classifier it checks
/// (#2075, #5400).
#[test]
fn a_constructor_keeps_its_family_under_another_s_classifier_2075()
{
    let mut arena = CoreArena::new();
    let source = include_str!(
        "tests/fixtures/a-constructor-keeps-its-family-under-another-s-classifier-2075.gandr"
    );
    let module = lowered(SourceText::from(source), &mut arena);
    for (name, family, classifier) in [
        ("foreign", 0_usize, 1_usize),
        ("signed", 2, 3),
        ("own", 0, 0),
    ] {
        let Some(&Value::Constructor {
            family: named,
            datatype,
            tag,
            ..
        }) = arena.value(body_named(&module, SurfaceName::from(name)))
        else {
            panic!("`{name}` stands bare at its classifier, with no ascription");
        };
        assert_eq!(
            (named, tag),
            (ConstantIndex::from(family), ConstructorTag::from(0_usize)),
            "`{name}` names its own family, at its own tag"
        );
        assert!(
            matches!(
                arena.value_type(datatype),
                Some(&ValueType::Data { declaration, .. })
                    if declaration == ConstantIndex::from(classifier)
            ),
            "`{name}` stands at the type the source wrote for it"
        );
    }
    let report = judged(&module, &mut arena);
    let verdicts: Vec<Verdict> = report
        .judged()
        .iter()
        .map(gandr_core_checker::Judged::verdict)
        .collect();
    let [
        Verdict::Data,
        Verdict::Data,
        Verdict::Data,
        Verdict::Data,
        Verdict::Refused(ref foreign),
        Verdict::Refused(ref signed),
        Verdict::Checked { .. },
    ] = *verdicts
    else {
        panic!("the families and the own constructor check, the foreign two refuse: {report:?}");
    };
    for (stated, family, count) in [(foreign, 0_usize, 0_usize), (signed, 2, 1)] {
        let gandr_core_checker::CheckRefusal::TypeMismatch(gandr_core_checker::Mismatch::Value {
            synthesised,
            ..
        }) = *stated
        else {
            panic!("a value of one family is no value of another of its shape: {stated:?}");
        };
        assert!(
            matches!(
                arena.value_type(synthesised),
                Some(ValueType::Data { declaration, arguments })
                    if *declaration == ConstantIndex::from(family) && arguments.len() == count
            ),
            "the refusal finds the constructor's own family, over the classifier's arguments: \
             {stated:?}"
        );
    }
}

#[test]
fn a_parameterized_constructor_needs_its_classifier()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        include_str!("tests/unformatted/a-parameterized-constructor-needs-its-classifier.gandr"),
        MAYBE = MAYBE
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    assert!(matches!(
        refusal_of(&module, SurfaceName::from("bare")),
        LoweringRefusal::OutOfFragment {
            boundary: FragmentBoundary::Unannotated,
            ..
        }
    ));
    assert!(
        matches!(
            arena.value(body_named(&module, SurfaceName::from("three"))),
            Some(Value::Constructor { fields, .. })
                if matches!(fields.first().and_then(|&field| arena.value(field)), Some(&Value::Ascribe { .. }))
        ),
        "an annotated field is ascribed inside its constructor (#1543)"
    );
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

/// #5035: a constructor of a family with arguments was refused `Unannotated`
/// as a typed `let`'s value and as the body of a returned lambda. The `let`'s
/// stated type classifies it, as an annotation does, and the lambda's body
/// takes the codomain of the value function space the definition answers.
#[test]
fn a_constructor_takes_a_typed_let_s_type_and_a_lambda_s_codomain_5035()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        include_str!(
            "tests/unformatted/a-constructor-takes-a-typed-let-s-type-and-a-lambda-s-codomain-5035.gandr"
        ),
        MAYBE = MAYBE
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    for name in ["kept", "here", "base", "lifted", "past"] {
        assert!(
            matches!(
                outcome_of(&module, SurfaceName::from(name)),
                DeclarationOutcome::Completed { .. }
            ),
            "`{name}` lowers: {:?}",
            outcome_of(&module, SurfaceName::from(name))
        );
    }
    assert_accepted(&judged(&module, &mut arena));
}

/// The families of variables over contexts that the #5050 tests bind.
const VARIABLES: &str = include_str!("tests/fixtures/variables.gandr");

/// #5050: a constructor of a family with indices was refused `Unannotated` as
/// the value of a `let` with no type. Its generator's result classifies it,
/// each field replaced by the value written for it, so a result type that
/// reads another argument is refused by the checker.
#[test]
fn an_untyped_let_reads_its_constructor_s_classifier_off_its_result_5050()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        include_str!(
            "tests/unformatted/an-untyped-let-reads-its-constructor-s-classifier-off-its-result-5050-1.gandr"
        ),
        VARIABLES = VARIABLES
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    for name in ["here", "next", "closed"] {
        assert!(
            matches!(
                outcome_of(&module, SurfaceName::from(name)),
                DeclarationOutcome::Completed { .. }
            ),
            "`{name}` lowers: {:?}",
            outcome_of(&module, SurfaceName::from(name))
        );
    }
    assert_accepted(&judged(&module, &mut arena));

    // The result's first index extends `g` by the second field, not the
    // first: a type stating `b` there misreads the order.
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        include_str!(
            "tests/unformatted/an-untyped-let-reads-its-constructor-s-classifier-off-its-result-5050-2.gandr"
        ),
        VARIABLES = VARIABLES
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    assert!(
        matches!(
            outcome_of(&module, SurfaceName::from("swapped")),
            DeclarationOutcome::Completed { .. }
        ),
        "`swapped` lowers: {:?}",
        outcome_of(&module, SurfaceName::from("swapped"))
    );
    let report = judged(&module, &mut arena);
    assert!(
        report
            .judged()
            .iter()
            .any(|judged| matches!(judged.verdict(), Verdict::Refused(_))),
        "the checker refuses a result type the classifier does not state: {report:?}"
    );
}

/// #5050: no field of a constructor fixes its family's parameter, so a `let`
/// with no type refuses the call and names the parameter.
#[test]
fn an_untyped_let_of_a_parameterised_constructor_names_its_parameter_5050()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!("{MAYBE}def kept() -> Maybe(Integer) {{ let x = Some 3; x }}\n");
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let refusal = refusal_of(&module, SurfaceName::from("kept"));
    let call = source.find("Some 3").unwrap_or_default();
    assert!(
        matches!(
            refusal,
            LoweringRefusal::UnfixedParameter { span, constructor, parameter }
                if constructor == SurfaceName::from("Some")
                    && parameter == SurfaceName::from("a")
                    && usize::from(span.start()) == call
                    && usize::from(span.end()) == call.saturating_add("Some 3".len())
        ),
        "the refusal names the constructor, its parameter and the call: {refusal:?}"
    );
}

/// An unsigned definition whose whole value is an annotation is declared at
/// the annotation's type and checked against it, a value the annotation
/// misstates refused by the checker rather than by the lowering (#1107).
#[test]
fn an_annotated_definition_value_is_signed_by_its_annotation_1107()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        include_str!(
            "tests/unformatted/an-annotated-definition-value-is-signed-by-its-annotation-1107.gandr"
        ),
        MAYBE = MAYBE
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
        include_str!("tests/unformatted/an-annotated-return-is-ascribed-its-returner-1107.gandr"),
        MAYBE = MAYBE
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

/// An annotation no other form carries — a pair's component, the value beside
/// a written signature — lowers to a value ascription at the annotation's
/// type, which the checker judges against it (#1543).
#[test]
fn an_annotation_no_form_carries_is_a_value_ascription_1543()
{
    let mut arena = CoreArena::new();
    let source = SourceText::from(include_str!(
        "tests/fixtures/an-annotation-no-form-carries-is-a-value-ascription-1543.gandr"
    ));
    let module = lowered(source, &mut arena);
    let DeclarationOutcome::Bodied { body, .. } = outcome_of(&module, SurfaceName::from("pair"))
    else {
        panic!("a pair is no annotation, and its definition stays unsigned");
    };
    let Some(&Value::Tuple(ref components)) = arena.value(body)
    else {
        panic!("the pair lowers to a tuple");
    };
    assert!(
        matches!(
            components.first().and_then(|&first| arena.value(first)),
            Some(&Value::Ascribe { value, ty })
                if matches!(arena.value(value), Some(&Value::Literal(_)))
                    && arena.value_type(ty) == Some(&ValueType::Base(BaseType::Integer))
        ),
        "the annotated component is the literal ascribed `Integer`"
    );
    let DeclarationOutcome::Completed { body, .. } =
        outcome_of(&module, SurfaceName::from("signed"))
    else {
        panic!("the signature completes the definition");
    };
    assert!(
        matches!(arena.value(body), Some(&Value::Ascribe { .. })),
        "beside a signature the annotation is an ascription the checker compares with it"
    );
    assert_accepted(&judged(&module, &mut arena));

    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/an-annotation-no-form-carries-is-a-value-ascription-1543-module.gandr"
        )),
        &mut arena,
    );
    let report = judged(&module, &mut arena);
    assert!(
        report
            .judged()
            .iter()
            .any(|judged| matches!(judged.verdict(), Verdict::Refused(_))),
        "the checker refuses an annotation its signature disagrees with: {report:?}"
    );
}

/// A type-valued call's argument is a value the type grammar reads, and no
/// parameter gives a constructor there its classifier. `(v : T)` gives it
/// one, as at a path's endpoint, and the checker judges the call at that
/// value (#3633).
#[test]
fn a_type_valued_calls_argument_takes_an_annotation_3633()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        include_str!(
            "tests/unformatted/a-type-valued-calls-argument-takes-an-annotation-3633.gandr"
        ),
        MAYBE = MAYBE
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    for name in ["held", "absent"].map(SurfaceName::from) {
        assert!(
            matches!(
                outcome_of(&module, name),
                DeclarationOutcome::Completed { .. }
            ),
            "`{name}` lowers its annotated argument: {:?}",
            outcome_of(&module, name)
        );
    }
    let constant = |name: &str| {
        module
            .declarations()
            .iter()
            .find(|declaration| declaration.name() == SurfaceName::from(name))
            .map(crate::module::LoweredDeclaration::constant)
    };
    let report = judged(&module, &mut arena);
    let verdict = |name: &str| {
        report
            .judged()
            .iter()
            .find(|judged| Some(judged.constant()) == constant(name))
            .map(gandr_core_checker::Judged::verdict)
    };
    assert!(
        matches!(verdict("held"), Some(Verdict::Checked { .. })),
        "`isSome` of the present option is `Unit`: {:?}",
        verdict("held")
    );
    assert!(
        matches!(verdict("absent"), Some(Verdict::Refused(_))),
        "`isSome` of the absent option is `Void`, which no `Unit` inhabits: {:?}",
        verdict("absent")
    );
}

#[test]
fn a_constructor_takes_its_classifier_from_the_type_it_answers_402()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        include_str!(
            "tests/unformatted/a-constructor-takes-its-classifier-from-the-type-it-answers-402.gandr"
        ),
        MAYBE = MAYBE
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

/// #2112: a constructor returned against a result written as a type-level
/// definition's application, `-> opt(Integer)` with `opt = fun (A) { -F
/// Maybe(A) }`, dropped the declaration as `Unminted`: the answer is the decode
/// of the application, no returner, so the constructor had no classifier. It
/// reads through the definition's body, at a closed argument, at a type
/// parameter, and through a definition that unfolds to `opt`; one answering a
/// constant with no written body is refused as unannotated, never dropped.
#[test]
fn a_constructor_answers_a_definition_s_application_2112()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        include_str!(
            "tests/unformatted/a-constructor-answers-a-definition-s-application-2112-1.gandr"
        ),
        MAYBE = MAYBE
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    for name in ["some1", "none", "twice"].map(SurfaceName::from) {
        assert!(
            matches!(
                outcome_of(&module, name),
                DeclarationOutcome::Completed { .. }
            ),
            "`{name}` lowers: {:?}",
            outcome_of(&module, name)
        );
    }
    let report = judged(&module, &mut arena);
    assert_accepted(&report);
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        include_str!(
            "tests/unformatted/a-constructor-answers-a-definition-s-application-2112-2.gandr"
        ),
        MAYBE = MAYBE
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    assert!(matches!(
        refusal_of(&module, SurfaceName::from("some1")),
        LoweringRefusal::OutOfFragment {
            boundary: FragmentBoundary::Unannotated,
            ..
        }
    ));
}

/// #3665: a constructor returned against a result written as the application
/// of a definition written as a function tail, `-> wrapped(Integer)` with
/// `def wrapped(A : Type) -> -F Type { … }`, was refused as unannotated: the
/// lowering found the body of a definition written `= e` alone. The tail's
/// declaration form holds its body, so the constructor lowers, bare and
/// returned, and the checker accepts it.
#[test]
fn a_constructor_answers_a_function_tail_s_application_3665()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        include_str!(
            "tests/unformatted/a-constructor-answers-a-function-tail-s-application-3665.gandr"
        ),
        MAYBE = MAYBE
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    for name in ["bare", "returned"].map(SurfaceName::from) {
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
        include_str!(
            "tests/unformatted/a-constructor-argument-takes-its-parameter-s-type-1833.gandr"
        ),
        MAYBE = MAYBE
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
        include_str!(
            "tests/unformatted/a-constructor-argument-reads-the-arguments-before-it-1876-1.gandr"
        ),
        MAYBE = MAYBE
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
        include_str!(
            "tests/unformatted/a-constructor-argument-reads-the-arguments-before-it-1876-2.gandr"
        ),
        MAYBE = MAYBE
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

/// #2126: a constructor written as the argument of a call to a refused
/// declaration took that declaration's parameter as its classifier, whose
/// type never lowered, so the caller minted nothing and was dropped as
/// `Unminted`, an engine fault. A refused callee classifies nothing: the
/// constructor is refused as unannotated, as one passed to no declaration
/// is, and a typed argument still leaves its caller lowered.
#[test]
fn a_refused_callee_classifies_no_argument_2126()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        include_str!("tests/unformatted/a-refused-callee-classifies-no-argument-2126.gandr"),
        MAYBE = MAYBE
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("refused")),
            LoweringRefusal::OutOfFragment {
                boundary: FragmentBoundary::WrongSort,
                ..
            }
        ),
        "the callee is refused: {:?}",
        outcome_of(&module, SurfaceName::from("refused"))
    );
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("bare")),
            LoweringRefusal::OutOfFragment {
                boundary: FragmentBoundary::Unannotated,
                ..
            }
        ),
        "`bare`'s argument is refused unannotated: {:?}",
        outcome_of(&module, SurfaceName::from("bare"))
    );
    assert!(
        matches!(
            outcome_of(&module, SurfaceName::from("annotated")),
            DeclarationOutcome::Completed { .. }
        ),
        "`annotated` lowers: {:?}",
        outcome_of(&module, SurfaceName::from("annotated"))
    );
}

/// #2127: a constructor written as an argument of a descent `f[<](…)` took no
/// classifier, since the head names the recursion's own binder rather than a
/// declaration, so `onto[<](rest, Cons(x, acc))` was refused as unannotated
/// where `onto(rest, Cons(x, acc))` checked. The declaration whose recursion
/// the head names classifies it by its parameter, a leading parameter the
/// descent passes unchanged counted in its place.
#[test]
fn a_descent_call_s_constructor_argument_takes_its_parameter_s_type_2127()
{
    let mut arena = CoreArena::new();
    let source = include_str!(
        "tests/fixtures/a-descent-call-s-constructor-argument-takes-its-parameter-s-type-2127.gandr"
    );
    let module = lowered(SourceText::from(source), &mut arena);
    for name in ["onto", "padded", "reverseOnto"].map(SurfaceName::from) {
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
        include_str!(
            "tests/unformatted/a-field-classifies-the-constructor-written-in-it-1171.gandr"
        ),
        MAYBE = MAYBE
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

/// #3744: a constructor annotated inside a signature type, past a parameter
/// no type names, read its annotation counting that parameter's binder,
/// which the arrow drops: the annotation's `d` read one past its binder,
/// refused `UnboundIndex`. The annotation counts in the signature's
/// telescope, as the constructor's fields do.
#[test]
fn an_annotation_inside_a_signature_type_counts_its_binders_there_3744()
{
    let mut arena = CoreArena::new();
    let source = SourceText::from(include_str!(
        "tests/fixtures/an-annotation-inside-a-signature-type-counts-its-binders-there-3744.gandr"
    ));
    let module = lowered(source, &mut arena);
    for name in [
        "named",
        "unnamed",
        "between",
        "outermost",
        "inBody",
        "quoted",
        "wrapped",
    ]
    .map(SurfaceName::from)
    {
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
fn a_listed_constructor_takes_the_element_type_1544()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        include_str!("tests/unformatted/a-listed-constructor-takes-the-element-type-1544.gandr"),
        MAYBE = MAYBE
    );
    let source = listing(&source);
    let module = listed(&source, &mut arena);
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
        include_str!(
            "tests/unformatted/a-listed-constructor-takes-the-answered-element-type-1602.gandr"
        ),
        MAYBE = MAYBE
    );
    let source = listing(&source);
    let module = listed(&source, &mut arena);
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
        include_str!(
            "tests/unformatted/a-tuple-gives-its-members-the-product-s-components-1877.gandr"
        ),
        MAYBE = MAYBE
    );
    let source = listing(&source);
    let module = listed(&source, &mut arena);
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
    let families = include_str!(
        "tests/fixtures/a-constructor-takes-its-slot-as-a-family-argument-421-families.gandr"
    );
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
        include_str!(
            "tests/unformatted/a-type-argument-names-the-type-its-constructor-shares-a-name-with-1855.gandr"
        ),
        MAYBE = MAYBE
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
        "{MAYBE}def first(m : Maybe(Integer)) -> -F Integer {{ match m {{ | Some(x) => return x | None => return 0 }} }}\n"
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
    let source = include_str!("tests/fixtures/a-record-names-every-field-binder-in-order.gandr");
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
        include_str!("tests/unformatted/a-data-family-applies-to-its-parameters.gandr"),
        MAYBE = MAYBE
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
        include_str!("tests/unformatted/a-match-takes-its-answer-from-the-function-result.gandr"),
        COLOR = COLOR
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
        "{COLOR}def inner(c : Color) -> -F Integer {{ let n = match c {{ | Red => pure 0 | _ => pure 1 }}; return n }}\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    assert!(matches!(
        refusal_of(&module, SurfaceName::from("inner")),
        LoweringRefusal::OutOfFragment {
            form: FormName::MATCH,
            boundary: FragmentBoundary::Unannotated,
            ..
        }
    ));
}

#[test]
fn a_layout_match_writes_where_before_its_arms_5557()
{
    let source = include_str!(
        "tests/fixtures/a-layout-match-writes-where-before-its-arms-5557-module.gandr"
    );
    let head = source
        .find("match c\n")
        .map(|at| at.saturating_add("match c".len()));
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source), &mut arena);
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("bare")),
            LoweringRefusal::OutOfFragment {
                span,
                form: FormName::MATCH,
                boundary: FragmentBoundary::BareArms,
                ..
            } if Some(usize::from(span.start())) == head && span.start() == span.end()
        ),
        "a layout match with no `where` is refused at the end of its head"
    );
    assert!(
        matches!(
            outcome_of(&module, SurfaceName::from("marked")),
            DeclarationOutcome::Completed { .. }
        ),
        "the same match with `where` after its scrutinee lowers"
    );
}

#[test]
fn a_nested_match_records_its_cover_5103()
{
    use gandr_kernel_term::FieldCount;
    use gandr_kernel_term::cover::ArmCount;
    use gandr_kernel_term::cover::Cases;
    use gandr_kernel_term::cover::Cover;
    use gandr_kernel_term::cover::CoverRefusal;
    use gandr_kernel_term::cover::Step;
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/a-nested-match-records-its-cover-5103-module.gandr"
        )),
        &mut arena,
    );
    let signatures: Vec<_> = ["Nat", "Maybe", "List"]
        .into_iter()
        .map(|name| {
            let DeclarationOutcome::Data(index) = outcome_of(&module, SurfaceName::from(name))
            else {
                panic!("{name} lowers to its signature");
            };
            let Maybe::Present(signature) = module.data(index)
            else {
                panic!("{name}'s index names a signature");
            };
            Arc::clone(signature)
        })
        .collect();
    let declared = |family| {
        (0_usize .. signatures.len())
            .find(|&at| ConstantIndex::from(at) == family)
            .and_then(|at| signatures.get(at))
            .map(|signature| {
                signature
                    .constructors()
                    .iter()
                    .map(|fields| FieldCount::from(fields.len()))
            })
    };
    let root = tail_of(&arena, body_named(&module, SurfaceName::from("f")));
    let Maybe::Present(kept) = module.origins().case(root)
    else {
        panic!("the match keeps its arms");
    };
    let cover = &kept.cover;
    assert_eq!(
        cover.check(ArmCount::from(5_usize), declared),
        Ok(()),
        "{cover:?}"
    );
    let data_splits: Vec<(ConstantIndex, usize)> = cover
        .steps()
        .filter_map(|(_id, step)| match *step {
            Step::Split {
                cases:
                    Cases::Data {
                        family,
                        ref constructors,
                        ..
                    },
                ..
            } => Some((family, constructors.len())),
            Step::Split { .. } | Step::Var(_) | Step::Compose(_) => None,
        })
        .collect();
    assert_eq!(
        data_splits,
        [
            (ConstantIndex::from(2_usize), 2),
            (ConstantIndex::from(0_usize), 2),
            (ConstantIndex::from(1_usize), 2),
            (ConstantIndex::from(2_usize), 2),
        ],
        "one split for each switch, inner first, each over its family's two constructors"
    );
    // Mint the same steps again in order, leaving `Some` out of `Maybe`'s split.
    let mut dropped = Cover::new();
    for (_id, step) in cover.steps() {
        let step = match *step {
            Step::Split {
                cases:
                    Cases::Data {
                        family,
                        ref constructors,
                        ref loops,
                    },
                ref branches,
            } if family == ConstantIndex::from(1_usize) => Step::Split {
                cases: Cases::Data {
                    family,
                    constructors: constructors.iter().take(1).copied().collect(),
                    loops: loops.clone(),
                },
                branches: branches.iter().take(1).copied().collect(),
            },
            ref other @ (Step::Var(_) | Step::Split { .. } | Step::Compose(_)) => other.clone(),
        };
        dropped.mint(step);
    }
    assert!(
        matches!(
            dropped.check(ArmCount::from(5_usize), declared),
            Err(CoverRefusal::ConstructorCount(_))
        ),
        "a derivation whose `Maybe` split leaves out `Some` is refused by name"
    );
    let report = judged(&module, &mut arena);
    assert_accepted(&report);
}

#[test]
fn a_match_over_the_circle_covers_its_loop_5104()
{
    use gandr_kernel_term::CellIndex;
    use gandr_kernel_term::cover::Cases;
    use gandr_kernel_term::cover::Loop;
    use gandr_kernel_term::cover::Step;
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/a-match-over-the-circle-covers-its-loop-5104-module.gandr"
        )),
        &mut arena,
    );
    let root = tail_of(&arena, body_named(&module, SurfaceName::from("invLooper")));
    let Maybe::Present(kept) = module.origins().case(root)
    else {
        panic!("the match keeps its arms");
    };
    let Some((
        _root,
        &Step::Split {
            cases:
                Cases::Data {
                    ref constructors,
                    ref loops,
                    ..
                },
            ref branches,
        },
    )) = kept.cover.steps().last()
    else {
        panic!("the root is a data split: {:?}", kept.cover);
    };
    assert_eq!(constructors.len(), 1, "the point `Base`");
    assert_eq!(
        loops.iter().map(|owed| owed.cell()).collect::<Vec<_>>(),
        [CellIndex::from(0_usize)],
        "the one loop the case owes, after the point"
    );
    assert_eq!(branches.len(), 2, "the point's branch, then the loop's");
    assert_eq!(
        branches
            .get(1)
            .and_then(|&loop_arm| kept.cover.step(loop_arm)),
        Some(&Step::Var(1)),
        "the loop's branch runs the loop's arm, after the one constructor arm"
    );
    let _same: Option<&Loop> = loops.first();
}

#[test]
fn nested_constructor_patterns_compile_to_nested_cases()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/nested-constructor-patterns-compile-to-nested-cases-module.gandr"
        )),
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
        include_str!("tests/unformatted/a-data-case-names-the-family-it-eliminates-809.gandr"),
        MAYBE = MAYBE
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
        SourceText::from(include_str!(
            "tests/fixtures/literal-patterns-compare-and-branch-module.gandr"
        )),
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
        include_str!(
            "tests/unformatted/literal-and-nullary-patterns-nest-under-a-constructor.gandr"
        ),
        COLOR = COLOR,
        MAYBE = MAYBE
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
        include_str!("tests/unformatted/a-pattern-hole-leaves-its-leaf-stuck.gandr"),
        COLOR = COLOR,
        MAYBE = MAYBE
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
        include_str!("tests/unformatted/a-non-exhaustive-match-is-refused.gandr"),
        COLOR = COLOR
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
fn list_patterns_case_on_the_native_list()
{
    let mut arena = CoreArena::new();
    let source = listing(include_str!(
        "tests/fixtures/list-patterns-case-on-the-native-list.gandr"
    ));
    let module = listed(&source, &mut arena);
    let cases = |name: &str| -> Vec<ComputationId> {
        reachable(
            &arena,
            tail_of(&arena, body_named(&module, SurfaceName::from(name))),
        )
        .into_iter()
        .filter(|&at| matches!(arena.computation(at), Some(&Computation::ListCase { .. })))
        .collect()
    };
    assert_eq!(cases("empty").len(), 1_usize, "one case on the list");
    assert_eq!(
        cases("pair").len(),
        3_usize,
        "a case on the list, on its tail and on the tail's tail"
    );
    let returned = |name: &str| {
        let [case] = *cases(name).as_slice()
        else {
            return None;
        };
        let Some(&Computation::ListCase { on_cons, .. }) = arena.computation(case)
        else {
            return None;
        };
        match arena.computation(on_cons) {
            Some(&Computation::Return(value)) => arena.value(value).cloned(),
            _ => None,
        }
    };
    assert_eq!(
        returned("rest"),
        Some(variable(DeBruijnIndex::from(0_u32))),
        "the rest is the cell's tail, its innermost binder"
    );
    assert_eq!(
        returned("whole"),
        Some(variable(DeBruijnIndex::from(2_u32))),
        "the alias is the whole list, the parameter past the head and the tail"
    );
    assert_accepted(&judged(&module, &mut arena));
}

/// An as-pattern names its match with a name: a pattern before the `@` is
/// refused at that pattern, while the name form aliases the whole list.
#[test]
fn an_as_pattern_names_its_match_with_a_name()
{
    let mut arena = CoreArena::new();
    let source = listing(
        "def whole(xs : List(Integer)) -> -F List(Integer) { match xs { | #[a, .._] @ all => \
         return all | #[] => return #[] } }\n",
    );
    let module = listed(&source, &mut arena);
    let start = source.find("#[a, .._]").unwrap_or(0_usize);
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("whole")),
            LoweringRefusal::MalformedForm {
                form: FormName::AS_PATTERN,
                fault: crate::FormFault::NotAName,
                span,
            } if usize::from(span.start()) == start
        ),
        "the list pattern before `@` is refused where it stands"
    );
}

#[test]
fn patterns_outside_the_fragment_are_declined_by_name()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        include_str!("tests/unformatted/patterns-outside-the-fragment-are-declined-by-name.gandr"),
        COLOR = COLOR
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
        refusal_of(&module, SurfaceName::from("bound")),
        LoweringRefusal::OutOfFragment {
            form: FormName::OR_PATTERN,
            boundary: FragmentBoundary::Unadmitted(crate::Unbuilt::OrPattern),
            ..
        }
    ));
}

#[test]
fn a_pattern_of_another_type_is_refused_at_its_arm()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        include_str!("tests/unformatted/a-pattern-of-another-type-is-refused-at-its-arm.gandr"),
        COLOR = COLOR
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let at = |name: &str, pattern: &str| {
        let declared = source
            .find(&alloc::format!("def {name}"))
            .unwrap_or_default();
        let start = source
            .get(declared ..)
            .and_then(|rest| rest.find(&alloc::format!("{pattern} =>")))
            .map_or(0_usize, |offset| declared.saturating_add(offset));
        crate::fixture::span(
            gandr_surface_syntax::ByteOffset::from(start),
            gandr_surface_syntax::ByteOffset::from(start.saturating_add(pattern.len())),
        )
    };
    for (name, written) in [("foreign", "Boxed(n)"), ("literal", "1")] {
        assert_eq!(
            refusal_of(&module, SurfaceName::from(name)),
            LoweringRefusal::MismatchedPattern {
                span: at(name, written),
                first: at(name, "Red"),
            },
            "`{name}` is refused at its arm of another type, naming the first pattern tested there"
        );
    }
}

#[test]
fn a_misnamed_or_misshapen_pattern_is_refused_by_name()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        include_str!("tests/unformatted/a-misnamed-or-misshapen-pattern-is-refused-by-name.gandr"),
        MAYBE = MAYBE
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
        SourceText::from(include_str!(
            "tests/fixtures/a-match-of-no-arms-eliminates-the-empty-sum-module.gandr"
        )),
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
            form: FormName::MATCH,
            boundary: FragmentBoundary::Unadmitted(crate::Unbuilt::EmptyMatch),
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
        include_str!(
            "tests/unformatted/a-match-of-no-arms-switches-on-empty-data-and-on-a-path.gandr"
        ),
        COLOR = COLOR
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
    let source = alloc::format!("{COLOR}def some(c : Color) -> -F Integer {{ match c {{}} }}\n");
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
        SourceText::from(include_str!(
            "tests/fixtures/a-match-of-no-arms-switches-on-a-lambda-binder-its-arrow-types-module.gandr"
        )),
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
        SourceText::from(include_str!(
            "tests/fixtures/a-bare-signed-lambda-s-binder-is-typed-as-in-its-thunk-1944-module.gandr"
        )),
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
        SourceText::from(include_str!(
            "tests/fixtures/an-argument-lambda-s-binder-is-typed-by-its-parameter-1948-module.gandr"
        )),
        &mut arena,
    );
    assert_accepted(&judged(&module, &mut arena));
}

#[test]
fn a_lambda_under_a_value_function_alias_lowers_as_under_its_thunked_arrow_808()
{
    for (alias, arrow, body) in [
        (
            "Empty -> Integer",
            "+U (Empty -> -F Integer)",
            "thunk { fun (x) { match x {} } }",
        ),
        (
            "Empty -> Integer",
            "+U (Empty -> -F Integer)",
            "thunk { fun (x) { match x -> -F Integer {} } }",
        ),
        (
            "(Empty, Integer) -> Integer",
            "+U (Empty -> Integer -> -F Integer)",
            "thunk { fun (x) { fun (n) { match x {} } } }",
        ),
    ] {
        let mut arena = CoreArena::new();
        let source = alloc::format!(
            include_str!(
                "tests/unformatted/a-lambda-under-a-value-function-alias-lowers-as-under-its-thunked-arrow-808.gandr"
            ),
            alias = alias,
            arrow = arrow,
            body = body
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
            "(a : Empty, b : Integer) -> Integer",
            "+U ((a : Empty) -> (b : Integer) -> -F Integer)",
            "thunk { fun (a) { fun (b) { match a {} } } }",
        ),
        (
            "(a : One) -> Path[.A = One](a, a)",
            "+U ((a : One) -> -F Path[.A = One](a, a))",
            "thunk { fun (a) { match a { | Only => Path.here Only } } }",
        ),
        (
            "(a : One, Integer) -> Path[.A = One](a, a)",
            "+U ((a : One) -> Integer -> -F Path[.A = One](a, a))",
            "thunk { fun (x) { fun (n) { match x { | Only => Path.here Only } } } }",
        ),
    ] {
        let mut arena = CoreArena::new();
        let source = alloc::format!(
            include_str!(
                "tests/unformatted/a-lambda-under-a-telescope-alias-lowers-as-under-its-dependent-arrows-815.gandr"
            ),
            alias = alias,
            arrow = arrow,
            body = body
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
        "{COLOR}def warm(c : Color) -> -F Integer {{ match c {{ | Red | Green => return 1 | Blue => return 0 }} }}\n"
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
    let source = "def not(b : +{Unit, Unit}) -> -F +{Unit, Unit} { match b { | +{.0 = u} => return \
                  +{.1 = u} | +{.1 = u} => return +{.0 = u} } }\n";
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
        "{MAYBE}def pick(m : Maybe(Integer)) -> -F Integer {{ match m {{ | Some(x) => return x | ? => return 0 }} }}\n"
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
        identity.origin(),
        HoleOrigin::Written,
        "a pattern hole is a hole the text writes"
    );
    assert!(
        reachable(&arena, root)
            .into_iter()
            .any(|at| arena.computation(at) == Some(&Computation::Hole(identity))),
        "the tree is stuck on the same hole"
    );
    assert!(kept.scrutinee > kept.written);
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
        "{MAYBE}def pick(m : Maybe(Integer), d : Integer) -> -F Integer {{ match m {{ | Some(x) => return x | None => return d }} }}\n"
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
        "{MAYBE}def forget(b : Type, m : Maybe(b)) -> -F Maybe(b) {{ match m {{ | Some(x) => return (None : Maybe(b)) | None => return m }} }}\n"
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
        SourceText::from(include_str!(
            "tests/fixtures/telescope-patterns-split-and-project-module.gandr"
        )),
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
            "def swapped(t : *{Integer, String}) -> -F Integer { match t { | *{a, b} => return b } }\n",
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
            "def ragged(t : *{Integer, String}) -> -F Integer { match t { | *{a, b} => return a | *{a, b, c} => return a } }\n",
        ),
        &mut arena,
    );
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("ragged")),
            LoweringRefusal::MismatchedPattern { .. }
        ),
        "a tuple pattern wider than the tuple its column splits is refused: {:?}",
        refusal_of(&module, SurfaceName::from("ragged"))
    );
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(
            "def over(t : *{Integer, String}) -> -F Integer { match t { | *{a, b, c} => return a } }\n",
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
        SourceText::from(include_str!(
            "tests/fixtures/a-pattern-at-a-dependent-record-splits-it-under-its-motive-module.gandr"
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
/// states, as a `let` binder of the call does: a dependent record under a
/// motive over the scrutinee, so the checker reads the second component at
/// the first.
#[test]
fn a_call_as_the_scrutinee_splits_the_record_it_returns_1141()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/a-call-as-the-scrutinee-splits-the-record-it-returns-1141-module.gandr"
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
        include_str!(
            "tests/unformatted/a-case-over-a-variable-answers-its-motive-at-each-constructor.gandr"
        ),
        NAT = NAT
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

/// A match in an arm, with no answer of its own, on the variable naming the
/// arm's field, answers at the arm's constructor: its motive reads the
/// scrutinee it abstracts, and its branches read the outer scrutinee at the
/// arm's constructor over their own, two arms deep as one (#2994).
#[test]
fn a_match_in_an_arm_reads_the_answer_at_the_arm_s_constructor_2994()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        include_str!(
            "tests/unformatted/a-match-in-an-arm-reads-the-answer-at-the-arm-s-constructor-2994.gandr"
        ),
        NAT = NAT
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let inner = tail_of(&arena, body_named(&module, SurfaceName::from("inner")));
    let motives: Vec<_> = reachable(&arena, inner)
        .into_iter()
        .filter_map(|at| match arena.computation(at) {
            Some(&Computation::DataCase { motive, .. }) => Some(motive),
            _ => None,
        })
        .collect();
    assert_eq!(
        motives.len(),
        2_usize,
        "the outer match and the one in its arm"
    );
    for motive in motives {
        assert!(
            matches!(
                gandr_core_term::strengthen_comp_type(&mut arena, motive),
                Maybe::Absent(_)
            ),
            "each motive reads the scrutinee it abstracts"
        );
    }
    assert_accepted(&judged(&module, &mut arena));
}

/// An arm that leaves a field to a wildcard cannot name the constructor it
/// reads its scrutinee at, so a match in it on the field it does name takes
/// the answer as written, and its branches, reading the whole scrutinee,
/// check (#2994).
#[test]
fn an_arm_leaving_a_field_unnamed_passes_the_answer_as_written_2994()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        include_str!(
            "tests/unformatted/an-arm-leaving-a-field-unnamed-passes-the-answer-as-written-2994.gandr"
        ),
        NAT = NAT
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let _lowered = body_named(&module, SurfaceName::from("half"));
    assert_accepted(&judged(&module, &mut arena));
}

/// A leaf reads every level a dependent switch above it matched at that
/// switch's constructor: an arm variable at a field an earlier arm's nested
/// pattern switches, the scrutinee named below the nested switch, and a
/// variable for the whole scrutinee each read as the arm's answer does, and
/// a match in an arm whose nested pattern switches its field takes the
/// answer read at the nested constructor (#3008).
#[test]
fn an_arm_variable_at_a_switched_field_reads_its_constructor_3008()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        include_str!(
            "tests/unformatted/an-arm-variable-at-a-switched-field-reads-its-constructor-3008.gandr"
        ),
        NAT = NAT
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    assert_accepted(&judged(&module, &mut arena));
}

#[test]
fn the_presentation_code_names_its_family_where_a_type_is_read()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/the-presentation-code-names-its-family-where-a-type-is-read-module.gandr"
        )),
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

/// `Theory.App` names `Theory`'s application where the source's own `App`
/// takes the bare name, in a value and in a pattern, and `Term.App` the
/// source's; only `Theory`'s is shadowed (#2428).
#[test]
fn a_qualified_constructor_names_its_family_s_constructor_2428()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/a-qualified-constructor-names-its-family-s-constructor-2428-module.gandr"
        )),
        &mut arena,
    );
    let constant = |name: &str| {
        module
            .declarations()
            .iter()
            .find(|declaration| declaration.name() == SurfaceName::from(name))
            .map(crate::module::LoweredDeclaration::constant)
            .expect("the declaration is lowered")
    };
    let (theory, term) = (constant("Theory"), constant("Term"));
    let application = gandr_theory_levitation::THEORY_CONSTRUCTORS
        .iter()
        .position(|&name| name == "App")
        .expect("`Theory` has an application link");
    let built = |name: &str| match arena.value(body_named(&module, SurfaceName::from(name))) {
        Some(&Value::Constructor { datatype, tag, .. }) => match arena.value_type(datatype) {
            Some(&ValueType::Data { declaration, .. }) => (declaration, tag),
            other => panic!("`{name}` is built at a family: {other:?}"),
        },
        other => panic!("`{name}` is a constructor value: {other:?}"),
    };
    assert_eq!(built("theirs"), (theory, ConstructorTag::from(application)));
    assert_eq!(built("ours"), (term, ConstructorTag::from(1_usize)));
    assert_eq!(
        module.constructor_spelling(theory, SurfaceName::from("App")),
        crate::ConstructorSpelling::Qualified,
        "`Theory`'s `App` is shadowed, so written qualified"
    );
    assert_eq!(
        module.constructor_spelling(term, SurfaceName::from("App")),
        crate::ConstructorSpelling::Bare,
        "the source's own `App` is written bare"
    );
    assert_eq!(
        module.constructor_spelling(theory, SurfaceName::from("Oper")),
        crate::ConstructorSpelling::Bare,
        "a name the source leaves free is written bare"
    );
    assert_accepted(&judged(&module, &mut arena));
}

/// `Expr.Share` names the multi-output constructor through its family:
/// `Expr.Share(a).r` is the port, `Expr.Share(a)` the record of the ports,
/// and `Expr.Share(x).l` a port pattern coverage counts. A bare
/// `Expr.Share(x)` pattern is the joint pattern, and a name the family lacks
/// is its unknown member.
#[test]
fn a_qualified_multi_output_constructor_names_its_ports()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!("fixture/qualified_ports.gandr")),
        &mut arena,
    );
    let Some(&Value::Constructor { tag, .. }) =
        arena.value(body_named(&module, SurfaceName::from("port")))
    else {
        panic!("a qualified port is a constructor value");
    };
    assert_eq!(
        tag,
        ConstructorTag::from(2_usize),
        "`Expr.Share(a).right` is the port after `Lit` and `Share.left`"
    );
    let Some(&Value::Record(ref record)) =
        arena.value(body_named(&module, SurfaceName::from("ports")))
    else {
        panic!("a qualified constructor with no output named is a record");
    };
    assert_eq!(
        record.keys().map(AsRef::as_ref).collect::<Vec<&str>>(),
        ["left", "right"],
        "the record holds each port at its output's label"
    );
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("partial")),
            LoweringRefusal::NonExhaustiveMatch { .. }
        ),
        "a match missing the qualified `right` port is refused"
    );
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("joint")),
            LoweringRefusal::OutOfFragment {
                boundary: FragmentBoundary::Unadmitted(Unbuilt::PortPattern),
                ..
            }
        ),
        "a qualified pattern naming no output is the joint pattern"
    );
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("missing")),
            LoweringRefusal::UnknownMember { module, member, .. }
                if module == SurfaceName::from("Expr") && member == SurfaceName::from("Fork")
        ),
        "a constructor the family lacks is its unknown member"
    );
    let report = judged(&module, &mut arena);
    for name in ["Expr", "port", "ports", "size"] {
        let Some(declaration) = module
            .declarations()
            .iter()
            .find(|declaration| declaration.name() == SurfaceName::from(name))
        else {
            panic!("`{name}` is declared");
        };
        assert!(
            report.judged().iter().any(|judged| {
                judged.constant() == declaration.constant()
                    && matches!(
                        judged.verdict(),
                        Verdict::Data | Verdict::Checked { .. } | Verdict::Synthesised { .. }
                    )
            }),
            "`{name}` is accepted"
        );
    }
}

#[test]
fn a_case_over_a_family_of_parameters_reads_its_answer_unabstracted()
{
    let mut arena = CoreArena::new();
    let source = include_str!(
        "tests/fixtures/a-case-over-a-family-of-parameters-reads-its-answer-unabstracted.gandr"
    );
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
    let source =
        include_str!("tests/fixtures/a-constructor-no-row-admits-at-one-index-is-pruned.gandr");
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

/// A case over a family of two indices with no arm for its empty constructor
/// prunes that constructor at the index where it stands apart. `Grid`'s
/// `GNil` states `Zero` at both indices. Over `Grid(Succ(n), m)` its branch
/// eliminates the first equation, and over `Grid(m, Succ(n))` the second. The
/// checker admits both.
#[test]
fn a_case_over_two_indices_prunes_at_the_apart_one_3402()
{
    let mut arena = CoreArena::new();
    let source =
        include_str!("tests/fixtures/a-case-over-two-indices-prunes-at-the-apart-one-3402.gandr");
    let module = lowered(SourceText::from(source), &mut arena);
    // The equation the left-out `GNil` eliminates, counted from the innermost
    // of the two it binds.
    let eliminated = |name: &str| {
        let tail = tail_of(&arena, body_named(&module, SurfaceName::from(name)));
        let reached = reachable(&arena, tail);
        let cases: Vec<_> = reached
            .iter()
            .filter_map(|&at| match arena.computation(at) {
                Some(&Computation::DataCase { ref branches, .. }) if !branches.is_empty() => {
                    Some(branches.clone())
                },
                _ => None,
            })
            .collect();
        let [ref branches] = *cases
        else {
            panic!("`{name}` cases once on the grid: {cases:?}");
        };
        let mut at = *branches.first().expect("`GNil` has a branch");
        let mut bound = 0_usize;
        while let Some(&Computation::Lambda(body)) = arena.computation(at) {
            bound = bound.saturating_add(1);
            at = body;
        }
        assert_eq!(bound, 2, "`GNil` binds its two equations alone");
        let Some(&Computation::DataCase {
            scrutinee,
            ref branches,
            ..
        }) = arena.computation(at)
        else {
            panic!(
                "`{name}`'s left-out arm is a case: {:?}",
                arena.computation(at)
            );
        };
        assert!(branches.is_empty(), "of no branches");
        arena.value(scrutinee).cloned()
    };
    let equation = |index: u32| {
        Some(Value::Variable {
            zone: gandr_core_term::Zone::Intuitionistic,
            index: DeBruijnIndex::from(index),
        })
    };
    assert_eq!(
        eliminated("rows"),
        equation(1),
        "over `Grid(Succ(n), m)` the first index is apart"
    );
    assert_eq!(
        eliminated("cols"),
        equation(0),
        "over `Grid(m, Succ(n))` the second index is apart"
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
    let source =
        include_str!("tests/fixtures/a-leaf-copy-keeps-each-use-naming-its-pattern-variable.gandr");
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
        written("*{m, w}", "w"),
        "the copy's first component is the use of `w`"
    );
    assert_eq!(
        module.origins().binding(second),
        written("*{m, w}", "m"),
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
    let source = include_str!(
        "tests/fixtures/a-leaf-copy-of-a-copy-keeps-the-use-naming-its-binder-451.gandr"
    );
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source), &mut arena);
    let parameter = source.find("a : Int").expect("`f` declares `a`");
    let bound = Maybe::Present(crate::fixture::span(
        gandr_surface_syntax::ByteOffset::from(parameter),
        gandr_surface_syntax::ByteOffset::from(parameter.saturating_add(1)),
    ));
    let form = source
        .rfind("Path.back (r a)")
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
        SourceText::from(include_str!(
            "tests/fixtures/sum-patterns-case-on-the-stated-arity-module.gandr"
        )),
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
            "def unstated(n : Integer) -> -F Integer { match (+{.ok = n} : +{ok : Integer, err : String}) { | +{.ok = m} => return m | +{.err = s} => return 0 } }\n",
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
        SourceText::from(include_str!(
            "tests/fixtures/a-sum-pattern-reads-a-sum-stated-as-a-chain-791-module.gandr"
        )),
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
        SourceText::from(include_str!(
            "tests/unformatted/a-sum-pattern-reads-bool-as-its-sum-815-module.gandr"
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
/// a scrutinee bound by `let` states no type; before the fix such arms were
/// refused as unannotated, so the printed body did not read back. Indexed arms
/// covering every summand between them settle the sum they inject into.
#[test]
fn indexed_arms_settle_their_sum_1169()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/indexed-arms-settle-their-sum-1169-module.gandr"
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
        SourceText::from(include_str!(
            "tests/fixtures/indexed-arms-settle-their-sum-1169-refused.gandr"
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
    let source = include_str!("tests/fixtures/a-loop-mints-the-words-at-its-point.gandr");
    let module = lowered(SourceText::from(source), &mut arena);
    let [circle, words, looped, turned, flag] = *module.declarations().iter().collect::<Vec<_>>()
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
    let source =
        include_str!("tests/fixtures/a-cell-between-terms-is-a-loop-or-refused-by-name.gandr");
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
        ("Open", "Next x"),
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
    let source = include_str!("tests/fixtures/only-back-inverts-a-letter.gandr");
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source), &mut arena);
    let written = "here loop ∷ loop";
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
fn a_letter_naming_nothing_is_unresolved_1997()
{
    // `lop` names no loop and nothing else: the letter is unresolved at its
    // name, plain or inside `back`, and `turn`, a declaration other than a
    // loop, is still no letter.
    let source = include_str!("tests/fixtures/a-letter-naming-nothing-is-unresolved-1997.gandr");
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source), &mut arena);
    for (declaration, written) in [("plain", "= lop"), ("inverse", "back lop")] {
        let start = source
            .find(written)
            .map(|at| at.saturating_add(written.len()).saturating_sub("lop".len()))
            .expect("the letter is written");
        assert!(
            matches!(
                outcome_of(&module, declaration.into()),
                DeclarationOutcome::Refused(LoweringRefusal::UnresolvedName { span, name })
                    if name == SurfaceName::from("lop")
                        && usize::from(span.start()) == start
                        && usize::from(span.end()) == start.saturating_add("lop".len())
            ),
            "`{declaration}`'s letter names nothing: {:?}",
            outcome_of(&module, declaration.into())
        );
    }
    assert!(
        matches!(
            outcome_of(&module, "other".into()),
            DeclarationOutcome::Refused(LoweringRefusal::OutOfFragment {
                boundary: FragmentBoundary::Unadmitted(crate::Unbuilt::InfixForm),
                ..
            })
        ),
        "a declaration that is no loop is no letter: {:?}",
        outcome_of(&module, "other".into())
    );
}

#[test]
fn a_word_conses_its_letters_and_matches_them()
{
    let source = include_str!("tests/fixtures/a-word-conses-its-letters-and-matches-them.gandr");
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
        ..
    }) = arena.value(body_named(&module, SurfaceName::from("empty")))
    else {
        panic!("`Path.here Base` at the loop's point is a word");
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
        ..
    }) = arena.value(body_named(&module, SurfaceName::from("word")))
    else {
        panic!("a cons is a word");
    };
    assert!(is_words(datatype));
    assert_eq!(
        (usize::from(tag), fields.len()),
        (2_usize, 1_usize),
        "`back (loop)` is the loop's inverse letter, consed onto one word"
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
                | crate::origin::Labelled::Bound(_)
                | crate::origin::Labelled::Kind(_) => None,
            })
    };
    let after_word = source.find("def word =").expect("the word is written");
    let after_empty = source
        .find("def empty =")
        .expect("the empty word is written");
    for (text, from) in [
        ("back loop", after_word),
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
    let source =
        include_str!("tests/fixtures/a-loop-arm-follows-the-constructors-branches-1.gandr");
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
    let source =
        include_str!("tests/fixtures/a-loop-arm-follows-the-constructors-branches-2.gandr");
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

/// #1106: a field read off a data value by its name is the data case over the
/// value whose branch for each constructor binds its fields and returns that
/// constructor's field, typed by its position's answer or, where the position
/// states none, by the field's declaration at the family's written arguments.
#[test]
fn a_data_field_is_the_case_returning_it_1106()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/a-data-field-is-the-case-returning-it-1106-module.gandr"
        )),
        &mut arena,
    );
    // Each branch's field count and the index, under its lambdas, of the
    // variable it returns; and the type the motive returns. A field read as a
    // primitive's operand is the computation nested in that operand.
    let switch = |name: &str| {
        let tail = tail_of(&arena, body_named(&module, SurfaceName::from(name)));
        let mut roots = Vec::from([tail]);
        if let Some(&Computation::Primitive { ref arguments, .. }) = arena.computation(tail) {
            roots.extend(
                arguments
                    .iter()
                    .filter_map(|&operand| match arena.value(operand) {
                        Some(&Value::Nested(nested)) => Some(nested),
                        _ => None,
                    }),
            );
        }
        let Some(&Computation::DataCase {
            motive,
            ref branches,
            ..
        }) = roots
            .into_iter()
            .flat_map(|root| reachable(&arena, root))
            .find_map(|at| {
                arena
                    .computation(at)
                    .filter(|held| matches!(held, Computation::DataCase { .. }))
            })
        else {
            panic!("`{name}` reads its field by a data case");
        };
        let read: Vec<(usize, u32)> = branches
            .iter()
            .map(|&branch| {
                let (mut at, mut arity) = (branch, 0_usize);
                while let Some(&Computation::Lambda(body)) = arena.computation(at) {
                    (at, arity) = (body, arity.saturating_add(1));
                }
                let Some(&Computation::Return(value)) = arena.computation(at)
                else {
                    panic!("`{name}`'s branch returns its field");
                };
                let Some(&Value::Variable { index, .. }) = arena.value(value)
                else {
                    panic!("`{name}`'s branch returns a field binder");
                };
                (arity, u32::from(index))
            })
            .collect();
        let Some(&gandr_core_term::CompType::Returner { result, .. }) = arena.comp_type(motive)
        else {
            panic!("`{name}`'s motive returns the field's type");
        };
        (read, arena.value_type(result).cloned())
    };
    let integer = Some(ValueType::Base(gandr_kernel_term::BaseType::Integer));
    assert_eq!(
        switch("lowOf"),
        (Vec::from([(2_usize, 1_u32)]), integer.clone()),
        "the first of two fields, typed by the function's result"
    );
    assert_eq!(
        switch("above"),
        (Vec::from([(2_usize, 0_u32)]), integer.clone()),
        "the second of two fields in an operand, typed by its declaration"
    );
    assert_eq!(
        switch("tagOf"),
        (
            Vec::from([(1_usize, 0_u32), (2_usize, 0_u32)]),
            integer.clone()
        ),
        "a field each constructor declares at its own position"
    );
    assert_eq!(
        switch("secondAbove"),
        (Vec::from([(2_usize, 0_u32)]), integer),
        "a parameter's field read at the argument the written type gives it"
    );
    assert_accepted(&judged(&module, &mut arena));
}

/// #1106: a field some constructor of the value's family declares none of is
/// refused at the field, naming that constructor; a field whose type names a
/// field before it is refused as unannotated where its position states no
/// answer.
#[test]
fn a_data_field_some_constructor_lacks_is_refused_1106()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!(
            "tests/fixtures/a-data-field-some-constructor-lacks-is-refused-1106-module.gandr"
        )),
        &mut arena,
    );
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("startOf")),
            LoweringRefusal::PartialField { field, constructor, .. }
                if field.as_ref() == "start" && constructor.as_ref() == "Dot"
        ),
        "{:?}",
        refusal_of(&module, SurfaceName::from("startOf"))
    );
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("sizeOf")),
            LoweringRefusal::OutOfFragment {
                boundary: FragmentBoundary::Unannotated,
                ..
            }
        ),
        "{:?}",
        refusal_of(&module, SurfaceName::from("sizeOf"))
    );
}

/// #2089: a match that writes its answer has its root ascribed it, an
/// integer test's case under its comparison's binder, so it synthesises where
/// nothing states its type; a data case carries the answer as its motive
/// alone.
#[test]
fn a_written_answer_ascribes_the_match_2089()
{
    let source = include_str!("tests/fixtures/a-written-answer-ascribes-the-match-2089.gandr");
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source), &mut arena);
    let bound = |name| {
        let tail = tail_of(&arena, body_named(&module, SurfaceName::from(name)));
        let Some(&Computation::Bind(matched, _)) = arena.computation(tail)
        else {
            panic!("`{name}` runs its match: {:?}", arena.computation(tail));
        };
        matched
    };
    let compared = bound("bound");
    let Some(&Computation::Bind(_, case)) = arena.computation(compared)
    else {
        panic!(
            "the integer test binds its comparison: {:?}",
            arena.computation(compared)
        );
    };
    assert!(
        matches!(
            arena.computation(case),
            Some(&Computation::Ascribe { body, .. })
                if matches!(arena.computation(body), Some(&Computation::Case { .. }))
        ),
        "the case under the comparison is ascribed the written answer: {:?}",
        arena.computation(case)
    );
    let counted = bound("counted");
    assert!(
        matches!(
            arena.computation(counted),
            Some(&Computation::DataCase { .. })
        ),
        "a data case carries its answer as its motive alone: {:?}",
        arena.computation(counted)
    );
    assert_accepted(&judged(&module, &mut arena));
}

/// The leading lambdas of `computation`, outermost first, and the computation
/// under them.
///
/// # Specification
/// trivial.
fn under_lambdas(
    arena: &CoreArena,
    mut computation: ComputationId,
) -> (Vec<ComputationId>, ComputationId)
{
    let mut lambdas = Vec::new();
    while let Some(&Computation::Lambda(under)) = arena.computation(computation) {
        lambdas.push(computation);
        computation = under;
    }

    (lambdas, computation)
}

/// Clauses over `(Nat, Nat) => Nat` bind one lambda per column under the
/// fixpoint, and the tree switches on the column the patterns test: the first
/// for `plus`, the second for `add`, each read as its lambda's variable. A
/// recursion through a written parameter, `scale(by)`, and overlapping
/// clauses, `max`, check beside them.
#[test]
fn clauses_match_one_column_per_arrow()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!("fixture/clauses.gandr")),
        &mut arena,
    );
    for (name, column) in [("plus", 1_u32), ("add", 0_u32)] {
        let Some(&Value::Thunk(fixpoint)) =
            arena.value(body_named(&module, SurfaceName::from(name)))
        else {
            panic!("`{name}` lowers to a thunk");
        };
        let Some(&Computation::Fixpoint { body, .. }) = arena.computation(fixpoint)
        else {
            panic!(
                "`{name}`'s columns stand under its fixpoint: {:?}",
                arena.computation(fixpoint)
            );
        };
        let (lambdas, tree) = under_lambdas(&arena, body);
        assert_eq!(
            lambdas.len(),
            2_usize,
            "`{name}` binds one lambda per column"
        );
        let Some(&Computation::DataCase {
            scrutinee,
            ref branches,
            ..
        }) = arena.computation(tree)
        else {
            panic!(
                "`{name}` switches on a column: {:?}",
                arena.computation(tree)
            );
        };
        assert_eq!(
            arena.value(scrutinee),
            Some(&variable(DeBruijnIndex::from(column))),
            "`{name}` switches on the column its patterns test"
        );
        assert_eq!(branches.len(), 2_usize);
    }
    assert_accepted(&judged(&module, &mut arena));
}

/// A clause of one pattern more than the stated type has columns is refused at
/// the extra pattern.
#[test]
fn a_clause_of_too_many_patterns_is_refused()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!("{NAT}def f : Nat -> Nat where {{ | m, n => m }}\n");
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let extra = source.find("n =>").expect("the second pattern is written");
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("f")),
            LoweringRefusal::MalformedForm {
                span,
                fault: crate::error::FormFault::ExtraOperand,
                ..
            } if usize::from(span.start()) == extra
        ),
        "{:?}",
        outcome_of(&module, SurfaceName::from("f"))
    );
}

/// A guard reads its clause's variables, `m` in `| Succ(m) if isZero m`, and
/// tests a boolean behind the clause's leaf; a name the clause does not bind
/// is unresolved there.
#[test]
fn a_guard_reads_its_clause_s_variables()
{
    let mut arena = CoreArena::new();
    let source = include_str!("fixture/guards.gandr");
    let module = lowered(SourceText::from(source), &mut arena);
    let tree = tail_of(&arena, body_named(&module, SurfaceName::from("pred")));
    assert!(
        reachable(&arena, tree)
            .into_iter()
            .any(|at| matches!(arena.computation(at), Some(&Computation::Case { .. }))),
        "the guard is tested by a case on its boolean"
    );
    let stray = source.find("isZero k").map(|at| at.saturating_add(7_usize));
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("stray")),
            LoweringRefusal::UnresolvedName { span, name }
                if Some(usize::from(span.start())) == stray && name == "k".into()
        ),
        "{:?}",
        outcome_of(&module, SurfaceName::from("stray"))
    );
    assert_accepted(&judged(&module, &mut arena));
}

/// A matching lambda over two columns binds two lambdas, and its tree switches
/// on the column its patterns test, the outer lambda's.
#[test]
fn a_matching_lambda_binds_one_lambda_per_column()
{
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        "{NAT}def first : (Nat, Nat) -> Nat = fun {{ | Zero, n => n | Succ(m), _ => m }};\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let body = body_named(&module, SurfaceName::from("first"));
    let Some(&(Value::Thunk(lambda) | Value::Nested(lambda))) = arena.value(body)
    else {
        panic!("the definition is the lambda: {:?}", arena.value(body));
    };
    let (lambdas, tree) = under_lambdas(&arena, lambda);
    assert_eq!(lambdas.len(), 2_usize, "one lambda per column");
    assert!(
        matches!(
            arena.computation(tree),
            Some(&Computation::DataCase { scrutinee, .. })
                if arena.value(scrutinee) == Some(&variable(DeBruijnIndex::from(1_u32)))
        ),
        "the tree switches on the first column: {:?}",
        arena.computation(tree)
    );
    assert_accepted(&judged(&module, &mut arena));
}

/// A constructor passed for a clause column takes the column's type, the
/// parameter before it read from the call: `length(Nat, Cons(Zero, …))`
/// checks with no annotation on the list.
#[test]
fn a_clause_column_types_its_call_s_argument()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        SourceText::from(include_str!("fixture/clause-calls.gandr")),
        &mut arena,
    );
    for name in ["two", "one"].map(SurfaceName::from) {
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

/// #5373: a pair nested in the field of a pair, both returned against the
/// call of a definition that computes the pair type, was dropped as
/// `Unminted`, an engine fault. The inner pair's classifier is the outer
/// pair's field type, which the lowering reads off the outer classifier's
/// arguments, and the outer classifier is the decode of the call, no data
/// type. The declaration is now refused by name at the inner pair, as a
/// constructor that needs a type the source does not state. The inner pair
/// ascribed its pair type lowers, and the checker accepts it.
#[test]
fn a_pair_in_a_field_at_a_computed_pair_type_is_refused_by_name_5373()
{
    let family = include_str!(
        "tests/fixtures/a-pair-in-a-field-at-a-computed-pair-type-is-refused-by-name-5373-family.gandr"
    );
    let mut arena = CoreArena::new();
    let source =
        alloc::format!("{family}def nested(k : Nat) -> twoType(Z) = MkP Z (MkP Z *{{}});\n");
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let refusal = refusal_of(&module, SurfaceName::from("nested"));
    let LoweringRefusal::OutOfFragment {
        span,
        sort: FragmentSort::Value,
        boundary: FragmentBoundary::Unannotated,
        ..
    } = refusal
    else {
        panic!("`nested` is refused as unannotated: {refusal:?}");
    };
    assert_eq!(
        source.get(usize::from(span.start()) .. usize::from(span.end())),
        Some("MkP Z *{}"),
        "the refusal stands at the inner pair"
    );
    let mut arena = CoreArena::new();
    let source = alloc::format!(
        include_str!(
            "tests/unformatted/a-pair-in-a-field-at-a-computed-pair-type-is-refused-by-name-5373.gandr"
        ),
        family = family
    );
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    assert!(
        matches!(
            outcome_of(&module, SurfaceName::from("ascribed")),
            DeclarationOutcome::Completed { .. }
        ),
        "`ascribed` lowers: {:?}",
        outcome_of(&module, SurfaceName::from("ascribed"))
    );
    assert_accepted(&judged(&module, &mut arena));
}
