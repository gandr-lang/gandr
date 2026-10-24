use alloc::collections::BTreeMap;
use alloc::vec;
use alloc::vec::Vec;

use gandr_kernel_strata::Level;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldPosition;
use gandr_kernel_term::FixpointEvidence;
use gandr_kernel_term::FreeCell;
use gandr_kernel_term::FreeCells;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::OccurrenceSite;
use gandr_kernel_term::Presentation;
use gandr_kernel_term::RuleNode;
use quenchant_shape::shape::Maybe;

use super::Uncovered;
use super::equality;
use crate::Binders;
use crate::Computation;
use crate::ComputationId;
use crate::CoreArena;
use crate::DataSignature;
use crate::Sort;
use crate::Value;
use crate::ValueId;
use crate::ValueTypeId;
use crate::Zone;
use crate::primitive::PrimitiveType;

/// `Type[+, 0]`, every test declaration's universe.
///
/// # Specification
/// trivial.
fn kind(arena: &mut CoreArena) -> ValueTypeId
{
    arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero())
}

/// The derivation of `position` over `signatures`.
///
/// # Specification
/// trivial.
fn derived(
    arena: &mut CoreArena,
    position: ConstantIndex,
    signatures: &BTreeMap<ConstantIndex, DataSignature>,
) -> Result<super::Equality, Uncovered>
{
    equality(arena, position, &|at| signatures.get(&at))
}

/// More binders than any derivation opens: a value strengthening past them
/// names no binder at all.
///
/// # Specification
/// trivial.
fn far() -> Binders
{
    Binders::from(1_000_u32)
}

/// The computation a thunk suspends.
///
/// # Specification
/// trivial.
fn suspended(
    arena: &CoreArena,
    value: ValueId,
) -> ComputationId
{
    match arena.value(value) {
        Some(&Value::Thunk(body)) => body,
        other => panic!("a thunk, not {other:?}"),
    }
}

/// `computation` past `count` lambdas.
///
/// # Specification
/// trivial.
fn under(
    arena: &CoreArena,
    computation: ComputationId,
    count: Binders,
) -> ComputationId
{
    let mut focus = computation;
    for _lambda in 0 .. u32::from(count) {
        focus = match arena.computation(focus) {
            Some(&Computation::Lambda(body)) => body,
            other => panic!("a lambda, not {other:?}"),
        };
    }
    focus
}

/// A refused derivation's name, its declarations and its fault.
type Case = (&'static str, Vec<(usize, DataSignature)>, Uncovered);

/// The branches of a nominal case.
///
/// # Specification
/// trivial.
fn branches(
    arena: &CoreArena,
    computation: ComputationId,
) -> Vec<ComputationId>
{
    match arena.computation(computation) {
        Some(&Computation::DataCase { ref branches, .. }) => branches.clone(),
        other => panic!("a nominal case, not {other:?}"),
    }
}

/// The variable index `value` reads.
///
/// # Specification
/// trivial.
fn index(
    arena: &CoreArena,
    value: ValueId,
) -> DeBruijnIndex
{
    match arena.value(value) {
        Some(&Value::Variable {
            zone: Zone::Intuitionistic,
            index,
        }) => index,
        other => panic!("a variable, not {other:?}"),
    }
}

/// The body of a derivation's fixpoint, past `rec`, `a` and `b`, with the
/// evidence it claims.
///
/// # Specification
/// trivial.
fn fixed(
    arena: &CoreArena,
    body: ValueId,
) -> (ComputationId, FixpointEvidence)
{
    match arena.computation(suspended(arena, body)) {
        Some(&Computation::Fixpoint { body, evidence }) => {
            (under(arena, body, Binders::from(2_u32)), evidence)
        },
        other => panic!("a fixpoint, not {other:?}"),
    }
}

#[test]
fn a_point_derives_a_closed_equality_of_two_points()
{
    // Point(x : Integer, y : Integer): `U (Point → Point → F Bool)`, its one
    // arm comparing both fields with the integer primitive, closed.
    let mut arena = CoreArena::new();
    let universe = kind(&mut arena);
    let integer = arena.value_type_base(gandr_kernel_term::BaseType::Integer);
    let signatures = BTreeMap::from([(
        ConstantIndex::from(0_usize),
        DataSignature::new(vec![], vec![vec![integer, integer]], universe),
    )]);
    let equal = derived(&mut arena, ConstantIndex::from(0_usize), &signatures)
        .expect("a point derives its equality");

    let point = arena.value_type_data(ConstantIndex::from(0_usize), vec![]);
    let boolean = PrimitiveType::Boolean.mint(&mut arena);
    let answer = arena.comp_type_returner(boolean);
    let inner = arena.comp_type_arrow(point, answer);
    let outer = arena.comp_type_arrow(point, inner);
    let expected = arena.value_type_thunk(outer);
    assert_eq!(
        crate::equal_type_syntax(&arena, equal.declared(), expected),
        crate::CertificateEquality::Equal,
        "the declared type is the binary predicate"
    );
    assert!(
        matches!(
            crate::strengthen_value(&mut arena, equal.body(), far()),
            Maybe::Present(_)
        ),
        "the body is closed"
    );
    let (case, evidence) = fixed(&arena, equal.body());
    assert_eq!(evidence, FixpointEvidence::StructuralDescent);
    let [arm] = branches(&arena, case)[..]
    else {
        panic!("one constructor, one arm");
    };
    let [matched] = branches(&arena, under(&arena, arm, Binders::from(2_u32)))[..]
    else {
        panic!("one constructor, one inner arm");
    };
    // `r ← x == u; case r { _ ↦ y == v ; _ ↦ return false }`, the fields at
    // levels 3 and 4, the second point's at 5 and 6, seven binders deep.
    let Some(&Computation::Bind(first, rest)) =
        arena.computation(under(&arena, matched, Binders::from(2_u32)))
    else {
        panic!("two fields conjoin by a bind");
    };
    let Some(&Computation::Primitive {
        primitive,
        ref arguments,
    }) = arena.computation(first)
    else {
        panic!("the first field compares with a primitive");
    };
    assert_eq!(primitive.name().as_ref(), "eq");
    let crate::primitive::Arguments::Binary([left, right]) = *arguments
    else {
        panic!("integer equality is binary");
    };
    assert_eq!(
        (index(&arena, left), index(&arena, right)),
        (DeBruijnIndex::from(3_u32), DeBruijnIndex::from(1_u32)),
        "x is three out, u one"
    );
    let Some(&Computation::Case {
        branches: ref arms, ..
    }) = arena.computation(rest)
    else {
        panic!("the verdict is cased on");
    };
    assert!(
        matches!(arena.computation(arms[1]), Some(Computation::Return(_))),
        "a false first field ends the conjunction"
    );

    // A constructor with no fields answers true at its own arm.
    let mut arena = CoreArena::new();
    let universe = kind(&mut arena);
    let signatures = BTreeMap::from([(
        ConstantIndex::from(0_usize),
        DataSignature::new(vec![], vec![vec![], vec![]], universe),
    )]);
    let equal = derived(&mut arena, ConstantIndex::from(0_usize), &signatures)
        .expect("two nullary constructors derive");
    let (case, _) = fixed(&arena, equal.body());
    let arms = branches(&arena, case);
    let inner = branches(&arena, arms[0]);
    assert_eq!(inner.len(), 2, "each arm cases on the second argument");
    assert!(
        matches!(arena.computation(inner[0]), Some(&Computation::Return(truth)) if matches!(arena.value(truth), Some(&Value::Injection(summand, _)) if summand == gandr_kernel_term::Summand::from(0_usize))),
        "the same constructor answers true"
    );
    assert!(
        matches!(arena.computation(inner[1]), Some(&Computation::Return(falsity)) if matches!(arena.value(falsity), Some(&Value::Injection(summand, _)) if summand == gandr_kernel_term::Summand::from(1_usize))),
        "another constructor answers false"
    );
}

#[test]
fn a_recursive_declaration_derives_a_structural_fixpoint()
{
    // Nat: `Succ m` against `Succ n` calls `rec` on the two predecessors.
    let mut arena = CoreArena::new();
    let universe = kind(&mut arena);
    let nat = arena.value_type_data(ConstantIndex::from(0_usize), vec![]);
    let signatures = BTreeMap::from([(
        ConstantIndex::from(0_usize),
        DataSignature::new(vec![], vec![vec![], vec![nat]], universe),
    )]);
    let derived = derived(&mut arena, ConstantIndex::from(0_usize), &signatures)
        .expect("nat derives its equality");
    assert!(
        matches!(
            crate::strengthen_value(&mut arena, derived.body(), far()),
            Maybe::Present(_)
        ),
        "the body is closed"
    );
    let (case, evidence) = fixed(&arena, derived.body());
    assert_eq!(evidence, FixpointEvidence::StructuralDescent);
    let successor = branches(
        &arena,
        under(&arena, branches(&arena, case)[1], Binders::ONE),
    )[1];
    let Some(&Computation::Application(applied, right)) =
        arena.computation(under(&arena, successor, Binders::ONE))
    else {
        panic!("the successor arm applies `rec`");
    };
    let Some(&Computation::Application(head, left)) = arena.computation(applied)
    else {
        panic!("`rec` takes both predecessors");
    };
    let Some(&Computation::Force(recursive)) = arena.computation(head)
    else {
        panic!("`rec` is forced");
    };
    assert_eq!(
        (
            index(&arena, recursive),
            index(&arena, left),
            index(&arena, right)
        ),
        (
            DeBruijnIndex::from(4_u32),
            DeBruijnIndex::from(1_u32),
            DeBruijnIndex::from(0_u32)
        ),
        "`rec` four out, `m` one, `n` innermost"
    );
}

#[test]
fn a_declaration_s_field_of_another_derives_it_in_place()
{
    // Line(from : Point, to : Point, flag : Bool, pair : (Integer, String)):
    // the point's equality is written in place, the flag compared by its
    // injections, the pair component by component.
    let mut arena = CoreArena::new();
    let universe = kind(&mut arena);
    let integer = arena.value_type_base(gandr_kernel_term::BaseType::Integer);
    let string = arena.value_type_base(gandr_kernel_term::BaseType::String);
    let boolean = PrimitiveType::Boolean.mint(&mut arena);
    let pair = arena.value_type_product(&[integer, string]);
    let point = arena.value_type_data(ConstantIndex::from(0_usize), vec![]);
    let signatures = BTreeMap::from([
        (
            ConstantIndex::from(0_usize),
            DataSignature::new(vec![], vec![vec![integer, integer]], universe),
        ),
        (
            ConstantIndex::from(1_usize),
            DataSignature::new(vec![], vec![vec![point, point, boolean, pair]], universe),
        ),
    ]);
    let derived = derived(&mut arena, ConstantIndex::from(1_usize), &signatures)
        .expect("a line derives its equality");
    assert!(
        matches!(
            crate::strengthen_value(&mut arena, derived.body(), far()),
            Maybe::Present(_)
        ),
        "the body is closed"
    );
    let (case, _) = fixed(&arena, derived.body());
    let four = Binders::from(4_u32);
    let matched = branches(&arena, under(&arena, branches(&arena, case)[0], four))[0];
    let Some(&Computation::Bind(first, _)) = arena.computation(under(&arena, matched, four))
    else {
        panic!("four fields conjoin by binds");
    };
    let Some(&Computation::Application(applied, _)) = arena.computation(first)
    else {
        panic!("the point field applies the point's equality");
    };
    let Some(&Computation::Application(head, _)) = arena.computation(applied)
    else {
        panic!("the point's equality takes both points");
    };
    let Some(&Computation::Force(ascribed)) = arena.computation(head)
    else {
        panic!("the point's equality is forced");
    };
    // A thunk synthesises nothing; ascribed its predicate, it is forced.
    let Some(&Value::Ascribe { value: written, .. }) = arena.value(ascribed)
    else {
        panic!("the point's equality is ascribed its type");
    };
    assert!(
        matches!(arena.value(written), Some(Value::Thunk(_)))
            && matches!(
                crate::strengthen_value(&mut arena, written, far()),
                Maybe::Present(_)
            ),
        "the point's equality is a closed thunk written in place"
    );
}

#[test]
fn each_uncovered_declaration_refuses_at_its_site()
{
    let field = |tag: usize, place: usize| OccurrenceSite::Field {
        tag: ConstructorTag::from(tag),
        field: FieldPosition::from(place),
    };
    let at = ConstantIndex::from;
    let mut arena = CoreArena::new();
    let universe = kind(&mut arena);
    let integer = arena.value_type_base(gandr_kernel_term::BaseType::Integer);
    let float = arena.value_type_base(gandr_kernel_term::BaseType::Float64);
    let answer = arena.comp_type_returner(integer);
    let function = arena.comp_type_arrow(integer, answer);
    let thunk = arena.value_type_thunk(function);
    let own = arena.value_type_data(at(0_usize), vec![]);
    let other = arena.value_type_data(at(1_usize), vec![]);
    let nested = arena.value_type_product(&[own, own]);
    let earlier = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let reading = arena.value_type_data(at(1_usize), vec![earlier]);
    let base = || -> alloc::boxed::Box<[RuleNode]> {
        [RuleNode::Constructor(ConstructorTag::from(0_usize))].into()
    };
    let cells = FreeCells::new(at(0_usize), vec![FreeCell::new(base(), base())]);
    let cases: [Case; 7] = [
        (
            "a function field",
            vec![(
                0,
                DataSignature::new(vec![], vec![vec![], vec![integer, thunk]], universe),
            )],
            Uncovered::Field(at(0_usize), field(1, 1)),
        ),
        (
            "a float field",
            vec![(0, DataSignature::new(vec![], vec![vec![float]], universe))],
            Uncovered::Field(at(0_usize), field(0, 0)),
        ),
        (
            "a parameterised declaration",
            vec![(
                0,
                DataSignature::new(vec![universe], vec![vec![]], universe),
            )],
            Uncovered::Applied(at(0_usize)),
        ),
        (
            "a presented declaration",
            vec![(
                0,
                DataSignature::new(vec![], vec![vec![], vec![own], vec![own]], universe)
                    .presented(Presentation::words(cells)),
            )],
            Uncovered::Presented(at(0_usize)),
        ),
        (
            "a dependent field",
            vec![(
                0,
                DataSignature::new(vec![], vec![vec![integer, reading]], universe),
            )],
            Uncovered::Dependent(at(0_usize), field(0, 1)),
        ),
        (
            "a cycle through two declarations",
            vec![
                (0, DataSignature::new(vec![], vec![vec![other]], universe)),
                (1, DataSignature::new(vec![], vec![vec![own]], universe)),
            ],
            Uncovered::Cycle(at(1_usize), field(0, 0)),
        ),
        (
            "a recursive occurrence under a product",
            vec![(
                0,
                DataSignature::new(vec![], vec![vec![], vec![nested]], universe),
            )],
            Uncovered::Nested(at(0_usize), field(1, 0)),
        ),
    ];
    for (what, declared, expected) in cases {
        let signatures: BTreeMap<ConstantIndex, DataSignature> = declared
            .into_iter()
            .map(|(position, signature)| (at(position), signature))
            .collect();
        assert_eq!(
            derived(&mut arena, at(0_usize), &signatures),
            Err(expected),
            "{what} refuses at its site"
        );
    }
    assert_eq!(
        derived(&mut arena, at(0_usize), &BTreeMap::new()),
        Err(Uncovered::Unknown(at(0_usize))),
        "a position with no signature is unknown"
    );
}
