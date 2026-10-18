//! Bridge witnesses: the identity fold read in bridge mode at function,
//! universe and recursive codes, its refusal at a sealed type, and the
//! identity reading of the same codes beside each.

use alloc::string::ToString as _;
use alloc::vec::Vec;

use gandr_kernel_strata::Level;
use gandr_kernel_strata::LevelConstant;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::LevelSignature;
use gandr_kernel_term::SealExtent;
use gandr_kernel_term::SealScope;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueTypeId;

use super::IdentityError;
use super::bridge_fibre;
use super::tests::bool_returns;
use super::tests::closed;
use super::tests::forced;
use super::tests::persisted;
use super::tests::quantified;
use crate::check::check_closed_value;
use crate::conv::Convertibility;
use crate::conv::convertible_value_types;
use crate::env::Environment;
use crate::error::ExpectedValueShape;
use crate::error::KernelError;
use crate::error::ValueTypeHead;
use crate::identity_recursion::HigherEvaluation;
use crate::identity_recursion::Quantified;
use crate::identity_recursion::function_fixtures::apply_to;
use crate::identity_recursion::function_fixtures::boolean;
use crate::identity_recursion::function_fixtures::higher;
use crate::identity_recursion::function_fixtures::normal_form;
use crate::identity_recursion::function_fixtures::pointwise;
use crate::identity_recursion::function_fixtures::thunk_type;

/// The value universe at the constant level `level`.
///
/// # Specification
/// trivial.
fn universe(
    arena: &mut TermArena,
    level: LevelConstant,
) -> ValueTypeId
{
    arena.value_type_universe(GroundSort::Value, Level::constant(level))
}

/// `thunk (λ_. return output)`, a function ignoring its one argument.
///
/// # Specification
/// trivial.
fn constant(
    arena: &mut TermArena,
    output: ValueId,
) -> ValueId
{
    let body = arena.computation_return(output);
    let lambda = arena.computation_lambda(body);
    arena.value_thunk(lambda)
}

/// `thunk (λ_. λ_. return code)`, the relation relating every pair by the
/// one code.
///
/// # Specification
/// trivial.
fn relating_by(
    arena: &mut TermArena,
    code: ValueId,
) -> ValueId
{
    let body = arena.computation_return(code);
    let inner = arena.computation_lambda(body);
    let outer = arena.computation_lambda(inner);
    arena.value_thunk(outer)
}

/// The relation type `U (El_level left → El_level right → F U_level)`.
///
/// # Specification
/// trivial.
fn relations(
    arena: &mut TermArena,
    level: LevelConstant,
    [left, right]: [ValueId; 2],
) -> ValueTypeId
{
    let target = || Level::constant(level);
    let kinds = universe(arena, level);
    let returner = arena.comp_type_returner(kinds);
    let second = arena.value_type_element(right, target());
    let inner = arena.comp_type_arrow(second, returner);
    let first = arena.value_type_element(left, target());
    let outer = arena.comp_type_arrow(first, inner);
    arena.value_type_thunk(outer)
}

/// The list `[elements…]`, its first element outermost.
///
/// # Specification
/// trivial.
fn list(
    arena: &mut TermArena,
    elements: &[ValueId],
) -> ValueId
{
    let mut list = arena.value_list_nil();
    for &element in elements.iter().rev() {
        list = arena.value_list_cons(element, list);
    }
    list
}

#[test]
fn a_bridge_at_a_function_code_is_the_family_over_argument_bridges()
{
    let mut arena = TermArena::new();
    let boolean = boolean(&mut arena);
    let functions = boolean.function;
    let unit = arena.value_unit();

    // `Br (Bool → Bool) (not ∘ not) id` is the family over Bool's argument
    // bridges: one component per constructor, each output at `Br Bool b b`.
    let bridged = arena.value_type_bridge(functions, boolean.double, boolean.identity);
    let family = higher(&mut arena, &boolean, (boolean.double, boolean.identity), [
        (boolean.truth, boolean.truth),
        (boolean.falsity, boolean.falsity),
    ]);
    let family = persisted(&mut arena, &family);
    check_closed_value(&mut arena, family, bridged).expect("not ∘ not and id are bridged");
    // `not` and `id` disagree at both arguments: `Br Bool false true` is empty.
    let apart = arena.value_type_bridge(functions, boolean.not, boolean.identity);
    let wrong = higher(&mut arena, &boolean, (boolean.not, boolean.identity), [
        (boolean.falsity, boolean.truth),
        (boolean.truth, boolean.falsity),
    ]);
    let wrong = persisted(&mut arena, &wrong);
    assert!(matches!(
        check_closed_value(&mut arena, wrong, apart),
        Err(KernelError::ValueShapeMismatch {
            expected: ExpectedValueShape::Product,
            ..
        })
    ));

    // The family is the only introduction: bridge mode grants no
    // reflexivity, and a function bridge has no first-order fibre.
    let reflexive = arena.value_type_bridge(functions, boolean.not, boolean.not);
    let here = arena.value_here(boolean.not);
    assert!(matches!(
        check_closed_value(&mut arena, here, reflexive),
        Err(KernelError::ValueShapeMismatch {
            expected: ExpectedValueShape::Path,
            ..
        })
    ));
    assert_eq!(
        check_closed_value(&mut arena, unit, reflexive),
        Err(KernelError::Identity(
            IdentityError::HigherEvaluationRequired
        ))
    );

    // `Br (Unit → Bool) (λ_. true) (λ_. false)` is `Br Unit ⋆ ⋆ → Br Bool
    // true false`, so its one component has no evidence, while `λ_. true`
    // is bridged to itself.
    let unit_type = arena.value_type_unit();
    let points = thunk_type(&mut arena, unit_type, boolean.ty);
    let yes = constant(&mut arena, boolean.truth);
    let no = constant(&mut arena, boolean.falsity);
    let component = |arena: &mut TermArena, functions: (ValueId, ValueId), outputs| {
        let component = pointwise(arena, &[], functions, (unit, unit), outputs, unit);
        persisted(arena, &HigherEvaluation(Vec::from([component])))
    };
    let same = component(&mut arena, (yes, yes), (boolean.truth, boolean.truth));
    let bridged = arena.value_type_bridge(points, yes, yes);
    check_closed_value(&mut arena, same, bridged).expect("λ_. true is bridged to itself");
    let differ = component(&mut arena, (yes, no), (boolean.truth, boolean.falsity));
    let apart = arena.value_type_bridge(points, yes, no);
    assert!(matches!(
        check_closed_value(&mut arena, differ, apart),
        Err(KernelError::ValueShapeMismatch {
            expected: ExpectedValueShape::Product,
            ..
        })
    ));

    // Over `U₀ → Bool` the argument bridge is a relation `El X₀ → El X₁ →
    // U₀`, so one generic component, under the two codes and the relation,
    // covers every argument.
    let kinds = universe(&mut arena, LevelConstant::from(0_u64));
    let over_types = thunk_type(&mut arena, kinds, boolean.ty);
    let codes = [1_u32, 0].map(|index| arena.value_variable(DeBruijnIndex::from(index)));
    let premise = relations(&mut arena, LevelConstant::from(0_u64), codes);
    let context = [kinds, kinds, premise];
    let left = arena.value_variable(DeBruijnIndex::from(2_u32));
    let right = arena.value_variable(DeBruijnIndex::from(1_u32));
    let generic = |arena: &mut TermArena, functions: (ValueId, ValueId), outputs| {
        let component = pointwise(arena, &context, functions, (left, right), outputs, unit);
        persisted(arena, &HigherEvaluation(Vec::from([component])))
    };
    let parametric = generic(&mut arena, (yes, yes), (boolean.truth, boolean.truth));
    let bridged = arena.value_type_bridge(over_types, yes, yes);
    check_closed_value(&mut arena, parametric, bridged)
        .expect("λ_. true is bridged to itself over the universe");
    let differ = generic(&mut arena, (yes, no), (boolean.truth, boolean.falsity));
    let apart = arena.value_type_bridge(over_types, yes, no);
    assert!(matches!(
        check_closed_value(&mut arena, differ, apart),
        Err(KernelError::ValueShapeMismatch {
            expected: ExpectedValueShape::Product,
            ..
        })
    ));
    // The identity reading of the same code is the path universe's, which
    // a generic component does not cover: the clause is bridge mode's own.
    let identity = arena.value_type_path(over_types, yes, yes);
    assert!(check_closed_value(&mut arena, parametric, identity).is_err());

    // A bridge carries no eliminator: related application reads a path.
    let source = arena.value_variable(DeBruijnIndex::from(2_u32));
    let body = arena.computation_return(source);
    let bound = arena.value_variable(DeBruijnIndex::from(0_u32));
    let applied =
        arena.computation_related_application(bound, (boolean.truth, boolean.truth), unit, body);
    let lambda = arena.computation_lambda(applied);
    let lambda = arena.value_thunk(lambda);
    let returns = arena.comp_type_returner(boolean.ty);
    let arrow = arena.comp_type_arrow(reflexive, returns);
    let declared = arena.value_type_thunk(arrow);
    assert!(matches!(
        check_closed_value(&mut arena, lambda, declared),
        Err(KernelError::ValueShapeMismatch {
            expected: ExpectedValueShape::Path,
            ..
        })
    ));
}

#[test]
fn a_quantified_evaluation_relates_under_a_bridge_premise()
{
    // `λf. f(true)` over `U (Bool → F Bool)` is bridged to itself: its one
    // generic input is two functions and the bridge between them, and each
    // Bool output returns on both sides.
    let mut arena = TermArena::new();
    let boolean = boolean(&mut arena);
    let inner = boolean.function;
    let outer = thunk_type(&mut arena, inner, boolean.ty);
    let [first, second, premise] =
        [2_u32, 1, 0].map(|index| arena.value_variable(DeBruijnIndex::from(index)));
    let bridge = arena.value_type_bridge(inner, second, premise);
    let context = [inner, inner, bridge];
    let apply_true = apply_to(&mut arena, boolean.truth);
    let stuck = |arena: &mut TermArena, function: ValueId| {
        let claim = forced(arena, apply_true, function);
        let body = forced(arena, function, boolean.truth);
        let normal = closed(arena, &context, body);
        normal_form(arena, &context, claim, normal)
    };
    let fibre = DeBruijnIndex::from(0_u32);
    let application = Quantified::Apply {
        fibre,
        left: stuck(&mut arena, first),
        right: stuck(&mut arena, second),
    };
    let [on_true, on_false] = bool_returns(&mut arena, &context, &boolean);
    let steps = quantified(&mut arena, &[application, on_true, on_false]);
    let bridged = arena.value_type_bridge(outer, apply_true, apply_true);
    check_closed_value(&mut arena, steps, bridged).expect("λf. f(true) under a bridge premise");
}

#[test]
fn a_bridge_at_the_universe_is_a_relation()
{
    let mut arena = TermArena::new();
    let boolean = boolean(&mut arena);
    let unit_type = arena.value_type_unit();
    let unit = arena.value_unit();
    let kinds = universe(&mut arena, LevelConstant::from(0_u64));
    let unit_code = arena.value_quote(unit_type);
    let bool_code = arena.value_quote(boolean.ty);

    // `Br U₀ ⌜Unit⌝ ⌜Bool⌝` is the type of relations `El ⌜Unit⌝ → El ⌜Bool⌝
    // → U₀`, and a relation inhabits it.
    let fibre = bridge_fibre(&mut arena, kinds, unit_code, bool_code).expect("the universe clause");
    let expected = relations(&mut arena, LevelConstant::from(0_u64), [
        unit_code, bool_code,
    ]);
    assert_eq!(
        convertible_value_types(&arena, fibre, expected),
        Convertibility::Convertible
    );
    let bridged = arena.value_type_bridge(kinds, unit_code, bool_code);
    let total = relating_by(&mut arena, unit_code);
    check_closed_value(&mut arena, total, bridged).expect("the total relation");
    // A relation returns codes, and the bridge is a relation, not a tuple.
    let to_unit = relating_by(&mut arena, unit);
    for (value, head) in [
        (to_unit, ValueTypeHead::Universe),
        (unit, ValueTypeHead::Thunk),
    ] {
        assert!(matches!(
            check_closed_value(&mut arena, value, bridged),
            Err(KernelError::ValueShapeMismatch {
                expected: ExpectedValueShape::Product,
                actual,
            }) if actual.head() == head
        ));
    }
    // No reflexivity: the relation a code bears to itself is supplied.
    let reflexive = arena.value_type_bridge(kinds, unit_code, unit_code);
    let here = arena.value_here(unit_code);
    assert!(matches!(
        check_closed_value(&mut arena, here, reflexive),
        Err(KernelError::ValueShapeMismatch {
            expected: ExpectedValueShape::Path,
            ..
        })
    ));
    // Nor transport along one, in the decoding family `x. El x`.
    let endpoint = arena.value_variable(DeBruijnIndex::from(0_u32));
    let motive = arena.value_type_element(endpoint, Level::zero());
    let transport = arena.computation_path_transport(motive, endpoint, unit);
    let lambda = arena.computation_lambda(transport);
    let lambda = arena.value_thunk(lambda);
    let decoded = arena.value_type_element(unit_code, Level::zero());
    let returns = arena.comp_type_returner(decoded);
    let arrow = arena.comp_type_arrow(reflexive, returns);
    let declared = arena.value_type_thunk(arrow);
    assert!(matches!(
        check_closed_value(&mut arena, lambda, declared),
        Err(KernelError::ValueShapeMismatch {
            expected: ExpectedValueShape::Path,
            actual,
        }) if actual.head() == ValueTypeHead::Bridge
    ));

    // A nested universe: `Br U₁ ⌜U₀⌝ ⌜U₀⌝` relates into `U₁`.
    let large = universe(&mut arena, LevelConstant::from(1_u64));
    let small = arena.value_quote(kinds);
    let fibre = bridge_fibre(&mut arena, large, small, small).expect("the universe clause at one");
    let expected = relations(&mut arena, LevelConstant::from(1_u64), [small, small]);
    assert_eq!(
        convertible_value_types(&arena, fibre, expected),
        Convertibility::Convertible
    );
    let bridged = arena.value_type_bridge(large, small, small);
    let total = relating_by(&mut arena, small);
    check_closed_value(&mut arena, total, bridged).expect("the total relation at level one");

    // At `U₀ × U₀` the bridge is a relation per component.
    let pairs = arena.value_type_product(&[kinds, kinds]);
    let forward = arena.value_tuple(&[unit_code, bool_code]);
    let backward = arena.value_tuple(&[bool_code, unit_code]);
    let bridged = arena.value_type_bridge(pairs, forward, backward);
    let total = relating_by(&mut arena, unit_code);
    let both = arena.value_tuple(&[total, total]);
    check_closed_value(&mut arena, both, bridged).expect("a relation per component");
}

#[test]
fn a_bridge_at_a_recursive_code_is_the_relation_lifting()
{
    let mut arena = TermArena::new();
    let boolean = boolean(&mut arena);
    let unit = arena.value_unit();
    let lists = arena.value_type_list(boolean.ty);
    let empty = list(&mut arena, &[]);
    let truth = list(&mut arena, &[boolean.truth]);
    let falsity = list(&mut arena, &[boolean.falsity]);

    // nil/nil is `Unit`; cons/cons the head bridge beside the tails'.
    let bridged = arena.value_type_bridge(lists, empty, empty);
    check_closed_value(&mut arena, unit, bridged).expect("nil is bridged to nil");
    let bridged = arena.value_type_bridge(lists, truth, truth);
    let lifted = arena.value_tuple(&[unit, unit]);
    check_closed_value(&mut arena, lifted, bridged).expect("[true] is bridged to itself");
    let pair = list(&mut arena, &[boolean.truth, boolean.falsity]);
    let bridged = arena.value_type_bridge(lists, pair, pair);
    let nested = arena.value_tuple(&[unit, lifted]);
    check_closed_value(&mut arena, nested, bridged).expect("the tail's bridge is the lifting's");
    // Unequal heads, or a nil against a cons, have an empty lifting.
    let bridged = arena.value_type_bridge(lists, truth, falsity);
    assert!(check_closed_value(&mut arena, lifted, bridged).is_err());
    let bridged = arena.value_type_bridge(lists, empty, truth);
    assert!(check_closed_value(&mut arena, unit, bridged).is_err());
    // The identity reading of the same list is still observed only through
    // a guarded observation.
    let identity = arena.value_type_path(lists, truth, truth);
    assert_eq!(
        check_closed_value(&mut arena, lifted, identity),
        Err(KernelError::Identity(IdentityError::RecursiveObservation))
    );

    // `Br (List U₀) [⌜Unit⌝] [⌜Bool⌝]` lifts the universe's clause: a
    // relation for the heads beside the tails' bridge.
    let kinds = universe(&mut arena, LevelConstant::from(0_u64));
    let codes = arena.value_type_list(kinds);
    let unit_type = arena.value_type_unit();
    let unit_code = arena.value_quote(unit_type);
    let bool_code = arena.value_quote(boolean.ty);
    let left = list(&mut arena, &[unit_code]);
    let right = list(&mut arena, &[bool_code]);
    let bridged = arena.value_type_bridge(codes, left, right);
    let total = relating_by(&mut arena, unit_code);
    let lifted = arena.value_tuple(&[total, unit]);
    check_closed_value(&mut arena, lifted, bridged).expect("a relation beside the tails' bridge");

    // A neutral list suspends the lifting: its fibre is neutral.
    let bound = arena.value_variable(DeBruijnIndex::from(0_u32));
    let open = arena.value_type_bridge(lists, bound, empty);
    let returns = arena.comp_type_returner(open);
    let pi = arena.comp_type_pi(lists, returns);
    let declared = arena.value_type_thunk(pi);
    let body = arena.computation_return(unit);
    let lambda = arena.computation_lambda(body);
    let native = arena.value_thunk(lambda);
    assert_eq!(
        check_closed_value(&mut arena, native, declared),
        Err(KernelError::Identity(IdentityError::NeutralFibre))
    );
}

#[test]
fn the_codes_outside_the_bridge_clauses_are_refused_by_name()
{
    // Each code the bridge fold has no clause for is refused where its
    // fibre is read, by the name the identity reading of it gives.
    let mut arena = TermArena::new();
    let boolean = boolean(&mut arena);
    let unit = arena.value_unit();
    let family = higher(&mut arena, &boolean, (boolean.double, boolean.identity), [
        (boolean.truth, boolean.truth),
        (boolean.falsity, boolean.falsity),
    ]);
    let family = persisted(&mut arena, &family);
    let outside = |result: Result<_, KernelError>, head| matches!(result, Err(KernelError::Identity(IdentityError::OutsideFold(witness))) if witness.head() == head);
    // A dependent arrow: the function clause reads the non-dependent one.
    let returns = arena.comp_type_returner(boolean.ty);
    let pi = arena.comp_type_pi(boolean.ty, returns);
    let dependent = arena.value_type_thunk(pi);
    let dependent = arena.value_type_bridge(dependent, boolean.double, boolean.identity);
    assert!(outside(
        check_closed_value(&mut arena, family, dependent),
        ValueTypeHead::Thunk
    ));
    // A function over a list argument: its coverage needs the guarded
    // observation a list's inhabitants are read through.
    let lists = arena.value_type_list(boolean.ty);
    let over_lists = thunk_type(&mut arena, lists, boolean.ty);
    let yes = constant(&mut arena, boolean.truth);
    let over_lists = arena.value_type_bridge(over_lists, yes, yes);
    assert_eq!(
        check_closed_value(&mut arena, family, over_lists),
        Err(KernelError::Identity(IdentityError::RecursiveObservation))
    );
    // The path universe, and a bridge at a bridge.
    let unit_type = arena.value_type_unit();
    let unit_code = arena.value_quote(unit_type);
    let paths = arena.value_type_path_universe(unit_code, unit_code);
    let refl = arena.value_path_refl(unit_code);
    assert!(outside(
        bridge_fibre(&mut arena, paths, refl, refl).map(|_| ()),
        ValueTypeHead::PathUniverse
    ));
    let inner = arena.value_type_bridge(boolean.ty, boolean.truth, boolean.truth);
    assert!(outside(
        bridge_fibre(&mut arena, inner, unit, unit).map(|_| ()),
        ValueTypeHead::Bridge
    ));
}

#[test]
fn a_bridge_at_a_sealed_type_is_refused()
{
    // An atom, a point of it and a function into it; then bridges whose
    // domains reach the atom directly, through a function's result and
    // through a list's elements.
    let mut environment = Environment::new();
    let mut staging = environment.stage();
    let kind = universe(staging.arena(), LevelConstant::from(0_u64));
    let integer = staging.arena().value_type_base(BaseType::Integer);
    let declaration = staging.abstract_type(
        LevelSignature::monomorphic(),
        kind,
        integer,
        SealScope::Closed(SealExtent::from(0_usize)),
    );
    let atom = environment
        .add_decl(declaration)
        .expect("an abstract type at the value universe")
        .position();
    let mut staging = environment.stage();
    let sealed = staging.arena().value_type_abstract(atom);
    let declaration = staging.axiom(LevelSignature::monomorphic(), sealed);
    let point = environment
        .add_decl(declaration)
        .expect("a sealed point")
        .position();
    let mut staging = environment.stage();
    let (to_atom, body) = into_atom(staging.arena(), atom, point);
    let declaration = staging.def(LevelSignature::monomorphic(), to_atom, body);
    let function = environment
        .add_decl(declaration)
        .expect("a function into the atom")
        .position();
    let names = [atom, point, function];

    let bridged = |environment: &mut Environment, at: Domain| {
        let mut staging = environment.stage();
        let arena = staging.arena();
        let (domain, endpoint) = at(arena, names);
        let bridged = arena.value_type_bridge(domain, endpoint, endpoint);
        let unit = arena.value_unit();
        let declaration = staging.def(LevelSignature::monomorphic(), bridged, unit);
        environment.add_decl(declaration).map(|_| ())
    };
    let admitted = environment.entries().len();
    let at_atom = bridged(&mut environment, |arena, [atom, point, _]| {
        (arena.value_type_abstract(atom), arena.value_constant(point))
    });
    let Err(KernelError::Identity(error @ IdentityError::BridgeAtSealedType(_))) = at_atom
    else {
        panic!("a bridge at a sealed atom formed: {at_atom:?}");
    };
    assert_eq!(error.to_string(), "a bridge at a sealed type");
    let through_function = bridged(&mut environment, |arena, [atom, point, function]| {
        let (to_atom, _) = into_atom(arena, atom, point);
        (to_atom, arena.value_constant(function))
    });
    assert!(matches!(
        through_function,
        Err(KernelError::Identity(IdentityError::BridgeAtSealedType(_)))
    ));
    let in_a_list = bridged(&mut environment, |arena, [atom, _, _]| {
        let sealed = arena.value_type_abstract(atom);
        (arena.value_type_list(sealed), arena.value_list_nil())
    });
    assert!(matches!(
        in_a_list,
        Err(KernelError::Identity(IdentityError::BridgeAtSealedType(_)))
    ));
    assert_eq!(environment.entries().len(), admitted);

    // The identity at the same atom still forms: the refusal is bridge
    // mode's alone.
    let mut staging = environment.stage();
    let arena = staging.arena();
    let sealed = arena.value_type_abstract(atom);
    let point_value = arena.value_constant(point);
    let identity = arena.value_type_path(sealed, point_value, point_value);
    let here = arena.value_here(point_value);
    let declaration = staging.def(LevelSignature::monomorphic(), identity, here);
    environment
        .add_decl(declaration)
        .expect("reflexivity at a sealed atom");
}

/// A bridge's domain and its endpoint, minted from the atom, its point and
/// the function into it.
type Domain = fn(&mut TermArena, [ConstantIndex; 3]) -> (ValueTypeId, ValueId);

/// `U (Bool → F atom)` and the function constantly at `point`.
///
/// # Specification
/// trivial.
fn into_atom(
    arena: &mut TermArena,
    atom: ConstantIndex,
    point: ConstantIndex,
) -> (ValueTypeId, ValueId)
{
    let unit_type = arena.value_type_unit();
    let bool_type = arena.value_type_sum(&[unit_type, unit_type]);
    let sealed = arena.value_type_abstract(atom);
    let to_atom = thunk_type(arena, bool_type, sealed);
    let point = arena.value_constant(point);
    (to_atom, constant(arena, point))
}
