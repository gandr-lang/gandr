use gandr_kernel_term::BaseType;
use gandr_kernel_term::DeBruijnIndex;

use crate::CertificateEquality;
use crate::CoreArena;
use crate::arena::ValueId;
use crate::arena::ValueTypeId;
use crate::syntax::Zone;
use crate::syntax::equal_certificate_syntax;

/// The intuitionistic variable at `index`.
///
/// # Specification
/// trivial.
fn variable(
    arena: &mut CoreArena,
    index: DeBruijnIndex,
) -> ValueId
{
    arena.value_variable(Zone::Intuitionistic, index)
}

/// A carrier that reads the variable at `index`: `El(#index)`.
///
/// # Specification
/// trivial.
fn open_carrier(
    arena: &mut CoreArena,
    index: DeBruijnIndex,
) -> ValueTypeId
{
    let code = variable(arena, index);
    arena.value_type_element(code, gandr_kernel_strata::Level::zero())
}

/// How two built terms compare as syntax.
///
/// # Specification
/// trivial.
fn compared(
    arena: &CoreArena,
    left: crate::arena::ComputationId,
    right: crate::arena::ComputationId,
) -> CertificateEquality
{
    let mut probe = arena.clone();
    let left = probe.value_thunk(left);
    let right = probe.value_thunk(right);
    equal_certificate_syntax(&probe, left, right)
}

#[test]
fn back_transports_reflexivity_into_the_reversed_family()
{
    let mut arena = CoreArena::new();
    let carrier = open_carrier(&mut arena, 1_u32.into());
    let fixed = variable(&mut arena, 0_u32.into());
    let path = variable(&mut arena, 2_u32.into());
    let built = super::back(&mut arena, carrier, fixed, path);

    let lifted_carrier = open_carrier(&mut arena, 2_u32.into());
    let moving = variable(&mut arena, 0_u32.into());
    let lifted_fixed = variable(&mut arena, 1_u32.into());
    let motive = arena.value_type_path(lifted_carrier, moving, lifted_fixed);
    let base = arena.value_here(fixed);
    let expected = arena.computation_path_transport(motive, path, base);
    assert_eq!(
        compared(&arena, built, expected),
        CertificateEquality::Equal,
        "back reverses the family past one binder"
    );

    let unshifted = arena.value_type_path(carrier, moving, fixed);
    let capturing = arena.computation_path_transport(unshifted, path, base);
    assert_eq!(
        compared(&arena, built, capturing),
        CertificateEquality::Different,
        "an unshifted motive captures the outer variables"
    );
}

#[test]
fn back_along_a_flow_rides_stay_into_the_reversed_family()
{
    let mut arena = CoreArena::new();
    let carrier = open_carrier(&mut arena, 1_u32.into());
    let fixed = variable(&mut arena, 0_u32.into());
    let flow = variable(&mut arena, 2_u32.into());
    let built = super::back_flow(&mut arena, carrier, fixed, flow);

    let lifted_carrier = open_carrier(&mut arena, 2_u32.into());
    let moving = variable(&mut arena, 0_u32.into());
    let lifted_fixed = variable(&mut arena, 1_u32.into());
    let motive = arena.value_type_flow(lifted_carrier, moving, lifted_fixed);
    let base = arena.value_stay(fixed);
    let expected = arena.computation_ride(motive, flow, base);
    assert_eq!(
        compared(&arena, built, expected),
        CertificateEquality::Equal,
        "back along a flow moves the source past one binder"
    );

    let covariant = arena.value_type_flow(lifted_carrier, lifted_fixed, moving);
    let covariant = arena.computation_ride(covariant, flow, base);
    assert_eq!(
        compared(&arena, built, covariant),
        CertificateEquality::Different,
        "the reversed family moves the source, not the target"
    );
}

#[test]
fn then_transports_the_first_path_along_the_second()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let start = variable(&mut arena, 0_u32.into());
    let first = variable(&mut arena, 1_u32.into());
    let second = variable(&mut arena, 2_u32.into());
    let built = super::then(&mut arena, integer, start, first, second);

    let lifted_start = variable(&mut arena, 1_u32.into());
    let moving = variable(&mut arena, 0_u32.into());
    let motive = arena.value_type_path(integer, lifted_start, moving);
    let expected = arena.computation_path_transport(motive, second, first);
    assert_eq!(
        compared(&arena, built, expected),
        CertificateEquality::Equal,
        "then moves the right endpoint along the second path"
    );

    let swapped = arena.computation_path_transport(motive, first, second);
    assert_eq!(
        compared(&arena, built, swapped),
        CertificateEquality::Different,
        "transporting along the first path is another term"
    );
}

#[test]
fn cong_applies_the_map_to_the_moving_endpoint()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let function = variable(&mut arena, 0_u32.into());
    let start = variable(&mut arena, 1_u32.into());
    let path = variable(&mut arena, 2_u32.into());
    let built = super::cong(&mut arena, integer, function, start, path);

    let lifted_start = variable(&mut arena, 2_u32.into());
    let lifted_function = variable(&mut arena, 1_u32.into());
    let forced = arena.computation_force(lifted_function);
    let moving = variable(&mut arena, 0_u32.into());
    let applied = arena.computation_application(forced, moving);
    let image = arena.value_returned(applied);
    let motive = arena.value_type_path(integer, lifted_start, image);
    let base = arena.value_here(start);
    let expected = arena.computation_path_transport(motive, path, base);
    assert_eq!(
        compared(&arena, built, expected),
        CertificateEquality::Equal,
        "cong maps the moving endpoint through the function"
    );

    let unshifted = arena.computation_force(function);
    let captured = arena.computation_application(unshifted, moving);
    let captured = arena.value_returned(captured);
    let capturing = arena.value_type_path(integer, lifted_start, captured);
    let capturing = arena.computation_path_transport(capturing, path, base);
    assert_eq!(
        compared(&arena, built, capturing),
        CertificateEquality::Different,
        "an unshifted map reads the motive's own binder"
    );
}

#[test]
fn a_case_answers_at_a_point_by_the_value_its_branch_returns()
{
    let mut arena = CoreArena::new();
    let sort = arena.value_type_data(
        gandr_kernel_term::ConstantIndex::from(0_usize),
        alloc::vec::Vec::new(),
    );
    let point = arena.value_constructor(
        sort,
        gandr_kernel_term::ConstructorTag::from(0_usize),
        alloc::vec::Vec::new(),
    );
    let field = arena.value_unit();
    let fielded = arena.value_constructor(
        sort,
        gandr_kernel_term::ConstructorTag::from(1_usize),
        alloc::vec![field],
    );
    let motive = arena.comp_type_returner(sort);
    let held = variable(&mut arena, 0_u32.into());
    let (at_point, at_fielded) = (
        arena.computation_return(point),
        arena.computation_return(held),
    );
    let branches = [at_point, at_fielded];
    let arities = [0_usize, 1].map(gandr_kernel_term::FieldCount::from);
    assert_eq!(
        super::answer_at(&mut arena, point, motive, &branches, &arities),
        point,
        "a point without fields answers the value its branch returns"
    );

    let case_at = |arena: &CoreArena, answered| {
        matches!(arena.value(answered), Some(&crate::syntax::Value::Returned(case))
                if matches!(arena.computation(case), Some(&crate::syntax::Computation::DataCase { scrutinee, .. }) if scrutinee == point || scrutinee == fielded))
    };
    let answered = super::answer_at(&mut arena, fielded, motive, &branches, &arities);
    assert!(
        case_at(&arena, answered),
        "a point with fields answers the case at it"
    );
    let forced = arena.computation_force(held);
    let computing = [forced, at_fielded];
    let answered = super::answer_at(&mut arena, point, motive, &computing, &arities);
    assert!(
        case_at(&arena, answered),
        "a branch that computes answers the case at the point"
    );
}

/// How two built types compare as syntax, each read as its code.
///
/// # Specification
/// trivial.
fn compared_types(
    arena: &CoreArena,
    left: ValueTypeId,
    right: ValueTypeId,
) -> CertificateEquality
{
    let mut probe = arena.clone();
    let left = probe.value_quote(left);
    let right = probe.value_quote(right);
    equal_certificate_syntax(&probe, left, right)
}

/// `+U (El #from -> -F El #to)`.
///
/// # Specification
/// trivial.
fn written_map(
    arena: &mut CoreArena,
    from: DeBruijnIndex,
    to: DeBruijnIndex,
) -> ValueTypeId
{
    let domain = open_carrier(arena, from);
    let codomain = open_carrier(arena, to);
    let returner = arena.comp_type_returner(codomain);
    let arrow = arena.comp_type_arrow(domain, returner);
    arena.value_type_thunk(arrow)
}

/// The written round trip `+U ((x : El #domain) => -F Path(El #over,
/// outer(inner(x)), x))`, each map the variable at its index under `x`.
///
/// # Specification
/// trivial.
fn written_trip(
    arena: &mut CoreArena,
    [domain, over]: [DeBruijnIndex; 2],
    [inner, outer]: [DeBruijnIndex; 2],
) -> ValueTypeId
{
    let domain = open_carrier(arena, domain);
    let over = open_carrier(arena, over);
    let point = variable(arena, 0_u32.into());
    let inner = variable(arena, inner);
    let forced = arena.computation_force(inner);
    let applied = arena.computation_application(forced, point);
    let midway = arena.value_returned(applied);
    let outer = variable(arena, outer);
    let forced = arena.computation_force(outer);
    let applied = arena.computation_application(forced, midway);
    let there = arena.value_returned(applied);
    let path = arena.value_type_path(over, there, point);
    let returner = arena.comp_type_returner(path);
    let pi = arena.comp_type_pi(domain, returner);
    arena.value_type_thunk(pi)
}

#[test]
fn the_relation_records_state_their_maps_and_trips()
{
    // Two type codes in scope, `A = El #1` and `B = El #0`; each occurrence
    // reads them past the binders it stands under.
    let mut arena = CoreArena::new();
    let from = open_carrier(&mut arena, 1_u32.into());
    let to = open_carrier(&mut arena, 0_u32.into());

    let [zero, one, two, three, four] = [0_u32, 1, 2, 3, 4].map(DeBruijnIndex::from);
    let forward = written_map(&mut arena, one, zero);
    let other = written_map(&mut arena, one, two);
    // Past the forward map and the other: `other(to(x))` over `A`, and
    // `to(other(x))` over `B`.
    let section = written_trip(&mut arena, [three, four], [two, one]);
    let retraction = written_trip(&mut arena, [two, three], [one, two]);

    let left = arena.value_type_sigma(other, section);
    let right = arena.value_type_sigma(other, retraction);
    let inverses = arena.value_type_product(&[left, right]);
    let equivalence = arena.value_type_sigma(forward, inverses);
    let built = super::bi_invertible(&mut arena, from, to);
    assert_eq!(
        compared_types(&arena, built, equivalence),
        CertificateEquality::Equal,
        "A ≃ B is the map with a left and a right inverse"
    );

    let laws = arena.value_type_product(&[section, retraction]);
    let rest = arena.value_type_sigma(other, laws);
    let isomorphism = arena.value_type_sigma(forward, rest);
    let built = super::quasi_inverse(&mut arena, from, to);
    assert_eq!(
        compared_types(&arena, built, isomorphism),
        CertificateEquality::Equal,
        "A ≅ B is the map, the map back and both round trips"
    );

    // The section composed the other way round, or read over the unshifted
    // carrier, is another type.
    let swapped = written_trip(&mut arena, [three, four], [one, two]);
    let unshifted = written_trip(&mut arena, [one, one], [two, one]);
    for wrong in [swapped, unshifted] {
        let laws = arena.value_type_product(&[wrong, retraction]);
        let rest = arena.value_type_sigma(other, laws);
        let misread = arena.value_type_sigma(forward, rest);
        assert_eq!(
            compared_types(&arena, built, misread),
            CertificateEquality::Different
        );
    }
}

#[test]
fn univalence_carries_the_record_s_forward_map()
{
    // A record read from an outer variable: under the map's own binder it is
    // `#1`, and under the projection's binder the map is `#0` and the point
    // `#1`.
    let mut arena = CoreArena::new();
    let record = variable(&mut arena, 0_u32.into());
    let built = super::univalence_forward(&mut arena, record);

    let written = |arena: &mut CoreArena, record: u32, component: usize| {
        let lifted = variable(arena, record.into());
        let projected =
            arena.computation_tuple_projection(lifted, crate::Component::from(component));
        let map = variable(arena, 0_u32.into());
        let forced = arena.computation_force(map);
        let point = variable(arena, 1_u32.into());
        let applied = arena.computation_application(forced, point);
        let bound = arena.computation_bind(projected, applied);
        let lambda = arena.computation_lambda(bound);
        arena.value_thunk(lambda)
    };
    let expected = written(&mut arena, 1, 0);
    assert_eq!(
        equal_certificate_syntax(&arena, built, expected),
        CertificateEquality::Equal,
        "the map projects the record's first component and applies it to the point"
    );
    let unshifted = written(&mut arena, 0, 0);
    let inverses = written(&mut arena, 1, 1);
    for wrong in [unshifted, inverses] {
        assert_eq!(
            equal_certificate_syntax(&arena, built, wrong),
            CertificateEquality::Different
        );
    }
}
