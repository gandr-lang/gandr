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

/// Which endpoint of a path type a check reads.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
enum Endpoint
{
    /// The left endpoint.
    Left,
    /// The right endpoint.
    Right,
}

/// Assert that `value`, the endpoint `side`, is `⟨force function argument⟩`.
///
/// # Specification
/// trivial.
fn assert_applied_at(
    arena: &CoreArena,
    value: ValueId,
    (function, argument): (ValueId, ValueId),
    side: Endpoint,
)
{
    use crate::syntax::Computation;
    use crate::syntax::Value;
    assert!(
        matches!(arena.value(value), Some(&Value::Returned(run))
            if matches!(arena.computation(run), Some(&Computation::Application(forced, applied))
                if applied == argument
                    && arena.computation(forced) == Some(&Computation::Force(function)))),
        "the {side:?} endpoint is the map applied at the level's endpoint"
    );
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
fn a_whisker_moves_one_half_of_a_composite()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let [start, end, first, second, path] =
        [0_u32, 1, 2, 3, 4].map(|index| variable(&mut arena, index.into()));
    let built = super::whisker(
        &mut arena,
        (integer, start, end),
        (first, second),
        super::Whisker::Right,
        path,
    );

    let image = super::then(&mut arena, integer, start, first, second);
    let image = arena.value_returned(image);
    let [lifted_start, lifted_end, lifted_first, lifted_second] =
        [1_u32, 2, 3, 4].map(|index| variable(&mut arena, index.into()));
    let moving = variable(&mut arena, 0_u32.into());
    let lifted_codomain = arena.value_type_path(integer, lifted_start, lifted_end);
    let lifted_image = super::then(
        &mut arena,
        integer,
        lifted_start,
        lifted_first,
        lifted_second,
    );
    let lifted_image = arena.value_returned(lifted_image);
    let mut expected = |left, right| {
        let moved = super::then(&mut arena, integer, lifted_start, left, right);
        let moved = arena.value_returned(moved);
        let motive = arena.value_type_path(lifted_codomain, lifted_image, moved);
        let base = arena.value_here(image);
        let transported = arena.computation_path_transport(motive, path, base);
        let returned = arena.value_returned(transported);
        arena.computation_return(returned)
    };
    let right = expected(moving, lifted_second);
    let left = expected(lifted_first, moving);
    let built = arena.computation_return(built);
    assert_eq!(
        compared(&arena, built, right),
        CertificateEquality::Equal,
        "the right whisker moves the first half under the motive's binder"
    );
    assert_eq!(
        compared(&arena, built, left),
        CertificateEquality::Different,
        "moving the second half is the left whisker, another term"
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
fn cong_above_a_level_transports_along_the_point()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let function = variable(&mut arena, 0_u32.into());
    let from = variable(&mut arena, 1_u32.into());
    let point = variable(&mut arena, 2_u32.into());
    let level = (from, from);
    let built = super::cong_above(&mut arena, (function, integer), &[level], point)
        .expect("one level builds");
    let carrier = super::cong_codomain(&mut arena, (function, integer), &[level])
        .expect("one level has a type");

    // The start is the map at the level's left endpoint; under the motive's
    // binder the map and the start are read one binder further out.
    let forced = arena.computation_force(function);
    let start = arena.computation_application(forced, from);
    let start = arena.value_returned(start);
    let lifted_function = variable(&mut arena, 1_u32.into());
    let lifted_forced = arena.computation_force(lifted_function);
    let lifted_from = variable(&mut arena, 2_u32.into());
    let lifted_start = arena.computation_application(lifted_forced, lifted_from);
    let lifted_start = arena.value_returned(lifted_start);
    let moving = variable(&mut arena, 0_u32.into());
    let image = arena.computation_application(lifted_forced, moving);
    let image = arena.value_returned(image);
    let motive = arena.value_type_path(integer, lifted_start, image);
    let base = arena.value_here(start);
    let expected = arena.computation_path_transport(motive, point, base);
    assert_eq!(
        compared(&arena, built, expected),
        CertificateEquality::Equal,
        "one level is cong of the map along the point"
    );
    let Some(&crate::syntax::ValueType::Path {
        carrier: below,
        left,
        right,
    }) = arena.value_type(carrier)
    else {
        panic!("one level maps into a path type");
    };
    assert_eq!(below, integer, "the paths lie in the codomain");
    assert_applied_at(&arena, left, (function, from), Endpoint::Left);
    assert_applied_at(&arena, right, (function, from), Endpoint::Right);

    let applied =
        super::cong_above(&mut arena, (function, integer), &[], point).expect("no level builds");
    let direct = arena.computation_application(forced, point);
    assert_eq!(
        compared(&arena, applied, direct),
        CertificateEquality::Equal,
        "no level is the map applied"
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
        gandr_kernel_term::ConstantIndex::from(0_usize),
        sort,
        gandr_kernel_term::ConstructorTag::from(0_usize),
        alloc::vec::Vec::new(),
    );
    let field = arena.value_unit();
    let fielded = arena.value_constructor(
        gandr_kernel_term::ConstantIndex::from(0_usize),
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

/// The written round trip `+U ((x : El #domain) => -F Path[.A = El #over](
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

/// #6530: the cell `ua` reads at dimension two is a homotopy of the identity,
/// a map from each point to a path from that point to itself.
#[test]
fn a_homotopy_of_the_identity_returns_a_path_from_the_point_to_itself_6530()
{
    // Over `El(#0)`: under the map's binder the carrier is `El(#1)` and the
    // point is `#0`.
    let mut arena = CoreArena::new();
    let carrier = open_carrier(&mut arena, 0_u32.into());
    let built = super::self_homotopy(&mut arena, carrier);

    let written = |arena: &mut CoreArena, over: u32, (left, right): (u32, u32)| {
        let shifted = open_carrier(arena, over.into());
        let from = variable(arena, left.into());
        let to = variable(arena, right.into());
        let path = arena.value_type_path(shifted, from, to);
        let returned = arena.comp_type_returner(path);
        let dependent = arena.comp_type_pi(carrier, returned);
        arena.value_type_thunk(dependent)
    };
    let expected = written(&mut arena, 1, (0, 0));
    assert_eq!(
        compared_types(&arena, built, expected),
        CertificateEquality::Equal,
        "the map returns a path over the shifted carrier from the point to itself"
    );
    let unshifted = written(&mut arena, 0, (0, 0));
    let outer = written(&mut arena, 1, (0, 1));
    for wrong in [unshifted, outer] {
        assert_eq!(
            compared_types(&arena, built, wrong),
            CertificateEquality::Different
        );
    }
}
