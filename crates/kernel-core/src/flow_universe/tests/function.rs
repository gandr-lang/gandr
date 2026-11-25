//! Directed funext at a function code: the arrow's action on `Flow_U`.

use super::*;

/// Function codes over Bool and Unit, with the boundary flows between them.
struct Arrows
{
    /// The terminal-map fixture.
    base: Fixture,
    /// `U (Bool → F Bool)`, quoted.
    endo: ValueId,
    /// `U (Bool → F Bool)`.
    endo_type: ValueTypeId,
    /// `U (Unit → F Bool)`, quoted.
    point: ValueId,
    /// `U (Unit → F Bool)`.
    point_type: ValueTypeId,
    /// Closed Bool identity.
    identity: ValueId,
    /// Closed Bool negation.
    negation: ValueId,
    /// `Flow_U Unit Bool`, selecting `inl ()`.
    select: ValueId,
    /// `Flow_U Bool Bool`, negation.
    not: ValueId,
    /// `Flow_U Bool Unit`, the terminal map.
    terminal: ValueId,
}

/// Quote the function code `U (domain → F codomain)`.
///
/// # Specification
/// trivial.
fn arrow(
    arena: &mut TermArena,
    domain: ValueTypeId,
    codomain: ValueTypeId,
) -> (ValueId, ValueTypeId)
{
    let returner = arena.comp_type_returner(codomain);
    let body = arena.comp_type_arrow(domain, returner);
    let thunk = arena.value_type_thunk(body);
    (arena.value_quote(thunk), thunk)
}

/// Mint a function flow between two function codes over its boundaries.
///
/// # Specification
/// trivial.
fn function(
    arena: &mut TermArena,
    (source, target): (ValueId, ValueId),
    (domain, codomain): (ValueId, ValueId),
) -> ValueId
{
    let classifier = arena.value_type_flow_universe(source, target);
    arena.value_function_flow(classifier, domain, codomain)
}

/// Build the function codes and their first-order boundary flows.
///
/// # Specification
/// - ensures: every boundary flow carries independently produced image
///   dialogues; admission is left to each witness.
/// - panics: on an invalid fixture claim.
///
/// # Adequacy
/// - hypothesis: L3 — the boundary flows are ordinary forward certificates;
///   only the function introduction is new.
/// - witness: `flow_universe::tests::function::directed_funext_forms_and_rides_in_variance_order`
#[spec(ensures: |ret| [ret.select, ret.not, ret.terminal].iter().all(|&flow| matches!(arena.value(flow), Some(&gandr_kernel_term::Value::ForwardFlow { .. }))))]
fn arrows(arena: &mut TermArena) -> Arrows
{
    let base = fixture(arena);
    let (endo, endo_type) = arrow(arena, base.boolean_type, base.boolean_type);
    let (point, point_type) = arrow(arena, base.unit_type, base.boolean_type);
    let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
    let identity = returning(arena, variable);
    let [left, right] = base.constructors;
    let to_right = arena.computation_return(right);
    let to_left = arena.computation_return(left);
    let case = arena.computation_case(variable, &[to_right, to_left]);
    let lambda = arena.computation_lambda(case);
    let negation = arena.value_thunk(lambda);
    let images = vec![
        image(
            arena,
            negation,
            (left, right),
            right,
            BinderDepth::from(0_u32),
        ),
        image(
            arena,
            negation,
            (right, left),
            left,
            BinderDepth::from(0_u32),
        ),
    ];
    let not = forward(arena, (base.boolean, base.boolean), negation, images);
    let constant = returning(arena, left);
    let evidence = image(
        arena,
        constant,
        (base.unit, left),
        left,
        BinderDepth::from(0_u32),
    );
    let select = forward(arena, (base.unit_code, base.boolean), constant, vec![
        evidence,
    ]);
    let terminal = terminal(arena, &base);
    Arrows {
        base,
        endo,
        endo_type,
        point,
        point_type,
        identity,
        negation,
        select,
        not,
        terminal,
    }
}

#[test]
fn directed_funext_forms_and_rides_in_variance_order()
{
    let mut arena = TermArena::new();
    let fixture = arrows(&mut arena);
    let [left, right] = fixture.base.constructors;

    // Flow_U (U (Bool → F Bool)) (U (Unit → F Bool)) from Flow_U Unit Bool at
    // the contravariant argument and Flow_U Bool Bool at the covariant result.
    let funext = function(
        &mut arena,
        (fixture.endo, fixture.point),
        (fixture.select, fixture.not),
    );
    assert_eq!(
        form_certificate(&mut arena, funext, Family::Flow, ReplayBudget::DEFAULT),
        Ok(CertificateType::Flow(FlowType {
            source: fixture.endo_type,
            target: fixture.point_type,
        }))
    );

    // The input checks at the source function code; a Bool does not.
    let misplaced = ride(&mut arena, funext, left);
    let expected = arena.computation_return(left);
    assert!(matches!(
        replay_ride(
            &mut arena,
            misplaced,
            expected,
            EngineClaim::Convertible,
            &Dialogue::default(),
            ReplayBudget::DEFAULT
        ),
        Err(error) if !matches!(error, KernelError::Flow(_))
    ));

    // `select` runs before the function and `not` after it: identity lands on
    // `not false`, negation on `not (not false)`.
    let to_true = returning(&mut arena, right);
    let to_false = returning(&mut arena, left);
    computes(&mut arena, funext, fixture.identity, to_true);
    computes(&mut arena, funext, fixture.negation, to_false);

    // Over Bool at both ends, a constant-false argument boundary and a
    // negating result boundary separate the two orders: applied as the arrow
    // fixes them, identity becomes constant true; swapped, constant false.
    let constant = arena.value_then(
        fixture.terminal,
        fixture.select,
        gandr_kernel_term::Seam::Sequence,
    );
    let ordered = function(
        &mut arena,
        (fixture.endo, fixture.endo),
        (constant, fixture.not),
    );
    computes(&mut arena, ordered, fixture.identity, to_true);

    // Sequential composition at function codes is the same seam.
    let composite = arena.value_then(ordered, funext, gandr_kernel_term::Seam::Sequence);
    assert_eq!(
        form_certificate(&mut arena, composite, Family::Flow, ReplayBudget::DEFAULT),
        Ok(CertificateType::Flow(FlowType {
            source: fixture.endo_type,
            target: fixture.point_type,
        }))
    );
    computes(&mut arena, composite, fixture.identity, to_false);
}

#[test]
fn stay_at_a_thunk_code_collapses()
{
    let mut arena = TermArena::new();
    let fixture = arrows(&mut arena);
    let stay = arena.value_stay(fixture.endo);
    assert_eq!(
        form_certificate(&mut arena, stay, Family::Flow, ReplayBudget::DEFAULT),
        Ok(CertificateType::Flow(FlowType {
            source: fixture.endo_type,
            target: fixture.endo_type,
        }))
    );
    for function in [fixture.identity, fixture.negation] {
        computes(&mut arena, stay, function, function);
    }

    // The arrow of two stays is the identity on functions, by replay.
    let argument = arena.value_stay(fixture.base.boolean);
    let result = arena.value_stay(fixture.base.boolean);
    let identity = function(&mut arena, (fixture.endo, fixture.endo), (argument, result));
    computes(&mut arena, identity, fixture.negation, fixture.negation);
}

#[test]
fn symmetry_refusal_holds_at_a_thunk_code()
{
    let mut arena = TermArena::new();
    let fixture = arrows(&mut arena);
    assert_eq!(Boundary::Domain.variance(), Variance::Contravariant);
    assert_eq!(Boundary::Codomain.variance(), Variance::Covariant);
    let result = arena.value_stay(fixture.base.boolean);

    // The terminal map runs from the source's argument to the target's: the
    // non-forward direction for a contravariant boundary.
    let backward = function(
        &mut arena,
        (fixture.endo, fixture.point),
        (fixture.terminal, result),
    );
    assert_eq!(
        admit(&mut arena, backward),
        Err(KernelError::Flow(FlowError::Boundary(Boundary::Domain)))
    );

    // One certificate, two boundaries: `select` is the argument boundary from
    // `U (Bool → F Unit)` to `U (Unit → F Bool)` and the result boundary
    // between the same codes reversed in their results only.
    let (narrow, _) = arrow(
        &mut arena,
        fixture.base.boolean_type,
        fixture.base.unit_type,
    );
    let (wide, _) = arrow(
        &mut arena,
        fixture.base.unit_type,
        fixture.base.boolean_type,
    );
    let unit_stay = arena.value_stay(fixture.base.unit_code);
    let boolean_stay = arena.value_stay(fixture.base.boolean);
    for (domain, codomain, refused) in [
        (fixture.select, fixture.select, None),
        (fixture.terminal, fixture.select, Some(Boundary::Domain)),
        (fixture.select, fixture.terminal, Some(Boundary::Codomain)),
    ] {
        let flow = function(&mut arena, (narrow, wide), (domain, codomain));
        match (refused, admit(&mut arena, flow)) {
            (None, Ok(_)) => {},
            (Some(expected), Err(KernelError::Flow(FlowError::Boundary(found))))
                if found == expected => {},
            (_, other) => panic!("unexpected boundary verdict: {other:?}"),
        }
    }
    let reversed = function(
        &mut arena,
        (fixture.endo, narrow),
        (boolean_stay, fixture.select),
    );
    assert_eq!(
        admit(&mut arena, reversed),
        Err(KernelError::Flow(FlowError::Boundary(Boundary::Codomain)))
    );
    let mixed = function(&mut arena, (narrow, narrow), (boolean_stay, unit_stay));
    admit(&mut arena, mixed).expect("identity of U (Bool → F Unit)");

    // Riding a flow through a function's argument is the symmetry motive in
    // disguise: the moving endpoint sits in the arrow's domain.
    let zero = DeBruijnIndex::from(0_u32);
    let moving = element(&mut arena);
    let fixed = fixture.base.boolean_type;
    let fixed_returner = arena.comp_type_returner(fixed);
    let moving_returner = arena.comp_type_returner(moving);
    let argument = arena.comp_type_arrow(moving, fixed_returner);
    let argument = arena.value_type_thunk(argument);
    let outcome = arena.comp_type_arrow(fixed, moving_returner);
    let outcome = arena.value_type_thunk(outcome);
    assert_eq!(
        check_motive(&mut arena, argument, zero, ReplayBudget::DEFAULT),
        Err(FlowError::NonCovariantMotive(
            gandr_kernel_term::AnyNode::ValueType(moving)
        ))
    );
    check_motive(&mut arena, outcome, zero, ReplayBudget::DEFAULT).expect("covariant result");

    // There and back again is an endomorphism, never an inverse, and closing
    // the loop is a cycle.
    let forth = function(
        &mut arena,
        (fixture.endo, fixture.point),
        (fixture.select, result),
    );
    let back = function(
        &mut arena,
        (fixture.point, fixture.endo),
        (fixture.terminal, result),
    );
    let round = arena.value_then(forth, back, gandr_kernel_term::Seam::Sequence);
    let [left, _] = fixture.base.constructors;
    let to_false = returning(&mut arena, left);
    computes(&mut arena, round, fixture.identity, to_false);
    let feedback = arena.value_then(forth, back, gandr_kernel_term::Seam::Feedback);
    assert_eq!(
        admit(&mut arena, feedback),
        Err(KernelError::Flow(FlowError::Cycle {
            first: forth,
            second: back
        }))
    );
}

#[test]
fn constant_map_refusal_holds_at_a_thunk_code()
{
    let mut arena = TermArena::new();
    let string = arena.value_type_base(BaseType::String);
    let code = arena.value_quote(string);
    let (function_code, function_type) = arrow(&mut arena, string, string);
    let sample = arena.value_literal(Literal::Text(StringLiteral::new("constant".into())));
    let constant = returning(&mut arena, sample);
    let evidence = image(
        &mut arena,
        constant,
        (sample, sample),
        sample,
        BinderDepth::from(1_u32),
    );
    let manufactured = forward(&mut arena, (code, code), constant, vec![evidence]);
    let stay = arena.value_stay(code);

    // A literal cannot enter through the result boundary.
    let through = function(
        &mut arena,
        (function_code, function_code),
        (stay, manufactured),
    );
    assert_eq!(
        admit(&mut arena, through),
        Err(KernelError::Flow(FlowError::NonNatural(sample)))
    );

    // Nor as a forward translator at a function code: the leaf-natural stock
    // covers constructor patterns, and a function has none.
    let thunk = returning(&mut arena, sample);
    let constant_function = arena.computation_return(thunk);
    let lambda = arena.computation_lambda(constant_function);
    let translator = arena.value_thunk(lambda);
    for (source, target) in [(function_code, function_code), (code, function_code)] {
        let flow = forward(&mut arena, (source, target), translator, Vec::new());
        assert_eq!(
            admit(&mut arena, flow),
            Err(KernelError::Flow(FlowError::UnsupportedType(function_type)))
        );
    }

    // A function introduction's endpoints are function codes over first-order
    // codes only.
    let first_order = function(&mut arena, (code, function_code), (stay, stay));
    assert_eq!(
        admit(&mut arena, first_order),
        Err(KernelError::Flow(FlowError::UnsupportedType(string)))
    );
    let (higher, _) = arrow(&mut arena, function_type, string);
    let higher_order = function(&mut arena, (higher, higher), (stay, stay));
    assert_eq!(
        admit(&mut arena, higher_order),
        Err(KernelError::Flow(FlowError::UnsupportedType(function_type)))
    );
}
