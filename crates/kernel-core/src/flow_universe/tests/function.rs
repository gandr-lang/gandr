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
    select: FlowId,
    /// `Flow_U Bool Bool`, negation.
    not: FlowId,
    /// `Flow_U Bool Unit`, the terminal map.
    terminal: FlowId,
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

/// Build the function codes and their first-order boundary flows.
///
/// # Specification
/// - ensures: every boundary flow carries independently produced image
///   dialogues; formation is left to each witness.
/// - panics: on an invalid fixture claim or exhausted flow identifiers.
///
/// # Adequacy
/// - hypothesis: L3 — the boundary flows are ordinary forward certificates;
///   only the function introduction is new.
/// - witness: `flow_universe::tests::function::directed_funext_forms_and_rides_in_variance_order`
#[spec(ensures: |ret| flows.get(ret.select).is_ok() && flows.get(ret.not).is_ok() && flows.get(ret.terminal).is_ok())]
fn arrows(
    arena: &mut TermArena,
    flows: &mut Flows,
) -> Arrows
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
        image(arena, negation, left, right, right),
        image(arena, negation, right, left, left),
    ];
    let not = flows
        .push(Flow::Forward {
            source: base.boolean,
            target: base.boolean,
            translator: negation,
            images,
        })
        .expect("negation");
    let constant = returning(arena, left);
    let evidence = image(arena, constant, base.unit, left, left);
    let select = flows
        .push(Flow::Forward {
            source: base.unit_code,
            target: base.boolean,
            translator: constant,
            images: vec![evidence],
        })
        .expect("selection");
    let terminal = terminal(arena, flows, &base);
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
    let mut flows = Flows::new();
    let fixture = arrows(&mut arena, &mut flows);
    let [left, right] = fixture.base.constructors;

    // Flow_U (U (Bool → F Bool)) (U (Unit → F Bool)) from Flow_U Unit Bool at
    // the contravariant argument and Flow_U Bool Bool at the covariant result.
    let funext = flows
        .push(Flow::Function {
            source: fixture.endo,
            target: fixture.point,
            domain: fixture.select,
            codomain: fixture.not,
        })
        .expect("function flow");
    assert_eq!(
        form(&mut arena, &flows, funext, ReplayBudget::DEFAULT).expect("formation"),
        FlowType {
            source: fixture.endo_type,
            target: fixture.point_type,
        }
    );

    // The input checks at the source function code; a Bool does not.
    let term = Ride {
        certificate: Certificate::Flow(funext),
        value: fixture.identity,
    };
    elaborate(&mut arena, &flows, term, ReplayBudget::DEFAULT).expect("a function input");
    let misplaced = Ride {
        value: left,
        ..term
    };
    assert!(matches!(
        elaborate(&mut arena, &flows, misplaced, ReplayBudget::DEFAULT),
        Err(FlowError::Typing(_))
    ));
    assert!(matches!(
        beta(&mut arena, &flows, term, ReplayBudget::DEFAULT).expect("beta"),
        Reduct::Compute(_)
    ));

    // `select` runs before the function and `not` after it: identity lands on
    // `not false`, negation on `not (not false)`.
    let to_true = returning(&mut arena, right);
    let to_false = returning(&mut arena, left);
    computes(&mut arena, &flows, funext, fixture.identity, to_true);
    computes(&mut arena, &flows, funext, fixture.negation, to_false);

    // Over Bool at both ends, a constant-false argument boundary and a
    // negating result boundary separate the two orders: applied as the arrow
    // fixes them, identity becomes constant true; swapped, constant false.
    let constant = flows
        .push(Flow::Compose {
            first: fixture.terminal,
            second: fixture.select,
            seam: Seam::Sequence,
        })
        .expect("constant false");
    let ordered = flows
        .push(Flow::Function {
            source: fixture.endo,
            target: fixture.endo,
            domain: constant,
            codomain: fixture.not,
        })
        .expect("endomorphism flow");
    computes(&mut arena, &flows, ordered, fixture.identity, to_true);

    // Sequential composition at function codes is the existing seam.
    let composite = flows
        .push(Flow::Compose {
            first: ordered,
            second: funext,
            seam: Seam::Sequence,
        })
        .expect("sequence of function flows");
    assert_eq!(
        form(&mut arena, &flows, composite, ReplayBudget::DEFAULT).expect("composite"),
        FlowType {
            source: fixture.endo_type,
            target: fixture.point_type,
        }
    );
    computes(&mut arena, &flows, composite, fixture.identity, to_false);
}

#[test]
fn stay_at_a_thunk_code_collapses()
{
    let mut arena = TermArena::new();
    let mut flows = Flows::new();
    let fixture = arrows(&mut arena, &mut flows);
    let stay = flows.push(Flow::Stay(fixture.endo)).expect("stay");
    assert_eq!(
        form(&mut arena, &flows, stay, ReplayBudget::DEFAULT).expect("stay formation"),
        FlowType {
            source: fixture.endo_type,
            target: fixture.endo_type,
        }
    );
    for function in [fixture.identity, fixture.negation] {
        let term = Ride {
            certificate: Certificate::Flow(stay),
            value: function,
        };
        elaborate(&mut arena, &flows, term, ReplayBudget::DEFAULT).expect("stay elaboration");
        let watermark = arena.watermark();
        assert_eq!(
            beta(&mut arena, &flows, term, ReplayBudget::from(0_u64)).expect("one step"),
            Reduct::Return(function)
        );
        assert_eq!(arena.watermark(), watermark);
        computes(&mut arena, &flows, stay, function, function);
    }

    // The arrow of two stays is the identity on functions, by replay.
    let argument = flows
        .push(Flow::Stay(fixture.base.boolean))
        .expect("argument stay");
    let result = flows
        .push(Flow::Stay(fixture.base.boolean))
        .expect("result stay");
    let identity = flows
        .push(Flow::Function {
            source: fixture.endo,
            target: fixture.endo,
            domain: argument,
            codomain: result,
        })
        .expect("arrow of stays");
    computes(
        &mut arena,
        &flows,
        identity,
        fixture.negation,
        fixture.negation,
    );
}

#[test]
fn symmetry_refusal_holds_at_a_thunk_code()
{
    let mut arena = TermArena::new();
    let mut flows = Flows::new();
    let fixture = arrows(&mut arena, &mut flows);
    assert_eq!(Boundary::Domain.variance(), Variance::Contravariant);
    assert_eq!(Boundary::Codomain.variance(), Variance::Covariant);
    let result = flows
        .push(Flow::Stay(fixture.base.boolean))
        .expect("result stay");

    // The terminal map runs from the source's argument to the target's: the
    // non-forward direction for a contravariant boundary.
    let backward = flows
        .push(Flow::Function {
            source: fixture.endo,
            target: fixture.point,
            domain: fixture.terminal,
            codomain: result,
        })
        .expect("covariant argument");
    assert!(matches!(
        form(&mut arena, &flows, backward, ReplayBudget::DEFAULT),
        Err(FlowError::Boundary(Boundary::Domain))
    ));

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
    let unit_stay = flows
        .push(Flow::Stay(fixture.base.unit_code))
        .expect("unit stay");
    let boolean_stay = flows
        .push(Flow::Stay(fixture.base.boolean))
        .expect("boolean stay");
    for (domain, codomain, refused) in [
        (fixture.select, fixture.select, None),
        (fixture.terminal, fixture.select, Some(Boundary::Domain)),
        (fixture.select, fixture.terminal, Some(Boundary::Codomain)),
    ] {
        let flow = flows
            .push(Flow::Function {
                source: narrow,
                target: wide,
                domain,
                codomain,
            })
            .expect("boundary pair");
        let formed = form(&mut arena, &flows, flow, ReplayBudget::DEFAULT);
        match (refused, formed) {
            | (None, Ok(_)) => {},
            | (Some(expected), Err(FlowError::Boundary(found))) if found == expected => {},
            | (_, other) => panic!("unexpected boundary verdict: {other:?}"),
        }
    }
    let reversed = flows
        .push(Flow::Function {
            source: fixture.endo,
            target: narrow,
            domain: boolean_stay,
            codomain: fixture.select,
        })
        .expect("contravariant result");
    assert!(matches!(
        form(&mut arena, &flows, reversed, ReplayBudget::DEFAULT),
        Err(FlowError::Boundary(Boundary::Codomain))
    ));
    let mixed = flows
        .push(Flow::Function {
            source: narrow,
            target: narrow,
            domain: boolean_stay,
            codomain: unit_stay,
        })
        .expect("stays at both boundaries");
    form(&mut arena, &flows, mixed, ReplayBudget::DEFAULT).expect("identity of U (Bool → F Unit)");

    // Riding a flow through a function's argument is the symmetry motive in
    // disguise: the moving endpoint sits in the arrow's domain.
    let mut motives = Motives::new();
    let fixed = motives.push(Motive::El(Endpoint::Fixed)).expect("fixed");
    let moving = motives.push(Motive::El(Endpoint::Moving)).expect("moving");
    let argument = motives
        .push(Motive::Arrow(moving, fixed))
        .expect("argument transport");
    let outcome = motives
        .push(Motive::Arrow(fixed, moving))
        .expect("result transport");
    let symmetry = motives
        .push(Motive::Flow(Endpoint::Moving, Endpoint::Fixed))
        .expect("symmetry");
    assert!(matches!(
        check_motive(&motives, argument, ReplayBudget::DEFAULT),
        Err(FlowError::NonCovariantMotive(found)) if found == moving
    ));
    assert!(matches!(
        check_motive(&motives, symmetry, ReplayBudget::DEFAULT),
        Err(FlowError::NonCovariantMotive(found)) if found == symmetry
    ));
    check_motive(&motives, outcome, ReplayBudget::DEFAULT).expect("covariant result");

    // There and back again is an endomorphism, never an inverse, and closing
    // the loop is a cycle.
    let forth = flows
        .push(Flow::Function {
            source: fixture.endo,
            target: fixture.point,
            domain: fixture.select,
            codomain: result,
        })
        .expect("forth");
    let back = flows
        .push(Flow::Function {
            source: fixture.point,
            target: fixture.endo,
            domain: fixture.terminal,
            codomain: result,
        })
        .expect("back");
    let round = flows
        .push(Flow::Compose {
            first: forth,
            second: back,
            seam: Seam::Sequence,
        })
        .expect("round trip");
    let [left, _] = fixture.base.constructors;
    let to_false = returning(&mut arena, left);
    computes(&mut arena, &flows, round, fixture.identity, to_false);
    let feedback = flows
        .push(Flow::Compose {
            first: forth,
            second: back,
            seam: Seam::Feedback,
        })
        .expect("feedback");
    assert!(matches!(
        form(&mut arena, &flows, feedback, ReplayBudget::DEFAULT),
        Err(FlowError::Cycle { first, second }) if first == forth && second == back
    ));
}

#[test]
fn constant_map_refusal_holds_at_a_thunk_code()
{
    let mut arena = TermArena::new();
    let mut flows = Flows::new();
    let string = arena.value_type_base(BaseType::String);
    let code = arena.value_quote(string);
    let (function_code, function_type) = arrow(&mut arena, string, string);
    let sample = arena.value_literal(Literal::Text(StringLiteral::new("constant".into())));
    let constant = returning(&mut arena, sample);
    let evidence = image(&mut arena, constant, sample, sample, sample);
    let manufactured = flows
        .push(Flow::Forward {
            source: code,
            target: code,
            translator: constant,
            images: vec![evidence],
        })
        .expect("raw constant");
    let stay = flows.push(Flow::Stay(code)).expect("argument stay");

    // A literal cannot enter through the result boundary.
    let through = flows
        .push(Flow::Function {
            source: function_code,
            target: function_code,
            domain: stay,
            codomain: manufactured,
        })
        .expect("constant result");
    assert!(matches!(
        form(&mut arena, &flows, through, ReplayBudget::DEFAULT),
        Err(FlowError::NonNatural(found)) if found == sample
    ));

    // Nor as a forward translator at a function code: the leaf-natural stock
    // covers constructor patterns, and a function has none.
    let thunk = returning(&mut arena, sample);
    let constant_function = arena.computation_return(thunk);
    let lambda = arena.computation_lambda(constant_function);
    let translator = arena.value_thunk(lambda);
    for (source, target) in [(function_code, function_code), (code, function_code)] {
        let forward = flows
            .push(Flow::Forward {
                source,
                target,
                translator,
                images: Vec::new(),
            })
            .expect("forward at a function code");
        assert!(matches!(
            form(&mut arena, &flows, forward, ReplayBudget::DEFAULT),
            Err(FlowError::UnsupportedType(found)) if found == function_type
        ));
    }

    // A function introduction's endpoints are function codes over first-order
    // codes only.
    let first_order = flows
        .push(Flow::Function {
            source: code,
            target: function_code,
            domain: stay,
            codomain: stay,
        })
        .expect("first-order endpoint");
    assert!(matches!(
        form(&mut arena, &flows, first_order, ReplayBudget::DEFAULT),
        Err(FlowError::UnsupportedType(found)) if found == string
    ));
    let (higher, _) = arrow(&mut arena, function_type, string);
    let higher_order = flows
        .push(Flow::Function {
            source: higher,
            target: higher,
            domain: stay,
            codomain: stay,
        })
        .expect("higher-order argument");
    assert!(matches!(
        form(&mut arena, &flows, higher_order, ReplayBudget::DEFAULT),
        Err(FlowError::UnsupportedType(found)) if found == function_type
    ));
}
