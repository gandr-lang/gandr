//! Directed computation, naturality, variance and family-boundary witnesses.

use alloc::vec;
use alloc::vec::Vec;

use gandr_kernel_term::BaseType;
use gandr_kernel_term::ComputationId;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Side;
use gandr_kernel_term::StringLiteral;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueTypeId;

use super::*;
use crate::path_universe::Path;
use crate::path_universe::Paths;
use crate::path_universe::RoundTrips;
use crate::replay::EngineClaim;
use crate::replay::ReplayBudget;

mod engine;
use engine::engine;

/// Bool, Unit and their canonical closed values.
struct Fixture
{
    /// Bool's quoted code.
    boolean: ValueId,
    /// Unit's quoted code.
    unit_code: ValueId,
    /// Bool's type.
    boolean_type: ValueTypeId,
    /// Unit's type.
    unit_type: ValueTypeId,
    /// Unit value.
    unit: ValueId,
    /// Both Bool constructors, in source-pattern order.
    constructors: [ValueId; 2],
    /// Closed terminal translator.
    terminal: ValueId,
}

/// Build the terminal-map fixture without host-language translators.
///
/// # Specification
/// trivial.
fn fixture(arena: &mut TermArena) -> Fixture
{
    let unit_type = arena.value_type_unit();
    let boolean_type = arena.value_type_sum(unit_type, unit_type);
    let boolean = arena.value_quote(boolean_type);
    let unit_code = arena.value_quote(unit_type);
    let unit = arena.value_unit();
    let constructors = [
        arena.value_injection(Side::Left, unit),
        arena.value_injection(Side::Right, unit),
    ];
    let terminal = returning(arena, unit);
    Fixture {
        boolean,
        unit_code,
        boolean_type,
        unit_type,
        unit,
        constructors,
        terminal,
    }
}

/// Make a closed thunk of a lambda returning the supplied binder-relative
/// value.
///
/// # Specification
/// trivial.
fn returning(
    arena: &mut TermArena,
    output: ValueId,
) -> ValueId
{
    let body = arena.computation_return(output);
    let lambda = arena.computation_lambda(body);
    arena.value_thunk(lambda)
}

/// Apply a translator syntactically, without reduction.
///
/// # Specification
/// trivial.
fn apply(
    arena: &mut TermArena,
    function: ValueId,
    value: ValueId,
) -> ComputationId
{
    let force = arena.computation_force(function);
    arena.computation_application(force, value)
}

/// Produce an image dialogue from an independent closed engine computation.
///
/// # Specification
/// - ensures: the retained dialogue comes from the engine on the sample;
///   formation must independently validate the symbolic output and replay it.
/// - panics: if the fixture's proposed sample output is not convertible.
///
/// # Adequacy
/// - hypothesis: L3 — a sample trace for a constant cannot certify a Base map.
/// - witness: `flow_universe::tests::constant_leaf_and_forged_evidence_refuse`
fn image(
    arena: &mut TermArena,
    function: ValueId,
    input: ValueId,
    sample_output: ValueId,
    output: ValueId,
) -> Image
{
    let action = apply(arena, function, input);
    let expected = arena.computation_return(sample_output);
    let (claim, dialogue) = engine(arena, action, expected);
    assert_eq!(claim, EngineClaim::Convertible);
    Image { output, dialogue }
}

/// Insert a terminal map with both source-constructor dialogues.
///
/// # Specification
/// trivial.
fn terminal(
    arena: &mut TermArena,
    flows: &mut Flows,
    fixture: &Fixture,
) -> FlowId
{
    let images = fixture
        .constructors
        .into_iter()
        .map(|input| image(arena, fixture.terminal, input, fixture.unit, fixture.unit))
        .collect();
    flows
        .push(Flow::Forward {
            source: fixture.boolean,
            target: fixture.unit_code,
            translator: fixture.terminal,
            images,
        })
        .expect("terminal syntax")
}

/// Compare a lowered ride with an independently specified output and replay it.
///
/// # Specification
/// - ensures: both the engine and kernel certify the explicit expected value.
/// - panics: on any failed elaboration, reduction or replay assertion.
///
/// # Adequacy
/// - hypothesis: L2/L3 — golden outputs distinguish forward maps and order; the
///   independent engine supplies decisions, never a kernel verdict.
/// - witness: `flow_universe::tests::composition_preserves_direction_and_refuses_feedback`
fn computes(
    arena: &mut TermArena,
    flows: &Flows,
    id: FlowId,
    input: ValueId,
    output: ValueId,
)
{
    let term = Ride {
        certificate: Certificate::Flow(id),
        value: input,
    };
    assert_eq!(
        elaborate(arena, flows, term, ReplayBudget::DEFAULT).expect("elaboration"),
        term
    );
    let action = match beta(arena, flows, term, ReplayBudget::DEFAULT).expect("beta") {
        | Reduct::Return(value) => arena.computation_return(value),
        | Reduct::Compute(computation) => computation,
    };
    let expected = arena.computation_return(output);
    let (claim, dialogue) = engine(arena, action, expected);
    assert_eq!(claim, EngineClaim::Convertible);
    let watermark = arena.watermark();
    assert_eq!(
        replay_ride(
            arena,
            flows,
            term,
            expected,
            claim,
            &dialogue,
            ReplayBudget::DEFAULT
        )
        .expect("ride replay"),
        KernelVerdict::Convertible
    );
    assert_eq!(arena.watermark(), watermark);
}

#[test]
fn terminal_ride_and_stay_compute()
{
    let mut arena = TermArena::new();
    let fixture = fixture(&mut arena);
    let mut flows = Flows::new();
    let terminal = terminal(&mut arena, &mut flows, &fixture);
    assert_eq!(
        form(&mut arena, &flows, terminal, ReplayBudget::DEFAULT).expect("formation"),
        FlowType {
            source: fixture.boolean_type,
            target: fixture.unit_type
        }
    );
    let stay = flows.push(Flow::Stay(fixture.boolean)).expect("stay");
    for input in fixture.constructors {
        computes(&mut arena, &flows, terminal, input, fixture.unit);
        let term = Ride {
            certificate: Certificate::Flow(stay),
            value: input,
        };
        elaborate(&mut arena, &flows, term, ReplayBudget::DEFAULT).expect("stay formation");
        let watermark = arena.watermark();
        assert_eq!(
            beta(&mut arena, &flows, term, ReplayBudget::from(0_u64)).expect("one step"),
            Reduct::Return(input)
        );
        assert_eq!(arena.watermark(), watermark);
        computes(&mut arena, &flows, stay, input, input);
    }
}

#[test]
fn one_way_classes_preserve_leaves()
{
    let mut arena = TermArena::new();
    let mut flows = Flows::new();
    let base = arena.value_type_base(BaseType::String);
    let code = arena.value_quote(base);
    let sample = arena.value_literal(Literal::Text(StringLiteral::new("leaf".into())));
    let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
    let product = arena.value_type_product(base, base);
    let product_code = arena.value_quote(product);
    let pair = arena.value_pair(variable, variable);
    let diagonal = returning(&mut arena, pair);
    let sample_pair = arena.value_pair(sample, sample);
    let evidence = image(&mut arena, diagonal, sample, sample_pair, pair);
    let diagonal = flows
        .push(Flow::Forward {
            source: code,
            target: product_code,
            translator: diagonal,
            images: vec![evidence],
        })
        .expect("diagonal");
    computes(&mut arena, &flows, diagonal, sample, sample_pair);

    let sum = arena.value_type_sum(base, base);
    let sum_code = arena.value_quote(sum);
    for side in [Side::Left, Side::Right] {
        let injection = arena.value_injection(side, variable);
        let function = returning(&mut arena, injection);
        let output = arena.value_injection(side, sample);
        let evidence = image(&mut arena, function, sample, output, injection);
        let id = flows
            .push(Flow::Forward {
                source: code,
                target: sum_code,
                translator: function,
                images: vec![evidence],
            })
            .expect("injection");
        computes(&mut arena, &flows, id, sample, output);
    }
    let branch = arena.computation_return(variable);
    let case = arena.computation_case(variable, branch, branch);
    let lambda = arena.computation_lambda(case);
    let fold = arena.value_thunk(lambda);
    let inputs = [
        arena.value_injection(Side::Left, sample),
        arena.value_injection(Side::Right, sample),
    ];
    let images = inputs
        .into_iter()
        .map(|input| image(&mut arena, fold, input, sample, variable))
        .collect();
    let fold = flows
        .push(Flow::Forward {
            source: sum_code,
            target: code,
            translator: fold,
            images,
        })
        .expect("codiagonal");
    for input in inputs {
        computes(&mut arena, &flows, fold, input, sample);
    }

    // Projection onto Unit is definable in the inherited CBPV fragment.
    let unit_type = arena.value_type_unit();
    let unit_code = arena.value_quote(unit_type);
    let unit = arena.value_unit();
    let discard = returning(&mut arena, unit);
    let evidence = image(&mut arena, discard, sample_pair, unit, unit);
    let projection = flows
        .push(Flow::Forward {
            source: product_code,
            target: unit_code,
            translator: discard,
            images: vec![evidence],
        })
        .expect("terminal projection");
    computes(&mut arena, &flows, projection, sample_pair, unit);

    // Two equal-typed input positions must remain distinct in symbolic coverage.
    let identity = returning(&mut arena, variable);
    let first = arena.value_variable(DeBruijnIndex::from(1_u32));
    let output = arena.value_pair(first, variable);
    let evidence = image(&mut arena, identity, sample_pair, sample_pair, output);
    let identity = flows
        .push(Flow::Forward {
            source: product_code,
            target: product_code,
            translator: identity,
            images: vec![evidence],
        })
        .expect("product identity");
    computes(&mut arena, &flows, identity, sample_pair, sample_pair);
}

#[test]
fn constant_leaf_and_forged_evidence_refuse()
{
    let mut arena = TermArena::new();
    let mut flows = Flows::new();
    let string = arena.value_type_base(BaseType::String);
    let code = arena.value_quote(string);
    let sample = arena.value_literal(Literal::Text(StringLiteral::new("constant".into())));
    let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
    let constant = returning(&mut arena, sample);
    let evidence = image(&mut arena, constant, sample, sample, sample);
    let bad = flows
        .push(Flow::Forward {
            source: code,
            target: code,
            translator: constant,
            images: vec![evidence.clone()],
        })
        .expect("raw constant");
    assert!(
        matches!(form(&mut arena, &flows, bad, ReplayBudget::DEFAULT), Err(FlowError::NonNatural(found)) if found == sample)
    );
    let forged = flows
        .push(Flow::Forward {
            source: code,
            target: code,
            translator: constant,
            images: vec![Image {
                output: variable,
                dialogue: evidence.dialogue,
            }],
        })
        .expect("forged generic image");
    assert!(matches!(
        form(&mut arena, &flows, forged, ReplayBudget::DEFAULT),
        Err(FlowError::ForwardReplay {
            pattern: PatternPosition(0),
            verdict: KernelVerdict::Declined(_)
        })
    ));
    let identity = returning(&mut arena, variable);
    let fresh = arena.value_variable(DeBruijnIndex::from(1_u32));
    let identity_image = image(&mut arena, identity, sample, sample, variable);
    for output in [sample, fresh] {
        let bad = flows
            .push(Flow::Forward {
                source: code,
                target: code,
                translator: identity,
                images: vec![Image {
                    output,
                    dialogue: identity_image.dialogue.clone(),
                }],
            })
            .expect("bad leaf");
        assert!(
            matches!(form(&mut arena, &flows, bad, ReplayBudget::DEFAULT), Err(FlowError::NonNatural(found)) if found == output)
        );
    }
    let pair_type = arena.value_type_product(string, string);
    let pair_code = arena.value_quote(pair_type);
    let sample_pair = arena.value_pair(sample, sample);
    let wrong_pair = arena.value_pair(variable, variable);
    let evidence = image(&mut arena, identity, sample_pair, sample_pair, wrong_pair);
    let bad = flows
        .push(Flow::Forward {
            source: pair_code,
            target: pair_code,
            translator: identity,
            images: vec![evidence],
        })
        .expect("aliasing leaves");
    assert!(matches!(
        form(&mut arena, &flows, bad, ReplayBudget::DEFAULT),
        Err(FlowError::ForwardReplay {
            pattern: PatternPosition(0),
            verdict: KernelVerdict::Declined(_)
        })
    ));
    let literal_pair = arena.value_pair(variable, sample);
    let diagonal = returning(&mut arena, wrong_pair);
    let evidence = image(&mut arena, diagonal, sample, sample_pair, literal_pair);
    let bad = flows
        .push(Flow::Forward {
            source: code,
            target: pair_code,
            translator: diagonal,
            images: vec![evidence],
        })
        .expect("nested literal");
    assert!(
        matches!(form(&mut arena, &flows, bad, ReplayBudget::DEFAULT), Err(FlowError::NonNatural(found)) if found == sample)
    );
    let integer = arena.value_type_base(BaseType::Integer);
    let heterogeneous = arena.value_type_product(string, integer);
    let heterogeneous_code = arena.value_quote(heterogeneous);
    let first = arena.value_variable(DeBruijnIndex::from(1_u32));
    let swapped = arena.value_pair(variable, first);
    let bad = flows
        .push(Flow::Forward {
            source: heterogeneous_code,
            target: heterogeneous_code,
            translator: identity,
            images: vec![Image {
                output: swapped,
                dialogue: Dialogue::default(),
            }],
        })
        .expect("mistyped leaf permutation");
    assert!(
        matches!(form(&mut arena, &flows, bad, ReplayBudget::DEFAULT), Err(FlowError::NonNatural(found)) if found == variable)
    );
    let sum = arena.value_type_sum(string, string);
    let sum_code = arena.value_quote(sum);
    let injection = arena.value_injection(Side::Left, variable);
    let function = returning(&mut arena, injection);
    let literal_injection = arena.value_injection(Side::Left, sample);
    let evidence = image(
        &mut arena,
        function,
        sample,
        literal_injection,
        literal_injection,
    );
    let bad = flows
        .push(Flow::Forward {
            source: code,
            target: sum_code,
            translator: function,
            images: vec![evidence],
        })
        .expect("literal below sum");
    assert!(
        matches!(form(&mut arena, &flows, bad, ReplayBudget::DEFAULT), Err(FlowError::NonNatural(found)) if found == sample)
    );
}

#[test]
fn symmetry_motive_is_refused_structurally()
{
    let mut motives = Motives::new();
    let fixed = motives.push(Motive::El(Endpoint::Fixed)).expect("fixed");
    let moving = motives.push(Motive::El(Endpoint::Moving)).expect("moving");
    let migration = motives
        .push(Motive::Arrow(fixed, moving))
        .expect("migration");
    let forward = motives
        .push(Motive::Flow(Endpoint::Fixed, Endpoint::Moving))
        .expect("forward");
    let symmetry = motives
        .push(Motive::Flow(Endpoint::Moving, Endpoint::Fixed))
        .expect("symmetry");
    assert!(
        matches!(check_motive(&motives, symmetry, ReplayBudget::DEFAULT), Err(FlowError::NonCovariantMotive(found)) if found == symmetry)
    );
    check_motive(&motives, migration, ReplayBudget::DEFAULT).expect("covariant migration");
    check_motive(&motives, forward, ReplayBudget::DEFAULT).expect("forward family");
    let twice = motives
        .push(Motive::Arrow(symmetry, fixed))
        .expect("double reversal");
    check_motive(&motives, twice, ReplayBudget::DEFAULT).expect("two negatives are positive");
    let mixed = motives
        .push(Motive::Arrow(moving, moving))
        .expect("shared at both signs");
    let nested = motives
        .push(Motive::Product(migration, mixed))
        .expect("nested product");
    assert!(
        matches!(check_motive(&motives, nested, ReplayBudget::DEFAULT), Err(FlowError::NonCovariantMotive(found)) if found == moving)
    );
    let sum = motives.push(Motive::Sum(forward, migration)).expect("sum");
    check_motive(&motives, sum, ReplayBudget::DEFAULT).expect("covariant sum");
    assert!(matches!(
        check_motive(&motives, moving, ReplayBudget::from(0_u64)),
        Err(FlowError::Budget)
    ));
    let missing = sum;
    let mut empty = Motives::new();
    assert!(
        matches!(check_motive(&empty, missing, ReplayBudget::DEFAULT), Err(FlowError::UnknownMotive(found)) if found == missing)
    );
    assert!(
        matches!(empty.push(Motive::Arrow(missing, missing)), Err(FlowError::UnknownMotive(found)) if found == missing)
    );
}

#[test]
fn path_and_flow_never_coerce()
{
    let mut arena = TermArena::new();
    let fixture = fixture(&mut arena);
    let mut flows = Flows::new();
    let flow = terminal(&mut arena, &mut flows, &fixture);
    let mut paths = Paths::new();
    let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
    let identity = returning(&mut arena, variable);
    let first = apply(&mut arena, identity, fixture.unit);
    let second = apply(&mut arena, identity, variable);
    let composite = arena.computation_bind(first, second);
    let expected = arena.computation_return(fixture.unit);
    let (_, dialogue) = engine(&arena, composite, expected);
    let path = paths
        .push(Path::Equiv {
            source: fixture.unit_code,
            target: fixture.unit_code,
            forward: identity,
            backward: identity,
            round_trips: RoundTrips {
                source: vec![dialogue.clone()],
                target: vec![dialogue],
            },
        })
        .expect("equivalence");
    assert!(
        matches!(form_certificate(&mut arena, &paths, &flows, Certificate::Path(path), Family::Path, ReplayBudget::DEFAULT), Ok(CertificateType::Path(classifier)) if classifier.source == fixture.unit_type && classifier.target == fixture.unit_type)
    );
    assert!(
        matches!(form_certificate(&mut arena, &paths, &flows, Certificate::Flow(flow), Family::Flow, ReplayBudget::DEFAULT), Ok(CertificateType::Flow(classifier)) if classifier.source == fixture.boolean_type && classifier.target == fixture.unit_type)
    );
    assert!(matches!(
        form_certificate(
            &mut arena,
            &paths,
            &flows,
            Certificate::Path(path),
            Family::Flow,
            ReplayBudget::DEFAULT
        ),
        Err(FlowError::FamilyMismatch {
            expected: Family::Flow,
            actual: Family::Path
        })
    ));
    assert!(matches!(
        form_certificate(
            &mut arena,
            &paths,
            &flows,
            Certificate::Flow(flow),
            Family::Path,
            ReplayBudget::DEFAULT
        ),
        Err(FlowError::FamilyMismatch {
            expected: Family::Path,
            actual: Family::Flow
        })
    ));
    let term = Ride {
        certificate: Certificate::Path(path),
        value: fixture.unit,
    };
    assert!(matches!(
        elaborate(&mut arena, &flows, term, ReplayBudget::DEFAULT),
        Err(FlowError::FamilyMismatch {
            expected: Family::Flow,
            actual: Family::Path
        })
    ));
}

#[test]
fn composition_preserves_direction_and_refuses_feedback()
{
    let mut arena = TermArena::new();
    let fixture = fixture(&mut arena);
    let mut flows = Flows::new();
    let fold = terminal(&mut arena, &mut flows, &fixture);
    let selected = fixture.constructors[1];
    let function = returning(&mut arena, selected);
    let evidence = image(&mut arena, function, fixture.unit, selected, selected);
    let injection = flows
        .push(Flow::Forward {
            source: fixture.unit_code,
            target: fixture.boolean,
            translator: function,
            images: vec![evidence],
        })
        .expect("injection");
    let constant = flows
        .push(Flow::Compose {
            first: fold,
            second: injection,
            seam: Seam::Sequence,
        })
        .expect("sequence");
    for input in fixture.constructors {
        computes(&mut arena, &flows, constant, input, selected);
    }
    let identity = flows
        .push(Flow::Compose {
            first: injection,
            second: fold,
            seam: Seam::Sequence,
        })
        .expect("injection then fold");
    computes(&mut arena, &flows, identity, fixture.unit, fixture.unit);
    let nested = flows
        .push(Flow::Compose {
            first: constant,
            second: fold,
            seam: Seam::Sequence,
        })
        .expect("nested composition");
    computes(&mut arena, &flows, nested, selected, fixture.unit);
    let cycle = flows
        .push(Flow::Compose {
            first: injection,
            second: fold,
            seam: Seam::Feedback,
        })
        .expect("feedback syntax");
    assert!(
        matches!(form(&mut arena, &flows, cycle, ReplayBudget::DEFAULT), Err(FlowError::Cycle { first, second }) if first == injection && second == fold)
    );
    let mismatch = flows
        .push(Flow::Compose {
            first: fold,
            second: fold,
            seam: Seam::Sequence,
        })
        .expect("mismatched seam");
    assert!(matches!(
        form(&mut arena, &flows, mismatch, ReplayBudget::DEFAULT),
        Err(FlowError::EndpointMismatch)
    ));
    let missing = FlowId(usize::MAX);
    assert!(
        matches!(flows.push(Flow::Compose { first: fold, second: missing, seam: Seam::Sequence }), Err(FlowError::UnknownFlow(found)) if found == missing)
    );
}

#[test]
fn formation_boundaries_refuse()
{
    let mut arena = TermArena::new();
    let fixture = fixture(&mut arena);
    let mut flows = Flows::new();
    let terminal = terminal(&mut arena, &mut flows, &fixture);
    let missing = FlowId(usize::MAX);
    assert!(
        matches!(form(&mut arena, &flows, missing, ReplayBudget::DEFAULT), Err(FlowError::UnknownFlow(found)) if found == missing)
    );
    assert!(matches!(
        form(&mut arena, &flows, terminal, ReplayBudget::from(0_u64)),
        Err(FlowError::Budget)
    ));
    let bad = flows.push(Flow::Stay(fixture.unit)).expect("noncode");
    assert!(
        matches!(form(&mut arena, &flows, bad, ReplayBudget::DEFAULT), Err(FlowError::UnsupportedCode(found)) if found == fixture.unit)
    );
    let returner = arena.comp_type_returner(fixture.unit_type);
    let thunk = arena.value_type_thunk(returner);
    let code = arena.value_quote(thunk);
    let bad = flows.push(Flow::Stay(code)).expect("higher-order code");
    assert!(
        matches!(form(&mut arena, &flows, bad, ReplayBudget::DEFAULT), Err(FlowError::UnsupportedType(found)) if found == thunk)
    );
    let bad = flows
        .push(Flow::Forward {
            source: fixture.boolean,
            target: fixture.unit_code,
            translator: fixture.unit,
            images: Vec::new(),
        })
        .expect("nonfunction");
    assert!(matches!(
        form(&mut arena, &flows, bad, ReplayBudget::DEFAULT),
        Err(FlowError::Typing(_))
    ));
    let evidence = image(
        &mut arena,
        fixture.terminal,
        fixture.constructors[0],
        fixture.unit,
        fixture.unit,
    );
    for images in [Vec::new(), vec![evidence.clone()], vec![
        evidence.clone(),
        evidence.clone(),
        evidence,
    ]] {
        let bad = flows
            .push(Flow::Forward {
                source: fixture.boolean,
                target: fixture.unit_code,
                translator: fixture.terminal,
                images,
            })
            .expect("coverage");
        assert!(matches!(
            form(&mut arena, &flows, bad, ReplayBudget::DEFAULT),
            Err(FlowError::Coverage)
        ));
    }
    let term = Ride {
        certificate: Certificate::Flow(terminal),
        value: fixture.unit,
    };
    let expected = arena.computation_return(fixture.unit);
    let watermark = arena.watermark();
    assert!(matches!(
        replay_ride(
            &mut arena,
            &flows,
            term,
            expected,
            EngineClaim::Convertible,
            &Dialogue::default(),
            ReplayBudget::DEFAULT
        ),
        Err(FlowError::Typing(_))
    ));
    assert_eq!(arena.watermark(), watermark);
    let term = Ride {
        value: fixture.constructors[0],
        ..term
    };
    let wrong_type = arena.computation_return(fixture.constructors[0]);
    let watermark = arena.watermark();
    assert!(matches!(
        replay_ride(
            &mut arena,
            &flows,
            term,
            wrong_type,
            EngineClaim::Convertible,
            &Dialogue::default(),
            ReplayBudget::DEFAULT
        ),
        Err(FlowError::Typing(_))
    ));
    assert_eq!(arena.watermark(), watermark);
    assert!(matches!(
        replay_ride(
            &mut arena,
            &flows,
            term,
            expected,
            EngineClaim::Convertible,
            &Dialogue(vec![gandr_kernel_conversion_trace::ConversionDecision::Decompose; 32]),
            ReplayBudget::DEFAULT
        ),
        Ok(KernelVerdict::Declined(_))
    ));
}
