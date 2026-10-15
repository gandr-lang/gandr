//! Directed computation, naturality, variance and family-boundary witnesses,
//! over native flow nodes admitted by the ordinary checker.

use alloc::collections::BTreeMap;
use alloc::sync::Arc;
use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_check_memo::NullMemo;
use gandr_kernel_conversion_trace::ConversionDecision;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::Computation;
use gandr_kernel_term::ComputationId;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::Dialogue as ImageDialogue;
use gandr_kernel_term::Literal;
use gandr_kernel_term::PathEvidence;
use gandr_kernel_term::Side;
use gandr_kernel_term::StringLiteral;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueTypeId;

use super::reduce::RideStep;
use super::reduce::ride_beta;
use super::*;
use crate::KernelError;
use crate::check::check_closed_value;
use crate::check::synth_closed_value;
use crate::encoding::ContentTable;
use crate::path_universe::Dialogue;
use crate::path_universe::Reduction;
use crate::replay::EngineClaim;
use crate::replay::ReplayBudget;
use crate::rewrite::BinderDepth;

mod engine;
mod function;
use engine::engine;
use engine::portable;

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
    let boolean_type = arena.value_type_sum(&[unit_type, unit_type]);
    let boolean = arena.value_quote(boolean_type);
    let unit_code = arena.value_quote(unit_type);
    let unit = arena.value_unit();
    let constructors = [
        arena.value_injection(Side::Left.into(), unit),
        arena.value_injection(Side::Right.into(), unit),
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

/// Close an output under one binder per pattern leaf: the image `thunk(λ…λ.
/// return o)`.
///
/// # Specification
/// trivial.
fn opened(
    arena: &mut TermArena,
    output: ValueId,
    leaves: BinderDepth,
) -> ValueId
{
    let mut body = arena.computation_return(output);
    for _leaf in 0 .. usize::from(leaves) {
        body = arena.computation_lambda(body);
    }
    arena.value_thunk(body)
}

/// Produce an image and its dialogue from an independent closed engine
/// computation on a sample.
///
/// # Specification
/// - requires: the sample and map belong to the fixture fragment.
/// - ensures: opens `output` under `leaves` binders and retains the portable
///   engine-produced evidence from the sample; admission must independently
///   validate the symbolic output and replay it.
/// - panics: if the fixture's proposed sample output is not convertible.
///
/// # Adequacy
/// - hypothesis: L3 — a sample trace for a constant cannot certify a Base map.
/// - witness: `flow_universe::tests::constant_leaf_and_forged_evidence_refuse`
#[spec(ensures: |ret| matches!(arena.value(ret.0), Some(&gandr_kernel_term::Value::Thunk(_))))]
fn image(
    arena: &mut TermArena,
    function: ValueId,
    (input, sample_output): (ValueId, ValueId),
    output: ValueId,
    leaves: BinderDepth,
) -> (ValueId, ImageDialogue)
{
    let action = apply(arena, function, input);
    let expected = arena.computation_return(sample_output);
    let (claim, dialogue) = engine(arena, action, expected);
    assert_eq!(claim, EngineClaim::Convertible);
    let image = opened(arena, output, leaves);
    (image, dialogue.0.into_iter().map(portable).collect())
}

/// Mint a forward flow between two codes from its translator and images.
///
/// # Specification
/// trivial.
fn forward(
    arena: &mut TermArena,
    (source, target): (ValueId, ValueId),
    translator: ValueId,
    images: Vec<(ValueId, ImageDialogue)>,
) -> ValueId
{
    let classifier = arena.value_type_flow_universe(source, target);
    let (outputs, dialogues): (Vec<_>, Vec<_>) = images.into_iter().unzip();
    arena.value_forward_flow(classifier, translator, outputs.into(), dialogues.into())
}

/// The terminal map from Bool to Unit with both source-constructor images.
///
/// # Specification
/// - requires: the fixture's terminal translator.
/// - ensures: a forward flow at `Flow_U(Bool, Unit)` retaining that translator.
/// - panics: on an invalid fixture claim.
///
/// # Adequacy
/// - hypothesis: L3 — a terminal flow discards Boolean information, never
///   invents it.
/// - witness: `flow_universe::tests::stay_and_forward_admit_and_ride`
#[spec(ensures: |ret| matches!(arena.value(ret), Some(&gandr_kernel_term::Value::ForwardFlow { translator, .. }) if translator == fixture.terminal))]
fn terminal(
    arena: &mut TermArena,
    fixture: &Fixture,
) -> ValueId
{
    let images = fixture
        .constructors
        .into_iter()
        .map(|input| {
            image(
                arena,
                fixture.terminal,
                (input, fixture.unit),
                fixture.unit,
                BinderDepth::from(0_u32),
            )
        })
        .collect();
    forward(
        arena,
        (fixture.boolean, fixture.unit_code),
        fixture.terminal,
        images,
    )
}

/// The level-zero value universe.
///
/// # Specification
/// trivial.
fn universe(arena: &mut TermArena) -> ValueTypeId
{
    arena.value_type_universe(
        gandr_kernel_term::GroundSort::Value,
        gandr_kernel_strata::Level::zero(),
    )
}

/// The value motive `El(x)` over the level-zero universe.
///
/// # Specification
/// trivial.
fn element(arena: &mut TermArena) -> ValueTypeId
{
    let moving = arena.value_variable(DeBruijnIndex::from(0_u32));
    arena.value_type_element(moving, gandr_kernel_strata::Level::zero())
}

/// Ride a value along a flow at the value motive `El(x)`.
///
/// # Specification
/// trivial.
fn ride(
    arena: &mut TermArena,
    flow: ValueId,
    value: ValueId,
) -> ComputationId
{
    let motive = element(arena);
    arena.computation_ride(motive, flow, value)
}

/// The test's own model of a flow's forward action: a closed translator,
/// built independently of the kernel's ride table.
///
/// # Specification
/// - requires: `root` is built from `stay`, forward, sequential and function
///   flows.
/// - ensures: `stay` is the identity, a forward flow its translator, a sequence
///   the bind of its parts in order, and a function flow `λf. return thunk(λa'.
///   domain a' to a. f a to b. codomain b)`.
/// - panics: on any other flow.
///
/// # Adequacy
/// - hypothesis: L3 — the kernel's ride and this model agree on every flow the
///   witnesses ride.
/// - witness: `flow_universe::tests::composition_preserves_direction_and_refuses_feedback`
#[spec(ensures: |ret| matches!(arena.value(ret), Some(&gandr_kernel_term::Value::Thunk(_))))]
fn lowered(
    arena: &mut TermArena,
    root: ValueId,
) -> ValueId
{
    let mut pending = vec![(root, false)];
    let mut lowered = BTreeMap::<ValueId, ValueId>::new();
    while let Some((id, expanded)) = pending.pop() {
        if lowered.contains_key(&id) {
            continue;
        }
        let node = arena.value(id).cloned().expect("flow resolves");
        let translator = match node {
            gandr_kernel_term::Value::Stay { .. } => {
                let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
                returning(arena, variable)
            },
            gandr_kernel_term::Value::ForwardFlow { translator, .. } => translator,
            gandr_kernel_term::Value::Then { first, second, .. }
            | gandr_kernel_term::Value::FunctionFlow {
                domain: first,
                codomain: second,
                ..
            } if !expanded => {
                pending.push((id, true));
                pending.push((second, false));
                pending.push((first, false));
                continue;
            },
            gandr_kernel_term::Value::Then { first, second, .. } => {
                let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
                let first = apply(arena, lowered[&first], variable);
                let second = apply(arena, lowered[&second], variable);
                let body = arena.computation_bind(first, second);
                let lambda = arena.computation_lambda(body);
                arena.value_thunk(lambda)
            },
            gandr_kernel_term::Value::FunctionFlow {
                domain, codomain, ..
            } => {
                let argument = arena.value_variable(DeBruijnIndex::from(0_u32));
                let function = arena.value_variable(DeBruijnIndex::from(2_u32));
                let domain = apply(arena, lowered[&domain], argument);
                let function = apply(arena, function, argument);
                let codomain = apply(arena, lowered[&codomain], argument);
                let result = arena.computation_bind(function, codomain);
                let body = arena.computation_bind(domain, result);
                let lambda = arena.computation_lambda(body);
                let transported = arena.value_thunk(lambda);
                let returned = arena.computation_return(transported);
                let lambda = arena.computation_lambda(returned);
                arena.value_thunk(lambda)
            },
            gandr_kernel_term::Value::Constructor { .. }
            | gandr_kernel_term::Value::Record(_)
            | gandr_kernel_term::Value::SessionPath { .. }
            | gandr_kernel_term::Value::SessionFlow { .. }
            | gandr_kernel_term::Value::FlowProduct(..)
            | gandr_kernel_term::Value::PathRefl(_)
            | gandr_kernel_term::Value::PathProduct(..)
            | gandr_kernel_term::Value::PathEquiv { .. }
            | gandr_kernel_term::Value::Here { .. }
            | gandr_kernel_term::Value::Returned(_)
            | gandr_kernel_term::Value::Higher { .. }
            | gandr_kernel_term::Value::HigherEvaluation { .. }
            | gandr_kernel_term::Value::QuantifiedEvaluation { .. }
            | gandr_kernel_term::Value::Variable(_)
            | gandr_kernel_term::Value::Constant(_)
            | gandr_kernel_term::Value::Literal(_)
            | gandr_kernel_term::Value::Tuple(_)
            | gandr_kernel_term::Value::Injection(..)
            | gandr_kernel_term::Value::ListNil
            | gandr_kernel_term::Value::ListCons(..)
            | gandr_kernel_term::Value::Thunk(_)
            | gandr_kernel_term::Value::Lift { .. }
            | gandr_kernel_term::Value::Quote(_)
            | gandr_kernel_term::Value::QuoteComputation(_)
            | gandr_kernel_term::Value::StaticApplication(..) => {
                panic!("no forward action in the fixture")
            },
        };
        lowered.insert(id, translator);
    }
    lowered[&root]
}

/// Ride a value at `El(x)` and replay the ride against an independently
/// specified output.
///
/// # Specification
/// - ensures: returns the independently produced engine claim and kernel
///   verdict; both certify the explicit expected value, and the replay restores
///   the arena.
/// - panics: on any failed admission or replay assertion.
///
/// # Adequacy
/// - hypothesis: L2/L3 — golden outputs distinguish forward maps and order; the
///   independent engine supplies decisions over the test's own model, never a
///   kernel verdict.
/// - witness: `flow_universe::tests::composition_preserves_direction_and_refuses_feedback`
#[spec(ensures: |ret| ret == (EngineClaim::Convertible, KernelVerdict::Convertible))]
fn computes(
    arena: &mut TermArena,
    flow: ValueId,
    input: ValueId,
    output: ValueId,
) -> (EngineClaim, KernelVerdict)
{
    let model = lowered(arena, flow);
    let action = apply(arena, model, input);
    let expected = arena.computation_return(output);
    let (claim, dialogue) = engine(arena, action, expected);
    assert_eq!(claim, EngineClaim::Convertible);
    let term = ride(arena, flow, input);
    let watermark = arena.watermark();
    let verdict = replay_ride(
        arena,
        term,
        expected,
        claim,
        &dialogue,
        ReplayBudget::DEFAULT,
    )
    .expect("ride replay");
    assert_eq!(verdict, KernelVerdict::Convertible);
    assert_eq!(arena.watermark(), watermark);
    (claim, verdict)
}

/// Admit a closed value through the ordinary checker.
///
/// # Specification
/// trivial.
fn admit(
    arena: &mut TermArena,
    value: ValueId,
) -> Result<ValueTypeId, KernelError>
{
    synth_closed_value(arena, value)
}

#[test]
fn stay_and_forward_admit_and_ride()
{
    let mut arena = TermArena::new();
    let fixture = fixture(&mut arena);
    let terminal = terminal(&mut arena, &fixture);
    let classifier = admit(&mut arena, terminal).expect("the terminal map admits");
    assert_eq!(
        arena.value_type(classifier),
        Some(&gandr_kernel_term::ValueType::FlowUniverse(
            fixture.boolean,
            fixture.unit_code
        ))
    );
    assert_eq!(
        form_certificate(&mut arena, terminal, Family::Flow, ReplayBudget::DEFAULT),
        Ok(CertificateType::Flow(FlowType {
            source: fixture.boolean_type,
            target: fixture.unit_type,
        }))
    );
    // The universe certificate checks at the element reading too.
    let carrier = universe(&mut arena);
    let element_reading = arena.value_type_flow(carrier, fixture.boolean, fixture.unit_code);
    assert_eq!(
        check_closed_value(&mut arena, terminal, element_reading),
        Ok(())
    );

    // `stay` synthesizes the directed diagonal and checks at either reading.
    let stay = arena.value_stay(fixture.boolean);
    let diagonal = admit(&mut arena, stay).expect("stay admits");
    assert!(matches!(
        arena.value_type(diagonal),
        Some(&gandr_kernel_term::ValueType::Flow { domain, source, target })
            if source == fixture.boolean && target == fixture.boolean
                && level_zero_universe(&arena, domain) == Reading::Universe
    ));
    let reflexive = arena.value_type_flow_universe(fixture.boolean, fixture.boolean);
    assert_eq!(check_closed_value(&mut arena, stay, reflexive), Ok(()));
    assert_eq!(
        form_certificate(&mut arena, stay, Family::Flow, ReplayBudget::DEFAULT),
        Ok(CertificateType::Flow(FlowType {
            source: fixture.boolean_type,
            target: fixture.boolean_type,
        }))
    );
    let elsewhere = arena.value_type_flow_universe(fixture.boolean, fixture.unit_code);
    assert!(matches!(
        check_closed_value(&mut arena, stay, elsewhere),
        Err(KernelError::Identity(
            crate::element_identity::IdentityError::EndpointsDiffer { .. }
        ))
    ));

    for input in fixture.constructors {
        computes(&mut arena, terminal, input, fixture.unit);
        computes(&mut arena, stay, input, input);
        // `stay` returns its argument in one step, without its translator.
        let motive = element(&mut arena);
        let reduced = ride_beta(
            &mut arena,
            &mut ContentTable::new(),
            &mut NullMemo,
            RideStep {
                motive,
                flow: stay,
                value: input,
            },
        )
        .expect("one step");
        assert!(
            matches!(reduced, Reduction::Reduced(reduct) if arena.computation(reduct) == Some(&Computation::Return(input)))
        );
    }

    // An element `stay` at a Bool checks where its point does not synthesize.
    let [left, right] = fixture.constructors;
    let point = arena.value_stay(left);
    let at_bool = arena.value_type_flow(fixture.boolean_type, left, left);
    assert_eq!(check_closed_value(&mut arena, point, at_bool), Ok(()));
    let apart = arena.value_type_flow(fixture.boolean_type, left, right);
    assert!(matches!(
        check_closed_value(&mut arena, point, apart),
        Err(KernelError::Identity(
            crate::element_identity::IdentityError::EndpointsDiffer { .. }
        ))
    ));
}

#[test]
fn one_way_classes_preserve_leaves()
{
    let mut arena = TermArena::new();
    let base = arena.value_type_base(BaseType::String);
    let code = arena.value_quote(base);
    let sample = arena.value_literal(Literal::Text(StringLiteral::new("leaf".into())));
    let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
    let product = arena.value_type_product(&[base, base]);
    let product_code = arena.value_quote(product);
    let pair = arena.value_tuple(&[variable, variable]);
    let diagonal = returning(&mut arena, pair);
    let sample_pair = arena.value_tuple(&[sample, sample]);
    let evidence = image(
        &mut arena,
        diagonal,
        (sample, sample_pair),
        pair,
        BinderDepth::from(1_u32),
    );
    let diagonal = forward(&mut arena, (code, product_code), diagonal, vec![evidence]);
    admit(&mut arena, diagonal).expect("diagonal");
    computes(&mut arena, diagonal, sample, sample_pair);

    let sum = arena.value_type_sum(&[base, base]);
    let sum_code = arena.value_quote(sum);
    for side in [Side::Left, Side::Right] {
        let injection = arena.value_injection(side.into(), variable);
        let function = returning(&mut arena, injection);
        let output = arena.value_injection(side.into(), sample);
        let evidence = image(
            &mut arena,
            function,
            (sample, output),
            injection,
            BinderDepth::from(1_u32),
        );
        let flow = forward(&mut arena, (code, sum_code), function, vec![evidence]);
        admit(&mut arena, flow).expect("injection");
        computes(&mut arena, flow, sample, output);
    }
    let branch = arena.computation_return(variable);
    let case = arena.computation_case(variable, &[branch, branch]);
    let lambda = arena.computation_lambda(case);
    let fold = arena.value_thunk(lambda);
    let inputs = [
        arena.value_injection(Side::Left.into(), sample),
        arena.value_injection(Side::Right.into(), sample),
    ];
    let images = inputs
        .into_iter()
        .map(|input| {
            image(
                &mut arena,
                fold,
                (input, sample),
                variable,
                BinderDepth::from(1_u32),
            )
        })
        .collect();
    let fold = forward(&mut arena, (sum_code, code), fold, images);
    admit(&mut arena, fold).expect("codiagonal");
    for input in inputs {
        computes(&mut arena, fold, input, sample);
    }

    // Projection onto Unit is definable in the inherited CBPV fragment.
    let unit_type = arena.value_type_unit();
    let unit_code = arena.value_quote(unit_type);
    let unit = arena.value_unit();
    let discard = returning(&mut arena, unit);
    let evidence = image(
        &mut arena,
        discard,
        (sample_pair, unit),
        unit,
        BinderDepth::from(2_u32),
    );
    let projection = forward(&mut arena, (product_code, unit_code), discard, vec![
        evidence,
    ]);
    admit(&mut arena, projection).expect("terminal projection");
    computes(&mut arena, projection, sample_pair, unit);

    // Two equal-typed input positions must remain distinct in symbolic coverage.
    let identity = returning(&mut arena, variable);
    let first = arena.value_variable(DeBruijnIndex::from(1_u32));
    let output = arena.value_tuple(&[first, variable]);
    let evidence = image(
        &mut arena,
        identity,
        (sample_pair, sample_pair),
        output,
        BinderDepth::from(2_u32),
    );
    let identity = forward(&mut arena, (product_code, product_code), identity, vec![
        evidence,
    ]);
    admit(&mut arena, identity).expect("product identity");
    computes(&mut arena, identity, sample_pair, sample_pair);
}

/// **Permanent.** A translator that returns one string literal for every
/// string maps an infinite Base leaf to a constant: no leaf-natural image
/// exists, and forward admission refuses the literal by name.
#[test]
fn a_constant_literal_into_an_infinite_leaf_is_refused_at_forward()
{
    let mut arena = TermArena::new();
    let string = arena.value_type_base(BaseType::String);
    let code = arena.value_quote(string);
    let literal = arena.value_literal(Literal::Text(StringLiteral::new("constant".into())));
    let constant = returning(&mut arena, literal);
    let evidence = image(
        &mut arena,
        constant,
        (literal, literal),
        literal,
        BinderDepth::from(1_u32),
    );
    let flow = forward(&mut arena, (code, code), constant, vec![evidence]);
    assert_eq!(
        admit(&mut arena, flow),
        Err(KernelError::Flow(FlowError::NonNatural(literal)))
    );
}

#[test]
fn constant_leaf_and_forged_evidence_refuse()
{
    let mut arena = TermArena::new();
    let string = arena.value_type_base(BaseType::String);
    let code = arena.value_quote(string);
    let sample = arena.value_literal(Literal::Text(StringLiteral::new("constant".into())));
    let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
    let constant = returning(&mut arena, sample);
    let (_, constant_dialogue) = image(
        &mut arena,
        constant,
        (sample, sample),
        sample,
        BinderDepth::from(1_u32),
    );

    // A generic image beside the constant's sample trace does not replay.
    let generic = opened(&mut arena, variable, BinderDepth::from(1_u32));
    let forged = forward(&mut arena, (code, code), constant, vec![(
        generic,
        constant_dialogue,
    )]);
    assert!(matches!(
        admit(&mut arena, forged),
        Err(KernelError::Flow(FlowError::ForwardReplay {
            pattern: PatternPosition(0),
            verdict: KernelVerdict::Declined(_)
        }))
    ));

    // Neither a literal nor a fresh variable selects a source leaf.
    let identity = returning(&mut arena, variable);
    let fresh = arena.value_variable(DeBruijnIndex::from(1_u32));
    let (_, identity_dialogue) = image(
        &mut arena,
        identity,
        (sample, sample),
        variable,
        BinderDepth::from(1_u32),
    );
    for output in [sample, fresh] {
        let image = opened(&mut arena, output, BinderDepth::from(1_u32));
        let bad = forward(&mut arena, (code, code), identity, vec![(
            image,
            identity_dialogue.clone(),
        )]);
        assert_eq!(
            admit(&mut arena, bad),
            Err(KernelError::Flow(FlowError::NonNatural(output)))
        );
    }

    // An image binding one leaf too few is refused naming the image.
    let short = opened(&mut arena, variable, BinderDepth::from(0_u32));
    let bad = forward(&mut arena, (code, code), identity, vec![(
        short,
        identity_dialogue,
    )]);
    assert_eq!(
        admit(&mut arena, bad),
        Err(KernelError::Flow(FlowError::NonNatural(short)))
    );

    let pair_type = arena.value_type_product(&[string, string]);
    let pair_code = arena.value_quote(pair_type);
    let sample_pair = arena.value_tuple(&[sample, sample]);
    let wrong_pair = arena.value_tuple(&[variable, variable]);
    let evidence = image(
        &mut arena,
        identity,
        (sample_pair, sample_pair),
        wrong_pair,
        BinderDepth::from(2_u32),
    );
    let bad = forward(&mut arena, (pair_code, pair_code), identity, vec![evidence]);
    assert!(matches!(
        admit(&mut arena, bad),
        Err(KernelError::Flow(FlowError::ForwardReplay {
            pattern: PatternPosition(0),
            verdict: KernelVerdict::Declined(_)
        }))
    ));
    let literal_pair = arena.value_tuple(&[variable, sample]);
    let diagonal = returning(&mut arena, wrong_pair);
    let evidence = image(
        &mut arena,
        diagonal,
        (sample, sample_pair),
        literal_pair,
        BinderDepth::from(1_u32),
    );
    let bad = forward(&mut arena, (code, pair_code), diagonal, vec![evidence]);
    assert_eq!(
        admit(&mut arena, bad),
        Err(KernelError::Flow(FlowError::NonNatural(sample)))
    );
    let integer = arena.value_type_base(BaseType::Integer);
    let heterogeneous = arena.value_type_product(&[string, integer]);
    let heterogeneous_code = arena.value_quote(heterogeneous);
    let first = arena.value_variable(DeBruijnIndex::from(1_u32));
    let swapped = arena.value_tuple(&[variable, first]);
    let swapped = opened(&mut arena, swapped, BinderDepth::from(2_u32));
    let bad = forward(
        &mut arena,
        (heterogeneous_code, heterogeneous_code),
        identity,
        vec![(swapped, Vec::new())],
    );
    assert_eq!(
        admit(&mut arena, bad),
        Err(KernelError::Flow(FlowError::NonNatural(variable)))
    );
    let sum = arena.value_type_sum(&[string, string]);
    let sum_code = arena.value_quote(sum);
    let injection = arena.value_injection(Side::Left.into(), variable);
    let function = returning(&mut arena, injection);
    let literal_injection = arena.value_injection(Side::Left.into(), sample);
    let evidence = image(
        &mut arena,
        function,
        (sample, literal_injection),
        literal_injection,
        BinderDepth::from(1_u32),
    );
    let bad = forward(&mut arena, (code, sum_code), function, vec![evidence]);
    assert_eq!(
        admit(&mut arena, bad),
        Err(KernelError::Flow(FlowError::NonNatural(sample)))
    );
}

/// **Permanent.** Riding a flow at the motive `Flow(x, a)` would turn a flow
/// from `a` to `b` into one from `b` back to `a`: the moving endpoint sits at
/// a flow's source, and the covariance gate refuses it by name at `ride`.
#[test]
fn symmetry_motive_is_refused_at_ride()
{
    let mut arena = TermArena::new();
    let fixture = fixture(&mut arena);
    let terminal = terminal(&mut arena, &fixture);
    let carrier = universe(&mut arena);
    let moving = arena.value_variable(DeBruijnIndex::from(0_u32));
    let symmetry = arena.value_type_flow(carrier, moving, fixture.boolean);
    let stay = arena.value_stay(fixture.boolean);
    let back = arena.computation_ride(symmetry, terminal, stay);
    let expected = arena.computation_return(stay);
    let watermark = arena.watermark();
    assert_eq!(
        replay_ride(
            &mut arena,
            back,
            expected,
            EngineClaim::Convertible,
            &Dialogue::default(),
            ReplayBudget::DEFAULT
        ),
        Err(KernelError::Flow(FlowError::NonCovariantMotive(
            gandr_kernel_term::AnyNode::ValueType(symmetry)
        )))
    );
    assert_eq!(arena.watermark(), watermark);

    // The gate's signs: a flow's target and an arrow's codomain preserve,
    // a flow's source and an arrow's domain reverse, and two reversals admit.
    let zero = DeBruijnIndex::from(0_u32);
    let el_moving = element(&mut arena);
    let el_fixed = arena.value_type_element(fixture.boolean, gandr_kernel_strata::Level::zero());
    let forward_motive = arena.value_type_flow(carrier, fixture.boolean, moving);
    let fixed_returner = arena.comp_type_returner(el_fixed);
    let moving_returner = arena.comp_type_returner(el_moving);
    let migration = arena.comp_type_arrow(el_fixed, moving_returner);
    let migration = arena.value_type_thunk(migration);
    let argument = arena.comp_type_arrow(el_moving, fixed_returner);
    let argument = arena.value_type_thunk(argument);
    let twice = arena.comp_type_arrow(argument, fixed_returner);
    let twice = arena.value_type_thunk(twice);
    for admitted in [forward_motive, migration, twice, el_moving] {
        check_motive(&mut arena, admitted, zero, ReplayBudget::DEFAULT)
            .expect("a covariant motive");
    }
    assert_eq!(
        check_motive(&mut arena, argument, zero, ReplayBudget::DEFAULT),
        Err(FlowError::NonCovariantMotive(
            gandr_kernel_term::AnyNode::ValueType(el_moving)
        ))
    );
    // One subtree at both signs refuses wherever it sits.
    let both = arena.comp_type_arrow(el_moving, moving_returner);
    let both = arena.value_type_thunk(both);
    let nested = arena.value_type_product(&[migration, both]);
    assert_eq!(
        check_motive(&mut arena, nested, zero, ReplayBudget::DEFAULT),
        Err(FlowError::NonCovariantMotive(
            gandr_kernel_term::AnyNode::ValueType(el_moving)
        ))
    );
    // An identity relates its endpoints both ways: no occurrence admits.
    let identity = arena.value_type_path(carrier, fixture.boolean, moving);
    assert_eq!(
        check_motive(&mut arena, identity, zero, ReplayBudget::DEFAULT),
        Err(FlowError::NonCovariantMotive(
            gandr_kernel_term::AnyNode::ValueType(identity)
        ))
    );
    // An outer variable is fixed, wherever it stands.
    let outer = arena.value_variable(DeBruijnIndex::from(1_u32));
    let outer = arena.value_type_flow(carrier, outer, fixture.boolean);
    let watermark = arena.watermark();
    check_motive(&mut arena, outer, zero, ReplayBudget::DEFAULT).expect("a fixed outer variable");
    assert_eq!(arena.watermark(), watermark);
    assert_eq!(
        check_motive(&mut arena, el_moving, zero, ReplayBudget::from(0_u64)),
        Err(FlowError::Budget)
    );
}

/// **Permanent.** No node reverses a flow: a flow checked at its reversed
/// classifier, a value ridden from the target, and a flow composed with
/// itself the wrong way round each refuse by name.
#[test]
fn back_has_no_directed_reading()
{
    let mut arena = TermArena::new();
    let fixture = fixture(&mut arena);
    let terminal = terminal(&mut arena, &fixture);
    let reversed = arena.value_type_flow_universe(fixture.unit_code, fixture.boolean);
    assert!(matches!(
        check_closed_value(&mut arena, terminal, reversed),
        Err(KernelError::ValueTypeMismatch(_))
    ));
    let carrier = universe(&mut arena);
    let reversed = arena.value_type_flow(carrier, fixture.unit_code, fixture.boolean);
    assert!(matches!(
        check_closed_value(&mut arena, terminal, reversed),
        Err(KernelError::ValueTypeMismatch(_))
    ));
    let from_target = ride(&mut arena, terminal, fixture.unit);
    let expected = arena.computation_return(fixture.constructors[0]);
    assert!(matches!(
        replay_ride(
            &mut arena,
            from_target,
            expected,
            EngineClaim::Convertible,
            &Dialogue::default(),
            ReplayBudget::DEFAULT
        ),
        Err(error) if !matches!(error, KernelError::Flow(_))
    ));
    let round = arena.value_then(terminal, terminal, gandr_kernel_term::Seam::Sequence);
    assert_eq!(
        admit(&mut arena, round),
        Err(KernelError::Flow(FlowError::EndpointMismatch))
    );
}

#[test]
fn path_and_flow_never_coerce()
{
    let mut arena = TermArena::new();
    let fixture = fixture(&mut arena);
    let flow = terminal(&mut arena, &fixture);
    let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
    let identity = returning(&mut arena, variable);
    let first = apply(&mut arena, identity, fixture.unit);
    let second = apply(&mut arena, identity, variable);
    let composite = arena.computation_bind(first, second);
    let expected = arena.computation_return(fixture.unit);
    let (_, dialogue) = engine(&arena, composite, expected);
    let classifier = arena.value_type_path_universe(fixture.unit_code, fixture.unit_code);
    let dialogue = dialogue.0.into_iter().map(portable).collect::<Vec<_>>();
    let path = arena.value_path_equiv(
        classifier,
        identity,
        identity,
        Arc::new(PathEvidence {
            source: vec![dialogue.clone()],
            target: vec![dialogue],
        }),
    );
    assert!(
        matches!(form_certificate(&mut arena, path, Family::Path, ReplayBudget::DEFAULT), Ok(CertificateType::Path(classifier)) if classifier.source == fixture.unit_type && classifier.target == fixture.unit_type)
    );
    assert!(
        matches!(form_certificate(&mut arena, flow, Family::Flow, ReplayBudget::DEFAULT), Ok(CertificateType::Flow(classifier)) if classifier.source == fixture.boolean_type && classifier.target == fixture.unit_type)
    );
    assert_eq!(
        form_certificate(&mut arena, path, Family::Flow, ReplayBudget::DEFAULT),
        Err(KernelError::Flow(FlowError::FamilyMismatch {
            expected: Family::Flow,
            actual: Family::Path
        }))
    );
    assert_eq!(
        form_certificate(&mut arena, flow, Family::Path, ReplayBudget::DEFAULT),
        Err(KernelError::Flow(FlowError::FamilyMismatch {
            expected: Family::Path,
            actual: Family::Flow
        }))
    );
    // `ride` consumes no equivalence.
    let along_path = ride(&mut arena, path, fixture.unit);
    let expected = arena.computation_return(fixture.unit);
    assert_eq!(
        replay_ride(
            &mut arena,
            along_path,
            expected,
            EngineClaim::Convertible,
            &Dialogue::default(),
            ReplayBudget::DEFAULT
        ),
        Err(KernelError::Flow(FlowError::FamilyMismatch {
            expected: Family::Flow,
            actual: Family::Path
        }))
    );
    let not_path = form_certificate(
        &mut arena,
        fixture.unit,
        Family::Path,
        ReplayBudget::DEFAULT,
    );
    assert!(matches!(
        not_path,
        Err(KernelError::Path(
            crate::path_universe::PathError::ExpectedPath(_)
        ))
    ));
    assert!(matches!(
        form_certificate(&mut arena, fixture.unit, Family::Flow, ReplayBudget::DEFAULT),
        Err(KernelError::Flow(FlowError::ExpectedFlow(found))) if arena.value_type(found) == Some(&gandr_kernel_term::ValueType::unit())
    ));
    let forged = arena.value_path_equiv(
        classifier,
        identity,
        identity,
        Arc::new(PathEvidence::default()),
    );
    let result = form_certificate(&mut arena, forged, Family::Path, ReplayBudget::DEFAULT);
    assert!(matches!(result, Err(KernelError::Path(_))));
}

#[test]
fn composition_preserves_direction_and_refuses_feedback()
{
    let mut arena = TermArena::new();
    let fixture = fixture(&mut arena);
    let fold = terminal(&mut arena, &fixture);
    let selected = fixture.constructors[1];
    let function = returning(&mut arena, selected);
    let evidence = image(
        &mut arena,
        function,
        (fixture.unit, selected),
        selected,
        BinderDepth::from(0_u32),
    );
    let injection = forward(
        &mut arena,
        (fixture.unit_code, fixture.boolean),
        function,
        vec![evidence],
    );
    let constant = arena.value_then(fold, injection, gandr_kernel_term::Seam::Sequence);
    let endomap = admit(&mut arena, constant).expect("sequence");
    assert_eq!(
        arena.value_type(endomap),
        Some(&gandr_kernel_term::ValueType::FlowUniverse(
            fixture.boolean,
            fixture.boolean
        ))
    );
    for input in fixture.constructors {
        computes(&mut arena, constant, input, selected);
    }
    let identity = arena.value_then(injection, fold, gandr_kernel_term::Seam::Sequence);
    computes(&mut arena, identity, fixture.unit, fixture.unit);
    let nested = arena.value_then(constant, fold, gandr_kernel_term::Seam::Sequence);
    computes(&mut arena, nested, selected, fixture.unit);

    // A feedback seam closes a cycle and refuses, naming both occurrences.
    let cycle = arena.value_then(injection, fold, gandr_kernel_term::Seam::Feedback);
    assert_eq!(
        admit(&mut arena, cycle),
        Err(KernelError::Flow(FlowError::Cycle {
            first: injection,
            second: fold
        }))
    );
    let mismatch = arena.value_then(fold, fold, gandr_kernel_term::Seam::Sequence);
    assert_eq!(
        admit(&mut arena, mismatch),
        Err(KernelError::Flow(FlowError::EndpointMismatch))
    );

    // Element flows compose at their carrier, and `stay` composes with a
    // universe flow under the level-zero universe's two readings.
    let string = arena.value_type_base(BaseType::String);
    let sample = arena.value_literal(Literal::Text(StringLiteral::new("point".into())));
    let point = arena.value_stay(sample);
    let twice = arena.value_then(point, point, gandr_kernel_term::Seam::Sequence);
    let at_string = admit(&mut arena, twice).expect("element composition");
    assert!(matches!(
        arena.value_type(at_string),
        Some(&gandr_kernel_term::ValueType::Flow { domain, source, target })
            if source == sample && target == sample
                && arena.value_type(domain) == arena.value_type(string)
    ));
    let stay = arena.value_stay(fixture.boolean);
    let prefixed = arena.value_then(stay, fold, gandr_kernel_term::Seam::Sequence);
    let carrier = universe(&mut arena);
    let element_reading = arena.value_type_flow(carrier, fixture.boolean, fixture.unit_code);
    assert_eq!(
        check_closed_value(&mut arena, prefixed, element_reading),
        Ok(())
    );
    for input in fixture.constructors {
        computes(&mut arena, prefixed, input, fixture.unit);
    }
}

#[test]
fn ride_computes_through_the_motive_rows()
{
    let mut arena = TermArena::new();
    let fixture = fixture(&mut arena);
    let terminal = terminal(&mut arena, &fixture);
    let [left, right] = fixture.constructors;
    let moving = element(&mut arena);
    let replays = |arena: &mut TermArena, term: ComputationId, output: ValueId| {
        let expected = arena.computation_return(output);
        replay_ride(
            arena,
            term,
            expected,
            EngineClaim::Convertible,
            &Dialogue::default(),
            ReplayBudget::DEFAULT,
        )
    };

    // A pair rides componentwise.
    let pair = arena.value_type_product(&[moving, moving]);
    let input = arena.value_tuple(&[left, right]);
    let output = arena.value_tuple(&[fixture.unit, fixture.unit]);
    let term = arena.computation_ride(pair, terminal, input);
    assert_eq!(
        replays(&mut arena, term, output),
        Ok(KernelVerdict::Convertible)
    );
    // A sum rides within its summand.
    let unit_type = fixture.unit_type;
    let sum = arena.value_type_sum(&[moving, unit_type]);
    let input = arena.value_injection(Side::Left.into(), right);
    let output = arena.value_injection(Side::Left.into(), fixture.unit);
    let term = arena.computation_ride(sum, terminal, input);
    assert_eq!(
        replays(&mut arena, term, output),
        Ok(KernelVerdict::Convertible)
    );
    // A list rides cell by cell.
    let list = arena.value_type_list(moving);
    let nil = arena.value_list_nil();
    let tail = arena.value_list_cons(right, nil);
    let input = arena.value_list_cons(left, tail);
    let unit_tail = arena.value_list_cons(fixture.unit, nil);
    let output = arena.value_list_cons(fixture.unit, unit_tail);
    let term = arena.computation_ride(list, terminal, input);
    assert_eq!(
        replays(&mut arena, term, output),
        Ok(KernelVerdict::Convertible)
    );
    // A false output does not certify.
    let term = arena.computation_ride(list, terminal, input);
    assert!(matches!(
        replays(&mut arena, term, input),
        Err(error) if !matches!(error, KernelError::Flow(_))
    ));

    // The singleton motive composes: `stay` rides to the flow, any other
    // flow to its composition with it.
    let carrier = universe(&mut arena);
    let moving_point = arena.value_variable(DeBruijnIndex::from(0_u32));
    let singleton = arena.value_type_flow(carrier, fixture.boolean, moving_point);
    let stay = arena.value_stay(fixture.boolean);
    let term = arena.computation_ride(singleton, terminal, stay);
    assert_eq!(
        replays(&mut arena, term, terminal),
        Ok(KernelVerdict::Convertible)
    );
    let constant = returning(&mut arena, right);
    let images = fixture
        .constructors
        .into_iter()
        .map(|input| {
            image(
                &mut arena,
                constant,
                (input, right),
                right,
                BinderDepth::from(0_u32),
            )
        })
        .collect();
    let to_right = forward(
        &mut arena,
        (fixture.boolean, fixture.boolean),
        constant,
        images,
    );
    let term = arena.computation_ride(singleton, terminal, to_right);
    let composite = arena.value_then(to_right, terminal, gandr_kernel_term::Seam::Sequence);
    assert_eq!(
        replays(&mut arena, term, composite),
        Ok(KernelVerdict::Convertible)
    );
    // A motive ignoring its binder returns the value.
    let term = arena.computation_ride(fixture.boolean_type, terminal, left);
    assert_eq!(
        replays(&mut arena, term, left),
        Ok(KernelVerdict::Convertible)
    );
}

/// A flow product synthesizes the universe flow between the pairs of its
/// components' endpoints, refuses the reversed classifier, and rides a pair
/// componentwise, the first flow on the left.
#[test]
fn a_flow_product_rides_a_pair_componentwise()
{
    let mut arena = TermArena::new();
    let fixture = fixture(&mut arena);
    let terminal = terminal(&mut arena, &fixture);
    let stay = arena.value_stay(fixture.boolean);
    let product = arena.value_flow_product(terminal, stay);
    let classifier = admit(&mut arena, product).expect("the product admits");
    let decoded = |arena: &TermArena, code: ValueId| match arena.value(code) {
        Some(&gandr_kernel_term::Value::Quote(root)) => arena.value_type(root).cloned(),
        _ => None,
    };
    let Some(&gandr_kernel_term::ValueType::FlowUniverse(source, target)) =
        arena.value_type(classifier)
    else {
        panic!("a flow product synthesizes a universe flow");
    };
    assert_eq!(
        decoded(&arena, source),
        Some(gandr_kernel_term::ValueType::Product(
            [fixture.boolean_type, fixture.boolean_type].into()
        ))
    );
    assert_eq!(
        decoded(&arena, target),
        Some(gandr_kernel_term::ValueType::Product(
            [fixture.unit_type, fixture.boolean_type].into()
        ))
    );
    let reversed = arena.value_type_flow_universe(target, source);
    assert!(check_closed_value(&mut arena, product, reversed).is_err());

    let [left, right] = fixture.constructors;
    let replays = |arena: &mut TermArena, input: ValueId, output: ValueId| {
        let term = ride(arena, product, input);
        let expected = arena.computation_return(output);
        replay_ride(
            arena,
            term,
            expected,
            EngineClaim::Convertible,
            &Dialogue::default(),
            ReplayBudget::DEFAULT,
        )
    };
    let input = arena.value_tuple(&[right, left]);
    let output = arena.value_tuple(&[fixture.unit, left]);
    assert_eq!(
        replays(&mut arena, input, output),
        Ok(KernelVerdict::Convertible)
    );
    // The components ride in place: the right component is not the left's.
    let swapped = arena.value_tuple(&[fixture.unit, right]);
    let verdict = replays(&mut arena, input, swapped);
    assert!(
        !matches!(
            verdict,
            Ok(KernelVerdict::Convertible) | Err(KernelError::Flow(_))
        ),
        "{verdict:?}"
    );
    // A pair over a function code is no code of the universe's vocabulary.
    let returner = arena.comp_type_returner(fixture.boolean_type);
    let function = arena.comp_type_arrow(fixture.boolean_type, returner);
    let function = arena.value_type_thunk(function);
    let function = arena.value_quote(function);
    let at_function = arena.value_stay(function);
    let mixed = arena.value_flow_product(at_function, stay);
    assert!(
        matches!(admit(&mut arena, mixed), Err(KernelError::Flow(_))),
        "a flow product over a function code is refused"
    );
}

/// Directed J: a telescope ride along `stay` in both entries returns its
/// value; along `stay` in the carrier it rides in the fibre; a flow over
/// another start refuses by name.
#[test]
fn directed_j_rides_the_telescope()
{
    let mut arena = TermArena::new();
    let string = arena.value_type_base(BaseType::String);
    let here = arena.value_literal(Literal::Text(StringLiteral::new("here".into())));
    let there = arena.value_literal(Literal::Text(StringLiteral::new("there".into())));
    // Π (y : String). Π (z : Flow(String, here, y)). F Flow(String, here, y).
    let point = arena.value_variable(DeBruijnIndex::from(0_u32));
    let family = arena.value_type_flow(string, here, point);
    let outer = arena.value_variable(DeBruijnIndex::from(1_u32));
    let body = arena.value_type_flow(string, here, outer);
    let returner = arena.comp_type_returner(body);
    let inner = arena.comp_type_pi(family, returner);
    let motive = arena.comp_type_pi(string, inner);
    let flow = arena.value_stay(here);
    let start = arena.value_stay(here);
    let over = arena.value_stay(start);
    let value = arena.value_stay(here);
    let term = arena.computation_telescope_ride(motive, flow, start, over, value);
    let expected = arena.computation_return(value);
    assert_eq!(
        replay_ride_closed(&mut arena, term, expected),
        Ok(KernelVerdict::Convertible)
    );
    let over = arena.value_then(over, over, gandr_kernel_term::Seam::Sequence);
    let term = arena.computation_telescope_ride(motive, flow, start, over, value);
    assert_eq!(
        replay_ride_closed(&mut arena, term, expected),
        Ok(KernelVerdict::Convertible)
    );
    // A flow over another start does not lie over the carrier flow.
    let elsewhere = arena.value_stay(there);
    let astray = arena.value_stay(elsewhere);
    let term = arena.computation_telescope_ride(motive, flow, start, astray, value);
    assert!(matches!(
        replay_ride_closed(&mut arena, term, expected),
        Err(KernelError::Identity(
            crate::element_identity::IdentityError::NotOver { .. }
        ))
    ));
    // A family whose point sits at a flow's source refuses at the gate.
    let backward = arena.value_type_flow(string, outer, here);
    let returner = arena.comp_type_returner(backward);
    let inner = arena.comp_type_pi(family, returner);
    let symmetric = arena.comp_type_pi(string, inner);
    let term = arena.computation_telescope_ride(symmetric, flow, start, over, value);
    assert_eq!(
        replay_ride_closed(&mut arena, term, expected),
        Err(KernelError::Flow(FlowError::NonCovariantMotive(
            gandr_kernel_term::AnyNode::ValueType(backward)
        )))
    );
}

/// Check a closed telescope ride and replay it against its expected result
/// with an empty dialogue.
///
/// # Specification
/// trivial.
fn replay_ride_closed(
    arena: &mut TermArena,
    term: ComputationId,
    expected: ComputationId,
) -> Result<KernelVerdict, KernelError>
{
    replay_ride(
        arena,
        term,
        expected,
        EngineClaim::Convertible,
        &Dialogue::default(),
        ReplayBudget::DEFAULT,
    )
}

#[test]
fn formation_boundaries_refuse()
{
    let mut arena = TermArena::new();
    let fixture = fixture(&mut arena);
    let terminal = terminal(&mut arena, &fixture);
    let classifier = arena.value_type_flow_universe(fixture.boolean, fixture.unit_code);
    assert_eq!(
        endpoints(&arena, classifier, ReplayBudget::from(0_u64)),
        Err(FlowError::Budget)
    );
    // A `Flow_U` endpoint outside the vocabulary refuses at formation.
    let returner = arena.comp_type_returner(fixture.unit_type);
    let thunk = arena.value_type_thunk(returner);
    let code = arena.value_quote(thunk);
    let stay = arena.value_stay(code);
    let outside = arena.value_type_flow_universe(code, code);
    assert_eq!(
        check_closed_value(&mut arena, stay, outside),
        Err(KernelError::Flow(FlowError::UnsupportedType(thunk)))
    );
    let nonfunction = forward(
        &mut arena,
        (fixture.boolean, fixture.unit_code),
        fixture.unit,
        Vec::new(),
    );
    assert!(matches!(
        admit(&mut arena, nonfunction),
        Err(error) if !matches!(error, KernelError::Flow(_))
    ));
    let evidence = image(
        &mut arena,
        fixture.terminal,
        (fixture.constructors[0], fixture.unit),
        fixture.unit,
        BinderDepth::from(0_u32),
    );
    for images in [Vec::new(), vec![evidence.clone()], vec![
        evidence.clone(),
        evidence.clone(),
        evidence,
    ]] {
        let bad = forward(
            &mut arena,
            (fixture.boolean, fixture.unit_code),
            fixture.terminal,
            images,
        );
        assert_eq!(
            admit(&mut arena, bad),
            Err(KernelError::Flow(FlowError::Coverage))
        );
    }
    let term = ride(&mut arena, terminal, fixture.unit);
    let expected = arena.computation_return(fixture.unit);
    let watermark = arena.watermark();
    assert!(matches!(
        replay_ride(
            &mut arena,
            term,
            expected,
            EngineClaim::Convertible,
            &Dialogue::default(),
            ReplayBudget::DEFAULT
        ),
        Err(error) if !matches!(error, KernelError::Flow(_))
    ));
    assert_eq!(arena.watermark(), watermark);
    let term = ride(&mut arena, terminal, fixture.constructors[0]);
    let wrong_type = arena.computation_return(fixture.constructors[0]);
    let watermark = arena.watermark();
    assert!(matches!(
        replay_ride(
            &mut arena,
            term,
            wrong_type,
            EngineClaim::Convertible,
            &Dialogue::default(),
            ReplayBudget::DEFAULT
        ),
        Err(error) if !matches!(error, KernelError::Flow(_))
    ));
    assert_eq!(arena.watermark(), watermark);
    assert!(matches!(
        replay_ride(
            &mut arena,
            term,
            expected,
            EngineClaim::Convertible,
            &Dialogue(vec![ConversionDecision::Decompose; 32]),
            ReplayBudget::DEFAULT
        ),
        Ok(KernelVerdict::Declined(_))
    ));
}
