use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::vec::Vec;

use gandr_core_term::CoreArena;
use gandr_core_term::DefinitionalEnvironment;
use gandr_core_term::FieldLabel;
use gandr_core_term::Summand;
use gandr_kernel_conversion_trace::ConversionSide;
use gandr_kernel_strata::Level;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::GlobalIndex;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Sign;

use super::Choice;
use super::DomainArena;
use super::DomainValueId;
use super::Frozen;
use super::Glued;
use super::Head;
use super::NeutralHead;
use super::Plan;
use super::Settled;
use super::Step;
use super::Unfolding;
use crate::TermFace;
use crate::closure::Environment;
use crate::domain::Elimination;
use crate::domain::FlowFormer;

/// What [`super::plan`] answers for two values under `frozen`, with nothing
/// to unfold.
///
/// # Specification
/// trivial.
fn planned(
    core: &CoreArena,
    domain: &DomainArena,
    frozen: &Frozen,
    left: DomainValueId,
    right: DomainValueId,
) -> Result<Plan, super::ConversionFault>
{
    let chain = crate::LoweredChain::new();
    let environment = DefinitionalEnvironment::new();
    let definitions = crate::Definitions::new(&chain, &environment, environment.root());
    super::plan(
        core,
        domain,
        definitions,
        frozen,
        Glued::Value(left),
        Glued::Value(right),
    )
}

/// A thunk over `return ⟨⟩`: a flexible part, so a value holding it is planned
/// by its former rather than settled by its guard.
///
/// # Specification
/// trivial.
fn thunk(
    core: &mut CoreArena,
    domain: &mut DomainArena,
) -> DomainValueId
{
    let produced = core.value_unit();
    let body = core.computation_return(produced);
    let suspended = domain.comp_closure_node(body, Environment::new());
    domain.value_thunk(suspended, TermFace::Reduced)
}

/// A domain literal over the integer one, held at a fresh core node.
///
/// # Specification
/// trivial.
fn literal_one(
    core: &mut CoreArena,
    domain: &mut DomainArena,
) -> DomainValueId
{
    let magnitude =
        Magnitude::from_decimal_text(String::from("1")).expect("the digits are decimal");
    let payload = Literal::Integer(IntegerLiteral::new(Sign::NonNegative, magnitude));
    let held = core.value_literal(payload.clone());
    domain.value_literal(held, &payload, TermFace::Reduced)
}

#[test]
fn freezing_is_idempotent_and_local_to_one_side()
{
    let mut domain = DomainArena::new();
    let floor = domain.watermark();
    let first = ConstantIndex::from(0_usize);
    let second = ConstantIndex::from(1_usize);
    let loaded = domain
        .neutral_node(
            NeutralHead::Constant(first),
            Vec::new(),
            Unfolding::Unforced(GlobalIndex::from(0_u32)),
        )
        .expect("a declaration can unfold");
    let opaque = domain
        .neutral_node(NeutralHead::Constant(first), Vec::new(), Unfolding::Rigid)
        .expect("the same name can stand opaque");
    let mut frozen = Frozen::default();
    frozen.freeze(ConversionSide::Left, first);
    let once = frozen.clone();
    frozen.freeze(ConversionSide::Left, first);
    assert_eq!(once, frozen, "freezing is idempotent in the goal key");
    frozen.freeze(ConversionSide::Right, second);
    assert_eq!(
        super::Membership::Absent,
        frozen.holds(ConversionSide::Left, second)
    );
    assert_eq!(
        super::Membership::Held,
        frozen.holds(ConversionSide::Right, second)
    );
    assert_eq!(
        Ok(Head::Frozen(first)),
        super::head(&domain, &frozen, ConversionSide::Left, loaded)
    );
    assert_eq!(
        Ok(Head::Defined(first)),
        super::head(&domain, &frozen, ConversionSide::Right, loaded)
    );
    assert_eq!(
        Ok(Head::Rigid),
        super::head(&domain, &frozen, ConversionSide::Left, opaque)
    );
    let value = domain.value_unit(TermFace::Reduced);
    domain
        .force_neutral(loaded, Glued::Value(value))
        .expect("the face is initially unforced");
    assert_eq!(
        Ok(Head::Defined(first)),
        super::head(&domain, &frozen, ConversionSide::Right, loaded)
    );
    domain.truncate_to(floor);
    assert_eq!(
        Err(super::ConversionFault::Domain(super::DomainFault::Dangling)),
        super::head(&domain, &frozen, ConversionSide::Left, loaded)
    );
}

#[test]
fn payloads_refuse_nonliteral_and_missing_nodes()
{
    let mut core = CoreArena::new();
    let floor = core.watermark();
    let unit = core.value_unit();
    let literal = core.value_literal(Literal::Integer(IntegerLiteral::new(
        Sign::NonNegative,
        Magnitude::zero(),
    )));
    assert!(matches!(
        super::payload(&core, literal),
        Ok(Literal::Integer(_))
    ));
    assert_eq!(
        Err(super::ConversionFault::LiteralPayload { literal: unit }),
        super::payload(&core, unit)
    );
    core.truncate_to(floor);
    assert_eq!(
        Err(super::ConversionFault::LiteralPayload { literal }),
        super::payload(&core, literal)
    );
}

#[test]
fn opposite_polarities_are_refused_in_both_orders()
{
    let core = CoreArena::new();
    let mut domain = DomainArena::new();
    let value = domain.value_unit(TermFace::Reduced);
    let computation = domain.comp_return(value, crate::CompTermFace::Reduced);
    let chain = crate::LoweredChain::new();
    let environment = DefinitionalEnvironment::new();
    let definitions = crate::Definitions::new(&chain, &environment, environment.root());
    for (left, right) in [
        (Glued::Value(value), Glued::Computation(computation)),
        (Glued::Computation(computation), Glued::Value(value)),
    ] {
        assert_eq!(
            Err(super::ConversionFault::Polarity),
            super::plan(&core, &domain, definitions, &Frozen::default(), left, right)
        );
    }
}

#[test]
fn a_returned_endpoint_over_a_frozen_call_is_indeterminate_on_that_side()
{
    let mut domain = DomainArena::new();
    let constant = ConstantIndex::from(0_usize);
    let call = domain
        .neutral_node(
            NeutralHead::Constant(constant),
            Vec::new(),
            Unfolding::Unforced(GlobalIndex::from(0_u32)),
        )
        .expect("a declaration can unfold");
    let call = domain.comp_neutral(call, crate::CompTermFace::Reduced);
    let endpoint = domain
        .neutral_node(NeutralHead::Returned(call), Vec::new(), Unfolding::Rigid)
        .expect("a returned endpoint is rigid");
    let mut frozen = Frozen::default();
    frozen.freeze(ConversionSide::Left, constant);
    assert_eq!(
        Ok(Head::Indeterminate),
        super::head(&domain, &frozen, ConversionSide::Left, endpoint)
    );
    assert_eq!(
        Ok(Head::Endpoint(constant)),
        super::head(&domain, &frozen, ConversionSide::Right, endpoint)
    );
}

#[test]
fn a_defined_head_meets_its_frozen_twin_only_at_one_constant_and_arity()
{
    let mut core = CoreArena::new();
    let mut domain = DomainArena::new();
    let argument = literal_one(&mut core, &mut domain);
    let mut stuck = |constant: usize, spine: Vec<Elimination>| {
        let neutral = domain
            .neutral_node(
                NeutralHead::Constant(ConstantIndex::from(constant)),
                spine,
                Unfolding::Unforced(GlobalIndex::from(0_u32)),
            )
            .expect("a declaration can unfold");
        domain
            .value_neutral(neutral, TermFace::Reduced)
            .expect("a static spine stands as a value")
    };
    let defined = stuck(0, Vec::new());
    let twin = stuck(0, Vec::new());
    let other = stuck(1, Vec::new());
    let applied = stuck(0, Vec::from([Elimination::StaticApply(argument)]));
    for (frozen_side, defined_side) in [
        (ConversionSide::Right, ConversionSide::Left),
        (ConversionSide::Left, ConversionSide::Right),
    ] {
        let mut frozen = Frozen::default();
        frozen.freeze(frozen_side, ConstantIndex::from(0_usize));
        frozen.freeze(frozen_side, ConstantIndex::from(1_usize));
        let sides = |unfrozen, held| match defined_side {
            ConversionSide::Left => (unfrozen, held),
            ConversionSide::Right => (held, unfrozen),
        };
        for (unfrozen, held, expected) in [
            (
                defined,
                twin,
                Plan::Choose(Choice::Frozen {
                    defined: defined_side,
                }),
            ),
            (defined, other, Plan::Step(Step::Unfold(defined_side))),
            (applied, twin, Plan::Step(Step::Unfold(defined_side))),
        ] {
            let (left, right) = sides(unfrozen, held);
            assert_eq!(
                Ok(expected),
                planned(&core, &domain, &frozen, left, right),
                "defined on the {defined_side:?}"
            );
        }
    }
}

#[test]
fn each_former_decomposes_against_its_twin_at_another_id()
{
    let mut core = CoreArena::new();
    let mut domain = DomainArena::new();
    let part = thunk(&mut core, &mut domain);
    let unit = domain.value_unit(TermFace::Reduced);
    let unit_term = core.value_unit();
    let labelled = core.value_record(BTreeMap::from([(
        FieldLabel::from(String::from("x")),
        unit_term,
    )]));
    let record = |domain: &mut DomainArena| {
        let fields = domain.hold_fields([unit]);
        domain
            .value_record(labelled, fields, TermFace::Reduced)
            .expect("the fields are live")
    };
    let lift = |domain: &mut DomainArena| {
        let target = domain.hold_level(Level::zero());
        domain.value_lift(target, part, TermFace::Reduced)
    };
    let pairs = [
        ("a record", record(&mut domain), record(&mut domain), unit),
        (
            "a flow",
            domain.value_flow(FlowFormer::Then, [part], TermFace::Reduced),
            domain.value_flow(FlowFormer::Then, [part], TermFace::Reduced),
            part,
        ),
        (
            "an injection",
            domain.value_injection(Summand::from(1_usize), part, TermFace::Reduced),
            domain.value_injection(Summand::from(1_usize), part, TermFace::Reduced),
            part,
        ),
        ("a lift", lift(&mut domain), lift(&mut domain), part),
    ];
    for (former, left, right, inside) in pairs {
        assert_eq!(
            Ok(Plan::Decompose(Vec::from([super::Subgoal::Values(
                inside, inside
            )]))),
            planned(&core, &domain, &Frozen::default(), left, right),
            "{former} decomposes into its parts"
        );
    }
}

#[test]
fn two_flows_of_different_formers_are_planned_apart()
{
    let mut core = CoreArena::new();
    let mut domain = DomainArena::new();
    let part = thunk(&mut core, &mut domain);
    let then = domain.value_flow(FlowFormer::Then, [part, part], TermFace::Reduced);
    let product = domain.value_flow(FlowFormer::Product, [part, part], TermFace::Reduced);
    assert_eq!(
        Ok(Plan::Leaf(Settled::NotConvertible)),
        planned(&core, &domain, &Frozen::default(), then, product)
    );
}

#[test]
fn a_record_with_more_labels_than_fields_is_refused_by_the_plan_on_either_side()
{
    let mut core = CoreArena::new();
    let mut domain = DomainArena::new();
    let unit = domain.value_unit(TermFace::Reduced);
    let unit_term = core.value_unit();
    let narrow = core.value_record(BTreeMap::from([(
        FieldLabel::from(String::from("x")),
        unit_term,
    )]));
    let wide = core.value_record(BTreeMap::from([
        (FieldLabel::from(String::from("x")), unit_term),
        (FieldLabel::from(String::from("y")), unit_term),
    ]));
    let fields = domain.hold_fields([unit]);
    let formed = domain
        .value_record(narrow, fields, TermFace::Reduced)
        .expect("the fields are live");
    let fields = domain.hold_fields([unit]);
    let malformed = domain
        .value_record(wide, fields, TermFace::Reduced)
        .expect("the fields are live");
    for (left, right) in [(malformed, formed), (formed, malformed)] {
        assert_eq!(
            Err(super::ConversionFault::MachineInvariant),
            planned(&core, &domain, &Frozen::default(), left, right)
        );
    }
}

#[test]
fn two_path_products_of_one_path_share_a_convertible_plan()
{
    let core = CoreArena::new();
    let mut domain = DomainArena::new();
    let path = domain
        .neutral_node(
            NeutralHead::Variable {
                zone: gandr_core_term::Zone::Intuitionistic,
                level: crate::BinderLevel::from(0_u32),
            },
            Vec::new(),
            Unfolding::Rigid,
        )
        .expect("a variable is rigid");
    let path = domain
        .value_neutral(path, TermFace::Reduced)
        .expect("a spineless neutral stands as a value");
    let left = domain.value_path_product(path, path, TermFace::Reduced);
    let right = domain.value_path_product(path, path, TermFace::Reduced);
    assert_eq!(
        Ok(Plan::Shared(Settled::Convertible)),
        planned(&core, &domain, &Frozen::default(), left, right)
    );
}

#[test]
fn two_literals_held_apart_with_one_payload_are_convertible()
{
    let mut core = CoreArena::new();
    let mut domain = DomainArena::new();
    let one = literal_one(&mut core, &mut domain);
    let again = literal_one(&mut core, &mut domain);
    assert_eq!(
        Ok(Plan::Leaf(Settled::Convertible)),
        planned(&core, &domain, &Frozen::default(), one, again)
    );
}
