use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;

use gandr_core_term::ComponentCount;
use gandr_core_term::CoreArena;
use gandr_core_term::DataSignature;
use gandr_core_term::Sort;
use gandr_core_term::control::EffectClause;
use gandr_core_term::control::StackFrame;
use gandr_core_term::effect::EffectName;
use gandr_core_term::effect::EffectOp;
use gandr_core_term::effect::EffectRow;
use gandr_core_term::effect::EffectSig;
use gandr_core_term::effect::OperationName;
use gandr_core_term::effect::capability::CapabilityGrade;
use gandr_core_term::effect::capability::Region;
use gandr_core_term::effect::capability::RegionDepth;
use gandr_core_term::hole::MarkIndex;
use gandr_core_term::memory::HoldGrade;
use gandr_core_term::memory::MemoryForm;
use gandr_core_term::session::RecordedMove;
use gandr_core_term::session::SessionAction;
use gandr_core_term::session::SessionRelation;
use gandr_core_term::world::World;
use gandr_core_term::world::WorldForm;
use gandr_core_term::world::WorldType;
use gandr_kernel_strata::Level;
use gandr_kernel_term::Component;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldCount;
use gandr_kernel_term::FieldLabel;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::PathEvidence;
use gandr_kernel_term::Stage;
use gandr_kernel_term::StageId;
use gandr_kernel_term::Summand;

use super::reach;

/// A declaration at position 0 whose one field names position 7 inside
/// every former the walk descends — a type former, a term inside a decoded
/// code, a computation inside a thunk — reaches one past 7: the walk finds a
/// later position wherever it stands, so no former hides a block member.
#[test]
fn a_later_position_extends_the_block_through_every_former()
{
    let mut arena = CoreArena::new();
    let universe = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let unit = arena.value_type_unit();
    let nothing = arena.value_unit();
    let later = arena.value_constant(ConstantIndex::from(7_usize));
    let later_type = arena.value_type_data(ConstantIndex::from(7_usize), Vec::new());
    let returns_later = arena.comp_type_returner(later_type);
    let returns_unit = arena.comp_type_returner(unit);
    let reads = arena.computation_return(later);
    let finishes = arena.computation_return(nothing);
    let label = || FieldLabel::from(String::from("x"));
    let values = [
        arena.value_record(BTreeMap::from([(label(), later)])),
        arena.value_tuple(&[nothing, later]),
        arena.value_path_product(nothing, later),
        arena.value_funext(later, nothing),
        arena.value_equiv(nothing, later),
        arena.value_univalence(later, nothing),
        arena.value_then(nothing, later),
        arena.value_flow_product(later, nothing),
        arena.value_function_flow(nothing, later),
        arena.value_list_cons(later, nothing),
        arena.value_static_application(nothing, later),
        arena.value_reify(Arc::from([StackFrame::Apply(later)])),
        arena.value_reify(Arc::from([StackFrame::Bind(reads)])),
        arena.value_path_refl(later),
        arena.value_here(later),
        arena.value_stay(later),
        arena.value_forward(later),
        arena.value_injection(Summand::from(0_usize), later),
        arena.value_lift(Level::zero(), later),
        arena.value_static_lambda(later),
        arena.value_mark(MarkIndex::from(0_u32), later),
        arena.value_returned(reads),
        arena.value_nested(reads),
        arena.value_run(reads),
        arena.value_quote(later_type),
        arena.value_quote_computation(returns_later),
        arena.value_constructor(later_type, ConstructorTag::from(0_usize), Vec::new()),
        arena.value_constructor(unit, ConstructorTag::from(0_usize), Vec::from([later])),
        arena.value_path_equiv(
            later_type,
            nothing,
            nothing,
            Arc::new(PathEvidence {
                source: Vec::new(),
                target: Vec::new(),
            }),
        ),
        arena.value_path_equiv(
            unit,
            later,
            nothing,
            Arc::new(PathEvidence {
                source: Vec::new(),
                target: Vec::new(),
            }),
        ),
        arena.value_recorded(Arc::from([RecordedMove::Sent(later), RecordedMove::Closed])),
        arena.value_session_related(SessionRelation::Equivalence, nothing, later),
    ];
    let pair = ComponentCount::from(2_usize);
    let computations = [
        arena.computation_data_case(
            later,
            returns_unit,
            Vec::from([finishes]),
            Vec::from([FieldCount::from(0_usize)]),
        ),
        arena.computation_data_case(
            nothing,
            returns_later,
            Vec::from([finishes]),
            Vec::from([FieldCount::from(0_usize)]),
        ),
        arena.computation_record_projection(later, label()),
        arena.computation_tuple_projection(later, Component::from(0_usize)),
        arena.computation_abandon(later),
        arena.computation_force(later),
        arena.computation_lambda(reads),
        arena.computation_mark(MarkIndex::from(0_u32), reads),
        arena.computation_reset(reads),
        arena.computation_shift(reads),
        arena.computation_project(Component::from(0_usize), reads),
        arena.computation_with(&[finishes, reads]),
        arena.computation_ascribe(finishes, returns_later),
        arena.computation_resume(later, finishes),
        arena.computation_split(nothing, pair, reads),
        arena.computation_list_fold(later_type, unit, nothing, finishes, finishes),
        arena.computation_list_case(nothing, finishes, reads),
        arena.computation_application(finishes, later),
        arena.computation_bind(finishes, reads),
        arena.computation_case(nothing, &[finishes, reads]),
        arena.computation_transport(nothing, later),
        arena.computation_path_transport(later_type, nothing, nothing),
        arena.computation_ride(unit, nothing, later),
        arena.computation_telescope_transport(returns_later, nothing, nothing, nothing, nothing),
        arena.computation_world(WorldForm::Hold { value: later }),
        arena.computation_world(WorldForm::Leta {
            value: nothing,
            body: reads,
        }),
        arena.computation_world(WorldForm::Migrate {
            world: World::Host,
            body: reads,
        }),
    ];
    let signature = |payload| {
        EffectSig::new(EffectName::from("Probe"), [EffectOp {
            name: OperationName::from("poke"),
            payload,
            reply: payload,
        }])
        .expect("one operation")
    };
    let plain = signature(unit);
    let naming = signature(later_type);
    let poking = |body| -> Arc<[EffectClause]> {
        Arc::from([EffectClause {
            operation: OperationName::from("poke"),
            body,
        }])
    };
    let effects = [
        arena.computation_perform(naming.clone(), OperationName::from("poke"), nothing),
        arena.computation_perform(plain.clone(), OperationName::from("poke"), later),
        arena.computation_exercise(later, plain.clone(), OperationName::from("poke"), nothing),
        arena.computation_exercise(
            nothing,
            naming.clone(),
            OperationName::from("poke"),
            nothing,
        ),
        arena.computation_handle(plain.clone(), reads, finishes, poking(finishes)),
        arena.computation_handle(plain.clone(), finishes, finishes, poking(reads)),
        arena.computation_handle(naming.clone(), finishes, finishes, poking(finishes)),
        arena.computation_scope(plain, finishes, reads, poking(finishes)),
        arena.computation_scope(naming.clone(), finishes, finishes, poking(finishes)),
        arena.computation_session(SessionAction::Send {
            endpoint: DeBruijnIndex::from(0_u32),
            payload: later,
        }),
        arena.computation_session(SessionAction::Receive {
            endpoint: DeBruijnIndex::from(0_u32),
            body: reads,
        }),
        arena.computation_memory(MemoryForm::Hold {
            value: later,
            body: finishes,
            grade: HoldGrade::One,
        }),
        arena.computation_memory(MemoryForm::Hold {
            value: nothing,
            body: reads,
            grade: HoldGrade::Many,
        }),
    ];
    let effectful = arena.comp_type_returner_with_effects(unit, EffectRow::singleton(naming));
    let decode = |arena: &mut CoreArena, code| arena.value_type_element(code, Level::zero());
    let mut fields = Vec::from([
        arena.value_type_path(later_type, nothing, nothing),
        arena.value_type_path_universe(nothing, later),
        arena.value_type_flow(later_type, nothing, nothing),
        arena.value_type_run(later),
        arena.value_type_list(later_type),
        arena.value_type_stack(returns_later, returns_unit),
        arena.value_type_stack(returns_unit, returns_later),
        arena.value_type_sum(&[unit, later_type]),
        arena.value_type_product(&[unit, later_type]),
        arena.value_type_record(BTreeMap::from([(label(), later_type)])),
        arena.value_type_sigma(unit, later_type),
        arena.value_type_static_pi(later_type, unit),
        arena.value_type_lift(later_type, Level::zero()),
        arena.value_type_staged(later_type, Stage::At(StageId::from(0_usize))),
        arena.value_type_world(WorldType::At {
            inner: later_type,
            world: World::Host,
        }),
        arena.value_type_kept(later_type, Region::Scoped(RegionDepth::from(1_u32))),
        arena.value_type_capability(
            EffectRow::singleton(signature(later_type)),
            CapabilityGrade::Durable,
            Region::Scoped(RegionDepth::from(1_u32)),
        ),
    ]);
    let computation_types = [
        arena.comp_type_arrow(later_type, returns_unit),
        arena.comp_type_pi(unit, returns_later),
        arena.comp_type_with(&[returns_unit, returns_later]),
        arena.comp_type_element(later, Level::zero()),
        arena.comp_type_codata(ConstantIndex::from(7_usize), Vec::new()),
        arena.comp_type_codata(ConstantIndex::from(0_usize), Vec::from([later])),
        effectful,
    ];
    for ty in computation_types {
        fields.push(arena.value_type_thunk(ty));
    }
    for value in values {
        fields.push(decode(&mut arena, value));
    }
    for computation in computations.into_iter().chain(effects) {
        let thunk = arena.value_thunk(computation);
        fields.push(decode(&mut arena, thunk));
    }
    let measured = |arena: &CoreArena, field| {
        let signature = DataSignature::new(Vec::new(), Vec::from([Vec::from([field])]), universe);
        reach(arena, ConstantIndex::from(0_usize), &signature)
    };
    assert_eq!(
        measured(&arena, unit),
        ConstantIndex::from(1_usize),
        "a field naming nothing later reaches one past the declaration"
    );
    for (at, field) in fields.into_iter().enumerate() {
        assert_eq!(
            measured(&arena, field),
            ConstantIndex::from(8_usize),
            "field {at}: {:?}",
            arena.value_type(field)
        );
    }
}

/// A session's payload is sent as well as received, so a family it names
/// stands where no stage reaches and is refused at the field; a payload
/// naming nothing of the block is admitted.
#[test]
fn a_family_named_by_a_session_payload_is_refused_at_its_field()
{
    use gandr_core_term::session::PayloadCount;
    use gandr_core_term::session::PayloadSlot;
    use gandr_core_term::session::Protocol;
    use gandr_core_term::session::ProtocolState;
    use gandr_core_term::session::ProtocolSyntax;
    use gandr_core_term::session::SessionType;

    use super::Accessibility;
    use super::Block;
    use super::occurrences;

    let mut arena = CoreArena::new();
    let universe = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let own = arena.value_type_data(ConstantIndex::from(0_usize), Vec::new());
    let unit = arena.value_type_unit();
    // `?P. end`
    let protocol = Protocol::new(
        alloc::vec![
            ProtocolSyntax::Receive {
                payload: PayloadSlot::from(0_usize),
                next: ProtocolState::from(1_usize),
            },
            ProtocolSyntax::End,
        ],
        ProtocolState::from(0_usize),
        PayloadCount::from(1_usize),
    )
    .expect("the protocol is well formed");
    let protocol = Arc::new(protocol);
    let mut receiving = |payload| {
        let session = SessionType::new(Arc::clone(&protocol), Arc::from([payload]))
            .expect("one payload for one slot");
        arena.value_type_session(session)
    };
    let naming = receiving(own);
    let plain = receiving(unit);
    let earlier: BTreeMap<ConstantIndex, Accessibility> = BTreeMap::new();
    let block = Block::lone(ConstantIndex::from(0_usize));
    let declared =
        |field| DataSignature::new(Vec::new(), alloc::vec![alloc::vec![field]], universe);
    assert!(
        occurrences(&arena, (&block, &[], &earlier), &declared(plain)).is_ok(),
        "a payload naming nothing of the block is admitted"
    );
    let refused = occurrences(&arena, (&block, &[], &earlier), &declared(naming));
    assert!(
        matches!(
            refused,
            Err(crate::refusal::CheckRefusal::NegativeOccurrence(
                gandr_kernel_term::OccurrenceSite::Field { tag, field }
            )) if usize::from(tag) == 0 && usize::from(field) == 0
        ),
        "a payload naming the family is refused at its field: {refused:?}"
    );
}
