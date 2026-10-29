use alloc::vec::Vec;
use core::convert::Infallible;

use anodized::spec;
use gandr_core_term::CompType;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::DefinitionChain;
use gandr_core_term::DefinitionalEnvironment;
use gandr_core_term::Transparency;
use gandr_core_term::Value;
use gandr_core_term::ValueType;
use gandr_core_term::Zone;
use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::GlobalIndex;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Side;
use gandr_kernel_term::Sign;

use super::OpenBinders;
use super::ReadbackFault;
use super::ReadbackMode;
use super::ZoneDepth;
use super::read_comp_under;
use super::read_value_under;
use super::readback_computation;
use super::readback_value;
use crate::arena::DomainArena;
use crate::arena::DomainCompId;
use crate::arena::DomainFault;
use crate::closure::Environment;
use crate::domain::BinderLevel;
use crate::domain::CompTermFace;
use crate::domain::DomainComp;
use crate::domain::DomainValue;
use crate::domain::Elimination;
use crate::domain::Glued;
use crate::domain::NeutralHead;
use crate::domain::TermFace;
use crate::domain::Unfolding;
use crate::eval::Definitions;
use crate::eval::EvalFault;
use crate::eval::Fuel;
use crate::eval::LoweredChain;
use crate::eval::eval_computation;
use crate::eval::eval_value;

/// Ample fuel for every case that is meant to finish.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a budget far above the step count any fixture below needs, so an
///   exhaustion refusal in one of them is a defect rather than a tight budget.
/// - provides: the budget every finishing case is run with; the
///   budget-sensitive cases name their own.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — finishing fixtures must fit while the independent budget
///   search finds strictly smaller successful boundaries; an exhausted default
///   would turn their structural observations into refusals.
/// - witness: `readback::tests::one_budget_bounds_the_readback_and_the_evaluations_it_drives`
/// - witness: `readback::tests::a_readback_declines_on_fuel_rather_than_running_on`
#[spec(
        ensures: |ret| u32::from(ret) >= BUDGET_CEILING,
    )]
fn ample() -> Fuel
{
    Fuel::from(4_096_u32)
}

/// The index at the innermost binder.
///
/// # Specification
/// trivial.
fn innermost() -> DeBruijnIndex
{
    DeBruijnIndex::from(0_u32)
}

/// An empty chain and environment, which unfold nothing.
///
/// # Specification
/// - requires: nothing.
/// - ensures: an empty chain and an empty definitional environment, so every
///   constant reads as not manifest and no run unfolds.
/// - provides: the definition side of every fixture that is about rebuilding
///   rather than unfolding.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the empty lowering refuses a named unforced body, whereas
///   a populated lowering unfolds it. Supplying a body from another fixture
///   changes that boundary.
/// - witness: `readback::tests::the_unfolding_mode_refuses_a_body_no_chain_entry_names`
/// - witness: `readback::tests::a_lowered_definition_body_unfolds_through_readback`
#[spec(
        ensures: |ret| ret.0.chain().entries().is_empty() && ret.0.bodies().is_empty(),
    )]
fn nothing_unfolds() -> (LoweredChain, DefinitionalEnvironment)
{
    (LoweredChain::new(), DefinitionalEnvironment::new())
}

/// The number of bind links in the body each suspension of the
/// shared-budget witness holds.
///
/// It is the structural bound that witness measures against: the machine
/// spends one unit of fuel per task and the body has this many bind nodes
/// to visit, so evaluating it cannot cost fewer units than this under
/// any accounting. Large enough that the handful of tasks one extra
/// suspension costs the readback's *own* stack cannot be mistaken for
/// it.
const SUSPENDED_LINKS: u32 = 32_u32;

/// A budget no case here needs, bounding the search for the least
/// sufficient one so a machine that never finishes fails the search rather
/// than running forever.
const BUDGET_CEILING: u32 = 4_096_u32;

/// `x ← …; return ⟨⟩` nested [`SUSPENDED_LINKS`] deep: a body whose
/// evaluation visits at least that many nodes and whose weak head is one
/// returner, so what it costs is large and what it produces is small.
///
/// # Specification
/// - requires: `core` is the arena the returned id will be read against.
/// - ensures: a computation whose weak head is one returner and whose
///   evaluation visits at least [`SUSPENDED_LINKS`] bind nodes, so its cost is
///   large while its result is small.
/// - provides: the body the shared-budget witness measures a suspension's cost
///   against.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a second suspension increases the least sufficient budget
///   by at least the declared bind-chain depth. Omitting links, returning a
///   weak head without evaluating them, or failing to pass each bound value
///   onward breaks that observation.
/// - witness: `readback::tests::one_budget_bounds_the_readback_and_the_evaluations_it_drives`
#[spec(
        ensures: |ret| matches!(core.computation(ret), Some(&Computation::Bind(_, pass_on))
            if matches!(core.computation(pass_on), Some(&Computation::Return(occurrence))
                if core.value(occurrence) == Some(&Value::Variable { zone: Zone::Intuitionistic, index: DeBruijnIndex::from(0_u32) }))),
    )]
fn suspended_body(core: &mut CoreArena) -> ComputationId
{
    let produced = core.value_unit();
    let mut sequenced = core.computation_return(produced);
    let occurrence = core.value_variable(Zone::Intuitionistic, innermost());
    let pass_on = core.computation_return(occurrence);
    let mut remaining = SUSPENDED_LINKS;
    while remaining > 0_u32 {
        sequenced = core.computation_bind(sequenced, pass_on);
        remaining = remaining.saturating_sub(1_u32);
    }
    sequenced
}

/// Read `evaluated` back at `fuel` in an independent domain copy,
/// discarding every core node the readback minted.
///
/// Core truncation alone does not undo a neutral's forced unfolding face.
/// Each attempt therefore owns its domain, so a failed attempt cannot pay
/// for a later one by leaving a forced definition behind.
///
/// # Specification
/// - requires: `core` and `domain` are the arenas `evaluated` was produced
///   against, and no core id minted after the entry mark is retained by the
///   caller.
/// - ensures: on success the readback ran to completion at `fuel`; either way
///   `core` returns to its entry mark and `domain` is untouched, including its
///   unfolding faces. Attempts start from the same state.
/// - provides: the repeatable single attempt the budget search below is built
///   from.
/// - fails: propagates the readback's own refusal unchanged, the exhaustion one
///   included, which is what the search reads as "not yet sufficient".
/// - panics: none.
///
/// [`CoreArena::truncate_to`]: gandr_core_term::CoreArena::truncate_to
///
/// # Adequacy
/// - hypothesis: L3 — direct and nested fuel refusals retain their exact
///   variants. A partially forced definition must not subsidize the next
///   attempt: the reported minimum succeeds from the original domain and its
///   predecessor refuses. Each attempt owns a domain clone; its forcing cache
///   cannot escape.
/// - witness: `readback::tests::one_budget_bounds_the_readback_and_the_evaluations_it_drives`
/// - witness: `readback::tests::budget_search_does_not_reuse_forcing_from_failed_attempts`
#[spec(
        captures: [entry_mark = core.watermark()],
        ensures: core.watermark() == entry_mark,
    )]
fn read_at(
    core: &mut CoreArena,
    domain: &DomainArena,
    definitions: Definitions<'_>,
    evaluated: DomainCompId,
    fuel: Fuel,
) -> Result<(), ReadbackFault>
{
    let mark = core.watermark();
    let mut attempt = domain.clone();
    let read = readback_computation(
        core,
        &mut attempt,
        definitions,
        ReadbackMode::Unfolding,
        fuel,
        evaluated,
    );
    core.truncate_to(mark);
    read.map(|_| ())
}

/// The least budget at which reading `evaluated` back succeeds, or `None`
/// when [`BUDGET_CEILING`] does not suffice.
///
/// Each attempt starts with the same domain, including its forcing cache.
/// Fuel only gates this deterministic run, so its first success is minimal.
///
/// # Specification
/// - requires: `core` and `domain` are the arenas `evaluated` was produced
///   against.
/// - ensures: the least budget at which the readback succeeds, and nothing when
///   no budget at or below [`BUDGET_CEILING`] does. The first success is the
///   least one for the monotonicity the paragraph above states.
/// - provides: the measured cost the shared-budget witnesses compare.
/// - fails: yields nothing at the ceiling, so a machine that never finishes
///   fails the search rather than running forever.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the first successful budget is checked in an independent
///   domain, and one less is refused. Warming a definition during an earlier
///   failed attempt or returning a later success changes that boundary. The
///   fixed ceiling bounds a permanently refusing search.
/// - witness: `readback::tests::budget_search_does_not_reuse_forcing_from_failed_attempts`
/// - witness: `readback::tests::one_budget_bounds_the_readback_and_the_evaluations_it_drives`
#[spec(
        captures: [entry_mark = core.watermark()],
        ensures: |ret| core.watermark() == entry_mark
            && ret.is_none_or(|fuel| u32::from(fuel) > 0_u32 && u32::from(fuel) <= BUDGET_CEILING),
    )]
fn least_sufficient(
    core: &mut CoreArena,
    domain: &DomainArena,
    definitions: Definitions<'_>,
    evaluated: DomainCompId,
) -> Option<Fuel>
{
    let mut budget = 1_u32;
    while budget <= BUDGET_CEILING {
        let fuel = Fuel::from(budget);
        if read_at(core, domain, definitions, evaluated, fuel).is_ok() {
            return Some(fuel);
        }
        budget = budget.saturating_add(1_u32);
    }
    None
}

/// One binder open in the intuitionistic zone.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one binder open in the intuitionistic zone and none in the linear
///   one.
/// - provides: the under-a-binder position the level and index fixtures below
///   are read at.
/// - panics: never in practice — the first binder of a zone is far below the
///   depth ceiling, and the expectation names that reason.
///
/// # Adequacy
/// - hypothesis: L3 — the first intuitionistic level resolves here and does not
///   resolve with no binder open. Opening the linear zone or starting at the
///   wrong depth changes its index.
/// - witness: `readback::tests::a_level_becomes_the_index_counting_the_other_way`
/// - witness: `readback::tests::a_level_outside_the_open_binders_is_refused`
#[spec(
        ensures: |ret| ret.intuitionistic.0 == 1_u32 && ret.linear.0 == 0_u32,
    )]
fn under_one() -> OpenBinders
{
    OpenBinders::none()
        .opened(Zone::Intuitionistic)
        .expect("the first binder is far below the ceiling")
}

#[test]
fn opening_a_binder_counts_one_zone_and_leaves_the_other()
{
    let none = OpenBinders::none();
    assert_eq!(
        BinderLevel::from(0_u32),
        none.fresh(Zone::Intuitionistic),
        "the first binder of a zone takes level zero"
    );

    let structural = under_one();
    assert_eq!(
        BinderLevel::from(1_u32),
        structural.fresh(Zone::Intuitionistic),
        "the next binder of that zone takes the level after it"
    );
    assert_eq!(
        BinderLevel::from(0_u32),
        structural.fresh(Zone::Linear),
        "and the other zone is untouched, because the zones count separately"
    );

    let linear = none
        .opened(Zone::Linear)
        .expect("the first linear binder is far below the ceiling");
    assert_eq!(
        BinderLevel::from(0_u32),
        linear.fresh(Zone::Intuitionistic),
        "extending one zone did not deepen the other"
    );
    assert_eq!(BinderLevel::from(1_u32), linear.fresh(Zone::Linear));
}

#[test]
fn the_binder_ceiling_is_refused_rather_than_reused()
{
    let ceiling = OpenBinders {
        intuitionistic: ZoneDepth(u32::MAX),
        linear: ZoneDepth::default(),
    };
    assert_eq!(
        None,
        ceiling.opened(Zone::Intuitionistic),
        "a zone at the level ceiling cannot open another binder"
    );
    assert!(
        ceiling.opened(Zone::Linear).is_some(),
        "while the zone that is not at the ceiling still has room"
    );

    let mut core = CoreArena::new();
    let produced = core.value_unit();
    let body = core.computation_return(produced);
    let lambda = core.computation_lambda(body);

    let (chain, environment) = nothing_unfolds();
    let scope = environment.root();
    let definitions = Definitions::new(&chain, &environment, scope);
    let mut domain = DomainArena::new();
    let evaluated = eval_computation(&core, &mut domain, definitions, ample(), lambda)
        .expect("a lambda is already a weak head");
    assert_eq!(
        Err(ReadbackFault::BinderCeiling {
            zone: Zone::Intuitionistic,
        }),
        read_comp_under(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::Unfolding,
            ample(),
            evaluated,
            ceiling,
        ),
        "and a lambda opened at the ceiling is refused rather than binding a second \
             variable at the ceiling level"
    );
}

#[test]
fn a_level_becomes_the_index_counting_the_other_way()
{
    let two = under_one()
        .opened(Zone::Intuitionistic)
        .expect("the second binder is far below the ceiling");
    assert_eq!(
        Some(DeBruijnIndex::from(1_u32)),
        two.index(Zone::Intuitionistic, BinderLevel::from(0_u32)),
        "the outermost of two binders is one index out"
    );
    assert_eq!(
        Some(innermost()),
        two.index(Zone::Intuitionistic, BinderLevel::from(1_u32)),
        "and the innermost is index zero, so the two orders are inverses"
    );
    assert_eq!(
        None,
        two.index(Zone::Intuitionistic, BinderLevel::from(2_u32)),
        "the first level at the depth names no open binder"
    );
    assert_eq!(
        None,
        two.index(Zone::Intuitionistic, BinderLevel::from(3_u32)),
        "nor does one past it"
    );
    assert_eq!(
        None,
        two.index(Zone::Linear, BinderLevel::from(0_u32)),
        "and a zone with nothing open binds no level at all"
    );
}

#[test]
fn a_level_outside_the_open_binders_is_refused()
{
    let mut core = CoreArena::new();
    let (chain, environment) = nothing_unfolds();
    let scope = environment.root();
    let definitions = Definitions::new(&chain, &environment, scope);
    let mut domain = DomainArena::new();

    let level = BinderLevel::from(0_u32);
    let neutral = domain
        .neutral_node(
            NeutralHead::Variable {
                zone: Zone::Intuitionistic,
                level,
            },
            Vec::new(),
            Unfolding::Rigid,
        )
        .expect("a variable head mints rigid");
    let stood = domain
        .value_neutral(neutral, TermFace::Reduced)
        .expect("a spineless neutral stands in a value position");

    assert_eq!(
        Err(ReadbackFault::LevelOutOfScope {
            zone: Zone::Intuitionistic,
            level,
        }),
        readback_value(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::ZeroUnfold,
            ample(),
            stood,
        ),
        "with no binder open, level zero names nothing and is refused rather than wrapped"
    );

    let read = read_value_under(
        &mut core,
        &mut domain,
        definitions,
        ReadbackMode::ZeroUnfold,
        ample(),
        stood,
        under_one(),
    )
    .expect("one binder open answers level zero");
    assert_eq!(
        Some(&Value::Variable {
            zone: Zone::Intuitionistic,
            index: innermost(),
        }),
        core.value(read),
        "and there it is the innermost index"
    );
}

#[test]
fn an_unreduced_value_reads_back_as_its_own_source()
{
    let mut core = CoreArena::new();
    let first = core.value_unit();
    let second = core.value_unit();
    let pair = core.value_tuple(&[first, second]);

    let (chain, environment) = nothing_unfolds();
    let scope = environment.root();
    let definitions = Definitions::new(&chain, &environment, scope);
    let mut domain = DomainArena::new();
    let evaluated = eval_value(&core, &mut domain, definitions, ample(), pair)
        .expect("a closed pair of units evaluates");

    let mark = core.watermark();
    let read = readback_value(
        &mut core,
        &mut domain,
        definitions,
        ReadbackMode::ZeroUnfold,
        ample(),
        evaluated,
    )
    .expect("an unreduced pair reads back");
    assert_eq!(
        pair, read,
        "the face named the source node, so the readback answered with it"
    );
    assert_eq!(
        mark,
        core.watermark(),
        "and minted nothing, which is what reading back without rebuilding means"
    );
}

#[test]
fn an_unreduced_weak_head_reads_back_as_its_own_source()
{
    let mut core = CoreArena::new();
    let produced = core.value_unit();
    let returner = core.computation_return(produced);

    let (chain, environment) = nothing_unfolds();
    let scope = environment.root();
    let definitions = Definitions::new(&chain, &environment, scope);
    let mut domain = DomainArena::new();
    let evaluated = eval_computation(&core, &mut domain, definitions, ample(), returner)
        .expect("a closed returner evaluates");

    let mark = core.watermark();
    let read = readback_computation(
        &mut core,
        &mut domain,
        definitions,
        ReadbackMode::ZeroUnfold,
        ample(),
        evaluated,
    )
    .expect("an unreduced returner reads back");
    assert_eq!(
        returner, read,
        "the negative face is chosen the same way the positive one is"
    );
    assert_eq!(mark, core.watermark(), "and mints nothing either");
}

#[test]
fn a_reduced_value_is_rebuilt_from_the_domain()
{
    let mut core = CoreArena::new();
    let argument = core.value_unit();
    let held = core.value_unit();
    let bound = core.value_variable(Zone::Intuitionistic, innermost());
    let pair = core.value_tuple(&[bound, held]);
    let body = core.computation_return(pair);
    let lambda = core.computation_lambda(body);
    let redex = core.computation_application(lambda, argument);

    let (chain, environment) = nothing_unfolds();
    let scope = environment.root();
    let definitions = Definitions::new(&chain, &environment, scope);
    let mut domain = DomainArena::new();
    let evaluated =
        eval_computation(&core, &mut domain, definitions, ample(), redex).expect("the redex fires");
    let Some(&DomainComp::Return { value, .. }) = domain.computation(evaluated)
    else {
        panic!("the weak head is a returner");
    };

    let read = readback_value(
        &mut core,
        &mut domain,
        definitions,
        ReadbackMode::ZeroUnfold,
        ample(),
        value,
    )
    .expect("a substituted pair reads back");
    assert_eq!(
        Some(&Value::Tuple([argument, held].into())),
        core.value(read),
        "with the substituted child spliced by the id it denotes and the untouched child \
             by its own — in that order, so the assembly frame did not swap its operands"
    );
}

#[test]
fn native_lists_and_folds_read_back_without_sum_encoding()
{
    let mut core = CoreArena::new();
    let element = core.value_type_unit();
    let result = core.value_type_list(element);
    let nil = core.value_list_nil();
    let first = core.value_constant(ConstantIndex::from(0_usize));
    let second = core.value_constant(ConstantIndex::from(1_usize));
    let tail = core.value_list_cons(second, nil);
    let list = core.value_list_cons(first, tail);
    let head = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let folded = core.value_variable(Zone::Intuitionistic, innermost());
    let cell = core.value_list_cons(head, folded);
    let on_nil = core.computation_return(nil);
    let on_cons = core.computation_return(cell);
    let (chain, environment) = nothing_unfolds();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    for mode in [ReadbackMode::ZeroUnfold, ReadbackMode::Unfolding] {
        let mut domain = DomainArena::new();
        let empty = core.computation_list_fold(element, result, nil, on_nil, on_cons);
        let evaluated = eval_computation(&core, &mut domain, definitions, ample(), empty)
            .expect("empty fold evaluates");
        let read = readback_computation(
            &mut core,
            &mut domain,
            definitions,
            mode,
            ample(),
            evaluated,
        )
        .expect("empty fold reads back");
        assert!(
            matches!(core.computation(read), Some(&Computation::Return(value)) if matches!(core.value(value), Some(Value::ListNil)))
        );
        let full = core.computation_list_fold(element, result, list, on_nil, on_cons);
        let evaluated = eval_computation(&core, &mut domain, definitions, ample(), full)
            .expect("cell fold evaluates");
        let read = readback_computation(
            &mut core,
            &mut domain,
            definitions,
            mode,
            ample(),
            evaluated,
        )
        .expect("cell fold reads back");
        let Some(&Computation::Return(value)) = core.computation(read)
        else {
            panic!("fold returns a list");
        };
        let Some(&Value::ListCons(first, tail)) = core.value(value)
        else {
            panic!("first native cell");
        };
        let Some(&Value::ListCons(second, nil)) = core.value(tail)
        else {
            panic!("second native cell");
        };
        assert_eq!(
            core.value(first),
            Some(&Value::Constant(ConstantIndex::from(0_usize)))
        );
        assert_eq!(
            core.value(second),
            Some(&Value::Constant(ConstantIndex::from(1_usize)))
        );
        assert_eq!(core.value(nil), Some(&Value::ListNil));

        let outer = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(2_u32));
        let tail = core.value_list_cons(outer, folded);
        let cell = core.value_list_cons(head, tail);
        let captured_cons = core.computation_return(cell);
        let stuck = core.computation_list_fold(element, result, first, on_nil, captured_cons);
        let function = core.computation_lambda(stuck);
        let unit = core.value_unit();
        let applied = core.computation_application(function, unit);
        let evaluated = eval_computation(&core, &mut domain, definitions, ample(), applied)
            .expect("neutral fold captures outer argument");
        let read = readback_computation(
            &mut core,
            &mut domain,
            definitions,
            mode,
            ample(),
            evaluated,
        )
        .expect("neutral fold reads both local binders");
        let Some(&Computation::ListFold { on_cons, .. }) = core.computation(read)
        else {
            panic!("native fold remains neutral");
        };
        let Some(&Computation::Return(cell)) = core.computation(on_cons)
        else {
            panic!("cell branch returns");
        };
        let Some(&Value::ListCons(head, tail)) = core.value(cell)
        else {
            panic!("cell retains head");
        };
        let Some(&Value::ListCons(captured, folded)) = core.value(tail)
        else {
            panic!("cell retains capture and folded tail");
        };
        assert_eq!(
            core.value(head),
            Some(&Value::Variable {
                zone: Zone::Intuitionistic,
                index: DeBruijnIndex::from(1_u32)
            })
        );
        assert_eq!(
            core.value(folded),
            Some(&Value::Variable {
                zone: Zone::Intuitionistic,
                index: innermost()
            })
        );
        assert_eq!(core.value(captured), Some(&Value::unit()));
    }
}

#[test]
fn the_unfolding_mode_rebuilds_a_kept_face()
{
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let produced = core.computation_return(unit);
    let occurrence = core.value_variable(Zone::Intuitionistic, innermost());
    let continued = core.computation_return(occurrence);
    let redex = core.computation_bind(produced, continued);
    let suspended = core.value_thunk(redex);
    let returner = core.computation_return(suspended);
    let (chain, environment) = nothing_unfolds();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let mut domain = DomainArena::new();
    let evaluated = eval_computation(&core, &mut domain, definitions, ample(), returner)
        .expect("the suspended redex is not evaluated yet");
    assert_eq!(
        Ok(returner),
        readback_computation(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::ZeroUnfold,
            ample(),
            evaluated
        )
    );
    let read = readback_computation(
        &mut core,
        &mut domain,
        definitions,
        ReadbackMode::Unfolding,
        ample(),
        evaluated,
    )
    .expect("the rebuilding mode enters the suspension");
    let Some(&Computation::Return(rebuilt)) = core.computation(read)
    else {
        panic!("the outer returner remains");
    };
    let Some(&Value::Thunk(body)) = core.value(rebuilt)
    else {
        panic!("its result remains suspended");
    };
    let Some(&Computation::Return(value)) = core.computation(body)
    else {
        panic!("the redex beneath both kept faces must normalize");
    };
    assert_eq!(Some(&Value::unit()), core.value(value));
}

#[test]
fn the_leaf_and_lift_arms_read_back_into_the_core_arena()
{
    let mut core = CoreArena::new();
    let literal = core.value_literal(Literal::Integer(IntegerLiteral::new(
        Sign::NonNegative,
        Magnitude::zero(),
    )));
    let lifted = core.value_unit();
    let target = Level::zero().succ().expect("level one exists");
    let lift = core.value_lift(target.clone(), lifted);
    let pair = core.value_tuple(&[literal, lift]);

    let (chain, environment) = nothing_unfolds();
    let scope = environment.root();
    let definitions = Definitions::new(&chain, &environment, scope);
    let mut domain = DomainArena::new();
    let evaluated = eval_value(&core, &mut domain, definitions, ample(), pair)
        .expect("a pair of a literal and a lift evaluates");

    let read = readback_value(
        &mut core,
        &mut domain,
        definitions,
        ReadbackMode::Unfolding,
        ample(),
        evaluated,
    )
    .expect("the leaf and lift arms read back");
    let Some(&[first, second]) = core.value(read).and_then(Value::components)
    else {
        panic!("the rebuilt value is a pair");
    };
    assert_eq!(
        literal, first,
        "the payload never left the core arena, so the literal arm splices the id \
             holding it rather than copying the payload out and back"
    );
    let Some(node) = core.value(second)
    else {
        panic!("the second component resolves");
    };
    let Value::Lift {
        target: ref held,
        body,
    } = *node
    else {
        panic!("the second component is a lift");
    };
    assert_eq!(
        &target, held,
        "the level came back out of the domain's own level table"
    );
    assert_eq!(
        Some(&Value::unit()),
        core.value(body),
        "and the lifted body was rebuilt under it"
    );
}

#[test]
fn a_pair_and_an_injection_rebuild_from_their_children()
{
    let mut core = CoreArena::new();
    let left_leaf = core.value_unit();
    let right_leaf = core.value_literal(Literal::Integer(IntegerLiteral::new(
        Sign::NonNegative,
        Magnitude::zero(),
    )));
    let pair = core.value_tuple(&[left_leaf, right_leaf]);
    let injected = core.value_injection(Side::Right.into(), pair);

    let (chain, environment) = nothing_unfolds();
    let scope = environment.root();
    let definitions = Definitions::new(&chain, &environment, scope);
    let mut domain = DomainArena::new();
    let evaluated = eval_value(&core, &mut domain, definitions, ample(), injected)
        .expect("an injection of a pair evaluates");

    let read = readback_value(
        &mut core,
        &mut domain,
        definitions,
        ReadbackMode::Unfolding,
        ample(),
        evaluated,
    )
    .expect("the composite arms read back");
    let Some(&Value::Injection(side, body)) = core.value(read)
    else {
        panic!("the rebuilt value is an injection");
    };
    assert_eq!(
        gandr_core_term::Summand::from(Side::Right),
        side,
        "the side rode through the frame rather than being defaulted"
    );
    let Some(&[first, second]) = core.value(body).and_then(Value::components)
    else {
        panic!("the injected value is a pair");
    };
    assert_eq!(
        Some(&Value::unit()),
        core.value(first),
        "the unit is the first component"
    );
    assert_eq!(
        right_leaf, second,
        "and the literal the second, so the pair frame kept its operands in order"
    );
}

#[test]
fn a_thunk_reads_back_through_the_body_it_suspends()
{
    let mut core = CoreArena::new();
    let produced = core.value_unit();
    let returner = core.computation_return(produced);
    let thunk = core.value_thunk(returner);

    let (chain, environment) = nothing_unfolds();
    let scope = environment.root();
    let definitions = Definitions::new(&chain, &environment, scope);
    let mut domain = DomainArena::new();
    let evaluated = eval_value(&core, &mut domain, definitions, ample(), thunk)
        .expect("a thunk over the empty environment evaluates");

    let retained = readback_value(
        &mut core,
        &mut domain,
        definitions,
        ReadbackMode::ZeroUnfold,
        ample(),
        evaluated,
    )
    .expect("the retaining mode reads the thunk back");
    assert_eq!(
        thunk, retained,
        "the closure captured nothing, so the source thunk still denotes it and the \
             suspended body is never entered"
    );

    let read = readback_value(
        &mut core,
        &mut domain,
        definitions,
        ReadbackMode::Unfolding,
        ample(),
        evaluated,
    )
    .expect("the rebuilding mode reads the thunk back");
    let Some(&Value::Thunk(body)) = core.value(read)
    else {
        panic!("the rebuilt value is a thunk");
    };
    let Some(&Computation::Return(rebuilt)) = core.computation(body)
    else {
        panic!("the suspended body is a returner");
    };
    assert_eq!(
        Some(&Value::unit()),
        core.value(rebuilt),
        "and the body it evaluated to came back as its own term"
    );
}

#[test]
fn a_lambda_reads_back_with_its_binder_as_an_index()
{
    let mut core = CoreArena::new();
    let occurrence = core.value_variable(Zone::Intuitionistic, innermost());
    let body = core.computation_return(occurrence);
    let lambda = core.computation_lambda(body);

    let (chain, environment) = nothing_unfolds();
    let scope = environment.root();
    let definitions = Definitions::new(&chain, &environment, scope);
    let mut domain = DomainArena::new();
    let evaluated = eval_computation(&core, &mut domain, definitions, ample(), lambda)
        .expect("a lambda is already a weak head");

    let read = readback_computation(
        &mut core,
        &mut domain,
        definitions,
        ReadbackMode::Unfolding,
        ample(),
        evaluated,
    )
    .expect("the rebuilding mode opens the binder");
    let Some(&Computation::Lambda(rebuilt)) = core.computation(read)
    else {
        panic!("the rebuilt weak head is a lambda");
    };
    let Some(&Computation::Return(produced)) = core.computation(rebuilt)
    else {
        panic!("the body is a returner");
    };
    assert_eq!(
        Some(&Value::Variable {
            zone: Zone::Intuitionistic,
            index: innermost(),
        }),
        core.value(produced),
        "the binder was opened at a level and the occurrence came back as the index \
             counting the other way"
    );
}

/// `λy. λz. split z as (a, b) in return (b, a, y)`: the stuck split reads
/// back over its scrutinee's index, its arity kept and its components
/// bound innermost, past the outer binders.
#[test]
fn a_stuck_split_reads_back_with_its_components_bound()
{
    use gandr_core_term::ComponentCount;
    let mut core = CoreArena::new();
    let variable = |core: &mut CoreArena, index: u32| {
        core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index))
    };
    let scrutinee = variable(&mut core, 0);
    let produced = [0, 1, 3].map(|index| variable(&mut core, index));
    let produced = core.value_tuple(&produced);
    let body = core.computation_return(produced);
    let split = core.computation_split(scrutinee, ComponentCount::from(2_usize), body);
    let inner = core.computation_lambda(split);
    let outer = core.computation_lambda(inner);
    let (chain, environment) = nothing_unfolds();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let mut domain = DomainArena::new();
    let evaluated = eval_computation(&core, &mut domain, definitions, ample(), outer)
        .expect("a lambda is already a weak head");
    let read = readback_computation(
        &mut core,
        &mut domain,
        definitions,
        ReadbackMode::Unfolding,
        ample(),
        evaluated,
    )
    .expect("both binders and the split's open");
    let Some(&Computation::Lambda(inner)) = core.computation(read)
    else {
        panic!("the outer lambda reads back");
    };
    let Some(&Computation::Lambda(split)) = core.computation(inner)
    else {
        panic!("the inner lambda reads back");
    };
    let Some(&Computation::Split {
        scrutinee,
        arity,
        motive: gandr_core_term::SplitMotive::Ambient,
        body,
    }) = core.computation(split)
    else {
        panic!("the stuck split reads back as an ambient split");
    };
    assert_eq!(arity, ComponentCount::from(2_usize));
    let index = |core: &CoreArena, value| match core.value(value) {
        Some(&Value::Variable {
            zone: Zone::Intuitionistic,
            index,
        }) => u32::from(index),
        _ => panic!("a variable reads back"),
    };
    assert_eq!(index(&core, scrutinee), 0);
    let Some(&Computation::Return(produced)) = core.computation(body)
    else {
        panic!("the body returns");
    };
    let Some(&[second, first, captured]) = core.value(produced).and_then(Value::components)
    else {
        panic!("the body's triple reads back");
    };
    assert_eq!(
        [
            index(&core, second),
            index(&core, first),
            index(&core, captured)
        ],
        [0, 1, 3]
    );
}

#[test]
fn a_fixpoint_reads_back_with_its_self_binder()
{
    // `(λy. fix rec. λx. return ⟨rec, y⟩) ()`: the fixpoint captures the
    // argument, and its self binder reads back past the inner lambda's.
    let mut core = CoreArena::new();
    let recursive = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let captured = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(2_u32));
    let pair = core.value_tuple(&[recursive, captured]);
    let returned = core.computation_return(pair);
    let inner = core.computation_lambda(returned);
    let partial = gandr_kernel_term::FixpointEvidence::Partial;
    let fixpoint = core.computation_fixpoint(inner, partial);
    let outer = core.computation_lambda(fixpoint);
    let unit = core.value_unit();
    let applied = core.computation_application(outer, unit);
    let expected_pair = core.value_tuple(&[recursive, unit]);
    let expected_return = core.computation_return(expected_pair);
    let expected_inner = core.computation_lambda(expected_return);
    let expected = core.computation_fixpoint(expected_inner, partial);
    let mislabelled = core.computation_fixpoint(
        expected_inner,
        gandr_kernel_term::FixpointEvidence::StructuralDescent,
    );

    let (chain, environment) = nothing_unfolds();
    let scope = environment.root();
    let definitions = Definitions::new(&chain, &environment, scope);
    let mut domain = DomainArena::new();
    let evaluated = eval_computation(&core, &mut domain, definitions, ample(), applied)
        .expect("the redex fires and leaves the fixpoint inert");
    assert!(
        matches!(
            domain.computation(evaluated),
            Some(&DomainComp::Fixpoint {
                face: CompTermFace::Reduced,
                ..
            })
        ),
        "the fixpoint captured a binding, so it no longer denotes its source"
    );
    let read = readback_computation(
        &mut core,
        &mut domain,
        definitions,
        ReadbackMode::Unfolding,
        ample(),
        evaluated,
    )
    .expect("the rebuilding mode opens the self binder");
    let read = core.value_thunk(read);
    let expected = core.value_thunk(expected);
    let mislabelled = core.value_thunk(mislabelled);
    assert_eq!(
        gandr_core_term::CertificateEquality::Equal,
        gandr_core_term::equal_certificate_syntax(&core, read, expected),
        "the self occurrence comes back as the index past the inner binder and the \
             captured argument as itself"
    );
    assert_eq!(
        gandr_core_term::CertificateEquality::Different,
        gandr_core_term::equal_certificate_syntax(&core, read, mislabelled),
        "and the evidence survives the round trip"
    );
}

#[test]
fn a_definition_s_own_recursion_reads_back_as_the_definition()
{
    // `pred := thunk (fix rec. λu. case u { Z => return Z; S(p) => force
    // rec · p })` run at `S(v)` for a free `v`, as the returned endpoint a
    // code's run reads: the run unfolds `pred`, takes the successor arm and
    // sticks at the recursion applied to `v`. Under the refolding stance
    // that call reads back as `force pred · v`, the call a source writes;
    // under the unrolling stance as the fixpoint itself applied to `v`.
    let mut core = CoreArena::new();
    let constant = ConstantIndex::from(0_usize);
    let nat = core.value_type_data(ConstantIndex::from(1_usize), Vec::new());
    let zero = core.value_constructor(nat, ConstructorTag::from(0_usize), Vec::new());
    let on_zero = core.computation_return(zero);
    let recursive = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(2_u32));
    let recursion = core.computation_force(recursive);
    let predecessor = core.value_variable(Zone::Intuitionistic, innermost());
    let recurse = core.computation_application(recursion, predecessor);
    let on_successor = core.computation_lambda(recurse);
    let scrutinee = core.value_variable(Zone::Intuitionistic, innermost());
    let motive = core.comp_type_returner(nat);
    let cases = core.computation_data_case(
        scrutinee,
        motive,
        Vec::from([on_zero, on_successor]),
        [0_usize, 1]
            .map(gandr_kernel_term::FieldCount::from)
            .to_vec(),
    );
    let lambda = core.computation_lambda(cases);
    let fixpoint = core.computation_fixpoint(
        lambda,
        gandr_kernel_term::FixpointEvidence::StructuralDescent,
    );
    let body = core.value_thunk(fixpoint);
    let named = core.value_constant(constant);
    let forced = core.computation_force(named);
    let free = core.value_variable(Zone::Intuitionistic, innermost());
    let successor = core.value_constructor(nat, ConstructorTag::from(1_usize), Vec::from([free]));
    let run = core.computation_application(forced, successor);
    let run = core.value_returned(run);
    let run = core.computation_return(run);
    let run = core.computation_lambda(run);
    let read_as = |core: &mut CoreArena, head: ComputationId| {
        let call = core.computation_application(head, free);
        let call = core.value_returned(call);
        let call = core.computation_return(call);
        core.computation_lambda(call)
    };
    let source_call = read_as(&mut core, forced);
    let unrolled_call = read_as(&mut core, fixpoint);

    let mut chain = DefinitionChain::new();
    let defined = chain.define(
        constant,
        GlobalIndex::from(0_u32),
        Transparency::Manifest,
        &[],
    );
    assert!(defined.is_ok());
    let environment = DefinitionalEnvironment::new();
    let chain = LoweredChain::lower(chain, |_| Ok::<_, Infallible>(body))
        .unwrap_or_else(|never| match never {});
    let definitions = Definitions::new(&chain, &environment, environment.root());

    for (recursion, expected) in [
        (crate::Recursion::Refolded, source_call),
        (crate::Recursion::Unrolled, unrolled_call),
    ] {
        let definitions = definitions.reading_recursion(recursion);
        let mut domain = DomainArena::new();
        let evaluated = eval_computation(&core, &mut domain, definitions, ample(), run)
            .expect("the run evaluates");
        let read = readback_computation(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::Unfolding,
            ample(),
            evaluated,
        )
        .expect("the run reads back");
        let read = core.value_thunk(read);
        let expected = core.value_thunk(expected);
        assert_eq!(
            gandr_core_term::CertificateEquality::Equal,
            gandr_core_term::equal_certificate_syntax(&core, read, expected),
            "under {recursion:?}"
        );
    }
}

#[test]
fn nested_binders_read_back_as_the_indices_that_name_them()
{
    let (chain, environment) = nothing_unfolds();
    let scope = environment.root();
    let definitions = Definitions::new(&chain, &environment, scope);

    for named in [0_u32, 1_u32] {
        let mut core = CoreArena::new();
        let occurrence = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(named));
        let body = core.computation_return(occurrence);
        let inner = core.computation_lambda(body);
        let outer = core.computation_lambda(inner);

        let mut domain = DomainArena::new();
        let evaluated = eval_computation(&core, &mut domain, definitions, ample(), outer)
            .expect("a lambda is already a weak head");
        let read = readback_computation(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::Unfolding,
            ample(),
            evaluated,
        )
        .expect("two binders open and close");

        let Some(&Computation::Lambda(under_outer)) = core.computation(read)
        else {
            panic!("the rebuilt weak head is a lambda");
        };
        let Some(&Computation::Lambda(under_inner)) = core.computation(under_outer)
        else {
            panic!("and so is its body");
        };
        let Some(&Computation::Return(produced)) = core.computation(under_inner)
        else {
            panic!("whose body is a returner");
        };
        assert_eq!(
            Some(&Value::Variable {
                zone: Zone::Intuitionistic,
                index: DeBruijnIndex::from(named),
            }),
            core.value(produced),
            "each binder came back as the index that named it, so the two levels did \
                 not collapse onto one"
        );
    }
}

#[test]
fn a_module_head_and_a_declaration_head_read_back_alike()
{
    let mut core = CoreArena::new();
    let (chain, environment) = nothing_unfolds();
    let scope = environment.root();
    let definitions = Definitions::new(&chain, &environment, scope);
    let mut domain = DomainArena::new();

    let position = ConstantIndex::from(2_usize);
    for head in [
        NeutralHead::Module(position),
        NeutralHead::Constant(position),
    ] {
        let neutral = domain
            .neutral_node(head, Vec::new(), Unfolding::Rigid)
            .expect("a rigid head mints without a body");
        let stood = domain
            .value_neutral(neutral, TermFace::Reduced)
            .expect("a spineless neutral stands in a value position");
        let read = readback_value(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::ZeroUnfold,
            ample(),
            stood,
        )
        .expect("a rigid head reads back");
        assert_eq!(
            Some(&Value::Constant(position)),
            core.value(read),
            "the core value vocabulary has one reference former, and one admission \
                 position admits one declaration, so the collapse loses nothing"
        );
    }
}

/// A native call stands on its operation, closed literals included, and reads
/// back as the operation's thunk forced and applied to its arguments in order:
/// the normaliser runs no native operation (#2378).
#[test]
fn a_primitive_head_reads_back_as_its_thunk_2378()
{
    use gandr_core_term::primitive::Arguments;
    use gandr_core_term::primitive::PRELUDE;
    let mut core = CoreArena::new();
    let int_eq = PRELUDE
        .iter()
        .copied()
        .find(|primitive| primitive.name().as_ref() == "int.eq")
        .expect("the prelude holds int.eq");
    let [zero, one] = ["0", "1"].map(|digits| {
        let magnitude = Magnitude::from_decimal_text(alloc::string::String::from(digits))
            .expect("decimal digits");
        core.value_literal(Literal::Integer(IntegerLiteral::new(
            Sign::NonNegative,
            magnitude,
        )))
    });
    let call = core.computation_primitive(int_eq, Arguments::Binary([zero, one]));

    let (chain, environment) = nothing_unfolds();
    let scope = environment.root();
    let definitions = Definitions::new(&chain, &environment, scope);
    let mut domain = DomainArena::new();
    let evaluated = eval_computation(&core, &mut domain, definitions, ample(), call)
        .expect("a native call stands rather than faulting");
    let Some(&DomainComp::Neutral { neutral, .. }) = domain.computation(evaluated)
    else {
        panic!("a native call is stuck");
    };
    let held = domain.neutral(neutral).expect("its neutral resolves");
    assert_eq!(
        NeutralHead::Primitive(int_eq),
        held.head(),
        "the call is stuck on its operation"
    );
    assert!(
        matches!(*held.spine(), [
            Elimination::Force,
            Elimination::Apply(_),
            Elimination::Apply(_)
        ]),
        "the operation is forced, then applied once per argument: {:?}",
        held.spine()
    );

    let read = readback_computation(
        &mut core,
        &mut domain,
        definitions,
        ReadbackMode::ZeroUnfold,
        ample(),
        evaluated,
    )
    .expect("a stuck native call reads back");
    let Some(&Computation::Application(applied, second)) = core.computation(read)
    else {
        panic!("the second argument is applied last");
    };
    let Some(&Computation::Application(forced, first)) = core.computation(applied)
    else {
        panic!("the first argument is applied to the forced operation");
    };
    let Some(&Computation::Force(operation)) = core.computation(forced)
    else {
        panic!("the operation is forced");
    };
    assert!(
        matches!(
            core.value(operation),
            Some(&Value::Primitive { primitive, .. }) if primitive == int_eq
        ),
        "the head reads back as the operation's thunk"
    );
    assert_eq!(
        [core.value(zero), core.value(one)],
        [core.value(first), core.value(second)],
        "the arguments come back in source order"
    );
}

#[test]
fn a_stuck_spine_reads_back_as_its_eliminations()
{
    let mut core = CoreArena::new();
    let position = ConstantIndex::from(0_usize);
    let opaque = core.value_constant(position);
    let argument = core.value_unit();
    let forced = core.computation_force(opaque);
    let applied = core.computation_application(forced, argument);

    let (chain, environment) = nothing_unfolds();
    let scope = environment.root();
    let definitions = Definitions::new(&chain, &environment, scope);
    let mut domain = DomainArena::new();
    let evaluated = eval_computation(&core, &mut domain, definitions, ample(), applied)
        .expect("an eliminator over a rigid constant gets stuck");

    let read = readback_computation(
        &mut core,
        &mut domain,
        definitions,
        ReadbackMode::ZeroUnfold,
        ample(),
        evaluated,
    )
    .expect("a stuck spine reads back");
    let Some(&Computation::Application(head, spliced)) = core.computation(read)
    else {
        panic!("the outermost elimination is the application");
    };
    assert_eq!(
        argument, spliced,
        "the argument kept its source face and was spliced rather than rebuilt"
    );
    let Some(&Computation::Force(thunked)) = core.computation(head)
    else {
        panic!("and the innermost is the force, so the spine folded innermost first");
    };
    assert_eq!(
        Some(&Value::Constant(position)),
        core.value(thunked),
        "over the head the spine was stacked on"
    );
}

#[test]
fn a_stuck_bind_and_case_read_back_their_branches()
{
    let (chain, environment) = nothing_unfolds();
    let scope = environment.root();
    let definitions = Definitions::new(&chain, &environment, scope);
    let position = ConstantIndex::from(0_usize);

    let mut core = CoreArena::new();
    let opaque = core.value_constant(position);
    let forced = core.computation_force(opaque);
    let occurrence = core.value_variable(Zone::Intuitionistic, innermost());
    let continuation = core.computation_return(occurrence);
    let sequenced = core.computation_bind(forced, continuation);

    let mut domain = DomainArena::new();
    let evaluated = eval_computation(&core, &mut domain, definitions, ample(), sequenced)
        .expect("a bind over a stuck computation gets stuck");
    let read = readback_computation(
        &mut core,
        &mut domain,
        definitions,
        ReadbackMode::ZeroUnfold,
        ample(),
        evaluated,
    )
    .expect("a stuck bind reads back");
    let Some(&Computation::Bind(bound, body)) = core.computation(read)
    else {
        panic!("the outermost elimination is the bind");
    };
    assert!(
        matches!(core.computation(bound), Some(&Computation::Force(_))),
        "the bound computation is what the spine had beneath it"
    );
    let Some(&Computation::Return(produced)) = core.computation(body)
    else {
        panic!("the continuation is a returner");
    };
    assert_eq!(
        Some(&Value::Variable {
            zone: Zone::Intuitionistic,
            index: innermost(),
        }),
        core.value(produced),
        "and the continuation's own binder was opened and closed again as an index"
    );

    let mut core = CoreArena::new();
    let opaque = core.value_constant(position);
    let taken = core.value_unit();
    let on_left = core.computation_return(taken);
    let occurrence = core.value_variable(Zone::Intuitionistic, innermost());
    let on_right = core.computation_return(occurrence);
    let cased = core.computation_case(opaque, &[on_left, on_right]);

    let mut domain = DomainArena::new();
    let evaluated = eval_computation(&core, &mut domain, definitions, ample(), cased)
        .expect("a case over a stuck scrutinee gets stuck");
    let read = readback_computation(
        &mut core,
        &mut domain,
        definitions,
        ReadbackMode::ZeroUnfold,
        ample(),
        evaluated,
    )
    .expect("a stuck case reads back");
    let Some(&Computation::Case {
        scrutinee,
        ref branches,
    }) = core.computation(read)
    else {
        panic!("the elimination is the case");
    };
    let &[left, right] = &**branches
    else {
        panic!("the case keeps both branches");
    };
    assert_eq!(
        Some(&Value::Constant(position)),
        core.value(scrutinee),
        "the scrutinee is the stuck head the case could not fire on"
    );
    assert!(
        matches!(
            core.computation(left),
            Some(&Computation::Return(produced)) if core.value(produced) == Some(&Value::unit())
        ),
        "the left branch is the one that returns the unit"
    );
    let Some(&Computation::Return(produced)) = core.computation(right)
    else {
        panic!("the right branch is a returner");
    };
    assert_eq!(
        Some(&Value::Variable {
            zone: Zone::Intuitionistic,
            index: innermost(),
        }),
        core.value(produced),
        "and the right branch is the one that reads its binder, so the two were not \
             swapped on the way out"
    );
}

#[test]
fn a_spine_that_misses_its_polarity_is_refused()
{
    let mut core = CoreArena::new();
    let (chain, environment) = nothing_unfolds();
    let scope = environment.root();
    let definitions = Definitions::new(&chain, &environment, scope);
    let mut domain = DomainArena::new();
    let position = ConstantIndex::from(0_usize);

    let bare = domain
        .neutral_node(
            NeutralHead::Constant(position),
            Vec::new(),
            Unfolding::Rigid,
        )
        .expect("a rigid declaration head mints");
    let stuck = domain.comp_neutral(bare, CompTermFace::Reduced);
    assert_eq!(
        Err(ReadbackFault::NeutralPolarity { neutral: bare }),
        readback_computation(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::ZeroUnfold,
            ample(),
            stuck,
        ),
        "a head with nothing stacked on it is a value, so it cannot stand where a \
             computation is expected"
    );

    let unit = domain.value_unit(TermFace::Reduced);
    let applied = domain
        .neutral_node(
            NeutralHead::Constant(position),
            Vec::from([Elimination::Apply(unit)]),
            Unfolding::Rigid,
        )
        .expect("a spined neutral mints");
    let stuck = domain.comp_neutral(applied, CompTermFace::Reduced);
    assert_eq!(
        Err(ReadbackFault::NeutralPolarity { neutral: applied }),
        readback_computation(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::ZeroUnfold,
            ample(),
            stuck,
        ),
        "and an application stacked straight onto a value head is refused rather than \
             folded over whatever the computation stack happened to hold"
    );
}

#[test]
fn the_zero_unfold_mode_leaves_an_unforced_body_unforced()
{
    let mut core = CoreArena::new();
    let (chain, environment) = nothing_unfolds();
    let scope = environment.root();
    let definitions = Definitions::new(&chain, &environment, scope);
    let mut domain = DomainArena::new();

    let position = ConstantIndex::from(0_usize);
    let body = GlobalIndex::from(9_u32);
    let neutral = domain
        .neutral_node(
            NeutralHead::Constant(position),
            Vec::new(),
            Unfolding::Unforced(body),
        )
        .expect("a declaration head may carry a body");
    let stood = domain
        .value_neutral(neutral, TermFace::Reduced)
        .expect("a spineless neutral stands in a value position");

    let read = readback_value(
        &mut core,
        &mut domain,
        definitions,
        ReadbackMode::ZeroUnfold,
        ample(),
        stood,
    )
    .expect("the zero-unfold mode reads the neutral form");
    assert_eq!(
        Some(&Value::Constant(position)),
        core.value(read),
        "the neutral form is the answer, whatever the unfolding face holds"
    );
    let held = domain.neutral(neutral).expect("the neutral resolves");
    assert_eq!(
        Unfolding::Unforced(body),
        held.unfolding(),
        "and the body is still unforced when the readback returns, which is the \
             property a conversion comparing neutral forms stands on"
    );
}

#[test]
fn the_unfolding_mode_refuses_a_body_no_chain_entry_names()
{
    let mut core = CoreArena::new();
    let (chain, environment) = nothing_unfolds();
    let scope = environment.root();
    let definitions = Definitions::new(&chain, &environment, scope);
    let mut domain = DomainArena::new();

    let body = GlobalIndex::from(9_u32);
    let neutral = domain
        .neutral_node(
            NeutralHead::Constant(ConstantIndex::from(0_usize)),
            Vec::new(),
            Unfolding::Unforced(body),
        )
        .expect("a declaration head may carry a body");
    let stood = domain
        .value_neutral(neutral, TermFace::Reduced)
        .expect("a spineless neutral stands in a value position");

    assert_eq!(
        Err(ReadbackFault::UnloweredBody { body }),
        readback_value(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::Unfolding,
            ample(),
            stood,
        ),
        "the spending mode declines a body no entry of the run's chain names rather \
             than answering the neutral form under a mode that promised to unfold it"
    );
}

#[test]
fn the_unfolding_mode_spends_a_body_already_forced()
{
    let mut core = CoreArena::new();
    let (chain, environment) = nothing_unfolds();
    let scope = environment.root();
    let definitions = Definitions::new(&chain, &environment, scope);
    let mut domain = DomainArena::new();

    let position = ConstantIndex::from(0_usize);
    let neutral = domain
        .neutral_node(
            NeutralHead::Constant(position),
            Vec::new(),
            Unfolding::Unforced(GlobalIndex::from(9_u32)),
        )
        .expect("a declaration head may carry a body");
    let stood = domain
        .value_neutral(neutral, TermFace::Reduced)
        .expect("a spineless neutral stands in a value position");
    let unfolded = domain.value_unit(TermFace::Reduced);
    assert_eq!(
        Ok(()),
        domain.force_neutral(neutral, Glued::Value(unfolded)),
        "the body is forced by the caller, because lowering it is not this crate's job"
    );

    let retained = readback_value(
        &mut core,
        &mut domain,
        definitions,
        ReadbackMode::ZeroUnfold,
        ample(),
        stood,
    )
    .expect("the zero-unfold mode reads the neutral form");
    assert_eq!(
        Some(&Value::Constant(position)),
        core.value(retained),
        "the zero-unfold mode still answers the neutral form, even where a body has \
             been forced"
    );

    let spent = readback_value(
        &mut core,
        &mut domain,
        definitions,
        ReadbackMode::Unfolding,
        ample(),
        stood,
    )
    .expect("the spending mode reads the unfolded body");
    assert_eq!(
        Some(&Value::unit()),
        core.value(spent),
        "while the spending mode answers with the body it was forced to"
    );
}

#[test]
fn a_lowered_definition_body_unfolds_through_readback()
{
    let mut core = CoreArena::new();
    let inner = ConstantIndex::from(0_usize);
    let outer = ConstantIndex::from(1_usize);
    let inner_entry = GlobalIndex::from(3_u32);
    let outer_entry = GlobalIndex::from(7_u32);

    // `inner := ⟨⟩` and `outer := (inner, ⟨⟩)`, both lowered into `core`.
    let unit = core.value_unit();
    let mention = core.value_constant(inner);
    let outer_body = core.value_tuple(&[mention, unit]);
    let reference = core.value_constant(outer);

    let mut chain = DefinitionChain::new();
    let defined = chain.define(inner, inner_entry, Transparency::Manifest, &[]);
    assert!(defined.is_ok());
    let defined = chain.define(outer, outer_entry, Transparency::Manifest, &[inner]);
    assert!(defined.is_ok());
    let environment = DefinitionalEnvironment::new();
    let scope = environment.root();
    let chain = LoweredChain::lower(chain, |entry| match entry.constant() {
        position if position == inner => Ok(unit),
        position if position == outer => Ok(outer_body),
        position => Err(position),
    })
    .expect("both bodies lower");
    let definitions = Definitions::new(&chain, &environment, scope);

    let mut domain = DomainArena::new();
    let evaluated = eval_value(&core, &mut domain, definitions, ample(), reference)
        .expect("a constant evaluates to a neutral");
    let Some(&DomainValue::Neutral { neutral, .. }) = domain.value(evaluated)
    else {
        panic!("a manifest constant is stuck until a readback spends it");
    };

    let kept = readback_value(
        &mut core,
        &mut domain,
        definitions,
        ReadbackMode::ZeroUnfold,
        ample(),
        evaluated,
    )
    .expect("the zero-unfold mode reads the neutral form");
    assert_eq!(
        Some(&Value::Constant(outer)),
        core.value(kept),
        "a held lowering changes nothing for the mode that spends nothing"
    );

    let before = domain.watermark();
    let mut marks = [before; 2];
    for (attempt, mark) in ["first", "second"].into_iter().zip(marks.iter_mut()) {
        let unfolded = readback_value(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::Unfolding,
            ample(),
            evaluated,
        )
        .expect("the spending mode forces both lowered bodies");
        let Some(&[first, second]) = core.value(unfolded).and_then(Value::components)
        else {
            panic!("the {attempt} reading is the outer body's pair");
        };
        assert_eq!(
            (Some(&Value::unit()), Some(&Value::unit())),
            (core.value(first), core.value(second)),
            "and in the {attempt} reading the inner constant unfolded too, through its \
                 own lowering"
        );
        let held = domain.neutral(neutral).expect("the neutral resolves");
        assert!(
            matches!(held.unfolding(), Unfolding::Forced(Glued::Value(_))),
            "the force is recorded on the neutral, not discarded with the readback"
        );
        *mark = domain.watermark();
    }
    let [first_mark, second_mark] = marks;
    assert_eq!(
        first_mark, second_mark,
        "and the second reading evaluates neither body again"
    );
}

#[test]
fn a_quote_reads_back_through_its_environment()
{
    // `λ. return ⌜El(#0)⌝`: the quote reads the lambda's binder.
    let mut core = CoreArena::new();
    let occurrence = core.value_variable(Zone::Intuitionistic, innermost());
    let level = Level::zero().succ().expect("level one exists");
    let decoded = core.value_type_element(occurrence, level.clone());
    let quote = core.value_quote(decoded);
    let returned = core.computation_return(quote);
    let lambda = core.computation_lambda(returned);

    let (chain, environment) = nothing_unfolds();
    let scope = environment.root();
    let definitions = Definitions::new(&chain, &environment, scope);
    let mut domain = DomainArena::new();
    let evaluated = eval_computation(&core, &mut domain, definitions, ample(), lambda)
        .expect("a lambda is already a weak head");
    let read = readback_computation(
        &mut core,
        &mut domain,
        definitions,
        ReadbackMode::Unfolding,
        ample(),
        evaluated,
    )
    .expect("the lambda reads back");

    let Some(&Computation::Lambda(body)) = core.computation(read)
    else {
        panic!("the rebuilt computation is a lambda");
    };
    let Some(&Computation::Return(value)) = core.computation(body)
    else {
        panic!("its body is a returner");
    };
    let Some(&Value::Quote(quoted)) = core.value(value)
    else {
        panic!("the returned value is a quote");
    };
    let Some(&ValueType::Element { code, ref target }) = core.value_type(quoted)
    else {
        panic!("the quoted type is a decode");
    };
    assert_eq!(
        &level, target,
        "the captured decode retains its nonzero target"
    );
    assert_eq!(
        Some(&Value::Variable {
            zone: Zone::Intuitionistic,
            index: innermost(),
        }),
        core.value(code),
        "and its code is the lambda's binder again, read through the quote's environment"
    );
}

#[test]
fn a_quoted_decode_unfolds_to_the_quoted_type()
{
    // `code := ⌜Unit⌝`, and the quote `⌜El(code)⌝` reads it.
    let mut core = CoreArena::new();
    let code = ConstantIndex::from(0_usize);
    let unit = core.value_type_unit();
    let body = core.value_quote(unit);
    let mention = core.value_constant(code);
    let decoded = core.value_type_element(mention, Level::zero());
    let quote = core.value_quote(decoded);

    let mut chain = DefinitionChain::new();
    let defined = chain.define(code, GlobalIndex::from(0_u32), Transparency::Manifest, &[]);
    assert!(defined.is_ok());
    let environment = DefinitionalEnvironment::new();
    let scope = environment.root();
    let chain = LoweredChain::lower(chain, |_| Ok::<_, Infallible>(body))
        .unwrap_or_else(|never| match never {});
    let definitions = Definitions::new(&chain, &environment, scope);

    let mut domain = DomainArena::new();
    let evaluated = eval_value(&core, &mut domain, definitions, ample(), quote)
        .expect("a closed quote evaluates");
    let kept = readback_value(
        &mut core,
        &mut domain,
        definitions,
        ReadbackMode::ZeroUnfold,
        ample(),
        evaluated,
    )
    .expect("the zero-unfold mode reads the quote");
    assert_eq!(quote, kept, "a closed quote still denotes its source");

    let unfolded = readback_value(
        &mut core,
        &mut domain,
        definitions,
        ReadbackMode::Unfolding,
        ample(),
        evaluated,
    )
    .expect("the unfolding mode reads the quote");
    let Some(&Value::Quote(quoted)) = core.value(unfolded)
    else {
        panic!("the read value is a quote");
    };
    assert_eq!(
        Some(&ValueType::unit()),
        core.value_type(quoted),
        "the decode's code unfolded to a quote, and decoding it on mint left the quoted type"
    );
}

#[test]
fn a_static_lambda_reads_back_with_its_binder_as_an_index()
{
    // `λX. λY. ⌜El X × El Y⌝`: the inner quote reads both binders.
    let mut core = CoreArena::new();
    let outer = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let inner = core.value_variable(Zone::Intuitionistic, innermost());
    let first = core.value_type_element(outer, Level::zero());
    let second = core.value_type_element(inner, Level::zero());
    let product = core.value_type_product(&[first, second]);
    let quote = core.value_quote(product);
    let inner_lambda = core.value_static_lambda(quote);
    let lambda = core.value_static_lambda(inner_lambda);

    let (chain, environment) = nothing_unfolds();
    let scope = environment.root();
    let definitions = Definitions::new(&chain, &environment, scope);
    let mut domain = DomainArena::new();
    let evaluated = eval_value(&core, &mut domain, definitions, ample(), lambda)
        .expect("a static lambda is already a value");
    assert!(
        matches!(
            domain.value(evaluated),
            Some(&DomainValue::StaticLambda { .. })
        ),
        "a static lambda evaluates to an operator"
    );
    let kept = readback_value(
        &mut core,
        &mut domain,
        definitions,
        ReadbackMode::ZeroUnfold,
        ample(),
        evaluated,
    )
    .expect("the zero-unfold mode reads the operator");
    assert_eq!(lambda, kept, "a closed operator still denotes its source");

    let read = readback_value(
        &mut core,
        &mut domain,
        definitions,
        ReadbackMode::Unfolding,
        ample(),
        evaluated,
    )
    .expect("the unfolding mode rebuilds the operator");
    let Some(&Value::StaticLambda(body)) = core.value(read)
    else {
        panic!("the rebuilt value is a static lambda");
    };
    let Some(&Value::StaticLambda(body)) = core.value(body)
    else {
        panic!("whose body is the inner static lambda");
    };
    let Some(&Value::Quote(quoted)) = core.value(body)
    else {
        panic!("whose body is the quote");
    };
    let Some(held) = core.value_type(quoted)
    else {
        panic!("the quoted type is the product");
    };
    let ValueType::Product(ref components) = *held
    else {
        panic!("the quoted type is the product");
    };
    let [left, right] = **components
    else {
        panic!("the product is binary");
    };
    for (component, index) in [(left, 1_u32), (right, 0_u32)] {
        let Some(&ValueType::Element { code, .. }) = core.value_type(component)
        else {
            panic!("each component is a decode");
        };
        assert_eq!(
            Some(&Value::Variable {
                zone: Zone::Intuitionistic,
                index: DeBruijnIndex::from(index),
            }),
            core.value(code),
            "each decode names the binder it was written under, as an index again"
        );
    }
}

#[test]
fn a_quoted_static_pi_reads_back_former_by_former()
{
    // Distinct leaves separate domain and codomain order.
    let mut core = CoreArena::new();
    let universe = core.value_type_universe(
        gandr_core_term::Sort::Ground(gandr_kernel_term::GroundSort::Value),
        Level::zero(),
    );
    let unit = core.value_type_unit();
    let pi = core.value_type_static_pi(unit, universe);
    let quote = core.value_quote(pi);

    let (chain, environment) = nothing_unfolds();
    let scope = environment.root();
    let definitions = Definitions::new(&chain, &environment, scope);
    let mut domain = DomainArena::new();
    let evaluated = eval_value(&core, &mut domain, definitions, ample(), quote)
        .expect("a closed quote evaluates");
    let read = readback_value(
        &mut core,
        &mut domain,
        definitions,
        ReadbackMode::Unfolding,
        ample(),
        evaluated,
    )
    .expect("the unfolding mode reads the quote");
    let Some(&Value::Quote(quoted)) = core.value(read)
    else {
        panic!("the read value is a quote");
    };
    assert_eq!(
        Some(&ValueType::StaticPi {
            domain: unit,
            codomain: universe,
        }),
        core.value_type(quoted),
        "the unit domain precedes the universe codomain"
    );
}

#[test]
fn an_unfolded_operator_reads_back_reduced()
{
    // `Pair := λA. λB. ⌜El A × El B⌝`, read at `Pair ⌜Integer⌝ ⌜Unit⌝`.
    let mut core = CoreArena::new();
    let pair = ConstantIndex::from(0_usize);
    let first = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let second = core.value_variable(Zone::Intuitionistic, innermost());
    let left = core.value_type_element(first, Level::zero());
    let right = core.value_type_element(second, Level::zero());
    let product = core.value_type_product(&[left, right]);
    let quote = core.value_quote(product);
    let inner = core.value_static_lambda(quote);
    let body = core.value_static_lambda(inner);
    let integer = core.value_type_base(gandr_kernel_term::BaseType::Integer);
    let unit = core.value_type_unit();
    let integer_code = core.value_quote(integer);
    let unit_code = core.value_quote(unit);
    let head = core.value_constant(pair);
    let partial = core.value_static_application(head, integer_code);
    let applied = core.value_static_application(partial, unit_code);

    let mut chain = DefinitionChain::new();
    let defined = chain.define(pair, GlobalIndex::from(0_u32), Transparency::Manifest, &[]);
    assert!(defined.is_ok());
    let environment = DefinitionalEnvironment::new();
    let scope = environment.root();
    let chain = LoweredChain::lower(chain, |_| Ok::<_, Infallible>(body))
        .unwrap_or_else(|never| match never {});
    let definitions = Definitions::new(&chain, &environment, scope);

    let mut domain = DomainArena::new();
    let evaluated = eval_value(&core, &mut domain, definitions, ample(), applied)
        .expect("a defined operator applied evaluates");
    let Some(&DomainValue::Neutral { neutral, .. }) = domain.value(evaluated)
    else {
        panic!("the operator is stuck until a readback spends it");
    };
    assert!(
        matches!(
            domain.neutral(neutral).map(crate::domain::Neutral::spine),
            Some([Elimination::StaticApply(_), Elimination::StaticApply(_)])
        ),
        "the neutral carries both static applications"
    );

    let kept = readback_value(
        &mut core,
        &mut domain,
        definitions,
        ReadbackMode::ZeroUnfold,
        ample(),
        evaluated,
    )
    .expect("the zero-unfold mode reads the stuck application");
    let Some(&Value::StaticApplication(kept_head, _)) = core.value(kept)
    else {
        panic!("the mode that spends nothing keeps the application");
    };
    assert!(
        matches!(core.value(kept_head), Some(&Value::StaticApplication(..))),
        "both applications stand"
    );

    let reduced = readback_value(
        &mut core,
        &mut domain,
        definitions,
        ReadbackMode::Unfolding,
        ample(),
        evaluated,
    )
    .expect("the spending mode unfolds the operator and fires both betas");
    let Some(&Value::Quote(quoted)) = core.value(reduced)
    else {
        panic!("the reduct is the body's quote, with no application left");
    };
    let Some(held) = core.value_type(quoted)
    else {
        panic!("the quoted type is the body's product");
    };
    let ValueType::Product(ref components) = *held
    else {
        panic!("the quoted type is the body's product");
    };
    let [read_left, read_right] = **components
    else {
        panic!("the body's product is binary");
    };
    assert_eq!(
        (
            Some(&ValueType::Base(gandr_kernel_term::BaseType::Integer)),
            Some(&ValueType::unit())
        ),
        (core.value_type(read_left), core.value_type(read_right)),
        "each parameter was replaced by its own argument, in order"
    );
}

#[test]
fn a_quoted_dependent_arrow_reads_its_binder_as_an_index()
{
    // `λ. return ⌜Thunk(Π(_ : El(#0)). El(#0) ⊸ El(#1))⌝`, written with
    // the codomain's `#1` naming the lambda's binder past the arrow's.
    let mut core = CoreArena::new();
    let outer = core.value_variable(Zone::Intuitionistic, innermost());
    let from = core.value_type_element(outer, Level::zero());
    let bound = core.value_variable(Zone::Intuitionistic, innermost());
    let near = core.value_type_element(bound, Level::zero());
    let past = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let far = core.comp_type_element(past, Level::zero());
    let arrow = core.comp_type_arrow(near, far);
    let pi = core.comp_type_pi(from, arrow);
    let thunk = core.value_type_thunk(pi);
    let quote = core.value_quote(thunk);
    let returned = core.computation_return(quote);
    let lambda = core.computation_lambda(returned);

    let (chain, environment) = nothing_unfolds();
    let scope = environment.root();
    let definitions = Definitions::new(&chain, &environment, scope);
    let mut domain = DomainArena::new();
    let evaluated = eval_computation(&core, &mut domain, definitions, ample(), lambda)
        .expect("a lambda is already a weak head");
    let read = readback_computation(
        &mut core,
        &mut domain,
        definitions,
        ReadbackMode::Unfolding,
        ample(),
        evaluated,
    )
    .expect("the lambda reads back");

    let Some(&Computation::Lambda(body)) = core.computation(read)
    else {
        panic!("a lambda");
    };
    let Some(&Computation::Return(value)) = core.computation(body)
    else {
        panic!("returning");
    };
    let Some(&Value::Quote(quoted)) = core.value(value)
    else {
        panic!("a quote");
    };
    let Some(&ValueType::Thunk(suspended)) = core.value_type(quoted)
    else {
        panic!("of a thunk type");
    };
    let Some(&CompType::Pi {
        domain: read_from,
        codomain,
    }) = core.comp_type(suspended)
    else {
        panic!("over a dependent arrow");
    };
    let Some(&CompType::Arrow {
        domain: read_near,
        codomain: read_far,
    }) = core.comp_type(codomain)
    else {
        panic!("whose codomain is an arrow");
    };
    let code_of_value = |core: &CoreArena, ty| match core.value_type(ty) {
        Some(&ValueType::Element { code, .. }) => core.value(code).cloned(),
        _ => None,
    };
    let variable = |index: u32| {
        Some(Value::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(index),
        })
    };
    assert_eq!(
        variable(0_u32),
        code_of_value(&core, read_from),
        "outside the arrow's binder, the lambda's is innermost"
    );
    assert_eq!(
        variable(0_u32),
        code_of_value(&core, read_near),
        "inside it, the arrow's own binder is innermost"
    );
    let Some(&CompType::Element { code: far_code, .. }) = core.comp_type(read_far)
    else {
        panic!("the arrow's codomain is a decode");
    };
    assert_eq!(
        variable(1_u32).as_ref(),
        core.value(far_code),
        "and the lambda's binder is one further out, so the fresh variable the readback \
             opened for the arrow counts as a binder"
    );
}

#[test]
fn a_quoted_dependent_pair_reads_its_binder_as_an_index()
{
    // `λ. return ⌜Σ(_ : El(#0)). Product(El(#0), El(#1))⌝`, the second
    // factor's `#1` naming the lambda's binder past the pair's.
    let mut core = CoreArena::new();
    let outer = core.value_variable(Zone::Intuitionistic, innermost());
    let first = core.value_type_element(outer, Level::zero());
    let bound = core.value_variable(Zone::Intuitionistic, innermost());
    let near = core.value_type_element(bound, Level::zero());
    let past = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let far = core.value_type_element(past, Level::zero());
    let second = core.value_type_product(&[near, far]);
    let sigma = core.value_type_sigma(first, second);
    let quote = core.value_quote(sigma);
    let returned = core.computation_return(quote);
    let lambda = core.computation_lambda(returned);

    let (chain, environment) = nothing_unfolds();
    let scope = environment.root();
    let definitions = Definitions::new(&chain, &environment, scope);
    let mut domain = DomainArena::new();
    let evaluated = eval_computation(&core, &mut domain, definitions, ample(), lambda)
        .expect("a lambda is already a weak head");
    let read = readback_computation(
        &mut core,
        &mut domain,
        definitions,
        ReadbackMode::Unfolding,
        ample(),
        evaluated,
    )
    .expect("the lambda reads back");

    let Some(&Computation::Lambda(body)) = core.computation(read)
    else {
        panic!("a lambda");
    };
    let Some(&Computation::Return(value)) = core.computation(body)
    else {
        panic!("returning");
    };
    let Some(&Value::Quote(quoted)) = core.value(value)
    else {
        panic!("a quote");
    };
    let Some(&ValueType::Sigma {
        first: read_first,
        second: read_second,
    }) = core.value_type(quoted)
    else {
        panic!("of a dependent pair");
    };
    let Some(read) = core.value_type(read_second)
    else {
        panic!("whose second factor is in the arena");
    };
    let ValueType::Product(ref parts) = *read
    else {
        panic!("whose second factor is a product");
    };
    let [read_near, read_far] = **parts
    else {
        panic!("of two parts");
    };
    let code_of = |core: &CoreArena, ty| match core.value_type(ty) {
        Some(&ValueType::Element { code, .. }) => core.value(code).cloned(),
        _ => None,
    };
    let variable = |index: u32| {
        Some(Value::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(index),
        })
    };
    assert_eq!(
        variable(0_u32),
        code_of(&core, read_first),
        "outside the pair's binder, the lambda's is innermost"
    );
    assert_eq!(
        variable(0_u32),
        code_of(&core, read_near),
        "inside it, the pair's own binder is innermost"
    );
    assert_eq!(
        variable(1_u32),
        code_of(&core, read_far),
        "and the lambda's binder is one further out"
    );
}

#[test]
fn a_readback_declines_on_fuel_rather_than_running_on()
{
    let mut core = CoreArena::new();
    let first = core.value_unit();
    let second = core.value_unit();
    let pair = core.value_tuple(&[first, second]);

    let (chain, environment) = nothing_unfolds();
    let scope = environment.root();
    let definitions = Definitions::new(&chain, &environment, scope);
    let mut domain = DomainArena::new();
    let evaluated = eval_value(&core, &mut domain, definitions, ample(), pair)
        .expect("a closed pair of units evaluates");

    assert_eq!(
        Err(ReadbackFault::OutOfFuel),
        readback_value(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::Unfolding,
            Fuel::from(2_u32),
            evaluated,
        ),
        "rebuilding the pair takes four tasks, so a budget of two runs out on the \
             readback's own stack"
    );

    let mut core = CoreArena::new();
    let occurrence = core.value_variable(Zone::Intuitionistic, innermost());
    let inner_force = core.computation_force(occurrence);
    let self_application = core.computation_application(inner_force, occurrence);
    let looping = core.computation_lambda(self_application);
    let looper = core.value_thunk(looping);
    let outer_force = core.computation_force(looper);
    let omega = core.computation_application(outer_force, looper);
    let suspended = core.computation_lambda(omega);

    let mut domain = DomainArena::new();
    let evaluated = eval_computation(&core, &mut domain, definitions, ample(), suspended)
        .expect("a lambda is already a weak head, whatever its body does");
    assert_eq!(
        Err(ReadbackFault::Eval(EvalFault::OutOfFuel)),
        readback_computation(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::Unfolding,
            Fuel::from(500_u32),
            evaluated,
        ),
        "and opening a binder over a body that loops exhausts the same budget inside \
             the evaluation, which says so under evaluation's own name"
    );
}

#[test]
fn one_budget_bounds_the_readback_and_the_evaluations_it_drives()
{
    // Two terms differing only in how many suspensions of the *same* body
    // the readback must enter: `return ⟨thunk B⟩` drives one evaluation of
    // B, and `return ⟨(thunk B, thunk B)⟩` drives two.
    //
    // Under one shared budget the second costs the first plus a whole
    // evaluation of B. Under a budget handed fresh to each driven
    // evaluation it costs the first plus only the few tasks the extra
    // suspension takes on the readback's own stack — however large B is —
    // because each evaluation would receive the whole budget again. So the
    // gap between the two least sufficient budgets is what separates the
    // two accountings, and B's own link count is the structural bound the
    // gap is measured against rather than a number read off a run.
    let mut core = CoreArena::new();
    let (chain, environment) = nothing_unfolds();
    let scope = environment.root();
    let definitions = Definitions::new(&chain, &environment, scope);

    let body = suspended_body(&mut core);
    let only = core.value_thunk(body);
    let one_suspension = core.computation_return(only);

    let body = suspended_body(&mut core);
    let first = core.value_thunk(body);
    let body = suspended_body(&mut core);
    let second = core.value_thunk(body);
    let both = core.value_tuple(&[first, second]);
    let two_suspensions = core.computation_return(both);

    // Evaluation is not what the budgets below are about, so it runs once
    // with fuel to spare and the search reads its weak head back many
    // times. Both weak heads are one returner over suspensions evaluation
    // never entered, which is why the whole cost lands on the readback.
    let mut domain = DomainArena::new();
    let evaluated_one = eval_computation(&core, &mut domain, definitions, ample(), one_suspension)
        .expect("a returner over one suspension has a weak head");
    let evaluated_two = eval_computation(&core, &mut domain, definitions, ample(), two_suspensions)
        .expect("a returner over a pair of suspensions has a weak head");

    let one = least_sufficient(&mut core, &domain, definitions, evaluated_one)
        .expect("one suspension fits below the search ceiling");
    let two = least_sufficient(&mut core, &domain, definitions, evaluated_two)
        .expect("two suspensions fit below the search ceiling");
    let gap = u32::from(two)
        .checked_sub(u32::from(one))
        .expect("a second suspension cannot make the readback cheaper");
    assert!(
        gap >= SUSPENDED_LINKS,
        "the second suspension cost a whole evaluation of its body, which is at least \
             one unit per bind link; a budget handed fresh to each driven evaluation would \
             have charged only the few tasks the suspension itself takes"
    );

    assert_eq!(
        Err(ReadbackFault::OutOfFuel),
        read_at(
            &mut core,
            &domain,
            definitions,
            evaluated_two,
            Fuel::from(u32::from(two).saturating_sub(1_u32)),
        ),
        "one unit short of sufficient, the last task of the readback's own stack cannot \
             run"
    );

    assert_eq!(
        Err(ReadbackFault::Eval(EvalFault::OutOfFuel)),
        read_at(
            &mut core,
            &domain,
            definitions,
            evaluated_two,
            Fuel::from(u32::from(one).saturating_add(1_u32)),
        ),
        "and one unit past what a single suspension needs, the shared budget reaches the \
             second suspension's evaluation with nothing left to spend inside it — which is \
             the reading a fresh budget per driven evaluation could not produce, because it \
             would hand that evaluation the whole budget over again"
    );
}

#[test]
fn a_value_from_another_domain_arena_is_refused()
{
    let mut core = CoreArena::new();
    let (chain, environment) = nothing_unfolds();
    let scope = environment.root();
    let definitions = Definitions::new(&chain, &environment, scope);

    let mut other = DomainArena::new();
    let mut stranger = other.value_unit(TermFace::Reduced);
    let mut remaining = 8_usize;
    while remaining > 0 {
        stranger = other.value_tuple([stranger, stranger], TermFace::Reduced);
        remaining = remaining.saturating_sub(1_usize);
    }

    let mut domain = DomainArena::new();
    let _padding = domain.value_unit(TermFace::Reduced);
    assert_eq!(
        Err(ReadbackFault::Domain(DomainFault::Dangling)),
        readback_value(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::ZeroUnfold,
            ample(),
            stranger,
        ),
        "a domain id minted by one arena names no node of another, and the refusal \
             names the domain arena rather than blaming the core one"
    );
}

#[test]
fn effect_operation_types_read_back_in_their_captured_scope()
{
    use gandr_core_term::effect::EffectName;
    use gandr_core_term::effect::EffectOp;
    use gandr_core_term::effect::EffectRow;
    use gandr_core_term::effect::EffectSig;
    use gandr_core_term::effect::OperationName;
    let mut core = CoreArena::new();
    let unit = core.value_type_unit();
    let integer = core.value_type_base(BaseType::Integer);
    let string = core.value_type_base(BaseType::String);
    let variable = core.value_variable(Zone::Intuitionistic, innermost());
    let parameter = core.value_type_element(variable, Level::zero());
    let list = core.value_type_list(parameter);
    let signature = EffectSig::new(EffectName::from("State"), alloc::vec![
        EffectOp {
            name: OperationName::from("put"),
            payload: list,
            reply: integer
        },
        EffectOp {
            name: OperationName::from("get"),
            payload: unit,
            reply: list
        },
    ])
    .unwrap();
    let result = core.comp_type_returner_with_effects(string, EffectRow::singleton(signature));
    let quote = core.value_quote_computation(result);
    let lambda = core.value_static_lambda(quote);
    let argument = core.value_quote(unit);
    let applied = core.value_static_application(lambda, argument);
    let (chain, environment) = nothing_unfolds();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let mut domain = DomainArena::new();
    let evaluated = eval_value(&core, &mut domain, definitions, ample(), applied).unwrap();
    let read = readback_value(
        &mut core,
        &mut domain,
        definitions,
        ReadbackMode::Unfolding,
        ample(),
        evaluated,
    )
    .unwrap();
    let Some(&Value::QuoteComputation(read)) = core.value(read)
    else {
        panic!("expected a computation code")
    };
    let Some(&CompType::Returner {
        result,
        ref effects,
    }) = core.comp_type(read)
    else {
        panic!("expected a returner")
    };
    assert_eq!(
        core.value_type(result),
        Some(&ValueType::Base(BaseType::String))
    );
    let signature = effects.signatures().next().unwrap();
    assert_eq!(signature.name().as_ref(), "State");
    let operations: alloc::vec::Vec<_> = signature.operations().collect();
    assert_eq!(operations[0].name.as_ref(), "get");
    assert_eq!(
        core.value_type(operations[0].payload),
        Some(&ValueType::unit())
    );
    assert_eq!(operations[1].name.as_ref(), "put");
    assert_eq!(
        core.value_type(operations[1].reply),
        Some(&ValueType::Base(BaseType::Integer))
    );
    for list in [operations[0].reply, operations[1].payload] {
        let Some(&ValueType::List(element)) = core.value_type(list)
        else {
            panic!("the operation retains its List former")
        };
        assert_eq!(core.value_type(element), Some(&ValueType::unit()));
    }
}

#[test]
fn control_type_codes_read_back_their_captured_scope()
{
    use gandr_core_term::CertificateEquality;
    use gandr_core_term::equal_certificate_syntax;
    let mut core = CoreArena::new();
    let parameter = core.value_variable(Zone::Intuitionistic, innermost());
    let decoded = core.value_type_element(parameter, Level::zero());
    let list = core.value_type_list(decoded);
    let input = core.comp_type_returner(list);
    let unit = core.value_type_unit();
    let returned_unit = core.comp_type_returner(unit);
    let output = core.comp_type_with(&[returned_unit, input]);
    let stack = core.value_type_stack(input, output);
    let quote = core.value_quote(stack);
    let lambda = core.value_static_lambda(quote);
    let string = core.value_type_base(BaseType::String);
    let argument = core.value_quote(string);
    let applied = core.value_static_application(lambda, argument);
    let (chain, environment) = nothing_unfolds();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let mut domain = DomainArena::new();
    let evaluated = eval_value(&core, &mut domain, definitions, ample(), applied).unwrap();
    let read = readback_value(
        &mut core,
        &mut domain,
        definitions,
        ReadbackMode::Unfolding,
        ample(),
        evaluated,
    )
    .unwrap();
    let closed_list = core.value_type_list(string);
    let closed_input = core.comp_type_returner(closed_list);
    let closed_output = core.comp_type_with(&[returned_unit, closed_input]);
    let closed_stack = core.value_type_stack(closed_input, closed_output);
    let expected = core.value_quote(closed_stack);
    assert_eq!(
        equal_certificate_syntax(&core, read, expected),
        CertificateEquality::Equal
    );
}

#[test]
fn an_opened_closure_reports_the_evaluations_own_fault()
{
    let mut core = CoreArena::new();
    let (chain, environment) = nothing_unfolds();
    let scope = environment.root();
    let definitions = Definitions::new(&chain, &environment, scope);

    let mut other = CoreArena::new();
    let produced = other.value_unit();
    let mut stranger = other.computation_return(produced);
    let mut remaining = 8_usize;
    while remaining > 0 {
        stranger = other.computation_bind(stranger, stranger);
        remaining = remaining.saturating_sub(1_usize);
    }

    let mut domain = DomainArena::new();
    let closure = domain.comp_closure_node(stranger, Environment::new());
    let thunk = domain.value_thunk(closure, TermFace::Reduced);
    assert_eq!(
        Err(ReadbackFault::Eval(EvalFault::DanglingTerm)),
        readback_value(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::ZeroUnfold,
            ample(),
            thunk,
        ),
        "the core-arena miss reaches a readback only through the evaluation an opened \
             closure drives, and it arrives under that machine's own name"
    );
}

#[test]
fn a_manifest_definition_reads_back_as_the_reference_it_came_from()
{
    let mut core = CoreArena::new();
    let position = ConstantIndex::from(0_usize);
    let reference = core.value_constant(position);
    let unfolded = core.value_unit();

    let mut chain = DefinitionChain::new();
    let body = GlobalIndex::from(9_u32);
    let defined = chain.define(position, body, Transparency::Manifest, &[]);
    assert_eq!(Ok(()), defined.map(|_| ()), "the definition is admitted");
    let chain =
        LoweredChain::lower(chain, |_| Ok::<_, Infallible>(unfolded)).expect("the body lowers");
    let environment = DefinitionalEnvironment::new();
    let scope = environment.root();
    let definitions = Definitions::new(&chain, &environment, scope);

    let mut domain = DomainArena::new();
    let evaluated = eval_value(&core, &mut domain, definitions, ample(), reference)
        .expect("a constant evaluates to a neutral");
    let mark = core.watermark();
    let read = readback_value(
        &mut core,
        &mut domain,
        definitions,
        ReadbackMode::ZeroUnfold,
        ample(),
        evaluated,
    )
    .expect("the zero-unfold mode reads it back");
    assert_eq!(
        reference, read,
        "an evaluated constant keeps its source face, so the readback answers with \
             the reference rather than rebuilding one"
    );
    assert_eq!(mark, core.watermark(), "and mints nothing to do it");
}

#[test]
fn budget_search_does_not_reuse_forcing_from_failed_attempts()
{
    let mut core = CoreArena::new();
    let mut body = core.value_unit();
    let links = 16_u32;
    for _link in 0_u32 .. links {
        body = core.value_injection(Side::Left.into(), body);
    }
    let constant = ConstantIndex::from(0_usize);
    let mut chain = DefinitionChain::new();
    chain
        .define(
            constant,
            GlobalIndex::from(0_u32),
            Transparency::Manifest,
            &[],
        )
        .expect("the closed body has no dependencies");
    let Ok(chain) = LoweredChain::lower(chain, |_| Ok::<_, Infallible>(body));
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let reference = core.value_constant(constant);
    let returned = core.computation_return(reference);
    let mut domain = DomainArena::new();
    let evaluated = eval_computation(&core, &mut domain, definitions, ample(), returned)
        .expect("the definition remains unforced during evaluation");
    let pristine = domain.clone();
    let minimum = least_sufficient(&mut core, &domain, definitions, evaluated)
        .expect("the finite readback has a sufficient budget");
    let boundary = core.watermark();
    let mut fresh = pristine.clone();
    let read = readback_computation(
        &mut core,
        &mut fresh,
        definitions,
        ReadbackMode::Unfolding,
        minimum,
        evaluated,
    )
    .expect("the reported minimum must suffice without an earlier attempt's cached forcing");
    let Some(&Computation::Return(mut value)) = core.computation(read)
    else {
        panic!("the complete readback returns the definition's body");
    };
    for _link in 0_u32 .. links {
        let Some(&Value::Injection(summand, next)) = core.value(value)
        else {
            panic!("every layer of the forced body is rebuilt");
        };
        assert_eq!(summand, Side::Left.into());
        value = next;
    }
    assert_eq!(Some(&Value::unit()), core.value(value));
    core.truncate_to(boundary);
    let mut below = pristine;
    let smaller = Fuel::from(
        u32::from(minimum)
            .checked_sub(1_u32)
            .expect("every readback performs a task"),
    );
    assert!(matches!(
        readback_computation(
            &mut core,
            &mut below,
            definitions,
            ReadbackMode::Unfolding,
            smaller,
            evaluated
        ),
        Err(ReadbackFault::OutOfFuel | ReadbackFault::Eval(EvalFault::OutOfFuel))
    ));
}

#[test]
fn quoted_formers_preserve_distinct_children_and_targets()
{
    let mut core = CoreArena::new();
    let unit = core.value_type_unit();
    let universe = core.value_type_universe(
        gandr_core_term::Sort::Ground(gandr_kernel_term::GroundSort::Value),
        Level::zero(),
    );
    let target = Level::zero()
        .succ()
        .and_then(|one| one.succ())
        .expect("level two exists");
    let (chain, environment) = nothing_unfolds();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let rebuild = |core: &mut CoreArena, source| {
        let mut domain = DomainArena::new();
        let evaluated = eval_value(core, &mut domain, definitions, ample(), source)
            .expect("the closed quote evaluates");
        readback_value(
            core,
            &mut domain,
            definitions,
            ReadbackMode::Unfolding,
            ample(),
            evaluated,
        )
        .expect("its formers normalize")
    };
    let types = [
        (
            core.value_type_product(&[unit, universe]),
            ValueType::Product([unit, universe].into()),
        ),
        (
            core.value_type_sum(&[universe, unit]),
            ValueType::Sum([universe, unit].into()),
        ),
        (
            core.value_type_lift(unit, target.clone()),
            ValueType::Lift {
                inner: unit,
                target: target.clone(),
            },
        ),
    ];
    for (ty, expected) in types {
        let source = core.value_quote(ty);
        let read = rebuild(&mut core, source);
        let Some(&Value::Quote(quoted)) = core.value(read)
        else {
            panic!("a value-type quote stays positive");
        };
        assert_eq!(Some(&expected), core.value_type(quoted));
    }
    let result = core.comp_type_returner(unit);
    let suspended = core.value_type_thunk(result);
    let source = core.value_quote(suspended);
    let read = rebuild(&mut core, source);
    let Some(&Value::Quote(quoted)) = core.value(read)
    else {
        panic!("a thunk type is quoted positively");
    };
    let Some(&ValueType::Thunk(body)) = core.value_type(quoted)
    else {
        panic!("the thunk former is retained");
    };
    assert_eq!(
        Some(&CompType::Returner {
            result: unit,
            effects: gandr_core_term::effect::EffectRow::EMPTY
        }),
        core.comp_type(body)
    );

    let source = core.value_quote_computation(result);
    let read = rebuild(&mut core, source);
    let Some(&Value::QuoteComputation(quoted)) = core.value(read)
    else {
        panic!("the quoted computation type retains its polarity");
    };
    assert_eq!(
        Some(&CompType::Returner {
            result: unit,
            effects: gandr_core_term::effect::EffectRow::EMPTY
        }),
        core.comp_type(quoted)
    );

    let constant = ConstantIndex::from(0_usize);
    let reference = core.value_constant(constant);
    let decoded = core.comp_type_element(reference, target.clone());
    let source = core.value_quote_computation(decoded);
    let read = rebuild(&mut core, source);
    let Some(&Value::QuoteComputation(quoted)) = core.value(read)
    else {
        panic!("the decoded computation type retains its polarity");
    };
    let Some(&CompType::Element {
        code,
        target: ref held,
    }) = core.comp_type(quoted)
    else {
        panic!("the opaque code remains a decode");
    };
    assert_eq!(&target, held);
    assert_eq!(Some(&Value::Constant(constant)), core.value(code));
}

#[test]
fn a_shared_value_reads_back_once_at_each_binder_depth()
{
    // `return () to x₀. return (x₀, x₀) to x₁. … return x₁₆`: the domain
    // shares each pair's two components, so readback builds one pair a step.
    let doublings = 16_usize;
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let bound = core.value_variable(Zone::Intuitionistic, innermost());
    let mut body = core.computation_return(bound);
    for _ in 0 .. doublings {
        let pair = core.value_tuple(&[bound, bound]);
        let returned = core.computation_return(pair);
        body = core.computation_bind(returned, body);
    }
    let first = core.computation_return(unit);
    let chain = core.computation_bind(first, body);
    let suspended = core.value_thunk(chain);
    let (lowered, environment) = nothing_unfolds();
    let definitions = Definitions::new(&lowered, &environment, environment.root());
    let mut domain = DomainArena::new();
    let evaluated = eval_value(&core, &mut domain, definitions, ample(), suspended)
        .expect("the chain evaluates");
    let read = readback_value(
        &mut core,
        &mut domain,
        definitions,
        ReadbackMode::Unfolding,
        ample(),
        evaluated,
    )
    .expect("the shared chain reads back within a budget its tree would exhaust");
    let Some(&Value::Thunk(read_body)) = core.value(read)
    else {
        panic!("the chain reads back as a thunk");
    };
    let Some(&Computation::Return(mut node)) = core.computation(read_body)
    else {
        panic!("its body returns the last pair");
    };
    for step in 0 .. doublings {
        let Some(&Value::Tuple(ref components)) = core.value(node)
        else {
            panic!("step {step} is a pair");
        };
        let [left, right] = **components
        else {
            panic!("step {step} has two components");
        };
        assert_eq!(
            left, right,
            "step {step}'s two components are one core node"
        );
        node = left;
    }
    assert_eq!(
        Some(&Value::unit()),
        core.value(node),
        "the chain ends at the unit"
    );

    // `thunk (λ. return (x₀, thunk (λ. return x₁)))`: the outer binder's
    // variable is one domain value, read under one binder and under two.
    let mut core = CoreArena::new();
    let near = core.value_variable(Zone::Intuitionistic, innermost());
    let far = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let inner_return = core.computation_return(far);
    let inner_lambda = core.computation_lambda(inner_return);
    let inner = core.value_thunk(inner_lambda);
    let pair = core.value_tuple(&[near, inner]);
    let outer_return = core.computation_return(pair);
    let outer_lambda = core.computation_lambda(outer_return);
    let outer = core.value_thunk(outer_lambda);
    let mut domain = DomainArena::new();
    let evaluated = eval_value(&core, &mut domain, definitions, ample(), outer)
        .expect("the nested thunk evaluates");
    let read = readback_value(
        &mut core,
        &mut domain,
        definitions,
        ReadbackMode::Unfolding,
        ample(),
        evaluated,
    )
    .expect("the nested thunk reads back");
    let variable = |index: u32| {
        Some(Value::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(index),
        })
    };
    let returned = |core: &CoreArena, thunk| {
        let Some(&Value::Thunk(body)) = core.value(thunk)
        else {
            panic!("a thunk reads back as a thunk");
        };
        let Some(&Computation::Lambda(inside)) = core.computation(body)
        else {
            panic!("its body is a lambda");
        };
        let Some(&Computation::Return(value)) = core.computation(inside)
        else {
            panic!("the lambda returns a value");
        };
        value
    };
    let Some(&Value::Tuple(ref components)) = core.value(returned(&core, read))
    else {
        panic!("the outer lambda returns a pair");
    };
    let [first, second] = **components
    else {
        panic!("the pair has two components");
    };
    assert_eq!(
        variable(0),
        core.value(first).cloned(),
        "under one binder, x reads as index 0"
    );
    assert_eq!(
        variable(1),
        core.value(returned(&core, second)).cloned(),
        "under two binders, the same domain value reads as index 1"
    );
}
