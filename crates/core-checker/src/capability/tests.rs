use alloc::sync::Arc;

use gandr_core_term::CompType;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::control::EffectClause;
use gandr_core_term::effect::EffectRow;
use gandr_core_term::effect::OperationName;
use gandr_core_term::effect::RowInclusion;
use gandr_core_term::effect::capability::CapabilityGrade;
use gandr_core_term::effect::capability::Region;
use gandr_core_term::effect::capability::RegionDepth;
use gandr_core_term::effect::host::AuthorityError;
use gandr_core_term::effect::host::HostSignatures;
use gandr_core_term::hole::HoleId;
use gandr_core_term::world::World;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use quenchant_shape::shape::Maybe;

use super::Grants;
use super::HostGrant;
use crate::CheckBudget;
use crate::CheckRefusal;
use crate::CheckingContext;
use crate::CheckingForm;
use crate::Declaration;
use crate::ExpectedShape;
use crate::OriginToken;
use crate::TermNode;
use crate::TypeNode;
use crate::Verdict;
use crate::body;
use crate::check_comp;
use crate::check_module;
use crate::check_value;
use crate::fixture::integer_literal;
use crate::fixture::text_literal;
use crate::form_comp_type;
use crate::form_value_type;
use crate::synthesise_comp;
use crate::worlds::Entry;
use crate::worlds::HostEntry;
use crate::worlds::WorldName;

/// The host filesystem restricted to `names`, as an authority.
///
/// # Specification
/// trivial.
fn files(
    host: &HostSignatures,
    names: &[OperationName],
) -> EffectRow
{
    EffectRow::authority(&[host.fs.restrict(names).unwrap()]).unwrap()
}

/// Check the innermost variable, bound at `hypothesis`, against
/// `expected`.
///
/// # Specification
/// trivial.
fn passed(
    arena: &mut CoreArena,
    hypothesis: ValueTypeId,
    expected: ValueTypeId,
) -> Result<(), CheckRefusal>
{
    let variable = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let mut context = CheckingContext::new(arena, CheckBudget::DEFAULT);
    context.binders().open(Zone::Intuitionistic, hypothesis);
    let expected = form_value_type(&mut context, expected)?;
    check_value(&mut context, variable, expected).map(|_checked| ())
}

#[test]
fn attenuation_narrows_and_never_widens()
{
    let mut arena = CoreArena::new();
    let host = HostSignatures::new(&mut arena).unwrap();
    let durable = CapabilityGrade::Durable;
    let both = arena.value_type_capability(
        files(&host, &["read".into(), "write".into()]),
        durable,
        Region::Held,
    );
    let reads = arena.value_type_capability(files(&host, &["read".into()]), durable, Region::Held);
    let writes =
        arena.value_type_capability(files(&host, &["write".into()]), durable, Region::Held);
    let outer_depth = Region::Scoped(RegionDepth::from(1_u32));
    let scoped_reads =
        arena.value_type_capability(files(&host, &["read".into()]), durable, outer_depth);
    let inner_reads = arena.value_type_capability(
        files(&host, &["read".into()]),
        durable,
        Region::Scoped(RegionDepth::from(2_u32)),
    );
    assert_eq!(
        passed(&mut arena, both, reads),
        Ok(()),
        "{{read, write}} narrows to {{read}}"
    );
    assert_eq!(
        passed(&mut arena, both, both),
        Ok(()),
        "a capability stands at its own type"
    );
    assert!(
        matches!(
            passed(&mut arena, reads, both),
            Err(CheckRefusal::CapabilityAmplified(_))
        ),
        "{{read}} never widens to {{read, write}}"
    );
    assert!(
        matches!(
            passed(&mut arena, reads, writes),
            Err(CheckRefusal::CapabilityAmplified(_))
        ),
        "{{read}} never becomes {{write}}"
    );
    assert_eq!(
        passed(&mut arena, reads, scoped_reads),
        Ok(()),
        "a held capability stands where a scoped one is expected"
    );
    assert_eq!(
        passed(&mut arena, scoped_reads, inner_reads),
        Ok(()),
        "an outer scope's capability stands in an inner scope"
    );
    for (shorter, longer) in [(scoped_reads, reads), (inner_reads, scoped_reads)] {
        assert!(
            matches!(
                passed(&mut arena, shorter, longer),
                Err(CheckRefusal::CapabilityEscaped {
                    at: TermNode::Value(_),
                    found: TypeNode::Value(_)
                })
            ),
            "a capability never outlives its region"
        );
    }
}

#[test]
fn a_consumable_capability_is_refused_by_name()
{
    let mut arena = CoreArena::new();
    let host = HostSignatures::new(&mut arena).unwrap();
    let consumable = arena.value_type_capability(
        files(&host, &["write".into()]),
        CapabilityGrade::Consumable,
        Region::Held,
    );
    let returns = arena.comp_type_returner(consumable);
    let suspended = arena.value_type_thunk(returns);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    for ty in [consumable, suspended] {
        assert_eq!(
            form_value_type(&mut context, ty),
            Err(CheckRefusal::CapabilityConsumable(consumable)),
            "the linear zone admits no binder, so a consumable capability never forms"
        );
    }
}

#[test]
fn no_term_forges_a_capability()
{
    let mut arena = CoreArena::new();
    let host = HostSignatures::new(&mut arena).unwrap();
    let cap = arena.value_type_capability(
        files(&host, &["read".into()]),
        CapabilityGrade::Durable,
        Region::Held,
    );
    let integer = arena.value_type_base(BaseType::Integer);
    let string = arena.value_type_base(BaseType::String);
    let zero = arena.value_literal(integer_literal());
    let returned = arena.computation_return(zero);
    let thunk = arena.value_thunk(returned);
    let pair = arena.value_tuple(&[zero, zero]);
    let hole = arena.value_hole(HoleId::from(0_u32));
    let variable = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    context.binders().open(Zone::Intuitionistic, string);
    let formed = form_value_type(&mut context, cap).unwrap();
    for term in [zero, thunk, pair, variable] {
        assert_eq!(
            check_value(&mut context, term, formed).map(|_checked| ()),
            Err(CheckRefusal::CapabilityForged {
                at: term,
                expected: cap
            }),
            "only a capability hypothesis stands at a capability type"
        );
    }
    assert_eq!(
        check_value(&mut context, hole, formed).map(|_checked| ()),
        Ok(()),
        "a hole owes the capability rather than forging it"
    );
    let integer = form_value_type(&mut context, integer).unwrap();
    assert!(
        matches!(
            check_value(&mut context, thunk, integer),
            Err(CheckRefusal::ShapeMismatch {
                wanted: ExpectedShape::Thunk,
                ..
            })
        ),
        "a thunk at another type keeps its shape mismatch"
    );
}

#[test]
fn an_operation_is_exercised_only_within_the_authority()
{
    let mut arena = CoreArena::new();
    let host = HostSignatures::new(&mut arena).unwrap();
    let cap = arena.value_type_capability(
        files(&host, &["read".into()]),
        CapabilityGrade::Durable,
        Region::Held,
    );
    let string = arena.value_type_base(BaseType::String);
    let path = arena.value_literal(text_literal());
    let unit = arena.value_unit();
    let contents = arena.value_tuple(&[path, path]);
    let variable = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let read = arena.computation_exercise(variable, host.fs.clone(), "read".into(), path);
    let write = arena.computation_exercise(variable, host.fs.clone(), "write".into(), contents);
    let missing = arena.computation_exercise(variable, host.fs.clone(), "missing".into(), path);
    let wrong = arena.computation_exercise(variable, host.fs.clone(), "read".into(), unit);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    context.binders().open(Zone::Intuitionistic, cap);
    let inferred = synthesise_comp(&mut context, read).unwrap().produced().id();
    let Maybe::Present(&gandr_core_term::effect::EffectOp { reply, .. }) =
        host.fs.operation(&"read".into())
    else {
        panic!("the filesystem reads");
    };
    assert_eq!(
        context.arena().comp_type(inferred),
        Some(&CompType::Returner {
            result: reply,
            effects: EffectRow::singleton(host.fs)
        }),
        "a granted read returns its reply, its row the whole interface"
    );
    assert!(
        matches!(
            synthesise_comp(&mut context, write),
            Err(CheckRefusal::CapabilityOutsideAuthority { at, .. }) if at == write
        ),
        "a read capability grants no write"
    );
    assert_eq!(
        synthesise_comp(&mut context, missing).map(|_synthesised| ()),
        Err(CheckRefusal::UnknownOperation { at: missing })
    );
    assert!(
        matches!(
            synthesise_comp(&mut context, wrong),
            Err(CheckRefusal::TypeMismatch(_))
        ),
        "the payload checks against the operation's payload type"
    );
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    context.binders().open(Zone::Intuitionistic, string);
    assert!(
        matches!(
            synthesise_comp(&mut context, read),
            Err(CheckRefusal::ShapeMismatch {
                at: TermNode::Value(at),
                wanted: ExpectedShape::Capability,
                ..
            }) if at == variable
        ),
        "a string is exercised as nothing"
    );
}

/// One clause per operation of the process interface, each answering
/// `body`.
///
/// # Specification
/// trivial.
fn exits(body: gandr_core_term::ComputationId) -> Arc<[EffectClause]>
{
    [EffectClause {
        operation: "exit".into(),
        body,
    }]
    .into()
}

#[test]
fn a_scope_handles_the_capability_it_introduces()
{
    let mut arena = CoreArena::new();
    let host = HostSignatures::new(&mut arena).unwrap();
    let unit_type = arena.value_type_unit();
    let answer = arena.comp_type_returner(unit_type);
    let zero = arena.value_literal(integer_literal());
    let unit = arena.value_unit();
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let exit = arena.computation_exercise(bound, host.proc.clone(), "exit".into(), zero);
    let returned = arena.computation_return(unit);
    let passes = arena.computation_return(bound);
    let scope = arena.computation_scope(host.proc.clone(), exit, passes, exits(returned));
    let integer_return = arena.computation_return(zero);
    let wrong_return =
        arena.computation_scope(host.proc.clone(), exit, integer_return, exits(returned));
    let uncovered = arena.computation_scope(host.proc, exit, passes, [].into());
    let other_process =
        gandr_core_term::effect::EffectSig::new(gandr_core_term::effect::host::PROC.into(), [
            gandr_core_term::effect::EffectOp {
                name: "quit".into(),
                payload: unit_type,
                reply: unit_type,
            },
        ])
        .unwrap();
    let conflicting =
        arena.comp_type_returner_with_effects(unit_type, EffectRow::singleton(other_process));
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let answer = form_comp_type(&mut context, answer).unwrap();
    let conflicting = form_comp_type(&mut context, conflicting).unwrap();
    check_comp(&mut context, scope, answer)
        .expect("the subject exercises the capability its scope introduces");
    assert_eq!(
        context.binders().depth(Zone::Intuitionistic),
        gandr_core_term::BinderDepth::from(0_usize),
        "the scope closes every binder it opened"
    );
    assert!(
        matches!(
            check_comp(&mut context, wrong_return, answer),
            Err(CheckRefusal::TypeMismatch(_))
        ),
        "the return clause delivers the answer"
    );
    assert_eq!(
        check_comp(&mut context, uncovered, answer).map(|_checked| ()),
        Err(CheckRefusal::HandlerCoverage { at: uncovered })
    );
    assert_eq!(
        synthesise_comp(&mut context, scope).map(|_synthesised| ()),
        Err(CheckRefusal::NotSynthesisable {
            form: CheckingForm::Scope(scope)
        })
    );
    assert!(
        matches!(
            check_comp(&mut context, scope, conflicting),
            Err(CheckRefusal::EffectSignatureConflict { at, first, .. })
                if at == scope && first == conflicting.id()
        ),
        "an answer row giving the interface's name other operations conflicts"
    );
}

#[test]
fn a_scoped_capability_never_leaves_its_scope()
{
    let mut arena = CoreArena::new();
    let host = HostSignatures::new(&mut arena).unwrap();
    let process = EffectRow::singleton(host.proc.clone());
    let durable = CapabilityGrade::Durable;
    let unit_type = arena.value_type_unit();
    let held = arena.value_type_capability(process.clone(), durable, Region::Held);
    let outer = arena.value_type_capability(
        process.clone(),
        durable,
        Region::Scoped(RegionDepth::from(1_u32)),
    );
    let returns_held = arena.comp_type_returner(held);
    let returns_outer = arena.comp_type_returner(outer);
    let pure = arena.comp_type_returner(unit_type);
    let requests = arena.comp_type_returner_with_effects(unit_type, process);
    let takes_outer = arena.comp_type_arrow(outer, requests);
    let consumer = arena.value_type_thunk(takes_outer);
    let unit = arena.value_unit();
    let returned = arena.computation_return(unit);
    let [zeroth, first, second] = [0_u32, 1, 2]
        .map(|index| arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index)));
    let passes = arena.computation_return(zeroth);
    let leaks = arena.computation_scope(host.proc.clone(), passes, passes, exits(passes));
    let mentions = arena.computation_scope(host.proc.clone(), returned, returned, exits(returned));
    let consume = |arena: &mut CoreArena, argument| {
        let head = arena.computation_force(second);
        let applied = arena.computation_application(head, argument);
        let inner = arena.computation_scope(host.proc.clone(), applied, passes, exits(returned));
        arena.computation_scope(host.proc.clone(), inner, returned, exits(returned))
    };
    let outer_passed = consume(&mut arena, first);
    let inner_passed = consume(&mut arena, zeroth);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let returns_held = form_comp_type(&mut context, returns_held).unwrap();
    assert!(
        matches!(
            check_comp(&mut context, leaks, returns_held),
            Err(CheckRefusal::CapabilityEscaped {
                at: TermNode::Value(at),
                ..
            }) if at == zeroth
        ),
        "the scope's capability never passes where a held one is promised"
    );
    let returns_outer = form_comp_type(&mut context, returns_outer).unwrap();
    assert_eq!(
        check_comp(&mut context, mentions, returns_outer).map(|_checked| ()),
        Err(CheckRefusal::CapabilityEscaped {
            at: TermNode::Computation(mentions),
            found: TypeNode::Computation(returns_outer.id())
        }),
        "an answer naming the scope's region is refused at the scope"
    );
    context.binders().open(Zone::Intuitionistic, consumer);
    let pure = form_comp_type(&mut context, pure).unwrap();
    check_comp(&mut context, outer_passed, pure)
        .expect("the outer scope's capability stands in the inner scope");
    assert!(
        matches!(
            check_comp(&mut context, inner_passed, pure),
            Err(CheckRefusal::CapabilityEscaped {
                at: TermNode::Value(at),
                ..
            }) if at == zeroth
        ),
        "the inner scope's capability lives one region deeper"
    );
}

#[test]
fn a_held_capability_enters_only_within_the_grant()
{
    let mut arena = CoreArena::new();
    let host = HostSignatures::new(&mut arena).unwrap();
    let durable = CapabilityGrade::Durable;
    let both = arena.value_type_capability(
        files(&host, &["read".into(), "write".into()]),
        durable,
        Region::Held,
    );
    let reads = arena.value_type_capability(files(&host, &["read".into()]), durable, Region::Held);
    let integer = arena.value_type_base(BaseType::Integer);
    let module: alloc::vec::Vec<Declaration> = [both, reads, integer]
        .into_iter()
        .enumerate()
        .map(|(position, declared)| {
            Declaration::new(
                ConstantIndex::from(position),
                Maybe::Present(declared),
                Maybe::Absent(body::Absent::Hole),
                OriginToken::from(position),
            )
        })
        .collect();
    let verdicts = |arena: &mut CoreArena, grants: Grants| {
        let mut context = CheckingContext::new(arena, CheckBudget::DEFAULT);
        context.grant(grants);
        let report = check_module(&mut context, &module);
        report
            .judged()
            .iter()
            .map(|judged| matches!(judged.verdict(), Verdict::Owed(_)))
            .collect::<alloc::vec::Vec<_>>()
    };
    assert_eq!(
        verdicts(&mut arena, Grants::Unbounded),
        [true, true, true],
        "with no grant every held capability is owed"
    );
    let all = files(&host, &["read".into(), "write".into()]);
    assert_eq!(verdicts(&mut arena, Grants::Within(all)), [
        true, true, true
    ]);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    context.grant(Grants::Within(files(&host, &["read".into()])));
    let report = check_module(&mut context, &module);
    assert_eq!(
        report.judged()[0].verdict(),
        Verdict::Refused(CheckRefusal::CapabilityUngranted {
            constant: ConstantIndex::from(0_usize),
            declared: both
        }),
        "a held capability beyond the grant is refused by name"
    );
    assert!(
        report.judged()[1 ..]
            .iter()
            .all(|judged| matches!(judged.verdict(), Verdict::Owed(_))),
        "a capability within the grant, and a hole of another type, are owed"
    );
}

#[test]
fn a_named_grant_bounds_the_held_capabilities()
{
    let [read, write, send] = ["read", "write", "send"].map(OperationName::from);
    assert_eq!(
        HostGrant::within([&read, &send]),
        Err(AuthorityError::Undeclared(send)),
        "an operation the host does not declare is refused when the grant is formed"
    );
    let reads = HostGrant::within([&read, &read]).expect("the host declares read");
    let mut arena = CoreArena::new();
    assert_eq!(HostGrant::UNBOUNDED.grants(&mut arena), Grants::Unbounded);
    let Grants::Within(granted) = reads.grants(&mut arena)
    else {
        panic!("a named grant bounds");
    };
    let host = HostSignatures::new(&mut arena).unwrap();
    let both = files(&host, &[read.clone(), write.clone()]);
    assert_eq!(
        files(&host, core::slice::from_ref(&read)).grants_within(&granted, &arena),
        RowInclusion::Included,
        "the grant holds read"
    );
    assert_eq!(
        both.grants_within(&granted, &arena),
        RowInclusion::Excluded,
        "and not write"
    );
    let written = HostGrant::within([&write, &read]).expect("the host declares both");
    let Grants::Within(granted) = written.grants(&mut arena)
    else {
        panic!("a named grant bounds");
    };
    assert_eq!(both.grants_within(&granted, &arena), RowInclusion::Included);
}

#[test]
fn a_named_entry_reads_as_the_declared_worlds()
{
    let [operator, seat, elsewhere] = ["operator", "seat", "elsewhere"].map(WorldName::from);
    let declared = alloc::collections::BTreeMap::from([
        (operator.clone(), ConstantIndex::from(0_usize)),
        (seat.clone(), ConstantIndex::from(1_usize)),
    ]);
    assert_eq!(
        HostGrant::UNBOUNDED.entry(&declared),
        HostEntry::Unbounded,
        "a grant naming no world bounds no entry"
    );
    assert_eq!(
        HostGrant::UNBOUNDED
            .entering(alloc::vec![operator.clone(), seat.clone(), seat])
            .entry(&declared),
        HostEntry::Within(Entry::new(
            World::Declared(ConstantIndex::from(0_usize)),
            alloc::vec![
                World::Declared(ConstantIndex::from(1_usize)),
                World::Declared(ConstantIndex::from(1_usize)),
            ],
        )),
        "the first world is the home and each later one a capability, in order"
    );
    assert_eq!(
        HostGrant::UNBOUNDED
            .entering(alloc::vec![operator, elsewhere])
            .entry(&declared),
        HostEntry::Undeclared,
        "a world the module declares nowhere grants nothing"
    );
}

/// A value kept at a definition's region binder lives longer than every scope
/// the definition opens and no longer than the held region; a capability
/// there is read the same way, and a type naming the binder abstracts a
/// region where the same type at a scope does not (#1221).
#[test]
fn a_bound_region_outlives_every_scope_and_no_held_one_1221()
{
    use gandr_core_term::effect::capability::RegionBinder;

    use super::Reach;
    use super::abstracts;
    use super::binders;
    use super::reaches;

    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let [first, second] = [0_u32, 1].map(|ordinal| Region::Bound(RegionBinder::from(ordinal)));
    let scope = Region::Scoped(RegionDepth::from(2_u32));
    let kept = arena.value_type_kept(integer, first);
    let held = arena.value_type_capability(EffectRow::EMPTY, CapabilityGrade::Durable, second);
    let both = arena.value_type_product(&[kept, held]);
    let at_scope = arena.value_type_kept(integer, scope);
    let reach = |outside| reaches(&arena, TypeNode::Value(kept), outside);
    assert_eq!(
        [
            reach(Region::Held),
            reach(second),
            reach(first),
            reach(scope),
            reach(Region::Scoped(RegionDepth::from(0_u32))),
        ],
        [
            Ok(Reach::Keeps),
            Ok(Reach::Keeps),
            Ok(Reach::Clear),
            Ok(Reach::Clear),
            Ok(Reach::Clear)
        ],
        "kept at r, the value ends before the held region and any other binder's, outlives \
         every scope and lives as long as r"
    );
    assert_eq!(
        reaches(&arena, TypeNode::Value(held), Region::Held),
        Ok(Reach::Mentions),
        "a capability at a region binder ends before the held region"
    );
    assert_eq!(
        [both, at_scope].map(|root| {
            abstracts(&arena, TypeNode::Value(root)).map(|reach| reach != Reach::Clear)
        }),
        [Ok(true), Ok(false)],
        "a type naming a region binder abstracts a region, and one kept at a scope does not"
    );
    assert_eq!(
        binders(&arena, TypeNode::Value(both)),
        Ok(alloc::collections::BTreeSet::from([
            RegionBinder::from(0_u32),
            RegionBinder::from(1_u32)
        ])),
        "both binders are named, the capability's included"
    );
}

/// A region binder kept under any former a type is built from is named,
/// a family's or codata type's quoted argument and a capability's operations
/// included.
#[test]
fn a_binder_is_named_through_every_former()
{
    use alloc::collections::BTreeMap;
    use alloc::collections::BTreeSet;
    use alloc::string::String;
    use alloc::vec::Vec;

    use gandr_core_term::effect::EffectName;
    use gandr_core_term::effect::EffectOp;
    use gandr_core_term::effect::EffectSig;
    use gandr_core_term::effect::capability::RegionBinder;
    use gandr_core_term::world::WorldType;
    use gandr_kernel_strata::Level;
    use gandr_kernel_term::FieldLabel;
    use gandr_kernel_term::Stage;
    use gandr_kernel_term::StageId;

    use super::binders;

    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let unit = arena.value_type_unit();
    let returns_unit = arena.comp_type_returner(unit);
    let zero = arena.value_literal(crate::fixture::integer_literal());
    let binder = RegionBinder::from(0_u32);
    let kept = arena.value_type_kept(integer, Region::Bound(binder));
    let returns_kept = arena.comp_type_returner(kept);
    let quoted = arena.value_quote(kept);
    let quoted_computation = arena.value_quote_computation(returns_kept);
    let operations = EffectSig::new(EffectName::from("Probe"), [EffectOp {
        name: OperationName::from("poke"),
        payload: kept,
        reply: unit,
    }])
    .expect("one operation");
    let rows: Vec<(TypeNode, &str)> = Vec::from([
        (
            TypeNode::Value(
                arena.value_type_data(ConstantIndex::from(0_usize), Vec::from([quoted])),
            ),
            "a family's quoted argument",
        ),
        (
            TypeNode::Value(arena.value_type_data(
                ConstantIndex::from(0_usize),
                Vec::from([quoted_computation]),
            )),
            "a family's quoted computation type",
        ),
        (
            TypeNode::Value(arena.value_type_record(BTreeMap::from([(
                FieldLabel::from(String::from("x")),
                kept,
            )]))),
            "a record field",
        ),
        (
            TypeNode::Value(arena.value_type_sum(&[unit, kept])),
            "a summand",
        ),
        (
            TypeNode::Value(arena.value_type_lift(kept, Level::zero())),
            "a lift",
        ),
        (
            TypeNode::Value(arena.value_type_path(kept, zero, zero)),
            "a path's carrier",
        ),
        (
            TypeNode::Value(arena.value_type_flow(kept, zero, zero)),
            "a flow's carrier",
        ),
        (
            TypeNode::Value(arena.value_type_staged(kept, Stage::At(StageId::from(0_usize)))),
            "a staged base",
        ),
        (
            TypeNode::Value(arena.value_type_static_pi(unit, kept)),
            "a static pi",
        ),
        (
            TypeNode::Value(arena.value_type_sigma(kept, unit)),
            "a sigma",
        ),
        (
            TypeNode::Value(arena.value_type_stack(returns_unit, returns_kept)),
            "a stack",
        ),
        (
            TypeNode::Value(arena.value_type_world(WorldType::At {
                inner: kept,
                world: World::Host,
            })),
            "a value held at a world",
        ),
        (
            TypeNode::Value(arena.value_type_capability(
                EffectRow::singleton(operations.clone()),
                CapabilityGrade::Durable,
                Region::Scoped(RegionDepth::from(1_u32)),
            )),
            "a capability's operations",
        ),
        (
            TypeNode::Computation(
                arena.comp_type_returner_with_effects(unit, EffectRow::singleton(operations)),
            ),
            "a returner's effects",
        ),
        (
            TypeNode::Computation(arena.comp_type_with(&[returns_unit, returns_kept])),
            "a lazy product",
        ),
        (
            TypeNode::Computation(
                arena.comp_type_codata(ConstantIndex::from(0_usize), Vec::from([quoted])),
            ),
            "a codata type's quoted argument",
        ),
        (
            TypeNode::Computation(arena.comp_type_codata(
                ConstantIndex::from(0_usize),
                Vec::from([quoted_computation]),
            )),
            "a codata type's quoted computation type",
        ),
    ]);
    for (root, former) in rows {
        assert_eq!(
            binders(&arena, root),
            Ok(BTreeSet::from([binder])),
            "{former}"
        );
    }
}
