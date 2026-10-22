use alloc::vec::Vec;

use gandr_core_term::CoreArena;
use gandr_core_term::Zone;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::GlobalIndex;

use super::DomainArena;
use super::DomainFault;
use super::NeutralId;
use super::RunWatermark;
use crate::closure::Environment;
use crate::domain::BinderLevel;
use crate::domain::CompTermFace;
use crate::domain::Elimination;
use crate::domain::Glued;
use crate::domain::NeutralHead;
use crate::domain::TermFace;
use crate::domain::Unfolding;
use crate::guard::Guard;

#[test]
fn a_child_id_is_strictly_below_its_parent()
{
    let mut arena = DomainArena::new();
    let unit = arena.value_unit(TermFace::Reduced);
    let pair = arena.value_tuple([unit, unit], TermFace::Reduced);
    assert!(
        unit < pair,
        "constructor-only minting orders child below parent"
    );
}

#[test]
fn truncating_to_a_watermark_drops_later_nodes()
{
    let mut arena = DomainArena::new();
    let kept = arena.value_unit(TermFace::Reduced);
    let mark = arena.watermark();
    let dropped = arena.value_unit(TermFace::Reduced);
    let later_mark = arena.watermark();
    arena.truncate_to(mark);
    assert!(
        arena.value(kept).is_some(),
        "content below the mark survives"
    );
    assert!(
        arena.value(dropped).is_none(),
        "an id minted past the mark dangles after truncation"
    );
    arena.truncate_to(mark);
    assert!(
        arena.value(kept).is_some(),
        "truncating twice to the same mark is a no-op"
    );
    arena.truncate_to(later_mark);
    assert_eq!(
        mark,
        arena.watermark(),
        "a stale mark cannot regrow the arena"
    );
    assert!(arena.value(dropped).is_none());
}

#[test]
fn truncating_to_the_floor_empties_every_family()
{
    let mut arena = DomainArena::new();
    let floor = arena.watermark();
    let neutral = arena
        .neutral_node(
            NeutralHead::Constant(ConstantIndex::from(0_usize)),
            Vec::new(),
            Unfolding::Unforced(GlobalIndex::from(0_u32)),
        )
        .expect("a declaration head may carry a body");
    let mut core = CoreArena::new();
    let produced = core.value_unit();
    let body = core.computation_return(produced);
    let closure = arena.comp_closure_node(body, Environment::new());
    let unit = arena.value_unit(TermFace::Reduced);
    let thunk = arena.value_thunk(closure, TermFace::Reduced);
    let returner = arena.comp_return(unit, CompTermFace::Reduced);
    let value_closure =
        arena.value_closure_node(crate::ValueBody::Source(produced), Environment::new());
    let target = arena.hold_level(super::Level::zero());
    assert!(arena.value_closure(value_closure).is_some());
    assert!(arena.comp_closure(closure).is_some());
    assert!(arena.level(target).is_some());
    assert!(arena.neutral(neutral).is_some());
    assert!(arena.computation(returner).is_some());
    assert!(arena.value(thunk).is_some());

    arena.truncate_to(floor);
    assert_eq!(
        RunWatermark::default(),
        arena.watermark(),
        "the floor is the empty arena, which is what a run's teardown is"
    );
    assert!(arena.value(unit).is_none());
    assert!(arena.value(thunk).is_none());
    assert!(arena.computation(returner).is_none());
    assert!(arena.neutral(neutral).is_none());
    assert!(arena.comp_closure(closure).is_none());
    assert!(arena.value_closure(value_closure).is_none());
    assert!(arena.level(target).is_none());
    assert_eq!(Err(DomainFault::Dangling), arena.value_guard(unit));
    assert_eq!(Err(DomainFault::Dangling), arena.comp_guard(returner));
    assert_eq!(Err(DomainFault::Dangling), arena.neutral_guard(neutral));
}

#[test]
fn a_value_neutral_refuses_a_computation_spine()
{
    let mut arena = DomainArena::new();
    let spineless = arena
        .neutral_node(
            NeutralHead::Module(ConstantIndex::from(0_usize)),
            Vec::new(),
            Unfolding::Rigid,
        )
        .expect("a module form is a rigid head");
    let stood = arena.value_neutral(spineless, TermFace::Reduced);
    assert!(
        stood.is_ok(),
        "a module form stands in a value position as a rigid neutral"
    );

    let unit = arena.value_unit(TermFace::Reduced);
    let operated = arena
        .neutral_node(
            NeutralHead::Constant(ConstantIndex::from(1_usize)),
            Vec::from([Elimination::StaticApply(unit)]),
            Unfolding::Rigid,
        )
        .expect("a statically applied neutral mints");
    assert!(
        arena.value_neutral(operated, TermFace::Reduced).is_ok(),
        "a static application is the one value eliminator, so its neutral stands as a value"
    );
    let applied = arena
        .neutral_node(
            NeutralHead::Constant(ConstantIndex::from(1_usize)),
            Vec::from([Elimination::Apply(unit)]),
            Unfolding::Rigid,
        )
        .expect("a spined neutral mints; it just cannot stand in a value slot");
    assert_eq!(
        Err(DomainFault::ValueNeutralEliminatesComputation),
        arena.value_neutral(applied, TermFace::Reduced),
        "an applied neutral is a stuck computation and cannot stand in a value slot"
    );
    assert_eq!(
        Err(DomainFault::Dangling),
        arena.value_neutral(NeutralId(99_u32), TermFace::Reduced),
        "and an unresolvable neutral is refused rather than minted over"
    );
}

#[test]
fn a_head_that_cannot_unfold_carries_no_body()
{
    let mut arena = DomainArena::new();
    let unit = arena.value_unit(TermFace::Reduced);
    let bound = NeutralHead::Variable {
        zone: Zone::Intuitionistic,
        level: BinderLevel::from(0_u32),
    };
    let module = NeutralHead::Module(ConstantIndex::from(0_usize));
    let declaration = NeutralHead::Constant(ConstantIndex::from(0_usize));
    let loaded = [
        Unfolding::Unforced(GlobalIndex::from(0_u32)),
        Unfolding::Forced(Glued::Value(unit)),
    ];

    for head in [bound, module] {
        assert!(
            arena
                .neutral_node(head, Vec::new(), Unfolding::Rigid)
                .is_ok(),
            "a head with no definition behind it mints rigid"
        );
        for face in loaded {
            assert_eq!(
                Err(DomainFault::RigidHeadCarriesBody),
                arena.neutral_node(head, Vec::new(), face),
                "and is refused a body it could not have, at either loaded face"
            );
        }
    }
    assert!(
        arena
            .neutral_node(declaration, Vec::new(), Unfolding::Rigid)
            .is_ok(),
        "a declaration head mints rigid — an axiom, or a definition sealed here"
    );
    for face in loaded {
        assert!(
            arena.neutral_node(declaration, Vec::new(), face).is_ok(),
            "and it is the one head a body may stand behind"
        );
    }
}

#[test]
fn forcing_a_dangling_neutral_is_refused()
{
    let mut arena = DomainArena::new();
    let unit = arena.value_unit(TermFace::Reduced);
    assert_eq!(
        Err(DomainFault::Dangling),
        arena.force_neutral(NeutralId(4_u32), Glued::Value(unit)),
        "an unresolvable neutral is refused under the same vocabulary as any other \
             unresolvable id"
    );
    let rigid = arena
        .neutral_node(
            NeutralHead::Constant(ConstantIndex::from(0_usize)),
            Vec::new(),
            Unfolding::Rigid,
        )
        .expect("an opaque declaration is a rigid head");
    assert_eq!(
        Err(DomainFault::NeutralIsRigid),
        arena.force_neutral(rigid, Glued::Value(unit)),
        "and a resolvable neutral's own refusal arrives translated, not nested"
    );
    let unforced = arena
        .neutral_node(
            NeutralHead::Constant(ConstantIndex::from(1_usize)),
            Vec::new(),
            Unfolding::Unforced(GlobalIndex::from(0_u32)),
        )
        .expect("a declaration head may carry a body");
    assert_eq!(Ok(()), arena.force_neutral(unforced, Glued::Value(unit)));
    assert_eq!(
        Err(DomainFault::NeutralAlreadyForced),
        arena.force_neutral(unforced, Glued::Value(unit)),
        "as does the second-force refusal"
    );
}

#[test]
fn a_neutral_is_rigid_only_without_a_body_or_a_closure()
{
    let mut core = CoreArena::new();
    let mut arena = DomainArena::new();
    let argument = arena.value_unit(TermFace::Reduced);
    let head = NeutralHead::Variable {
        zone: Zone::Intuitionistic,
        level: BinderLevel::from(0_u32),
    };
    let applied = arena
        .neutral_node(
            head,
            Vec::from([Elimination::Apply(argument)]),
            Unfolding::Rigid,
        )
        .expect("a variable head stands rigid");
    assert!(
        matches!(arena.neutral_guard(applied), Ok(Guard::Rigid(_))),
        "a rigid head applied to a rigid argument is rigid"
    );

    let defined = arena
        .neutral_node(
            NeutralHead::Constant(ConstantIndex::from(0_usize)),
            Vec::from([Elimination::Apply(argument)]),
            Unfolding::Unforced(GlobalIndex::from(0_u32)),
        )
        .expect("a declaration head may carry a body");
    assert_eq!(
        Ok(Guard::Flexible),
        arena.neutral_guard(defined),
        "a head with a body to unfold is flexible"
    );
    let unit = core.value_unit();
    let body = core.computation_return(unit);
    let continuation = arena.comp_closure_node(body, Environment::new());
    let bound = arena
        .neutral_node(
            head,
            Vec::from([
                Elimination::Apply(argument),
                Elimination::Bind(continuation),
            ]),
            Unfolding::Rigid,
        )
        .expect("a variable head stands rigid");
    assert_eq!(
        Ok(Guard::Flexible),
        arena.neutral_guard(bound),
        "and so is a spine stacking a closure"
    );
    let stuck = arena.comp_neutral(bound, CompTermFace::Reduced);
    assert_eq!(
        Ok(Guard::Flexible),
        arena.comp_guard(stuck),
        "and the computation standing for it inherits the word"
    );
}

#[test]
fn index_conversion_preserves_the_range_before_saturating()
{
    let ceiling = usize::try_from(u32::MAX).expect("supported platforms hold an index");
    for index in [0_u32, 1_u32, u32::MAX - 1, u32::MAX] {
        let length = usize::try_from(index).expect("the index fits");
        assert_eq!(index, super::id_index(super::ArenaLength(length)).0);
        assert_eq!(length, super::id_offset(super::ArenaIndex(index)).0);
    }
    if let Some(above) = ceiling.checked_add(1) {
        assert_eq!(u32::MAX, super::id_index(super::ArenaLength(above)).0);
    }
}

#[test]
fn guard_flexibility_survives_the_entire_spine()
{
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let body = core.computation_return(unit);
    let mut arena = DomainArena::new();
    let closure = arena.comp_closure_node(body, Environment::new());
    let flexible = arena.value_thunk(closure, TermFace::Reduced);
    let rigid = arena.value_unit(TermFace::Reduced);
    let dangling = super::DomainValueId(u32::MAX);
    for spine in [
        [Elimination::Apply(dangling), Elimination::Force],
        [Elimination::Apply(flexible), Elimination::Apply(rigid)],
        [Elimination::StaticApply(flexible), Elimination::Force],
        [
            Elimination::Case(arena.hold_branches([closure, closure])),
            Elimination::Force,
        ],
    ] {
        let neutral = arena
            .neutral_node(
                NeutralHead::Constant(ConstantIndex::from(0_usize)),
                Vec::from(spine),
                Unfolding::Rigid,
            )
            .expect("every spine is admissible on a rigid declaration head");
        assert_eq!(Ok(Guard::Flexible), arena.neutral_guard(neutral));
    }
}

#[test]
fn native_field_spans_obey_truncation()
{
    let mut arena = DomainArena::new();
    let first = arena.value_unit(TermFace::Reduced);
    let second = arena.value_tuple([first, first], TermFace::Reduced);
    let kept = arena.hold_fields([first, second]);
    let mark = arena.watermark();
    let discarded = arena.hold_fields([second, first, second]);
    arena.truncate_to(mark);
    assert_eq!(arena.fields(kept), Ok([first, second].as_slice()));
    assert_eq!(arena.fields(discarded), Err(DomainFault::Dangling));
    let replacement = arena.hold_fields([first]);
    assert_eq!(arena.fields(replacement), Ok([first].as_slice()));
    assert_eq!(arena.fields(kept), Ok([first, second].as_slice()));
    arena.truncate_to(mark);
    assert_eq!(arena.fields(replacement), Err(DomainFault::Dangling));
}

#[test]
fn a_tuple_s_components_are_its_fields_in_order_and_no_other_former_has_any()
{
    let mut arena = DomainArena::new();
    let unit = arena.value_unit(TermFace::Reduced);
    let inner = arena.value_tuple([unit, unit], TermFace::Reduced);
    let pair = arena.value_tuple([inner, unit], TermFace::Reduced);
    let here = arena.value_here(pair, TermFace::Reduced);
    let nil = arena.value_list_nil(TermFace::Reduced);
    let read = |id| {
        arena
            .value(id)
            .and_then(|value| arena.components(value))
            .map(<[_]>::to_vec)
    };
    assert_eq!(
        read(pair),
        Some(Vec::from([inner, unit])),
        "a tuple's components are its fields, in the order written"
    );
    assert_eq!(read(unit), Some(Vec::new()), "the unit is the empty tuple");
    assert_eq!(
        read(here),
        None,
        "a reflexivity over a tuple has no components"
    );
    assert_eq!(read(nil), None, "nor has an empty list");
}

#[test]
fn case_branch_spans_obey_truncation()
{
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let body = core.computation_return(unit);
    let mut arena = DomainArena::new();
    let first = arena.comp_closure_node(body, Environment::new());
    let second = arena.comp_closure_node(body, Environment::new());
    let kept = arena.hold_branches([first, second]);
    let mark = arena.watermark();
    let discarded = arena.hold_branches([second, first, second]);
    arena.truncate_to(mark);
    assert_eq!(arena.branches(kept), Ok([first, second].as_slice()));
    assert_eq!(arena.branches(discarded), Err(DomainFault::Dangling));
    let replacement = arena.hold_branches([second]);
    assert_eq!(arena.branches(replacement), Ok([second].as_slice()));
    assert_eq!(arena.branches(kept), Ok([first, second].as_slice()));
    arena.truncate_to(mark);
    assert_eq!(arena.branches(replacement), Err(DomainFault::Dangling));
}

#[test]
fn a_hole_or_mark_head_is_never_rigid()
{
    let mut core = CoreArena::new();
    let hole = core.value_hole(gandr_core_term::hole::HoleId::from(0_u32));
    let mut arena = DomainArena::new();
    let closure =
        arena.value_closure_node(crate::closure::ValueBody::Source(hole), Environment::new());
    let suspended = crate::domain::Suspended::Value(closure);
    for head in [
        NeutralHead::Hole {
            hole: gandr_core_term::hole::HoleId::from(0_u32),
            closure: suspended,
        },
        NeutralHead::Mark {
            mark: gandr_core_term::hole::MarkIndex::from(0_u32),
            closure: suspended,
        },
    ] {
        let neutral = arena
            .neutral_node(head, Vec::new(), Unfolding::Rigid)
            .expect("a hole or a mark mints rigid-faced");
        assert_eq!(Ok(Guard::Flexible), arena.neutral_guard(neutral));
        assert_eq!(
            Err(DomainFault::RigidHeadCarriesBody),
            arena.neutral_node(
                head,
                Vec::new(),
                Unfolding::Unforced(GlobalIndex::from(0_u32))
            ),
            "and no definition stands behind it"
        );
    }
    let variable = arena
        .neutral_node(
            NeutralHead::Variable {
                zone: Zone::Intuitionistic,
                level: BinderLevel::from(0_u32),
            },
            Vec::new(),
            Unfolding::Rigid,
        )
        .expect("a variable mints rigid");
    assert!(matches!(arena.neutral_guard(variable), Ok(Guard::Rigid(_))));
}
