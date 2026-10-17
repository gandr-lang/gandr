use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use super::Binding;
use super::CursorId;
use super::DuplicationFault;
use super::Mode;
use super::ScopeCell;
use super::ScopeId;
use super::Walk;
use crate::DuplicationPolicy;
use crate::Overlay;
use crate::OverlayId;
use crate::ValueGraft;
use crate::ValueNode;

#[test]
fn nullary_grafts_cannot_stand_in_an_abstraction_prefix()
{
    for mode in [
        Mode::Prefix {
            cursor: CursorId(0),
        },
        Mode::DryPrefix {
            cursor: CursorId(0),
        },
    ] {
        let mut overlay = Overlay::new();
        let unit = overlay
            .mint_value(ValueNode::Grafted(ValueGraft::Unit))
            .expect("a unit has no children");
        let mut walk = Walk {
            overlay: &mut overlay,
            policy: DuplicationPolicy::default(),
            reached: BTreeMap::new(),
            tasks: Vec::new(),
            results: Vec::new(),
            frames: Vec::new(),
            scopes: Vec::from([ScopeCell {
                binding: Binding::Empty,
                parent: ScopeId::EMPTY,
            }]),
            cursors: Vec::new(),
        };
        assert_eq!(
            Err(DuplicationFault::MachineInvariant),
            walk.graft(OverlayId::Value(unit), ScopeId::EMPTY, mode)
        );
    }
}

#[test]
fn scope_distances_and_typed_results_keep_their_boundaries()
{
    use super::Bound;
    use super::CompGraft;
    use super::CompNode;
    use super::Cursor;
    use super::FrameIndex;
    use super::RibCount;
    use super::Shape;
    use super::ShareDistance;
    use super::SharePosition;
    use super::Taken;
    use super::innermost;
    let mut overlay = Overlay::new();
    let value = overlay
        .mint_value(ValueNode::Grafted(ValueGraft::Unit))
        .expect("the unit is closed");
    let comp = overlay
        .mint_computation(CompNode::Grafted(CompGraft::Return(value)))
        .expect("the value lives");
    let legs = [OverlayId::Value(value), OverlayId::Computation(comp)];
    assert_eq!(
        Ok(OverlayId::Computation(comp)),
        innermost(&legs, ShareDistance::from(0_u32))
    );
    assert_eq!(
        Ok(OverlayId::Value(value)),
        innermost(&legs, ShareDistance::from(1_u32))
    );
    for distance in [2_u32, u32::MAX] {
        assert_eq!(
            Err(DuplicationFault::MachineInvariant),
            innermost(&legs, ShareDistance::from(distance))
        );
    }
    let mut walk = Walk {
        overlay: &mut overlay,
        policy: DuplicationPolicy::default(),
        reached: BTreeMap::new(),
        tasks: Vec::new(),
        results: Vec::new(),
        frames: Vec::new(),
        scopes: Vec::from([ScopeCell {
            binding: Binding::Empty,
            parent: ScopeId::EMPTY,
        }]),
        cursors: Vec::new(),
    };
    let first_binding = Binding::Kept {
        frame: FrameIndex(2),
    };
    let first = walk.bind(ScopeId::EMPTY, first_binding);
    let separate = walk.bind(ScopeId::EMPTY, Binding::Covered);
    let inner_binding = Binding::Inlined {
        leg: OverlayId::Value(value),
        scope: first,
    };
    let inner = walk.bind(first, inner_binding);
    assert_eq!(
        Ok(inner_binding),
        walk.binding(inner, ShareDistance::from(0_u32))
    );
    assert_eq!(
        Ok(first_binding),
        walk.binding(inner, ShareDistance::from(1_u32))
    );
    assert_eq!(
        Ok(Binding::Covered),
        walk.binding(separate, ShareDistance::from(0_u32))
    );
    for distance in [2_u32, u32::MAX] {
        assert_eq!(
            Err(DuplicationFault::MachineInvariant),
            walk.binding(inner, ShareDistance::from(distance))
        );
    }
    assert_eq!(
        Err(DuplicationFault::MachineInvariant),
        walk.binding(ScopeId(usize::MAX), ShareDistance::from(0_u32))
    );
    walk.results
        .extend([OverlayId::Value(value), OverlayId::Computation(comp)]);
    assert_eq!(Err(DuplicationFault::MachineInvariant), walk.value());
    assert_eq!(Err(DuplicationFault::MachineInvariant), walk.computation());
    assert_eq!(Err(DuplicationFault::MachineInvariant), walk.value());
    walk.results
        .extend([OverlayId::Computation(comp), OverlayId::Value(value)]);
    assert_eq!(Ok(value), walk.value());
    assert_eq!(Ok(comp), walk.computation());
    walk.frames.extend([Taken(2), Taken(5)]);
    let outer = walk
        .point(OverlayId::Value(value), FrameIndex(0))
        .expect("the outer frame lives");
    let inner = walk
        .point(OverlayId::Computation(comp), FrameIndex(1))
        .expect("the inner frame lives");
    assert_eq!(
        Ok(Shape::Bound(Bound {
            distance: ShareDistance::from(1_u32),
            position: SharePosition::from(2_u32)
        })),
        walk.overlay.shape(outer)
    );
    assert_eq!(
        Ok(Shape::Bound(Bound {
            distance: ShareDistance::from(0_u32),
            position: SharePosition::from(5_u32)
        })),
        walk.overlay.shape(inner)
    );
    assert_eq!(Vec::from([Taken(3), Taken(6)]), walk.frames);
    *walk.frames.get_mut(0).expect("the outer frame lives") = Taken(u32::MAX);
    assert_eq!(
        Err(DuplicationFault::MachineInvariant),
        walk.point(OverlayId::Value(value), FrameIndex(0))
    );
    assert_eq!(
        Err(DuplicationFault::MachineInvariant),
        walk.point(OverlayId::Value(value), FrameIndex(usize::MAX))
    );
    assert_eq!(Some(&Taken(u32::MAX)), walk.frames.first());
    let full = walk.cursor(FrameIndex(0));
    walk.cursors.get_mut(full.0).expect("the cursor lives").met = RibCount(u32::MAX);
    assert_eq!(Err(DuplicationFault::MachineInvariant), walk.open_rib(full));
    assert_eq!(
        Err(DuplicationFault::MachineInvariant),
        walk.open_rib(CursorId(usize::MAX))
    );
    assert_eq!(2, walk.frames.len());
    let fresh = walk.cursor(FrameIndex(2));
    walk.open_rib(fresh)
        .expect("a fresh cursor opens its first frame");
    assert_eq!(
        Some(&Cursor {
            ribs: FrameIndex(2),
            met: RibCount(1)
        }),
        walk.cursors.get(fresh.0)
    );
    assert_eq!(Some(&Taken::default()), walk.frames.get(2));
    assert_eq!(
        Some(&Cursor {
            ribs: FrameIndex(0),
            met: RibCount(u32::MAX)
        }),
        walk.cursors.get(full.0)
    );
}

#[test]
fn surveys_lower_only_the_binders_above_each_child()
{
    use super::BinderDepth;
    use super::Child;
    use super::CompGraft;
    use super::CompNode;
    use super::DeBruijnIndex;
    use super::InnerFrames;
    use super::Lowering;
    use super::Outward;
    use super::RibSite;
    use super::Under;
    use super::Zone;
    use super::survey;
    let mut overlay = Overlay::new();
    let one = overlay
        .mint_value(ValueNode::Grafted(ValueGraft::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(1_u32),
        }))
        .expect("a variable has no children");
    let branch_one = overlay
        .mint_value(ValueNode::Grafted(ValueGraft::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(1_u32),
        }))
        .expect("a second occurrence has its own overlay node");
    let two = overlay
        .mint_value(ValueNode::Grafted(ValueGraft::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(2_u32),
        }))
        .expect("a variable has no children");
    let linear = overlay
        .mint_value(ValueNode::Grafted(ValueGraft::Variable {
            zone: Zone::Linear,
            index: DeBruijnIndex::from(0_u32),
        }))
        .expect("a variable has no children");
    let left = overlay
        .mint_computation(CompNode::Grafted(CompGraft::Return(branch_one)))
        .expect("the child lives");
    let right = overlay
        .mint_computation(CompNode::Grafted(CompGraft::Return(two)))
        .expect("the child lives");
    let case = overlay
        .mint_computation(CompNode::Grafted(CompGraft::Case {
            scrutinee: one,
            on_left: left,
            on_right: right,
        }))
        .expect("the children live");
    let lambda = overlay
        .mint_computation(CompNode::Grafted(CompGraft::Lambda(case)))
        .expect("the body lives");
    overlay
        .validate(OverlayId::Computation(lambda))
        .expect("the fixture uses each overlay node once");
    assert_eq!(
        Ok(Under {
            listed: [
                Some(Child {
                    node: OverlayId::Value(one),
                    binders: Lowering::NONE
                }),
                Some(Child {
                    node: OverlayId::Computation(left),
                    binders: Lowering::ONE
                }),
                Some(Child {
                    node: OverlayId::Computation(right),
                    binders: Lowering::ONE
                }),
            ]
        }),
        Under::of(&overlay, OverlayId::Computation(case))
    );
    let core = gandr_core_term::CoreArena::new();
    let reached = survey(&overlay, &core, OverlayId::Computation(lambda))
        .expect("the overlay has no unresolved shares");
    assert_eq!(
        Outward::single(DeBruijnIndex::from(0_u32)),
        reached
            .get(&OverlayId::Computation(lambda))
            .expect("the root was surveyed")
            .reads
    );
    let mut case_reads = Outward::single(DeBruijnIndex::from(0_u32));
    case_reads.join_lowered(&Outward::single(DeBruijnIndex::from(1_u32)), Lowering::NONE);
    assert_eq!(
        case_reads,
        reached
            .get(&OverlayId::Computation(case))
            .expect("the case was surveyed")
            .reads
    );
    assert_eq!(
        Outward::default(),
        reached
            .get(&OverlayId::Computation(lambda))
            .expect("the root was surveyed")
            .escapes
    );
    let linear_reach =
        survey(&overlay, &core, OverlayId::Value(linear)).expect("a linear variable surveys");
    assert_eq!(
        Outward::default(),
        linear_reach
            .get(&OverlayId::Value(linear))
            .expect("the root was surveyed")
            .reads
    );
    let site = RibSite {
        depth: BinderDepth(5),
        inner: InnerFrames(7),
    };
    assert_eq!(
        Ok(RibSite {
            depth: BinderDepth(6),
            inner: InnerFrames(7)
        }),
        site.under(Lowering::ONE)
    );
    assert_eq!(
        Ok(RibSite {
            depth: BinderDepth(5),
            inner: InnerFrames(8)
        }),
        site.within()
    );
    let deepest = RibSite {
        depth: BinderDepth(u32::MAX),
        inner: InnerFrames(7),
    };
    assert_eq!(Ok(deepest), deepest.under(Lowering::NONE));
    assert_eq!(
        Err(DuplicationFault::MachineInvariant),
        deepest.under(Lowering::ONE)
    );
    assert_eq!(
        Err(DuplicationFault::MachineInvariant),
        (RibSite {
            depth: BinderDepth(5),
            inner: InnerFrames(u32::MAX)
        })
        .within()
    );
}

#[test]
fn assembly_preserves_formers_payloads_and_child_order()
{
    use super::CompGraft;
    use super::CompNode;
    use super::DeBruijnIndex;
    use super::Zone;
    let mut overlay = Overlay::new();
    let original = overlay
        .mint_value(ValueNode::Grafted(ValueGraft::Variable {
            zone: Zone::Linear,
            index: DeBruijnIndex::from(3_u32),
        }))
        .expect("a variable has no children");
    let unit = overlay
        .mint_value(ValueNode::Grafted(ValueGraft::Unit))
        .expect("a unit has no children");
    let other = overlay
        .mint_value(ValueNode::Grafted(ValueGraft::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(7_u32),
        }))
        .expect("a variable has no children");
    let pair = overlay
        .mint_value(ValueNode::Grafted(ValueGraft::Pair(original, unit)))
        .expect("both children live");
    let left = overlay
        .mint_computation(CompNode::Grafted(CompGraft::Return(unit)))
        .expect("the child lives");
    let forced_variable = overlay
        .mint_value(ValueNode::Grafted(ValueGraft::Variable {
            zone: Zone::Linear,
            index: DeBruijnIndex::from(3_u32),
        }))
        .expect("the force has its own occurrence node");
    let right = overlay
        .mint_computation(CompNode::Grafted(CompGraft::Force(forced_variable)))
        .expect("the child lives");
    let case = overlay
        .mint_computation(CompNode::Grafted(CompGraft::Case {
            scrutinee: original,
            on_left: left,
            on_right: right,
        }))
        .expect("the children live");
    overlay
        .validate(OverlayId::Computation(case))
        .expect("the source case has no implicit node reuse");
    let mut walk = Walk {
        overlay: &mut overlay,
        policy: DuplicationPolicy::default(),
        reached: BTreeMap::new(),
        tasks: Vec::new(),
        results: Vec::new(),
        frames: Vec::new(),
        scopes: Vec::from([ScopeCell {
            binding: Binding::Empty,
            parent: ScopeId::EMPTY,
        }]),
        cursors: Vec::new(),
    };
    walk.results
        .extend([OverlayId::Value(unit), OverlayId::Value(other)]);
    let rebuilt = walk
        .assemble(OverlayId::Value(pair))
        .expect("the rebuilt pair children are ready");
    assert!(
        matches!(rebuilt, OverlayId::Value(id) if walk.overlay.value(id) == Some(&ValueNode::Grafted(ValueGraft::Pair(unit, other))))
    );
    let copied = walk
        .assemble(OverlayId::Value(original))
        .expect("a variable has no children to pop");
    assert!(
        matches!(copied, OverlayId::Value(id) if walk.overlay.value(id) == Some(&ValueNode::Grafted(ValueGraft::Variable { zone: Zone::Linear, index: DeBruijnIndex::from(3_u32) })))
    );
    walk.results.extend([
        OverlayId::Value(other),
        OverlayId::Computation(right),
        OverlayId::Computation(left),
    ]);
    let rebuilt = walk
        .assemble(OverlayId::Computation(case))
        .expect("the rebuilt case children are ready");
    assert!(
        matches!(rebuilt, OverlayId::Computation(id) if walk.overlay.computation(id) == Some(&CompNode::Grafted(CompGraft::Case { scrutinee: other, on_left: right, on_right: left })))
    );
    walk.results.push(OverlayId::Value(unit));
    assert_eq!(
        Err(DuplicationFault::MachineInvariant),
        walk.assemble(OverlayId::Value(pair))
    );
}

/// A walk over `overlay` with nothing surveyed, queued or open but the empty
/// scope.
///
/// # Specification
/// trivial.
fn fresh(overlay: &mut Overlay) -> Walk<'_>
{
    Walk {
        overlay,
        policy: DuplicationPolicy::default(),
        reached: BTreeMap::new(),
        tasks: Vec::new(),
        results: Vec::new(),
        frames: Vec::new(),
        scopes: Vec::from([ScopeCell {
            binding: Binding::Empty,
            parent: ScopeId::EMPTY,
        }]),
        cursors: Vec::new(),
    }
}

#[test]
fn a_share_is_spine_only_where_an_escape_reaches_inside_the_inner_frames()
{
    use super::BinderDepth;
    use super::InnerFrames;
    use super::Reach;
    use super::RibSite;
    use super::ShareDistance;
    use crate::free::Outward;
    use crate::policy::SharedPart;

    let mut overlay = Overlay::new();
    let unit = overlay
        .mint_value(ValueNode::Grafted(ValueGraft::Unit))
        .expect("the unit is closed");
    let node = OverlayId::Value(unit);
    let mut walk = fresh(&mut overlay);
    let _absent = walk.reached.insert(node, Reach {
        reads: Outward::default(),
        escapes: Outward::single(ShareDistance::from(2_u32)),
    });
    let site = |inner| RibSite {
        depth: BinderDepth(0_u32),
        inner: InnerFrames(inner),
    };
    assert_eq!(
        Ok(SharedPart::Rib),
        walk.part(node, site(2_u32)),
        "an escape as far as the inner frames reach leaves a rib"
    );
    assert_eq!(
        Ok(SharedPart::Spine),
        walk.part(node, site(3_u32)),
        "one that stops inside them is spine"
    );
}

#[test]
fn a_walk_that_ends_with_a_frame_open_is_refused()
{
    use super::Taken;

    let mut overlay = Overlay::new();
    let unit = overlay
        .mint_value(ValueNode::Grafted(ValueGraft::Unit))
        .expect("the unit is closed");
    let mut walk = fresh(&mut overlay);
    walk.frames.push(Taken(0_u32));
    assert_eq!(
        Err(DuplicationFault::MachineInvariant),
        walk.run(OverlayId::Value(unit))
    );
}
