//! Component-trace pairing, whole-head units, and selected refutations.

use proptest::prelude::*;

use super::ConversionDecision;
use super::CoreArena;
use super::KernelVerdict;
use super::MachineVerdict;
use super::Name;
use super::ReplayDecline;
use super::ReplayNode;
use super::ReplayRefusal;
use super::Sides;
use super::SubgoalPosition;
use super::TracePosition;
use super::Vec;
use super::World;
use super::kernel_decision;
use super::ladders;
use super::named;

#[test]
fn concatenation_consumes_the_first_component_before_the_second()
{
    let mut core = CoreArena::new();
    let first_body = core.value_unit();
    let second_body = core.value_unit();
    let unit = core.value_unit();
    let zero = core.value_constant(Name::Zero.constant());
    let one = core.value_constant(Name::One.constant());
    let pair = Sides::Values(core.value_pair(zero, one), core.value_pair(unit, unit));
    let world = World::new(core, &[(Name::Zero, first_body), (Name::One, second_body)]);
    let mut concatenated = Vec::new();
    for (name, reference) in [(Name::Zero, zero), (Name::One, one)] {
        let sides = Sides::Values(reference, unit);
        let (verdict, trace) = world.traced(sides);
        assert_eq!(MachineVerdict::Convertible, verdict);
        assert_eq!(
            [
                ConversionDecision::Unfold {
                    constant: named(name)
                },
                ConversionDecision::ReduceLeft { redex: named(name) },
            ],
            trace.as_slice(),
        );
        assert_eq!(
            KernelVerdict::Convertible,
            world.replayed(sides, verdict, &trace)
        );
        concatenated.extend(trace);
    }
    assert_eq!(
        KernelVerdict::Convertible,
        world.replayed(pair, MachineVerdict::Convertible, &concatenated),
    );
    concatenated.rotate_left(2);
    assert_eq!(
        KernelVerdict::Declined(ReplayDecline::Refused(ReplayRefusal::Inapplicable {
            at: TracePosition::from(1_usize),
        })),
        world.replayed(pair, MachineVerdict::Convertible, &concatenated),
        "the reduction names the second component while the first goal is current",
    );
}

#[test]
fn every_pair_of_generated_ladder_traces_replays()
{
    let (mut world, rungs) = ladders();
    for &first in &rungs {
        for &second in &rungs {
            let (Sides::Values(first_left, first_right), Sides::Values(second_left, second_right)) =
                (first, second)
            else {
                panic!("the ladder generates value claims");
            };
            let pair = Sides::Values(
                world.core.value_pair(first_left, second_left),
                world.core.value_pair(first_right, second_right),
            );
            let mut concatenated = Vec::new();
            for sides in [first, second] {
                let (verdict, trace) = world.traced(sides);
                assert_eq!(MachineVerdict::Convertible, verdict);
                assert_eq!(
                    KernelVerdict::Convertible,
                    world.replayed(sides, verdict, &trace)
                );
                concatenated.extend(trace);
            }
            assert_eq!(
                KernelVerdict::Convertible,
                world.replayed(pair, MachineVerdict::Convertible, &concatenated),
                "{first:?}, {second:?}: {concatenated:?}",
            );
        }
    }
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 256,
        rng_seed: proptest::test_runner::RngSeed::Fixed(0x7061_6972),
        .. ProptestConfig::default()
    })]

    /// Independent unfolding traces concatenate through bounded pair contexts.
    #[test]
    fn generated_component_traces_concatenate(
        first_context in proptest::collection::vec(any::<bool>(), 0..8),
        second_context in proptest::collection::vec(any::<bool>(), 0..8),
        first_shared in any::<bool>(),
        reverse_first in any::<bool>(),
        reverse_second in any::<bool>(),
    ) {
        let mut core = CoreArena::new();
        let body = core.value_unit();
        let components = [
            (Name::Zero, first_context, first_shared, reverse_first),
            (Name::One, second_context, false, reverse_second),
        ].map(|(name, context, shared, reverse)| {
            let mut left = if shared { core.value_unit() } else { core.value_constant(name.constant()) };
            let mut right = core.value_unit();
            for before in context {
                let left_unit = core.value_unit();
                let right_unit = core.value_unit();
                (left, right) = if before {
                    (core.value_pair(left_unit, left), core.value_pair(right_unit, right))
                } else {
                    (core.value_pair(left, left_unit), core.value_pair(right, right_unit))
                };
            }
            if reverse { (right, left) } else { (left, right) }
        });
        let [(first_left, first_right), (second_left, second_right)] = components;
        let pair = Sides::Values(core.value_pair(first_left, second_left), core.value_pair(first_right, second_right));
        let world = World::new(core, &[(Name::Zero, body), (Name::One, body)]);
        let mut concatenated = Vec::new();
        for (left, right) in components {
            let sides = Sides::Values(left, right);
            let (verdict, trace) = world.traced(sides);
            prop_assert_eq!(MachineVerdict::Convertible, verdict);
            prop_assert_eq!(KernelVerdict::Convertible, world.replayed(sides, verdict, &trace));
            concatenated.extend(trace);
        }
        prop_assert_eq!(KernelVerdict::Convertible, world.replayed(pair, MachineVerdict::Convertible, &concatenated));
    }

    /// Alpha equality closes the enclosing pair before the second unit is read.
    #[test]
    fn an_alpha_equal_pair_uses_its_unit_not_component_concatenation(
        contexts in proptest::array::uniform2(proptest::collection::vec(any::<bool>(), 0..8)),
    ) {
        let mut core = CoreArena::new();
        let components = contexts.map(|context| {
            let mut left = core.value_unit();
            let mut right = core.value_unit();
            for before in context {
                let left_unit = core.value_unit();
                let right_unit = core.value_unit();
                (left, right) = if before {
                    (core.value_pair(left_unit, left), core.value_pair(right_unit, right))
                } else {
                    (core.value_pair(left, left_unit), core.value_pair(right, right_unit))
                };
            }
            (left, right)
        });
        let [(first_left, first_right), (second_left, second_right)] = components;
        let pair = Sides::Values(core.value_pair(first_left, second_left), core.value_pair(first_right, second_right));
        let world = World::new(core, &[]);
        let unit = [ConversionDecision::ComparedShared { left: ReplayNode::Other, right: ReplayNode::Other }];
        let mut concatenated = Vec::new();
        for (left, right) in components {
            let sides = Sides::Values(left, right);
            let (verdict, trace) = world.traced(sides);
            prop_assert_eq!(MachineVerdict::Convertible, verdict);
            prop_assert!(unit.into_iter().eq(trace.iter().copied().map(kernel_decision)));
            prop_assert_eq!(KernelVerdict::Convertible, world.replayed(sides, verdict, &trace));
            concatenated.extend(trace);
        }
        let (verdict, trace) = world.traced(pair);
        prop_assert_eq!(MachineVerdict::Convertible, verdict);
        prop_assert!(unit.into_iter().eq(trace.iter().copied().map(kernel_decision)));
        prop_assert_eq!(KernelVerdict::Convertible, world.replayed(pair, verdict, &trace));
        prop_assert_eq!(
            KernelVerdict::Declined(ReplayDecline::Refused(ReplayRefusal::Leftover { at: TracePosition::from(1_usize) })),
            world.replayed(pair, verdict, &concatenated),
        );
    }

    /// A selected negative premise certifies; selecting its equal sibling contradicts it.
    #[test]
    fn a_refuted_pair_preserves_the_selected_component_and_refusal_class(
        context in proptest::collection::vec(any::<bool>(), 0..8),
        second in any::<bool>(),
    ) {
        let mut core = CoreArena::new();
        let mut left = core.value_unit();
        let mut right = core.value_constant(Name::Rigid.constant());
        for before in context {
            let unit = core.value_unit();
            (left, right) = if before {
                (core.value_pair(unit, left), core.value_pair(unit, right))
            } else {
                (core.value_pair(left, unit), core.value_pair(right, unit))
            };
        }
        let unit = core.value_unit();
        let pair = if second {
            Sides::Values(core.value_pair(unit, left), core.value_pair(unit, right))
        } else {
            Sides::Values(core.value_pair(left, unit), core.value_pair(right, unit))
        };
        let world = World::new(core, &[]);
        let sides = Sides::Values(left, right);
        let (verdict, trace) = world.traced(sides);
        prop_assert_eq!(MachineVerdict::NotConvertible, verdict);
        prop_assert!(
            core::iter::once(ConversionDecision::ComparedShared { left: ReplayNode::Other, right: ReplayNode::Other })
                .eq(trace.iter().copied().map(kernel_decision)),
            "the rigid component has a one-decision refutation",
        );
        prop_assert_eq!(KernelVerdict::NotConvertible, world.replayed(sides, verdict, &trace));
        let mut selected = Vec::with_capacity(trace.len().saturating_add(1));
        selected.push(ConversionDecision::NegativeSubgoal { position: SubgoalPosition::from(u32::from(second)) });
        selected.extend(trace);
        prop_assert_eq!(KernelVerdict::NotConvertible, world.replayed(pair, verdict, &selected));
        selected[0] = ConversionDecision::NegativeSubgoal { position: SubgoalPosition::from(u32::from(!second)) };
        prop_assert_eq!(
            KernelVerdict::Declined(ReplayDecline::Refused(ReplayRefusal::Contradicted { at: TracePosition::from(2_usize) })),
            world.replayed(pair, verdict, &selected),
        );
        selected[0] = ConversionDecision::NegativeSubgoal { position: SubgoalPosition::from(2_u32) };
        prop_assert_eq!(
            KernelVerdict::Declined(ReplayDecline::Refused(ReplayRefusal::Inapplicable { at: TracePosition::from(0_usize) })),
            world.replayed(pair, verdict, &selected),
        );
    }
}

#[test]
fn a_selected_refutation_replays_its_unfolding_before_rigid_separation()
{
    let mut core = CoreArena::new();
    let body = core.value_unit();
    let unit = core.value_unit();
    let reference = core.value_constant(Name::Zero.constant());
    let units = core.value_pair(unit, unit);
    let pair = Sides::Values(
        core.value_pair(unit, reference),
        core.value_pair(unit, units),
    );
    let world = World::new(core, &[(Name::Zero, body)]);
    let sides = Sides::Values(reference, units);
    let (verdict, trace) = world.traced(sides);
    assert_eq!(MachineVerdict::NotConvertible, verdict);
    assert_eq!(
        KernelVerdict::NotConvertible,
        world.replayed(sides, verdict, &trace)
    );
    let expected = [
        ConversionDecision::Unfold {
            constant: ReplayNode::Constant(Name::Zero.constant()),
        },
        ConversionDecision::ReduceLeft {
            redex: ReplayNode::Constant(Name::Zero.constant()),
        },
        ConversionDecision::ComparedShared {
            left: ReplayNode::Other,
            right: ReplayNode::Other,
        },
    ];
    assert!(
        expected
            .into_iter()
            .eq(trace.iter().copied().map(kernel_decision))
    );
    let mut selected = Vec::with_capacity(trace.len().saturating_add(1));
    selected.push(ConversionDecision::NegativeSubgoal {
        position: SubgoalPosition::from(1_u32),
    });
    selected.extend(trace);
    assert_eq!(
        KernelVerdict::NotConvertible,
        world.replayed(pair, verdict, &selected)
    );
    selected[0] = ConversionDecision::NegativeSubgoal {
        position: SubgoalPosition::from(0_u32),
    };
    assert_eq!(
        KernelVerdict::Declined(ReplayDecline::Refused(ReplayRefusal::Contradicted {
            at: TracePosition::from(1_usize),
        })),
        world.replayed(pair, verdict, &selected),
        "the equal sibling contradicts the negative claim before consuming the unfolding",
    );
}
