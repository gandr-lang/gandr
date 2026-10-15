use gandr_core_term::DefinitionHeight;

use super::Copied;
use super::DuplicationPolicy;
use super::DuplicationStance;
use super::GranularityPolicy;
use super::GranularityStance;
use super::PolicyRefusal;
use super::SchedulingPolicy;
use super::SchedulingStance;
use super::SharedPart;

/// The floor, an ordinary height, and the ceiling.
const HEIGHTS: [u32; 3] = [0_u32, 5_u32, u32::MAX];

#[test]
fn every_stance_gives_every_height_a_positive_share()
{
    for stance in [
        SchedulingStance::UniformFair,
        SchedulingStance::HeightWeighted,
    ] {
        let policy = SchedulingPolicy::new(stance);
        for height in HEIGHTS {
            let share = policy.share(DefinitionHeight::from(height));
            assert!(
                u32::from(share) > 0_u32,
                "a share slows a process and never stops one, so no stance may answer zero"
            );
        }
    }
}

#[test]
fn the_uniform_stance_ignores_the_height()
{
    let policy = SchedulingPolicy::default();
    assert_eq!(
        SchedulingStance::UniformFair,
        policy.stance(),
        "the uniform stance is the default"
    );
    let floor = policy.share(DefinitionHeight::from(0_u32));
    for height in HEIGHTS {
        assert_eq!(
            floor,
            policy.share(DefinitionHeight::from(height)),
            "round-robin gives one share whatever the goal's height"
        );
    }
}

#[test]
fn the_weighted_stance_rises_with_the_height()
{
    let policy = SchedulingPolicy::new(SchedulingStance::HeightWeighted);
    let floor = policy.share(DefinitionHeight::from(0_u32));
    let ordinary = policy.share(DefinitionHeight::from(5_u32));
    let ceiling = policy.share(DefinitionHeight::from(u32::MAX));
    assert!(floor < ordinary, "a taller goal receives a larger share");
    assert!(
        ordinary < ceiling,
        "and the growth continues up to the saturation point"
    );
    assert_eq!(
        ceiling,
        policy.share(DefinitionHeight::from(u32::MAX.saturating_sub(1_u32))),
        "and the last two heights answer one share, which is the saturation itself \
             rather than a restatement of the same call"
    );
    assert_eq!(
        floor,
        SchedulingPolicy::default().share(DefinitionHeight::from(0_u32)),
        "and at the floor the two stances agree, so the parameter is inert on a flat corpus"
    );
}

#[test]
fn the_finer_duplication_stance_is_gated()
{
    let baseline = DuplicationPolicy::new(DuplicationStance::EraseAndClone);
    assert_eq!(
        Ok(DuplicationStance::EraseAndClone),
        baseline.map(|policy| policy.stance()),
        "the conservative stance installs and is the default"
    );
    assert_eq!(
        DuplicationStance::EraseAndClone,
        DuplicationPolicy::default().stance()
    );
    assert_eq!(
        Err(PolicyRefusal::StanceGated {
            stance: DuplicationStance::Spinal,
        }),
        DuplicationPolicy::new(DuplicationStance::Spinal),
        "the finer stance is representable and refused: the gate is the ordering, mechanized"
    );
}

#[test]
fn the_finer_granularity_stance_is_gated()
{
    assert_eq!(
        Ok(GranularityStance::Skeleton),
        GranularityPolicy::new(GranularityStance::Skeleton).map(|policy| policy.stance()),
        "one channel per subterm-table entry installs and is the default"
    );
    assert_eq!(
        GranularityStance::Skeleton,
        GranularityPolicy::default().stance()
    );
    assert_eq!(
        Err(PolicyRefusal::GranularityGated {
            stance: GranularityStance::Spinal,
        }),
        GranularityPolicy::new(GranularityStance::Spinal),
        "minting along spines is representable and refused until a trace certifies it"
    );
}

#[test]
fn the_stances_differ_only_on_the_ribs()
{
    let baseline = DuplicationPolicy::default();
    assert_eq!(Copied::Copied, baseline.copies(SharedPart::Spine));
    assert_eq!(
        Copied::Copied,
        baseline.copies(SharedPart::Rib),
        "the erasure copies everything, which is what makes it the unshared reference"
    );

    // The gated stance's table is still the parameter's shape, so it is
    // asserted here through the stance rather than through an installation
    // the gate refuses.
    let spinal = DuplicationPolicy {
        stance: DuplicationStance::Spinal,
    };
    assert_eq!(Copied::Copied, spinal.copies(SharedPart::Spine));
    assert_eq!(
        Copied::Shared,
        spinal.copies(SharedPart::Rib),
        "the spinal stance keeps the ribs shared, which is the whole difference"
    );
}
