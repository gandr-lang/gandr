use gandr_core_term::Zone;
use gandr_kernel_term::DeBruijnIndex;

use super::Environment;
use super::EnvironmentDepth;
use crate::arena::DomainArena;
use crate::domain::TermFace;

#[test]
fn the_zones_resolve_one_index_to_two_bindings()
{
    let mut arena = DomainArena::new();
    let outer = arena.value_unit(TermFace::Reduced);
    let structural = arena.value_unit(TermFace::Reduced);
    let linear = arena.value_unit(TermFace::Reduced);
    let mut environment = Environment::new();
    environment.extend(Zone::Intuitionistic, outer);
    environment.extend(Zone::Intuitionistic, structural);
    environment.extend(Zone::Linear, linear);

    assert_eq!(
        Some(structural),
        environment.lookup(Zone::Intuitionistic, DeBruijnIndex::from(0_u32)),
        "index zero names the innermost binding of its own zone"
    );
    assert_eq!(
        Some(outer),
        environment.lookup(Zone::Intuitionistic, DeBruijnIndex::from(1_u32)),
        "and one out names the one before it"
    );
    assert_eq!(
        Some(linear),
        environment.lookup(Zone::Linear, DeBruijnIndex::from(0_u32)),
        "the same index in the other zone names a different binding"
    );
    assert_eq!(
        EnvironmentDepth::from(2_usize),
        environment.depth(Zone::Intuitionistic),
        "the zones count separately"
    );
    assert_eq!(
        EnvironmentDepth::from(1_usize),
        environment.depth(Zone::Linear)
    );
}

#[test]
fn an_index_past_the_depth_resolves_to_nothing()
{
    let mut arena = DomainArena::new();
    let bound = arena.value_unit(TermFace::Reduced);
    let mut environment = Environment::new();
    assert_eq!(
        EnvironmentDepth::from(0_usize),
        environment.depth(Zone::Intuitionistic)
    );
    assert_eq!(
        EnvironmentDepth::from(0_usize),
        environment.depth(Zone::Linear)
    );
    assert!(
        environment
            .lookup(Zone::Intuitionistic, DeBruijnIndex::from(0_u32))
            .is_none(),
        "an empty zone binds no index"
    );
    environment.extend(Zone::Intuitionistic, bound);
    assert!(
        environment
            .lookup(Zone::Intuitionistic, DeBruijnIndex::from(1_u32))
            .is_none(),
        "the first index past the depth resolves to nothing rather than wrapping"
    );
    assert!(
        environment
            .lookup(Zone::Linear, DeBruijnIndex::from(0_u32))
            .is_none(),
        "and extending one zone did not populate the other"
    );
    for zone in [Zone::Intuitionistic, Zone::Linear] {
        assert_eq!(
            None,
            environment.lookup(zone, DeBruijnIndex::from(u32::MAX))
        );
    }
}
