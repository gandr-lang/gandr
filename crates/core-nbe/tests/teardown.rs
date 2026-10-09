//! The teardown witness for the per-run domain arena.
//!
//! The claim under test is that the domain arena is **flat**, not that some
//! particular release order happens to work. So a chain is released twice —
//! once by truncating the arena to its floor and once by dropping it outright —
//! and both releases run inside a thread with a deliberately small stack. A
//! recursive destructor over a chain this deep would need megabytes of frames
//! and cannot fit; nine flat vector drops need none.
//!
//! The depth is observed **through a weak handle**: an id retained across the
//! release, which is not an owning reference and keeps nothing alive. Before
//! the release it resolves; after it, it does not. A test that merely finished
//! would be measuring the host stack, and a test that held the chain by an
//! owning reference would have measured nothing at all.
//!
//! # The core arena outlives every domain arena here, deliberately
//!
//! A domain arena holds ids into the core arena it was evaluated against — a
//! closure's body, a literal's payload, a term face's source — and the
//! precondition the domain arena's own documentation states is that the core
//! arena outlives it. A witness that built a core arena per chain and dropped
//! it with the chain would be exercising the violation rather than the claim.
//!
//! So one core arena is built once, at the top, and both domain arenas are
//! built against it, released, and dropped while it is still live. The core
//! arena is asserted still to resolve its nodes after both releases, which is
//! what makes the ordering an observation rather than a comment.

/// The teardown case and its chain builder, in a `cfg(test)` module so the
/// crate's lint wall reads them as test code rather than as shipping code.
#[cfg(test)]
mod teardown
{
    use gandr_core_nbe::DomainArena;
    use gandr_core_nbe::DomainValueId;
    use gandr_core_nbe::Elimination;
    use gandr_core_nbe::Environment;
    use gandr_core_nbe::NeutralHead;
    use gandr_core_nbe::RunWatermark;
    use gandr_core_nbe::TermFace;
    use gandr_core_nbe::Unfolding;
    use gandr_core_term::ComputationId;
    use gandr_core_term::CoreArena;
    use gandr_core_term::ValueId;
    use gandr_kernel_term::ConstantIndex;

    /// The number of links in one chain. Each link owns the one below it, so a
    /// per-node recursive destructor would need one frame per link.
    ///
    /// Two chains are built, one per release order, so the case walks twice
    /// this many links in total.
    const CHAIN_LINKS: usize = 100_000;

    /// A stack far too small for a per-node recursive destructor over the
    /// chain, and ample for a flat vector drop whose work is on the heap.
    const SMALL_STACK_BYTES: usize = 256 * 1024;

    /// Build a domain arena deep in **every family that owns heap data** and
    /// return it with a weak handle on the deepest value.
    ///
    /// Depth in the value family alone would witness only one of the six drops,
    /// and the three that actually own allocations — neutrals hold a spine,
    /// both closure spaces hold an environment — are the ones a recursive
    /// destructor would have walked. Each link therefore adds one value,
    /// one neutral carrying a spine, and one closure of each space.
    ///
    /// The core nodes are taken as parameters rather than built here, so the
    /// arena that minted them stays owned by the caller and outlives what
    /// this returns.
    ///
    /// The handle is a `Copy` id, so returning it retains nothing: whether it
    /// still resolves is a fact about the arena rather than about the
    /// handle.
    ///
    /// # Specification
    /// - requires: `body` and `produced` name live nodes of a core arena the
    ///   caller keeps alive at least as long as the returned domain arena.
    /// - ensures: an arena holding [`CHAIN_LINKS`] links, each adding one
    ///   value, one spined neutral, and one closure of each space, together
    ///   with a handle on the deepest value.
    /// - provides: the deep, owning graph the drop-order witnesses release
    ///   inside a small stack.
    /// - panics: when a link's neutral mint is refused, which the assertion
    ///   names; a declaration head with a rigid face is admitted by the arena's
    ///   own rule, so the panic is unreachable while that rule holds.
    fn deep_chain(
        body: ComputationId,
        produced: ValueId,
    ) -> (DomainArena, DomainValueId)
    {
        let mut arena = DomainArena::new();
        let mut top = arena.value_unit(TermFace::Reduced);
        let mut remaining = CHAIN_LINKS;
        while remaining > 0 {
            let comp_closure = arena.comp_closure_node(body, Environment::new());
            let _value_closure = arena.value_closure_node(produced, Environment::new());
            let spined = arena.neutral_node(
                NeutralHead::Constant(ConstantIndex::from(remaining)),
                Vec::from([Elimination::Apply(top), Elimination::Bind(comp_closure)]),
                Unfolding::Rigid,
            );
            assert!(spined.is_ok(), "a declaration head mints rigid");
            top = arena.value_pair(top, top, TermFace::Reduced);
            remaining = remaining.saturating_sub(1);
        }
        (arena, top)
    }

    #[test]
    fn a_deep_chain_is_released_in_both_orders_inside_a_small_stack()
    {
        let released = std::thread::Builder::new()
            .stack_size(SMALL_STACK_BYTES)
            .spawn(|| {
                // The core arena is built first and dropped last, so every domain
                // arena below holds ids into an arena that is still live — which is
                // the precondition the domain arena states rather than checks.
                let mut core = CoreArena::new();
                let produced = core.value_unit();
                let body = core.computation_return(produced);

                // First order: truncate to the floor, then drop the empty arena.
                let (mut arena, handle) = deep_chain(body, produced);
                assert!(
                    arena.value(handle).is_some(),
                    "the chain was built to its full depth before anything was released"
                );
                arena.truncate_to(RunWatermark::default());
                assert!(
                    arena.value(handle).is_none(),
                    "the weak handle stops resolving, so the release actually happened"
                );
                assert_eq!(
                    RunWatermark::default(),
                    arena.watermark(),
                    "and every family is back at the floor"
                );
                drop(arena);

                // Second order: drop the arena outright, with the chain still in it.
                let (arena, handle) = deep_chain(body, produced);
                assert!(arena.value(handle).is_some());
                drop(arena);

                // The core arena outlived both, which is what the closures and the
                // faces in them required.
                assert!(
                    core.computation(body).is_some() && core.value(produced).is_some(),
                    "the core nodes every released closure named are still there"
                );
                drop(core);
            })
            .expect("the small-stack thread starts")
            .join();
        assert!(
            released.is_ok(),
            "both release orders complete inside a stack too small for a recursive destructor"
        );
    }
}
