//! A static family as deep as an elaborator might build stays flat: built,
//! rewritten and walked inside a stack far too small for a per-node recursion.
//!
//! The arena is flat by construction, so minting a spine is a push per node;
//! the substitution static beta takes is a machine with its task stack on the
//! heap; and dropping the arena frees vectors rather than a tree. A case that
//! merely finished on the host's default stack would measure the host, so the
//! case runs inside a thread whose stack could not hold a frame per node.

#[cfg(test)]
mod deep_static
{
    use gandr_core_term::CoreArena;
    use gandr_core_term::Value;
    use gandr_core_term::Zone;
    use gandr_core_term::instantiate_value;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::DeBruijnIndex;

    /// The number of static applications on the spine. Each is one node of the
    /// arena and one frame of the recursive walk the flat representation
    /// replaces.
    const SPINE_LENGTH: usize = 50_000;

    /// A stack far too small for a per-node recursive walk over the spine, and
    /// ample for a machine whose task stack is on the heap.
    const SMALL_STACK_BYTES: usize = 256 * 1024;

    #[test]
    fn flat_arena_round_trips_deep_static_family_without_stack_recursion()
    {
        let walked = std::thread::Builder::new()
            .stack_size(SMALL_STACK_BYTES)
            .spawn(|| {
                let mut arena = CoreArena::new();
                let family = ConstantIndex::from(0_usize);
                let instance = ConstantIndex::from(1_usize);
                // `F #0 #0 … #0` under one binder: every application reads the
                // binder the instantiation substitutes.
                let mut spine = arena.value_constant(family);
                for _ in 0 .. SPINE_LENGTH {
                    let bound =
                        arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
                    spine = arena.value_static_application(spine, bound);
                }
                let argument = arena.value_constant(instance);
                let reduct = instantiate_value(&mut arena, spine, argument);

                let mut applications = 0_usize;
                let mut at = reduct;
                while let Some(&Value::StaticApplication(head, applied)) = arena.value(at) {
                    assert_eq!(
                        Some(&Value::Constant(instance)),
                        arena.value(applied),
                        "application {applications} carries the substituted argument"
                    );
                    applications = applications
                        .checked_add(1_usize)
                        .expect("the spine's length fits a counter");
                    at = head;
                }
                assert_eq!(
                    Some(&Value::Constant(family)),
                    arena.value(at),
                    "the walk ends at the family's head"
                );
                applications
            })
            .expect("the small-stack thread spawns")
            .join()
            .expect("the build, the rewrite, the walk and the drop fit the small stack");
        assert_eq!(
            SPINE_LENGTH, walked,
            "every application round-trips through the rewrite"
        );
    }
}
