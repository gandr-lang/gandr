//! Readback is iterative, observed as stack usage rather than as completion.
//!
//! Readback has the same reason to be a machine that evaluation has, and one
//! more besides: it not only walks a structure whose depth is whatever an
//! elaborator built, it *drives* an evaluation at every binder and thunk it
//! goes under. The direct presentation is two mutually recursive functions
//! whose depth scales with the normal form, so a deep-term case that merely
//! finishes measures the host stack rather than the machine.
//!
//! These therefore run inside a thread with a deliberately small stack: a
//! per-node recursive readback over a chain this deep would need megabytes of
//! frames and cannot fit, while a task stack on the heap needs none.
//!
//! Both polarities are covered, because the recursive presentation is two
//! functions and a machine that flattened only one of them would pass a
//! value-only witness.
//!
//! Every case runs in [`ReadbackMode::Unfolding`], which is the load-bearing
//! part rather than a detail: the retaining mode answers an unreduced chain
//! with the one id it was evaluated from, so it would traverse nothing at all
//! and measure neither the machine nor the host stack.

/// The deep-readback cases, in a `cfg(test)` module so the crate's lint wall
/// reads them as test code rather than as shipping code.
#[cfg(test)]
mod deep_readback
{
    use gandr_core_nbe::Definitions;
    use gandr_core_nbe::DomainArena;
    use gandr_core_nbe::Fuel;
    use gandr_core_nbe::ReadbackMode;
    use gandr_core_nbe::eval_computation;
    use gandr_core_nbe::eval_value;
    use gandr_core_nbe::readback_computation;
    use gandr_core_nbe::readback_value;
    use gandr_core_term::Computation;
    use gandr_core_term::CoreArena;
    use gandr_core_term::DefinitionChain;
    use gandr_core_term::DefinitionalEnvironment;
    use gandr_core_term::Value;

    /// The number of links in each chain. Each contributes one node to the
    /// readback's task stack and one frame to the recursive presentation it
    /// replaces.
    const CHAIN_LINKS: usize = 50_000;

    /// A stack far too small for a per-node recursive readback over the chain,
    /// and ample for a machine whose task stack is on the heap.
    const SMALL_STACK_BYTES: usize = 256 * 1024;

    /// Fuel well above the step count either chain needs, so the witness fails
    /// on depth rather than on the budget. The budget is shared with the
    /// evaluations the readback drives, which is why it is generous rather than
    /// tight.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a budget above the step count either chain below needs,
    ///   counting the evaluations the readback drives from the same budget.
    /// - provides: the budget that keeps a refusal in these witnesses a depth
    ///   result rather than an exhaustion one.
    /// - panics: none.
    fn ample() -> Fuel
    {
        Fuel::from(4_000_000_u32)
    }

    #[test]
    fn a_deep_value_reads_back_inside_a_small_stack()
    {
        let read = std::thread::Builder::new()
            .stack_size(SMALL_STACK_BYTES)
            .spawn(|| {
                // The chain is linear rather than self-shared: each link's
                // second component is one leaf. A link naming the level below it
                // twice would be a shared DAG, and this readback expands sharing
                // rather than preserving it, so the case would measure the
                // exponent instead of the depth.
                let mut core = CoreArena::new();
                let leaf = core.value_unit();
                let mut nested = leaf;
                let mut remaining = CHAIN_LINKS;
                while remaining > 0 {
                    nested = core.value_pair(nested, leaf);
                    remaining = remaining.saturating_sub(1);
                }

                let chain = DefinitionChain::new();
                let environment = DefinitionalEnvironment::new();
                let scope = environment.root();
                let definitions = Definitions::new(&chain, &environment, scope);
                let mut domain = DomainArena::new();
                let evaluated = eval_value(&core, &mut domain, definitions, ample(), nested)
                    .expect("a deep nest of pairs evaluates");
                let rebuilt = readback_value(
                    &mut core,
                    &mut domain,
                    definitions,
                    ReadbackMode::Unfolding,
                    ample(),
                    evaluated,
                )
                .expect("and reads back");

                assert_ne!(
                    nested, rebuilt,
                    "the rebuilding mode ignored the source face, so every link was walked"
                );

                // Walk back down the result so the depth cannot degenerate into
                // a shallow graph and keep passing.
                let mut depth = 0_usize;
                let mut here = rebuilt;
                while let Some(&Value::Pair(first, _)) = core.value(here) {
                    depth = depth.saturating_add(1_usize);
                    here = first;
                }
                assert_eq!(
                    CHAIN_LINKS, depth,
                    "every link of the chain is present in the term that was read back"
                );
                assert!(
                    matches!(core.value(here), Some(&Value::Unit)),
                    "and the leaf under all of them came back too"
                );
            })
            .expect("the small-stack thread starts")
            .join();
        assert!(read.is_ok(), "the value machine's depth lives on the heap");
    }

    #[test]
    fn a_deep_computation_reads_back_inside_a_small_stack()
    {
        let read = std::thread::Builder::new()
            .stack_size(SMALL_STACK_BYTES)
            .spawn(|| {
                // `return ⟨thunk (return ⟨thunk (… return ⟨⟩ …)⟩)⟩`: the depth is
                // in the *suspensions*, so evaluation stops at the first weak
                // head and readback is what drives the whole chain — one
                // evaluation per link, each entering the closure the link below
                // it suspended. No binder is opened, so the environment stays
                // empty and the case measures depth rather than the quadratic
                // copying a nest of binders would pay.
                let mut core = CoreArena::new();
                let produced = core.value_unit();
                let mut nested = core.computation_return(produced);
                let mut remaining = CHAIN_LINKS;
                while remaining > 0 {
                    let suspended = core.value_thunk(nested);
                    nested = core.computation_return(suspended);
                    remaining = remaining.saturating_sub(1);
                }

                let chain = DefinitionChain::new();
                let environment = DefinitionalEnvironment::new();
                let scope = environment.root();
                let definitions = Definitions::new(&chain, &environment, scope);
                let mut domain = DomainArena::new();
                let evaluated = eval_computation(&core, &mut domain, definitions, ample(), nested)
                    .expect("the outermost returner has a weak head");
                let rebuilt = readback_computation(
                    &mut core,
                    &mut domain,
                    definitions,
                    ReadbackMode::Unfolding,
                    ample(),
                    evaluated,
                )
                .expect("and the chain of suspensions reads back");

                assert_ne!(
                    nested, rebuilt,
                    "the rebuilding mode entered every suspension rather than answering \
                     with the source"
                );

                let mut depth = 0_usize;
                let mut here = rebuilt;
                while let Some(&Computation::Return(carried)) = core.computation(here) {
                    let Some(&Value::Thunk(body)) = core.value(carried)
                    else {
                        break;
                    };
                    depth = depth.saturating_add(1_usize);
                    here = body;
                }
                assert_eq!(
                    CHAIN_LINKS, depth,
                    "every suspension of the chain was entered and rebuilt"
                );
                assert!(
                    matches!(core.computation(here), Some(&Computation::Return(_))),
                    "and the innermost returner is what the last one suspended"
                );
            })
            .expect("the small-stack thread starts")
            .join();
        assert!(
            read.is_ok(),
            "the computation machine's depth lives on the heap too, and so does the depth \
             of the evaluations it drives"
        );
    }
}
