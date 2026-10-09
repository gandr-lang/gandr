//! Evaluation is iterative, observed as stack usage rather than as completion.
//!
//! The machine's whole reason for existing is that the direct presentation —
//! two mutually recursive functions over the term — has a depth that scales
//! with whatever an elaborator built. A deep-term test that merely finishes
//! measures the host stack, so these run inside a thread with a deliberately
//! small stack: a per-node recursive evaluator over a chain this deep would
//! need megabytes of frames and cannot fit, while a task stack on the heap
//! needs none.
//!
//! Both polarities are covered, because the recursive presentation is two
//! functions and a machine that flattened only one of them would pass a
//! value-only witness.

/// The deep-evaluation cases, in a `cfg(test)` module so the crate's lint
/// wall reads them as test code rather than as shipping code.
#[cfg(test)]
mod deep_evaluation
{
    use gandr_core_nbe::Definitions;
    use gandr_core_nbe::DomainArena;
    use gandr_core_nbe::DomainComp;
    use gandr_core_nbe::DomainValue;
    use gandr_core_nbe::Fuel;
    use gandr_core_nbe::LoweredChain;
    use gandr_core_nbe::eval_computation;
    use gandr_core_nbe::eval_value;
    use gandr_core_term::CoreArena;
    use gandr_core_term::DefinitionalEnvironment;
    use gandr_core_term::Zone;
    use gandr_kernel_term::DeBruijnIndex;

    /// The number of links in each chain. Each contributes one task to the
    /// machine and one frame to the recursive presentation it replaces.
    const CHAIN_LINKS: usize = 50_000;

    /// A stack far too small for a per-node recursive evaluator over the chain,
    /// and ample for a machine whose task stack is on the heap.
    const SMALL_STACK_BYTES: usize = 256 * 1024;

    /// The arity of the curried application whose step count is pinned linear.
    ///
    /// Smaller than the chains above, because the case is about the *step*
    /// budget rather than about depth, and because the copying it does not
    /// bound is quadratic in it.
    const CURRIED_ARGUMENTS: usize = 2_000;

    /// Fuel well above the step count either chain needs, so the witness fails
    /// on depth rather than on the budget.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a budget above the step count either chain below needs.
    /// - provides: the budget that keeps a refusal in these witnesses a depth
    ///   result rather than an exhaustion one.
    /// - panics: none.
    fn ample() -> Fuel
    {
        Fuel::from(4_000_000_u32)
    }

    #[test]
    fn a_deep_value_evaluates_inside_a_small_stack()
    {
        let evaluated = std::thread::Builder::new()
            .stack_size(SMALL_STACK_BYTES)
            .spawn(|| {
                // The chain is linear rather than self-shared: each link's second
                // component is one leaf. A link that named the level below it twice
                // would be a shared DAG, and this machine expands sharing rather
                // than preserving it, so the case would measure the exponent
                // instead of the depth.
                let mut core = CoreArena::new();
                let leaf = core.value_unit();
                let mut nested = leaf;
                let mut remaining = CHAIN_LINKS;
                while remaining > 0 {
                    nested = core.value_pair(nested, leaf);
                    remaining = remaining.saturating_sub(1);
                }

                let chain = LoweredChain::new();
                let environment = DefinitionalEnvironment::new();
                let scope = environment.root();
                let mut domain = DomainArena::new();
                let result = eval_value(
                    &core,
                    &mut domain,
                    Definitions::new(&chain, &environment, scope),
                    ample(),
                    nested,
                )
                .expect("a deep nest of pairs evaluates");

                // Walk back down the result so the depth cannot degenerate into a
                // shallow graph and keep passing.
                let mut depth = 0_usize;
                let mut here = result;
                while let Some(&DomainValue::Pair { first, .. }) = domain.value(here) {
                    depth = depth.saturating_add(1_usize);
                    here = first;
                }
                assert_eq!(
                    CHAIN_LINKS, depth,
                    "every link of the chain is present in the evaluated value"
                );
            })
            .expect("the small-stack thread starts")
            .join();
        assert!(
            evaluated.is_ok(),
            "the value machine's depth lives on the heap"
        );
    }

    #[test]
    fn a_deeply_curried_application_costs_linear_steps()
    {
        // The shape the recorded quadratic is about: each beta reduction extends
        // and retains an environment one entry larger than the last. The *steps*
        // stay linear in the depth, which is what the fuel bounds; the copying does
        // not, which is what the `economy:` note at the extension site records.
        //
        // The budget is deliberately a small multiple of the depth, so a machine
        // that took a step per retained entry rather than per task would exhaust it
        // rather than pass.
        let mut core = CoreArena::new();
        let argument = core.value_unit();
        let bound = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let mut body = core.computation_return(bound);
        let mut remaining = CURRIED_ARGUMENTS;
        while remaining > 0 {
            body = core.computation_lambda(body);
            remaining = remaining.saturating_sub(1);
        }
        let mut applied = body;
        let mut remaining = CURRIED_ARGUMENTS;
        while remaining > 0 {
            applied = core.computation_application(applied, argument);
            remaining = remaining.saturating_sub(1);
        }

        let chain = LoweredChain::new();
        let environment = DefinitionalEnvironment::new();
        let scope = environment.root();
        let mut domain = DomainArena::new();
        let budget = Fuel::from(
            u32::try_from(CURRIED_ARGUMENTS)
                .expect("the depth fits a step budget")
                .saturating_mul(8_u32),
        );
        let result = eval_computation(
            &core,
            &mut domain,
            Definitions::new(&chain, &environment, scope),
            budget,
            applied,
        )
        .expect("a curried application of this depth finishes within a linear step budget");

        let Some(&DomainComp::Return { value, .. }) = domain.computation(result)
        else {
            panic!("the weak head is a returner");
        };
        assert!(
            matches!(domain.value(value), Some(&DomainValue::Unit { .. })),
            "the innermost body returned the argument the last application bound"
        );
    }

    #[test]
    fn a_deep_computation_evaluates_inside_a_small_stack()
    {
        let evaluated = std::thread::Builder::new()
            .stack_size(SMALL_STACK_BYTES)
            .spawn(|| {
                // `x0 ← (x1 ← (… return unit …); return x1); return x0`: a left-nested
                // chain of binds, each of which must run before the one above it.
                let mut core = CoreArena::new();
                let produced = core.value_unit();
                let mut sequenced = core.computation_return(produced);
                let bound_occurrence =
                    core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
                let pass_on = core.computation_return(bound_occurrence);
                let mut remaining = CHAIN_LINKS;
                while remaining > 0 {
                    sequenced = core.computation_bind(sequenced, pass_on);
                    remaining = remaining.saturating_sub(1);
                }

                let chain = LoweredChain::new();
                let environment = DefinitionalEnvironment::new();
                let scope = environment.root();
                let mut domain = DomainArena::new();
                let result = eval_computation(
                    &core,
                    &mut domain,
                    Definitions::new(&chain, &environment, scope),
                    ample(),
                    sequenced,
                )
                .expect("a deep chain of binds evaluates");

                let Some(&DomainComp::Return { value, .. }) = domain.computation(result)
                else {
                    panic!("the weak head is a returner");
                };
                assert!(
                    matches!(domain.value(value), Some(&DomainValue::Unit { .. })),
                    "the unit the innermost returner produced was passed up every link"
                );
            })
            .expect("the small-stack thread starts")
            .join();
        assert!(
            evaluated.is_ok(),
            "the computation machine's depth lives on the heap too"
        );
    }
}
