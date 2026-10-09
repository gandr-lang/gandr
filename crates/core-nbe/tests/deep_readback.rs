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
//!
//! # Each deep case is also an erased overlay
//!
//! Every case is built a second time as a sharing overlay and erased: the
//! value chain with its leaf one share among all of its occurrences, the chain
//! of suspensions as grafts alone. The erased core arena is compared with the
//! hand-built one node for node, and the unshared pipeline then evaluates and
//! reads back both: equal domain arenas, equal core arenas after readback and
//! equal rebuilt ids are what make the unshared pipeline the reference.
//!
//! # Each deep case is measured
//!
//! Each overlay is measured inside the same small stack, its five quantities
//! asserted exactly, and its expansion size compared with the erased term's
//! size walked as a tree: the nodes the unshared pipeline visits.
//!
//! # The overlay evaluator is the erased pipeline
//!
//! Each overlay is evaluated a second time through the overlay evaluator and
//! read back, and the core arena, the domain arena and the rebuilt term are
//! compared, node for node, with erasure followed by the unshared pipeline.

/// The expansion oracle, shared with the measure's suite.
#[cfg(test)]
#[path = "support/unfolding.rs"]
mod unfolding;

/// The deep-readback cases, in a `cfg(test)` module so the crate's lint wall
/// reads them as test code rather than as shipping code.
#[cfg(test)]
mod deep_readback
{
    use gandr_core_nbe::Bound;
    use gandr_core_nbe::CompGraft;
    use gandr_core_nbe::CompNode;
    use gandr_core_nbe::Definitions;
    use gandr_core_nbe::DomainArena;
    use gandr_core_nbe::Fuel;
    use gandr_core_nbe::LoweredChain;
    use gandr_core_nbe::Overlay;
    use gandr_core_nbe::OverlayCompId;
    use gandr_core_nbe::OverlayId;
    use gandr_core_nbe::OverlayValueId;
    use gandr_core_nbe::ReadbackMode;
    use gandr_core_nbe::ShareArity;
    use gandr_core_nbe::ShareDistance;
    use gandr_core_nbe::SharePosition;
    use gandr_core_nbe::Sharing;
    use gandr_core_nbe::SharingMeasure;
    use gandr_core_nbe::ValueGraft;
    use gandr_core_nbe::ValueNode;
    use gandr_core_nbe::erase_computation;
    use gandr_core_nbe::erase_value;
    use gandr_core_nbe::eval_computation;
    use gandr_core_nbe::eval_overlay_computation;
    use gandr_core_nbe::eval_overlay_value;
    use gandr_core_nbe::eval_value;
    use gandr_core_nbe::readback_computation;
    use gandr_core_nbe::readback_value;
    use gandr_core_term::Computation;
    use gandr_core_term::ComputationId;
    use gandr_core_term::CoreArena;
    use gandr_core_term::DefinitionalEnvironment;
    use gandr_core_term::Value;
    use gandr_core_term::ValueId;

    use crate::unfolding::CoreNode;
    use crate::unfolding::Quantities;
    use crate::unfolding::Unfolded;
    use crate::unfolding::unfolded;

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

    /// `pair(… pair(pair(⟨⟩, ⟨⟩), ⟨⟩) …, ⟨⟩)`: the deep value, built by hand.
    ///
    /// The chain is linear rather than self-shared: each link's second
    /// component is one leaf. A link naming the level below it twice would be
    /// a shared DAG, and this readback expands sharing rather than preserving
    /// it, so the case would measure the exponent instead of the depth.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: an arena holding the leaf and [`CHAIN_LINKS`] pairs, with the
    ///   outermost pair's id.
    /// - provides: the deep value and the reference its overlay erases to.
    /// - panics: none.
    fn unshared_value_chain() -> (CoreArena, ValueId)
    {
        let mut core = CoreArena::new();
        let leaf = core.value_unit();
        let mut nested = leaf;
        let mut remaining = CHAIN_LINKS;
        while remaining > 0 {
            nested = core.value_pair(nested, leaf);
            remaining = remaining.saturating_sub(1);
        }
        (core, nested)
    }

    /// The deep value as an overlay: the leaf one share among all of its
    /// occurrences.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: an overlay whose root shares one unit among one more
    ///   occurrence than [`CHAIN_LINKS`], placed in preorder down the chain.
    /// - provides: the overlay that erases to [`unshared_value_chain`].
    /// - panics: when a mint is refused, which only the id ceiling causes.
    fn shared_value_chain() -> (Overlay, OverlayValueId)
    {
        let mut overlay = Overlay::new();
        let leaf = overlay
            .mint_value(ValueNode::Grafted(ValueGraft::Unit))
            .expect("a leaf names no child");
        let mut taken = 0_u32;
        let mut nested = value_occurrence(&mut overlay, SharePosition::from(taken));
        taken = taken.saturating_add(1);
        let mut remaining = CHAIN_LINKS;
        while remaining > 0 {
            let second = value_occurrence(&mut overlay, SharePosition::from(taken));
            taken = taken.saturating_add(1);
            nested = overlay
                .mint_value(ValueNode::Grafted(ValueGraft::Pair(nested, second)))
                .expect("both components resolve");
            remaining = remaining.saturating_sub(1);
        }
        let root = overlay
            .mint_value(ValueNode::Shared(Sharing {
                arity: ShareArity::from(taken),
                leg: OverlayId::Value(leaf),
                body: nested,
            }))
            .expect("the leaf and the chain resolve");
        (overlay, root)
    }

    /// `return ⟨thunk (return ⟨thunk (… return ⟨⟩ …)⟩)⟩`: the chain of
    /// suspensions, built by hand.
    ///
    /// The depth is in the *suspensions*, so evaluation stops at the first weak
    /// head and readback is what drives the whole chain — one evaluation per
    /// link, each entering the closure the link below it suspended. No binder
    /// is opened, so the environment stays empty and the case measures depth
    /// rather than the quadratic copying a nest of binders would pay.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: an arena holding the unit, the innermost returner and
    ///   [`CHAIN_LINKS`] thunk-returner links, with the outermost returner's
    ///   id.
    /// - provides: the deep computation and the reference its overlay erases
    ///   to.
    /// - panics: none.
    fn unshared_suspension_chain() -> (CoreArena, ComputationId)
    {
        let mut core = CoreArena::new();
        let produced = core.value_unit();
        let mut nested = core.computation_return(produced);
        let mut remaining = CHAIN_LINKS;
        while remaining > 0 {
            let suspended = core.value_thunk(nested);
            nested = core.computation_return(suspended);
            remaining = remaining.saturating_sub(1);
        }
        (core, nested)
    }

    /// The chain of suspensions as an overlay of grafts alone.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: an overlay whose root is the outermost of [`CHAIN_LINKS`]
    ///   thunk-returner links over `return ⟨⟩`, with no share.
    /// - provides: the overlay that erases to [`unshared_suspension_chain`].
    /// - panics: when a mint is refused, which only the id ceiling causes.
    fn grafted_suspension_chain() -> (Overlay, OverlayCompId)
    {
        let mut overlay = Overlay::new();
        let produced = overlay
            .mint_value(ValueNode::Grafted(ValueGraft::Unit))
            .expect("a leaf names no child");
        let mut nested = overlay
            .mint_computation(CompNode::Grafted(CompGraft::Return(produced)))
            .expect("the returned value resolves");
        let mut remaining = CHAIN_LINKS;
        while remaining > 0 {
            let suspended = overlay
                .mint_value(ValueNode::Grafted(ValueGraft::Thunk(nested)))
                .expect("the suspended computation resolves");
            nested = overlay
                .mint_computation(CompNode::Grafted(CompGraft::Return(suspended)))
                .expect("the returned thunk resolves");
            remaining = remaining.saturating_sub(1);
        }
        (overlay, nested)
    }

    /// One value occurrence of the innermost share, at `position`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a fresh occurrence at distance zero.
    /// - provides: the occurrences the shared builder places in preorder.
    /// - panics: when the mint is refused, which only the id ceiling causes.
    fn value_occurrence(
        overlay: &mut Overlay,
        position: SharePosition,
    ) -> OverlayValueId
    {
        overlay
            .mint_value(ValueNode::Bound(Bound {
                distance: ShareDistance::from(0_u32),
                position,
            }))
            .expect("an occurrence names no child")
    }

    /// Evaluate a closed value and read it back in the rebuilding mode.
    ///
    /// # Specification
    /// - requires: `term` is a closed value of `core`.
    /// - ensures: the domain arena the run filled and the rebuilt core value,
    ///   minted into `core`.
    /// - provides: the one run of the unshared pipeline both sides of a
    ///   comparison go through.
    /// - panics: when the evaluation or the readback is refused, which a closed
    ///   term under an ample budget does not provoke.
    fn read_back_value(
        core: &mut CoreArena,
        term: ValueId,
    ) -> (DomainArena, ValueId)
    {
        let chain = LoweredChain::new();
        let environment = DefinitionalEnvironment::new();
        let scope = environment.root();
        let definitions = Definitions::new(&chain, &environment, scope);
        let mut domain = DomainArena::new();
        let evaluated = eval_value(core, &mut domain, definitions, ample(), term)
            .expect("a closed value evaluates");
        let rebuilt = readback_value(
            core,
            &mut domain,
            definitions,
            ReadbackMode::Unfolding,
            ample(),
            evaluated,
        )
        .expect("and reads back");
        (domain, rebuilt)
    }

    /// Evaluate a closed computation and read it back in the rebuilding mode.
    ///
    /// # Specification
    /// - requires: `term` is a closed computation of `core`.
    /// - ensures: the domain arena the run filled and the rebuilt core
    ///   computation, minted into `core`.
    /// - provides: the one run of the unshared pipeline both sides of a
    ///   comparison go through.
    /// - panics: when the evaluation or the readback is refused, which a closed
    ///   term under an ample budget does not provoke.
    fn read_back_computation(
        core: &mut CoreArena,
        term: ComputationId,
    ) -> (DomainArena, ComputationId)
    {
        let chain = LoweredChain::new();
        let environment = DefinitionalEnvironment::new();
        let scope = environment.root();
        let definitions = Definitions::new(&chain, &environment, scope);
        let mut domain = DomainArena::new();
        let evaluated = eval_computation(core, &mut domain, definitions, ample(), term)
            .expect("the outermost returner has a weak head");
        let rebuilt = readback_computation(
            core,
            &mut domain,
            definitions,
            ReadbackMode::Unfolding,
            ample(),
            evaluated,
        )
        .expect("and the chain of suspensions reads back");
        (domain, rebuilt)
    }

    #[test]
    fn a_deep_value_reads_back_inside_a_small_stack()
    {
        let read = std::thread::Builder::new()
            .stack_size(SMALL_STACK_BYTES)
            .spawn(|| {
                let (mut core, nested) = unshared_value_chain();
                let (_domain, rebuilt) = read_back_value(&mut core, nested);

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
                let (mut core, nested) = unshared_suspension_chain();
                let (_domain, rebuilt) = read_back_computation(&mut core, nested);

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

    #[test]
    fn an_erased_value_chain_reads_back_byte_for_byte_as_the_unshared_one()
    {
        let compared = std::thread::Builder::new()
            .stack_size(SMALL_STACK_BYTES)
            .spawn(|| {
                let (mut reference, reference_root) = unshared_value_chain();
                let (overlay, root) = shared_value_chain();
                let mut erased = CoreArena::new();
                let erased_root = erase_value(&overlay, root, &mut erased)
                    .expect("the shared leaf validates and erases");
                assert!(
                    reference == erased,
                    "the erased arena is the hand-built one, node for node"
                );
                assert_eq!(reference_root, erased_root);

                let (reference_domain, reference_rebuilt) =
                    read_back_value(&mut reference, reference_root);
                let (erased_domain, erased_rebuilt) = read_back_value(&mut erased, erased_root);
                assert!(
                    reference_domain == erased_domain,
                    "the unshared pipeline fills one domain arena from both"
                );
                assert!(
                    reference == erased,
                    "and its readback mints the same core nodes into both arenas"
                );
                assert_eq!(reference_rebuilt, erased_rebuilt);
            })
            .expect("the small-stack thread starts")
            .join();
        assert!(
            compared.is_ok(),
            "validation, erasure, evaluation and readback all keep their depth on the heap"
        );
    }

    #[test]
    fn an_erased_suspension_chain_reads_back_byte_for_byte_as_the_unshared_one()
    {
        let compared = std::thread::Builder::new()
            .stack_size(SMALL_STACK_BYTES)
            .spawn(|| {
                let (mut reference, reference_root) = unshared_suspension_chain();
                let (overlay, root) = grafted_suspension_chain();
                let mut erased = CoreArena::new();
                let erased_root = erase_computation(&overlay, root, &mut erased)
                    .expect("the grafted chain validates and erases");
                assert!(
                    reference == erased,
                    "the erased arena is the hand-built one, node for node"
                );
                assert_eq!(reference_root, erased_root);

                let (reference_domain, reference_rebuilt) =
                    read_back_computation(&mut reference, reference_root);
                let (erased_domain, erased_rebuilt) =
                    read_back_computation(&mut erased, erased_root);
                assert!(
                    reference_domain == erased_domain,
                    "the unshared pipeline fills one domain arena from both"
                );
                assert!(
                    reference == erased,
                    "and its readback mints the same core nodes into both arenas"
                );
                assert_eq!(reference_rebuilt, erased_rebuilt);
            })
            .expect("the small-stack thread starts")
            .join();
        assert!(
            compared.is_ok(),
            "validation, erasure, evaluation and readback all keep their depth on the heap"
        );
    }

    #[test]
    fn erase_and_clone_overlay_evaluation_is_the_erased_pipeline()
    {
        let compared = std::thread::Builder::new()
            .stack_size(SMALL_STACK_BYTES)
            .spawn(|| {
                let chain = LoweredChain::new();
                let environment = DefinitionalEnvironment::new();
                let definitions = Definitions::new(&chain, &environment, environment.root());

                let (overlay, root) = shared_value_chain();
                let mut erased = CoreArena::new();
                let erased_root = erase_value(&overlay, root, &mut erased)
                    .expect("the shared leaf validates and erases");
                let (reference_domain, reference_rebuilt) =
                    read_back_value(&mut erased, erased_root);
                let mut core = CoreArena::new();
                let mut domain = DomainArena::new();
                let (value, _remaining) = eval_overlay_value(
                    &overlay,
                    &mut core,
                    &mut domain,
                    definitions,
                    ample(),
                    root,
                )
                .expect("the shared leaf evaluates through the overlay");
                let rebuilt = readback_value(
                    &mut core,
                    &mut domain,
                    definitions,
                    ReadbackMode::Unfolding,
                    ample(),
                    value,
                )
                .expect("and reads back");
                assert!(
                    erased == core,
                    "the value chain's core arena is erasure's and its readback's"
                );
                assert!(
                    reference_domain == domain,
                    "and its domain arena the unshared pipeline's"
                );
                assert_eq!(reference_rebuilt, rebuilt);

                let (overlay, root) = grafted_suspension_chain();
                let mut erased = CoreArena::new();
                let erased_root = erase_computation(&overlay, root, &mut erased)
                    .expect("the grafted chain validates and erases");
                let (reference_domain, reference_rebuilt) =
                    read_back_computation(&mut erased, erased_root);
                let mut core = CoreArena::new();
                let mut domain = DomainArena::new();
                let (head, _remaining) = eval_overlay_computation(
                    &overlay,
                    &mut core,
                    &mut domain,
                    definitions,
                    ample(),
                    root,
                )
                .expect("the outermost returner has a weak head through the overlay");
                let rebuilt = readback_computation(
                    &mut core,
                    &mut domain,
                    definitions,
                    ReadbackMode::Unfolding,
                    ample(),
                    head,
                )
                .expect("and the chain of suspensions reads back");
                assert!(
                    erased == core,
                    "the suspension chain's core arena is erasure's and its readback's"
                );
                assert!(
                    reference_domain == domain,
                    "and its domain arena the unshared pipeline's"
                );
                assert_eq!(reference_rebuilt, rebuilt);
            })
            .expect("the small-stack thread starts")
            .join();
        assert!(
            compared.is_ok(),
            "erasure, evaluation through the overlay and readback keep their depth on the heap"
        );
    }

    #[test]
    fn the_deep_readback_cases_measure_as_their_erasure_inside_a_small_stack()
    {
        let measured = std::thread::Builder::new()
            .stack_size(SMALL_STACK_BYTES)
            .spawn(|| {
                let links = u64::try_from(CHAIN_LINKS).expect("the chain's length fits a counter");

                let (overlay, root) = shared_value_chain();
                let measured = SharingMeasure::of(&overlay, OverlayId::Value(root))
                    .expect("the shared leaf validates and fits the counter");
                assert_eq!(
                    Quantities {
                        shares: 1,
                        occurrences: links.saturating_add(1),
                        depth: 1,
                        nodes: links.saturating_mul(2).saturating_add(3),
                        expansion: links.saturating_mul(2).saturating_add(1),
                    },
                    Quantities::from(measured),
                    "one leaf shared among one occurrence per link and one more stands for a \
                     pair and a leaf per link and one more leaf"
                );
                let mut erased = CoreArena::new();
                let before = erased.clone();
                let erased_root = erase_value(&overlay, root, &mut erased)
                    .expect("the shared leaf validates and erases");
                assert_eq!(
                    Unfolded(u64::from(measured.expansion())),
                    unfolded(&erased, CoreNode::Value(erased_root), &before),
                    "the value chain's expansion is its erasure walked as a tree"
                );

                let (overlay, root) = grafted_suspension_chain();
                let measured = SharingMeasure::of(&overlay, OverlayId::Computation(root))
                    .expect("the chain of grafts validates and fits the counter");
                let size = links.saturating_mul(2).saturating_add(2);
                assert_eq!(
                    Quantities {
                        shares: 0,
                        occurrences: 0,
                        depth: 0,
                        nodes: size,
                        expansion: size,
                    },
                    Quantities::from(measured),
                    "a chain with no share stands for itself: a thunk and a returner per link \
                     over a returned unit"
                );
                let mut erased = CoreArena::new();
                let before = erased.clone();
                let erased_root = erase_computation(&overlay, root, &mut erased)
                    .expect("the chain of grafts validates and erases");
                assert_eq!(
                    Unfolded(u64::from(measured.expansion())),
                    unfolded(&erased, CoreNode::Computation(erased_root), &before),
                    "the suspension chain's expansion is its erasure walked as a tree"
                );
            })
            .expect("the small-stack thread starts")
            .join();
        assert!(
            measured.is_ok(),
            "validation, the measure and erasure all keep their depth on the heap"
        );
    }
}
