// Specification backfill pending (gandr-lang/gandr#9): the executable-
// specification lints are allowed until this crate's own backfill lands.
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    allow(
        spec_attribute_present,
        adequacy_present,
        maybe_shape,
        erased_error_signature
    )
)]
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
//!
//! # Each deep case is also an erased overlay
//!
//! Every case is built a second time as a sharing overlay — the shared leaf,
//! the shared argument and the shared continuation each a share among their
//! occurrences — and erased. The erased core arena is compared with the
//! hand-built one node for node, and the unshared pipeline then evaluates both:
//! equal domain arenas and equal results are what make the unshared pipeline
//! the reference rather than a second implementation. Validation and erasure
//! run inside the same small stack as the evaluation.
//!
//! # Each deep case is measured
//!
//! Each overlay is measured inside the same small stack, its five quantities
//! asserted exactly, and its expansion size compared with the erased term's
//! size walked as a tree: the nodes the unshared pipeline visits.
//!
//! # The overlay evaluator is the erased pipeline
//!
//! Each overlay is evaluated a second time through the overlay evaluator, and
//! the core arena it erased into, the domain arena it filled and the result it
//! reached are compared, node for node, with erasure followed by the unshared
//! pipeline: the reference every sharing stance is compared against.
//!
//! # The spinal overlay evaluator agrees with it
//!
//! Each overlay is evaluated once more under the spinal stance, installed
//! bound to a recording sink: duplicated, erased with its legs kept, and run
//! with every leg shared by configuration. Its result is read back and
//! compared, as a tree, with the reference's readback.

/// The expansion oracle, shared with the measure's suite.
#[cfg(test)]
#[path = "support/unfolding.rs"]
mod unfolding;

/// The tree oracle, shared with the duplication suite.
#[cfg(test)]
#[path = "support/trees.rs"]
mod trees;

/// The deep-evaluation cases, in a `cfg(test)` module so the crate's lint
/// wall reads them as test code rather than as shipping code.
#[cfg(test)]
mod deep_evaluation
{
    use gandr_core_nbe::Bound;
    use gandr_core_nbe::CompGraft;
    use gandr_core_nbe::CompNode;
    use gandr_core_nbe::Definitions;
    use gandr_core_nbe::DomainArena;
    use gandr_core_nbe::DomainComp;
    use gandr_core_nbe::DomainCompId;
    use gandr_core_nbe::DomainValue;
    use gandr_core_nbe::DomainValueId;
    use gandr_core_nbe::DuplicationStance;
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
    use gandr_core_nbe::TracedDuplication;
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
    use gandr_core_term::ComputationId;
    use gandr_core_term::CoreArena;
    use gandr_core_term::DefinitionalEnvironment;
    use gandr_core_term::ValueId;
    use gandr_core_term::Zone;
    use gandr_kernel_conversion_trace::TraceLog;
    use gandr_kernel_term::DeBruijnIndex;

    use crate::trees::Term;
    use crate::trees::Trees;
    use crate::trees::same_tree;
    use crate::unfolding::CoreNode;
    use crate::unfolding::Quantities;
    use crate::unfolding::Unfolded;
    use crate::unfolding::unfolded;

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

    /// `pair(… pair(pair(⟨⟩, ⟨⟩), ⟨⟩) …, ⟨⟩)`: the deep value, built by hand.
    ///
    /// The chain is linear rather than self-shared: each link's second
    /// component is one leaf. A link that named the level below it twice
    /// would be a shared DAG, and the machine expands sharing rather than
    /// preserving it, so the case would measure the exponent instead of the
    /// depth.
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

    /// `(λ … λ. return x₀) ⟨⟩ … ⟨⟩`: the deep curried application, built by
    /// hand.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: an arena holding one argument, one occurrence, one returner,
    ///   [`CURRIED_ARGUMENTS`] lambdas and as many applications, with the
    ///   outermost application's id.
    /// - provides: the curried case and the reference its overlay erases to.
    /// - panics: none.
    fn unshared_curried_application() -> (CoreArena, ComputationId)
    {
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
        (core, applied)
    }

    /// The curried application as an overlay: the argument one share among
    /// every application.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: an overlay whose root shares one unit among the arguments of
    ///   [`CURRIED_ARGUMENTS`] applications.
    /// - provides: the overlay that erases to [`unshared_curried_application`].
    /// - panics: when a mint is refused, which only the id ceiling causes.
    fn shared_curried_application() -> (Overlay, OverlayCompId)
    {
        let mut overlay = Overlay::new();
        let argument = overlay
            .mint_value(ValueNode::Grafted(ValueGraft::Unit))
            .expect("a leaf names no child");
        let bound = overlay
            .mint_value(ValueNode::Grafted(ValueGraft::Variable {
                zone: Zone::Intuitionistic,
                index: DeBruijnIndex::from(0_u32),
            }))
            .expect("a leaf names no child");
        let mut body = overlay
            .mint_computation(CompNode::Grafted(CompGraft::Return(bound)))
            .expect("the returned value resolves");
        let mut remaining = CURRIED_ARGUMENTS;
        while remaining > 0 {
            body = overlay
                .mint_computation(CompNode::Grafted(CompGraft::Lambda(body)))
                .expect("the body resolves");
            remaining = remaining.saturating_sub(1);
        }
        let mut applied = body;
        let mut taken = 0_u32;
        let mut remaining = CURRIED_ARGUMENTS;
        while remaining > 0 {
            let occurrence = value_occurrence(&mut overlay, SharePosition::from(taken));
            taken = taken.saturating_add(1);
            applied = overlay
                .mint_computation(CompNode::Grafted(CompGraft::Application(
                    applied, occurrence,
                )))
                .expect("the head and the argument resolve");
            remaining = remaining.saturating_sub(1);
        }
        let root = overlay
            .mint_computation(CompNode::Shared(Sharing {
                arity: ShareArity::from(taken),
                leg: OverlayId::Value(argument),
                body: applied,
            }))
            .expect("the argument and the applications resolve");
        (overlay, root)
    }

    /// `x0 ← (x1 ← (… return ⟨⟩ …); return x1); return x0`: the deep chain of
    /// binds, built by hand, every link's continuation one node.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: an arena holding the base returner, one continuation and
    ///   [`CHAIN_LINKS`] binds, with the outermost bind's id.
    /// - provides: the deep computation and the reference its overlay erases
    ///   to.
    /// - panics: none.
    fn unshared_bind_chain() -> (CoreArena, ComputationId)
    {
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
        (core, sequenced)
    }

    /// The chain of binds as an overlay over an opaque base: the continuation
    /// one share among every bind, its free index read under each binder.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a core arena holding the base returner, and an overlay whose
    ///   root shares one continuation among [`CHAIN_LINKS`] binds over that
    ///   base, held opaque.
    /// - provides: the overlay that erases to [`unshared_bind_chain`], with the
    ///   arena it erases into.
    /// - panics: when a mint is refused, which only the id ceiling causes.
    fn shared_bind_chain() -> (CoreArena, Overlay, OverlayCompId)
    {
        let mut core = CoreArena::new();
        let produced = core.value_unit();
        let base = core.computation_return(produced);

        let mut overlay = Overlay::new();
        let bound_occurrence = overlay
            .mint_value(ValueNode::Grafted(ValueGraft::Variable {
                zone: Zone::Intuitionistic,
                index: DeBruijnIndex::from(0_u32),
            }))
            .expect("a leaf names no child");
        let pass_on = overlay
            .mint_computation(CompNode::Grafted(CompGraft::Return(bound_occurrence)))
            .expect("the returned value resolves");
        let mut sequenced = overlay
            .mint_computation(CompNode::Opaque(base))
            .expect("an opaque node names no overlay child");
        let mut taken = 0_u32;
        let mut remaining = CHAIN_LINKS;
        while remaining > 0 {
            let continuation = overlay
                .mint_computation(CompNode::Bound(Bound {
                    distance: ShareDistance::from(0_u32),
                    position: SharePosition::from(taken),
                }))
                .expect("an occurrence names no child");
            taken = taken.saturating_add(1);
            sequenced = overlay
                .mint_computation(CompNode::Grafted(CompGraft::Bind(sequenced, continuation)))
                .expect("the bound computation and the body resolve");
            remaining = remaining.saturating_sub(1);
        }
        let root = overlay
            .mint_computation(CompNode::Shared(Sharing {
                arity: ShareArity::from(taken),
                leg: OverlayId::Computation(pass_on),
                body: sequenced,
            }))
            .expect("the continuation and the chain resolve");
        (core, overlay, root)
    }

    /// One value occurrence of the innermost share, at `position`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a fresh occurrence at distance zero.
    /// - provides: the occurrences the shared builders place in preorder.
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

    /// Evaluate a closed value with no definitions, into a fresh domain arena.
    ///
    /// # Specification
    /// - requires: `term` is a closed value of `core`.
    /// - ensures: the domain arena the evaluation filled and the value it
    ///   produced.
    /// - provides: the one run of the unshared pipeline both sides of a
    ///   comparison go through.
    /// - panics: when the evaluation is refused, which a closed term under an
    ///   ample budget does not provoke.
    fn evaluated_value(
        core: &CoreArena,
        term: ValueId,
    ) -> (DomainArena, DomainValueId)
    {
        let chain = LoweredChain::new();
        let environment = DefinitionalEnvironment::new();
        let scope = environment.root();
        let mut domain = DomainArena::new();
        let result = eval_value(
            core,
            &mut domain,
            Definitions::new(&chain, &environment, scope),
            ample(),
            term,
        )
        .expect("a closed value evaluates");
        (domain, result)
    }

    /// Evaluate a closed computation with no definitions under `fuel`, into a
    /// fresh domain arena.
    ///
    /// # Specification
    /// - requires: `term` is a closed computation of `core` whose evaluation
    ///   fits `fuel`.
    /// - ensures: the domain arena the evaluation filled and the weak head it
    ///   produced.
    /// - provides: the one run of the unshared pipeline both sides of a
    ///   comparison go through.
    /// - panics: when the evaluation is refused, which the requirement
    ///   excludes.
    fn evaluated_computation(
        core: &CoreArena,
        term: ComputationId,
        fuel: Fuel,
    ) -> (DomainArena, DomainCompId)
    {
        let chain = LoweredChain::new();
        let environment = DefinitionalEnvironment::new();
        let scope = environment.root();
        let mut domain = DomainArena::new();
        let result = eval_computation(
            core,
            &mut domain,
            Definitions::new(&chain, &environment, scope),
            fuel,
            term,
        )
        .expect("a closed computation evaluates within its budget");
        (domain, result)
    }

    /// Evaluate the overlay root `root` under `stance`, erasing into a copy of
    /// `core`, and read the result back there.
    ///
    /// # Specification
    /// - requires: `core` holds the overlay's opaque nodes, and `root` stands
    ///   for a closed term.
    /// - ensures: the arena the run erased and read back into, and the result
    ///   read back; the overlay is as it was.
    /// - provides: the one run both sides of a spinal differential go through.
    /// - panics: when installation, evaluation or readback refuses, which no
    ///   deep case under an ample budget provokes.
    fn read_back_under(
        stance: DuplicationStance,
        overlay: &mut Overlay,
        core: &CoreArena,
        root: OverlayId,
    ) -> (CoreArena, Term)
    {
        let chain = LoweredChain::new();
        let environment = DefinitionalEnvironment::new();
        let definitions = Definitions::new(&chain, &environment, environment.root());
        let mut core = core.clone();
        let mut domain = DomainArena::new();
        let mut log = TraceLog::new();
        let installed = TracedDuplication::install(stance, &mut log)
            .expect("a recording sink carries either stance");
        let read = match root {
            | OverlayId::Value(id) => {
                let (value, _remaining) = installed
                    .eval_overlay_value(overlay, &mut core, &mut domain, definitions, ample(), id)
                    .unwrap_or_else(|fault| panic!("{stance:?} evaluates the root: {fault:?}"));
                Term::Value(
                    readback_value(
                        &mut core,
                        &mut domain,
                        definitions,
                        ReadbackMode::Unfolding,
                        ample(),
                        value,
                    )
                    .expect("a closed value reads back"),
                )
            },
            | OverlayId::Computation(id) => {
                let (head, _remaining) = installed
                    .eval_overlay_computation(
                        overlay,
                        &mut core,
                        &mut domain,
                        definitions,
                        ample(),
                        id,
                    )
                    .unwrap_or_else(|fault| panic!("{stance:?} evaluates the root: {fault:?}"));
                Term::Computation(
                    readback_computation(
                        &mut core,
                        &mut domain,
                        definitions,
                        ReadbackMode::Unfolding,
                        ample(),
                        head,
                    )
                    .expect("a closed weak head reads back"),
                )
            },
            | OverlayId::ValueType(_) | OverlayId::CompType(_) => {
                panic!("the deep cases are evaluation roots")
            },
        };
        (core, read)
    }

    /// Run `root` under both stances inside the small stack and compare the
    /// readbacks as trees.
    ///
    /// # Specification
    /// - requires: as [`read_back_under`].
    /// - ensures: nothing beyond the assertion.
    /// - provides: the spinal differential each deep case runs.
    /// - panics: when the spinal readback is another tree than the reference's,
    ///   or when a run panics.
    fn spinal_agrees(
        mut overlay: Overlay,
        core: &CoreArena,
        root: OverlayId,
    )
    {
        let (reference, expected) =
            read_back_under(DuplicationStance::EraseAndClone, &mut overlay, core, root);
        let (spinal, read) = read_back_under(DuplicationStance::Spinal, &mut overlay, core, root);
        assert_eq!(
            Trees::Same,
            same_tree(&spinal, read, &reference, expected),
            "the spinal run reads back as the reference does"
        );
    }

    #[test]
    fn a_deep_value_evaluates_inside_a_small_stack()
    {
        let evaluated = std::thread::Builder::new()
            .stack_size(SMALL_STACK_BYTES)
            .spawn(|| {
                let (core, nested) = unshared_value_chain();
                let (domain, result) = evaluated_value(&core, nested);

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
        let (core, applied) = unshared_curried_application();
        let budget = Fuel::from(
            u32::try_from(CURRIED_ARGUMENTS)
                .expect("the depth fits a step budget")
                .saturating_mul(8_u32),
        );
        let (domain, result) = evaluated_computation(&core, applied, budget);

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
                // A left-nested chain of binds, each of which must run before the one
                // above it.
                let (core, sequenced) = unshared_bind_chain();
                let (domain, result) = evaluated_computation(&core, sequenced, ample());

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

    #[test]
    fn an_erased_value_chain_evaluates_byte_for_byte_as_the_unshared_one()
    {
        let compared = std::thread::Builder::new()
            .stack_size(SMALL_STACK_BYTES)
            .spawn(|| {
                let (reference, reference_root) = unshared_value_chain();
                let (overlay, root) = shared_value_chain();
                let mut erased = CoreArena::new();
                let erased_root = erase_value(&overlay, root, &mut erased)
                    .expect("the shared leaf validates and erases");
                assert!(
                    reference == erased,
                    "the erased arena is the hand-built one, node for node"
                );
                assert_eq!(reference_root, erased_root);

                let (reference_domain, reference_value) =
                    evaluated_value(&reference, reference_root);
                let (erased_domain, erased_value) = evaluated_value(&erased, erased_root);
                assert!(
                    reference_domain == erased_domain,
                    "the unshared pipeline fills one domain arena from both"
                );
                assert_eq!(reference_value, erased_value);
            })
            .expect("the small-stack thread starts")
            .join();
        assert!(
            compared.is_ok(),
            "validation, erasure and evaluation all keep their depth on the heap"
        );
    }

    #[test]
    fn an_erased_curried_application_evaluates_byte_for_byte_as_the_unshared_one()
    {
        let (reference, reference_root) = unshared_curried_application();
        let (overlay, root) = shared_curried_application();
        let mut erased = CoreArena::new();
        let erased_root = erase_computation(&overlay, root, &mut erased)
            .expect("the shared argument validates and erases");
        assert!(
            reference == erased,
            "the erased arena is the hand-built one, node for node"
        );
        assert_eq!(reference_root, erased_root);

        let (reference_domain, reference_head) =
            evaluated_computation(&reference, reference_root, ample());
        let (erased_domain, erased_head) = evaluated_computation(&erased, erased_root, ample());
        assert!(
            reference_domain == erased_domain,
            "the unshared pipeline fills one domain arena from both"
        );
        assert_eq!(reference_head, erased_head);
    }

    #[test]
    fn an_erased_bind_chain_evaluates_byte_for_byte_as_the_unshared_one()
    {
        let compared = std::thread::Builder::new()
            .stack_size(SMALL_STACK_BYTES)
            .spawn(|| {
                let (reference, reference_root) = unshared_bind_chain();
                let (mut erased, overlay, root) = shared_bind_chain();
                let erased_root = erase_computation(&overlay, root, &mut erased)
                    .expect("the shared continuation validates and erases");
                assert!(
                    reference == erased,
                    "the erased arena is the hand-built one, node for node, the opaque \
                     base included"
                );
                assert_eq!(reference_root, erased_root);

                let (reference_domain, reference_head) =
                    evaluated_computation(&reference, reference_root, ample());
                let (erased_domain, erased_head) =
                    evaluated_computation(&erased, erased_root, ample());
                assert!(
                    reference_domain == erased_domain,
                    "the unshared pipeline fills one domain arena from both"
                );
                assert_eq!(reference_head, erased_head);
            })
            .expect("the small-stack thread starts")
            .join();
        assert!(
            compared.is_ok(),
            "validation, erasure and evaluation all keep their depth on the heap"
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
                let (reference_domain, reference_value) = evaluated_value(&erased, erased_root);
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
                assert!(erased == core, "the value chain's core arena is erasure's");
                assert!(
                    reference_domain == domain,
                    "and its domain arena the unshared pipeline's"
                );
                assert_eq!(reference_value, value);

                let (overlay, root) = shared_curried_application();
                let mut erased = CoreArena::new();
                let erased_root = erase_computation(&overlay, root, &mut erased)
                    .expect("the shared argument validates and erases");
                let (reference_domain, reference_head) =
                    evaluated_computation(&erased, erased_root, ample());
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
                .expect("the shared argument evaluates through the overlay");
                assert!(
                    erased == core,
                    "the curried application's core arena is erasure's"
                );
                assert!(
                    reference_domain == domain,
                    "and its domain arena the unshared pipeline's"
                );
                assert_eq!(reference_head, head);

                let (mut erased, overlay, root) = shared_bind_chain();
                let mut core = erased.clone();
                let erased_root = erase_computation(&overlay, root, &mut erased)
                    .expect("the shared continuation validates and erases");
                let (reference_domain, reference_head) =
                    evaluated_computation(&erased, erased_root, ample());
                let mut domain = DomainArena::new();
                let (head, _remaining) = eval_overlay_computation(
                    &overlay,
                    &mut core,
                    &mut domain,
                    definitions,
                    ample(),
                    root,
                )
                .expect("the shared continuation evaluates through the overlay");
                assert!(
                    erased == core,
                    "the bind chain's core arena is erasure's, the opaque base included"
                );
                assert!(
                    reference_domain == domain,
                    "and its domain arena the unshared pipeline's"
                );
                assert_eq!(reference_head, head);
            })
            .expect("the small-stack thread starts")
            .join();
        assert!(
            compared.is_ok(),
            "erasure and evaluation through the overlay keep their depth on the heap"
        );
    }

    #[test]
    fn a_spinal_value_chain_evaluates_as_the_erased_one()
    {
        let compared = std::thread::Builder::new()
            .stack_size(SMALL_STACK_BYTES)
            .spawn(|| {
                let (overlay, root) = shared_value_chain();
                spinal_agrees(overlay, &CoreArena::new(), OverlayId::Value(root));
            })
            .expect("the small-stack thread starts")
            .join();
        assert!(
            compared.is_ok(),
            "duplication, erasure, shared evaluation and readback keep their depth on the heap"
        );
    }

    #[test]
    fn a_spinal_curried_application_evaluates_as_the_erased_one()
    {
        let compared = std::thread::Builder::new()
            .stack_size(SMALL_STACK_BYTES)
            .spawn(|| {
                let (overlay, root) = shared_curried_application();
                spinal_agrees(overlay, &CoreArena::new(), OverlayId::Computation(root));
            })
            .expect("the small-stack thread starts")
            .join();
        assert!(
            compared.is_ok(),
            "duplication, erasure, shared evaluation and readback keep their depth on the heap"
        );
    }

    #[test]
    fn a_spinal_bind_chain_evaluates_as_the_erased_one()
    {
        let compared = std::thread::Builder::new()
            .stack_size(SMALL_STACK_BYTES)
            .spawn(|| {
                let (core, overlay, root) = shared_bind_chain();
                spinal_agrees(overlay, &core, OverlayId::Computation(root));
            })
            .expect("the small-stack thread starts")
            .join();
        assert!(
            compared.is_ok(),
            "duplication, erasure, shared evaluation and readback keep their depth on the heap"
        );
    }

    #[test]
    fn the_deep_evaluation_cases_measure_as_their_erasure_inside_a_small_stack()
    {
        let measured = std::thread::Builder::new()
            .stack_size(SMALL_STACK_BYTES)
            .spawn(|| {
                let links = u64::try_from(CHAIN_LINKS).expect("the chain's length fits a counter");
                let arguments = u64::try_from(CURRIED_ARGUMENTS).expect("the arity fits a counter");

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

                let (overlay, root) = shared_curried_application();
                let measured = SharingMeasure::of(&overlay, OverlayId::Computation(root))
                    .expect("the shared argument validates and fits the counter");
                assert_eq!(
                    Quantities {
                        shares: 1,
                        occurrences: arguments,
                        depth: 1,
                        nodes: arguments.saturating_mul(3).saturating_add(4),
                        expansion: arguments.saturating_mul(3).saturating_add(2),
                    },
                    Quantities::from(measured),
                    "one argument shared among every application stands for a lambda, an \
                     application and an argument per arity, a returner and its variable"
                );
                let mut erased = CoreArena::new();
                let before = erased.clone();
                let erased_root = erase_computation(&overlay, root, &mut erased)
                    .expect("the shared argument validates and erases");
                assert_eq!(
                    Unfolded(u64::from(measured.expansion())),
                    unfolded(&erased, CoreNode::Computation(erased_root), &before),
                    "the curried application's expansion is its erasure walked as a tree"
                );

                let (mut erased, overlay, root) = shared_bind_chain();
                let measured = SharingMeasure::of(&overlay, OverlayId::Computation(root))
                    .expect("the shared continuation validates and fits the counter");
                assert_eq!(
                    Quantities {
                        shares: 1,
                        occurrences: links,
                        depth: 1,
                        nodes: links.saturating_mul(2).saturating_add(4),
                        expansion: links.saturating_mul(3).saturating_add(1),
                    },
                    Quantities::from(measured),
                    "one two-node continuation shared among every bind stands for a bind and \
                     the continuation per link over the opaque base, which counts once"
                );
                let before = erased.clone();
                let erased_root = erase_computation(&overlay, root, &mut erased)
                    .expect("the shared continuation validates and erases");
                assert_eq!(
                    Unfolded(u64::from(measured.expansion())),
                    unfolded(&erased, CoreNode::Computation(erased_root), &before),
                    "the bind chain's expansion is its erasure walked as a tree, the base held \
                     before erasure counting once"
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
