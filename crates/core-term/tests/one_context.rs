//! The one unified context through the public surface: a dependent function
//! type built in the arena, its binders opened and closed in order, and an
//! unfolding permission decided from the definition chain and the per-scope
//! definitional environment together.
//!
//! The unit suites separate each decision surface; this suite asserts that the
//! four pieces compose through the re-exports a consumer actually reaches,
//! which is the property a per-module test cannot observe.

#[cfg(test)]
mod one_context
{
    use gandr_core_term::BinderDepth;
    use gandr_core_term::Context;
    use gandr_core_term::ContextError;
    use gandr_core_term::CoreArena;
    use gandr_core_term::DefinitionChain;
    use gandr_core_term::DefinitionHeight;
    use gandr_core_term::DefinitionalEnvironment;
    use gandr_core_term::Sort;
    use gandr_core_term::Transparency;
    use gandr_core_term::Zone;
    use gandr_kernel_strata::Level;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::GlobalIndex;
    use gandr_kernel_term::GroundSort;

    #[test]
    fn a_dependent_codomain_is_checked_under_its_own_binder()
    {
        // `Π (A : Type[+, 0]). F (El A)` — the smallest type whose codomain reads
        // its binder, which is what makes the two zones' index arithmetic
        // observable.
        let mut arena = CoreArena::new();
        let universe = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
        let code = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let element = arena.value_type_element(code, Level::zero());
        let returner = arena.comp_type_returner(element);
        let pi = arena.comp_type_pi(universe, returner);

        let mut context = Context::new();
        // The domain stands in the ambient context; the codomain stands under it.
        context.open(Zone::Intuitionistic, universe);
        assert_eq!(
            Ok(universe),
            context.occurrence(Zone::Intuitionistic, DeBruijnIndex::from(0_u32)),
            "the code the codomain reads is the binder the dependent arrow opened"
        );
        assert_eq!(
            Err(ContextError::UnboundIndex {
                zone: Zone::Intuitionistic,
                index: DeBruijnIndex::from(1_u32),
                depth: BinderDepth::from(1_usize),
            }),
            context.occurrence(Zone::Intuitionistic, DeBruijnIndex::from(1_u32)),
            "and nothing outside the arrow is in scope for it"
        );
        assert_eq!(Ok(universe), context.close(Zone::Intuitionistic));

        // Ordering is a within-family fact: an id is an index into its own family,
        // so the invariant is asserted on each family rather than across the two.
        assert!(
            pi > returner,
            "the dependent arrow is minted above the codomain it is built over"
        );
        assert!(
            element > universe,
            "and the code's type above the universe minted before it"
        );
    }

    #[test]
    fn a_linear_binder_is_spent_once_and_only_once()
    {
        let mut arena = CoreArena::new();
        let unit = arena.value_type_unit();
        let mut context = Context::new();

        context.open(Zone::Linear, unit);
        assert_eq!(
            Err(ContextError::LinearSlotUnconsumed {
                depth: BinderDepth::from(1_usize),
            }),
            context.close(Zone::Linear),
            "an unspent capture cannot be discarded"
        );
        assert_eq!(
            Ok(unit),
            context.occurrence(Zone::Linear, DeBruijnIndex::from(0_u32))
        );
        assert_eq!(
            Err(ContextError::LinearSlotConsumed {
                index: DeBruijnIndex::from(0_u32)
            }),
            context.occurrence(Zone::Linear, DeBruijnIndex::from(0_u32)),
            "and it cannot be duplicated"
        );
        assert_eq!(Ok(unit), context.close(Zone::Linear));
    }

    #[test]
    fn an_unfolding_permission_reads_the_chain_and_the_scope_together()
    {
        let ground = ConstantIndex::from(0_usize);
        let derived = ConstantIndex::from(1_usize);

        let mut chain = DefinitionChain::new();
        let base = chain.define(ground, GlobalIndex::from(0_u32), Transparency::Manifest, &[
        ]);
        assert_eq!(
            Ok(DefinitionHeight::from(1_u32)),
            base,
            "a leaf definition still unfolds once, so the chain's floor is one"
        );
        let above = chain.define(
            derived,
            GlobalIndex::from(1_u32),
            Transparency::Manifest,
            &[ground],
        );
        assert_eq!(
            Ok(DefinitionHeight::from(2_u32)),
            above,
            "the height is the scheduling prior, computed in admission order"
        );

        let mut environment = DefinitionalEnvironment::new();
        let outside = environment.root();
        let inside = environment
            .open_scope(outside)
            .expect("the root scope resolves");
        let sealed = environment.state(outside, derived, Transparency::Opaque);
        assert_eq!(Ok(()), sealed);
        let reopened = environment.state(inside, derived, Transparency::Manifest);
        assert_eq!(Ok(()), reopened);

        let entry = chain
            .entry(derived)
            .expect("the definition is in the chain");
        assert_eq!(
            Ok(Transparency::Manifest),
            environment.transparency(inside, entry.constant(), entry.declared()),
            "the same atom is manifest inside the seal"
        );
        assert_eq!(
            Ok(Transparency::Opaque),
            environment.transparency(outside, entry.constant(), entry.declared()),
            "and opaque outside it — which is why one global table would be wrong"
        );
        assert_eq!(
            GlobalIndex::from(1_u32),
            entry.body(),
            "the chain names a canonical subterm-table entry, never a node of any arena"
        );
    }
}
