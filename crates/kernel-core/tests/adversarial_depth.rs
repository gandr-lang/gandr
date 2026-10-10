//! Adversarial-depth totality of the two machines and of the key derivation.
//!
//! Decode can build an arbitrarily deep term from bytes, so every walk the
//! kernel runs over one has to be iterative rather than recursive. A deep-term
//! test that merely has to finish is measuring the host stack, so these run
//! inside a thread with a deliberately small stack: a recursive checker, a
//! recursive type-formation walk, a recursive conversion or a recursive
//! encoder over a chain this deep would need megabytes of frames and cannot
//! fit, while an explicit frame stack on the heap needs none.
//!
//! The depth is asserted through the expansion census before the verdict is
//! read, so a case cannot silently degenerate into a shallow term and keep
//! passing.

/// The adversarial-depth cases, in a `cfg(test)` module so the crate's lint
/// wall reads them as test code rather than as shipping code.
#[cfg(test)]
mod adversarial_depth
{
    use anodized::spec;
    use gandr_kernel_check_memo::CheckMemo as _;
    use gandr_kernel_check_memo::MemoEntryCount;
    use gandr_kernel_check_memo::NullMemo;
    use gandr_kernel_core::BinderDepth;
    use gandr_kernel_core::ContentTable;
    use gandr_kernel_core::DefaultMemo;
    use gandr_kernel_core::ExpansionCensus;
    use gandr_kernel_core::ExpansionCount;
    use gandr_kernel_core::LevelContext;
    use gandr_kernel_core::RewriteMemo;
    use gandr_kernel_core::RewritePlane;
    use gandr_kernel_core::SupportContext;
    use gandr_kernel_core::SupportPlane;
    use gandr_kernel_core::check_declaration_with_memo;
    use gandr_kernel_core::shift_value_type;
    use gandr_kernel_core::substitute_comp_type;
    use gandr_kernel_strata::Level;
    use gandr_kernel_term::CompType;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::DeclarationBuilder;
    use gandr_kernel_term::LevelParamCount;
    use gandr_kernel_term::LevelSignature;
    use gandr_kernel_term::TermArena;
    use gandr_kernel_term::Value;
    use gandr_kernel_term::ValueType;

    /// The number of `thunk`-over-`return` links in the chain. Each link
    /// contributes one value node, one computation node, and their two types.
    const CHAIN_LINKS: u32 = 20_000;

    /// A stack far too small for a per-node recursive walk over the chain, and
    /// ample for iterative machines whose frame stacks live on the heap.
    const SMALL_STACK_BYTES: usize = 256 * 1024;

    /// An unconstrained level context binding no prenex parameters.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a level context binding no prenex parameters and declaring no
    ///   constraints.
    /// - provides: the level context every case here checks under.
    /// - fails: never.
    /// - panics: when admission refuses, which an empty constraint set never
    ///   does.
    ///
    /// # Adequacy
    /// - hypothesis: L3: both checker variants admit the closed 20,000-link
    ///   fixture under a zero-parameter level context; this fixes the fixture
    ///   scope, not arbitrary level constraints.
    /// - witness: `adversarial_depth::adversarial_depth::the_two_machines_are_total_on_a_chain_deep_term`
    #[spec(ensures: |ret| u32::from(ret.params()) == 0)]
    fn levels() -> LevelContext
    {
        LevelContext::admit(LevelParamCount::from(0_u32), Vec::new())
            .expect("an unconstrained context admits")
    }

    /// Check a chain-deep definition and report the census.
    ///
    /// The term is `thunk (return (thunk (return (... ())...)))` against the
    /// matching chain of thunk-and-returner types, so the checker, the
    /// type-formation walk, the conversion at the innermost mode switch and the
    /// key derivation all descend the full depth.
    ///
    /// # Specification
    /// - requires: nothing; the caller runs this on a stack far too small for a
    ///   per-node recursive walk, which is the point of the case.
    /// - ensures: the expansion census of a check of the chain-deep definition
    ///   at the chosen instantiation, having asserted the definition checks.
    ///   The checker, the type-formation walk, the conversion at the innermost
    ///   mode switch and the key derivation all descend the full depth, and the
    ///   arena is dropped here on that same small stack, which is the teardown
    ///   half of the claim.
    /// - provides: the observation the totality claim is asserted through, per
    ///   instantiation.
    /// - fails: never.
    /// - panics: when the chain-deep definition does not check, which is the
    ///   assertion this helper exists for.
    ///
    /// # Adequacy
    /// - hypothesis: L3: at 20,000 links on a 256 KiB thread stack, both memo
    ///   choices must finish checking and teardown, with the exact term census
    ///   and a type descent beyond the link count. No unbounded stack theorem
    ///   is claimed.
    /// - witness: `adversarial_depth::adversarial_depth::the_two_machines_are_total_on_a_chain_deep_term`
    #[spec(ensures: |ret| u64::from(ret.plane_expansions(SupportPlane::Term)) == u64::from(CHAIN_LINKS).saturating_mul(2).saturating_add(2)
        && u64::from(ret.plane_expansions(SupportPlane::Type)) > u64::from(CHAIN_LINKS))]
    fn check_a_deep_chain(active: MemoActivityChoice) -> ExpansionCensus
    {
        let mut arena = TermArena::new();
        let declaration = {
            let mut builder = DeclarationBuilder::new(&mut arena);
            let mint = builder.arena();
            let mut declared = mint.value_type_unit();
            let mut body = mint.value_unit();
            for _link in 0 .. CHAIN_LINKS {
                let returner = mint.comp_type_returner(declared);
                declared = mint.value_type_thunk(returner);
                let computation = mint.computation_return(body);
                body = mint.value_thunk(computation);
            }
            builder.def(LevelSignature::monomorphic(), declared, body)
        };
        let mut census = ExpansionCensus::new();
        let mut session = SupportContext::new();
        let verdict = match active {
            | MemoActivityChoice::Live => {
                let mut memo: DefaultMemo = DefaultMemo::new();
                check_declaration_with_memo(
                    &mut arena,
                    &[],
                    &levels(),
                    &declaration,
                    &mut memo,
                    &mut session,
                    &mut census,
                )
            },
            | MemoActivityChoice::Null => {
                let mut memo = NullMemo;
                check_declaration_with_memo(
                    &mut arena,
                    &[],
                    &levels(),
                    &declaration,
                    &mut memo,
                    &mut session,
                    &mut census,
                )
            },
        };
        assert_eq!(Ok(()), verdict, "the chain-deep definition checks");
        // The arena is dropped here, on the worker's small stack and with no
        // ordering care taken, which is the teardown half of the claim.
        census
    }

    /// Which instantiation of the memo seam a run takes.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum MemoActivityChoice
    {
        /// The live memo: the default path.
        Live,
        /// The memo that never answers: the permanently differentialed rollback
        /// target.
        Null,
    }

    use quenchant_arith::arith;

    /// The number of goal expansions a chain of `CHAIN_LINKS` links costs on
    /// each plane. Every node of the chain is distinct, so the memo
    /// collapses nothing and the two instantiations agree — which is what
    /// makes this a depth test rather than a sharing one.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `2 * CHAIN_LINKS + 2`: two term goals per link, plus the unit
    ///   leaf's check and its synthesis.
    /// - provides: the closed form both instantiations are asserted against.
    ///   Every node of the chain is distinct, so the memo collapses nothing and
    ///   the two agree — which is what makes this a depth case rather than a
    ///   sharing one.
    /// - fails: never.
    /// - panics: when the form leaves the representable range, which the pinned
    ///   chain length does not reach.
    ///
    /// # Adequacy
    /// - hypothesis: L3: the closed form is compared with independently counted
    ///   live and null-memo executions at 20,000 links, distinguishing a
    ///   missing leaf synthesis or an omitted link plane.
    /// - witness: `adversarial_depth::adversarial_depth::the_two_machines_are_total_on_a_chain_deep_term`
    #[spec(ensures: |ret| u64::from(ret) == u64::from(CHAIN_LINKS).saturating_add(u64::from(CHAIN_LINKS)).saturating_add(2))]
    fn expected_term_expansions() -> ExpansionCount
    {
        // Two term goals per link (the thunk's check and the returner's check),
        // plus the unit leaf's check and its synthesis.
        let scaled = arith::mul(
            arith::Int::from(u64::from(CHAIN_LINKS)),
            arith::Int::from(2_u64),
        );
        ExpansionCount::from(u64::from(arith::add(scaled, arith::Int::from(2_u64))))
    }

    #[test]
    fn the_two_machines_are_total_on_a_chain_deep_term()
    {
        for choice in [MemoActivityChoice::Null, MemoActivityChoice::Live] {
            let worker = std::thread::Builder::new()
                .stack_size(SMALL_STACK_BYTES)
                .spawn(move || check_a_deep_chain(choice))
                .expect("the small-stack worker starts");
            let census = worker.join().expect("the small-stack worker finishes");
            assert_eq!(
                expected_term_expansions(),
                census.plane_expansions(SupportPlane::Term),
                "the term really is chain-deep, so the totality claim is not vacuous ({choice:?})"
            );
            assert!(
                u64::from(census.plane_expansions(SupportPlane::Type)) > u64::from(CHAIN_LINKS),
                "and the type-formation walk descended the full depth too ({choice:?})"
            );
        }
    }

    /// The number of `thunk`-over-`returner` links in the rewrite chain.
    const REWRITE_CHAIN_LINKS: u32 = 20_000;

    /// Instantiate a chain-deep computation type and read the answer back.
    ///
    /// The chain is closed, so every link rewrites to itself and the walk hands
    /// the root back unchanged — and it still descends the full depth to
    /// find that out, because a chain's links are distinct content and the
    /// memo short-circuits nothing. A recursive substitution over a chain
    /// this deep needs megabytes of frames and cannot fit the worker's
    /// stack; an explicit task stack on the heap needs none.
    ///
    /// The returned memo entry count lets the outer witness assert the descent
    /// after the arena has been dropped on the same small stack, so a shallow
    /// fixture cannot masquerade as a deep traversal.
    ///
    /// # Specification
    /// - requires: nothing; the caller runs this on the small-stack worker.
    /// - ensures: substituting into the closed chain hands back the very node
    ///   it came from; the returned substitution memo count reaches one entry
    ///   per link, so the outer witness observes the descent after teardown.
    /// - provides: the reuse path's depth claim: the walk descends the full
    ///   depth, mints nothing, and needs no frames on the worker's stack.
    /// - fails: never.
    /// - panics: when the chain does not instantiate to itself, when the
    ///   descent did not reach one entry per link, or when the chain length
    ///   does not fit a machine index.
    ///
    /// # Adequacy
    /// - hypothesis: L3: a 20,000-link closed chain is reused and torn down on
    ///   a 256 KiB stack; the returned memo count distinguishes full descent
    ///   from a shallow fixture.
    /// - witness: `adversarial_depth::adversarial_depth::the_rewrite_machines_are_total_on_a_chain_deep_term`
    #[spec(ensures: |ret| ret >= MemoEntryCount::from(usize::try_from(REWRITE_CHAIN_LINKS).expect("the chain length fits a usize")))]
    fn instantiate_a_deep_chain() -> MemoEntryCount
    {
        let mut arena = TermArena::new();
        let mut node = arena.value_type_unit();
        for _link in 0 .. REWRITE_CHAIN_LINKS {
            let returner = arena.comp_type_returner(node);
            node = arena.value_type_thunk(returner);
        }
        let root = arena.comp_type_returner(node);
        let replacement = arena.value_unit();
        let mut table = ContentTable::new();
        let mut memo = RewriteMemo::new();
        let instantiated =
            substitute_comp_type(&mut arena, &mut table, &mut memo, root, replacement);
        assert_eq!(
            root, instantiated,
            "a closed chain instantiates to the very node it came from"
        );
        memo.plane_entry_count(RewritePlane::Substitute)
    }

    #[test]
    fn the_rewrite_machines_are_total_on_a_chain_deep_term()
    {
        let worker = std::thread::Builder::new()
            .stack_size(SMALL_STACK_BYTES)
            .spawn(instantiate_a_deep_chain)
            .expect("the small-stack worker starts");
        let entries = worker.join().expect("the small-stack worker finishes");
        let links = usize::try_from(REWRITE_CHAIN_LINKS).expect("the chain length fits a usize");
        assert!(
            entries >= MemoEntryCount::from(links),
            "the reuse walk descended every link"
        );
    }

    /// Shift a chain-deep type whose leaf is a code, and read the rewritten
    /// spine back.
    ///
    /// The closed-chain case above pins the depth of the *reuse* path, where
    /// the walk descends and mints nothing. This pins the depth of the
    /// minting path: the chain's innermost node is a type read off a bound
    /// variable, so every link's rewrite changes and the walk re-mints the
    /// whole spine. A recursive shift over a chain this deep cannot fit the
    /// worker's stack; an explicit task stack on the heap needs none.
    ///
    /// # Specification
    /// - requires: nothing; the caller runs this on the small-stack worker.
    /// - ensures: shifting the code-carrying chain re-mints the whole spine and
    ///   the rewritten spine reads back link for link; the returned shift memo
    ///   count lets the outer witness observe the descent after teardown.
    /// - provides: the minting path's depth claim, where the closed-chain case
    ///   pins the reuse path's: the innermost node is a type read off a bound
    ///   variable, so every link's rewrite changes.
    /// - fails: never.
    /// - panics: when the rewritten spine does not read back as the shift
    ///   requires.
    ///
    /// # Adequacy
    /// - hypothesis: L3: a 20,000-link code-carrying chain is shifted and torn
    ///   down on a 256 KiB stack; read-back distinguishes a collapsed spine or
    ///   wrong free index, and the returned memo count witnesses full descent.
    /// - witness: `adversarial_depth::adversarial_depth::the_rewrite_machines_are_total_on_a_code_carrying_chain`
    #[spec(ensures: |ret| ret >= MemoEntryCount::from(usize::try_from(REWRITE_CHAIN_LINKS).expect("the chain length fits a usize")))]
    fn shift_a_deep_code_carrying_chain() -> MemoEntryCount
    {
        let zero = Level::zero();
        let mut arena = TermArena::new();
        let code = arena.value_variable(DeBruijnIndex::from(0_u32));
        let mut node = arena.value_type_element(code, zero);
        for _link in 0 .. REWRITE_CHAIN_LINKS {
            let returner = arena.comp_type_returner(node);
            node = arena.value_type_thunk(returner);
        }
        let mut table = ContentTable::new();
        let mut memo = RewriteMemo::new();
        let shifted = shift_value_type(
            &mut arena,
            &mut table,
            &mut memo,
            node,
            BinderDepth::NONE,
            BinderDepth::from(1_u32),
        );
        assert_ne!(
            node, shifted,
            "the chain's code moved, so every link was re-minted and nothing short-circuited"
        );

        // Walk the rewritten spine iteratively to its leaf, which asserts the depth
        // is the one that was built rather than a collapsed one.
        let mut cursor = shifted;
        let mut links = 0_u32;
        while let Some(&ValueType::Thunk(body)) = arena.value_type(cursor) {
            let Some(&CompType::Returner(next)) = arena.comp_type(body)
            else {
                panic!("every link of the rewritten chain is a thunk over a returner");
            };
            cursor = next;
            links = u32::from(arith::add(arith::Int::from(links), arith::Int::from(1_u32)));
        }
        assert_eq!(
            REWRITE_CHAIN_LINKS, links,
            "the rewritten chain is as deep as the one it came from"
        );
        let Some(&ValueType::Element { code: raised, .. }) = arena.value_type(cursor)
        else {
            panic!("and its leaf is a type read off a code");
        };
        assert_eq!(
            Some(&Value::Variable(DeBruijnIndex::from(1_u32))),
            arena.value(raised),
            "whose free index rose with the type it sits in"
        );
        memo.plane_entry_count(RewritePlane::Shift)
    }

    #[test]
    fn the_rewrite_machines_are_total_on_a_code_carrying_chain()
    {
        let worker = std::thread::Builder::new()
            .stack_size(SMALL_STACK_BYTES)
            .spawn(shift_a_deep_code_carrying_chain)
            .expect("the small-stack worker starts");
        let entries = worker.join().expect("the small-stack worker finishes");
        let links = usize::try_from(REWRITE_CHAIN_LINKS).expect("the chain length fits a usize");
        assert!(
            entries >= MemoEntryCount::from(links),
            "the minting walk descended every link"
        );
    }
}
