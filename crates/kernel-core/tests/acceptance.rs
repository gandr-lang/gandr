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
//! The kernel's acceptance suite: the collapse law, anti-vacuity on both sides,
//! edit locality, the memoized-against-memoless differential, and the
//! poisoned-entry cases that prove the differential bites.
//!
//! Every measurement here is asserted rather than reported. A differential can
//! be green while never reaching the code it tests, so each case pins its
//! exercised-path counts through the checker's declared expansion census.

/// The acceptance cases, in a `cfg(test)` module so the crate's lint wall
/// reads them as test code rather than as shipping code.
#[cfg(test)]
mod acceptance
{
    use gandr_kernel_check_memo::CheckMemo;
    use gandr_kernel_check_memo::MemoEntryCount;
    use gandr_kernel_check_memo::NullMemo;
    use gandr_kernel_core::Admission;
    use gandr_kernel_core::DefaultMemo;
    use gandr_kernel_core::Environment;
    use gandr_kernel_core::ExpansionCensus;
    use gandr_kernel_core::ExpansionCount;
    use gandr_kernel_core::KernelError;
    use gandr_kernel_core::LevelContext;
    use gandr_kernel_core::NodeOutcome;
    use gandr_kernel_core::NodeSupport;
    use gandr_kernel_core::RewritePlane;
    use gandr_kernel_core::SupportContext;
    use gandr_kernel_core::SupportGoal;
    use gandr_kernel_core::SupportPlane;
    use gandr_kernel_core::check_declaration_with_memo;
    use gandr_kernel_strata::Level;
    use gandr_kernel_strata::LevelConstant;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::Declaration;
    use gandr_kernel_term::DeclarationBuilder;
    use gandr_kernel_term::DeclarationContent;
    use gandr_kernel_term::GroundSort;
    use gandr_kernel_term::LevelParamCount;
    use gandr_kernel_term::LevelSignature;
    use gandr_kernel_term::Side;
    use gandr_kernel_term::TermArena;
    use gandr_kernel_term::ValueId;
    use gandr_kernel_term::ValueTypeId;
    use quenchant_arith::arith;

    /// The depth of a self-similar composite fixture.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
    struct CompositeDepth(u32);

    /// The three depths the collapse law is pinned at, so the law is asserted
    /// as a closed form rather than sampled at one point.
    const PINNED_DEPTHS: [CompositeDepth; 3] =
        [CompositeDepth(8), CompositeDepth(12), CompositeDepth(16)];

    /// The depth at which the capability is demonstrated through the public
    /// admission entry point.
    const CAPABILITY_DEPTH: CompositeDepth = CompositeDepth(28);

    /// A count the closed forms produce: goal expansions, or the occurrences
    /// they stand in for.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
    struct GoalCount(u64);

    impl From<GoalCount> for u64
    {
        /// The raw count `count` carries.
        ///
        /// # Specification
        /// trivial.
        #[inline]
        fn from(count: GoalCount) -> Self
        {
            count.0
        }
    }

    impl From<GoalCount> for ExpansionCount
    {
        /// The same count as an expansion count.
        ///
        /// # Specification
        /// trivial.
        #[inline]
        fn from(count: GoalCount) -> Self
        {
            Self::from(count.0)
        }
    }

    /// `2^depth`, as the occurrence count of a depth-`depth` composite's leaf.
    ///
    /// # Specification
    /// - requires: `depth` is one of the pinned depths, all small enough for
    ///   the shift to be representable.
    /// - ensures: `2^depth`, the occurrence count of a depth-`depth`
    ///   composite's leaf.
    /// - provides: the term every closed form below is written over.
    /// - fails: never.
    /// - panics: when the shift leaves the representable range, which no pinned
    ///   depth reaches.
    fn two_to_the(depth: CompositeDepth) -> GoalCount
    {
        let mut count = arith::Int::from(1_u64);
        for _ in 0 .. depth.0 {
            count = arith::mul(count, arith::Int::from(2_u64));
        }
        GoalCount(u64::from(count))
    }

    /// The memoless goal-expansion law: `5 * 2^d - 2` in total.
    ///
    /// # Specification
    /// - requires: `depth` is one of the pinned depths.
    /// - ensures: `5 * 2^depth - 2`, the total goal expansions a memoless check
    ///   of the composite makes across both planes.
    /// - provides: the closed form the memoless side of the collapse law is
    ///   asserted against, so the law is a form rather than a sample.
    /// - fails: never.
    /// - panics: when the form leaves the representable range, which no pinned
    ///   depth reaches.
    fn memoless_total(depth: CompositeDepth) -> GoalCount
    {
        let scaled = arith::mul(
            arith::Int::from(5_u64),
            arith::Int::from(two_to_the(depth).0),
        );
        GoalCount(u64::from(arith::sub(scaled, arith::Int::from(2_u64))))
    }

    /// The memoless term-plane law: `3 * 2^d - 1` body checks.
    ///
    /// # Specification
    /// - requires: `depth` is one of the pinned depths.
    /// - ensures: `3 * 2^depth - 1`, the body checks a memoless check makes on
    ///   the term plane.
    /// - provides: the term-plane half of the memoless form, so neither plane's
    ///   collapse hides behind the other's numbers.
    /// - fails: never.
    /// - panics: when the form leaves the representable range.
    fn memoless_term(depth: CompositeDepth) -> GoalCount
    {
        let scaled = arith::mul(
            arith::Int::from(3_u64),
            arith::Int::from(two_to_the(depth).0),
        );
        GoalCount(u64::from(arith::sub(scaled, arith::Int::from(1_u64))))
    }

    /// The memoless type-plane law: `2^(d+1) - 1` type formations.
    ///
    /// # Specification
    /// - requires: `depth` is one of the pinned depths.
    /// - ensures: `2^(depth + 1) - 1`, the type formations a memoless check
    ///   makes on the type plane.
    /// - provides: the type-plane half of the memoless form.
    /// - fails: never.
    /// - panics: when the form leaves the representable range.
    fn memoless_type(depth: CompositeDepth) -> GoalCount
    {
        let doubled = arith::mul(
            arith::Int::from(two_to_the(depth).0),
            arith::Int::from(2_u64),
        );
        GoalCount(u64::from(arith::sub(doubled, arith::Int::from(1_u64))))
    }

    /// The memoized term-plane law: `d + 1` body checks plus one leaf
    /// synthesis.
    ///
    /// # Specification
    /// - requires: `depth` is one of the pinned depths.
    /// - ensures: `depth + 2`: one body check per spine level plus the leaf
    ///   synthesis.
    /// - provides: the term-plane half of the memoized form — linear against
    ///   the memoless form's exponential, which is the collapse stated as a
    ///   number.
    /// - fails: never.
    /// - panics: when the sum leaves the representable range, which no pinned
    ///   depth reaches.
    fn memoized_term(depth: CompositeDepth) -> GoalCount
    {
        GoalCount(u64::from(arith::add(
            arith::Int::from(u64::from(depth.0)),
            arith::Int::from(2_u64),
        )))
    }

    /// The memoized type-plane law: `d + 1` type formations.
    ///
    /// # Specification
    /// - requires: `depth` is one of the pinned depths.
    /// - ensures: `depth + 1`, the type formations a memoized check makes on
    ///   the type plane.
    /// - provides: the type-plane half of the memoized form.
    /// - fails: never.
    /// - panics: when the sum leaves the representable range.
    fn memoized_type(depth: CompositeDepth) -> GoalCount
    {
        GoalCount(u64::from(arith::add(
            arith::Int::from(u64::from(depth.0)),
            arith::Int::from(1_u64),
        )))
    }

    /// The `d + 1` spine levels a depth-`d` edit re-checks.
    ///
    /// # Specification
    /// - requires: `depth` is one of the pinned depths.
    /// - ensures: `depth + 1`, the spine levels a depth-`depth` edit re-checks.
    /// - provides: the locality form the edit case is asserted against, so an
    ///   edit's cost is stated as the spine rather than as the term.
    /// - fails: never.
    /// - panics: when the sum leaves the representable range.
    fn edit_locality(depth: CompositeDepth) -> GoalCount
    {
        GoalCount(u64::from(arith::add(
            arith::Int::from(u64::from(depth.0)),
            arith::Int::from(1_u64),
        )))
    }

    /// An unconstrained level context binding no prenex parameters.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a level context binding no prenex parameters and declaring no
    ///   constraints.
    /// - provides: the level context every case in this suite checks under.
    /// - fails: never.
    /// - panics: when admission refuses, which an empty constraint set never
    ///   does.
    fn levels() -> LevelContext
    {
        LevelContext::admit(LevelParamCount::from(0_u32), Vec::new())
            .expect("an unconstrained context admits")
    }

    /// The constant level `value`.
    ///
    /// # Specification
    /// trivial.
    fn level(value: LevelConstant) -> Level
    {
        Level::constant(value)
    }

    /// The **shared** self-similar composite: `t_0 = ()`, `t_{k+1} = (t_k,
    /// t_k)` against `T_0 = Unit`, `T_{k+1} = T_k x T_k`.
    ///
    /// Every level is two references to the level beneath it, so the occurrence
    /// count is exponential in the depth while the distinct-node count is
    /// linear.
    ///
    /// # Specification
    /// - requires: `arena` is the one this declaration's content is minted
    ///   into.
    /// - ensures: the declared type and body of the depth-`depth` composite,
    ///   every level being two references to the level beneath it — so the
    ///   occurrence count is exponential in the depth while the distinct-node
    ///   count is linear.
    /// - provides: the shared side of the collapse law, whose sharing the
    ///   checker preserves and never creates.
    /// - fails: never.
    /// - panics: none.
    fn shared_composite(
        arena: &mut TermArena,
        depth: CompositeDepth,
    ) -> (ValueTypeId, ValueId)
    {
        let mut declared = arena.value_type_unit();
        let mut body = arena.value_unit();
        for _step in 0 .. depth.0 {
            declared = arena.value_type_product(declared, declared);
            body = arena.value_pair(body, body);
        }
        (declared, body)
    }

    /// The **unshared** spelling of the same composite: every occurrence gets
    /// its own arena node, folded bottom-up so nothing recurses.
    ///
    /// # Specification
    /// - requires: `arena` is the one this declaration's content is minted
    ///   into, and `depth` is small enough for the leaf count to be allocated.
    /// - ensures: the same term as the shared composite, with every occurrence
    ///   given its own arena node, folded bottom-up so nothing recurses.
    /// - provides: the unshared side of the collapse law, so the content key's
    ///   payoff is a measured number rather than an argument.
    /// - fails: never.
    /// - panics: when the leaf count does not fit a machine index, which no
    ///   pinned depth reaches.
    fn unshared_composite(
        arena: &mut TermArena,
        depth: CompositeDepth,
    ) -> (ValueTypeId, ValueId)
    {
        let leaves = usize::try_from(u64::from(two_to_the(depth))).expect("the leaf count fits");
        let mut types: Vec<ValueTypeId> = Vec::with_capacity(leaves);
        let mut values: Vec<ValueId> = Vec::with_capacity(leaves);
        for _leaf in 0 .. leaves {
            types.push(arena.value_type_unit());
            values.push(arena.value_unit());
        }
        while types.len() > 1 {
            let mut next_types: Vec<ValueTypeId> = Vec::new();
            let mut next_values: Vec<ValueId> = Vec::new();
            for slot in types.chunks(2) {
                let (Some(&first), Some(&second)) = (slot.first(), slot.last())
                else {
                    panic!("each level has an even length");
                };
                next_types.push(arena.value_type_product(first, second));
            }
            for slot in values.chunks(2) {
                let (Some(&first), Some(&second)) = (slot.first(), slot.last())
                else {
                    panic!("each level has an even length");
                };
                next_values.push(arena.value_pair(first, second));
            }
            types = next_types;
            values = next_values;
        }
        let (Some(&declared), Some(&body)) = (types.first(), values.first())
        else {
            panic!("the fold leaves one root per family");
        };
        (declared, body)
    }

    /// The edit fixture's leaf: `T_0 = Unit + Unit`, with the left injection as
    /// the original leaf.
    ///
    /// A sum leaf rather than a unit one, because an edit has to be able to
    /// change the leaf's *content* while leaving its type alone — which is
    /// what a real edit does and what a fresh-but-identical re-minting does
    /// not.
    ///
    /// # Specification
    /// - requires: `arena` is the one this declaration's content is minted
    ///   into.
    /// - ensures: the composite over a sum leaf, together with every level of
    ///   its body from the leaf up, so an edit can name the sibling it keeps.
    /// - provides: the edit fixture's shape — a sum leaf, because an edit has
    ///   to change the leaf's content while leaving its type alone, which a
    ///   unit leaf cannot express.
    /// - fails: never.
    /// - panics: none.
    fn injection_composite(
        arena: &mut TermArena,
        depth: CompositeDepth,
    ) -> (ValueTypeId, ValueId, Vec<ValueId>)
    {
        let unit_type = arena.value_type_unit();
        let unit = arena.value_unit();
        let mut declared = arena.value_type_sum(unit_type, unit_type);
        let mut body = arena.value_injection(Side::Left, unit);
        let mut levels_of_body = Vec::new();
        levels_of_body.push(body);
        for _step in 0 .. depth.0 {
            declared = arena.value_type_product(declared, declared);
            body = arena.value_pair(body, body);
            levels_of_body.push(body);
        }
        (declared, body, levels_of_body)
    }

    /// The unedited counterpart of [`edited_composite`]: the composite paired
    /// with **itself**, so the two fixtures differ by exactly one edit.
    ///
    /// # Specification
    /// - requires: `arena` is the one this declaration's content is minted
    ///   into.
    /// - ensures: the composite paired with itself, so this fixture and the
    ///   edited one differ by exactly one edit.
    /// - provides: the baseline the edit's cost is measured against.
    /// - fails: never.
    /// - panics: none.
    fn unedited_composite(
        arena: &mut TermArena,
        depth: CompositeDepth,
    ) -> (ValueTypeId, ValueId)
    {
        let (declared, body, _levels) = injection_composite(arena, depth);
        let pair_type = arena.value_type_product(declared, declared);
        let pair = arena.value_pair(body, body);
        (pair_type, pair)
    }

    /// A **genuine depth-`d` edit**, minted beside the original in one arena.
    ///
    /// The leaf's content changes — the left injection becomes the right one —
    /// and its own payload is re-minted as a fresh node structurally
    /// identical to the original's. The spine from the edited leaf to the
    /// root is re-minted level by level, each new node pairing the edited
    /// child with the *original* untouched sibling, so every off-spine
    /// subterm is the very arena id the original names.
    ///
    /// Returned as one declaration checking `(original, edited)`, so both
    /// spellings are checked in **one** call. That matters: the memo's
    /// lifetime is a single check, deliberately, so measuring an edit's
    /// cost by warming a memo on the original and reusing it across calls
    /// would be measuring exactly the unsound thing the lifetime rule
    /// forbids.
    ///
    /// # Specification
    /// - requires: `arena` is the one this declaration's content is minted
    ///   into.
    /// - ensures: one declaration checking the original composite paired with a
    ///   genuinely edited spelling of it: the leaf's injection side changes
    ///   over a freshly minted but structurally identical payload, and the
    ///   spine is re-minted level by level, each new node pairing the edited
    ///   child with the original untouched sibling. Both spellings are checked
    ///   in one call, since the memo's lifetime is a single check.
    /// - provides: the edit fixture the locality form is asserted over. A
    ///   content key collapses the fresh payload with the original's, where an
    ///   arena-identity key would not; measuring the edit by warming a memo
    ///   across two calls would measure exactly the unsound thing the lifetime
    ///   rule forbids.
    /// - fails: never.
    /// - panics: when a level below the root was not recorded, which the
    ///   fixture's own construction rules out.
    fn edited_composite(
        arena: &mut TermArena,
        depth: CompositeDepth,
    ) -> (ValueTypeId, ValueId)
    {
        let (declared, original, levels_of_body) = injection_composite(arena, depth);

        // The edited leaf: a different injection over a *fresh* payload node that
        // is structurally identical to the original's. A content key collapses the
        // payload with the original's; an arena-identity key would not.
        let fresh_unit = arena.value_unit();
        let mut edited = arena.value_injection(Side::Right, fresh_unit);
        for step in 0 .. depth.0 {
            let index = usize::try_from(step).expect("the level index fits");
            let Some(&sibling) = levels_of_body.get(index)
            else {
                panic!("every level below the root was recorded");
            };
            edited = arena.value_pair(edited, sibling);
        }

        let pair_type = arena.value_type_product(declared, declared);
        let body = arena.value_pair(original, edited);
        (pair_type, body)
    }

    /// Mint one definition's content into a fresh arena and finalize it.
    ///
    /// A bare arena rather than an environment, so the differential can run the
    /// same declaration twice without an admission mutating what the second run
    /// sees.
    ///
    /// # Specification
    /// - requires: `build` mints one definition's declared type and body into
    ///   the arena it is handed.
    /// - ensures: a fresh arena holding exactly that content, and the finalized
    ///   monomorphic definition over it.
    /// - provides: the staging every case runs through. A bare arena rather
    ///   than an environment is what lets a differential run the same
    ///   declaration twice without an admission mutating what the second run
    ///   sees.
    /// - fails: never.
    /// - panics: none.
    fn stage<Build>(build: Build) -> (TermArena, Declaration)
    where
        Build: FnOnce(&mut TermArena) -> (ValueTypeId, ValueId),
    {
        let mut arena = TermArena::new();
        let declaration = {
            let mut builder = DeclarationBuilder::new(&mut arena);
            let (declared, body) = build(builder.arena());
            builder.def(LevelSignature::monomorphic(), declared, body)
        };
        (arena, declaration)
    }

    /// Check one staged definition with `memo`, reporting the verdict beside
    /// the census.
    ///
    /// # Specification
    /// - requires: `declaration` was staged into `arena`.
    /// - ensures: the check's verdict beside the expansion census of that run,
    ///   against a session of its own.
    /// - provides: the ordinary measurement path of this suite.
    /// - fails: never — the verdict is returned rather than propagated.
    /// - panics: none.
    fn check_with<Memo>(
        arena: &mut TermArena,
        declaration: &Declaration,
        memo: &mut Memo,
    ) -> (Result<(), KernelError>, ExpansionCensus)
    where
        Memo: CheckMemo<NodeSupport, NodeOutcome>,
    {
        let mut session = SupportContext::new();
        check_in_session(arena, declaration, memo, &mut session)
    }

    /// Check one staged definition against a caller-held session, so a
    /// poisoning test can build its entry through the very session the
    /// check then uses.
    ///
    /// That sharing is the point: a support is meaningful against its own
    /// session and against no other, which is the memo's one-call lifetime
    /// made structural.
    ///
    /// # Specification
    /// - requires: `declaration` was staged into `arena`, and `session` is the
    ///   one every support handed to `memo` was built against.
    /// - ensures: the check's verdict beside its expansion census, with the
    ///   caller's session threaded through.
    /// - provides: the sharing a poisoning case needs — a support is meaningful
    ///   against its own session and no other, which is the memo's one-call
    ///   lifetime made structural.
    /// - fails: never — the verdict is returned rather than propagated.
    /// - panics: none.
    fn check_in_session<Memo>(
        arena: &mut TermArena,
        declaration: &Declaration,
        memo: &mut Memo,
        session: &mut SupportContext,
    ) -> (Result<(), KernelError>, ExpansionCensus)
    where
        Memo: CheckMemo<NodeSupport, NodeOutcome>,
    {
        let mut census = ExpansionCensus::new();
        let verdict = check_declaration_with_memo(
            arena,
            &[],
            &levels(),
            declaration,
            memo,
            session,
            &mut census,
        );
        (verdict, census)
    }

    /// Check `build`'s definition twice — once with the live memo, once with
    /// the memo that never answers — and require the two verdicts to agree.
    ///
    /// Each run gets its own arena built by the same closure, so the checker
    /// intermediates one run mints cannot reach the other.
    ///
    /// # Specification
    /// - requires: `build` mints the same content into every arena it is
    ///   handed.
    /// - ensures: the memoless verdict, having asserted that the live memo
    ///   reached the same verdict and, on a refusal, the very same refusal.
    ///   Each run gets its own arena built by the same closure, so one run's
    ///   checker intermediates cannot reach the other.
    /// - provides: the zero-drift differential every acceptance and refusal in
    ///   this suite is run through.
    /// - fails: the memoless refusal, returned so a caller can assert on it.
    /// - panics: when the two verdicts disagree, which is the assertion this
    ///   harness exists for.
    fn verdicts_agree<Build>(build: Build) -> Result<(), KernelError>
    where
        Build: Fn(&mut TermArena) -> (ValueTypeId, ValueId),
    {
        let (mut fresh_arena, fresh_declaration) = stage(&build);
        let mut null = NullMemo;
        let (memoless, _fresh_census) = check_with(&mut fresh_arena, &fresh_declaration, &mut null);

        let (mut memo_arena, memo_declaration) = stage(&build);
        let mut live: DefaultMemo = DefaultMemo::new();
        let (memoized, _live_census) = check_with(&mut memo_arena, &memo_declaration, &mut live);

        assert_eq!(
            memoless.is_ok(),
            memoized.is_ok(),
            "memoized checking must reach the memoless verdict: {memoless:?} against {memoized:?}"
        );
        if let (Err(memoless_error), Err(memoized_error)) = (memoless.as_ref(), memoized.as_ref()) {
            assert_eq!(
                memoless_error, memoized_error,
                "a refusal must be the same refusal, not merely a refusal"
            );
        }
        memoless
    }

    // ---------------------------------------------------------------------------
    // The collapse, as a closed form at three depths, decomposed per plane
    // ---------------------------------------------------------------------------

    #[test]
    fn the_collapse_is_a_closed_form_at_three_depths()
    {
        for depth in PINNED_DEPTHS {
            let (mut arena, declaration) = stage(|arena| shared_composite(arena, depth));
            let mut null = NullMemo;
            let (verdict, memoless) = check_with(&mut arena, &declaration, &mut null);
            assert_eq!(Ok(()), verdict, "the composite checks at depth {depth:?}");

            let (mut arena, declaration) = stage(|arena| shared_composite(arena, depth));
            let mut live: DefaultMemo = DefaultMemo::new();
            let (verdict, memoized) = check_with(&mut arena, &declaration, &mut live);
            assert_eq!(Ok(()), verdict, "and it checks memoized at depth {depth:?}");

            // The law, in total.
            assert_eq!(
                ExpansionCount::from(memoless_total(depth)),
                memoless.expansions(),
                "memoless expansions are 5 * 2^d - 2 at depth {depth:?}"
            );
            let memoized_total = arith::add(
                arith::Int::from(u64::from(memoized_term(depth))),
                arith::Int::from(u64::from(memoized_type(depth))),
            );
            assert_eq!(
                ExpansionCount::from(u64::from(memoized_total)),
                memoized.expansions(),
                "memoized expansions are 2d + 3 at depth {depth:?}"
            );

            // The law, decomposed per plane, so neither machine's collapse can hide
            // behind the other's numbers.
            assert_eq!(
                ExpansionCount::from(memoless_term(depth)),
                memoless.plane_expansions(SupportPlane::Term),
                "memoless body checks are 3 * 2^d - 1 at depth {depth:?}"
            );
            assert_eq!(
                ExpansionCount::from(memoless_type(depth)),
                memoless.plane_expansions(SupportPlane::Type),
                "memoless type formations are 2^(d+1) - 1 at depth {depth:?}"
            );
            assert_eq!(
                ExpansionCount::from(memoized_term(depth)),
                memoized.plane_expansions(SupportPlane::Term),
                "memoized body checks are d + 2 at depth {depth:?}"
            );
            assert_eq!(
                ExpansionCount::from(memoized_type(depth)),
                memoized.plane_expansions(SupportPlane::Type),
                "memoized type formations are d + 1 at depth {depth:?}"
            );
        }
    }

    // ---------------------------------------------------------------------------
    // Anti-vacuity, on both sides
    // ---------------------------------------------------------------------------

    #[test]
    fn the_occurrence_count_is_pinned_so_the_workload_cannot_stop_being_shared()
    {
        for depth in PINNED_DEPTHS {
            let (mut arena, declaration) = stage(|arena| shared_composite(arena, depth));
            let mut null = NullMemo;
            let (verdict, census) = check_with(&mut arena, &declaration, &mut null);
            assert_eq!(Ok(()), verdict);
            // The memoless count *is* the occurrence count. A workload that quietly
            // lost its sharing would report a memoless count equal to its memoized
            // one, and this assertion is what would notice.
            assert_eq!(
                ExpansionCount::from(memoless_term(depth)),
                census.plane_expansions(SupportPlane::Term),
                "the leaf occurs 2^d times, so the body's occurrence count is 3 * 2^d - 1"
            );
            assert!(
                u64::from(two_to_the(depth)) > u64::from(memoized_term(depth)),
                "and the occurrence count exceeds the distinct-support count, which is what makes \
                 the collapse a collapse"
            );
        }
    }

    #[test]
    fn the_memo_entry_count_matches_the_expansion_count_per_plane()
    {
        for depth in PINNED_DEPTHS {
            let (mut arena, declaration) = stage(|arena| shared_composite(arena, depth));
            let mut live: DefaultMemo = DefaultMemo::new();
            let (verdict, census) = check_with(&mut arena, &declaration, &mut live);
            assert_eq!(Ok(()), verdict);
            // The cross-check from the other direction: the memo's own entry count
            // is compared against the census the machines kept, per plane. A memo
            // that silently stopped recording, or a plane whose machine silently
            // stopped consulting it, separates the two numbers.
            assert_eq!(
                MemoEntryCount::from(
                    usize::try_from(u64::from(census.plane_expansions(SupportPlane::Term)))
                        .expect("the count fits")
                ),
                live.plane_entry_count(SupportPlane::Term),
                "one term-plane entry per term-plane expansion at depth {depth:?}"
            );
            assert_eq!(
                MemoEntryCount::from(
                    usize::try_from(u64::from(census.plane_expansions(SupportPlane::Type)))
                        .expect("the count fits")
                ),
                live.plane_entry_count(SupportPlane::Type),
                "one type-plane entry per type-plane expansion at depth {depth:?}"
            );
            assert_eq!(
                MemoEntryCount::from(
                    usize::try_from(u64::from(census.expansions())).expect("the count fits")
                ),
                live.entry_count(),
                "and the total agrees, so neither plane borrowed the other's entries"
            );
            assert!(
                u64::from(census.recalls()) > 0,
                "the memo actually answered, so the measurement is not of a memo nobody consulted"
            );
        }
    }

    #[test]
    fn sharing_costs_the_memoless_checker_nothing()
    {
        // The statement this pins is that sharing buys *checking* nothing without
        // the memo: the shared composite and its fully unshared spelling cost
        // the memoless checker identically, node check for node check.
        for depth in [CompositeDepth(8), CompositeDepth(12)] {
            let (mut shared_arena, shared_declaration) =
                stage(|arena| shared_composite(arena, depth));
            let mut null = NullMemo;
            let (shared_verdict, shared_census) =
                check_with(&mut shared_arena, &shared_declaration, &mut null);

            let (mut unshared_arena, unshared_declaration) =
                stage(|arena| unshared_composite(arena, depth));
            let mut null = NullMemo;
            let (unshared_verdict, unshared_census) =
                check_with(&mut unshared_arena, &unshared_declaration, &mut null);

            assert_eq!(Ok(()), shared_verdict, "the shared spelling checks");
            assert_eq!(Ok(()), unshared_verdict, "so does the unshared one");
            assert_eq!(
                shared_census.expansions(),
                unshared_census.expansions(),
                "the two spellings cost the memoless checker identically at depth {depth:?}"
            );
            assert_eq!(
                ExpansionCount::from(memoless_total(depth)),
                unshared_census.expansions(),
                "and both sit on the closed form"
            );

            // The memo is what turns the difference on.
            let (mut shared_arena, shared_declaration) =
                stage(|arena| shared_composite(arena, depth));
            let mut live: DefaultMemo = DefaultMemo::new();
            let (_verdict, shared_memoized) =
                check_with(&mut shared_arena, &shared_declaration, &mut live);
            assert!(
                shared_memoized.expansions() < unshared_census.expansions(),
                "with the memo on, the shared spelling costs strictly less"
            );
        }
    }

    // ---------------------------------------------------------------------------
    // Edit locality, measured within one check call
    // ---------------------------------------------------------------------------

    #[test]
    fn a_depth_d_edit_re_checks_its_spine_and_nothing_else()
    {
        for depth in PINNED_DEPTHS {
            let (mut arena, declaration) = stage(|arena| unedited_composite(arena, depth));
            let mut live: DefaultMemo = DefaultMemo::new();
            let (verdict, plain) = check_with(&mut arena, &declaration, &mut live);
            assert_eq!(
                Ok(()),
                verdict,
                "the unedited pair checks at depth {depth:?}"
            );

            let (mut arena, declaration) = stage(|arena| edited_composite(arena, depth));
            let mut live: DefaultMemo = DefaultMemo::new();
            let (verdict, edited) = check_with(&mut arena, &declaration, &mut live);
            assert_eq!(Ok(()), verdict, "the edited pair checks at depth {depth:?}");

            let extra = GoalCount(u64::from(arith::sub(
                arith::Int::from(u64::from(edited.plane_expansions(SupportPlane::Term))),
                arith::Int::from(u64::from(plain.plane_expansions(SupportPlane::Term))),
            )));
            assert_eq!(
                edit_locality(depth),
                extra,
                "a depth-{depth:?} edit re-checks exactly its d + 1 spine levels: the fresh leaf's \
                 own payload collapses with the original's because the key is content"
            );
            assert_eq!(
                plain.plane_expansions(SupportPlane::Type),
                edited.plane_expansions(SupportPlane::Type),
                "and the type plane does no extra work, because the edit changes no type"
            );

            // Anti-vacuity for this measurement: the spine is a vanishing fraction
            // of the occurrences it sits in.
            assert!(
                u64::from(extra) < u64::from(two_to_the(depth)),
                "the spine is a vanishing fraction of the 2^d occurrences it sits in"
            );
        }
    }

    // ---------------------------------------------------------------------------
    // The capability, at the public admission entry point
    // ---------------------------------------------------------------------------

    #[test]
    fn a_billion_occurrence_definition_admits_checked()
    {
        let mut environment = Environment::new();
        let staged = {
            let mut staging = environment.stage();
            let (declared, body) = shared_composite(staging.arena(), CAPABILITY_DEPTH);
            staging.def(LevelSignature::monomorphic(), declared, body)
        };
        assert!(
            environment.add_decl(staged).is_ok(),
            "a definition whose tree expansion is {} goals admits checked through the public choke \
             point, with no bypass",
            u64::from(memoless_total(CAPABILITY_DEPTH))
        );
        assert_eq!(
            1_342_177_278_u64,
            u64::from(memoless_total(CAPABILITY_DEPTH)),
            "and that is the number the memoless law names at depth 28"
        );
        let admitted = environment
            .entries()
            .first()
            .expect("the declaration was appended");
        assert!(
            matches!(admitted.admission(), Admission::Checked),
            "checked, not bypassed"
        );

        // The same shape through the opt-in entry, so the row's memoized columns are
        // asserted rather than merely predicted. The memoless columns are the closed
        // form's value and are deliberately never run.
        let (mut arena, declaration) = stage(|arena| shared_composite(arena, CAPABILITY_DEPTH));
        let mut live: DefaultMemo = DefaultMemo::new();
        let (verdict, census) = check_with(&mut arena, &declaration, &mut live);
        assert_eq!(Ok(()), verdict);
        assert_eq!(
            ExpansionCount::from(memoized_term(CAPABILITY_DEPTH)),
            census.plane_expansions(SupportPlane::Term),
            "d + 2 body checks at depth 28"
        );
        assert_eq!(
            ExpansionCount::from(memoized_type(CAPABILITY_DEPTH)),
            census.plane_expansions(SupportPlane::Type),
            "d + 1 type formations at depth 28"
        );
        assert_eq!(
            ExpansionCount::from(59_u64),
            census.expansions(),
            "fifty-nine goal expansions against the {} the memoless law names",
            u64::from(memoless_total(CAPABILITY_DEPTH))
        );
    }

    // ---------------------------------------------------------------------------
    // The differential: memoized equals memoless, verdict for verdict
    // ---------------------------------------------------------------------------

    #[test]
    fn memoized_checking_agrees_with_memoless_checking()
    {
        // Acceptances over the self-similar corpus, its unshared spelling, and the
        // edited spelling.
        for depth in [CompositeDepth(4), CompositeDepth(8)] {
            assert_eq!(
                Ok(()),
                verdicts_agree(|arena| shared_composite(arena, depth)),
                "the shared composite"
            );
            assert_eq!(
                Ok(()),
                verdicts_agree(|arena| unshared_composite(arena, depth)),
                "its unshared spelling"
            );
            assert_eq!(
                Ok(()),
                verdicts_agree(|arena| edited_composite(arena, depth)),
                "and the edited spelling"
            );
        }

        // A refusal: the same refusal, not merely a refusal.
        let refused = verdicts_agree(|arena| {
            let declared = arena.value_type_base(BaseType::Integer);
            let body = arena.value_unit();
            (declared, body)
        });
        assert!(
            matches!(refused, Err(KernelError::ValueTypeMismatch(_))),
            "unit does not inhabit the integers: {refused:?}"
        );

        // A closed subterm shared under two different binders.
        assert_eq!(
            Ok(()),
            verdicts_agree(|arena| {
                let integer = arena.value_type_base(BaseType::Integer);
                let unit_type = arena.value_type_unit();
                let closed = arena.value_unit();
                let inner_return = arena.computation_return(closed);
                let integer_arrow = {
                    let returner = arena.comp_type_returner(unit_type);
                    arena.comp_type_arrow(integer, returner)
                };
                let unit_arrow = {
                    let returner = arena.comp_type_returner(unit_type);
                    arena.comp_type_arrow(unit_type, returner)
                };
                let first = arena.computation_lambda(inner_return);
                let second = arena.computation_lambda(inner_return);
                let first_thunk = arena.value_thunk(first);
                let second_thunk = arena.value_thunk(second);
                let first_type = arena.value_type_thunk(integer_arrow);
                let second_type = arena.value_type_thunk(unit_arrow);
                let declared = arena.value_type_product(first_type, second_type);
                let body = arena.value_pair(first_thunk, second_thunk);
                (declared, body)
            }),
            "one closed body under binders of two different types"
        );

        // A binder-reading subterm shared under binders of different types: the
        // identity under `Integer` and under `Unit`.
        assert_eq!(
            Ok(()),
            verdicts_agree(|arena| {
                let integer = arena.value_type_base(BaseType::Integer);
                let unit_type = arena.value_type_unit();
                let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
                let body = arena.computation_return(variable);
                let lambda = arena.computation_lambda(body);
                let integer_arrow = {
                    let returner = arena.comp_type_returner(integer);
                    arena.comp_type_arrow(integer, returner)
                };
                let unit_arrow = {
                    let returner = arena.comp_type_returner(unit_type);
                    arena.comp_type_arrow(unit_type, returner)
                };
                let first_thunk = arena.value_thunk(lambda);
                let second_thunk = arena.value_thunk(lambda);
                let first_type = arena.value_type_thunk(integer_arrow);
                let second_type = arena.value_type_thunk(unit_arrow);
                let declared = arena.value_type_product(first_type, second_type);
                let body = arena.value_pair(first_thunk, second_thunk);
                (declared, body)
            }),
            "one binder-reading body under binders of two different types"
        );
    }

    // ---------------------------------------------------------------------------
    // Poisoned entries: both directions, both planes, all permanent suite members
    // ---------------------------------------------------------------------------

    /// Stage the refusing declaration the term-plane poison turns into an
    /// acceptance: `def _ : Integer = ()`.
    ///
    /// # Specification
    /// trivial.
    fn refusing_declaration(arena: &mut TermArena) -> (ValueTypeId, ValueId)
    {
        let declared = arena.value_type_base(BaseType::Integer);
        let body = arena.value_unit();
        (declared, body)
    }

    #[test]
    fn a_poisoned_term_entry_turns_a_refusal_into_an_acceptance()
    {
        let (mut arena, declaration) = stage(refusing_declaration);
        let mut null = NullMemo;
        let (honest, _census) = check_with(&mut arena, &declaration, &mut null);
        assert!(
            matches!(honest, Err(KernelError::ValueTypeMismatch(_))),
            "the honest verdict is a refusal: {honest:?}"
        );

        let (mut arena, declaration) = stage(refusing_declaration);
        let DeclarationContent::Def { declared, body } = *declaration.content()
        else {
            panic!("the fixture is a definition");
        };
        let mut poisoned: DefaultMemo = DefaultMemo::new();
        let mut session = SupportContext::new();
        let support = NodeSupport::build(
            &arena,
            &mut session,
            SupportGoal::CheckValue(body, declared),
            &[],
        );
        poisoned
            .remember(support, NodeOutcome::Checked)
            .expect("the poisoned entry records");
        let (poisoned_verdict, census) =
            check_in_session(&mut arena, &declaration, &mut poisoned, &mut session);

        assert_eq!(
            Ok(()),
            poisoned_verdict,
            "one entry claiming a value already checked against a type it refuses turns the refusal \
             into an acceptance — which is what makes the differential's negative direction bite"
        );
        assert_eq!(
            ExpansionCount::from(1),
            census.plane_recalls(SupportPlane::Term),
            "and the poison was reached exactly once, so the case is not green by never running"
        );
    }

    #[test]
    fn an_entry_differing_only_in_its_binder_component_is_not_served()
    {
        // `def _ : U (Unit -> F Integer) = thunk (\ x. return x)` refuses: the
        // bound variable has type `Unit` and the codomain demands `Integer`.
        let build = |arena: &mut TermArena| {
            let integer = arena.value_type_base(BaseType::Integer);
            let unit_type = arena.value_type_unit();
            let returner = arena.comp_type_returner(integer);
            let arrow = arena.comp_type_arrow(unit_type, returner);
            let declared = arena.value_type_thunk(arrow);
            let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
            let body = arena.computation_return(variable);
            let lambda = arena.computation_lambda(body);
            let thunk = arena.value_thunk(lambda);
            (declared, thunk)
        };

        let (mut arena, declaration) = stage(build);
        let mut null = NullMemo;
        let (honest, _census) = check_with(&mut arena, &declaration, &mut null);
        assert!(
            matches!(honest, Err(KernelError::ValueTypeMismatch(_))),
            "the honest verdict is a refusal: {honest:?}"
        );

        // The goal the poison targets: synthesizing the bound variable's type. In
        // the real check its telescope is `[Unit]`.
        let mut arena = TermArena::new();
        let declaration = {
            let mut builder = DeclarationBuilder::new(&mut arena);
            let (declared, body) = build(builder.arena());
            builder.def(LevelSignature::monomorphic(), declared, body)
        };
        let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
        let integer = arena.value_type_base(BaseType::Integer);
        let unit_type = arena.value_type_unit();

        // Poisoned under the *wrong* telescope: the entry claims the variable
        // synthesizes `Integer` when the binder is an `Integer`, which is true and
        // useless here, because the real check runs under a `Unit` binder.
        let mut wrong: DefaultMemo = DefaultMemo::new();
        let mut wrong_session = SupportContext::new();
        let wrong_support = NodeSupport::build(
            &arena,
            &mut wrong_session,
            SupportGoal::SynthValue(variable),
            &[integer],
        );
        wrong
            .remember(wrong_support, NodeOutcome::ValueType(integer))
            .expect("the entry records");
        let (unchanged, unchanged_census) =
            check_in_session(&mut arena, &declaration, &mut wrong, &mut wrong_session);
        assert!(
            matches!(unchanged, Err(KernelError::ValueTypeMismatch(_))),
            "an entry differing only in its binder component is not served, so the verdict stands: \
             {unchanged:?}"
        );
        assert_eq!(
            ExpansionCount::from(0),
            unchanged_census.plane_recalls(SupportPlane::Term),
            "and nothing at all was served, which is the exercised-path claim"
        );

        // The positive control: the same entry under the telescope the check
        // actually runs under *does* change the verdict, so the case above is
        // measuring the binder component and not an inert poison.
        let mut right: DefaultMemo = DefaultMemo::new();
        let mut right_session = SupportContext::new();
        let right_support = NodeSupport::build(
            &arena,
            &mut right_session,
            SupportGoal::SynthValue(variable),
            &[unit_type],
        );
        right
            .remember(right_support, NodeOutcome::ValueType(integer))
            .expect("the entry records");
        let (changed, changed_census) =
            check_in_session(&mut arena, &declaration, &mut right, &mut right_session);
        assert_eq!(
            Ok(()),
            changed,
            "under the matching telescope the same poison turns the refusal into an acceptance"
        );
        assert_eq!(
            ExpansionCount::from(1),
            changed_census.plane_recalls(SupportPlane::Term),
            "served exactly once"
        );
    }

    #[test]
    fn a_poisoned_type_entry_turns_admission_into_a_universe_refusal()
    {
        // `axiom _ : Lift (Universe 0) 2` admits: `Universe 0` forms at level 1,
        // and 1 is strictly below 2.
        let stage_axiom = |arena: &mut TermArena| {
            let inner = arena.value_type_universe(GroundSort::Value, level(LevelConstant::from(0)));
            let declared = arena.value_type_lift(inner, level(LevelConstant::from(2)));
            (declared, inner)
        };

        let mut arena = TermArena::new();
        let (declaration, inner) = {
            let mut builder = DeclarationBuilder::new(&mut arena);
            let (declared, inner) = stage_axiom(builder.arena());
            (
                builder.axiom(LevelSignature::monomorphic(), declared),
                inner,
            )
        };
        let mut null = NullMemo;
        let (honest, _census) = check_with(&mut arena, &declaration, &mut null);
        assert_eq!(Ok(()), honest, "the honest verdict is an acceptance");

        let mut poisoned: DefaultMemo = DefaultMemo::new();
        let mut session = SupportContext::new();
        let support =
            NodeSupport::build(&arena, &mut session, SupportGoal::ValueTypeLevel(inner), &[
            ]);
        poisoned
            .remember(support, NodeOutcome::Formed(level(LevelConstant::from(5))))
            .expect("the poisoned entry records");
        let (poisoned_verdict, census) =
            check_in_session(&mut arena, &declaration, &mut poisoned, &mut session);
        assert!(
            matches!(poisoned_verdict, Err(KernelError::UniverseViolation(_))),
            "a poisoned formation entry claiming a higher level than the type has turns the \
             admission into a universe-violation refusal: {poisoned_verdict:?}"
        );
        assert_eq!(
            ExpansionCount::from(1),
            census.plane_recalls(SupportPlane::Type),
            "and it was served exactly once, on the type plane"
        );
    }

    #[test]
    fn a_term_shaped_answer_in_a_type_support_is_declined_and_recomputed()
    {
        let mut arena = TermArena::new();
        let (declaration, inner) = {
            let mut builder = DeclarationBuilder::new(&mut arena);
            let inner = builder
                .arena()
                .value_type_universe(GroundSort::Value, level(LevelConstant::from(0)));
            let declared = builder
                .arena()
                .value_type_lift(inner, level(LevelConstant::from(2)));
            (
                builder.axiom(LevelSignature::monomorphic(), declared),
                inner,
            )
        };

        let mut honest_memo: DefaultMemo = DefaultMemo::new();
        let (honest, honest_census) = check_with(&mut arena, &declaration, &mut honest_memo);
        assert_eq!(Ok(()), honest, "the honest verdict is an acceptance");

        // The same support, filled with an answer only the *term* machine could
        // have produced.
        let mut confused: DefaultMemo = DefaultMemo::new();
        let mut session = SupportContext::new();
        let support =
            NodeSupport::build(&arena, &mut session, SupportGoal::ValueTypeLevel(inner), &[
            ]);
        confused
            .remember(support, NodeOutcome::Checked)
            .expect("the entry records");
        let (verdict, census) =
            check_in_session(&mut arena, &declaration, &mut confused, &mut session);
        assert_eq!(
            Ok(()),
            verdict,
            "a support carrying the wrong shape is declined rather than trusted"
        );
        assert_eq!(
            ExpansionCount::from(0),
            census.plane_recalls(SupportPlane::Type),
            "the entry was not served"
        );
        assert_eq!(
            honest_census.plane_expansions(SupportPlane::Type),
            census.plane_expansions(SupportPlane::Type),
            "and the goal was recomputed, at exactly the cost of not having had an entry at all"
        );
    }

    #[test]
    fn a_formation_shaped_answer_in_a_term_support_is_declined_and_recomputed()
    {
        // The mirror of the type-plane case, on the term plane: a formation level
        // cannot be the answer to a term goal.
        let (mut arena, declaration) = stage(|arena| {
            let declared = arena.value_type_unit();
            let body = arena.value_unit();
            (declared, body)
        });
        let DeclarationContent::Def { declared, body } = *declaration.content()
        else {
            panic!("the fixture is a definition");
        };

        let mut honest_memo: DefaultMemo = DefaultMemo::new();
        let (honest, honest_census) = check_with(&mut arena, &declaration, &mut honest_memo);
        assert_eq!(Ok(()), honest);

        let mut confused: DefaultMemo = DefaultMemo::new();
        let mut session = SupportContext::new();
        let support = NodeSupport::build(
            &arena,
            &mut session,
            SupportGoal::CheckValue(body, declared),
            &[],
        );
        confused
            .remember(support, NodeOutcome::Formed(level(LevelConstant::from(9))))
            .expect("the entry records");
        let (verdict, census) =
            check_in_session(&mut arena, &declaration, &mut confused, &mut session);
        assert_eq!(Ok(()), verdict, "declined rather than trusted");
        assert_eq!(
            ExpansionCount::from(0),
            census.plane_recalls(SupportPlane::Term),
            "the entry was not served"
        );
        assert_eq!(
            honest_census.plane_expansions(SupportPlane::Term),
            census.plane_expansions(SupportPlane::Term),
            "and the goal was recomputed"
        );
    }

    #[test]
    fn the_public_admission_entry_cannot_be_handed_a_memo()
    {
        // A structural claim, asserted the only way a test can assert one: the
        // admitting surface takes a staged declaration and nothing else, and the
        // memo-taking entry returns a verdict rather than a receipt. A poisoned
        // memo can therefore change a *check* and can never produce an admission.
        let mut environment = Environment::new();
        let staged = {
            let mut staging = environment.stage();
            let declared = staging.arena().value_type_base(BaseType::Integer);
            let body = staging.arena().value_unit();
            staging.def(LevelSignature::monomorphic(), declared, body)
        };
        assert!(
            environment.add_decl(staged).is_err(),
            "admission re-derives the obligation with a memo it built itself"
        );
        assert!(
            environment.entries().is_empty(),
            "and nothing entered the environment"
        );
    }

    /// The two rewrite machines account to their own planes through a real
    /// check, and the shifting machine's reuse is real rather than assumed.
    ///
    /// The fixture is a thunked dependent arrow applied to a value under a
    /// lambda, so the check reaches both wiring sites: every variable
    /// synthesis raises its context slot past the binders between them, and
    /// the application at the dependent head instantiates the codomain at
    /// its argument.
    ///
    /// **Both planes are asserted, and the shifting plane's count is the
    /// load-bearing one.** A rewrite that stopped being consulted would
    /// leave its plane at zero, which is exactly the silent regression a
    /// hit-rate assertion would miss.
    #[test]
    fn the_rewrite_planes_account_separately_through_a_real_check()
    {
        let mut arena = TermArena::new();
        let declaration = {
            let mut builder = DeclarationBuilder::new(&mut arena);
            let mint = builder.arena();
            // `λ f. λ x. force f x`, at `U (Π (_ : Unit). F Unit) → Unit → F Unit`
            // spelled with the dependent arrow so the application's dependent arm
            // fires.
            let unit_type = mint.value_type_unit();
            let returner = mint.comp_type_returner(unit_type);
            let dependent = mint.comp_type_pi(unit_type, returner);
            let function_thunk = mint.value_type_thunk(dependent);
            let inner = mint.comp_type_arrow(unit_type, returner);
            let outer = mint.comp_type_arrow(function_thunk, inner);
            let declared = mint.value_type_thunk(outer);

            let argument = mint.value_variable(DeBruijnIndex::from(0_u32));
            let function = mint.value_variable(DeBruijnIndex::from(1_u32));
            let head = mint.computation_force(function);
            let application = mint.computation_application(head, argument);
            let inner_lambda = mint.computation_lambda(application);
            let outer_lambda = mint.computation_lambda(inner_lambda);
            let body = mint.value_thunk(outer_lambda);
            builder.def(LevelSignature::monomorphic(), declared, body)
        };

        let mut session = SupportContext::new();
        let mut memo: DefaultMemo = DefaultMemo::new();
        let (verdict, _census) =
            check_in_session(&mut arena, &declaration, &mut memo, &mut session);
        assert_eq!(Ok(()), verdict, "the dependent application checks");

        assert_ne!(
            MemoEntryCount::from(0_usize),
            session.rewrite_entry_count(RewritePlane::Shift),
            "the shifting machine ran: every variable synthesis raises its context slot"
        );
        assert_ne!(
            MemoEntryCount::from(0_usize),
            session.rewrite_entry_count(RewritePlane::Substitute),
            "and the substitution machine ran: the dependent head's codomain was instantiated"
        );
    }

    /// The polymorphic identity, as a fixture: `Π (A : U 0). Π (_ : El A). F
    /// (El A)` inhabited by `λ A. λ x. return x`.
    ///
    /// # Specification
    /// - requires: `arena` is the one this declaration's content is minted
    ///   into.
    /// - ensures: the polymorphic identity as a declaration: a thunk of two
    ///   nested dependent functions, whose codomain reads its type off the code
    ///   the outer binder bound.
    /// - provides: the dependent fixture the zero-drift differential is run
    ///   over, which is where a key that dropped the reached binder slice would
    ///   serve one type's level for another's.
    /// - fails: never.
    /// - panics: none.
    fn dependent_identity(arena: &mut TermArena) -> (ValueTypeId, ValueId)
    {
        let zero = level(LevelConstant::from(0));
        let universe = arena.value_type_universe(GroundSort::Value, zero.clone());
        let outer_code = arena.value_variable(DeBruijnIndex::from(0_u32));
        let domain = arena.value_type_element(outer_code, zero.clone());
        let inner_code = arena.value_variable(DeBruijnIndex::from(1_u32));
        let result = arena.value_type_element(inner_code, zero);
        let returner = arena.comp_type_returner(result);
        let inner = arena.comp_type_pi(domain, returner);
        let outer = arena.comp_type_pi(universe, inner);
        let declared = arena.value_type_thunk(outer);

        let returned = arena.value_variable(DeBruijnIndex::from(0_u32));
        let body = arena.computation_return(returned);
        let inner_lambda = arena.computation_lambda(body);
        let outer_lambda = arena.computation_lambda(inner_lambda);
        let thunk = arena.value_thunk(outer_lambda);
        (declared, thunk)
    }

    /// The same shape with a code that inhabits nothing: the type is read off
    /// the unit *value*, whose type is the unit type rather than a
    /// universe.
    ///
    /// # Specification
    /// - requires: `arena` is the one this declaration's content is minted
    ///   into.
    /// - ensures: the same shape over a code that inhabits nothing — the type
    ///   is read off the unit value, whose type is the unit type rather than a
    ///   universe — so the declaration is refused.
    /// - provides: the refusal half of the dependent differential, so agreement
    ///   is asserted in both directions.
    /// - fails: never.
    /// - panics: none.
    fn bad_code_identity(arena: &mut TermArena) -> (ValueTypeId, ValueId)
    {
        let zero = level(LevelConstant::from(0));
        let not_a_code = arena.value_unit();
        let result = arena.value_type_element(not_a_code, zero);
        let returner = arena.comp_type_returner(result);
        let unit_type = arena.value_type_unit();
        let arrow = arena.comp_type_arrow(unit_type, returner);
        let declared = arena.value_type_thunk(arrow);
        let returned = arena.value_variable(DeBruijnIndex::from(0_u32));
        let body = arena.computation_return(returned);
        let lambda = arena.computation_lambda(body);
        let thunk = arena.value_thunk(lambda);
        (declared, thunk)
    }

    /// The zero-drift differential over the dependent shapes, in **both**
    /// directions.
    ///
    /// The dependent path is where a memo can serve a wrong answer: a type's
    /// formation depends on the binder slice its codes reach, and a key that
    /// dropped that slice would serve one type's level for another's.
    /// So the acceptance and the refusal are both differentialed, and the
    /// refusal is compared as the *same* refusal rather than merely as a
    /// refusal.
    #[test]
    fn dependent_checking_agrees_memoized_and_memoless()
    {
        assert_eq!(
            Ok(()),
            verdicts_agree(dependent_identity),
            "the dependent identity admits at both memo instantiations"
        );
        let refusal = verdicts_agree(bad_code_identity);
        assert!(
            matches!(refusal, Err(KernelError::ValueTypeMismatch(_))),
            "and a code that is not of its declared universe is refused at both, alike: {refusal:?}"
        );
    }

    /// The formation walk owes code obligations and the driver drains them
    /// through the checking machine, so the term plane records expansions
    /// the declaration's own body never asked for.
    ///
    /// Asserted as an inequality between the dependent shape and the same shape
    /// with its codes replaced by closed types: a drain that stopped running
    /// would leave the two equal.
    #[test]
    fn draining_code_obligations_reaches_the_checking_machine()
    {
        let (mut arena, declaration) = stage(dependent_identity);
        let mut memo: DefaultMemo = DefaultMemo::new();
        let (verdict, dependent_census) = check_with(&mut arena, &declaration, &mut memo);
        assert_eq!(Ok(()), verdict, "the dependent identity checks");

        let (mut closed_arena, closed_declaration) = stage(|arena| {
            let unit_type = arena.value_type_unit();
            let returner = arena.comp_type_returner(unit_type);
            let inner = arena.comp_type_pi(unit_type, returner);
            let outer = arena.comp_type_pi(unit_type, inner);
            let declared = arena.value_type_thunk(outer);
            let returned = arena.value_variable(DeBruijnIndex::from(0_u32));
            let body = arena.computation_return(returned);
            let inner_lambda = arena.computation_lambda(body);
            let outer_lambda = arena.computation_lambda(inner_lambda);
            let thunk = arena.value_thunk(outer_lambda);
            (declared, thunk)
        });
        let mut closed_memo: DefaultMemo = DefaultMemo::new();
        let (closed_verdict, closed_census) =
            check_with(&mut closed_arena, &closed_declaration, &mut closed_memo);
        assert_eq!(Ok(()), closed_verdict, "the closed shape checks too");

        assert!(
            u64::from(dependent_census.plane_expansions(SupportPlane::Term))
                > u64::from(closed_census.plane_expansions(SupportPlane::Term)),
            "the codes are checked through the term machine, which the closed shape never asks for"
        );
    }
}
