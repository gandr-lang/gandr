//! Evaluate, read back, and compare the term against one written out by hand.
//!
//! The unit suites separate each decision surface of the readback machine one
//! assertion at a time. This suite pins whole answers: for each source term, an
//! **independently written** expected term is built in the same arena and the
//! two are compared structurally.
//!
//! The oracle is external by construction. Comparing a readback against another
//! run of the same machine — or against the term that was evaluated — would be
//! blind to any fault that shifted both sides, which is exactly the class a
//! differential suite is supposed to catch. A hand-written expected term shares
//! no code with the machine, so a machine that normalizes wrongly disagrees
//! with it.
//!
//! Structural comparison is what the pinning needs: readback mints fresh nodes,
//! so the answer and the expectation are equal terms at different ids, and the
//! arena's own derived equality is id equality by design.

extern crate alloc;

/// The structural oracle shared with duplication witnesses.
#[cfg(test)]
#[path = "support/trees.rs"]
mod trees;

/// The pinned-term cases, in a `cfg(test)` module so the crate's lint wall
/// reads them as test code rather than as shipping code.
#[cfg(test)]
mod readback_terms
{
    use anodized::spec;
    use gandr_core_nbe::Definitions;
    use gandr_core_nbe::DomainArena;
    use gandr_core_nbe::Fuel;
    use gandr_core_nbe::LoweredChain;
    use gandr_core_nbe::ReadbackMode;
    use gandr_core_nbe::eval_computation;
    use gandr_core_nbe::eval_value;
    use gandr_core_nbe::readback_computation;
    use gandr_core_nbe::readback_value;
    use gandr_core_term::CoreArena;
    use gandr_core_term::DefinitionalEnvironment;
    use gandr_core_term::Zone;
    use gandr_kernel_strata::Level;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::IntegerLiteral;
    use gandr_kernel_term::Literal;
    use gandr_kernel_term::Magnitude;
    use gandr_kernel_term::Side;
    use gandr_kernel_term::Sign;

    use crate::trees::Term;
    use crate::trees::Trees;
    use crate::trees::same_tree;

    /// Ample fuel for every case that is meant to finish.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a budget far above the step count any fixture below needs, so
    ///   an exhaustion refusal in one of them is a defect rather than a tight
    ///   budget.
    /// - provides: the budget every case here is run with.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the fixed budget is not a normalization oracle. The
    ///   executable value guard records the supplied budget; the binder and
    ///   stuck-spine fixtures reaching their independently written terms
    ///   witness that it is ample rather than merely positive.
    /// - witness: `readback_terms::readback_terms::a_redex_under_a_binder_normalizes_to_the_term_written_out_by_hand`
    /// - witness: `readback_terms::readback_terms::a_stuck_elimination_normalizes_to_the_spine_written_out_by_hand`
    #[spec(
        ensures: |ret| ret == Fuel::from(4_096_u32)
    )]
    fn ample() -> Fuel
    {
        Fuel::from(4_096_u32)
    }

    /// The index at the innermost binder.
    ///
    /// # Specification
    /// trivial.
    fn innermost() -> DeBruijnIndex
    {
        DeBruijnIndex::from(0_u32)
    }

    /// An empty chain and environment, which unfold nothing.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: an empty chain and an empty definitional environment, so
    ///   every constant reads as not manifest and no run unfolds.
    /// - provides: the definition side of every fixture that is about
    ///   rebuilding rather than unfolding.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — no declarations means no body can unfold, regardless
    ///   of a queried constant. The empty admission sequence is the observer;
    ///   the stuck-case and unreduced-source witnesses distinguish accidental
    ///   unfolding from rebuilding.
    /// - witness: `readback_terms::readback_terms::a_stuck_elimination_normalizes_to_the_spine_written_out_by_hand`
    /// - witness: `readback_terms::readback_terms::an_unreduced_term_reads_back_as_the_id_it_was_evaluated_from`
    #[spec(
        ensures: |ret| ret.0.chain().entries().is_empty()
    )]
    fn nothing_unfolds() -> (LoweredChain, DefinitionalEnvironment)
    {
        (LoweredChain::new(), DefinitionalEnvironment::new())
    }

    #[test]
    fn the_comparator_reads_static_formers()
    {
        let mut core = CoreArena::new();
        let first = core.value_unit();
        let second = core.value_unit();
        let left = core.value_static_lambda(first);
        let right = core.value_static_lambda(second);
        assert!(
            matches!(
                same_tree(&core, Term::Value(left), &core, Term::Value(right)),
                Trees::Same
            ),
            "equal static abstractions agree even at distinct ids"
        );
        assert!(
            !matches!(
                same_tree(&core, Term::Value(left), &core, Term::Value(first)),
                Trees::Same
            ),
            "a static abstraction is not its body"
        );
        let applied_left = core.value_static_application(left, first);
        let applied_right = core.value_static_application(right, second);
        let swapped = core.value_static_application(second, right);
        assert_eq!(
            Trees::Same,
            same_tree(
                &core,
                Term::Value(applied_left),
                &core,
                Term::Value(applied_right)
            )
        );
        assert_eq!(
            Trees::Different,
            same_tree(
                &core,
                Term::Value(applied_left),
                &core,
                Term::Value(swapped)
            )
        );
    }

    #[test]
    fn the_comparator_descends_into_quoted_type_families()
    {
        let mut core = CoreArena::new();
        let first = core.value_type_unit();
        let second = core.value_type_unit();
        let atom = core.value_type_abstract(ConstantIndex::from(7_usize));
        let left = core.value_type_product(first, atom);
        let right = core.value_type_product(second, atom);
        let swapped = core.value_type_product(atom, second);
        let other_former = core.value_type_sum(second, atom);
        let left_returner = core.comp_type_returner(left);
        let right_returner = core.comp_type_returner(right);
        let left_arrow = core.comp_type_arrow(first, left_returner);
        let right_arrow = core.comp_type_arrow(second, right_returner);
        let pi = core.comp_type_pi(second, right_returner);
        let left_thunk = core.value_type_thunk(left_arrow);
        let right_thunk = core.value_type_thunk(right_arrow);
        let one = Level::zero().succ().expect("level one");
        let two = one.succ().expect("level two");
        let left_lift = core.value_type_lift(left_thunk, one.clone());
        let right_lift = core.value_type_lift(right_thunk, one);
        let wrong_lift = core.value_type_lift(right_thunk, two);
        let left_static = core.value_type_static_pi(first, left_lift);
        let right_static = core.value_type_static_pi(second, right_lift);
        let wrong_static = core.value_type_static_pi(second, wrong_lift);
        for (left, right, expected) in [
            (left, right, Trees::Same),
            (left, swapped, Trees::Different),
            (left, other_former, Trees::Different),
            (left_static, right_static, Trees::Same),
            (left_static, wrong_static, Trees::Different),
        ] {
            let left = core.value_quote(left);
            let right = core.value_quote(right);
            assert_eq!(
                expected,
                same_tree(&core, Term::Value(left), &core, Term::Value(right))
            );
        }
        let left = core.value_quote_computation(left_arrow);
        let right = core.value_quote_computation(right_arrow);
        let other = core.value_quote_computation(pi);
        assert_eq!(
            Trees::Same,
            same_tree(&core, Term::Value(left), &core, Term::Value(right))
        );
        assert_eq!(
            Trees::Different,
            same_tree(&core, Term::Value(left), &core, Term::Value(other))
        );

        let mut empty = CoreArena::new();
        let missing_type = empty.value_quote(first);
        let missing_comp_type = empty.value_quote_computation(left_returner);
        for missing in [missing_type, missing_comp_type] {
            assert_eq!(
                Trees::Different,
                same_tree(&empty, Term::Value(missing), &empty, Term::Value(missing)),
                "identity does not hide a missing quoted child"
            );
        }
    }
    #[test]
    fn the_comparator_separates_terms_it_is_asked_to_pin()
    {
        // The oracle is the thing every other case in this file trusts, so it
        // is checked against itself first: equal shapes at different ids agree,
        // and each way of differing — a former, a payload, a child, a binder
        // index — disagrees.
        let mut core = CoreArena::new();
        let first = core.value_unit();
        let second = core.value_unit();
        let one = core.value_pair(first, second);
        let other = core.value_pair(second, first);
        assert!(
            matches!(
                same_tree(&core, Term::Value(one), &core, Term::Value(other)),
                Trees::Same
            ),
            "two pairs of units are the same term at different ids"
        );

        let occurrence = core.value_variable(Zone::Intuitionistic, innermost());
        let outer = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
        let linear = core.value_variable(Zone::Linear, innermost());
        assert!(
            !matches!(
                same_tree(&core, Term::Value(occurrence), &core, Term::Value(outer)),
                Trees::Same
            ),
            "two indices are two different occurrences"
        );
        assert!(
            !matches!(
                same_tree(&core, Term::Value(occurrence), &core, Term::Value(linear)),
                Trees::Same
            ),
            "and so are one index in two zones"
        );
        assert!(
            !matches!(
                same_tree(&core, Term::Value(occurrence), &core, Term::Value(first)),
                Trees::Same
            ),
            "different formers are different terms"
        );

        let mixed = core.value_pair(first, occurrence);
        assert!(
            !matches!(
                same_tree(&core, Term::Value(one), &core, Term::Value(mixed)),
                Trees::Same
            ),
            "a difference in a child is a difference in the term"
        );

        let left = core.value_injection(Side::Left, first);
        let right = core.value_injection(Side::Right, first);
        assert!(
            !matches!(
                same_tree(&core, Term::Value(left), &core, Term::Value(right)),
                Trees::Same
            ),
            "and a difference in a payload the walk cannot recurse through is one too"
        );

        let returner = core.computation_return(first);
        let forced = core.computation_force(first);
        assert!(
            !matches!(
                same_tree(
                    &core,
                    Term::Computation(returner),
                    &core,
                    Term::Computation(forced)
                ),
                Trees::Same
            ),
            "the negative table separates its formers the same way"
        );

        // Every remaining arm of both tables, each at a difference the walk
        // must notice. An arm that answered `true` unconditionally would be a
        // comparator that pins nothing, so each is charged once.
        let here = core.value_constant(ConstantIndex::from(1_usize));
        let there = core.value_constant(ConstantIndex::from(2_usize));
        assert!(
            matches!(
                same_tree(&core, Term::Value(here), &core, Term::Value(here)),
                Trees::Same
            ),
            "one admission position is one reference"
        );
        assert!(
            !matches!(
                same_tree(&core, Term::Value(here), &core, Term::Value(there)),
                Trees::Same
            ),
            "and two are two, which the arm compares rather than assumes"
        );

        let zero = core.value_literal(Literal::Integer(IntegerLiteral::new(
            Sign::NonNegative,
            Magnitude::zero(),
        )));
        let also_zero = core.value_literal(Literal::Integer(IntegerLiteral::new(
            Sign::NonNegative,
            Magnitude::zero(),
        )));
        let digits = Magnitude::from_decimal_text(String::from("7"))
            .expect("a single decimal digit is a magnitude");
        let seven = core.value_literal(Literal::Integer(IntegerLiteral::new(
            Sign::NonNegative,
            digits.clone(),
        )));
        let negative_seven = core.value_literal(Literal::Integer(IntegerLiteral::new(
            Sign::Negative,
            digits,
        )));
        assert!(
            matches!(
                same_tree(&core, Term::Value(zero), &core, Term::Value(also_zero)),
                Trees::Same
            ),
            "equal literal payloads at different ids are one term"
        );
        assert!(
            !matches!(
                same_tree(&core, Term::Value(zero), &core, Term::Value(seven)),
                Trees::Same
            ),
            "a difference in the magnitude is a difference in the term"
        );
        assert!(
            !matches!(
                same_tree(
                    &core,
                    Term::Value(seven),
                    &core,
                    Term::Value(negative_seven)
                ),
                Trees::Same
            ),
            "and so is a difference in the sign, which is the whole of the leaf arm — the \
             zero magnitude would witness neither, because the literal has no negative zero"
        );

        let one_level = Level::zero().succ().expect("level one exists");
        let two_level = one_level.succ().expect("level two exists");
        let lifted_low = core.value_lift(one_level.clone(), first);
        let lifted_low_again = core.value_lift(one_level, second);
        let lifted_high = core.value_lift(two_level, first);
        assert!(
            matches!(
                same_tree(
                    &core,
                    Term::Value(lifted_low),
                    &core,
                    Term::Value(lifted_low_again)
                ),
                Trees::Same
            ),
            "one target over equal bodies is one lift"
        );
        assert!(
            !matches!(
                same_tree(
                    &core,
                    Term::Value(lifted_low),
                    &core,
                    Term::Value(lifted_high)
                ),
                Trees::Same
            ),
            "and the target is compared, not carried past"
        );

        let suspend_returner = core.value_thunk(returner);
        let suspend_forced = core.value_thunk(forced);
        assert!(
            !matches!(
                same_tree(
                    &core,
                    Term::Value(suspend_returner),
                    &core,
                    Term::Value(suspend_forced)
                ),
                Trees::Same
            ),
            "a thunk is compared through the computation it suspends, which is the one \
             value arm that crosses polarity"
        );

        let abstraction = core.computation_lambda(returner);
        let other_abstraction = core.computation_lambda(forced);
        assert!(
            !matches!(
                same_tree(
                    &core,
                    Term::Computation(abstraction),
                    &core,
                    Term::Computation(other_abstraction)
                ),
                Trees::Same
            ),
            "a lambda is compared through its body"
        );

        let applied = core.computation_application(returner, first);
        let applied_elsewhere = core.computation_application(returner, occurrence);
        let applied_to_other = core.computation_application(forced, first);
        assert!(
            !matches!(
                same_tree(
                    &core,
                    Term::Computation(applied),
                    &core,
                    Term::Computation(applied_elsewhere)
                ),
                Trees::Same
            ),
            "an application is compared through its argument"
        );
        assert!(
            !matches!(
                same_tree(
                    &core,
                    Term::Computation(applied),
                    &core,
                    Term::Computation(applied_to_other)
                ),
                Trees::Same
            ),
            "and through its head, so neither child is dropped"
        );

        let sequenced = core.computation_bind(returner, forced);
        let sequenced_other_way = core.computation_bind(forced, returner);
        assert!(
            !matches!(
                same_tree(
                    &core,
                    Term::Computation(sequenced),
                    &core,
                    Term::Computation(sequenced_other_way)
                ),
                Trees::Same
            ),
            "a bind is compared in both positions, so a comparator that swapped them \
             would call these equal"
        );

        let cased = core.computation_case(first, returner, forced);
        let cased_other_scrutinee = core.computation_case(occurrence, returner, forced);
        let cased_swapped = core.computation_case(first, forced, returner);
        assert!(
            !matches!(
                same_tree(
                    &core,
                    Term::Computation(cased),
                    &core,
                    Term::Computation(cased_other_scrutinee)
                ),
                Trees::Same
            ),
            "a case is compared through its scrutinee"
        );
        assert!(
            !matches!(
                same_tree(
                    &core,
                    Term::Computation(cased),
                    &core,
                    Term::Computation(cased_swapped)
                ),
                Trees::Same
            ),
            "and through each branch in its own position"
        );

        // The resolution guard: an id minted by another arena names no node
        // here, and the comparator answers that they are not the same term
        // rather than treating an unresolvable pair as vacuously equal — which
        // would make every assertion above pass on a truncated arena.
        let mut other_arena = CoreArena::new();
        let mut stranger = other_arena.value_unit();
        let mut stranger_comp = other_arena.computation_return(stranger);
        let mut remaining = 32_usize;
        while remaining > 0 {
            stranger = other_arena.value_pair(stranger, stranger);
            stranger_comp = other_arena.computation_bind(stranger_comp, stranger_comp);
            remaining = remaining.saturating_sub(1);
        }
        assert!(
            !matches!(
                same_tree(&core, Term::Value(first), &core, Term::Value(stranger)),
                Trees::Same
            ),
            "an unresolvable value id is not the same term as anything"
        );
        assert!(
            !matches!(
                same_tree(
                    &core,
                    Term::Computation(returner),
                    &core,
                    Term::Computation(stranger_comp)
                ),
                Trees::Same
            ),
            "and neither is an unresolvable computation id"
        );
    }

    #[test]
    fn a_redex_normalizes_to_the_term_written_out_by_hand()
    {
        let mut core = CoreArena::new();
        let argument = core.value_unit();
        let bound = core.value_variable(Zone::Intuitionistic, innermost());
        let body = core.computation_return(bound);
        let identity = core.computation_lambda(body);
        let redex = core.computation_application(identity, argument);

        // Written out independently of the machine: `return ⟨⟩`.
        let expected_value = core.value_unit();
        let expected = core.computation_return(expected_value);

        let (chain, environment) = nothing_unfolds();
        let scope = environment.root();
        let definitions = Definitions::new(&chain, &environment, scope);
        let mut domain = DomainArena::new();
        let evaluated = eval_computation(&core, &mut domain, definitions, ample(), redex)
            .expect("the redex fires");
        let read = readback_computation(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::Unfolding,
            ample(),
            evaluated,
        )
        .expect("and the result reads back");

        assert!(
            matches!(
                same_tree(
                    &core,
                    Term::Computation(read),
                    &core,
                    Term::Computation(expected)
                ),
                Trees::Same
            ),
            "applying the identity to the unit normalizes to returning the unit"
        );
        assert!(
            !matches!(
                same_tree(
                    &core,
                    Term::Computation(read),
                    &core,
                    Term::Computation(redex)
                ),
                Trees::Same
            ),
            "and the redex itself is not that term, so the case is about the contraction \
             rather than about a round trip that changed nothing"
        );
    }

    #[test]
    fn a_redex_under_a_binder_normalizes_to_the_term_written_out_by_hand()
    {
        let mut core = CoreArena::new();
        let outer_occurrence = core.value_variable(Zone::Intuitionistic, innermost());
        let inner_occurrence = core.value_variable(Zone::Intuitionistic, innermost());
        let inner_body = core.computation_return(inner_occurrence);
        let inner = core.computation_lambda(inner_body);
        let applied = core.computation_application(inner, outer_occurrence);
        let source = core.computation_lambda(applied);

        // Written out independently of the machine: `λ. return x₀`.
        let expected_occurrence = core.value_variable(Zone::Intuitionistic, innermost());
        let expected_body = core.computation_return(expected_occurrence);
        let expected = core.computation_lambda(expected_body);

        let (chain, environment) = nothing_unfolds();
        let scope = environment.root();
        let definitions = Definitions::new(&chain, &environment, scope);
        let mut domain = DomainArena::new();
        let evaluated = eval_computation(&core, &mut domain, definitions, ample(), source)
            .expect("a lambda is already a weak head");
        let read = readback_computation(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::Unfolding,
            ample(),
            evaluated,
        )
        .expect("and reading it back opens the binder and contracts under it");

        assert!(
            matches!(
                same_tree(
                    &core,
                    Term::Computation(read),
                    &core,
                    Term::Computation(expected)
                ),
                Trees::Same
            ),
            "the redex under the binder was contracted, and the binder came back as the \
             index that names it"
        );
        assert!(
            !matches!(
                same_tree(
                    &core,
                    Term::Computation(read),
                    &core,
                    Term::Computation(source)
                ),
                Trees::Same
            ),
            "which the source term is not, so evaluation reached under the binder"
        );
    }

    #[test]
    fn a_case_that_fires_normalizes_to_the_branch_it_took()
    {
        let mut core = CoreArena::new();
        let payload = core.value_unit();
        let scrutinee = core.value_injection(Side::Right, payload);
        let untaken = core.value_unit();
        let on_left = core.computation_return(untaken);
        let occurrence = core.value_variable(Zone::Intuitionistic, innermost());
        let on_right = core.computation_return(occurrence);
        let source = core.computation_case(scrutinee, on_left, on_right);

        // Written out independently of the machine: `return ⟨⟩`, which is the
        // right branch with the injected payload substituted for its binder.
        let expected_value = core.value_unit();
        let expected = core.computation_return(expected_value);

        let (chain, environment) = nothing_unfolds();
        let scope = environment.root();
        let definitions = Definitions::new(&chain, &environment, scope);
        let mut domain = DomainArena::new();
        let evaluated = eval_computation(&core, &mut domain, definitions, ample(), source)
            .expect("a case over an injection picks a branch");
        let read = readback_computation(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::Unfolding,
            ample(),
            evaluated,
        )
        .expect("and the branch's result reads back");

        assert!(
            matches!(
                same_tree(
                    &core,
                    Term::Computation(read),
                    &core,
                    Term::Computation(expected)
                ),
                Trees::Same
            ),
            "the right injection took the right branch and its binder saw the payload"
        );
        assert!(
            !matches!(
                same_tree(
                    &core,
                    Term::Computation(read),
                    &core,
                    Term::Computation(on_right)
                ),
                Trees::Same
            ),
            "and the branch as written is not the answer, because its binder is still \
             free there"
        );
    }

    #[test]
    fn a_stuck_elimination_normalizes_to_the_spine_written_out_by_hand()
    {
        let mut core = CoreArena::new();
        let position = ConstantIndex::from(3_usize);
        let opaque = core.value_constant(position);
        let untaken = core.value_unit();
        let on_left = core.computation_return(untaken);
        let occurrence = core.value_variable(Zone::Intuitionistic, innermost());
        let on_right = core.computation_return(occurrence);
        let source = core.computation_case(opaque, on_left, on_right);

        // Written out independently of the machine: the same case, with the
        // scrutinee stuck and both branches normalized under their own binder.
        let expected_scrutinee = core.value_constant(position);
        let expected_untaken = core.value_unit();
        let expected_left = core.computation_return(expected_untaken);
        let expected_occurrence = core.value_variable(Zone::Intuitionistic, innermost());
        let expected_right = core.computation_return(expected_occurrence);
        let expected = core.computation_case(expected_scrutinee, expected_left, expected_right);

        let (chain, environment) = nothing_unfolds();
        let scope = environment.root();
        let definitions = Definitions::new(&chain, &environment, scope);
        let mut domain = DomainArena::new();
        let evaluated = eval_computation(&core, &mut domain, definitions, ample(), source)
            .expect("a case over a rigid constant gets stuck");
        let read = readback_computation(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::ZeroUnfold,
            ample(),
            evaluated,
        )
        .expect("and the stuck spine reads back");

        assert!(
            matches!(
                same_tree(
                    &core,
                    Term::Computation(read),
                    &core,
                    Term::Computation(expected)
                ),
                Trees::Same
            ),
            "the stuck case came back with its scrutinee, both branches, and both binders \
             in their source positions"
        );
    }

    #[test]
    fn an_unreduced_term_reads_back_as_the_id_it_was_evaluated_from()
    {
        let mut core = CoreArena::new();
        let first = core.value_unit();
        let second = core.value_unit();
        let source = core.value_pair(first, second);

        let (chain, environment) = nothing_unfolds();
        let scope = environment.root();
        let definitions = Definitions::new(&chain, &environment, scope);
        let mut domain = DomainArena::new();
        let evaluated = eval_value(&core, &mut domain, definitions, ample(), source)
            .expect("a closed pair of units evaluates");

        let mark = core.watermark();
        let read = readback_value(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::ZeroUnfold,
            ample(),
            evaluated,
        )
        .expect("the retaining mode reads it back");
        assert_eq!(
            source, read,
            "nothing reduced, so the answer is the source id itself rather than an equal \
             term at a fresh id"
        );
        assert_eq!(
            mark,
            core.watermark(),
            "and no node was minted, which is the whole of reading back without rebuilding"
        );

        let rebuilt = readback_value(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::Unfolding,
            ample(),
            evaluated,
        )
        .expect("the rebuilding mode reads it back too");
        assert_ne!(
            source, rebuilt,
            "the other mode rebuilt instead, at a fresh id"
        );
        assert!(
            matches!(
                same_tree(&core, Term::Value(source), &core, Term::Value(rebuilt)),
                Trees::Same
            ),
            "and landed on the same term, so the two modes differ in what they mint and \
             not in what they mean"
        );
    }
    #[test]
    fn native_tree_comparison_preserves_endpoints_maps_and_evidence()
    {
        let mut cases = Vec::new();
        for padding in 0 .. 2_u8 {
            let mut core = CoreArena::new();
            for _ in 0 .. padding {
                let _ = core.value_unit();
            }
            let unit = core.value_type_unit();
            let integer = core.value_type_base(gandr_kernel_term::BaseType::Integer);
            let source = core.value_quote(unit);
            let target = core.value_quote(integer);
            let classifier = core.value_type_path_universe(source, target);
            let reversed = core.value_type_path_universe(target, source);
            let refl = core.value_path_refl(source);
            let other = core.value_path_refl(target);
            let product = core.value_path_product(refl, other);
            let swapped = core.value_path_product(other, refl);
            let bound = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
            let returned = core.computation_return(bound);
            let identity = core.computation_lambda(returned);
            let map = core.value_thunk(identity);
            let proof = alloc::sync::Arc::new(gandr_kernel_term::PathEvidence {
                source: Vec::from([Vec::new()]),
                target: Vec::from([Vec::new()]),
            });
            let equiv =
                core.value_path_equiv(classifier, map, map, alloc::sync::Arc::clone(&proof));
            let wrong_map = core.value_path_equiv(classifier, map, source, proof);
            let altered = alloc::sync::Arc::new(gandr_kernel_term::PathEvidence {
                source: Vec::new(),
                target: Vec::from([Vec::new()]),
            });
            let wrong_evidence = core.value_path_equiv(classifier, map, map, altered);
            let transport = core.computation_transport(product, source);
            let wrong_value = core.computation_transport(product, target);
            cases.push((
                core,
                [
                    Term::Value(refl),
                    Term::Value(product),
                    Term::Value(equiv),
                    Term::Computation(transport),
                    Term::ValueType(classifier),
                ],
                [
                    Term::Value(other),
                    Term::Value(swapped),
                    Term::Value(wrong_map),
                    Term::Computation(wrong_value),
                    Term::ValueType(reversed),
                ],
                Term::Value(wrong_evidence),
            ));
        }
        let (ref left, ref positive, ..) = cases[0];
        let (ref right, ref equal, ref negative, ref evidence) = cases[1];
        for ((&one, &same), &different) in positive.iter().zip(equal).zip(negative) {
            assert_eq!(Trees::Same, same_tree(left, one, right, same));
            assert_eq!(Trees::Different, same_tree(left, one, right, different));
        }
        assert_eq!(
            Trees::Different,
            same_tree(left, positive[2], right, *evidence)
        );
    }
}
