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

/// The pinned-term cases, in a `cfg(test)` module so the crate's lint wall
/// reads them as test code rather than as shipping code.
#[cfg(test)]
mod readback_terms
{
    use gandr_core_nbe::Definitions;
    use gandr_core_nbe::DomainArena;
    use gandr_core_nbe::Fuel;
    use gandr_core_nbe::LoweredChain;
    use gandr_core_nbe::ReadbackMode;
    use gandr_core_nbe::eval_computation;
    use gandr_core_nbe::eval_value;
    use gandr_core_nbe::readback_computation;
    use gandr_core_nbe::readback_value;
    use gandr_core_term::Computation;
    use gandr_core_term::ComputationId;
    use gandr_core_term::CoreArena;
    use gandr_core_term::DefinitionalEnvironment;
    use gandr_core_term::Value;
    use gandr_core_term::ValueId;
    use gandr_core_term::Zone;
    use gandr_kernel_strata::Level;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::IntegerLiteral;
    use gandr_kernel_term::Literal;
    use gandr_kernel_term::Magnitude;
    use gandr_kernel_term::Side;
    use gandr_kernel_term::Sign;

    /// Ample fuel for every case that is meant to finish.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a budget far above the step count any fixture below needs, so
    ///   an exhaustion refusal in one of them is a defect rather than a tight
    ///   budget.
    /// - provides: the budget every case here is run with.
    /// - panics: none.
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

    /// One pair of nodes still to be compared.
    ///
    /// The comparison is a worklist rather than a recursive walk for the same
    /// reason every other traversal in this workspace is: a term's depth is
    /// whatever built it, and a recursive comparator would overflow on exactly
    /// the deep terms the machine under test handles.
    #[derive(Clone, Copy, Debug)]
    enum Pending
    {
        /// Two value nodes.
        Values(ValueId, ValueId),
        /// Two computation nodes.
        Comps(ComputationId, ComputationId),
    }

    /// Whether a structural comparison found the two terms identical.
    #[repr(transparent)]
    struct TermsAgree(bool);

    /// Whether two core values denote the same term, node for node.
    ///
    /// The wildcard arm of each table is the "different former" cell and
    /// nothing else: two nodes built by different constructors are different
    /// terms, which is total over the tables rather than a gap in them.
    ///
    /// # Specification
    /// - requires: `core` holds every node `start` names; a dangling id reads
    ///   as disagreement rather than a panic.
    /// - ensures: agreement exactly when the two terms are identical node for
    ///   node — the same formers in the same positions with the same payloads —
    ///   over both spaces, with the worklist reaching every reachable pair.
    /// - provides: the term equality the round-trip witnesses assert, which is
    ///   structural rather than by id, so a rebuilt term counts as equal to the
    ///   one it was read from.
    /// - fails: never — disagreement is the negative answer, not a failure.
    /// - panics: none. The comparison is a worklist for the reason the
    ///   paragraph above states, so depth costs heap rather than stack.
    fn same_term(
        core: &CoreArena,
        start: Pending,
    ) -> TermsAgree
    {
        let mut work = Vec::from([start]);
        while let Some(item) = work.pop() {
            match item {
                | Pending::Values(left, right) => {
                    let (Some(left), Some(right)) = (core.value(left), core.value(right))
                    else {
                        return TermsAgree(false);
                    };
                    match (left, right) {
                        | (&Value::Unit, &Value::Unit) => {},
                        | (
                            &Value::Variable {
                                zone: left,
                                index: left_index,
                            },
                            &Value::Variable {
                                zone: right,
                                index: right_index,
                            },
                        ) => {
                            if left != right || left_index != right_index {
                                return TermsAgree(false);
                            }
                        },
                        | (&Value::Constant(left), &Value::Constant(right)) => {
                            if left != right {
                                return TermsAgree(false);
                            }
                        },
                        // A literal has no children, so the nodes' own derived
                        // equality is exactly the comparison this arm owes.
                        | (&Value::Literal(_), &Value::Literal(_)) => {
                            if left != right {
                                return TermsAgree(false);
                            }
                        },
                        | (&Value::Pair(left, left_second), &Value::Pair(right, right_second)) => {
                            work.push(Pending::Values(left, right));
                            work.push(Pending::Values(left_second, right_second));
                        },
                        | (
                            &Value::Injection(left, left_body),
                            &Value::Injection(right, right_body),
                        ) => {
                            if left != right {
                                return TermsAgree(false);
                            }
                            work.push(Pending::Values(left_body, right_body));
                        },
                        | (&Value::Thunk(left), &Value::Thunk(right)) => {
                            work.push(Pending::Comps(left, right));
                        },
                        | (
                            &Value::Lift {
                                target: ref left,
                                body: left_body,
                            },
                            &Value::Lift {
                                target: ref right,
                                body: right_body,
                            },
                        ) => {
                            if left != right {
                                return TermsAgree(false);
                            }
                            work.push(Pending::Values(left_body, right_body));
                        },
                        | _ => return TermsAgree(false),
                    }
                },
                | Pending::Comps(left, right) => {
                    let (Some(left), Some(right)) =
                        (core.computation(left), core.computation(right))
                    else {
                        return TermsAgree(false);
                    };
                    match (left, right) {
                        | (&Computation::Lambda(left), &Computation::Lambda(right)) => {
                            work.push(Pending::Comps(left, right));
                        },
                        | (&Computation::Return(left), &Computation::Return(right))
                        | (&Computation::Force(left), &Computation::Force(right)) => {
                            work.push(Pending::Values(left, right));
                        },
                        | (
                            &Computation::Application(left, left_argument),
                            &Computation::Application(right, right_argument),
                        ) => {
                            work.push(Pending::Comps(left, right));
                            work.push(Pending::Values(left_argument, right_argument));
                        },
                        | (
                            &Computation::Bind(left, left_body),
                            &Computation::Bind(right, right_body),
                        ) => {
                            work.push(Pending::Comps(left, right));
                            work.push(Pending::Comps(left_body, right_body));
                        },
                        | (
                            &Computation::Case {
                                scrutinee: left,
                                on_left: left_first,
                                on_right: left_second,
                            },
                            &Computation::Case {
                                scrutinee: right,
                                on_left: right_first,
                                on_right: right_second,
                            },
                        ) => {
                            work.push(Pending::Values(left, right));
                            work.push(Pending::Comps(left_first, right_first));
                            work.push(Pending::Comps(left_second, right_second));
                        },
                        | _ => return TermsAgree(false),
                    }
                },
            }
        }
        TermsAgree(true)
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
    fn nothing_unfolds() -> (LoweredChain, DefinitionalEnvironment)
    {
        (LoweredChain::new(), DefinitionalEnvironment::new())
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
            same_term(&core, Pending::Values(one, other)).0,
            "two pairs of units are the same term at different ids"
        );

        let occurrence = core.value_variable(Zone::Intuitionistic, innermost());
        let outer = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
        let linear = core.value_variable(Zone::Linear, innermost());
        assert!(
            !same_term(&core, Pending::Values(occurrence, outer)).0,
            "two indices are two different occurrences"
        );
        assert!(
            !same_term(&core, Pending::Values(occurrence, linear)).0,
            "and so are one index in two zones"
        );
        assert!(
            !same_term(&core, Pending::Values(occurrence, first)).0,
            "different formers are different terms"
        );

        let mixed = core.value_pair(first, occurrence);
        assert!(
            !same_term(&core, Pending::Values(one, mixed)).0,
            "a difference in a child is a difference in the term"
        );

        let left = core.value_injection(Side::Left, first);
        let right = core.value_injection(Side::Right, first);
        assert!(
            !same_term(&core, Pending::Values(left, right)).0,
            "and a difference in a payload the walk cannot recurse through is one too"
        );

        let returner = core.computation_return(first);
        let forced = core.computation_force(first);
        assert!(
            !same_term(&core, Pending::Comps(returner, forced)).0,
            "the negative table separates its formers the same way"
        );

        // Every remaining arm of both tables, each at a difference the walk
        // must notice. An arm that answered `true` unconditionally would be a
        // comparator that pins nothing, so each is charged once.
        let here = core.value_constant(ConstantIndex::from(1_usize));
        let there = core.value_constant(ConstantIndex::from(2_usize));
        assert!(
            same_term(&core, Pending::Values(here, here)).0,
            "one admission position is one reference"
        );
        assert!(
            !same_term(&core, Pending::Values(here, there)).0,
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
            same_term(&core, Pending::Values(zero, also_zero)).0,
            "equal literal payloads at different ids are one term"
        );
        assert!(
            !same_term(&core, Pending::Values(zero, seven)).0,
            "a difference in the magnitude is a difference in the term"
        );
        assert!(
            !same_term(&core, Pending::Values(seven, negative_seven)).0,
            "and so is a difference in the sign, which is the whole of the leaf arm — the \
             zero magnitude would witness neither, because the literal has no negative zero"
        );

        let one_level = Level::zero().succ().expect("level one exists");
        let two_level = one_level.succ().expect("level two exists");
        let lifted_low = core.value_lift(one_level.clone(), first);
        let lifted_low_again = core.value_lift(one_level, second);
        let lifted_high = core.value_lift(two_level, first);
        assert!(
            same_term(&core, Pending::Values(lifted_low, lifted_low_again)).0,
            "one target over equal bodies is one lift"
        );
        assert!(
            !same_term(&core, Pending::Values(lifted_low, lifted_high)).0,
            "and the target is compared, not carried past"
        );

        let suspend_returner = core.value_thunk(returner);
        let suspend_forced = core.value_thunk(forced);
        assert!(
            !same_term(&core, Pending::Values(suspend_returner, suspend_forced)).0,
            "a thunk is compared through the computation it suspends, which is the one \
             value arm that crosses polarity"
        );

        let abstraction = core.computation_lambda(returner);
        let other_abstraction = core.computation_lambda(forced);
        assert!(
            !same_term(&core, Pending::Comps(abstraction, other_abstraction)).0,
            "a lambda is compared through its body"
        );

        let applied = core.computation_application(returner, first);
        let applied_elsewhere = core.computation_application(returner, occurrence);
        let applied_to_other = core.computation_application(forced, first);
        assert!(
            !same_term(&core, Pending::Comps(applied, applied_elsewhere)).0,
            "an application is compared through its argument"
        );
        assert!(
            !same_term(&core, Pending::Comps(applied, applied_to_other)).0,
            "and through its head, so neither child is dropped"
        );

        let sequenced = core.computation_bind(returner, forced);
        let sequenced_other_way = core.computation_bind(forced, returner);
        assert!(
            !same_term(&core, Pending::Comps(sequenced, sequenced_other_way)).0,
            "a bind is compared in both positions, so a comparator that swapped them \
             would call these equal"
        );

        let cased = core.computation_case(first, returner, forced);
        let cased_other_scrutinee = core.computation_case(occurrence, returner, forced);
        let cased_swapped = core.computation_case(first, forced, returner);
        assert!(
            !same_term(&core, Pending::Comps(cased, cased_other_scrutinee)).0,
            "a case is compared through its scrutinee"
        );
        assert!(
            !same_term(&core, Pending::Comps(cased, cased_swapped)).0,
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
            !same_term(&core, Pending::Values(first, stranger)).0,
            "an unresolvable value id is not the same term as anything"
        );
        assert!(
            !same_term(&core, Pending::Comps(returner, stranger_comp)).0,
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
            same_term(&core, Pending::Comps(read, expected)).0,
            "applying the identity to the unit normalizes to returning the unit"
        );
        assert!(
            !same_term(&core, Pending::Comps(read, redex)).0,
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
            same_term(&core, Pending::Comps(read, expected)).0,
            "the redex under the binder was contracted, and the binder came back as the \
             index that names it"
        );
        assert!(
            !same_term(&core, Pending::Comps(read, source)).0,
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
            same_term(&core, Pending::Comps(read, expected)).0,
            "the right injection took the right branch and its binder saw the payload"
        );
        assert!(
            !same_term(&core, Pending::Comps(read, on_right)).0,
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
            same_term(&core, Pending::Comps(read, expected)).0,
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
            same_term(&core, Pending::Values(source, rebuilt)).0,
            "and landed on the same term, so the two modes differ in what they mint and \
             not in what they mean"
        );
    }
}
