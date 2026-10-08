extern crate alloc;
#[cfg(test)]
mod level_oracle
{
    //! Differential property tests for the level oracle over the public API.
    //!
    //! A free term over zero, variables, successor and binary maximum is
    //! generated as a **flat, id-addressed arena** — no owning-pointer
    //! recursion anywhere, and every fold over it is a single forward pass
    //! over the node vector rather than a traversal. The term is folded
    //! into a canonical `Level` through the smart constructors, and every
    //! oracle answer is cross-checked against an **independent semantic
    //! reference**: direct arena evaluation over a provably complete finite
    //! valuation family — the zero valuation plus, per variable, a
    //! spike one past the right term's successor count. A violation of atom
    //! domination shows at a spike, a violation of the constant bound at zero,
    //! and domination itself is pointwise. The reference never looks at
    //! canonical forms, offsets, or witnesses; it only evaluates, so it is
    //! external to everything the oracle computes.
    //!
    //! The suite also pins the algebraic laws — maximum commutative,
    //! associative and idempotent with zero as unit, successor distributing
    //! over maximum — the order laws of reflexivity, irreflexivity,
    //! antisymmetry against canonical equality and transitivity, the law
    //! that strict order is non-strict order after a successor, and
    //! evidence validation on every decided pair.
    //!
    //! Agreement failures are assertions, since agreement is the property under
    //! test. Failures of the harness itself return [`TermFailure`], so the
    //! property body decides how they surface and the helpers stay free of
    //! `expect`.

    use alloc::collections::BTreeMap;
    use alloc::collections::BTreeSet;

    use gandr_kernel_strata::Level;
    use gandr_kernel_strata::LevelError;
    use gandr_kernel_strata::LevelValue;
    use gandr_kernel_strata::LevelVar;
    use gandr_kernel_strata::LevelVarIndex;
    use gandr_kernel_strata::OrderComparison;
    use gandr_kernel_strata::Strictness;
    use gandr_kernel_strata::validate_refutation;
    use gandr_kernel_strata::validate_witness;
    use proptest::prelude::Just;
    use proptest::prelude::ProptestConfig;
    use proptest::prelude::Strategy;
    use proptest::prelude::any;
    use proptest::prop_assert_eq;
    use proptest::prop_oneof;
    use proptest::proptest;

    /// The number of distinct variables generated terms range over.
    const VARIABLE_COUNT: u32 = 4;

    /// The maximum node count of a generated term arena.
    const NODE_BUDGET: usize = 24;

    /// A node identifier inside a generated term arena.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct TermId(usize);

    /// A generated selector, reduced modulo the node count already built so it
    /// always names an earlier node.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct NodeSelector(u32);

    /// A count of successor nodes in a term's unfolding.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
    struct SuccCount(u128);

    /// One node of a generated free level term. Children name strictly earlier
    /// nodes, so the arena is a flat id-addressed acyclic structure and every
    /// fold over it is one forward pass.
    #[derive(Clone, Copy, Debug)]
    enum TermNode
    {
        /// The level `0`.
        Zero,
        /// A level variable.
        Var(LevelVarIndex),
        /// The successor of an earlier node.
        Succ(TermId),
        /// The join of two earlier nodes.
        Max(TermId, TermId),
    }

    /// An unresolved generated node shape, before selectors are reduced into
    /// node identifiers.
    #[derive(Clone, Copy, Debug)]
    enum TermShape
    {
        /// The level `0`.
        Zero,
        /// A level variable.
        Var(LevelVarIndex),
        /// The successor of the selected node.
        Succ(NodeSelector),
        /// The join of the two selected nodes.
        Max(NodeSelector, NodeSelector),
    }

    /// A generated free term: a flat arena in topological order, rooted at its
    /// last node.
    #[repr(transparent)]
    #[derive(Clone, Debug)]
    struct Term
    {
        /// The nodes, each referring only to earlier ones.
        nodes: Vec<TermNode>,
    }

    /// A failure of the test harness itself, as distinct from a disagreement
    /// between the oracle and the reference.
    ///
    /// None of these should be reachable from the generator, so each one
    /// surfacing is itself a finding rather than a panic buried in a
    /// helper.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum TermFailure
    {
        /// The arena was empty, so it has no root.
        NoRoot,
        /// A node named a child the fold had not yet computed, which the
        /// topological build order excludes.
        DanglingChild,
        /// Reference arithmetic left the representable range.
        ReferenceOverflow,
        /// A level constructor refused.
        Level(LevelError),
    }

    impl From<LevelError> for TermFailure
    {
        /// Wraps a level failure as a harness failure.
        ///
        /// # Specification
        /// trivial.
        fn from(error: LevelError) -> Self
        {
            Self::Level(error)
        }
    }

    /// Reduces a generated selector into `[0, built)`.
    ///
    /// # Specification
    /// - requires: nothing; the selector is an arbitrary generated word.
    /// - ensures: `Some(id)` naming a node strictly below `built` whenever
    ///   `built` is nonzero and fits the selector's width, `None` otherwise.
    /// - provides: the reduction that keeps a generated child pointing at an
    ///   earlier node, so an arena is acyclic by construction.
    /// - panics: none.
    fn pick(
        selector: NodeSelector,
        built: TermId,
    ) -> Option<TermId>
    {
        let modulus = u32::try_from(built.0).ok()?;
        let index = selector.0.checked_rem(modulus)?;
        usize::try_from(index).ok().map(TermId)
    }

    /// Builds an arena from generated shapes, resolving each selector against
    /// the nodes already built.
    ///
    /// # Specification
    /// - requires: nothing; any shape sequence is admissible.
    /// - ensures: returns an arena with one node per shape, in the same order,
    ///   whose children name strictly earlier nodes; a selector with no earlier
    ///   node to name degrades to the zero node.
    /// - provides: the acyclic arena every fold below reads.
    /// - panics: none.
    fn build(shapes: &[TermShape]) -> Term
    {
        let mut nodes: Vec<TermNode> = Vec::with_capacity(shapes.len());
        for shape in shapes {
            let built = TermId(nodes.len());
            let node = match *shape {
                | TermShape::Zero => TermNode::Zero,
                | TermShape::Var(index) => TermNode::Var(index),
                | TermShape::Succ(selector) => {
                    pick(selector, built).map_or(TermNode::Zero, TermNode::Succ)
                },
                | TermShape::Max(left, right) => match (pick(left, built), pick(right, built)) {
                    | (Some(left), Some(right)) => TermNode::Max(left, right),
                    | _ => TermNode::Zero,
                },
            };
            nodes.push(node);
        }
        Term { nodes }
    }

    /// A generator for one node shape.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: generates the zero shape, a variable below the fixed variable
    ///   count, a successor selector, and a join of two selectors.
    /// - provides: the node-shape generator the term strategy repeats.
    /// - panics: none.
    fn shape_strategy() -> impl Strategy<Value = TermShape>
    {
        prop_oneof![
            Just(TermShape::Zero),
            (0_u32 .. VARIABLE_COUNT).prop_map(|index| TermShape::Var(LevelVarIndex::from(index))),
            any::<u32>().prop_map(|raw| TermShape::Succ(NodeSelector(raw))),
            (any::<u32>(), any::<u32>())
                .prop_map(|(left, right)| TermShape::Max(NodeSelector(left), NodeSelector(right))),
        ]
    }

    /// A generator for a whole term arena.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: generates arenas of between one shape and the node budget,
    ///   each already resolved into an arena.
    /// - provides: the term generator every property row draws from.
    /// - panics: none.
    fn term_strategy() -> impl Strategy<Value = Term>
    {
        proptest::collection::vec(shape_strategy(), 1 ..= NODE_BUDGET)
            .prop_map(|shapes| build(&shapes))
    }

    /// Folds a per-node accumulator over the arena in build order and returns
    /// the root's value.
    ///
    /// The step gets the node and the accumulators of every earlier node, which
    /// is what makes this a forward pass rather than a traversal.
    ///
    /// # Specification
    /// - requires: `term`'s nodes name only strictly earlier nodes, which the
    ///   arena builder guarantees, and `step` is total on those nodes.
    /// - ensures: returns the root node's accumulator, having applied `step` to
    ///   every node in build order with the earlier accumulators in hand.
    /// - provides: the one forward pass all four folds below are written as.
    /// - fails: `TermFailure::NoRoot` on an empty arena, and whatever `step`
    ///   returns.
    /// - panics: none.
    fn fold_root<Value, Step>(
        term: &Term,
        mut step: Step,
    ) -> Result<Value, TermFailure>
    where
        Value: Clone,
        Step: FnMut(TermNode, &[Value]) -> Result<Value, TermFailure>,
    {
        let mut values: Vec<Value> = Vec::with_capacity(term.nodes.len());
        for &node in &term.nodes {
            let value = step(node, &values)?;
            values.push(value);
        }
        values.last().cloned().ok_or(TermFailure::NoRoot)
    }
    /// Reads an earlier node's accumulator.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the accumulator already computed at `id`.
    /// - provides: the arena read each fold step makes for a child.
    /// - fails: `TermFailure::DanglingChild` when the fold has not reached
    ///   `id`, which the topological build order excludes.
    /// - panics: none.
    fn child<Value>(
        values: &[Value],
        id: TermId,
    ) -> Result<Value, TermFailure>
    where
        Value: Clone,
    {
        values.get(id.0).cloned().ok_or(TermFailure::DanglingChild)
    }

    /// Evaluates a term directly under a valuation, reading absent variables as
    /// zero.
    ///
    /// This is the semantic reference: it never consults canonical forms.
    ///
    /// # Specification
    /// - requires: nothing; any valuation is admissible.
    /// - ensures: returns the term's value under `valuation`, computed from the
    ///   unfolding alone, with an absent variable read as zero.
    /// - provides: the external oracle every agreement row compares against —
    ///   it shares no machinery with the canonical form.
    /// - fails: `TermFailure::ReferenceOverflow` when a successor leaves the
    ///   representable range, plus whatever the fold surfaces.
    /// - panics: none.
    fn eval(
        term: &Term,
        valuation: &BTreeMap<LevelVarIndex, LevelValue>,
    ) -> Result<LevelValue, TermFailure>
    {
        let value = fold_root(term, |node, values| match node {
            | TermNode::Zero => Ok(0_u128),
            | TermNode::Var(index) => Ok(valuation.get(&index).copied().map_or(0_u128, u128::from)),
            | TermNode::Succ(inner) => {
                let inner = child(values, inner)?;
                inner
                    .checked_add(1_u128)
                    .ok_or(TermFailure::ReferenceOverflow)
            },
            | TermNode::Max(left, right) => {
                let left = child(values, left)?;
                let right = child(values, right)?;
                Ok(left.max(right))
            },
        })?;
        Ok(LevelValue::from(value))
    }

    /// Folds a term into a canonical level through the smart constructors,
    /// which is the system under test.
    ///
    /// # Specification
    /// - requires: `term`'s nodes name only strictly earlier nodes.
    /// - ensures: returns the canonical level the root node denotes, folded
    ///   through the smart constructors.
    /// - provides: the system under test on the generated side of every row.
    /// - fails: `TermFailure::Level` where a successor passes the representable
    ///   range, plus whatever the fold surfaces.
    /// - panics: none.
    fn to_level(term: &Term) -> Result<Level, TermFailure>
    {
        fold_root(term, |node, values| match node {
            | TermNode::Zero => Ok(Level::zero()),
            | TermNode::Var(index) => Ok(Level::var(LevelVar::new(index))),
            | TermNode::Succ(inner) => {
                let inner = child(values, inner)?;
                let bumped = inner.succ()?;
                Ok(bumped)
            },
            | TermNode::Max(left, right) => {
                let left = child(values, left)?;
                let right = child(values, right)?;
                Ok(left.max(&right))
            },
        })
    }

    /// Counts the successor nodes of a term's unfolding — a syntactic upper
    /// bound on every constant and offset of its canonical form.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the number of successor nodes in the term's
    ///   unfolding, which bounds every constant and offset of its canonical
    ///   form from above.
    /// - provides: the syntactic ceiling the spike valuations are built one
    ///   past.
    /// - fails: `TermFailure::ReferenceOverflow` when the count leaves the
    ///   representable range, plus whatever the fold surfaces.
    /// - panics: none.
    fn succ_count(term: &Term) -> Result<SuccCount, TermFailure>
    {
        let count = fold_root(term, |node, values| match node {
            | TermNode::Zero | TermNode::Var(_) => Ok(0_u128),
            | TermNode::Succ(inner) => {
                let inner = child(values, inner)?;
                inner
                    .checked_add(1_u128)
                    .ok_or(TermFailure::ReferenceOverflow)
            },
            | TermNode::Max(left, right) => {
                let left = child(values, left)?;
                let right = child(values, right)?;
                left.checked_add(right)
                    .ok_or(TermFailure::ReferenceOverflow)
            },
        })?;
        Ok(SuccCount(count))
    }

    /// The variable indices a term's arena mentions.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns each variable index the arena mentions, once, in
    ///   ascending order.
    /// - provides: the variable set the valuation family spikes one at a time.
    /// - panics: none.
    fn variables(term: &Term) -> BTreeSet<LevelVarIndex>
    {
        let mut found = BTreeSet::new();
        for &node in &term.nodes {
            if let TermNode::Var(index) = node {
                let _fresh = found.insert(index);
            }
        }
        found
    }

    /// The complete valuation family for deciding `left + shift ≤ right`: the
    /// zero valuation plus, for each variable of either side, a spike one
    /// past `right`'s successor count.
    ///
    /// Domination failures on an atom show at that variable's spike;
    /// constant-bound failures show at zero; and when domination holds the
    /// order holds pointwise everywhere.
    ///
    /// # Specification
    /// - requires: nothing; any two terms are admissible.
    /// - ensures: returns the zero valuation followed by one valuation per
    ///   variable either side mentions, that variable spiked one past the right
    ///   term's successor count and every other variable read as zero.
    /// - provides: a family complete for the order question — a domination
    ///   failure on an atom shows at that variable's spike, a constant-bound
    ///   failure shows at zero, and where domination holds the order holds
    ///   pointwise everywhere.
    /// - fails: `TermFailure::ReferenceOverflow` when the spike leaves the
    ///   representable range, plus whatever the successor count surfaces.
    /// - panics: none.
    fn valuation_family(
        left: &Term,
        right: &Term,
    ) -> Result<Vec<BTreeMap<LevelVarIndex, LevelValue>>, TermFailure>
    {
        let mut names = variables(left);
        names.extend(variables(right));
        let count = succ_count(right)?;
        let spike = count
            .0
            .checked_add(1_u128)
            .ok_or(TermFailure::ReferenceOverflow)?;
        let mut family = vec![BTreeMap::new()];
        for index in names {
            let mut valuation = BTreeMap::new();
            let _fresh = valuation.insert(index, LevelValue::from(spike));
            family.push(valuation);
        }
        Ok(family)
    }

    /// The semantic reference decision: `left + shift ≤ right` at every member
    /// of the complete valuation family.
    ///
    /// # Specification
    /// - requires: nothing; any two terms are admissible.
    /// - ensures: answers affirmatively exactly when the left term, shifted by
    ///   the mode, is at most the right term at every member of the complete
    ///   valuation family.
    /// - provides: the reference decision, computed from the unfolding rather
    ///   than from any canonical form.
    /// - fails: `TermFailure::ReferenceOverflow` when the shifted value leaves
    ///   the representable range, plus whatever evaluation surfaces.
    /// - panics: none.
    fn semantic_leq(
        left: &Term,
        right: &Term,
        strict: Strictness,
    ) -> Result<OrderComparison, TermFailure>
    {
        let shift = u128::from(bool::from(strict));
        let family = valuation_family(left, right)?;
        let mut holds = true;
        for valuation in &family {
            let left_evaluated = eval(left, valuation)?;
            let right_evaluated = eval(right, valuation)?;
            let left_value = u128::from(left_evaluated);
            let right_value = u128::from(right_evaluated);
            let shifted = left_value
                .checked_add(shift)
                .ok_or(TermFailure::ReferenceOverflow)?;
            if shifted > right_value {
                holds = false;
            }
        }
        Ok(OrderComparison::from(holds))
    }

    /// Checks the oracle's order against the semantic reference in one mode.
    ///
    /// # Specification
    /// - requires: nothing; any two generated terms are admissible.
    /// - ensures: returns successfully exactly when the oracle's verdict in the
    ///   given mode equals the semantic reference's.
    /// - provides: the differential row the order oracle's L2 evidence rests
    ///   on.
    /// - fails: as the fold and the reference do.
    /// - panics: on a disagreement, which is how the property reports.
    fn check_order_agreement(
        left: &Term,
        right: &Term,
        strict: Strictness,
    ) -> Result<(), TermFailure>
    {
        let left_level = to_level(left)?;
        let right_level = to_level(right)?;
        let oracle = if bool::from(strict) {
            left_level.lt(&right_level)
        }
        else {
            left_level.leq(&right_level)
        };
        let reference = semantic_leq(left, right, strict)?;
        assert_eq!(
            oracle, reference,
            "the oracle must agree with the semantic reference"
        );
        Ok(())
    }

    /// Checks that canonical equality agrees with two-sided semantic order.
    ///
    /// # Specification
    /// - requires: nothing; any two generated terms are admissible.
    /// - ensures: returns successfully exactly when canonical-form identity
    ///   holds precisely where the semantic order holds in both directions.
    /// - provides: the row that earns derived `Eq` its standing as the
    ///   level-equality oracle.
    /// - fails: as the fold and the reference do.
    /// - panics: on a disagreement.
    fn check_equality_agreement(
        left: &Term,
        right: &Term,
    ) -> Result<(), TermFailure>
    {
        let left_level = to_level(left)?;
        let right_level = to_level(right)?;
        let oracle = left_level == right_level;
        let forward = semantic_leq(left, right, Strictness::NON_STRICT)?;
        let backward = semantic_leq(right, left, Strictness::NON_STRICT)?;
        assert_eq!(
            oracle,
            bool::from(forward) && bool::from(backward),
            "canonical equality is two-sided semantic order"
        );
        Ok(())
    }

    /// Checks that every piece of returned evidence validates, in both modes.
    ///
    /// # Specification
    /// - requires: nothing; any two generated terms are admissible.
    /// - ensures: returns successfully exactly when the evidence the oracle
    ///   returns for the two terms records the queried mode and validates, in
    ///   both modes.
    /// - provides: the self-incrimination row: the decision procedure is
    ///   checked against the validators on every generated input.
    /// - fails: as the fold does.
    /// - panics: on evidence that records the wrong mode or fails validation.
    fn check_evidence_validates(
        left: &Term,
        right: &Term,
    ) -> Result<(), TermFailure>
    {
        let left_level = to_level(left)?;
        let right_level = to_level(right)?;
        for strict in [Strictness::NON_STRICT, Strictness::STRICT] {
            let decision = if bool::from(strict) {
                left_level.lt_with_evidence(&right_level)
            }
            else {
                left_level.leq_with_evidence(&right_level)
            };
            match decision {
                | Ok(witness) => {
                    assert_eq!(witness.strict(), strict, "the witness records its mode");
                    assert_eq!(
                        validate_witness(&left_level, &right_level, &witness),
                        Ok(()),
                        "every oracle witness must validate"
                    );
                },
                | Err(refutation) => {
                    assert_eq!(
                        refutation.strict(),
                        strict,
                        "the refutation records its mode"
                    );
                    assert_eq!(
                        validate_refutation(&left_level, &right_level, &refutation),
                        Ok(()),
                        "every oracle refutation must validate"
                    );
                },
            }
        }
        Ok(())
    }

    /// Checks that strict order is non-strict order after a successor.
    ///
    /// # Specification
    /// - requires: nothing; any two generated terms are admissible.
    /// - ensures: returns successfully exactly when the strict order on the two
    ///   terms agrees with the non-strict order on the left successor.
    /// - provides: the row pinning that the two modes differ by exactly the
    ///   shift.
    /// - fails: as the fold and the successor do.
    /// - panics: on a disagreement.
    fn check_lt_equals_succ_leq(
        left: &Term,
        right: &Term,
    ) -> Result<(), TermFailure>
    {
        let left_level = to_level(left)?;
        let right_level = to_level(right)?;
        let shifted = left_level.succ()?;
        assert_eq!(
            left_level.lt(&right_level),
            shifted.leq(&right_level),
            "strict order is non-strict order after a successor"
        );
        Ok(())
    }

    /// Checks the join laws as canonical-form identities.
    ///
    /// # Specification
    /// - requires: nothing; any three generated terms are admissible.
    /// - ensures: returns successfully exactly when the join on the three terms
    ///   is commutative, associative, idempotent, and has zero as its unit — as
    ///   canonical-form identities, not merely as semantic agreements.
    /// - provides: the algebraic row one call's postcondition cannot state.
    /// - fails: as the fold does.
    /// - panics: on a law the join breaks.
    fn check_max_laws(
        first: &Term,
        second: &Term,
        third: &Term,
    ) -> Result<(), TermFailure>
    {
        let first = to_level(first)?;
        let second = to_level(second)?;
        let third = to_level(third)?;
        assert_eq!(
            first.max(&second),
            second.max(&first),
            "the join is commutative"
        );
        assert_eq!(
            first.max(&second).max(&third),
            first.max(&second.max(&third)),
            "the join is associative"
        );
        assert_eq!(first.max(&Level::zero()), first, "zero is the join's unit");
        assert_eq!(first.max(&first), first, "the join is idempotent");
        Ok(())
    }

    /// Checks that the successor distributes over the join.
    ///
    /// # Specification
    /// - requires: nothing; any two generated terms are admissible.
    /// - ensures: returns successfully exactly when the successor of a join
    ///   equals the join of the successors, as canonical forms.
    /// - provides: the row pinning the interaction of the algebra's two
    ///   generators.
    /// - fails: as the fold and the successor do.
    /// - panics: on a disagreement.
    fn check_succ_distributes(
        first: &Term,
        second: &Term,
    ) -> Result<(), TermFailure>
    {
        let first = to_level(first)?;
        let second = to_level(second)?;
        let joined_then_succ = first.max(&second).succ()?;
        let first_succ = first.succ()?;
        let second_succ = second.succ()?;
        assert_eq!(
            joined_then_succ,
            first_succ.max(&second_succ),
            "the successor distributes over the join"
        );
        Ok(())
    }

    /// Checks reflexivity, irreflexivity, antisymmetry, and the upper-bound
    /// law.
    ///
    /// # Specification
    /// - requires: nothing; any two generated terms are admissible.
    /// - ensures: returns successfully exactly when the order on the two terms
    ///   is reflexive, strictly irreflexive, antisymmetric onto canonical
    ///   equality, and bounds each component of their join.
    /// - provides: the row pinning the order's shape rather than a single
    ///   verdict.
    /// - fails: as the fold does.
    /// - panics: on a law the order breaks.
    fn check_order_laws(
        first: &Term,
        second: &Term,
    ) -> Result<(), TermFailure>
    {
        let first = to_level(first)?;
        let second = to_level(second)?;
        assert!(
            bool::from(first.leq(&first)),
            "non-strict order is reflexive"
        );
        assert!(!bool::from(first.lt(&first)), "strict order is irreflexive");
        assert_eq!(
            bool::from(first.leq(&second)) && bool::from(second.leq(&first)),
            first == second,
            "antisymmetry lands on canonical equality"
        );
        assert!(
            bool::from(first.leq(&first.max(&second))),
            "the join bounds its left component"
        );
        assert!(
            bool::from(second.leq(&first.max(&second))),
            "the join bounds its right component"
        );
        Ok(())
    }

    /// Checks transitivity of the oracle's non-strict order.
    ///
    /// # Specification
    /// - requires: nothing; any three generated terms are admissible.
    /// - ensures: returns successfully exactly when the non-strict order
    ///   composes across the three terms wherever both steps hold.
    /// - provides: the transitivity row, kept apart from the other laws so a
    ///   failure names itself.
    /// - fails: as the fold does.
    /// - panics: on a composition the order loses.
    fn check_transitivity(
        first: &Term,
        second: &Term,
        third: &Term,
    ) -> Result<(), TermFailure>
    {
        let first = to_level(first)?;
        let second = to_level(second)?;
        let third = to_level(third)?;
        if bool::from(first.leq(&second)) && bool::from(second.leq(&third)) {
            assert!(bool::from(first.leq(&third)), "the order is transitive");
        }
        Ok(())
    }

    /// Checks the in-crate evaluator against the reference evaluator.
    ///
    /// # Specification
    /// - requires: nothing; `values` assigns the variables by position, and a
    ///   position past the index width reads as variable zero.
    /// - ensures: returns successfully exactly when the crate's evaluator on
    ///   the canonical form agrees with the reference evaluator on the
    ///   unfolding, under the same valuation.
    /// - provides: the row that anchors canonical form to denotation, which
    ///   every other order row rests on.
    /// - fails: as the fold and both evaluators do.
    /// - panics: on a disagreement.
    fn check_eval_agreement(
        term: &Term,
        values: &[LevelValue],
    ) -> Result<(), TermFailure>
    {
        let mut reference_valuation = BTreeMap::new();
        let mut level_valuation = BTreeMap::new();
        for (position, &value) in values.iter().enumerate() {
            let index = LevelVarIndex::from(u32::try_from(position).unwrap_or(0_u32));
            let _fresh = reference_valuation.insert(index, value);
            let _also = level_valuation.insert(LevelVar::new(index), value);
        }
        let reference = eval(term, &reference_valuation)?;
        let level = to_level(term)?;
        let oracle = level.eval(&level_valuation)?;
        assert_eq!(
            oracle, reference,
            "the in-crate evaluator agrees with the reference"
        );
        Ok(())
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(256))]

        /// The oracle's non-strict order agrees with the semantic reference.
        #[test]
        fn prop_leq_agrees_with_semantic_reference(
            (left, right) in (term_strategy(), term_strategy())
        ) {
            prop_assert_eq!(
                check_order_agreement(&left, &right, Strictness::NON_STRICT),
                Ok(())
            );
        }

        /// The oracle's strict order agrees with the semantic reference.
        #[test]
        fn prop_lt_agrees_with_semantic_reference(
            (left, right) in (term_strategy(), term_strategy())
        ) {
            prop_assert_eq!(
                check_order_agreement(&left, &right, Strictness::STRICT),
                Ok(())
            );
        }

        /// Canonical equality agrees with two-sided semantic order, so the
        /// canonical form is a complete invariant.
        #[test]
        fn prop_eq_agrees_with_semantic_reference(
            (left, right) in (term_strategy(), term_strategy())
        ) {
            prop_assert_eq!(check_equality_agreement(&left, &right), Ok(()));
        }

        /// Every piece of evidence the oracle returns validates against its levels,
        /// in both strictness modes.
        #[test]
        fn prop_evidence_validates((left, right) in (term_strategy(), term_strategy())) {
            prop_assert_eq!(check_evidence_validates(&left, &right), Ok(()));
        }

        /// The strict order is exactly the non-strict order after a successor on
        /// the left.
        #[test]
        fn prop_lt_equals_succ_leq((left, right) in (term_strategy(), term_strategy())) {
            prop_assert_eq!(check_lt_equals_succ_leq(&left, &right), Ok(()));
        }

        /// Maximum is commutative, associative, idempotent, and has zero as unit,
        /// as canonical-form identities.
        #[test]
        fn prop_max_laws(
            (first, second, third) in (term_strategy(), term_strategy(), term_strategy())
        ) {
            prop_assert_eq!(check_max_laws(&first, &second, &third), Ok(()));
        }

        /// The successor distributes over maximum.
        #[test]
        fn prop_succ_distributes_over_max(
            (first, second) in (term_strategy(), term_strategy())
        ) {
            prop_assert_eq!(check_succ_distributes(&first, &second), Ok(()));
        }

        /// Order laws: reflexivity of non-strict order, irreflexivity of strict
        /// order, antisymmetry against canonical equality, and the join as an upper
        /// bound.
        #[test]
        fn prop_order_laws((first, second) in (term_strategy(), term_strategy())) {
            prop_assert_eq!(check_order_laws(&first, &second), Ok(()));
        }

        /// Transitivity of the oracle's order on generated triples.
        #[test]
        fn prop_leq_is_transitive(
            (first, second, third) in (term_strategy(), term_strategy(), term_strategy())
        ) {
            prop_assert_eq!(check_transitivity(&first, &second, &third), Ok(()));
        }

        /// The in-crate evaluator agrees with the reference evaluator under random
        /// small valuations, so the semantic anchor is itself anchored.
        #[test]
        fn prop_eval_agrees_with_reference(
            term in term_strategy(),
            values in proptest::collection::vec(0_u128..10_u128, 4)
        ) {
            let values: Vec<LevelValue> = values.into_iter().map(LevelValue::from).collect();
            prop_assert_eq!(check_eval_agreement(&term, &values), Ok(()));
        }
    }
}
