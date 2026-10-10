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

    use anodized::spec;
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
    ///
    /// # Specification
    /// - requires: child identifiers precede the node's position in its arena.
    /// - executable: none — this node does not hold its enclosing arena or
    ///   position, which the builder and forward fold use to check topology.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — absent predecessors become zero and wrapped selectors
    ///   refer backward; successor and shared-join evaluation observe those
    ///   edges, exposing malformed references or lost sharing.
    /// - witness: `level_oracle::level_oracle::selector_and_topological_builder_boundaries`
    /// - witness: `level_oracle::level_oracle::reference_arithmetic_and_absence_boundaries`
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
    ///
    /// # Specification
    /// - ensures: builder-produced children name strictly earlier nodes; the
    ///   final node is the root, and an empty arena has no root.
    /// - executable: none — data-item predicates are not checked at
    ///   construction; builder and fold predicates check the topology.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — first-node selectors fall back to zero, later
    ///   selectors wrap backward, and empty folds refuse with `NoRoot`. Exact
    ///   evaluated values and deterministic generator checks expose a dangling
    ///   edge or wrong root.
    /// - witness: `level_oracle::level_oracle::selector_and_topological_builder_boundaries`
    /// - witness: `level_oracle::level_oracle::reference_arithmetic_and_absence_boundaries`
    /// - witness: `level_oracle::level_oracle::generator_support_stays_within_its_domain`
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty and singleton prefixes, a two-node prefix and a
    ///   prefix beyond the selector width distinguish missing modulo, a bad
    ///   zero guard and narrowing overflow by exact optional child indices.
    /// - witness: `level_oracle::level_oracle::selector_and_topological_builder_boundaries`
    #[spec(ensures: |ret| ret.map(|id| id.0) == u32::try_from(built.0).ok()
        .and_then(|modulus| selector.0.checked_rem(modulus)).and_then(|index| usize::try_from(index).ok()))]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a first-node successor or join becomes zero, and
    ///   later selectors wrap to earlier nodes. Exact evaluation of the
    ///   resulting term distinguishes a forward edge, wrong fallback or changed
    ///   selector reduction.
    /// - witness: `level_oracle::level_oracle::selector_and_topological_builder_boundaries`
    #[spec(ensures: |ret| ret.nodes.len() == shapes.len() && ret.nodes.iter().enumerate().all(|(at, node)| match *node {
        TermNode::Zero | TermNode::Var(_) => true,
        TermNode::Succ(child) => child.0 < at,
        TermNode::Max(left, right) => left.0 < at && right.0 < at,
    }))]
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
    /// - executable: none — the opaque strategy describes a support over future
    ///   draws; evaluating one output cannot check that whole support.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — deterministic draws cover all four shape constructors
    ///   and variable bounds; generated-term differential laws then observe the
    ///   resolved semantics. Missing constructor alternatives or escaping the
    ///   domain change the sampled support or fail a generated-input
    ///   precondition.
    /// - witness: `level_oracle::level_oracle::generator_support_stays_within_its_domain`
    /// - witness: `level_oracle::level_oracle::prop_eval_agrees_with_reference`
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
    /// - executable: none — the opaque strategy's support is a property of
    ///   future draws, not a value returned by this call.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — deterministic draws assert nonempty arenas at or
    ///   below the node budget and topological child references. L2 — generated
    ///   semantic agreement then observes those terms, detecting malformed or
    ///   out-of-domain arenas rather than accepting a silently weakened
    ///   generator.
    /// - witness: `level_oracle::level_oracle::generator_support_stays_within_its_domain`
    /// - witness: `level_oracle::level_oracle::prop_eval_agrees_with_reference`
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty arenas, zero, variables, successors and shared
    ///   joins are evaluated against exact arithmetic. No-root refusal and
    ///   shared child reuse distinguish missing traversal steps and an
    ///   incorrect root.
    /// - witness: `level_oracle::level_oracle::reference_arithmetic_and_absence_boundaries`
    #[spec(requires: term.nodes.iter().enumerate().all(|(at, node)| match *node {
        TermNode::Zero | TermNode::Var(_) => true,
        TermNode::Succ(child) => child.0 < at,
        TermNode::Max(left, right) => left.0 < at && right.0 < at,
    }),
        ensures: |ret| !term.nodes.is_empty() || matches!(ret, Err(TermFailure::NoRoot)))]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an empty accumulator list, first and last existing
    ///   positions and one past the end distinguish off-by-one indexing and a
    ///   defaulted missing child by exact values and the dangling-child
    ///   variant.
    /// - witness: `level_oracle::level_oracle::reference_arithmetic_and_absence_boundaries`
    #[spec(ensures: |ret| ret.is_ok() == (id.0 < values.len()))]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — absent and supplied variables, zero, successor and
    ///   shared maximum are evaluated exactly; a successor at the u128 ceiling
    ///   must return `ReferenceOverflow`. These boundaries expose defaulting,
    ///   wrong join arithmetic, missing increments and wraparound.
    /// - witness: `level_oracle::level_oracle::reference_arithmetic_and_absence_boundaries`
    #[spec(requires: term.nodes.iter().enumerate().all(|(at, node)| match *node {
        TermNode::Zero | TermNode::Var(_) => true,
        TermNode::Succ(child) => child.0 < at,
        TermNode::Max(left, right) => left.0 < at && right.0 < at,
    }), ensures: |ret| match term.nodes.last() {
        None => matches!(ret, Err(TermFailure::NoRoot)),
        Some(&TermNode::Zero) => ret == Ok(LevelValue::ZERO),
        Some(&TermNode::Var(index)) => ret == Ok(valuation.get(&index).copied().unwrap_or(LevelValue::ZERO)),
        Some(&TermNode::Succ(_) | &TermNode::Max(_, _)) => true,
    })]
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
    ///
    /// # Adequacy
    /// - hypothesis: L2 — generated terms agree with direct evaluation, and
    ///   canonical equality agrees with two-sided semantic order. L3 — zero and
    ///   a shared successor join under absent and supplied valuations
    ///   distinguish incorrect constructor selection and lost child reuse.
    /// - witness: `level_oracle::level_oracle::prop_eval_agrees_with_reference`
    /// - witness: `level_oracle::level_oracle::prop_eq_agrees_with_semantic_reference`
    /// - witness: `level_oracle::level_oracle::reference_arithmetic_and_absence_boundaries`
    #[spec(requires: term.nodes.iter().enumerate().all(|(at, node)| match *node {
        TermNode::Zero | TermNode::Var(_) => true,
        TermNode::Succ(child) => child.0 < at,
        TermNode::Max(left, right) => left.0 < at && right.0 < at,
    }))]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a shared successor counted twice in an unfolding has
    ///   count two although its value is one; repeated doubling crosses the
    ///   u128 ceiling. Exact counts and overflow distinguish arena-node
    ///   counting from unfolding multiplicity and unchecked arithmetic.
    /// - witness: `level_oracle::level_oracle::unfolding_count_and_spike_boundaries`
    #[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|count|
        eval(term, &BTreeMap::new()).is_ok_and(|value| u128::from(value) <= count.0)))]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — repeated variables in reverse appearance order yield
    ///   one ascending entry each; the zero term yields none. The exact spike
    ///   family observes omission, duplication and altered variable identities.
    /// - witness: `level_oracle::level_oracle::unfolding_count_and_spike_boundaries`
    #[spec(ensures: |ret| term.nodes.iter().all(|node| match *node {
        TermNode::Var(index) => ret.contains(&index),
        TermNode::Zero | TermNode::Succ(_) | TermNode::Max(_, _) => true,
    }) && ret.iter().all(|index| term.nodes.iter().any(|node| matches!(*node, TermNode::Var(found) if found == *index))))]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — no variables yields only zero; overlapping variables
    ///   on the two sides yield one spike each in ascending order, at one above
    ///   the unfolding successor count. A maximal representable count refuses
    ///   the next spike, exposing omissions, a wrong height and unchecked
    ///   increment.
    /// - witness: `level_oracle::level_oracle::unfolding_count_and_spike_boundaries`
    #[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|family| {
        let mut names = variables(left);
        names.extend(variables(right));
        family.first().is_some_and(BTreeMap::is_empty)
            && family.len() == names.len().saturating_add(1)
            && succ_count(right).ok().and_then(|count| count.0.checked_add(1)).is_some_and(|spike|
                family.iter().skip(1).zip(names).all(|(valuation, index)|
                    valuation.len() == 1 && valuation.get(&index) == Some(&LevelValue::from(spike))))
    }))]
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
    ///
    /// # Adequacy
    /// - hypothesis: L2 — generated canonical comparisons agree with the
    ///   semantic reference. L3 — zero, unequal variables, shared successors
    ///   and equality under both modes distinguish an omitted spike or a
    ///   missing strict shift.
    /// - witness: `level_oracle::level_oracle::prop_leq_agrees_with_semantic_reference`
    /// - witness: `level_oracle::level_oracle::prop_lt_agrees_with_semantic_reference`
    /// - witness: `level_oracle::level_oracle::reference_arithmetic_and_absence_boundaries`
    #[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|answer|
        valuation_family(left, right).is_ok_and(|family| bool::from(*answer) ==
            family.iter().all(|valuation| match (eval(left, valuation), eval(right, valuation)) {
                (Ok(left), Ok(right)) => u128::from(left).checked_add(u128::from(bool::from(strict)))
                    .is_some_and(|shifted| shifted <= u128::from(right)),
                _ => false,
            }))))]
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
    ///
    /// # Adequacy
    /// - hypothesis: L2 — generated canonical terms are compared to
    ///   independently evaluated zero-and-spike valuations. Equality, distinct
    ///   variables and unit successors separate strictness, missing spikes and
    ///   reversed comparison.
    /// - witness: `level_oracle::level_oracle::prop_leq_agrees_with_semantic_reference`
    /// - witness: `level_oracle::level_oracle::prop_lt_agrees_with_semantic_reference`
    #[spec(requires: [left, right].iter().all(|term|
        !term.nodes.is_empty() && term.nodes.iter().enumerate().all(|(at, node)| match *node {
        TermNode::Zero | TermNode::Var(_) => true,
        TermNode::Succ(child) => child.0 < at,
        TermNode::Max(left, right) => left.0 < at && right.0 < at,
    })))]
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
    ///
    /// # Adequacy
    /// - hypothesis: L2 — generated terms compare canonical identity to
    ///   two-sided semantic order, including shared joins and equal denotations
    ///   with different syntax; lost normalization or wrong symmetry changes
    ///   that equality.
    /// - witness: `level_oracle::level_oracle::prop_eq_agrees_with_semantic_reference`
    #[spec(requires: [left, right].iter().all(|term|
        !term.nodes.is_empty() && term.nodes.iter().enumerate().all(|(at, node)| match *node {
        TermNode::Zero | TermNode::Var(_) => true,
        TermNode::Succ(child) => child.0 < at,
        TermNode::Max(left, right) => left.0 < at && right.0 < at,
    })))]
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
    ///
    /// # Adequacy
    /// - hypothesis: L2 — generated comparisons produce evidence validated in
    ///   both modes. Equality and incomparable variables exercise witness and
    ///   refutation branches, exposing wrong modes, offsets and invalid
    ///   counter-valuations.
    /// - witness: `level_oracle::level_oracle::prop_evidence_validates`
    #[spec(requires: [left, right].iter().all(|term|
        !term.nodes.is_empty() && term.nodes.iter().enumerate().all(|(at, node)| match *node {
        TermNode::Zero | TermNode::Var(_) => true,
        TermNode::Succ(child) => child.0 < at,
        TermNode::Max(left, right) => left.0 < at && right.0 < at,
    })))]
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
    ///
    /// # Adequacy
    /// - hypothesis: L2 — generated terms compare strict order to successor
    ///   non-strict order; equal terms and one-successor gaps expose a missing
    ///   increment or an inclusive strict comparison.
    /// - witness: `level_oracle::level_oracle::prop_lt_equals_succ_leq`
    #[spec(requires: [left, right].iter().all(|term|
        !term.nodes.is_empty() && term.nodes.iter().enumerate().all(|(at, node)| match *node {
        TermNode::Zero | TermNode::Var(_) => true,
        TermNode::Succ(child) => child.0 < at,
        TermNode::Max(left, right) => left.0 < at && right.0 < at,
    })))]
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
    ///
    /// # Adequacy
    /// - hypothesis: L2 — generated triples compare canonical join identities,
    ///   including zero, repeated operands and differently associated joins;
    ///   changed normalization, operand loss or an incorrect unit violates
    ///   those identities.
    /// - witness: `level_oracle::level_oracle::prop_max_laws`
    #[spec(requires: [first, second, third].iter().all(|term|
        !term.nodes.is_empty() && term.nodes.iter().enumerate().all(|(at, node)| match *node {
        TermNode::Zero | TermNode::Var(_) => true,
        TermNode::Succ(child) => child.0 < at,
        TermNode::Max(left, right) => left.0 < at && right.0 < at,
    })))]
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
    ///
    /// # Adequacy
    /// - hypothesis: L2 — generated pairs compare successor-before-join with
    ///   join-before-successor, including zero and shared operands; a missing
    ///   component increment or incorrect absorption breaks canonical equality.
    /// - witness: `level_oracle::level_oracle::prop_succ_distributes_over_max`
    #[spec(requires: [first, second].iter().all(|term|
        !term.nodes.is_empty() && term.nodes.iter().enumerate().all(|(at, node)| match *node {
        TermNode::Zero | TermNode::Var(_) => true,
        TermNode::Succ(child) => child.0 < at,
        TermNode::Max(left, right) => left.0 < at && right.0 < at,
    })))]
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
    ///
    /// # Adequacy
    /// - hypothesis: L2 — generated pairs expose equality, incomparability and
    ///   join upper bounds; wrong strictness, an asymmetric equality decision
    ///   or a lost join component breaks the exact laws.
    /// - witness: `level_oracle::level_oracle::prop_order_laws`
    #[spec(requires: [first, second].iter().all(|term|
        !term.nodes.is_empty() && term.nodes.iter().enumerate().all(|(at, node)| match *node {
        TermNode::Zero | TermNode::Var(_) => true,
        TermNode::Succ(child) => child.0 < at,
        TermNode::Max(left, right) => left.0 < at && right.0 < at,
    })))]
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
    ///
    /// # Adequacy
    /// - hypothesis: L2 — generated triples include equality and strict offset
    ///   chains; when both premises hold, the conclusion must hold. A missing
    ///   transitive comparison fails the exact verdict implication.
    /// - witness: `level_oracle::level_oracle::prop_leq_is_transitive`
    #[spec(requires: [first, second, third].iter().all(|term|
        !term.nodes.is_empty() && term.nodes.iter().enumerate().all(|(at, node)| match *node {
        TermNode::Zero | TermNode::Var(_) => true,
        TermNode::Succ(child) => child.0 < at,
        TermNode::Max(left, right) => left.0 < at && right.0 < at,
    })))]
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
    ///
    /// # Adequacy
    /// - hypothesis: L2 — generated terms under bounded valuations compare
    ///   direct arena evaluation to canonical evaluation, with absent or zero
    ///   variables and positive assignments separating wrong substitution, join
    ///   and successor.
    /// - witness: `level_oracle::level_oracle::prop_eval_agrees_with_reference`
    /// - witness: `level_oracle::level_oracle::reference_arithmetic_and_absence_boundaries`
    #[spec(requires: term.nodes.iter().enumerate().all(|(at, node)| match *node {
        TermNode::Zero | TermNode::Var(_) => true,
        TermNode::Succ(child) => child.0 < at,
        TermNode::Max(left, right) => left.0 < at && right.0 < at,
    }))]
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

    #[test]
    fn selector_and_topological_builder_boundaries()
    {
        assert_eq!(pick(NodeSelector(u32::MAX), TermId(0)), None);
        assert_eq!(pick(NodeSelector(u32::MAX), TermId(1)), Some(TermId(0)));
        assert_eq!(pick(NodeSelector(u32::MAX), TermId(2)), Some(TermId(1)));
        if let Ok(wide) = usize::try_from(u64::from(u32::MAX).saturating_add(1)) {
            assert_eq!(pick(NodeSelector(0), TermId(wide)), None);
        }
        for shape in [
            TermShape::Succ(NodeSelector(0)),
            TermShape::Max(NodeSelector(0), NodeSelector(u32::MAX)),
        ] {
            assert_eq!(
                eval(&build(&[shape]), &BTreeMap::new()),
                Ok(LevelValue::ZERO)
            );
        }
        let term = build(&[
            TermShape::Zero,
            TermShape::Succ(NodeSelector(u32::MAX)),
            TermShape::Max(NodeSelector(u32::MAX), NodeSelector(0)),
        ]);
        assert_eq!(eval(&term, &BTreeMap::new()), Ok(LevelValue::from(1_u128)));
        assert_eq!(
            to_level(&term)
                .expect("canonical term")
                .eval(&BTreeMap::new()),
            Ok(LevelValue::from(1_u128))
        );
    }

    #[test]
    fn reference_arithmetic_and_absence_boundaries()
    {
        assert_eq!(
            eval(&build(&[]), &BTreeMap::new()),
            Err(TermFailure::NoRoot)
        );
        assert_eq!(to_level(&build(&[])), Err(TermFailure::NoRoot));
        assert_eq!(
            child::<u128>(&[], TermId(0)),
            Err(TermFailure::DanglingChild)
        );
        assert_eq!(child(&[3_u128, 7], TermId(0)), Ok(3));
        assert_eq!(child(&[3_u128, 7], TermId(1)), Ok(7));
        assert_eq!(
            child(&[3_u128, 7], TermId(2)),
            Err(TermFailure::DanglingChild)
        );
        let variable = LevelVarIndex::from(0_u32);
        let atom = build(&[TermShape::Var(variable)]);
        let successor = build(&[TermShape::Var(variable), TermShape::Succ(NodeSelector(0))]);
        let shared = build(&[
            TermShape::Var(variable),
            TermShape::Succ(NodeSelector(0)),
            TermShape::Max(NodeSelector(1), NodeSelector(1)),
        ]);
        assert_eq!(eval(&atom, &BTreeMap::new()), Ok(LevelValue::ZERO));
        assert_eq!(
            eval(&shared, &BTreeMap::new()),
            Ok(LevelValue::from(1_u128))
        );
        let valuation = BTreeMap::from([(variable, LevelValue::from(7_u128))]);
        assert_eq!(eval(&atom, &valuation), Ok(LevelValue::from(7_u128)));
        assert_eq!(eval(&shared, &valuation), Ok(LevelValue::from(8_u128)));
        let largest = BTreeMap::from([(variable, LevelValue::from(u128::MAX))]);
        assert_eq!(eval(&atom, &largest), Ok(LevelValue::from(u128::MAX)));
        assert_eq!(
            eval(&successor, &largest),
            Err(TermFailure::ReferenceOverflow)
        );
        assert_eq!(
            semantic_leq(&atom, &atom, Strictness::NON_STRICT),
            Ok(OrderComparison::from(true))
        );
        assert_eq!(
            semantic_leq(&atom, &atom, Strictness::STRICT),
            Ok(OrderComparison::from(false))
        );
        assert_eq!(
            semantic_leq(&atom, &successor, Strictness::STRICT),
            Ok(OrderComparison::from(true))
        );
        assert_eq!(
            semantic_leq(&successor, &atom, Strictness::NON_STRICT),
            Ok(OrderComparison::from(false))
        );
        assert_eq!(check_eval_agreement(&shared, &[]), Ok(()));
        assert_eq!(
            check_eval_agreement(&shared, &[LevelValue::from(7_u128)]),
            Ok(())
        );
    }

    #[test]
    fn unfolding_count_and_spike_boundaries()
    {
        let x = LevelVarIndex::from(0_u32);
        let y = LevelVarIndex::from(1_u32);
        let shared = build(&[
            TermShape::Zero,
            TermShape::Succ(NodeSelector(0)),
            TermShape::Max(NodeSelector(1), NodeSelector(1)),
        ]);
        assert_eq!(succ_count(&shared), Ok(SuccCount(2)));
        let names = build(&[TermShape::Var(y), TermShape::Var(x), TermShape::Var(y)]);
        assert_eq!(variables(&names), BTreeSet::from([x, y]));
        assert_eq!(variables(&build(&[TermShape::Zero])), BTreeSet::new());
        assert_eq!(
            valuation_family(&names, &shared),
            Ok(vec![
                BTreeMap::new(),
                BTreeMap::from([(x, LevelValue::from(3_u128))]),
                BTreeMap::from([(y, LevelValue::from(3_u128))]),
            ])
        );
        assert_eq!(
            valuation_family(&shared, &shared),
            Ok(vec![BTreeMap::new()])
        );
        let mut doubled = build(&[TermShape::Zero, TermShape::Succ(NodeSelector(0))]);
        for _step in 0_u32 .. 128 {
            let previous = TermId(doubled.nodes.len().saturating_sub(1));
            doubled.nodes.push(TermNode::Max(previous, previous));
        }
        assert_eq!(succ_count(&doubled), Err(TermFailure::ReferenceOverflow));
        let mut ceiling = build(&[TermShape::Zero]);
        for _step in 0_u32 .. 128 {
            let previous = TermId(ceiling.nodes.len().saturating_sub(1));
            ceiling.nodes.push(TermNode::Max(previous, previous));
            ceiling.nodes.push(TermNode::Succ(TermId(
                ceiling.nodes.len().saturating_sub(1),
            )));
        }
        assert_eq!(succ_count(&ceiling), Ok(SuccCount(u128::MAX)));
        assert_eq!(
            valuation_family(&names, &ceiling),
            Err(TermFailure::ReferenceOverflow)
        );
    }

    #[test]
    fn generator_support_stays_within_its_domain()
    {
        use proptest::strategy::ValueTree as _;
        let mut runner = proptest::test_runner::TestRunner::deterministic();
        let shapes = shape_strategy();
        let terms = term_strategy();
        let mut seen = BTreeSet::new();
        for _draw in 0_u32 .. 256 {
            let kind = match shapes.new_tree(&mut runner).expect("shape draw").current() {
                | TermShape::Zero => 0_u8,
                | TermShape::Var(index) => {
                    assert!(u32::from(index) < VARIABLE_COUNT);
                    1
                },
                | TermShape::Succ(_) => 2,
                | TermShape::Max(..) => 3,
            };
            let _fresh = seen.insert(kind);
            let term = terms.new_tree(&mut runner).expect("term draw").current();
            assert!((1 ..= NODE_BUDGET).contains(&term.nodes.len()));
            assert!(term.nodes.iter().enumerate().all(|(at, node)| match *node {
                | TermNode::Zero | TermNode::Var(_) => true,
                | TermNode::Succ(child) => child.0 < at,
                | TermNode::Max(left, right) => left.0 < at && right.0 < at,
            }));
        }
        assert_eq!(seen, BTreeSet::from([0_u8, 1, 2, 3]));
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
