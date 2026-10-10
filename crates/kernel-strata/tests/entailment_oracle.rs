extern crate alloc;
#[cfg(test)]
mod entailment_oracle
{
    //! The acceptance gate for entailment under a landmark poset: **empty-poset
    //! agreement**. With no landmark constraints declared, loop-checking
    //! entailment must agree with the free-fragment order oracle on every
    //! generated input, exactly and in both strictness modes.
    //!
    //! The two deciders share no decision machinery — the free oracle compares
    //! canonical forms by domination, entailment saturates a Horn clause system
    //! — so agreement is a genuine differential rather than a tautology.
    //! The free oracle is itself differentially anchored to a semantic
    //! reference in the level-oracle suite, which is what makes it
    //! admissible as the external oracle here.
    //!
    //! The suite also pins, under a fixed nonempty poset: evidence validation
    //! on every decided query in both dichotomy branches, the law that
    //! strict order is non-strict order after a successor, and monotonicity
    //! of entailment in the hypotheses — whatever the free oracle accepts,
    //! an admitted poset accepts.
    //!
    //! Generated terms are flat, id-addressed arenas with no owning-pointer
    //! recursion, folded into canonical levels by one forward pass over the
    //! node vector. Agreement failures are assertions, since agreement is
    //! the property under test; harness failures return [`TermFailure`].

    use anodized::spec;
    use gandr_kernel_strata::AdmissionOutcome;
    use gandr_kernel_strata::Entailment;
    use gandr_kernel_strata::EntailmentHolds;
    use gandr_kernel_strata::LandmarkConstraint;
    use gandr_kernel_strata::LandmarkPoset;
    use gandr_kernel_strata::Level;
    use gandr_kernel_strata::LevelError;
    use gandr_kernel_strata::LevelVar;
    use gandr_kernel_strata::LevelVarIndex;
    use gandr_kernel_strata::PosetError;
    use gandr_kernel_strata::Strictness;
    use gandr_kernel_strata::validate_entailment_countermodel;
    use gandr_kernel_strata::validate_entailment_witness;
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
    const NODE_BUDGET: usize = 16;

    /// The first variable of the fixed poset.
    ///
    /// # Specification
    /// trivial.
    fn x() -> LevelVar
    {
        LevelVar::new(LevelVarIndex::from(0_u32))
    }

    /// The second variable of the fixed poset.
    ///
    /// # Specification
    /// trivial.
    fn y() -> LevelVar
    {
        LevelVar::new(LevelVarIndex::from(1_u32))
    }

    /// The third variable of the fixed poset.
    ///
    /// # Specification
    /// trivial.
    fn z() -> LevelVar
    {
        LevelVar::new(LevelVarIndex::from(2_u32))
    }

    /// A node identifier inside a generated term arena.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct TermId(usize);

    /// A generated selector, reduced modulo the node count already built so it
    /// always names an earlier node.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct NodeSelector(u32);

    /// One node of a generated free level term. Children name strictly earlier
    /// nodes, so the arena is a flat id-addressed acyclic structure.
    ///
    /// # Specification
    /// - requires: child identifiers precede this node's position in its arena.
    /// - executable: none — the enclosing arena and position are external to
    ///   this node; the builder and fold check the topological relation.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — first-node selectors become zero and later selectors
    ///   wrap backward; exact folded successor and shared-join levels expose a
    ///   dangling edge, a wrong fallback or lost sharing.
    /// - witness: `entailment_oracle::entailment_oracle::selector_and_fold_boundaries`
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
    ///   last node is the root, or there is no root in an empty arena.
    /// - executable: none — data-item predicates are not checked at
    ///   construction; the builder and fold check the topological invariant.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero-predecessor shapes, wrapped selectors and an
    ///   empty arena distinguish wrong fallback, malformed edges and
    ///   missing-root handling through exact levels; deterministic draws check
    ///   the generator domain.
    /// - witness: `entailment_oracle::entailment_oracle::selector_and_fold_boundaries`
    /// - witness: `entailment_oracle::entailment_oracle::generator_support_stays_within_its_domain`
    #[repr(transparent)]
    #[derive(Clone, Debug)]
    struct Term
    {
        /// The nodes, each referring only to earlier ones.
        nodes: Vec<TermNode>,
    }

    /// A failure of the test harness itself, as distinct from a disagreement
    /// between the two deciders.
    ///
    /// None of these should be reachable from the generator or from the fixed
    /// posets, so each one surfacing is itself a finding rather than a panic
    /// buried in a helper.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum TermFailure
    {
        /// The arena was empty, so it has no root.
        NoRoot,
        /// A node named a child the fold had not yet computed, which the
        /// topological build order excludes.
        DanglingChild,
        /// A constraint set the harness declares as admitting did not admit.
        NotAdmitted,
        /// A level constructor refused.
        Level(LevelError),
        /// A poset operation refused.
        Poset(PosetError),
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

    impl From<PosetError> for TermFailure
    {
        /// Wraps a poset failure as a harness failure.
        ///
        /// # Specification
        /// trivial.
        fn from(error: PosetError) -> Self
        {
            Self::Poset(error)
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
    /// - hypothesis: L3 — empty, singleton and two-node prefixes and an index
    ///   beyond the selector width expose modulo and narrowing mistakes through
    ///   exact optional indices; folded successor values observe the chosen
    ///   edges.
    /// - witness: `entailment_oracle::entailment_oracle::selector_and_fold_boundaries`
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
    /// - provides: the acyclic arena the fold below reads.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — first-node successors and joins become zero, later
    ///   selectors wrap backward, and shared joins preserve successor values.
    ///   Exact canonical results expose wrong fallback, selection or topology.
    /// - witness: `entailment_oracle::entailment_oracle::selector_and_fold_boundaries`
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
    ///   draws, not one runtime value this call can inspect.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — deterministic draws reach every constructor and keep
    ///   variable indices inside the declared domain. L2 — generated entailment
    ///   comparisons then observe the resolved terms, exposing missing
    ///   alternatives and malformed or out-of-domain generated inputs.
    /// - witness: `entailment_oracle::entailment_oracle::generator_support_stays_within_its_domain`
    /// - witness: `entailment_oracle::entailment_oracle::prop_empty_poset_agrees_with_the_free_oracle`
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
    /// - executable: none — the opaque strategy's support concerns future
    ///   draws; sampling is evidence rather than a postcondition on this value.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — deterministic draws remain nonempty, bounded and
    ///   topologically ordered; L2 compares the resulting queries with the free
    ///   oracle. Empty, oversized and forward-pointing arenas violate the
    ///   domain.
    /// - witness: `entailment_oracle::entailment_oracle::generator_support_stays_within_its_domain`
    /// - witness: `entailment_oracle::entailment_oracle::prop_empty_poset_agrees_with_the_free_oracle`
    fn term_strategy() -> impl Strategy<Value = Term>
    {
        proptest::collection::vec(shape_strategy(), 1 ..= NODE_BUDGET)
            .prop_map(|shapes| build(&shapes))
    }

    /// Folds a term into a canonical level through the smart constructors, in
    /// one forward pass over the node vector.
    ///
    /// # Specification
    /// - requires: `term`'s nodes name only strictly earlier nodes, which the
    ///   arena builder guarantees.
    /// - ensures: returns the canonical level the root node denotes, folded
    ///   through the smart constructors.
    /// - provides: the generated side of every differential row.
    /// - fails: `TermFailure::NoRoot` on an empty arena, `DanglingChild` on a
    ///   child the fold has not reached, and `TermFailure::Level` where a
    ///   successor passes the representable range.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero, a wrapped successor and a shared join yield
    ///   exact levels, while an empty arena refuses with `NoRoot`. L2 —
    ///   generated empty-poset queries agree with free comparisons, exposing
    ///   wrong constructor selection and lost or misordered edges.
    /// - witness: `entailment_oracle::entailment_oracle::selector_and_fold_boundaries`
    /// - witness: `entailment_oracle::entailment_oracle::prop_empty_poset_agrees_with_the_free_oracle`
    #[spec(requires: term.nodes.iter().enumerate().all(|(at, node)| match *node {
        TermNode::Zero | TermNode::Var(_) => true,
        TermNode::Succ(child) => child.0 < at,
        TermNode::Max(left, right) => left.0 < at && right.0 < at,
    }),
        ensures: |ret| !term.nodes.is_empty() || matches!(ret, Err(TermFailure::NoRoot)))]
    fn to_level(term: &Term) -> Result<Level, TermFailure>
    {
        let mut levels: Vec<Level> = Vec::with_capacity(term.nodes.len());
        for &node in &term.nodes {
            let level = match node {
                | TermNode::Zero => Level::zero(),
                | TermNode::Var(index) => Level::var(LevelVar::new(index)),
                | TermNode::Succ(inner) => {
                    let inner = child(&levels, inner)?;
                    inner.succ()?
                },
                | TermNode::Max(left, right) => {
                    let left = child(&levels, left)?;
                    let right = child(&levels, right)?;
                    left.max(&right)
                },
            };
            levels.push(level);
        }
        levels.last().cloned().ok_or(TermFailure::NoRoot)
    }

    /// Reads an earlier node's level.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the level already folded at `id`.
    /// - provides: the arena read the fold makes for each child.
    /// - fails: `TermFailure::DanglingChild` when the fold has not reached
    ///   `id`, which the topological build order excludes.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an empty list, existing first and last slots, and the
    ///   first absent slot distinguish defaulted absence or an off-by-one
    ///   lookup through exact canonical levels and the dangling-child refusal.
    /// - witness: `entailment_oracle::entailment_oracle::selector_and_fold_boundaries`
    #[spec(ensures: |ret| ret.as_ref().ok() == levels.get(id.0))]
    fn child(
        levels: &[Level],
        id: TermId,
    ) -> Result<Level, TermFailure>
    {
        levels.get(id.0).cloned().ok_or(TermFailure::DanglingChild)
    }

    /// Admits a constraint set the harness declares as admitting.
    ///
    /// # Specification
    /// - requires: nothing beyond well-formed constraints.
    /// - ensures: returns the admitted poset.
    /// - provides: the admitted-arm fixture builder both posets below use.
    /// - fails: `TermFailure::NotAdmitted` when the set loops, and
    ///   `TermFailure::Poset` when admission refuses.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty and acyclic hypotheses admit while a
    ///   self-successor equality returns `NotAdmitted`. Independent consistency
    ///   validation and exact query verdicts expose an inverted branch or
    ///   discarded hypotheses.
    /// - witness: `entailment_oracle::entailment_oracle::poset_fixture_relation_boundaries`
    #[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|poset|
        gandr_kernel_strata::validate_consistency(poset.constraints(), poset.consistency()).is_ok()))]
    fn admitted(constraints: Vec<LandmarkConstraint>) -> Result<LandmarkPoset, TermFailure>
    {
        let outcome = LandmarkPoset::admit(constraints)?;
        match outcome {
            | AdmissionOutcome::Admitted(poset) => Ok(poset),
            | AdmissionOutcome::Loop(_witness) => Err(TermFailure::NotAdmitted),
        }
    }

    /// The empty poset — the degeneration the acceptance gate quantifies over.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the poset with no declared constraints.
    /// - provides: the degenerate poset the agreement row quantifies over.
    /// - fails: as admission does, which an empty constraint set never
    ///   triggers.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — equality holds but unrelated variables are
    ///   incomparable without hypotheses; L2 — generated queries agree with the
    ///   free oracle. A spurious declaration or rejection changes those exact
    ///   answers.
    /// - witness: `entailment_oracle::entailment_oracle::poset_fixture_relation_boundaries`
    /// - witness: `entailment_oracle::entailment_oracle::prop_empty_poset_agrees_with_the_free_oracle`
    #[spec(ensures: |ret| ret.as_ref().is_ok_and(|poset| poset.constraints().is_empty()
        && poset.variables().is_empty()))]
    fn empty_poset() -> Result<LandmarkPoset, TermFailure>
    {
        admitted(Vec::new())
    }

    /// A fixed nonempty poset over the generator's variable range: `x0 ≤ x1`
    /// and `x1 + 1 ≤ x2`, so hypothesis paths, strict and non-strict, are
    /// genuinely exercised by generated queries.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the poset declaring `x0 ≤ x1` and `x1 + 1 ≤ x2`.
    /// - provides: the nonempty-hypothesis fixture, chosen inside the
    ///   generator's variable range so generated queries reach both hypothesis
    ///   paths.
    /// - fails: as the successor and admission do, neither of which these fixed
    ///   constraints trigger.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the first edge is non-strict only, the second is
    ///   strict, their composition holds and their reverse does not. These
    ///   exact verdicts expose a missing, reversed or incorrectly shifted
    ///   fixture hypothesis.
    /// - witness: `entailment_oracle::entailment_oracle::poset_fixture_relation_boundaries`
    #[spec(ensures: |ret| ret.as_ref().is_ok_and(|poset| poset.constraints().len() == 2
        && poset.constraints().iter().zip([(x(), 0_u64, y()), (y(), 1_u64, z())])
            .all(|(constraint, (left, offset, right))| constraint.relation() == gandr_kernel_strata::ConstraintRelation::Leq
                && constraint.left().atoms().eq(core::iter::once((left, gandr_kernel_strata::LevelOffset::from(offset))))
                && constraint.right().atoms().eq(core::iter::once((right, gandr_kernel_strata::LevelOffset::ZERO))))))]
    fn fixed_poset() -> Result<LandmarkPoset, TermFailure>
    {
        let first = Level::var(x());
        let second = Level::var(y());
        let second_succ = second.succ()?;
        let third = Level::var(z());
        let first_constraint = LandmarkConstraint::leq(first, second)?;
        let second_constraint = LandmarkConstraint::leq(second_succ, third)?;
        admitted(vec![first_constraint, second_constraint])
    }

    /// Decides under `poset`, validating whichever evidence comes back, and
    /// returns the boolean verdict.
    ///
    /// # Specification
    /// - requires: nothing; any two levels are admissible.
    /// - ensures: returns the verdict, having first checked that the evidence
    ///   records the queried mode and validates against the two levels.
    /// - provides: the decision every property row spends, with the validator
    ///   run folded in so no row reads unvalidated evidence.
    /// - fails: as the query does.
    /// - panics: when the evidence records the wrong mode or fails validation.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — generated queries validate evidence under empty and
    ///   fixed hypotheses in both modes. L3 — equality, unrelated variables,
    ///   non-strict and strict hypotheses pin returned truth values, exposing
    ///   branch inversion and loss of the strictness mode.
    /// - witness: `entailment_oracle::entailment_oracle::prop_empty_poset_evidence_validates`
    /// - witness: `entailment_oracle::entailment_oracle::prop_fixed_poset_evidence_validates`
    /// - witness: `entailment_oracle::entailment_oracle::poset_fixture_relation_boundaries`
    #[spec(ensures: |ret| ret == if bool::from(strict) {
        poset.entails_lt(left, right).map_err(TermFailure::from)
    } else {
        poset.entails_leq(left, right).map_err(TermFailure::from)
    })]
    fn decide_validated(
        poset: &LandmarkPoset,
        left: &Level,
        right: &Level,
        strict: Strictness,
    ) -> Result<EntailmentHolds, TermFailure>
    {
        let decision = if bool::from(strict) {
            poset.entails_lt_with_evidence(left, right)
        }
        else {
            poset.entails_leq_with_evidence(left, right)
        }?;
        match decision {
            | Entailment::Holds(witness) => {
                assert_eq!(witness.strict(), strict, "the witness records its mode");
                assert_eq!(
                    validate_entailment_witness(poset, left, right, &witness),
                    Ok(()),
                    "every oracle witness must validate"
                );
                Ok(EntailmentHolds::from(true))
            },
            | Entailment::Refuted(countermodel) => {
                assert_eq!(
                    countermodel.strict(),
                    strict,
                    "the countermodel records its mode"
                );
                assert_eq!(
                    validate_entailment_countermodel(poset, left, right, &countermodel),
                    Ok(()),
                    "every oracle countermodel must validate"
                );
                Ok(EntailmentHolds::from(false))
            },
        }
    }

    /// Checks that empty-poset entailment is the free order oracle, exactly.
    ///
    /// # Specification
    /// - requires: nothing; any two generated terms are admissible.
    /// - ensures: returns successfully exactly when empty-poset entailment
    ///   agrees with the free order oracle on the two terms, in both modes.
    /// - provides: the acceptance gate's body — the two deciders share no
    ///   decision machinery, so agreement is evidence rather than tautology.
    /// - fails: as the fold and the query do.
    /// - panics: on a disagreement, which is how the property reports.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — generated empty-poset queries are compared against
    ///   the independent free oracle in both modes. Equality, zero and unequal
    ///   variable offsets expose wrong mode shifts, lost constants and false
    ///   domination.
    /// - witness: `entailment_oracle::entailment_oracle::prop_empty_poset_agrees_with_the_free_oracle`
    #[spec(requires: [left, right].iter().all(|term| term.nodes.iter().enumerate().all(|(at, node)| match *node {
        TermNode::Zero | TermNode::Var(_) => true,
        TermNode::Succ(child) => child.0 < at,
        TermNode::Max(left, right) => left.0 < at && right.0 < at,
    })))]
    fn check_empty_poset_agreement(
        left: &Term,
        right: &Term,
    ) -> Result<(), TermFailure>
    {
        let poset = empty_poset()?;
        let left_level = to_level(left)?;
        let right_level = to_level(right)?;
        let entailed_leq = poset.entails_leq(&left_level, &right_level)?;
        assert_eq!(
            bool::from(entailed_leq),
            bool::from(left_level.leq(&right_level)),
            "empty-poset entailment is the free non-strict order"
        );
        let entailed_lt = poset.entails_lt(&left_level, &right_level)?;
        assert_eq!(
            bool::from(entailed_lt),
            bool::from(left_level.lt(&right_level)),
            "empty-poset entailment is the free strict order"
        );
        Ok(())
    }

    /// Checks that every piece of evidence validates under `poset`, in both
    /// modes.
    ///
    /// # Specification
    /// - requires: nothing; any two generated terms are admissible.
    /// - ensures: returns successfully exactly when the evidence the oracle
    ///   returns for the two terms validates, in both modes.
    /// - provides: the self-incrimination row: the decision procedure is
    ///   checked against the validators on every generated input.
    /// - fails: as the fold and the query do.
    /// - panics: on evidence that fails validation.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — generated queries check both evidence branches and
    ///   modes against independent validators with empty and fixed hypotheses.
    ///   Equality and incomparable terms distinguish invalid witnesses from
    ///   countermodels.
    /// - witness: `entailment_oracle::entailment_oracle::prop_empty_poset_evidence_validates`
    /// - witness: `entailment_oracle::entailment_oracle::prop_fixed_poset_evidence_validates`
    #[spec(requires: [left, right].iter().all(|term| term.nodes.iter().enumerate().all(|(at, node)| match *node {
        TermNode::Zero | TermNode::Var(_) => true,
        TermNode::Succ(child) => child.0 < at,
        TermNode::Max(left, right) => left.0 < at && right.0 < at,
    })))]
    fn check_evidence_validates(
        poset: &LandmarkPoset,
        left: &Term,
        right: &Term,
    ) -> Result<(), TermFailure>
    {
        let left_level = to_level(left)?;
        let right_level = to_level(right)?;
        for strict in [Strictness::NON_STRICT, Strictness::STRICT] {
            let _verdict = decide_validated(poset, &left_level, &right_level, strict)?;
        }
        Ok(())
    }

    /// Checks that strict entailment is non-strict entailment after a
    /// successor.
    ///
    /// # Specification
    /// - requires: nothing; any two generated terms are admissible.
    /// - ensures: returns successfully exactly when strict entailment of the
    ///   two terms agrees with non-strict entailment of the left successor.
    /// - provides: the row pinning that the two modes differ by exactly the
    ///   shift, under hypotheses rather than only in the free fragment.
    /// - fails: as the fold, the successor, and the query do.
    /// - panics: on a disagreement.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — generated strict queries equal successor non-strict
    ///   queries under the fixed hypotheses; zero versus one-unit gaps
    ///   distinguish a missing shift and a strict hypothesis interpreted as
    ///   non-strict.
    /// - witness: `entailment_oracle::entailment_oracle::prop_lt_equals_succ_leq_under_the_fixed_poset`
    #[spec(requires: [left, right].iter().all(|term| term.nodes.iter().enumerate().all(|(at, node)| match *node {
        TermNode::Zero | TermNode::Var(_) => true,
        TermNode::Succ(child) => child.0 < at,
        TermNode::Max(left, right) => left.0 < at && right.0 < at,
    })))]
    fn check_lt_equals_succ_leq(
        left: &Term,
        right: &Term,
    ) -> Result<(), TermFailure>
    {
        let poset = fixed_poset()?;
        let left_level = to_level(left)?;
        let right_level = to_level(right)?;
        let via_lt = poset.entails_lt(&left_level, &right_level)?;
        let shifted = left_level.succ()?;
        let via_succ = poset.entails_leq(&shifted, &right_level)?;
        assert_eq!(
            via_lt, via_succ,
            "strict entailment is non-strict entailment after a successor"
        );
        Ok(())
    }

    /// Checks that hypotheses only ever add entailments.
    ///
    /// # Specification
    /// - requires: nothing; any two generated terms are admissible.
    /// - ensures: returns successfully exactly when every free order between
    ///   the two terms survives under the fixed hypotheses, in both modes.
    /// - provides: the monotonicity row — hypotheses add entailments and remove
    ///   none.
    /// - fails: as the fold and the query do.
    /// - panics: on a free order the hypotheses lose.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — free entailments on generated terms survive adding
    ///   the fixed hypotheses in both modes; reflexive and successor
    ///   comparisons expose a hypothesis that accidentally removes an existing
    ///   derivation.
    /// - witness: `entailment_oracle::entailment_oracle::prop_hypotheses_are_monotone`
    #[spec(requires: [left, right].iter().all(|term| term.nodes.iter().enumerate().all(|(at, node)| match *node {
        TermNode::Zero | TermNode::Var(_) => true,
        TermNode::Succ(child) => child.0 < at,
        TermNode::Max(left, right) => left.0 < at && right.0 < at,
    })))]
    fn check_monotonicity(
        left: &Term,
        right: &Term,
    ) -> Result<(), TermFailure>
    {
        let poset = fixed_poset()?;
        let left_level = to_level(left)?;
        let right_level = to_level(right)?;
        if bool::from(left_level.leq(&right_level)) {
            let entailed = poset.entails_leq(&left_level, &right_level)?;
            assert!(
                bool::from(entailed),
                "hypotheses keep every free non-strict order"
            );
        }
        if bool::from(left_level.lt(&right_level)) {
            let entailed = poset.entails_lt(&left_level, &right_level)?;
            assert!(
                bool::from(entailed),
                "hypotheses keep every free strict order"
            );
        }
        Ok(())
    }

    /// Checks that entailment under hypotheses stays a reflexive, irreflexive
    /// and transitive provability relation.
    ///
    /// # Specification
    /// - requires: nothing; any three generated terms are admissible.
    /// - ensures: returns successfully exactly when entailment under the fixed
    ///   hypotheses is reflexive and transitive on the non-strict order and
    ///   irreflexive on the strict one.
    /// - provides: the order-laws row, which pins the relation's shape rather
    ///   than a single query's answer.
    /// - fails: as the fold and the query do.
    /// - panics: on a law the relation breaks.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — generated triples test non-strict reflexivity, strict
    ///   irreflexivity and transitivity under fixed hypotheses; equal levels
    ///   and two-edge chains expose an incorrect mode or a lost composed
    ///   entailment.
    /// - witness: `entailment_oracle::entailment_oracle::prop_entailment_order_laws_under_the_fixed_poset`
    #[spec(requires: [first, second, third].iter().all(|term| term.nodes.iter().enumerate().all(|(at, node)| match *node {
        TermNode::Zero | TermNode::Var(_) => true,
        TermNode::Succ(child) => child.0 < at,
        TermNode::Max(left, right) => left.0 < at && right.0 < at,
    })))]
    fn check_entailment_order_laws(
        first: &Term,
        second: &Term,
        third: &Term,
    ) -> Result<(), TermFailure>
    {
        let poset = fixed_poset()?;
        let first = to_level(first)?;
        let second = to_level(second)?;
        let third = to_level(third)?;
        let reflexive = poset.entails_leq(&first, &first)?;
        assert!(
            bool::from(reflexive),
            "entailment is reflexive on the non-strict order"
        );
        let irreflexive = poset.entails_lt(&first, &first)?;
        assert!(
            !bool::from(irreflexive),
            "entailment is irreflexive on the strict order"
        );
        let below = poset.entails_leq(&first, &second)?;
        let above = poset.entails_leq(&second, &third)?;
        if bool::from(below) && bool::from(above) {
            let composed = poset.entails_leq(&first, &third)?;
            assert!(bool::from(composed), "entailment is transitive");
        }
        Ok(())
    }

    #[test]
    fn selector_and_fold_boundaries()
    {
        assert_eq!(pick(NodeSelector(u32::MAX), TermId(0)), None);
        assert_eq!(pick(NodeSelector(u32::MAX), TermId(1)), Some(TermId(0)));
        assert_eq!(pick(NodeSelector(u32::MAX), TermId(2)), Some(TermId(1)));
        if let Ok(wide) = usize::try_from(u64::from(u32::MAX).saturating_add(1)) {
            assert_eq!(pick(NodeSelector(0), TermId(wide)), None);
        }
        assert_eq!(to_level(&build(&[])), Err(TermFailure::NoRoot));
        for shape in [
            TermShape::Succ(NodeSelector(0)),
            TermShape::Max(NodeSelector(0), NodeSelector(u32::MAX)),
        ] {
            assert_eq!(to_level(&build(&[shape])), Ok(Level::zero()));
        }
        let term = build(&[
            TermShape::Zero,
            TermShape::Succ(NodeSelector(u32::MAX)),
            TermShape::Max(NodeSelector(1), NodeSelector(1)),
        ]);
        let one = Level::zero().succ().expect("one fits");
        assert_eq!(to_level(&term), Ok(one.clone()));
        assert_eq!(child(&[], TermId(0)), Err(TermFailure::DanglingChild));
        let levels = [Level::zero(), one.clone()];
        assert_eq!(child(&levels, TermId(0)), Ok(Level::zero()));
        assert_eq!(child(&levels, TermId(1)), Ok(one));
        assert_eq!(child(&levels, TermId(2)), Err(TermFailure::DanglingChild));
    }

    #[test]
    fn poset_fixture_relation_boundaries()
    {
        let empty = empty_poset().expect("empty hypotheses admit");
        let fixed = fixed_poset().expect("acyclic hypotheses admit");
        for (left, right, mode, free, entailed) in [
            (x(), y(), Strictness::NON_STRICT, false, true),
            (x(), y(), Strictness::STRICT, false, false),
            (y(), z(), Strictness::STRICT, false, true),
            (z(), x(), Strictness::NON_STRICT, false, false),
            (x(), x(), Strictness::NON_STRICT, true, true),
            (x(), z(), Strictness::STRICT, false, true),
        ] {
            let left = Level::var(left);
            let right = Level::var(right);
            assert_eq!(
                decide_validated(&empty, &left, &right, mode),
                Ok(EntailmentHolds::from(free))
            );
            assert_eq!(
                decide_validated(&fixed, &left, &right, mode),
                Ok(EntailmentHolds::from(entailed))
            );
        }
        let constraint = LandmarkConstraint::equal(
            Level::var(x()),
            Level::var(x()).succ().expect("one offset fits"),
        )
        .expect("variable-only sides");
        assert!(matches!(
            admitted(vec![constraint]),
            Err(TermFailure::NotAdmitted)
        ));
    }

    #[test]
    fn generator_support_stays_within_its_domain()
    {
        use proptest::strategy::ValueTree as _;
        let mut runner = proptest::test_runner::TestRunner::deterministic();
        let shapes = shape_strategy();
        let terms = term_strategy();
        let mut seen = alloc::collections::BTreeSet::new();
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
        assert_eq!(seen, alloc::collections::BTreeSet::from([0_u8, 1, 2, 3]));
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(128))]

        /// The acceptance gate: empty-poset entailment is the free order oracle,
        /// exactly, in both strictness modes.
        #[test]
        fn prop_empty_poset_agrees_with_the_free_oracle(
            (left, right) in (term_strategy(), term_strategy())
        ) {
            prop_assert_eq!(check_empty_poset_agreement(&left, &right), Ok(()));
        }

        /// Every piece of evidence entailment returns validates against its query
        /// under the empty poset, in both modes and both branches.
        #[test]
        fn prop_empty_poset_evidence_validates(
            (left, right) in (term_strategy(), term_strategy())
        ) {
            let poset = empty_poset();
            prop_assert_eq!(
                poset.and_then(|poset| check_evidence_validates(&poset, &left, &right)),
                Ok(())
            );
        }

        /// Every piece of evidence entailment returns validates against its query
        /// under a fixed nonempty poset, hypothesis paths included.
        #[test]
        fn prop_fixed_poset_evidence_validates(
            (left, right) in (term_strategy(), term_strategy())
        ) {
            let poset = fixed_poset();
            prop_assert_eq!(
                poset.and_then(|poset| check_evidence_validates(&poset, &left, &right)),
                Ok(())
            );
        }

        /// The strict order is exactly the non-strict order after a successor on
        /// the left — under hypotheses too.
        #[test]
        fn prop_lt_equals_succ_leq_under_the_fixed_poset(
            (left, right) in (term_strategy(), term_strategy())
        ) {
            prop_assert_eq!(check_lt_equals_succ_leq(&left, &right), Ok(()));
        }

        /// Hypotheses only ever add entailments: whatever the free oracle accepts,
        /// an admitted poset accepts.
        #[test]
        fn prop_hypotheses_are_monotone(
            (left, right) in (term_strategy(), term_strategy())
        ) {
            prop_assert_eq!(check_monotonicity(&left, &right), Ok(()));
        }

        /// Entailment under hypotheses stays reflexive, irreflexive on the strict
        /// order, and transitive on generated levels.
        #[test]
        fn prop_entailment_order_laws_under_the_fixed_poset(
            (first, second, third) in (term_strategy(), term_strategy(), term_strategy())
        ) {
            prop_assert_eq!(
                check_entailment_order_laws(&first, &second, &third),
                Ok(())
            );
        }
    }
}
