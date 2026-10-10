//! Full laziness and beyond, read off the evaluator's step count.
//!
//! The spinal stance shares an abstraction's ribs: each maximal subterm of its
//! body that does not read its binder becomes a share of its own, and the
//! evaluator remembers each rib's weak head per configuration — one binding at
//! each of its free indices. Each witness builds one overlay at two sizes of
//! a chain whose evaluation costs a fixed number of steps per link, evaluates
//! it under both stances, and compares the growth of the step count between
//! the two sizes: the constant costs of the surrounding term cancel, and what
//! is left counts how many times the chain was evaluated. Every run's result
//! is read back and compared, as a tree, with the reference stance's.

/// The tree oracle, shared with the deep suites.
#[cfg(test)]
#[path = "support/trees.rs"]
mod trees;

/// The full-laziness witnesses, in a `cfg(test)` module so the crate's lint
/// wall reads them as test code rather than as shipping code.
#[cfg(test)]
mod full_laziness
{
    use anodized::spec;
    use gandr_core_nbe::Bound;
    use gandr_core_nbe::CompGraft;
    use gandr_core_nbe::CompNode;
    use gandr_core_nbe::Definitions;
    use gandr_core_nbe::DomainArena;
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
    use gandr_core_nbe::TracedDuplication;
    use gandr_core_nbe::ValueGraft;
    use gandr_core_nbe::ValueNode;
    use gandr_core_nbe::readback_computation;
    use gandr_core_term::ComputationId;
    use gandr_core_term::CoreArena;
    use gandr_core_term::DefinitionalEnvironment;
    use gandr_core_term::Zone;
    use gandr_kernel_conversion_trace::TraceLog;
    use gandr_kernel_term::DeBruijnIndex;

    use crate::trees::Term;
    use crate::trees::Trees;
    use crate::trees::same_tree;

    /// How many binds a chain holds.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct Links(u32);

    /// How many steps a run spent.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct Steps(u32);

    /// The chain's links at the smaller size.
    const FEWER: Links = Links(8);

    /// The chain's links at the larger size.
    const MORE: Links = Links(40);

    /// Fuel well above any witness's step count.
    ///
    /// # Specification
    /// trivial.
    fn ample() -> Fuel
    {
        Fuel::from(1_000_000_u32)
    }

    /// An intuitionistic index the witnesses read.
    #[derive(Clone, Copy, Debug)]
    enum Index
    {
        /// `x₀`.
        Zero,
        /// `x₁`.
        One,
        /// `x₂`.
        Two,
    }

    impl From<Index> for DeBruijnIndex
    {
        /// The index `index` names.
        ///
        /// # Specification
        /// trivial.
        #[inline]
        fn from(index: Index) -> Self
        {
            Self::from(match index {
                | Index::Zero => 0_u32,
                | Index::One => 1_u32,
                | Index::Two => 2_u32,
            })
        }
    }

    /// An overlay under construction.
    #[repr(transparent)]
    struct Build
    {
        /// The nodes minted so far.
        overlay: Overlay,
    }

    impl Build
    {
        /// Mint a value graft.
        ///
        /// # Specification
        /// trivial.
        fn value(
            &mut self,
            graft: ValueGraft,
        ) -> OverlayValueId
        {
            self.overlay
                .mint_value(ValueNode::Grafted(graft))
                .expect("a hand-built node mints")
        }

        /// Mint a computation graft.
        ///
        /// # Specification
        /// trivial.
        fn computation(
            &mut self,
            graft: CompGraft,
        ) -> OverlayCompId
        {
            self.overlay
                .mint_computation(CompNode::Grafted(graft))
                .expect("a hand-built node mints")
        }

        /// The unit value.
        ///
        /// # Specification
        /// trivial.
        fn unit(&mut self) -> OverlayValueId
        {
            self.value(ValueGraft::Unit)
        }

        /// The intuitionistic variable `index`.
        ///
        /// # Specification
        /// trivial.
        fn variable(
            &mut self,
            index: Index,
        ) -> OverlayValueId
        {
            self.value(ValueGraft::Variable {
                zone: Zone::Intuitionistic,
                index: DeBruijnIndex::from(index),
            })
        }

        /// `return value`.
        ///
        /// # Specification
        /// trivial.
        fn returning(
            &mut self,
            value: OverlayValueId,
        ) -> OverlayCompId
        {
            self.computation(CompGraft::Return(value))
        }

        /// `x ← bound; body`.
        ///
        /// # Specification
        /// trivial.
        fn bind(
            &mut self,
            bound: OverlayCompId,
            body: OverlayCompId,
        ) -> OverlayCompId
        {
            self.computation(CompGraft::Bind(bound, body))
        }

        /// `head argument`.
        ///
        /// # Specification
        /// trivial.
        fn apply(
            &mut self,
            head: OverlayCompId,
            argument: OverlayValueId,
        ) -> OverlayCompId
        {
            self.computation(CompGraft::Application(head, argument))
        }

        /// `force` of the innermost share's value occurrence at `position`.
        ///
        /// # Specification
        /// trivial.
        fn forced_occurrence(
            &mut self,
            position: SharePosition,
        ) -> OverlayCompId
        {
            let occurrence = self
                .overlay
                .mint_value(ValueNode::Bound(Bound {
                    distance: ShareDistance::from(0_u32),
                    position,
                }))
                .expect("an occurrence names no child");
            self.computation(CompGraft::Force(occurrence))
        }

        /// The innermost share's computation occurrence at `position`.
        ///
        /// # Specification
        /// trivial.
        fn computation_occurrence(
            &mut self,
            position: SharePosition,
        ) -> OverlayCompId
        {
            self.overlay
                .mint_computation(CompNode::Bound(Bound {
                    distance: ShareDistance::from(0_u32),
                    position,
                }))
                .expect("an occurrence names no child")
        }

        /// `x ← (… (x ← start; return x) …); return x`: `links` binds over
        /// `start`, each passing its bound value on, so the chain costs a
        /// fixed number of steps per link and reads what `start` reads.
        ///
        /// # Specification
        /// - requires: `start` resolves and the added links fit the id space.
        /// - ensures: exactly `links` binds pass intuitionistic index zero on,
        ///   ending at `start`; zero links return `start` unchanged.
        /// - panics: if a mint is refused.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — start is a live computation and the requested
        ///   links fit the id space. An independent bounded descent requires
        ///   exactly one bind and an intuitionistic zero-index return per link,
        ///   ending at start. The cost-slope witnesses distinguish an omitted
        ///   link, a wrong binder and reversed sequencing.
        /// - witness: `full_laziness::full_laziness::a_spinal_duplicate_shares_every_rib`
        /// - witness: `full_laziness::full_laziness::a_spinal_duplicate_shares_what_full_laziness_copies`
        /// - witness: `full_laziness::full_laziness::an_open_configuration_is_evaluated_per_occurrence`
        #[spec(
            requires: self.overlay.computation(start).is_some(),
            ensures: |ret| {
                let mut top = ret;
                for _ in 0..links.0 {
                    let Some(&CompNode::Grafted(CompGraft::Bind(bound, body))) = self.overlay.computation(top) else { return false; };
                    let Some(&CompNode::Grafted(CompGraft::Return(value))) = self.overlay.computation(body) else { return false; };
                    if self.overlay.value(value) != Some(&ValueNode::Grafted(ValueGraft::Variable { zone: Zone::Intuitionistic, index: DeBruijnIndex::from(0_u32) })) { return false; }
                    top = bound;
                }
                top == start
            }
        )]
        fn chain(
            &mut self,
            start: OverlayCompId,
            links: Links,
        ) -> OverlayCompId
        {
            let mut chained = start;
            for _link in 0 .. links.0 {
                let bound = self.variable(Index::Zero);
                let pass_on = self.returning(bound);
                chained = self.bind(chained, pass_on);
            }
            chained
        }

        /// Share `leg` among the two occurrences `body` holds.
        ///
        /// # Specification
        /// trivial.
        fn shared(
            &mut self,
            leg: OverlayId,
            body: OverlayCompId,
        ) -> OverlayCompId
        {
            self.overlay
                .mint_computation(CompNode::Shared(Sharing {
                    arity: ShareArity::from(2_u32),
                    leg,
                    body,
                }))
                .expect("the leg and the body resolve")
        }
    }

    /// A witness's overlay at a given chain length.
    type Built = fn(&mut Build, Links) -> OverlayCompId;

    /// Evaluate the overlay `built` makes at `links` under `stance`, and read
    /// the result back.
    ///
    /// # Specification
    /// - requires: `built` makes a closed computation overlay.
    /// - ensures: the steps the evaluation spent, and the result read back into
    ///   the arena the run erased into.
    /// - provides: the one run every witness compares.
    /// - panics: when installation, evaluation or readback refuses, which no
    ///   witness provokes.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the builder returns a closed computation. The
    ///   returned id must resolve in its returned arena and charged steps
    ///   cannot exceed the supplied fuel. Independent reference-tree
    ///   comparisons and exact relative growth separate wrong readback, swapped
    ///   stance results and a fictitious cost report.
    /// - witness: `full_laziness::full_laziness::a_spinal_duplicate_shares_every_rib`
    /// - witness: `full_laziness::full_laziness::a_spinal_duplicate_shares_what_full_laziness_copies`
    /// - witness: `full_laziness::full_laziness::an_open_configuration_is_evaluated_per_occurrence`
    #[spec(
        ensures: |ret| ret.0.0 <= u32::from(ample()) && ret.1.computation(ret.2).is_some()
    )]
    fn run(
        stance: DuplicationStance,
        built: Built,
        links: Links,
    ) -> (Steps, CoreArena, ComputationId)
    {
        let mut build = Build {
            overlay: Overlay::new(),
        };
        let root = built(&mut build, links);
        let mut overlay = build.overlay;
        let mut core = CoreArena::new();
        let chain = LoweredChain::new();
        let environment = DefinitionalEnvironment::new();
        let definitions = Definitions::new(&chain, &environment, environment.root());
        let mut domain = DomainArena::new();
        let mut log = TraceLog::new();
        let installed = TracedDuplication::install(stance, &mut log)
            .expect("a recording sink carries either stance");
        let (head, left) = installed
            .eval_overlay_computation(
                &mut overlay,
                &mut core,
                &mut domain,
                definitions,
                ample(),
                root,
            )
            .unwrap_or_else(|fault| panic!("{stance:?} at {links:?}: {fault:?}"));
        let read = readback_computation(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::Unfolding,
            ample(),
            head,
        )
        .expect("a closed result reads back");
        let spent = u32::from(ample())
            .checked_sub(u32::from(left))
            .expect("a run spends no more than it was given");
        (Steps(spent), core, read)
    }

    /// Run `built` at both sizes under both stances, check every result
    /// against the reference's, and answer how much each stance's step count
    /// grew between the sizes.
    ///
    /// # Specification
    /// - requires: as [`run`], with deterministic construction and
    ///   nondecreasing evaluation cost between the two sizes.
    /// - ensures: the growth under the reference stance, then under the spinal
    ///   one.
    /// - provides: the measurement every witness asserts on.
    /// - panics: when a run panics, or when a spinal result reads back as
    ///   another tree than the reference's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — deterministic closed builders have nondecreasing cost
    ///   over the two sizes. Each difference lies within one run budget; the
    ///   closed-rib and inner-binder witnesses require a two-to-one slope,
    ///   while the open-configuration witness requires equal slopes. These
    ///   distinguish swapped stances and sharing across different bindings
    ///   without replaying an effectful function pointer in a predicate.
    /// - witness: `full_laziness::full_laziness::a_spinal_duplicate_shares_every_rib`
    /// - witness: `full_laziness::full_laziness::a_spinal_duplicate_shares_what_full_laziness_copies`
    /// - witness: `full_laziness::full_laziness::an_open_configuration_is_evaluated_per_occurrence`
    #[spec(
        ensures: |ret| ret.0.0 <= u32::from(ample()) && ret.1.0 <= u32::from(ample())
    )]
    fn growth(built: Built) -> (Steps, Steps)
    {
        let mut grown = Vec::new();
        for stance in [DuplicationStance::EraseAndClone, DuplicationStance::Spinal] {
            let mut spent = Vec::new();
            for links in [FEWER, MORE] {
                let (steps, core, read) = run(stance, built, links);
                let (_, reference, expected) = run(DuplicationStance::EraseAndClone, built, links);
                assert_eq!(
                    Trees::Same,
                    same_tree(
                        &core,
                        Term::Computation(read),
                        &reference,
                        Term::Computation(expected)
                    ),
                    "{stance:?} at {links:?} reads back as the reference does"
                );
                spent.push(steps);
            }
            let [fewer, more] = spent[..]
            else {
                panic!("one run per size");
            };
            grown.push(Steps(
                more.0
                    .checked_sub(fewer.0)
                    .expect("a longer chain costs more"),
            ));
        }
        let [copied, spinal] = grown[..]
        else {
            panic!("one growth per stance");
        };
        (copied, spinal)
    }

    /// `share f = thunk (λ. (x ← R; return (x₁, x₀))) in
    /// (a ← force f ⟨⟩; b ← force f (⟨⟩, ⟨⟩); return (a, b))`, with `R` a
    /// closed chain of `links` binds: `R` reads nothing, so it is a rib.
    ///
    /// # Specification
    /// - requires: the requested links and surrounding nodes fit the id space.
    /// - ensures: the closed arity-two sharing computation described above.
    /// - panics: if a fixture mint is refused.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the link count fits the overlay id space. The result
    ///   validates as one arity-two share of a thunk with one lambda.
    ///   Independent result-tree equality and the exact cost slope distinguish
    ///   a misplaced rib, a wrong binder and copying where a configuration
    ///   should be shared.
    /// - witness: `full_laziness::full_laziness::a_spinal_duplicate_shares_every_rib`
    #[spec(
        ensures: |ret| {
            let Some(&CompNode::Shared(sharing)) = build.overlay.computation(ret) else { return false; };
            let OverlayId::Value(leg) = sharing.leg else { return false; };
            let Some(&ValueNode::Grafted(ValueGraft::Thunk(mut body))) = build.overlay.value(leg) else { return false; };
            for _ in 0_u32..1_u32 {
                let Some(&CompNode::Grafted(CompGraft::Lambda(inner))) = build.overlay.computation(body) else { return false; };
                body = inner;
            }
            sharing.arity == ShareArity::from(2_u32)
                && build.overlay.validate(OverlayId::Computation(ret)).is_ok()
        }
    )]
    fn closed_rib(
        build: &mut Build,
        links: Links,
    ) -> OverlayCompId
    {
        let produced = build.unit();
        let start = build.returning(produced);
        let rib = build.chain(start, links);
        let argument = build.variable(Index::One);
        let result = build.variable(Index::Zero);
        let paired = build.value(ValueGraft::Pair(argument, result));
        let returned = build.returning(paired);
        let body = build.bind(rib, returned);
        let lambda = build.computation(CompGraft::Lambda(body));
        let leg = build.value(ValueGraft::Thunk(lambda));

        let first_head = build.forced_occurrence(SharePosition::from(0_u32));
        let first_argument = build.unit();
        let first = build.apply(first_head, first_argument);
        let second_head = build.forced_occurrence(SharePosition::from(1_u32));
        let left_unit = build.unit();
        let right_unit = build.unit();
        let second_argument = build.value(ValueGraft::Pair(left_unit, right_unit));
        let second = build.apply(second_head, second_argument);
        let earlier = build.variable(Index::One);
        let later = build.variable(Index::Zero);
        let both = build.value(ValueGraft::Pair(earlier, later));
        let returned = build.returning(both);
        let rest = build.bind(second, returned);
        let applied = build.bind(first, rest);
        build.shared(OverlayId::Value(leg), applied)
    }

    /// `share f = thunk (λ. λ. (z ← T; return (x₂, z))) in
    /// (v ← return ⟨⟩; a ← force f ⟨⟩ v; b ← force f (⟨⟩, ⟨⟩) v;
    /// return (a, b))`, with `T` a chain of `links` binds over `return y`:
    /// `T` reads the inner binder and not the outer one, so it is a rib that
    /// full laziness could not float out of the inner lambda.
    ///
    /// # Specification
    /// - requires: the requested links and surrounding nodes fit the id space.
    /// - ensures: the closed arity-two sharing computation described above.
    /// - panics: if a fixture mint is refused.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the link count fits the overlay id space. The result
    ///   validates as one arity-two share of a thunk with two lambdas.
    ///   Independent result-tree equality and the exact cost slope distinguish
    ///   a misplaced rib, a wrong binder and copying where a configuration
    ///   should be shared.
    /// - witness: `full_laziness::full_laziness::a_spinal_duplicate_shares_what_full_laziness_copies`
    #[spec(
        ensures: |ret| {
            let Some(&CompNode::Shared(sharing)) = build.overlay.computation(ret) else { return false; };
            let OverlayId::Value(leg) = sharing.leg else { return false; };
            let Some(&ValueNode::Grafted(ValueGraft::Thunk(mut body))) = build.overlay.value(leg) else { return false; };
            for _ in 0_u32..2_u32 {
                let Some(&CompNode::Grafted(CompGraft::Lambda(inner))) = build.overlay.computation(body) else { return false; };
                body = inner;
            }
            sharing.arity == ShareArity::from(2_u32)
                && build.overlay.validate(OverlayId::Computation(ret)).is_ok()
        }
    )]
    fn inner_binder_rib(
        build: &mut Build,
        links: Links,
    ) -> OverlayCompId
    {
        let inner = build.variable(Index::Zero);
        let start = build.returning(inner);
        let rib = build.chain(start, links);
        let outer = build.variable(Index::Two);
        let result = build.variable(Index::Zero);
        let paired = build.value(ValueGraft::Pair(outer, result));
        let returned = build.returning(paired);
        let body = build.bind(rib, returned);
        let inner_lambda = build.computation(CompGraft::Lambda(body));
        let outer_lambda = build.computation(CompGraft::Lambda(inner_lambda));
        let leg = build.value(ValueGraft::Thunk(outer_lambda));

        let produced = build.unit();
        let once = build.returning(produced);
        let first_head = build.forced_occurrence(SharePosition::from(0_u32));
        let first_argument = build.unit();
        let first_partial = build.apply(first_head, first_argument);
        let first_bound = build.variable(Index::Zero);
        let first = build.apply(first_partial, first_bound);
        let second_head = build.forced_occurrence(SharePosition::from(1_u32));
        let left_unit = build.unit();
        let right_unit = build.unit();
        let second_argument = build.value(ValueGraft::Pair(left_unit, right_unit));
        let second_partial = build.apply(second_head, second_argument);
        let second_bound = build.variable(Index::One);
        let second = build.apply(second_partial, second_bound);
        let earlier = build.variable(Index::One);
        let later = build.variable(Index::Zero);
        let both = build.value(ValueGraft::Pair(earlier, later));
        let returned = build.returning(both);
        let rest = build.bind(second, returned);
        let applied = build.bind(first, rest);
        let sequenced = build.bind(once, applied);
        build.shared(OverlayId::Value(leg), sequenced)
    }

    /// `share t = T in (u ← return ⟨⟩; a ← t; w ← return (⟨⟩, ⟨⟩); b ← t;
    /// return (a, b))`, with `T` a chain of `links` binds over `return x₀`:
    /// each occurrence reads `x₀` where it stands, the first naming `u` and
    /// the second `w`.
    ///
    /// # Specification
    /// - requires: the requested links and surrounding nodes fit the id space.
    /// - ensures: the closed arity-two sharing computation described above.
    /// - panics: if a fixture mint is refused.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the link count fits the overlay id space. The result
    ///   validates as an arity-two share of a computation leg. Independent
    ///   result trees and equal cost slopes distinguish reusing one result
    ///   across the two different bindings from evaluating each occurrence.
    /// - witness: `full_laziness::full_laziness::an_open_configuration_is_evaluated_per_occurrence`
    #[spec(
        ensures: |ret| matches!(build.overlay.computation(ret), Some(CompNode::Shared(sharing))
            if sharing.arity == ShareArity::from(2_u32) && matches!(sharing.leg, OverlayId::Computation(_)))
            && build.overlay.validate(OverlayId::Computation(ret)).is_ok()
    )]
    fn open_leg(
        build: &mut Build,
        links: Links,
    ) -> OverlayCompId
    {
        let read = build.variable(Index::Zero);
        let start = build.returning(read);
        let leg = build.chain(start, links);

        let produced = build.unit();
        let first_binding = build.returning(produced);
        let first = build.computation_occurrence(SharePosition::from(0_u32));
        let left_unit = build.unit();
        let right_unit = build.unit();
        let pair = build.value(ValueGraft::Pair(left_unit, right_unit));
        let second_binding = build.returning(pair);
        let second = build.computation_occurrence(SharePosition::from(1_u32));
        let earlier = build.variable(Index::Two);
        let later = build.variable(Index::Zero);
        let both = build.value(ValueGraft::Pair(earlier, later));
        let returned = build.returning(both);
        let last = build.bind(second, returned);
        let rebound = build.bind(second_binding, last);
        let after_first = build.bind(first, rebound);
        let sequenced = build.bind(first_binding, after_first);
        build.shared(OverlayId::Computation(leg), sequenced)
    }

    #[test]
    fn a_spinal_duplicate_shares_every_rib()
    {
        let (copied, spinal) = growth(closed_rib);
        assert!(spinal.0 > 0, "the rib is evaluated at least once");
        assert_eq!(
            copied.0,
            spinal.0.checked_mul(2).expect("small"),
            "two applications evaluate the closed rib twice when copied and once when shared"
        );
    }

    #[test]
    fn a_spinal_duplicate_shares_what_full_laziness_copies()
    {
        let (copied, spinal) = growth(inner_binder_rib);
        assert!(spinal.0 > 0, "the rib is evaluated at least once");
        assert_eq!(
            copied.0,
            spinal.0.checked_mul(2).expect("small"),
            "a rib reading the inner binder, applied to one value at both copies, is \
             evaluated once"
        );
    }

    #[test]
    fn an_open_configuration_is_evaluated_per_occurrence()
    {
        let (copied, spinal) = growth(open_leg);
        assert!(spinal.0 > 0, "the leg is evaluated at least once");
        assert_eq!(
            copied, spinal,
            "a leg read under two different bindings is evaluated at both occurrences"
        );
    }
}
