//! Composition floor: replay boundaries, seam roles and presentation
//! sensitivity.

#[cfg(test)]
mod tests
{
    use anodized::spec;
    use gandr_theory_cell_complexes::Cell;
    use gandr_theory_cell_complexes::CellAlphabet as _;
    use gandr_theory_cell_complexes::CellId;
    use gandr_theory_cell_complexes::CellProvenance;
    use gandr_theory_cell_complexes::CellStore;
    use gandr_theory_cell_complexes::CellVariance;
    use gandr_theory_cell_complexes::CmdPat;
    use gandr_theory_cell_complexes::ConsPat;
    use gandr_theory_cell_complexes::Orientation;
    use gandr_theory_cell_complexes::Polarity;
    use gandr_theory_cell_complexes::ProdPat;
    use gandr_theory_cell_complexes::SeamRole;
    use gandr_theory_cell_complexes::SequentAlphabet;
    use gandr_theory_coherent_resolutions::Overlap;
    use gandr_theory_coherent_resolutions::OverlapKind;
    use gandr_theory_coherent_resolutions::ReplayPathOutcome;
    use gandr_theory_coherent_resolutions::Tracelet;
    use gandr_theory_coherent_resolutions::derive_fused;
    use gandr_theory_coherent_resolutions::enumerate_overlaps;
    use gandr_theory_coherent_resolutions::replay_equivalent;
    use gandr_theory_decomposition_spaces::compose_directed;
    use gandr_theory_decomposition_spaces::compose_invertible;
    use gandr_theory_dynamic_graphs::AcyclicityMaintenance;
    use gandr_theory_dynamic_graphs::EdgeVerdict;
    use gandr_theory_graphs::EdgeId;
    use gandr_theory_graphs::NodeId;

    /// No rule fires at the candidate peak.
    #[derive(Clone, Copy, Debug)]
    struct NoStep;
    /// Unwrap a fixture value whose presence the setup requires.
    ///
    /// # Specification
    /// trivial.
    fn present<Value, Reason>(value: Maybe<Value, Reason>) -> Value
    where
        Reason: core::fmt::Debug,
    {
        match value {
            | Maybe::Present(value) => value,
            | Maybe::Absent(reason) => panic!("fixture absent: {reason:?}"),
        }
    }

    extern crate alloc;
    use gandr_theory_decomposition_spaces::CompositionObstruction;
    use quenchant_shape::shape::Maybe;

    /// Fixture constructor name.
    #[repr(transparent)]
    #[derive(Clone, Copy)]
    struct ConstructorName<'fixture>(&'fixture str);

    /// Fixture fixture hole name.
    #[repr(transparent)]
    #[derive(Clone, Copy)]
    struct FixtureHoleName<'fixture>(&'fixture str);

    /// Fixture operation name.
    #[repr(transparent)]
    #[derive(Clone, Copy)]
    struct OperationName<'fixture>(&'fixture str);

    #[test]
    fn a_mixed_step_cell_is_classified_mixed()
    {
        let cell = mixed_step(
            FixtureHoleName("r"),
            OperationName("dn"),
            OperationName("up"),
        );
        let hole = cell
            .meta()
            .vars()
            .iter()
            .find(|v| v.var().hole().as_ref() == "r")
            .expect("r present");
        assert_eq!(
            CellVariance::Mixed,
            hole.variance(),
            "r spans a producer and a consumer position"
        );
    }

    #[test]
    fn invertible_composition_of_a_ground_chain_replays()
    {
        let (store, a, b) = ground_chain();
        assert_eq!(
            a.joins_at, b.overlap.peak,
            "the certificates share the seam ⟨C|★⟩"
        );
        let composite = compose_invertible(&a, &b);
        assert_eq!(
            composite.path_a.len(),
            a.path_a.len() + b.path_a.len(),
            "the composite grafts b's derivation onto a's"
        );
        assert!(
            bool::from(composite.replay(&store)),
            "the invertible composite replays A ~> C ~> E"
        );
    }

    #[test]
    fn directed_composition_of_a_ground_chain_replays()
    {
        let (store, a, b) = ground_chain();
        let composite =
            compose_directed(&a, &b, &store).expect("a ground (metavariable-free) seam is acyclic");
        assert!(
            bool::from(composite.replay(&store)),
            "the directed composite replays A ~> C ~> E"
        );
    }

    /// Construct the ground chain fixture.
    ///
    /// # Specification
    /// trivial.
    fn ground_chain() -> (CellStore, Tracelet, Tracelet)
    {
        let mut store = CellStore::new();
        let ab = store.insert(ground_step(ConstructorName("A"), ConstructorName("B")));
        let bc = store.insert(ground_step(ConstructorName("B"), ConstructorName("C")));
        let cd = store.insert(ground_step(ConstructorName("C"), ConstructorName("D")));
        let de = store.insert(ground_step(ConstructorName("D"), ConstructorName("E")));
        let first = fused(&mut store, ab, bc); // ⟨A|★⟩ ~> ⟨C|★⟩
        let second = fused(&mut store, cd, de); // ⟨C|★⟩ ~> ⟨E|★⟩
        (store, first, second)
    }

    /// Construct the ground step fixture.
    ///
    /// # Specification
    /// trivial.
    fn ground_step(
        from: ConstructorName<'_>,
        to: ConstructorName<'_>,
    ) -> Cell
    {
        Cell::new(
            CmdPat::cut(
                Polarity::Positive,
                ProdPat::ctor(from.0, []),
                ConsPat::top(),
            ),
            CmdPat::cut(Polarity::Positive, ProdPat::ctor(to.0, []), ConsPat::top()),
            Orientation::PolarityDerived,
            CellProvenance::SurfaceRule,
        )
    }

    #[test]
    fn directed_composition_declines_a_mixed_variance_cycle()
    {
        let mut store = CellStore::new();
        let u1 = store.insert(mixed_step(
            FixtureHoleName("r"),
            OperationName("dn1"),
            OperationName("mid1"),
        ));
        let v1 = store.insert(mixed_step(
            FixtureHoleName("s"),
            OperationName("mid1"),
            OperationName("up1"),
        ));
        let u2 = store.insert(mixed_step(
            FixtureHoleName("r"),
            OperationName("dn2"),
            OperationName("mid2"),
        ));
        let v2 = store.insert(mixed_step(
            FixtureHoleName("s"),
            OperationName("mid2"),
            OperationName("up2"),
        ));
        let a = fused(&mut store, u1, v1);
        let b = fused(&mut store, u2, v2);

        let obstruction = compose_directed(&a, &b, &store)
            .expect_err("a shared mixed-variance seam hole cycles the flow");

        let CompositionObstruction::Cycle { cycle } = obstruction
        else {
            panic!("expected a flow cycle")
        };
        assert!(
            cycle.len() >= 2,
            "a 2-cycle through distinct cells (never a self-loop), not empty"
        );
        let reachable: Vec<CellId> = participating(&a)
            .into_iter()
            .chain(participating(&b))
            .collect();
        let mut cycle_cells = Vec::new();
        for node in &cycle {
            let cell = node.0;
            let hole = &node.1;
            assert!(
                reachable.contains(&cell),
                "the cycle node names a cell the composition fires"
            );
            let meta = present(store.get(cell));
            let classified = meta
                .meta()
                .vars()
                .iter()
                .find(|v| v.var().hole() == hole.hole())
                .expect("the hole is one of the cell's metavariables");
            assert_eq!(
                CellVariance::Mixed,
                classified.variance(),
                "the cycling hole is mixed-variance in its cell"
            );
            if !cycle_cells.contains(&cell) {
                cycle_cells.push(cell);
            }
        }
        assert!(
            cycle_cells.len() >= 2,
            "the loop passes through the seam between two distinct cells"
        );
    }

    #[test]
    fn the_acyclicity_verdict_reads_the_recorded_cell_support_and_nothing_finer()
    {
        let (store, a, b) = mixed_pair();
        let baseline = compose_directed(&a, &b, &store);
        let mut reversed = a.clone();
        reversed.path_a.reverse();
        let mut repeated = a.clone();
        repeated.path_a.extend(a.path_a.iter().cloned());
        for (label, variant) in [("a reversed leg", &reversed), ("a repeated leg", &repeated)] {
            assert_eq!(
                cell_support(&a),
                cell_support(variant),
                "{label} records the same cells, which is the hypothesis"
            );
            assert_eq!(
                baseline.is_ok(),
                compose_directed(variant, &b, &store).is_ok(),
                "{label} is the same input to the gate, so the verdict cannot move"
            );
        }
        assert_ne!(
            participating(&a),
            participating(&reversed),
            "a reversed leg does reorder the cells the graph interns"
        );
    }

    #[test]
    fn the_acyclicity_verdict_is_not_invariant_under_certificate_identity()
    {
        let (mut store, fused_derivation) = mixed_certificate();
        let two_step = presentation(&fused_derivation, &fused_derivation.path_a);
        let single_step = presentation(&fused_derivation, &fused_derivation.path_b);
        assert!(
            bool::from(replay_equivalent(&two_step, &single_step, &store)),
            "the two presentations are ONE certificate: one boundary, both replay"
        );
        assert_ne!(
            cell_support(&two_step),
            cell_support(&single_step),
            "and they record different cells, which is what the identity forgets"
        );

        assert!(
            seam_hole_names(&single_step.joins_at)
                .iter()
                .all(|hole| endpoint_variances(
                    &participating(&single_step),
                    SeamHoleName(hole),
                    &store
                )
                .is_empty()),
            "the alpha-renamed presentation records no hole under a seam name"
        );
        assert!(
            variances(&two_step, &store).contains(&CellVariance::Mixed),
            "and the two-step presentation records one"
        );

        let onward = mixed_onward_certificate(&mut store, &fused_derivation);

        let declined = compose_directed(&two_step, &onward, &store).expect_err(
            "the two-step presentation records a mixed seam hole, which meets the partner's and \
             loops",
        );
        let CompositionObstruction::Cycle { cycle } = declined
        else {
            panic!("expected a flow cycle")
        };
        let recorded = participating(&two_step);
        assert!(
            cycle.iter().any(|node| recorded.contains(&node.0)),
            "the cycle runs through a cell only that presentation records"
        );
        let admitted = compose_directed(&single_step, &onward, &store)
            .expect("the fused presentation records no mixed seam hole, so nothing loops");
        assert!(
            bool::from(admitted.replay(&store)),
            "and the composite it admits is a real certificate — it replays"
        );
    }

    #[test]
    fn a_single_polarity_partner_hides_the_divergence_from_every_probe()
    {
        let (mut store, fused_derivation) = mixed_certificate();
        let two_step = presentation(&fused_derivation, &fused_derivation.path_a);
        let single_step = presentation(&fused_derivation, &fused_derivation.path_b);
        assert!(
            variances(&two_step, &store).contains(&CellVariance::Mixed),
            "the hypothesis: one presentation does record a mixed hole"
        );
        let onward = replayed_onward_partner(&mut store, &fused_derivation);
        for (label, presented) in [
            ("the two-step form", &two_step),
            ("the fused form", &single_step),
        ] {
            let admitted = compose_directed(presented, &onward, &store)
                .unwrap_or_else(|_| panic!("{label} composes: the partner closes no loop"));
            assert!(
                bool::from(admitted.replay(&store)),
                "{label} composite is a real certificate — it replays"
            );
        }
        assert_ne!(
            participating(&two_step),
            participating(&single_step),
            "even though the two presentations put different cells in front of the gate"
        );
    }

    #[test]
    fn the_composite_is_a_certificate_invariant_even_where_the_verdict_is_not()
    {
        let (mut store, fused_derivation) = split_certificate();
        let two_step = presentation(&fused_derivation, &fused_derivation.path_a);
        let single_step = presentation(&fused_derivation, &fused_derivation.path_b);
        assert!(
            bool::from(replay_equivalent(&two_step, &single_step, &store)),
            "the hypothesis: two presentations of ONE certificate"
        );
        assert_ne!(
            cell_support(&two_step),
            cell_support(&single_step),
            "recording different cells, or there is no presentation effect to be invariant under"
        );

        for (label, presented) in [("the two-step", &two_step), ("the fused", &single_step)] {
            let holes = variances(presented, &store);
            assert!(
                !holes.is_empty(),
                "{label} presentation records a metavariable seam, not a ground one"
            );
            assert!(
                holes
                    .iter()
                    .all(|variance| *variance != CellVariance::Mixed),
                "{label} presentation records no mixed hole, so its flow runs one way"
            );
        }

        let onward = replayed_onward_partner(&mut store, &fused_derivation);
        let from_two_step = compose_directed(&two_step, &onward, &store)
            .expect("the two-step presentation records no mixed seam hole, so nothing loops");
        let from_single_step = compose_directed(&single_step, &onward, &store)
            .expect("and neither does the fused presentation");
        assert!(
            bool::from(from_two_step.replay(&store)) && bool::from(from_single_step.replay(&store)),
            "each admitted composite is a real certificate — it replays"
        );
        assert!(
            bool::from(replay_equivalent(&from_two_step, &from_single_step, &store)),
            "and the two composites are ONE certificate: the composite is an invariant"
        );
        assert_ne!(
            from_two_step.path_a, from_single_step.path_a,
            "while the recorded derivations still differ, which is what makes that a claim"
        );
    }

    #[test]
    fn invertible_composition_is_well_defined_on_the_replay_quotient()
    {
        let (mut store, fused_derivation) = mixed_certificate();
        let two_step = presentation(&fused_derivation, &fused_derivation.path_a);
        let single_step = presentation(&fused_derivation, &fused_derivation.path_b);
        assert!(
            bool::from(replay_equivalent(&two_step, &single_step, &store)),
            "the hypothesis: two presentations of one certificate"
        );
        let onward = replayed_onward_partner(&mut store, &fused_derivation);
        let from_two_step = compose_invertible(&two_step, &onward);
        let from_single_step = compose_invertible(&single_step, &onward);
        assert!(
            bool::from(from_two_step.replay(&store)) && bool::from(from_single_step.replay(&store)),
            "the graft of two replaying certificates replays, on either presentation"
        );
        assert!(
            bool::from(replay_equivalent(&from_two_step, &from_single_step, &store)),
            "and the two composites are one certificate — the lane descends to the quotient"
        );
        assert_ne!(
            from_two_step.path_a, from_single_step.path_a,
            "while the recorded derivations still differ, which is the point of the quotient"
        );
    }

    #[test]
    fn the_refined_seam_criterion_declines_strictly_less_than_the_union_reading()
    {
        let (store, corpus) = certificate_corpus();
        assert!(
            corpus.len() >= 4,
            "the corpus carries several real certificates, not one probe"
        );
        let mut pairs = 0_usize;
        let mut union_declines = 0_usize;
        let mut shipped_declines = 0_usize;
        let mut recovered = 0_usize;
        let mut composable = 0_usize;
        for left in &corpus {
            for right in &corpus {
                pairs = pairs.saturating_add(1);
                let union = union_reading(left, right, &store).0;
                if union {
                    union_declines = union_declines.saturating_add(1);
                }
                match compose_directed(left, right, &store) {
                    | Err(_) => {
                        shipped_declines = shipped_declines.saturating_add(1);
                        assert!(
                            union,
                            "the refinement only ever admits more: a shipped decline is a \
                             decline under the superseded reading too"
                        );
                    },
                    | Ok(_) => {
                        if union {
                            recovered = recovered.saturating_add(1);
                        }
                    },
                }
            }
        }
        assert_eq!(
            union_declines.saturating_sub(shipped_declines),
            recovered,
            "the over-decline is exactly the recovered set, since the refinement is monotone"
        );
        assert!(
            recovered > 0,
            "some ordinary sequential seams are recovered"
        );
        assert!(
            shipped_declines > 0,
            "while the gate is refined rather than removed — it still declines \
             {shipped_declines} of {pairs}"
        );

        for left in &corpus {
            let Maybe::Present(partner) =
                one_step_certificate(&store, &left.overlap, &left.joins_at)
            else {
                continue;
            };
            composable = composable.saturating_add(1);
            match compose_directed(left, &partner, &store) {
                | Err(_) => assert!(
                    union_reading(left, &partner, &store).0,
                    "a shipped decline is a decline under the superseded reading too"
                ),
                | Ok(composite) => assert!(
                    bool::from(composite.replay(&store)),
                    "a composable pair the gate admits composes into a certificate that replays"
                ),
            }
        }
        assert!(
            composable > 0,
            "the composable half ran: {composable} certificates carry a further step at their \
             own join"
        );
    }

    #[test]
    fn the_ordinary_sequential_seam_is_what_the_union_reading_declined()
    {
        let (store, left, right) = variance_pair(SeamHoleMixed(false), SeamHoleMixed(false));
        assert!(
            union_reading(&left, &right, &store).0,
            "the superseded reading declines the ordinary sequential seam"
        );
        let composite = compose_directed(&left, &right, &store)
            .expect("the shipped criterion admits it: no endpoint both emits and absorbs");
        assert!(
            bool::from(composite.replay(&store)),
            "and the composition it admits replays"
        );
    }

    #[test]
    fn the_seam_edge_is_drawn_exactly_when_the_left_emits_and_the_right_absorbs()
    {
        for &(label, left_mixed, right_mixed, declines) in &[
            ("producer left, consumer right", false, false, false),
            ("mixed left, consumer right", true, false, false),
            ("producer left, mixed right", false, true, false),
            ("mixed on both sides", true, true, true),
        ] {
            let (store, a, b) =
                variance_pair(SeamHoleMixed(left_mixed), SeamHoleMixed(right_mixed));
            match compose_directed(&a, &b, &store) {
                | Err(
                    CompositionObstruction::Graph { .. }
                    | CompositionObstruction::NodeCapacityExceeded,
                ) => panic!("fixture graph must be representable"),
                | Err(CompositionObstruction::Cycle { cycle }) => {
                    assert!(
                        declines,
                        "{label}: a loop needs a side that emits and absorbs at each end"
                    );
                    assert!(
                        cycle.len() >= 2,
                        "{label}: the decline carries the closed walk, not an empty cycle"
                    );
                },
                | Ok(composite) => {
                    assert!(
                        !declines,
                        "{label}: both sides emit and absorb, so the flow closes a loop"
                    );
                    assert!(
                        bool::from(composite.replay(&store)),
                        "{label}: the admitted composite replays"
                    );
                },
            }
        }
    }

    /// Fixture seam hole mixed.
    #[repr(transparent)]
    #[derive(Clone, Copy)]
    struct SeamHoleMixed(bool);

    /// Construct the variance pair fixture.
    ///
    /// # Specification
    /// trivial.
    fn variance_pair(
        left_mixed: SeamHoleMixed,
        right_mixed: SeamHoleMixed,
    ) -> (CellStore, Tracelet, Tracelet)
    {
        let mut store = CellStore::new();
        let left_cell = store.insert(if left_mixed.0 {
            mixed_step(
                FixtureHoleName("s"),
                OperationName("in0"),
                OperationName("mid0"),
            )
        }
        else {
            split_step(
                FixtureHoleName("s"),
                FixtureHoleName("t"),
                OperationName("in0"),
                OperationName("mid0"),
            )
        });
        let right_cell = store.insert(if right_mixed.0 {
            mixed_step(
                FixtureHoleName("s"),
                OperationName("mid0"),
                OperationName("out0"),
            )
        }
        else {
            Cell::new(
                CmdPat::cut(
                    Polarity::Positive,
                    ProdPat::meta("u"),
                    ConsPat::op("mid0", [], ConsPat::meta("s")),
                ),
                CmdPat::cut(
                    Polarity::Positive,
                    ProdPat::meta("u"),
                    ConsPat::op("out0", [], ConsPat::meta("s")),
                ),
                Orientation::PolarityDerived,
                CellProvenance::SurfaceRule,
            )
        });
        let template = composition_overlap(&store, left_cell, right_cell);
        let peak = CmdPat::cut(
            Polarity::Positive,
            ProdPat::meta("s"),
            ConsPat::op("in0", [], ConsPat::meta("t")),
        );
        let left = present(one_step_certificate(&store, &template, &peak));
        assert_eq!(
            alloc::vec![left_cell],
            participating(&left),
            "the left certificate records the left cell and nothing else"
        );
        let right = present(one_step_certificate(&store, &template, &left.joins_at));
        assert_eq!(
            alloc::vec![right_cell],
            participating(&right),
            "the right certificate records the right cell and nothing else"
        );
        (store, left, right)
    }

    /// Construct the one step certificate fixture.
    ///
    /// # Specification
    /// trivial.
    fn one_step_certificate(
        store: &CellStore,
        template: &Overlap,
        peak: &CmdPat,
    ) -> Maybe<Tracelet, NoStep>
    {
        let stepped = gandr_theory_coherent_resolutions::normalize(store, peak, 1_usize.into());
        let Some(step) = stepped.path.first()
        else {
            return Maybe::Absent(NoStep);
        };
        let step = step.clone();
        let mut overlap = template.clone();
        overlap.peak = peak.clone();
        Maybe::Present(Tracelet {
            overlap,
            path_a: alloc::vec![step.clone()],
            path_b: alloc::vec![step],
            joins_at: stepped.normal,
        })
    }

    /// Construct the certificate corpus fixture.
    ///
    /// # Specification
    /// trivial.
    fn certificate_corpus() -> (CellStore, alloc::vec::Vec<Tracelet>)
    {
        use gandr_theory_levitation::Attrs;
        use gandr_theory_levitation::BridgeArity;
        use gandr_theory_levitation::Code;
        use gandr_theory_levitation::CtorDesc;
        use gandr_theory_levitation::DeclPolarity;
        use gandr_theory_levitation::FreeTerm;
        use gandr_theory_levitation::NominalId;
        use gandr_theory_levitation::OperDesc;
        use gandr_theory_levitation::RuleFace;
        use gandr_theory_levitation::SignDesc;
        use gandr_theory_levitation::SortRef;
        use gandr_theory_levitation::SurfaceSpan;

        let nat_op = |name: &str, inputs: alloc::vec::Vec<SortRef>| {
            OperDesc::new(
                name,
                BridgeArity::single_output(inputs, SortRef::new("out", "Nat")),
                Attrs::empty(),
            )
        };
        let face = |lhs: FreeTerm, rhs: FreeTerm| {
            RuleFace::new(
                lhs,
                rhs,
                alloc::vec::Vec::new(),
                SurfaceSpan::new(0_usize.into(), 0_usize.into()),
            )
        };
        let desc: SignDesc<()> = SignDesc::new(
            NominalId::new(0_u64.into(), "Nat"),
            alloc::vec::Vec::new(),
            [
                CtorDesc::new("Zero", Code::unit(), "Nat", Attrs::empty()),
                CtorDesc::new("Succ", Code::var("Nat"), "Nat", Attrs::empty()),
            ],
            [
                nat_op("add", alloc::vec![
                    SortRef::new("m", "Nat"),
                    SortRef::new("n", "Nat")
                ]),
                nat_op("double", alloc::vec![SortRef::new("m", "Nat")]),
            ],
            [
                face(
                    FreeTerm::op("add", [FreeTerm::ctor("Zero", []), FreeTerm::var("n")]),
                    FreeTerm::var("n"),
                ),
                face(
                    FreeTerm::op("add", [
                        FreeTerm::ctor("Succ", [FreeTerm::var("m")]),
                        FreeTerm::var("n"),
                    ]),
                    FreeTerm::ctor("Succ", [FreeTerm::op("add", [
                        FreeTerm::var("m"),
                        FreeTerm::var("n"),
                    ])]),
                ),
                face(
                    FreeTerm::op("double", [FreeTerm::ctor("Zero", [])]),
                    FreeTerm::ctor("Zero", []),
                ),
                face(
                    FreeTerm::op("double", [FreeTerm::ctor("Succ", [FreeTerm::var("m")])]),
                    FreeTerm::ctor("Succ", [FreeTerm::ctor("Succ", [FreeTerm::op(
                        "double",
                        [FreeTerm::var("m")],
                    )])]),
                ),
            ],
            DeclPolarity::Data,
            Attrs::empty(),
        );
        let elaborated = gandr_theory_computads::elaborate_data_desc(&desc);
        assert!(
            elaborated.declined_faces.is_empty() && elaborated.declined_opers.is_empty(),
            "the corpus description elaborates whole, so the measurement runs over real rules"
        );
        let mut store = elaborated.store;
        let mixed_left = store.insert(mixed_step(
            FixtureHoleName("r"),
            OperationName("dn1"),
            OperationName("mid1"),
        ));
        let mixed_right = store.insert(mixed_step(
            FixtureHoleName("s"),
            OperationName("mid1"),
            OperationName("up1"),
        ));
        let split_left = store.insert(split_step(
            FixtureHoleName("p"),
            FixtureHoleName("c"),
            OperationName("dn2"),
            OperationName("mid2"),
        ));
        let split_right = store.insert(split_step(
            FixtureHoleName("q"),
            FixtureHoleName("d"),
            OperationName("mid2"),
            OperationName("up2"),
        ));
        let sequential_left = store.insert(split_step(
            FixtureHoleName("r"),
            FixtureHoleName("c"),
            OperationName("dn3"),
            OperationName("mid3"),
        ));
        let sequential_right = store.insert(split_step(
            FixtureHoleName("p"),
            FixtureHoleName("r"),
            OperationName("mid3"),
            OperationName("up3"),
        ));
        let mut corpus = alloc::vec::Vec::new();
        corpus.push(fused(&mut store, sequential_left, sequential_right));
        corpus.push(fused(&mut store, mixed_left, mixed_right));
        corpus.push(fused(&mut store, split_left, split_right));
        let overlaps: alloc::vec::Vec<Overlap> = enumerate_overlaps(&store)
            .into_iter()
            .filter(|candidate| candidate.kind == OverlapKind::Composition)
            .collect();
        for overlap in overlaps {
            if let Ok((_, certificate)) = derive_fused(&overlap, &mut store) {
                corpus.push(certificate);
            }
        }
        (store, corpus)
    }

    #[test]
    fn a_recorded_cell_the_store_does_not_hold_contributes_no_endpoint()
    {
        let (store, left, right) = variance_pair(SeamHoleMixed(true), SeamHoleMixed(true));
        compose_directed(&left, &right, &store)
            .expect_err("the mixed pair declines against the store that holds its cells");

        let empty = CellStore::new();
        let composite = compose_directed(&left, &right, &empty)
            .expect("no endpoint resolves, so no edge is drawn and the seam is acyclic");
        assert_eq!(
            left.overlap.peak, composite.overlap.peak,
            "and the graft is still the sequential one"
        );
    }

    /// Classify the coarser union-of-roles criterion.
    ///
    /// # Specification
    /// - ensures: the result follows the named metadata projection.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 seam-role boundaries and replay witnesses separate
    ///   omitted flow edges, changed boundaries and lost certificate steps.
    /// - witness: `composition::tests::the_refined_seam_criterion_declines_strictly_less_than_the_union_reading`
    #[spec(ensures: |ret| ret.0 == seam_hole_names(&a.joins_at).iter().any(|hole| { let left = endpoint_variances(&participating(a), SeamHoleName(hole), store); let right = endpoint_variances(&participating(b), SeamHoleName(hole), store); !left.is_empty() && !right.is_empty() && left.iter().chain(&right).any(|v| matches!(v, CellVariance::Producer | CellVariance::Mixed)) && left.iter().chain(&right).any(|v| matches!(v, CellVariance::Consumer | CellVariance::Mixed)) }))]
    fn union_reading(
        a: &Tracelet,
        b: &Tracelet,
        store: &CellStore,
    ) -> UnionReadingDecline
    {
        let a_cells = participating(a);
        let b_cells = participating(b);
        for hole in seam_hole_names(&a.joins_at) {
            let a_side = endpoint_variances(&a_cells, SeamHoleName(&hole), store);
            let b_side = endpoint_variances(&b_cells, SeamHoleName(&hole), store);
            if a_side.is_empty() || b_side.is_empty() {
                continue;
            }
            let forward = a_side
                .iter()
                .chain(&b_side)
                .any(|variance| matches!(*variance, CellVariance::Producer | CellVariance::Mixed));
            let backward = a_side
                .iter()
                .chain(&b_side)
                .any(|variance| matches!(*variance, CellVariance::Consumer | CellVariance::Mixed));
            if forward && backward {
                return UnionReadingDecline(true);
            }
        }
        UnionReadingDecline(false)
    }

    /// Fixture union reading decline.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct UnionReadingDecline(bool);

    /// Collect the distinct names in a fixture seam.
    ///
    /// # Specification
    /// - ensures: the result follows the named metadata projection.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 seam-role boundaries and replay witnesses separate
    ///   omitted flow edges, changed boundaries and lost certificate steps.
    /// - witness: `composition::tests::the_refined_seam_criterion_declines_strictly_less_than_the_union_reading`
    #[spec(ensures: |ret| ret.iter().all(|name| SequentAlphabet::metavariables(cmd).iter().any(|var| var.hole().as_ref() == name)))]
    fn seam_hole_names(cmd: &CmdPat) -> alloc::vec::Vec<alloc::string::String>
    {
        let occurrences = SequentAlphabet::metavariables(cmd);
        let mut names: alloc::vec::Vec<alloc::string::String> = alloc::vec::Vec::new();
        for var in occurrences {
            if !names
                .iter()
                .any(|held| held.as_str() == var.hole().as_ref())
            {
                names.push(alloc::string::String::from(var.hole().as_ref()));
            }
        }
        names
    }

    /// Fixture seam hole name.
    #[repr(transparent)]
    #[derive(Clone, Copy)]
    struct SeamHoleName<'fixture>(&'fixture str);

    /// Read variances of live cells at a named hole.
    ///
    /// # Specification
    /// - ensures: the result follows the named metadata projection.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 seam-role boundaries and replay witnesses separate
    ///   omitted flow edges, changed boundaries and lost certificate steps.
    /// - witness: `composition::tests::the_refined_seam_criterion_declines_strictly_less_than_the_union_reading`
    #[spec(ensures: |ret| ret.iter().all(|variance| cells.iter().any(|cell| matches!(store.get(*cell), Maybe::Present(entry) if entry.meta().vars().iter().any(|v| v.var().hole().as_ref() == hole.0 && v.variance() == *variance)))))]
    fn endpoint_variances(
        cells: &[CellId],
        hole: SeamHoleName<'_>,
        store: &CellStore,
    ) -> alloc::vec::Vec<CellVariance>
    {
        let mut out = alloc::vec::Vec::new();
        for &cell in cells {
            let Maybe::Present(entry) = store.get(cell)
            else {
                continue;
            };
            for var in entry.meta().vars() {
                if var.var().hole().as_ref() == hole.0 {
                    out.push(var.variance());
                }
            }
        }
        out
    }

    /// Read all metadata variances of recorded cells.
    ///
    /// # Specification
    /// - ensures: the result follows the named metadata projection.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 seam-role boundaries and replay witnesses separate
    ///   omitted flow edges, changed boundaries and lost certificate steps.
    /// - witness: `composition::tests::the_refined_seam_criterion_declines_strictly_less_than_the_union_reading`
    #[spec(ensures: |ret| ret.iter().all(|variance| participating(tracelet).iter().any(|cell| matches!(store.get(*cell), Maybe::Present(entry) if entry.meta().vars().iter().any(|v| v.variance() == *variance)))))]
    fn variances(
        tracelet: &Tracelet,
        store: &CellStore,
    ) -> alloc::vec::Vec<CellVariance>
    {
        let mut out = alloc::vec::Vec::new();
        for cell in participating(tracelet) {
            let Maybe::Present(entry) = store.get(cell)
            else {
                continue;
            };
            out.extend(
                entry
                    .meta()
                    .vars()
                    .iter()
                    .map(gandr_theory_cell_complexes::CellVarMeta::variance),
            );
        }
        out
    }

    /// Sort and deduplicate recorded cell support.
    ///
    /// # Specification
    /// - ensures: the result follows the named metadata projection.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 seam-role boundaries and replay witnesses separate
    ///   omitted flow edges, changed boundaries and lost certificate steps.
    /// - witness: `composition::tests::the_refined_seam_criterion_declines_strictly_less_than_the_union_reading`
    #[spec(ensures: |ret| ret.windows(2).all(|pair| matches!(pair, [a, b] if a < b)) && tracelet.path_a.iter().chain(&tracelet.path_b).all(|step| ret.contains(&step.cell)))]
    fn cell_support(tracelet: &Tracelet) -> alloc::vec::Vec<CellId>
    {
        let mut cells = participating(tracelet);
        cells.sort_unstable();
        cells
    }

    /// Construct the mixed pair fixture.
    ///
    /// # Specification
    /// trivial.
    fn mixed_pair() -> (CellStore, Tracelet, Tracelet)
    {
        let mut store = CellStore::new();
        let u1 = store.insert(mixed_step(
            FixtureHoleName("r"),
            OperationName("dn1"),
            OperationName("mid1"),
        ));
        let v1 = store.insert(mixed_step(
            FixtureHoleName("s"),
            OperationName("mid1"),
            OperationName("up1"),
        ));
        let u2 = store.insert(mixed_step(
            FixtureHoleName("r"),
            OperationName("dn2"),
            OperationName("mid2"),
        ));
        let v2 = store.insert(mixed_step(
            FixtureHoleName("s"),
            OperationName("mid2"),
            OperationName("up2"),
        ));
        let a = fused(&mut store, u1, v1);
        let b = fused(&mut store, u2, v2);
        (store, a, b)
    }

    /// Construct the mixed certificate fixture.
    ///
    /// # Specification
    /// trivial.
    fn mixed_certificate() -> (CellStore, Tracelet)
    {
        let mut store = CellStore::new();
        let u1 = store.insert(mixed_step(
            FixtureHoleName("r"),
            OperationName("dn1"),
            OperationName("mid1"),
        ));
        let v1 = store.insert(mixed_step(
            FixtureHoleName("s"),
            OperationName("mid1"),
            OperationName("up1"),
        ));
        let mut a = fused(&mut store, u1, v1);
        let renamed = store.insert(mixed_step(
            FixtureHoleName("fresh"),
            OperationName("dn1"),
            OperationName("up1"),
        ));
        a.path_b = alloc::vec![gandr_theory_coherent_resolutions::CellApp {
            cell: renamed,
            at: gandr_theory_cell_complexes::Pos::root()
        }];
        (store, a)
    }

    /// Construct the replayed onward partner fixture.
    ///
    /// # Specification
    /// trivial.
    fn replayed_onward_partner(
        store: &mut CellStore,
        certificate: &Tracelet,
    ) -> Tracelet
    {
        let cell = store.insert(split_step(
            FixtureHoleName("s"),
            FixtureHoleName("s'"),
            OperationName("up1"),
            OperationName("up3"),
        ));
        let mut overlap = certificate.overlap.clone();
        overlap.peak = certificate.joins_at.clone();
        let step = gandr_theory_coherent_resolutions::CellApp {
            cell,
            at: gandr_theory_cell_complexes::Pos::root(),
        };
        let provisional = Tracelet {
            overlap,
            path_a: alloc::vec![step.clone()],
            path_b: alloc::vec![step],
            joins_at: certificate.joins_at.clone(),
        };
        let ReplayPathOutcome::Reached(reached) = provisional.replay_trace(store).path_a.outcome
        else {
            panic!("the partner's single step applies at the certificate's join")
        };
        Tracelet {
            joins_at: reached,
            ..provisional
        }
    }

    /// Construct the split certificate fixture.
    ///
    /// # Specification
    /// trivial.
    fn split_certificate() -> (CellStore, Tracelet)
    {
        let mut store = CellStore::new();
        let u1 = store.insert(split_step(
            FixtureHoleName("p"),
            FixtureHoleName("c"),
            OperationName("dn1"),
            OperationName("mid1"),
        ));
        let v1 = store.insert(split_step(
            FixtureHoleName("q"),
            FixtureHoleName("d"),
            OperationName("mid1"),
            OperationName("up1"),
        ));
        let a = fused(&mut store, u1, v1);
        (store, a)
    }

    /// Construct the presentation fixture.
    ///
    /// # Specification
    /// trivial.
    fn presentation(
        certificate: &Tracelet,
        leg: &[gandr_theory_coherent_resolutions::CellApp],
    ) -> Tracelet
    {
        Tracelet {
            overlap: certificate.overlap.clone(),
            path_a: leg.to_vec(),
            path_b: leg.to_vec(),
            joins_at: certificate.joins_at.clone(),
        }
    }

    /// Construct the mixed onward certificate fixture.
    ///
    /// # Specification
    /// trivial.
    fn mixed_onward_certificate(
        store: &mut CellStore,
        certificate: &Tracelet,
    ) -> Tracelet
    {
        let hole = certificate
            .joins_at
            .metavars()
            .next()
            .expect("mixed seam has a hole")
            .hole();
        store.insert(mixed_step(
            FixtureHoleName(hole.as_ref()),
            OperationName("up1"),
            OperationName("up3"),
        ));
        present(one_step_certificate(
            store,
            &certificate.overlap,
            &certificate.joins_at,
        ))
    }

    /// Construct the split step fixture.
    ///
    /// # Specification
    /// trivial.
    fn split_step(
        producer: FixtureHoleName<'_>,
        consumer: FixtureHoleName<'_>,
        in_op: OperationName<'_>,
        out_op: OperationName<'_>,
    ) -> Cell
    {
        Cell::new(
            CmdPat::cut(
                Polarity::Positive,
                ProdPat::meta(producer.0),
                ConsPat::op(in_op.0, [], ConsPat::meta(consumer.0)),
            ),
            CmdPat::cut(
                Polarity::Positive,
                ProdPat::meta(producer.0),
                ConsPat::op(out_op.0, [], ConsPat::meta(consumer.0)),
            ),
            Orientation::PolarityDerived,
            CellProvenance::SurfaceRule,
        )
    }

    /// Construct the mixed step fixture.
    ///
    /// # Specification
    /// trivial.
    fn mixed_step(
        hole: FixtureHoleName<'_>,
        in_op: OperationName<'_>,
        out_op: OperationName<'_>,
    ) -> Cell
    {
        Cell::new(
            CmdPat::cut(
                Polarity::Positive,
                ProdPat::meta(hole.0),
                ConsPat::op(in_op.0, [], ConsPat::meta(hole.0)),
            ),
            CmdPat::cut(
                Polarity::Positive,
                ProdPat::meta(hole.0),
                ConsPat::op(out_op.0, [], ConsPat::meta(hole.0)),
            ),
            Orientation::PolarityDerived,
            CellProvenance::SurfaceRule,
        )
    }

    /// Construct the fused fixture.
    ///
    /// # Specification
    /// trivial.
    fn fused(
        store: &mut CellStore,
        left: CellId,
        right: CellId,
    ) -> Tracelet
    {
        let overlap = composition_overlap(store, left, right);
        derive_fused(&overlap, store)
            .expect("the fused cell is derived")
            .1
    }

    /// Construct the composition overlap fixture.
    ///
    /// # Specification
    /// trivial.
    fn composition_overlap(
        store: &CellStore,
        left: CellId,
        right: CellId,
    ) -> Overlap
    {
        enumerate_overlaps(store)
            .into_iter()
            .find(|candidate| {
                candidate.kind == OverlapKind::Composition
                    && candidate.left == left
                    && candidate.right == right
            })
            .expect("the composition overlap exists")
    }

    /// Collect recorded cells without multiplicity.
    ///
    /// # Specification
    /// - ensures: the result follows the named metadata projection.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 seam-role boundaries and replay witnesses separate
    ///   omitted flow edges, changed boundaries and lost certificate steps.
    /// - witness: `composition::tests::the_refined_seam_criterion_declines_strictly_less_than_the_union_reading`
    #[spec(ensures: |ret| tracelet.path_a.iter().chain(&tracelet.path_b).all(|step| ret.iter().filter(|cell| **cell == step.cell).count() == 1))]
    fn participating(tracelet: &Tracelet) -> Vec<CellId>
    {
        let mut cells = Vec::new();
        for step in tracelet.path_a.iter().chain(&tracelet.path_b) {
            if !cells.contains(&step.cell) {
                cells.push(step.cell);
            }
        }
        cells
    }

    /// Reversing one pair changes which recorded join supplies the seam holes.
    #[test]
    fn the_criterion_reads_the_seam_holes_of_the_left_certificates_recorded_join()
    {
        let (store, mut left, right) = mixed_pair();
        // The gate consumes recorded support, independently of replay validation.
        left.joins_at = CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Ground", []),
            ConsPat::top(),
        );
        assert!(compose_directed(&left, &right, &store).is_ok());
        assert!(matches!(
            compose_directed(&right, &left, &store),
            Err(CompositionObstruction::Cycle { .. })
        ));
    }

    #[test]
    fn fanout_family_is_a_multi_sum_not_a_single_rule()
    {
        let mut store: CellStore = CellStore::new();
        let left = store.insert(Cell::new(
            CmdPat::cut(
                Polarity::Positive,
                ProdPat::meta("n"),
                ConsPat::op("plus", [], ConsPat::meta("alpha")),
            ),
            CmdPat::cut(
                Polarity::Positive,
                ProdPat::meta("n"),
                ConsPat::op("g", [], ConsPat::meta("alpha")),
            ),
            Orientation::PolarityDerived,
            CellProvenance::SurfaceRule,
        ));
        let linear_consumer = store.insert(Cell::new(
            CmdPat::cut(
                Polarity::Positive,
                ProdPat::meta("x"),
                ConsPat::op("g", [], ConsPat::meta("alpha")),
            ),
            CmdPat::cut(
                Polarity::Positive,
                ProdPat::meta("x"),
                ConsPat::meta("alpha"),
            ),
            Orientation::PolarityDerived,
            CellProvenance::SurfaceRule,
        ));
        let nonlinear_consumer = store.insert(Cell::new(
            CmdPat::cut(
                Polarity::Positive,
                ProdPat::ctor("Pair", [ProdPat::meta("y"), ProdPat::meta("y")]),
                ConsPat::op("g", [], ConsPat::meta("alpha")),
            ),
            CmdPat::cut(
                Polarity::Positive,
                ProdPat::meta("y"),
                ConsPat::meta("alpha"),
            ),
            Orientation::PolarityDerived,
            CellProvenance::SurfaceRule,
        ));

        let y = present(store.get(nonlinear_consumer))
            .meta()
            .vars()
            .iter()
            .find(|v| v.var().hole().as_ref() == "y")
            .expect("y present");
        assert!(
            !bool::from(y.linear()),
            "Pair(y; y) duplicates y, so y is non-linear"
        );

        let family: Vec<Overlap> = enumerate_overlaps(&store)
            .into_iter()
            .filter(|candidate| {
                candidate.kind == OverlapKind::Composition && candidate.left == left
            })
            .collect();
        assert!(
            family.len() >= 2,
            "the g-seam composition fans out to a family (multi-sum), not one rule"
        );
        let mut fused_rules = Vec::new();
        for overlap in &family {
            let composite = overlap.composite(&store).expect("the composite exists");
            if !fused_rules.contains(&composite) {
                fused_rules.push(composite);
            }
        }
        assert!(
            fused_rules.len() >= 2,
            "the family yields distinct fused right-hand sides, never a single rule"
        );
        let _ = (linear_consumer, nonlinear_consumer);
    }
    /// The sequent alphabet's hole identity, which is what a flow-graph node is
    /// keyed by.
    type SeamHole = <SequentAlphabet as gandr_theory_cell_complexes::CellAlphabet>::Hole;

    /// The sequent alphabet's metavariable, which a flow-graph node records.
    type SeamVar = <SequentAlphabet as gandr_theory_cell_complexes::CellAlphabet>::Var;

    /// The endpoints of `hole` among `cells`, read from each present cell's
    /// live metadata.
    ///
    /// # Specification
    /// - ensures: Returns only live metadata endpoints on the requested seam
    ///   hole.
    /// - fails: typed capacity, arithmetic or state errors described below.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 differential streams and L3 boundaries distinguish
    ///   wrong verdicts, lost edges and invalid maintained state on finite
    ///   graphs.
    /// - witness: `composition::tests::the_gates_own_graph_streamed_incrementally_reproduces_its_verdict`

    #[spec(ensures: |ret| ret.iter().all(|&(cell, ref var, _)| cells.contains(&cell) && SequentAlphabet::hole_of(var) == *hole))]
    fn seam_endpoints(
        cells: &[CellId],
        hole: &SeamHole,
        store: &CellStore,
    ) -> Vec<(CellId, SeamVar, SeamRole)>
    {
        let mut endpoints = Vec::new();
        for &cell in cells {
            let Maybe::Present(entry) = store.get(cell)
            else {
                continue;
            };
            for (var, role) in SequentAlphabet::hole_flow(entry.meta(), hole) {
                endpoints.push((cell, var, role));
            }
        }
        endpoints
    }

    /// The dense identity of the `(cell, hole)` node, allocating one on first
    /// sight.
    ///
    /// # Specification
    /// - ensures: Interns each cell-and-hole pair exactly once.
    /// - fails: typed capacity, arithmetic or state errors described below.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 differential streams and L3 boundaries distinguish
    ///   wrong verdicts, lost edges and invalid maintained state on finite
    ///   graphs.
    /// - witness: `composition::tests::the_gates_own_graph_streamed_incrementally_reproduces_its_verdict`

    #[spec(ensures: |ret| usize::try_from(u32::from(ret)).is_ok_and(|index| nodes.get(index) == Some(&(cell, SequentAlphabet::hole_of(var)))))]
    fn intern_node(
        nodes: &mut Vec<(CellId, SeamHole)>,
        cell: CellId,
        var: &SeamVar,
    ) -> NodeId
    {
        let key = (cell, SequentAlphabet::hole_of(var));
        if let Some(index) = nodes.iter().position(|entry| *entry == key) {
            return NodeId::from(u32::try_from(index).expect("a fixture graph is small"));
        }
        let index = nodes.len();
        nodes.push(key);
        NodeId::from(u32::try_from(index).expect("a fixture graph is small"))
    }

    /// Appends `edge` unless it is already present.
    ///
    /// # Specification
    /// - ensures: Retains the offered edge without duplicating it.
    /// - fails: typed capacity, arithmetic or state errors described below.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 differential streams and L3 boundaries distinguish
    ///   wrong verdicts, lost edges and invalid maintained state on finite
    ///   graphs.
    /// - witness: `composition::tests::the_gates_own_graph_streamed_incrementally_reproduces_its_verdict`

    #[spec(ensures: |ret| edges.contains(&edge))]
    fn push_edge(
        edges: &mut Vec<EdgeId>,
        edge: EdgeId,
    )
    {
        if !edges.contains(&edge) {
            edges.push(edge);
        }
    }

    /// **The gate's flow graph as an edge stream**, derived from the public
    /// alphabet surface exactly as [`compose_directed`]'s specification
    /// describes the construction: `(cell, hole)` nodes over the two
    /// certificates' participating cells and the seam holes of
    /// `a.joins_at`, with an edge for every endpoint pair where one side
    /// emits and the other absorbs.
    ///
    /// Deriving it here rather than reading the gate's own builder is the point
    /// of the test below. If the specification's account of the construction
    /// were wrong, this stream would carry different edges and the verdicts
    /// would diverge — so what is checked is the characterization itself,
    /// not only the maintenance that consumes it.
    ///
    /// # Specification
    /// - ensures: Derives emit-to-absorb edges at the left recorded join.
    /// - fails: typed capacity, arithmetic or state errors described below.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 differential streams and L3 boundaries distinguish
    ///   wrong verdicts, lost edges and invalid maintained state on finite
    ///   graphs.
    /// - witness: `composition::tests::the_gates_own_graph_streamed_incrementally_reproduces_its_verdict`

    #[spec(ensures: |ret| ret.iter().all(|edge| edge.source != edge.target) || participating(a).iter().any(|cell| participating(b).contains(cell)))]
    fn characterized_stream(
        a: &Tracelet,
        b: &Tracelet,
        store: &CellStore,
    ) -> Vec<EdgeId>
    {
        let left_cells = participating(a);
        let right_cells = participating(b);
        let mut holes: Vec<SeamHole> = Vec::new();
        for var in SequentAlphabet::metavariables(&a.joins_at) {
            let hole = SequentAlphabet::hole_of(&var);
            if !holes.contains(&hole) {
                holes.push(hole);
            }
        }
        let mut nodes: Vec<(CellId, SeamHole)> = Vec::new();
        let mut edges: Vec<EdgeId> = Vec::new();
        for hole in &holes {
            let left = seam_endpoints(&left_cells, hole, store);
            let right = seam_endpoints(&right_cells, hole, store);
            if left.is_empty() || right.is_empty() {
                // Not shared across the seam — no cross flow.
                continue;
            }
            for &(left_cell, ref left_var, left_role) in &left {
                for &(right_cell, ref right_var, right_role) in &right {
                    let source = intern_node(&mut nodes, left_cell, left_var);
                    let target = intern_node(&mut nodes, right_cell, right_var);
                    let left_emits = matches!(left_role, SeamRole::Forward | SeamRole::Both);
                    let left_absorbs = matches!(left_role, SeamRole::Backward | SeamRole::Both);
                    let right_emits = matches!(right_role, SeamRole::Forward | SeamRole::Both);
                    let right_absorbs = matches!(right_role, SeamRole::Backward | SeamRole::Both);
                    if left_emits && right_absorbs {
                        push_edge(&mut edges, EdgeId::new(source, target));
                    }
                    if right_emits && left_absorbs {
                        push_edge(&mut edges, EdgeId::new(target, source));
                    }
                }
            }
        }
        edges
    }

    #[test]
    fn the_gates_own_graph_streamed_incrementally_reproduces_its_verdict()
    {
        let mut corpus: Vec<(&'static str, CellStore, Tracelet, Tracelet)> = Vec::new();
        let (ground_store, ground_left, ground_right) = ground_chain();
        corpus.push((
            "ground chain, no seam metavariables",
            ground_store,
            ground_left,
            ground_right,
        ));
        for &(label, left_mixed, right_mixed) in &[
            ("producer left, consumer right", false, false),
            ("mixed left, consumer right", true, false),
            ("producer left, mixed right", false, true),
            ("mixed on both sides", true, true),
        ] {
            let (store, left, right) =
                variance_pair(SeamHoleMixed(left_mixed), SeamHoleMixed(right_mixed));
            corpus.push((label, store, left, right));
        }
        let (shared_store, shared_left, shared_right) = mixed_pair();
        corpus.push((
            "two shared mixed holes",
            shared_store,
            shared_left,
            shared_right,
        ));

        let mut edges_streamed: usize = 0;
        let mut admitted_rows_with_edges: usize = 0;
        let mut refused_rows_with_edges: usize = 0;

        for &(label, ref store, ref left, ref right) in &corpus {
            let gate_declines = compose_directed(left, right, store).is_err();
            let stream = characterized_stream(left, right, store);
            edges_streamed = edges_streamed.saturating_add(stream.len());

            let mut reversed = stream.clone();
            reversed.reverse();
            for (arrival, offers) in [("as derived", &stream), ("reversed", &reversed)] {
                let mut maintenance =
                    AcyclicityMaintenance::new().expect("a fresh structure is available");
                let mut refused = false;
                for &offer in offers {
                    let verdict = maintenance
                        .insert_edge(offer)
                        .expect("insertion is total over well-formed identifiers");
                    if matches!(verdict, EdgeVerdict::Refused(_)) {
                        refused = true;
                        break;
                    }
                }
                assert_eq!(
                    gate_declines, refused,
                    "{label}, streamed {arrival}: the incremental verdict must equal the gate's"
                );
            }

            if !stream.is_empty() {
                if gate_declines {
                    refused_rows_with_edges = refused_rows_with_edges.saturating_add(1);
                }
                else {
                    admitted_rows_with_edges = admitted_rows_with_edges.saturating_add(1);
                }
            }
        }

        // Non-vacuity: an agreement reached over empty graphs would agree about
        // nothing, so the corpus must exercise both answers with edges present.
        assert!(
            edges_streamed > 0,
            "the corpus must put real edges through the maintenance"
        );
        assert!(
            refused_rows_with_edges > 0,
            "the corpus must contain a declined composite whose graph is non-empty"
        );
        assert!(
            admitted_rows_with_edges > 0,
            "the corpus must contain an admitted composite whose graph is non-empty"
        );
    }
}
