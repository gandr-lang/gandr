//! Speculative refusals stay distinct from normalizer failures.

#[cfg(test)]
mod tests
{
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

    use gandr_theory_cell_complexes::CellStore;
    use gandr_theory_cell_complexes_tools::IncomparablePositions;
    use gandr_theory_cell_complexes_tools::Lying;
    use gandr_theory_cell_complexes_tools::Toy;
    use gandr_theory_cell_complexes_tools::lying_cell;
    use gandr_theory_coherent_resolutions::CellApp;
    use gandr_theory_decomposition_spaces::pathway::CandidateRefusal;
    use gandr_theory_decomposition_spaces::pathway::certify_candidate;
    use gandr_theory_deep_inference::NormalFormObstruction;
    use gandr_theory_deep_inference::prim_address;
    use quenchant_shape::shape::Maybe;

    /// A position in the fixture alphabet.
    macro_rules! at { ($($step:expr),* $(,)?) => { <Lying<IncomparablePositions> as gandr_theory_cell_complexes::CellAlphabet>::position_at_path(&[$(gandr_theory_cell_complexes::PositionStep::from($step)),*]) }; }

    #[test]
    fn a_kill_signal_stops_the_query_rather_than_refusing_a_candidate()
    {
        let mut store: CellStore<Lying<IncomparablePositions>> = CellStore::new();
        let c = store.insert(lying_cell(Toy::add(Toy::zero(), Toy::zero()), Toy::zero()));
        let peak = Toy::add(
            Toy::add(Toy::zero(), Toy::zero()),
            Toy::add(Toy::zero(), Toy::zero()),
        );
        let root = CellApp { cell: c, at: at![] };
        let recorded = alloc::vec![
            CellApp {
                cell: c,
                at: at![0],
            },
            CellApp {
                cell: c,
                at: at![1],
            },
            root.clone(),
        ];
        let cell = present(store.get(c));
        let root_address = prim_address(cell, &at![]);
        let left_address = prim_address(cell, &at![0]);
        let right_address = prim_address(cell, &at![1]);
        assert!(
            root_address < left_address.max(right_address),
            "the fixture needs the root application not to come last in the flattened layer"
        );
        let raised = certify_candidate(&store, &peak, &Toy::zero(), &recorded)
            .expect_err("the kill signal must reach the caller");
        assert_eq!(
            NormalFormObstruction::ShiftedScheduleDoesNotFire {
                step: alloc::boxed::Box::new(root)
            },
            raised,
            "the propagated obstruction is the kill signal, naming the step that carried no redex"
        );
    }

    #[test]
    fn an_ordinary_non_replaying_candidate_is_refused_without_failing()
    {
        let mut store: CellStore<Lying<IncomparablePositions>> = CellStore::new();
        let c = store.insert(lying_cell(Toy::add(Toy::zero(), Toy::zero()), Toy::zero()));
        let peak = Toy::add(Toy::zero(), Toy::zero());
        let recorded = alloc::vec![CellApp { cell: c, at: at![] }];
        let refused = certify_candidate(&store, &peak, &peak, &recorded)
            .expect("a candidate that misses its join is refused, not fatal");
        assert!(matches!(
            refused,
            Maybe::Absent(CandidateRefusal::Refused {
                obstruction: NormalFormObstruction::PathMissesTheJoin { .. }
            })
        ));
    }
    /// Backward growth admits one representative and preserves its stopped
    /// frontier.
    #[test]
    fn a_backward_extension_is_returned_once_with_its_exact_frontier()
    {
        use gandr_theory_cell_complexes::Cell;
        use gandr_theory_cell_complexes::CellProvenance;
        use gandr_theory_cell_complexes::CellStore;
        use gandr_theory_cell_complexes::CmdPat;
        use gandr_theory_cell_complexes::ConsPat;
        use gandr_theory_cell_complexes::Orientation;
        use gandr_theory_cell_complexes::Polarity;
        use gandr_theory_cell_complexes::Pos;
        use gandr_theory_cell_complexes::ProdPat;
        use gandr_theory_cell_complexes::SequentAlphabet;
        use gandr_theory_coherent_resolutions::CellApp;
        use gandr_theory_coherent_resolutions::Tracelet;
        use gandr_theory_coherent_resolutions::enumerate_overlaps;
        use gandr_theory_decomposition_spaces::compose_directed;
        use gandr_theory_decomposition_spaces::pathway::PathwayBudget;
        use gandr_theory_decomposition_spaces::pathway::PathwayDeclineReason;
        use gandr_theory_decomposition_spaces::pathway::PathwayOutcome;
        use gandr_theory_decomposition_spaces::pathway::synthesize_pathways;

        let term =
            |name: &str| CmdPat::cut(Polarity::Positive, ProdPat::ctor(name, []), ConsPat::top());
        let mut store = CellStore::<SequentAlphabet>::new();
        let [ab, bc] = [("A", "B"), ("B", "C")].map(|(a, b)| {
            store.insert(Cell::new(
                term(a),
                term(b),
                Orientation::CompletionDerived,
                CellProvenance::DerivedByCompletion,
            ))
        });
        let template = enumerate_overlaps(&store)
            .into_iter()
            .find(|o| o.left == ab && o.right == bc)
            .expect("sequential seam");
        let certificate = |cell, peak, join| {
            let step = CellApp {
                cell,
                at: Pos::root(),
            };
            let mut overlap = template.clone();
            overlap.peak = peak;
            Tracelet {
                overlap,
                path_a: vec![step.clone()],
                path_b: vec![step],
                joins_at: join,
            }
        };
        let left = certificate(ab, term("A"), term("B"));
        let seed = certificate(bc, term("B"), term("C"));
        let directed = compose_directed(&left, &seed, &store).expect("ground gate");

        let transitions = [left.clone(), left];
        let result = synthesize_pathways(
            &store,
            &seed,
            bc,
            &transitions,
            PathwayBudget::new(3_usize.into(), 16_usize.into()),
        )
        .expect("query");
        let PathwayOutcome::Complete { pathways } = result
        else {
            panic!("finite query exhausts")
        };
        let [ref seed_pathway, ref extension] = *pathways.as_slice()
        else {
            panic!("seed and one compressed extension")
        };
        assert_eq!(seed_pathway.certificate, seed);
        assert_eq!(extension.certificate, directed);
        assert_eq!(usize::from(extension.length), 2);
        assert_eq!(extension.certificate.path_a, vec![
            CellApp {
                cell: ab,
                at: Pos::root()
            },
            CellApp {
                cell: bc,
                at: Pos::root()
            }
        ]);
        assert!(bool::from(extension.certificate.replay(&store)));
        let bounded = synthesize_pathways(
            &store,
            &seed,
            bc,
            &transitions,
            PathwayBudget::new(2_usize.into(), 16_usize.into()),
        )
        .expect("bounded query");
        let PathwayOutcome::Declined {
            pathways: admitted,
            frontier,
            reason,
            built,
        } = bounded
        else {
            panic!("length ceiling")
        };
        assert_eq!(reason, PathwayDeclineReason::LengthBudget);
        assert_eq!(admitted.len(), 2);
        assert_eq!(frontier.len(), 1);
        assert_eq!(usize::from(built), 2);
        let capped = synthesize_pathways(
            &store,
            &seed,
            bc,
            &transitions,
            PathwayBudget::new(3_usize.into(), 1_usize.into()),
        )
        .expect("candidate ceiling");
        let PathwayOutcome::Declined {
            pathways: partial,
            frontier,
            reason,
            built,
        } = capped
        else {
            panic!("candidate ceiling reached mid-round")
        };
        assert_eq!(reason, PathwayDeclineReason::CandidateBudget);
        assert_eq!(usize::from(built), 1);
        assert!(
            partial
                .iter()
                .map(|pathway| &pathway.certificate)
                .eq([&seed, &directed]),
            "a candidate ceiling retains the pathway already admitted in this round"
        );
        assert!(
            frontier
                .iter()
                .map(|pathway| &pathway.certificate)
                .eq([&seed])
        );
    }
}
