//! Certificate transport through the public algebra and storage boundary.

extern crate alloc;

#[cfg(test)]
mod tests
{
    use gandr_storage_artifact::transport::TransportStepId;
    use gandr_storage_artifact::transport::TransportStepObstruction;
    use gandr_storage_artifact::transport::transport_step_id;
    use gandr_storage_artifact::transport::transport_step_index;
    use gandr_theory_cell_complexes::Cell;
    use gandr_theory_cell_complexes::CellId;
    use gandr_theory_cell_complexes::CellProvenance;
    use gandr_theory_cell_complexes::CellStore;
    use gandr_theory_cell_complexes::CmdPat;
    use gandr_theory_cell_complexes::ConsPat;
    use gandr_theory_cell_complexes::EtaKind;
    use gandr_theory_cell_complexes::Orientation;
    use gandr_theory_cell_complexes::Polarity;
    use gandr_theory_cell_complexes::Pos;
    use gandr_theory_cell_complexes::ProdPat;
    use gandr_theory_cell_complexes::Sym;
    use gandr_theory_cell_complexes::frame_defining_cell;
    use gandr_theory_coherent_resolutions::CellApp;
    use gandr_theory_coherent_resolutions::OverlapKind;
    use gandr_theory_coherent_resolutions::Tracelet;
    use gandr_theory_coherent_resolutions::derive_fused;
    use gandr_theory_coherent_resolutions::enumerate_overlaps;
    use gandr_theory_decomposition_spaces::compose_invertible;
    use gandr_theory_deep_inference::TraceletNf;
    use gandr_theory_deep_inference::normalize;
    use quenchant_shape::shape::Maybe;

    /// The successor-addition cell.
    ///
    /// # Specification
    /// trivial.
    fn add_s() -> Cell
    {
        Cell::new(
            CmdPat::cut(
                Polarity::Positive,
                ProdPat::ctor("Succ", [ProdPat::meta("m")]),
                ConsPat::op("add", [ProdPat::meta("n")], ConsPat::meta("alpha")),
            ),
            CmdPat::cut(
                Polarity::Positive,
                ProdPat::meta("m"),
                ConsPat::op(
                    "add",
                    [ProdPat::meta("n")],
                    ConsPat::frame("Succ", ConsPat::meta("alpha")),
                ),
            ),
            Orientation::PolarityDerived,
            CellProvenance::SurfaceRule,
        )
    }

    /// A frame/add composition with its fused certificate.
    ///
    /// # Specification
    /// trivial.
    fn fused_fixture() -> (CellStore, Tracelet)
    {
        let mut store = CellStore::new();
        let frame = store.insert(frame_defining_cell(&Sym::new("Succ")));
        let add = store.insert(add_s());
        let overlap = enumerate_overlaps(&store)
            .into_iter()
            .find(|overlap| {
                overlap.kind == OverlapKind::Composition
                    && overlap.left == frame
                    && overlap.right == add
            })
            .expect("composition exists");
        let (_, tracelet) = derive_fused(&overlap, &mut store).expect("fuses");
        (store, tracelet)
    }

    /// Resolve a fixture's issued handle.
    ///
    /// # Specification
    /// trivial.
    fn stored(
        store: &CellStore,
        id: CellId,
    ) -> &Cell
    {
        let Maybe::Present(cell) = store.get(id)
        else {
            panic!("fixture cell exists")
        };
        cell
    }

    /// Normalize the certificate's first leg.
    ///
    /// # Specification
    /// trivial.
    fn first_leg(
        store: &CellStore,
        tracelet: &Tracelet,
    ) -> TraceletNf
    {
        normalize(
            store,
            &tracelet.overlap.peak,
            &tracelet.joins_at,
            &tracelet.path_a,
        )
        .expect("first leg normalizes")
    }

    #[test]
    fn the_v1_golden_step_identity_is_stable()
    {
        let cell = frame_defining_cell(&Sym::new("Succ"));
        assert_eq!(
            transport_step_id(&cell, &Pos::root())
                .expect("encodes")
                .to_string(),
            "c04ba7d738000bed6f41d3115d5bfaf7d92a4566e0d7b92ced60d5a3cbd3fdc8"
        );
    }

    #[test]
    fn an_independently_rebuilt_cell_mints_the_same_identity()
    {
        let first = frame_defining_cell(&Sym::new("Succ"));
        let second = frame_defining_cell(&Sym::new("Succ"));
        assert_eq!(
            transport_step_id(&first, &Pos::root()),
            transport_step_id(&second, &Pos::root())
        );
    }

    #[test]
    fn the_identity_reads_the_position()
    {
        let cell = frame_defining_cell(&Sym::new("Succ"));
        assert_ne!(
            transport_step_id(&cell, &Pos::root()).expect("encodes"),
            transport_step_id(&cell, &Pos::root().child(0_usize.into())).expect("encodes")
        );
    }

    #[test]
    fn the_identity_reads_the_cell_content()
    {
        assert_ne!(
            transport_step_id(&frame_defining_cell(&Sym::new("Succ")), &Pos::root())
                .expect("encodes"),
            transport_step_id(&frame_defining_cell(&Sym::new("Pred")), &Pos::root())
                .expect("encodes")
        );
    }

    #[test]
    fn the_identity_is_stable_across_store_insertion_orders()
    {
        let mut forward = CellStore::new();
        let first = forward.insert(frame_defining_cell(&Sym::new("Succ")));
        let mut reverse = CellStore::new();
        reverse.insert(add_s());
        let second = reverse.insert(frame_defining_cell(&Sym::new("Succ")));
        assert_ne!(first, second);
        assert_eq!(
            transport_step_id(stored(&forward, first), &Pos::root()),
            transport_step_id(stored(&reverse, second), &Pos::root())
        );
    }

    #[test]
    fn the_index_preserves_the_graded_factorization()
    {
        let (store, tracelet) = fused_fixture();
        let normal = first_leg(&store, &tracelet);
        let index = transport_step_index(&normal, &store).expect("indexes");
        for &(ref cert, multiplicity) in normal.primitives.values() {
            let step = cert.step();
            let id = transport_step_id(stored(&store, step.cell), &step.at).expect("encodes");
            assert_eq!(
                index.entries().get(&id),
                Some(&(cert.clone(), multiplicity))
            );
        }
        assert_eq!(index.entries().len(), normal.primitives.len());
    }

    #[test]
    fn the_index_is_deterministic_across_repeated_normalization()
    {
        let (store, tracelet) = fused_fixture();
        let first = first_leg(&store, &tracelet);
        let second = first_leg(&store, &tracelet);
        assert_eq!(
            transport_step_index(&first, &store).expect("indexes"),
            transport_step_index(&second, &store).expect("indexes")
        );
    }

    #[test]
    fn distinct_factorizations_index_distinctly()
    {
        let (store, tracelet) = fused_fixture();
        let first = first_leg(&store, &tracelet);
        let fused = normalize(
            &store,
            &tracelet.overlap.peak,
            &tracelet.joins_at,
            &tracelet.path_b,
        )
        .expect("fused leg normalizes");
        assert_ne!(
            transport_step_index(&first, &store).expect("indexes"),
            transport_step_index(&fused, &store).expect("indexes")
        );
    }

    #[test]
    fn the_index_refuses_an_unresolved_cell()
    {
        let (store, tracelet) = fused_fixture();
        let normal = first_leg(&store, &tracelet);
        let cert = &normal
            .primitives
            .first_key_value()
            .expect("has factors")
            .1
            .0;
        assert_eq!(
            transport_step_index(&normal, &CellStore::new()),
            Err(TransportStepObstruction::UnknownCell {
                cell: cert.step().cell
            })
        );
    }

    #[test]
    fn a_publicly_composed_tracelet_round_trips_its_step_identities()
    {
        let (store, tracelet) = fused_fixture();
        // The identity certificate at the join supplies a genuine sequential unit.
        let mut unit = tracelet.clone();
        unit.overlap.peak = tracelet.joins_at.clone();
        unit.path_a.clear();
        unit.path_b.clear();
        let composed = compose_invertible(&tracelet, &unit);
        assert!(bool::from(composed.replay(&store)));
        let normal = first_leg(&store, &composed);
        let first = transport_step_index(&normal, &store).expect("indexes");
        let second = transport_step_index(&normal, &store).expect("indexes again");
        assert_eq!(first, second);
        let decoded: Vec<_> = first
            .entries()
            .keys()
            .map(|id| TransportStepId::try_from(id.as_ref()).expect("fixed-width readback"))
            .collect();
        assert_eq!(
            decoded,
            second.entries().keys().copied().collect::<Vec<_>>()
        );
        let Maybe::Present(path) = normal.canonical_path()
        else {
            panic!("normalized schedule resolves")
        };
        let readback: alloc::collections::BTreeMap<_, _> = decoded
            .into_iter()
            .zip(first.entries().values().map(|graded| graded.0.step()))
            .collect();
        let path: Vec<CellApp> = path
            .iter()
            .map(|step| {
                let id = transport_step_id(stored(&store, step.cell), &step.at).expect("encodes");
                (*readback.get(&id).expect("decoded identity resolves")).clone()
            })
            .collect();
        assert_eq!(
            normalize(&store, &composed.overlap.peak, &composed.joins_at, &path)
                .expect("replays decoded index factors"),
            normal
        );
    }

    #[test]
    fn every_orientation_provenance_and_polarity_is_bound()
    {
        let mut identities = alloc::collections::BTreeSet::new();
        for polarity in [Polarity::Positive, Polarity::Negative] {
            for orientation in [Orientation::PolarityDerived, Orientation::CompletionDerived] {
                for provenance in [
                    CellProvenance::SurfaceRule,
                    CellProvenance::MuMuTilde,
                    CellProvenance::FrameDefining,
                    CellProvenance::Eta(EtaKind::Data),
                    CellProvenance::Eta(EtaKind::Codata),
                    CellProvenance::DerivedByCompletion,
                ] {
                    let lhs = CmdPat::cut(polarity, ProdPat::meta("v"), ConsPat::meta("k"));
                    let rhs = CmdPat::cut(
                        polarity,
                        ProdPat::ctor("S", [ProdPat::meta("v")]),
                        ConsPat::meta("k"),
                    );
                    let cell = Cell::new(lhs, rhs, orientation, provenance);
                    let id = transport_step_id(&cell, &Pos::root()).expect("encodes");
                    assert!(
                        identities.insert(id),
                        "distinct structural tags cannot share a step image"
                    );
                }
            }
        }
    }
}
