//! Public-API law witnesses.

#[cfg(test)]
mod tests
{
    use anodized::spec;
    use gandr_theory_cell_complexes::Cell;
    use gandr_theory_cell_complexes::CellId;
    use gandr_theory_cell_complexes::CellProvenance;
    use gandr_theory_cell_complexes::CellStore;
    use gandr_theory_cell_complexes::CmdPat;
    use gandr_theory_cell_complexes::ConsPat;
    use gandr_theory_cell_complexes::Orientation;
    use gandr_theory_cell_complexes::Polarity;
    use gandr_theory_cell_complexes::ProdPat;
    use gandr_theory_coherent_resolutions::Overlap;
    use gandr_theory_coherent_resolutions::OverlapKind;
    use gandr_theory_coherent_resolutions::Tracelet;
    use gandr_theory_coherent_resolutions::derive_fused;
    use gandr_theory_coherent_resolutions::enumerate_overlaps;
    use gandr_theory_levitation::FreeTerm;
    use gandr_theory_levitation::Name;
    use gandr_theory_levitation::NameRef;
    use gandr_theory_levitation::NominalId;
    use gandr_theory_virtual_doctrines::BiDiagram;
    use gandr_theory_virtual_doctrines::Coend;
    use gandr_theory_virtual_doctrines::CutOutcome;
    use gandr_theory_virtual_doctrines::Diagram;
    use gandr_theory_virtual_doctrines::DirectedContext;
    use gandr_theory_virtual_doctrines::DirectedHom;
    use gandr_theory_virtual_doctrines::DirectedJ;
    use gandr_theory_virtual_doctrines::End;
    use gandr_theory_virtual_doctrines::JError;
    use gandr_theory_virtual_doctrines::MotiveShape;
    use gandr_theory_virtual_doctrines::OpSig;
    use gandr_theory_virtual_doctrines::Query;
    use gandr_theory_virtual_doctrines::RewriteStepBudget;
    use gandr_theory_virtual_doctrines::SignatureRef;
    use gandr_theory_virtual_doctrines::TermRef;
    use gandr_theory_virtual_doctrines::Variance;
    use gandr_theory_virtual_doctrines::VarianceError;
    use gandr_theory_virtual_doctrines::check_directed_j;
    use gandr_theory_virtual_doctrines::coyoneda_collapse;
    use gandr_theory_virtual_doctrines::directed_cut;
    use gandr_theory_virtual_doctrines::fubini_swap;
    use proptest::prelude::*;
    use quenchant_shape::shape::Maybe;

    /// Whether two slices are equal as multisets (order-independent).
    ///
    /// # Specification
    /// - ensures: equality preserves occurrence counts, including duplicates.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — transpose compares the full finite carrier multiset,
    ///   so lost or duplicated components change the observation.
    /// - witness: `tests::directed::tests::fubini_preserves_the_iterated_end`
    #[spec(ensures: |ret| bool::from(ret) == (left.len() == right.len() && left.iter().all(|value| left.iter().filter(|item| *item == value).count() == right.iter().filter(|item| *item == value).count())))]
    fn same_multiset(
        left: &[TermRef],
        right: &[TermRef],
    ) -> TermMultisetEquality
    {
        TermMultisetEquality::from(
            left.len() == right.len()
                && left.iter().all(|item| {
                    let in_left = left.iter().filter(|&other| other == item).count();
                    let in_right = right.iter().filter(|&other| other == item).count();
                    in_left == in_right
                }),
        )
    }

    /// A strategy over the two directed variances.
    /// # Specification
    /// trivial.
    fn variance_strategy() -> impl Strategy<Value = Variance>
    {
        prop_oneof![Just(Variance::Covariant), Just(Variance::Contravariant)]
    }

    // ---- variance-sorted reflected contexts --------------------------

    #[test]
    fn a_producer_hole_checks_covariantly()
    {
        // `m` is a producer var; sorted covariantly, the the reflection rules metadata
        // checks.
        let ctx = DirectedContext::new().with_var(NameRef::from("m"), OpSig::covariant(nat_sig()));
        assert_eq!(
            Ok(()),
            ctx.check_cell_variance(&add_s()),
            "a producer hole sorted covariantly passes the variance check"
        );
    }

    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct TermMultisetEquality(bool);

    impl From<bool> for TermMultisetEquality
    {
        #[inline]
        /// Convert the boundary value without changing its representation.
        ///
        /// # Specification
        /// trivial.
        fn from(value: bool) -> Self
        {
            Self(value)
        }
    }

    impl From<TermMultisetEquality> for bool
    {
        #[inline]
        /// Convert the boundary value without changing its representation.
        ///
        /// # Specification
        /// trivial.
        fn from(value: TermMultisetEquality) -> Self
        {
            value.0
        }
    }

    #[test]
    fn a_consumer_hole_checks_contravariantly()
    {
        // `alpha` is a consumer var; sorted contravariantly (`Iᵒᵖ`), it checks.
        let ctx = DirectedContext::new()
            .with_var(NameRef::from("alpha"), OpSig::contravariant(nat_sig()));
        assert_eq!(
            Ok(()),
            ctx.check_cell_variance(&add_s()),
            "a consumer hole sorted contravariantly passes the variance check"
        );
    }

    #[test]
    fn a_producer_hole_sorted_contravariantly_is_rejected()
    {
        // The the reflection rules metadata is now CHECKABLE: a producer hole declared
        // contravariant is a variance mismatch (not merely derived).
        let ctx =
            DirectedContext::new().with_var(NameRef::from("m"), OpSig::contravariant(nat_sig()));
        assert_eq!(
            ctx.check_cell_variance(&add_s()),
            Err(VarianceError::Mismatch {
                var: n(NameRef::from("m")),
                declared: Variance::Contravariant,
                derived: Variance::Covariant,
            }),
            "a producer hole sorted contravariantly is rejected"
        );
    }

    #[test]
    fn a_mixed_hole_cannot_be_sorted_at_a_directed_variance()
    {
        let mixed = mixed_step(NameRef::from("r"), NameRef::from("dn"), NameRef::from("up"));
        for variance in [Variance::Covariant, Variance::Contravariant] {
            let obj = OpSig {
                sig: nat_sig(),
                variance,
            };
            let ctx = DirectedContext::new().with_var(NameRef::from("r"), obj);
            assert_eq!(
                ctx.check_cell_variance(&mixed),
                Err(VarianceError::MixedHole {
                    var: n(NameRef::from("r"))
                }),
                "a mixed hole cannot inhabit a single directed variance"
            );
        }
    }

    #[test]
    fn an_undeclared_hole_is_unconstrained()
    {
        // Holes the context does not declare are the cell's local data.
        let ctx =
            DirectedContext::new().with_var(NameRef::from("absent"), OpSig::covariant(nat_sig()));
        assert_eq!(
            Ok(()),
            ctx.check_cell_variance(&add_s()),
            "undeclared holes do not constrain the variance check"
        );
    }

    proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]
    /// `op` is an involution on the reflected signature alone.
            #[test]
            fn op_is_an_involution_on_reflected_signatures(
                serial in 0_u64 .. 8,
                name in "[A-Z][a-z]{0,3}",
                variance in variance_strategy(),
            ) {
                let obj = OpSig {
                    sig: SignatureRef::single(NominalId::new(serial.into(), name.as_str())),
                    variance,
                };
                let once = obj.op();
                prop_assert_eq!(once.variance, variance.flip(), "op flips the variance");
                prop_assert_eq!(&once.sig, &obj.sig, "op leaves the reflected signature untouched");
                prop_assert_eq!(once.op(), obj, "op is an involution");
            }
    }

    // ---- directed hom + polarity-restricted directed J ---------------

    #[test]
    fn directed_j_transports_along_a_covariant_motive()
    {
        let scrut = DirectedHom::new(nat_sig(), vt(NameRef::from("a")), vt(NameRef::from("b")));
        // Covariant motive C(x) = hom(c ⇝ x): transports forward to hom(c ⇝ b).
        let covariant = DirectedJ::new(MotiveShape::CovariantTarget, vt(NameRef::from("c")));
        assert_eq!(
            check_directed_j(&scrut, &covariant),
            Ok(DirectedHom::new(
                nat_sig(),
                vt(NameRef::from("c")),
                vt(NameRef::from("b"))
            )),
            "a covariant motive transports the covariant endpoint forward"
        );
        // Constant motive C(x) = hom(c ⇝ c): admissible, yields the diagonal.
        let constant = DirectedJ::new(MotiveShape::Constant, vt(NameRef::from("c")));
        assert_eq!(
            check_directed_j(&scrut, &constant),
            Ok(DirectedHom::new(
                nat_sig(),
                vt(NameRef::from("c")),
                vt(NameRef::from("c"))
            )),
            "a constant motive is admissible"
        );
    }

    #[test]
    fn directed_j_refuses_the_symmetry_motive()
    {
        let scrut = DirectedHom::new(nat_sig(), vt(NameRef::from("a")), vt(NameRef::from("b")));
        // Symmetry needs C(x) = hom(x ⇝ a): the moving endpoint in the
        // contravariant source slot — the polarity side condition refuses it.
        let symmetry = DirectedJ::symmetry(vt(NameRef::from("a")));
        assert_eq!(
            Err(JError::MotiveNotCovariant),
            check_directed_j(&scrut, &symmetry),
            "the symmetry motive is refused (directed J is polarity-restricted)"
        );
    }

    #[test]
    fn a_directed_cell_with_no_inverse_has_no_backward_transport()
    {
        // A single oriented step `A ~> B` — a directed cell with no inverse.
        let mut store = CellStore::new();
        store.insert(ground_step(NameRef::from("A"), NameRef::from("B")));
        let query = Query::new(&store);
        let a = ground_cmd(NameRef::from("A"));
        let b = ground_cmd(NameRef::from("B"));
        let fwd = DirectedHom::new(nat_sig(), ct(NameRef::from("A")), ct(NameRef::from("B")));
        assert!(
            !bool::from(fwd.is_reflexive()),
            "the forward hom is a genuine directed cell"
        );
        // Forward is witnessed; backward (symmetry) has NO engine witness.
        assert!(
            bool::from(query.reaches(&a, &b, RewriteStepBudget::from(16_usize))),
            "the forward directed cell A ~> B is witnessed"
        );
        assert!(
            !bool::from(query.reaches(&b, &a, RewriteStepBudget::from(16_usize))),
            "the backward transport B ~> A has no witness (no inverse)"
        );
    }

    proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]
    /// symmetry is refused for every generated directed hom, and no
            /// covariant motive can produce the reversed hom.
            #[test]
            fn symmetry_is_never_derivable(
                source in "[a-z]{1,3}",
                target in "[a-z]{1,3}",
                fixed in "[a-z]{1,3}",
            ) {
                let scrut = DirectedHom::new(nat_sig(), vt(NameRef::from(source.as_str())), vt(NameRef::from(target.as_str())));
                // The symmetry motive is always refused.
                prop_assert_eq!(
                    check_directed_j(&scrut, &DirectedJ::symmetry(scrut.src.clone())),
                    Err(JError::MotiveNotCovariant),
                    "symmetry is underivable for every directed hom"
                );
                // The admissible (covariant) motive never reverses the target endpoint.
                let covariant = DirectedJ::new(MotiveShape::CovariantTarget, vt(NameRef::from(fixed.as_str())));
                let transported = check_directed_j(&scrut, &covariant)
                    .expect("a covariant motive is admissible");
                prop_assert_eq!(
                    transported.tgt, scrut.tgt,
                    "the admissible motive keeps the covariant target — never the reversed source"
                );
            }
    }

    /// A directed (oriented, **non-invertible**) ground step `⟨from | ★⟩ ~>
    /// ⟨to | ★⟩`.
    /// # Specification
    /// trivial.
    fn ground_step(
        from: NameRef<'_>,
        to: NameRef<'_>,
    ) -> Cell
    {
        Cell::new(
            ground_cmd(from),
            ground_cmd(to),
            Orientation::PolarityDerived,
            CellProvenance::SurfaceRule,
        )
    }

    // ---- (co)ends; Fubini and (co)Yoneda derived ---------------------

    #[test]
    fn the_end_and_coend_collect_the_diagonal_components()
    {
        let diagram = Diagram::new(vec![
            (ct(NameRef::from("P0")), ct(NameRef::from("V0"))),
            (ct(NameRef::from("P1")), ct(NameRef::from("V1"))),
        ]);
        assert_eq!(
            End::of(&diagram).components,
            vec![ct(NameRef::from("V0")), ct(NameRef::from("V1"))],
            "the end is the product of the diagonal components"
        );
        assert_eq!(
            Coend::of(&diagram).summands,
            vec![ct(NameRef::from("V0")), ct(NameRef::from("V1"))],
            "the coend is the coproduct of the diagonal components"
        );
    }

    proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]
    /// Fubini's swap is its own inverse.
            #[test]
            fn fubini_swap_is_an_involution(
                entries in prop::collection::vec(((0_u32 .. 4, 0_u32 .. 4), 0_u32 .. 6), 0_usize .. 6),
            ) {
                let bi_diagram = BiDiagram::new(
                    entries
                        .iter()
                        .map(|&entry| {
                            let ((x, y), payload) = entry;
                            (
                                (ct(NameRef::from(format!("X{x}").as_str())), ct(NameRef::from(format!("Y{y}").as_str()))),
                                ct(NameRef::from(format!("P{payload}").as_str())),
                            )
                        })
                        .collect::<Vec<_>>(),
                );
                prop_assert_eq!(
                    fubini_swap(&fubini_swap(&bi_diagram)),
                    bi_diagram,
                    "fubini_swap is an involution"
                );
            }

    /// Fubini preserves the iterated end — the transpose is a bijection.
            #[test]
            fn fubini_preserves_the_iterated_end(
                entries in prop::collection::vec(((0_u32 .. 4, 0_u32 .. 4), 0_u32 .. 6), 0_usize .. 6),
            ) {
                let bi_diagram = BiDiagram::new(
                    entries
                        .iter()
                        .map(|&entry| {
                            let ((x, y), payload) = entry;
                            (
                                (ct(NameRef::from(format!("X{x}").as_str())), ct(NameRef::from(format!("Y{y}").as_str()))),
                                ct(NameRef::from(format!("P{payload}").as_str())),
                            )
                        })
                        .collect::<Vec<_>>(),
                );
                let swapped = fubini_swap(&bi_diagram);
                prop_assert!(
                    bool::from(same_multiset(&bi_diagram.payloads(), &swapped.payloads())),
                    "the iterated-end payload multiset is preserved"
                );
                let transposed: Vec<(TermRef, TermRef)> = bi_diagram
                    .index_pairs()
                    .into_iter()
                    .map(|(x, y)| (y, x))
                    .collect();
                prop_assert_eq!(
                    swapped.index_pairs(), transposed,
                    "the index set is exactly transposed"
                );
            }
    }

    #[test]
    fn coyoneda_is_none_off_carrier()
    {
        let diagram = Diagram::new(vec![(ct(NameRef::from("P0")), ct(NameRef::from("V0")))]);
        assert_eq!(
            Maybe::Absent(
                gandr_theory_virtual_doctrines::directed::coend::carrier_lookup::Absent::OffCarrier
            ),
            coyoneda_collapse(&ct(NameRef::from("OffCarrier")), &diagram),
            "the density coend is empty off the carrier"
        );
    }

    proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]
    /// co-Yoneda collapses the density coend to `F(a)` on the carrier.
            #[test]
            fn coyoneda_collapses_to_the_diagonal_component(
                indices in prop::collection::vec(0_u32 .. 6, 1_usize .. 6),
                pick in 0_usize .. 64,
            ) {
                let diagram = Diagram::new(
                    indices
                        .iter()
                        .map(|index| (ct(NameRef::from(format!("P{index}").as_str())), ct(NameRef::from(format!("V{index}").as_str()))))
                        .collect::<Vec<_>>(),
                );
                let chosen = pick.checked_rem(diagram.entries.len()).expect("entries are nonempty");
                let object = diagram.entries[chosen].0.clone();
                let expected = ct(NameRef::from(format!("V{}", indices[chosen]).as_str()));
                prop_assert_eq!(
                    coyoneda_collapse(&object, &diagram),
                    Maybe::Present(&expected),
                    "the collapse reproduces F(a) for a carrier object"
                );
            }
    }

    // ---- the boundary theorem ----------------------------------------

    #[test]
    fn an_invertible_chain_cuts_unconditionally()
    {
        let (store, first, second) = invertible_chain(NameRef::from("A"));
        assert_eq!(
            first.joins_at, second.overlap.peak,
            "the invertible certificates share the ground seam"
        );
        let outcome = directed_cut(&first, &second, &store);
        assert!(
            bool::from(outcome.is_coherent()),
            "an all-invertible cut is admitted unconditionally (the boundary theorem)"
        );
        assert!(
            outcome
                .tracelet()
                .is_ok_and(|composite| bool::from(composite.replay(&store))),
            "the coherent composite replays the whole chain"
        );
    }

    proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]
    /// the invertible lane is never declined.
            #[test]
            fn the_invertible_lane_is_never_declined(
                prefix in proptest::sample::select(vec!["A", "B", "Q", "Zz", "mm"]),
            ) {
                let (store, first, second) = invertible_chain(NameRef::from(prefix));
                let outcome = directed_cut(&first, &second, &store);
                prop_assert!(
                    bool::from(outcome.is_coherent()),
                    "an invertible cut is coherent (never gated, never declined)"
                );
                prop_assert!(
                    !bool::from(outcome.is_declined()),
                    "the boundary theorem: the invertible lane is never declined"
                );
            }
    }

    /// A five-point **invertible** chain `p0 ~> … ~> p4` over `prefix`: two
    /// fused certificates sharing the ground seam `⟨p2 | ★⟩`, every
    /// participating cell invertible.
    /// # Specification
    /// trivial.
    fn invertible_chain(prefix: NameRef<'_>) -> (CellStore, Tracelet, Tracelet)
    {
        let prefix = prefix.as_ref();
        let point = |index: usize| format!("{prefix}{index}");
        let mut store = CellStore::new();
        let s01 = store.insert(invertible_ground_step(
            NameRef::from(point(0).as_str()),
            NameRef::from(point(1).as_str()),
        ));
        let s12 = store.insert(invertible_ground_step(
            NameRef::from(point(1).as_str()),
            NameRef::from(point(2).as_str()),
        ));
        let s23 = store.insert(invertible_ground_step(
            NameRef::from(point(2).as_str()),
            NameRef::from(point(3).as_str()),
        ));
        let s34 = store.insert(invertible_ground_step(
            NameRef::from(point(3).as_str()),
            NameRef::from(point(4).as_str()),
        ));
        let first = fused(&mut store, s01, s12);
        let second = fused(&mut store, s23, s34);
        (store, first, second)
    }

    /// An **invertible** ground step — provenance `DerivedByCompletion`, so the
    /// live metadata marks it an invertible joinability certificate.
    /// # Specification
    /// trivial.
    fn invertible_ground_step(
        from: NameRef<'_>,
        to: NameRef<'_>,
    ) -> Cell
    {
        Cell::new(
            ground_cmd(from),
            ground_cmd(to),
            Orientation::CompletionDerived,
            CellProvenance::DerivedByCompletion,
        )
    }

    /// The ground configuration `⟨name | ★⟩`.
    /// # Specification
    /// trivial.
    fn ground_cmd(name: NameRef<'_>) -> CmdPat
    {
        CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor(name.as_ref(), []),
            ConsPat::top(),
        )
    }

    #[test]
    fn a_mixed_variance_cycle_is_declined()
    {
        // Two certificates sharing a mixed-variance seam hole: not invertible,
        // so the cut consults the acyclicity gate and is declined.
        let mut store = CellStore::new();
        let u1 = store.insert(mixed_step(
            NameRef::from("r"),
            NameRef::from("dn1"),
            NameRef::from("mid1"),
        ));
        let v1 = store.insert(mixed_step(
            NameRef::from("s"),
            NameRef::from("mid1"),
            NameRef::from("up1"),
        ));
        let u2 = store.insert(mixed_step(
            NameRef::from("r"),
            NameRef::from("dn2"),
            NameRef::from("mid2"),
        ));
        let v2 = store.insert(mixed_step(
            NameRef::from("s"),
            NameRef::from("mid2"),
            NameRef::from("up2"),
        ));
        let a = fused(&mut store, u1, v1);
        let b = fused(&mut store, u2, v2);
        let outcome = directed_cut(&a, &b, &store);
        assert!(
            bool::from(outcome.is_declined()),
            "a mixed-variance cycle is declined by the acyclicity gate"
        );
        if let CutOutcome::Declined(ref obstruction) = outcome {
            assert!(
                matches!(obstruction, gandr_theory_decomposition_spaces::CompositionObstruction::Cycle { cycle } if cycle.len() >= 2),
                "the decline carries the variable-flow cycle"
            );
        }
        else {
            panic!("the mixed-variance cut must be declined");
        }
    }

    /// A mixed-variance step cell `⟨r | in(; r)⟩ ~> ⟨r | out(; r)⟩` — the name
    /// `r` is worn at both polarities, so the live derivation classifies it
    /// `Mixed`.
    /// # Specification
    /// trivial.
    fn mixed_step(
        hole: NameRef<'_>,
        in_op: NameRef<'_>,
        out_op: NameRef<'_>,
    ) -> Cell
    {
        Cell::new(
            CmdPat::cut(
                Polarity::Positive,
                ProdPat::meta(hole.as_ref()),
                ConsPat::op(in_op.as_ref(), [], ConsPat::meta(hole.as_ref())),
            ),
            CmdPat::cut(
                Polarity::Positive,
                ProdPat::meta(hole.as_ref()),
                ConsPat::op(out_op.as_ref(), [], ConsPat::meta(hole.as_ref())),
            ),
            Orientation::PolarityDerived,
            CellProvenance::SurfaceRule,
        )
    }

    /// The fused certificate of the composition overlap `left ∘ right`.
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

    /// The single composition overlap `left ∘ right` in `store`.
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

    /// The `Nat` signature.
    /// # Specification
    /// trivial.
    fn nat_sig() -> SignatureRef
    {
        SignatureRef::single(NominalId::new(0_u64.into(), "Nat"))
    }

    /// The (add-S) rule cell — `m`/`n` producer, `alpha` consumer.
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

    /// A variable reflected term.
    /// # Specification
    /// trivial.
    fn vt(name: NameRef<'_>) -> TermRef
    {
        TermRef::new(FreeTerm::var(name))
    }

    /// A nullary-constructor reflected term.
    /// # Specification
    /// trivial.
    fn ct(name: NameRef<'_>) -> TermRef
    {
        TermRef::new(FreeTerm::ctor(name, Vec::new()))
    }

    // ---- fixtures ---------------------------------------------------------

    /// A name.
    /// # Specification
    /// trivial.
    fn n(name: NameRef<'_>) -> Name
    {
        Name::from(name)
    }
}
