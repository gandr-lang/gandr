//! Public-API law witnesses.

#[cfg(test)]
mod tests
{
    use gandr_theory_cell_complexes::Cell;
    use gandr_theory_cell_complexes::CellId;
    use gandr_theory_cell_complexes::CellProvenance;
    use gandr_theory_cell_complexes::CellStore;
    use gandr_theory_cell_complexes::CmdPat;
    use gandr_theory_cell_complexes::ConsPat;
    use gandr_theory_cell_complexes::Orientation;
    use gandr_theory_cell_complexes::Polarity;
    use gandr_theory_cell_complexes::ProdPat;
    use gandr_theory_cell_complexes::Sym;
    use gandr_theory_cell_complexes::frame_defining_cell;
    use gandr_theory_coherent_resolutions::OverlapKind;
    use gandr_theory_coherent_resolutions::Tracelet;
    use gandr_theory_coherent_resolutions::derive_fused;
    use gandr_theory_coherent_resolutions::enumerate_overlaps;
    use gandr_theory_decomposition_spaces::compose_invertible;
    use gandr_theory_levitation::FreeTerm;
    use gandr_theory_levitation::Name;
    use gandr_theory_levitation::NameRef;
    use gandr_theory_levitation::NominalId;
    use gandr_theory_virtual_doctrines::CartesianLawError;
    use gandr_theory_virtual_doctrines::CellStoreVdc;
    use gandr_theory_virtual_doctrines::CheckError;
    use gandr_theory_virtual_doctrines::Checker;
    use gandr_theory_virtual_doctrines::Context;
    use gandr_theory_virtual_doctrines::Derivation;
    use gandr_theory_virtual_doctrines::DerivationId;
    use gandr_theory_virtual_doctrines::DerivationIndex;
    use gandr_theory_virtual_doctrines::DescTable;
    use gandr_theory_virtual_doctrines::IsoWitness;
    use gandr_theory_virtual_doctrines::Proterm;
    use gandr_theory_virtual_doctrines::Protype;
    use gandr_theory_virtual_doctrines::ProtypeIso;
    use gandr_theory_virtual_doctrines::Query;
    use gandr_theory_virtual_doctrines::RelationRef;
    use gandr_theory_virtual_doctrines::RewriteStepBudget;
    use gandr_theory_virtual_doctrines::SigMorphism;
    use gandr_theory_virtual_doctrines::SignatureRef;
    use gandr_theory_virtual_doctrines::TermRef;
    use gandr_theory_virtual_doctrines::Vdc as _;
    use gandr_theory_virtual_doctrines::WCartesianAction;

    use crate::require_present;

    // ---- the reflection rules law 1: tight category
    // ----------------------------------------

    #[test]
    fn tight_composition_is_associative_and_unital()
    {
        let descs = DescTable::<()>::new();
        let cells = CellStore::new();
        let vdc = CellStoreVdc::new(&descs, &cells);
        let sig = nat_sig();
        let id = vdc.id_tight(&sig);
        let a = SigMorphism::renaming(sig.clone(), sig.clone(), vec![(
            n(NameRef::from("x")),
            n(NameRef::from("y")),
        )]);
        let b = SigMorphism::renaming(sig.clone(), sig.clone(), vec![(
            n(NameRef::from("y")),
            n(NameRef::from("z")),
        )]);
        let c = SigMorphism::renaming(sig.clone(), sig, vec![(
            n(NameRef::from("z")),
            n(NameRef::from("w")),
        )]);
        // Unit: id is a two-sided unit.
        assert_eq!(vdc.comp_tight(&id, &a), a, "left unit");
        assert_eq!(vdc.comp_tight(&a, &id), a, "right unit");
        // Associativity: (a;b);c == a;(b;c).
        let left = vdc.comp_tight(&vdc.comp_tight(&a, &b), &c);
        let right = vdc.comp_tight(&a, &vdc.comp_tight(&b, &c));
        assert_eq!(left, right, "composition is associative");
        // The net function is x ↦ w.
        assert_eq!(
            "w",
            left.apply_name(NameRef::from("x")).as_ref(),
            "the composite renames x to w"
        );
    }

    // ---- the reflection rules law 3: restriction
    // -------------------------------------------

    #[test]
    fn restriction_by_identity_is_the_identity()
    {
        let descs = DescTable::<()>::new();
        let cells = CellStore::new();
        let vdc = CellStoreVdc::new(&descs, &cells);
        let sig = nat_sig();
        let r = rel(NameRef::from("R"), Vec::new());
        let id_src = vdc.id_tight(&sig);
        let id_tgt = vdc.id_tight(&sig);
        assert_eq!(
            vdc.restrict(&r, &id_src, &id_tgt),
            r,
            "R[id # id] = R (split by content-addressing)"
        );
    }

    #[test]
    fn restriction_composes()
    {
        let descs = DescTable::<()>::new();
        let cells = CellStore::new();
        let vdc = CellStoreVdc::new(&descs, &cells);
        let sig = nat_sig();
        let r = rel(NameRef::from("R"), Vec::new());
        let s = SigMorphism::renaming(sig.clone(), sig.clone(), vec![(
            n(NameRef::from("a")),
            n(NameRef::from("b")),
        )]);
        let s_prime = SigMorphism::renaming(sig.clone(), sig.clone(), vec![(
            n(NameRef::from("b")),
            n(NameRef::from("c")),
        )]);
        let t = SigMorphism::renaming(sig.clone(), sig.clone(), vec![(
            n(NameRef::from("p")),
            n(NameRef::from("q")),
        )]);
        let t_prime = SigMorphism::renaming(sig.clone(), sig, vec![(
            n(NameRef::from("q")),
            n(NameRef::from("r")),
        )]);
        // R[(s∘s') # (t∘t')] = R[s # t][s' # t'].
        let ss = vdc.comp_tight(&s_prime, &s);
        let tt = vdc.comp_tight(&t_prime, &t);
        let one_shot = vdc.restrict(&r, &ss, &tt);
        let staged = vdc.restrict(&vdc.restrict(&r, &s, &t), &s_prime, &t_prime);
        assert_eq!(one_shot, staged, "restriction is functorial");
    }

    // ---- the reflection rules law 2: cells compose multicategorically
    // ----------------------

    #[test]
    fn cell_grafting_matches_engine_composition()
    {
        let (store, ab, first, second) = ground_chain();
        let descs = DescTable::<()>::new();
        let vdc = CellStoreVdc::new(&descs, &store);
        assert_eq!(
            first.joins_at, second.overlap.peak,
            "the certificates share the ground seam ⟨C|★⟩"
        );
        let ra = rel(NameRef::from("RA"), vec![ab]);
        let rc = rel(NameRef::from("RC"), Vec::new());
        let re = rel(NameRef::from("RE"), Vec::new());
        let d_first = cert(first.clone(), ra.clone(), rc.clone());
        let d_second = cert(second.clone(), rc, re.clone());
        // compose_cells(outer = second, inners = [first]) grafts first then second.
        let graft = vdc.compose_cells(&d_second, &[d_first]);
        assert!(
            bool::from(graft.replays(&store)),
            "the grafted certificate replays A ~> E"
        );
        // compose(replay) ≡ replay(compose): the graft equals a direct engine
        // composite, up to replay-equivalence.
        let direct = cert(compose_invertible(&first, &second), ra, re);
        assert!(
            bool::from(vdc.cells_equal(&graft, &direct)),
            "grafting agrees with engine composition up to replay-equivalence"
        );
    }

    #[test]
    fn cell_grafting_is_unital_up_to_replay()
    {
        let (store, ab, first, _second) = ground_chain();
        let descs = DescTable::<()>::new();
        let vdc = CellStoreVdc::new(&descs, &store);
        let ra = rel(NameRef::from("RA"), vec![ab]);
        let rc = rel(NameRef::from("RC"), Vec::new());
        let d_first = cert(first, ra.clone(), rc);
        // compose_cells(c, [id_cell(dom)]) = c up to replay-equivalence.
        let unit = vdc.compose_cells(&d_first, &[vdc.id_cell(&ra)]);
        assert!(
            bool::from(vdc.cells_equal(&unit, &d_first)),
            "grafting the identity cell is a unit up to replay-equivalence"
        );
    }

    /// The linear ground chain `A ~> B ~> C ~> D ~> E`: two composable fused
    /// certificates sharing the ground seam `⟨C | ★⟩`.
    /// # Specification
    /// trivial.
    fn ground_chain() -> (CellStore, CellId, Tracelet, Tracelet)
    {
        let mut store = CellStore::new();
        let ab = store.insert(ground_step(NameRef::from("A"), NameRef::from("B")));
        let bc = store.insert(ground_step(NameRef::from("B"), NameRef::from("C")));
        let cd = store.insert(ground_step(NameRef::from("C"), NameRef::from("D")));
        let de = store.insert(ground_step(NameRef::from("D"), NameRef::from("E")));
        let first = fused(&mut store, ab, bc);
        let second = fused(&mut store, cd, de);
        (store, ab, first, second)
    }

    /// A ground step cell `⟨from | ★⟩ ~> ⟨to | ★⟩` over nullary constructors.
    /// # Specification
    /// trivial.
    fn ground_step(
        from: NameRef<'_>,
        to: NameRef<'_>,
    ) -> Cell
    {
        Cell::new(
            CmdPat::cut(
                Polarity::Positive,
                ProdPat::ctor(from.as_ref(), []),
                ConsPat::top(),
            ),
            CmdPat::cut(
                Polarity::Positive,
                ProdPat::ctor(to.as_ref(), []),
                ConsPat::top(),
            ),
            Orientation::PolarityDerived,
            CellProvenance::SurfaceRule,
        )
    }

    // ---- the reflection rules law 4: cartesian
    // ---------------------------------------------

    #[test]
    fn product_protype_is_well_formed_pointwise()
    {
        let (store, _tracelet) = peano_fused();
        let derivations: Vec<Derivation> = Vec::new();
        let checker = Checker::new(&derivations, &store);
        let sig = nat_sig();
        let ground = || TermRef::new(FreeTerm::ctor("Zero", Vec::new()));
        let half = Protype::path(sig, ground(), ground());
        let product = Protype::product(half.clone(), half);
        assert_eq!(
            Ok(()),
            checker.check_protype(&Context::new(), &product),
            "a product of well-formed protypes is well-formed pointwise"
        );
    }

    #[test]
    fn w_cartesian_action_preserves_projections_diagonal_and_structure()
    {
        let nat = nat_sig();
        let source = SignatureRef::product(Box::from([nat.clone(), nat.clone()]));
        let target = source.clone();
        let components = vec![
            SigMorphism::identity(nat.clone()),
            SigMorphism::identity(nat),
        ];
        let action = WCartesianAction::new(source, target, components);
        let witness = action
            .checked_witness()
            .expect("the componentwise identity action is cartesian");
        assert!(bool::from(witness.projections));
        assert!(bool::from(witness.diagonal));
        assert!(bool::from(witness.structure));
    }

    #[test]
    fn w_cartesian_action_rejects_projection_defect()
    {
        let first = SignatureRef::single(NominalId::new(0_u64.into(), "First"));
        let second = SignatureRef::single(NominalId::new(1_u64.into(), "Second"));
        let source = SignatureRef::product(Box::from([first, second.clone()]));
        let target = source.clone();
        let action = WCartesianAction::new(source, target, vec![
            SigMorphism::identity(second.clone()),
            SigMorphism::identity(second),
        ]);
        let Err(CartesianLawError::Violation(witness)) = action.checked_witness()
        else {
            panic!("a factor-boundary mismatch must fail the projection law");
        };
        assert!(!bool::from(witness.projections));
        assert!(bool::from(witness.diagonal));
        assert!(!bool::from(witness.structure));
    }

    #[test]
    fn w_cartesian_action_rejects_diagonal_defect()
    {
        let first = SignatureRef::single(NominalId::new(0_u64.into(), "First"));
        let second = SignatureRef::single(NominalId::new(1_u64.into(), "Second"));
        let source = SignatureRef::product(Box::from([first.clone(), second.clone()]));
        let target = source.clone();
        let action = WCartesianAction::new(source, target, vec![
            SigMorphism::identity(first),
            SigMorphism::identity(second),
        ]);
        let Err(CartesianLawError::Violation(witness)) = action.checked_witness()
        else {
            panic!("distinct component actions must fail diagonal preservation");
        };
        assert!(bool::from(witness.projections));
        assert!(!bool::from(witness.diagonal));
        assert!(!bool::from(witness.structure));
    }

    #[test]
    fn w_cartesian_action_rejects_product_structure_defect()
    {
        let nat = nat_sig();
        let source = SignatureRef::product(Box::from([nat.clone(), nat.clone()]));
        let target = SignatureRef::product(Box::from([nat.clone()]));
        let action = WCartesianAction::new(source, target, vec![
            SigMorphism::identity(nat.clone()),
            SigMorphism::identity(nat),
        ]);
        let Err(CartesianLawError::Violation(witness)) = action.checked_witness()
        else {
            panic!("a width-changing action must fail the cartesian structure law");
        };
        assert!(!bool::from(witness.projections));
        assert!(!bool::from(witness.diagonal));
        assert!(!bool::from(witness.structure));
    }

    // ---- the reflection rules law 5: units (path induction)
    // --------------------------------

    #[test]
    fn path_induction_folds_the_reduction_trace()
    {
        // ⟨Zero | Succ⁻(★)⟩ ~> ⟨Succ(Zero) | ★⟩ is a one-step path.
        let mut store = CellStore::new();
        store.insert(frame_defining_cell(&Sym::new("Succ")));
        let query = Query::new(&store);
        let start = CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Zero", []),
            ConsPat::frame("Succ", ConsPat::top()),
        );
        let path = query.path(&start, RewriteStepBudget::from(16_usize));
        // PathInd: base on refl (0 steps) plus one per reduction — the trace length.
        let steps = Query::induct(&path, 0_usize, |acc, _step| acc.saturating_add(1));
        assert_eq!(1, steps, "the induction counts the single reduction");
        assert_eq!(1, path.steps.len(), "the trace has one step");
    }

    #[test]
    fn a_path_query_trace_reproduces_its_target()
    {
        let mut store = CellStore::new();
        store.insert(frame_defining_cell(&Sym::new("Succ")));
        let query = Query::new(&store);
        let start = CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Zero", []),
            ConsPat::frame("Succ", ConsPat::top()),
        );
        let path = query.path(&start, RewriteStepBudget::from(16_usize));
        assert!(bool::from(path.complete), "a normal form is reached");
        let expected = CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Succ", [ProdPat::ctor("Zero", [])]),
            ConsPat::top(),
        );
        assert_eq!(
            path.target, expected,
            "the μ̃ reduction wrapped Zero in Succ"
        );
        // The trace re-runs to its target (external oracle: the engine's rewriting).
        assert!(
            bool::from(query.reaches(&start, &expected, RewriteStepBudget::from(16_usize))),
            "the recorded trace reaches the target"
        );
    }

    // ---- query surface: seam family + tabulator --------------------------

    #[test]
    fn the_seam_family_is_the_overlap_indexed_multi_sum()
    {
        // A non-linear seam: `plus` leaves a `g`-redex two consumers both match,
        // so the ⊙ family has two members, never one collapsed rule (the reflection
        // rules).
        let mut store = CellStore::new();
        let plus = store.insert(Cell::new(
            CmdPat::cut(
                Polarity::Positive,
                ProdPat::meta("k"),
                ConsPat::op("plus", [], ConsPat::meta("alpha")),
            ),
            CmdPat::cut(
                Polarity::Positive,
                ProdPat::meta("k"),
                ConsPat::op("g", [], ConsPat::meta("alpha")),
            ),
            Orientation::PolarityDerived,
            CellProvenance::SurfaceRule,
        ));
        let linear = store.insert(Cell::new(
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
        let nonlinear = store.insert(Cell::new(
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
        let query = Query::new(&store);
        let left = rel(NameRef::from("plus"), vec![plus]);
        let right = rel(NameRef::from("g"), vec![linear, nonlinear]);
        let family = query.seam_family(&left, &right);
        assert!(
            family.len() >= 2,
            "the g-seam composition is a multi-sum family, not a single rule"
        );
        // Every member re-derives its composite from the overlap (engine oracle).
        for member in &family {
            assert_eq!(member.left, plus, "each member is a plus∘g overlap");
        }
    }

    #[test]
    fn the_tabulator_projects_each_instance_to_its_two_faces()
    {
        let mut store = CellStore::new();
        let frame = store.insert(frame_defining_cell(&Sym::new("Succ")));
        let add = store.insert(add_s());
        let query = Query::new(&store);
        let relation = rel(NameRef::from("R"), vec![frame, add]);
        let table = query.tabulate(&relation);
        assert_eq!(2, table.rows.len(), "one instance per generating cell");
        // The two projections of each row are the cell's two faces.
        let frame_cell = require_present(store.get(frame));
        assert_eq!(table.rows[0].cell, frame, "first row is the frame cell");
        assert_eq!(
            &table.rows[0].left,
            frame_cell.lhs(),
            "left projection is the LHS"
        );
        assert_eq!(
            &table.rows[0].right,
            frame_cell.rhs(),
            "right projection is the RHS"
        );
        // A stale generator id contributes no row (boundary).
        let dangling = rel(NameRef::from("D"), vec![CellId::from(999_usize)]);
        assert!(
            query.tabulate(&dangling).rows.is_empty(),
            "a dangling generator id contributes no instance"
        );
    }

    // ---- per-rule checker soundness --------------------------------------

    #[test]
    fn compose_protype_requires_seam_agreement()
    {
        let store = CellStore::new();
        let derivations: Vec<Derivation> = Vec::new();
        let checker = Checker::new(&derivations, &store);
        let sig_a = SignatureRef::single(NominalId::new(0_u64.into(), "A"));
        let sig_b = SignatureRef::single(NominalId::new(1_u64.into(), "B"));
        let ground = || TermRef::new(FreeTerm::ctor("Zero", Vec::new()));
        // tgt(l) = A ≠ mid = B ⇒ ComposeSeamMismatch.
        let bad = Protype::compose(
            Protype::path(sig_a.clone(), ground(), ground()),
            sig_b.clone(),
            Protype::path(sig_b, ground(), ground()),
        );
        assert_eq!(
            Err(CheckError::ComposeSeamMismatch),
            checker.check_protype(&Context::new(), &bad),
            "a disagreeing seam is rejected"
        );
        // Agreeing seam (all A) ⇒ Ok.
        let good = Protype::compose(
            Protype::path(sig_a.clone(), ground(), ground()),
            sig_a.clone(),
            Protype::path(sig_a, ground(), ground()),
        );
        assert_eq!(
            Ok(()),
            checker.check_protype(&Context::new(), &good),
            "an agreeing seam is well-formed"
        );
    }

    #[test]
    fn a_term_over_an_undeclared_object_variable_is_rejected()
    {
        let store = CellStore::new();
        let derivations: Vec<Derivation> = Vec::new();
        let checker = Checker::new(&derivations, &store);
        let sig = nat_sig();
        let path = Protype::path(
            sig.clone(),
            TermRef::new(FreeTerm::var("x")),
            TermRef::new(FreeTerm::var("x")),
        );
        assert_eq!(
            checker.check_protype(&Context::new(), &path),
            Err(CheckError::UndeclaredTermVar(n(NameRef::from("x")))),
            "a term over an undeclared object variable is rejected"
        );
        let ctx = Context::new().with_dom(NameRef::from("x"), sig);
        assert_eq!(
            Ok(()),
            checker.check_protype(&ctx, &path),
            "declaring the variable admits the protype"
        );
    }

    #[test]
    fn a_replaying_certificate_checks_against_its_relation()
    {
        let (store, tracelet) = peano_fused();
        let relation = rel(NameRef::from("R"), Vec::new());
        let derivations = vec![cert(tracelet, relation.clone(), relation.clone())];
        let checker = Checker::new(&derivations, &store);
        let rel_protype = Protype::rel(
            relation,
            TermRef::new(FreeTerm::var("s")),
            TermRef::new(FreeTerm::var("t")),
        );
        assert_eq!(
            Ok(()),
            checker.check(
                &Context::new(),
                &[],
                &Proterm::cert(DerivationId::new(DerivationIndex::from(0_usize))),
                &rel_protype
            ),
            "a replaying certificate inhabits its engine-backed relation protype"
        );
    }

    #[test]
    fn a_non_replaying_certificate_is_rejected()
    {
        let (store, tracelet) = peano_fused();
        // Retarget the join to an unreachable term: the certificate no longer replays.
        let mut broken = tracelet;
        broken.joins_at = CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Nope", []),
            ConsPat::top(),
        );
        let relation = rel(NameRef::from("R"), Vec::new());
        let derivations = vec![cert(broken, relation.clone(), relation.clone())];
        let checker = Checker::new(&derivations, &store);
        let rel_protype = Protype::rel(
            relation,
            TermRef::new(FreeTerm::var("s")),
            TermRef::new(FreeTerm::var("t")),
        );
        assert_eq!(
            Err(CheckError::CertDoesNotReplay(DerivationId::new(
                DerivationIndex::from(0_usize)
            ))),
            checker.check(
                &Context::new(),
                &[],
                &Proterm::cert(DerivationId::new(DerivationIndex::from(0_usize))),
                &rel_protype
            ),
            "a non-replaying certificate is rejected "
        );
    }

    #[test]
    fn refl_off_the_diagonal_is_rejected()
    {
        let store = CellStore::new();
        let derivations: Vec<Derivation> = Vec::new();
        let checker = Checker::new(&derivations, &store);
        let sig = nat_sig();
        let refl_term = Proterm::refl(sig.clone(), TermRef::new(FreeTerm::var("a")));
        let off = Protype::path(
            sig.clone(),
            TermRef::new(FreeTerm::var("a")),
            TermRef::new(FreeTerm::var("b")),
        );
        assert_eq!(
            Err(CheckError::ReflOffDiagonal),
            checker.check(&Context::new(), &[], &refl_term, &off),
            "refl does not inhabit an off-diagonal path"
        );
        let diagonal = Protype::path(
            sig,
            TermRef::new(FreeTerm::var("a")),
            TermRef::new(FreeTerm::var("a")),
        );
        assert_eq!(
            Ok(()),
            checker.check(&Context::new(), &[], &refl_term, &diagonal),
            "refl inhabits the diagonal path"
        );
    }

    #[test]
    fn a_pair_checks_against_a_seam_composite()
    {
        let store = CellStore::new();
        let derivations: Vec<Derivation> = Vec::new();
        let checker = Checker::new(&derivations, &store);
        let sig = nat_sig();
        let diagonal = || {
            Protype::path(
                sig.clone(),
                TermRef::new(FreeTerm::var("a")),
                TermRef::new(FreeTerm::var("a")),
            )
        };
        let seam = Protype::compose(diagonal(), sig.clone(), diagonal());
        let refl_a = || Proterm::refl(sig.clone(), TermRef::new(FreeTerm::var("a")));
        let pair = Proterm::pair(refl_a(), TermRef::new(FreeTerm::var("a")), refl_a());
        assert_eq!(
            Ok(()),
            checker.check(&Context::new(), &[], &pair, &seam),
            "a pair of diagonal witnesses inhabits the seam composite"
        );
        // A pair checked against a non-seam protype is rejected.
        assert_eq!(
            Err(CheckError::ExpectedCompose),
            checker.check(&Context::new(), &[], &pair, &diagonal()),
            "a pair does not inhabit a non-seam protype"
        );
    }

    // ---- protype isomorphism certificate surface -------------------------

    #[test]
    fn a_reflexive_witness_pair_is_a_valid_iso()
    {
        let (store, base) = peano_fused();
        let refl = reflexive_cert(&base);
        let relation = rel(NameRef::from("R"), Vec::new());
        let d_refl = cert(refl, relation.clone(), relation);
        let witness = IsoWitness::new(d_refl.clone(), d_refl.clone());
        assert!(
            bool::from(witness.is_valid(&store)),
            "a reflexive witness pair round-trips to the identity "
        );
        // The syntactic surface resolves and agrees.
        let derivations = vec![d_refl.clone(), d_refl];
        let iso = ProtypeIso::new(
            Proterm::cert(DerivationId::new(DerivationIndex::from(0_usize))),
            Proterm::cert(DerivationId::new(DerivationIndex::from(1_usize))),
        );
        assert!(
            bool::from(iso.is_valid(&derivations, &store)),
            "the reflected ProtypeIso surface agrees with the witness"
        );
        // Composed in the invertible mode, the iso stays valid (the reflection rules).
        assert!(
            bool::from(witness.compose(&witness).is_valid(&store)),
            "invertible composition of valid isos is unconditional"
        );
    }

    #[test]
    fn the_inverse_of_a_valid_iso_is_valid()
    {
        let (store, base) = peano_fused();
        let d_refl = cert(
            reflexive_cert(&base),
            rel(NameRef::from("R"), Vec::new()),
            rel(NameRef::from("R"), Vec::new()),
        );
        let witness = IsoWitness::identity(d_refl);
        assert!(
            bool::from(witness.is_valid(&store)),
            "the identity iso is valid"
        );
        assert!(
            bool::from(witness.inverse().is_valid(&store)),
            "the inverse of a valid iso is valid (groupoid inverse law)"
        );
    }

    #[test]
    fn an_iso_whose_one_direction_fails_replay_is_rejected()
    {
        let (store, base) = peano_fused();
        let d_refl = cert(
            reflexive_cert(&base),
            rel(NameRef::from("R"), Vec::new()),
            rel(NameRef::from("R"), Vec::new()),
        );
        // A broken forward direction: retargeted join, neither reflexive nor replaying.
        let mut broken = base;
        broken.joins_at = CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Nope", []),
            ConsPat::top(),
        );
        let d_broken = cert(
            broken,
            rel(NameRef::from("R"), Vec::new()),
            rel(NameRef::from("R"), Vec::new()),
        );
        let witness = IsoWitness::new(d_broken, d_refl);
        assert!(
            !bool::from(witness.is_valid(&store)),
            "an iso whose one direction fails replay is rejected (protype-iso-replay-fail)"
        );
    }

    /// The `Nat` fusion store (`Succ⁻` frame + add-S rule) with the `frame ∘
    /// add` fused certificate.
    /// # Specification
    /// trivial.
    fn peano_fused() -> (CellStore, Tracelet)
    {
        let mut store = CellStore::new();
        let frame = store.insert(frame_defining_cell(&Sym::new("Succ")));
        let add = store.insert(add_s());
        let tracelet = fused(&mut store, frame, add);
        (store, tracelet)
    }

    /// The (add-S) rule cell `⟨Succ(m) | add(n; α)⟩ ~> ⟨m | add(n; Succ⁻(α))⟩`.
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

    /// The fused certificate of the composition overlap `left ∘ right`.
    /// # Specification
    /// trivial.
    fn fused(
        store: &mut CellStore,
        left: CellId,
        right: CellId,
    ) -> Tracelet
    {
        let overlap = enumerate_overlaps(store)
            .into_iter()
            .find(|candidate| {
                candidate.kind == OverlapKind::Composition
                    && candidate.left == left
                    && candidate.right == right
            })
            .expect("the composition overlap exists");
        derive_fused(&overlap, store)
            .expect("the fused cell is derived")
            .1
    }

    /// A reflexive certificate (`peak == joins_at`, empty paths) derived from a
    /// real tracelet's peak — it replays vacuously and is a groupoid identity.
    /// # Specification
    /// trivial.
    fn reflexive_cert(base: &Tracelet) -> Tracelet
    {
        let mut refl = base.clone();
        refl.path_a = Vec::new();
        refl.path_b = Vec::new();
        refl.joins_at = refl.overlap.peak.clone();
        refl
    }

    /// The `Nat` signature.
    /// # Specification
    /// trivial.
    fn nat_sig() -> SignatureRef
    {
        SignatureRef::single(NominalId::new(0_u64.into(), "Nat"))
    }

    /// A relation over the `Nat` signature named `name` with `generators`.
    /// # Specification
    /// trivial.
    fn rel(
        name: NameRef<'_>,
        generators: Vec<CellId>,
    ) -> RelationRef
    {
        RelationRef::new(name, nat_sig(), nat_sig(), generators.into_boxed_slice())
    }

    /// A single-relation `Cert` derivation with a chosen boundary.
    /// # Specification
    /// trivial.
    fn cert(
        tracelet: Tracelet,
        dom: RelationRef,
        cod: RelationRef,
    ) -> Derivation
    {
        Derivation::cert(tracelet, Box::from([dom]), cod)
    }

    // ---- fixtures ---------------------------------------------------------

    /// A signature name.
    /// # Specification
    /// trivial.
    fn n(name: NameRef<'_>) -> Name
    {
        Name::from(name)
    }
}
