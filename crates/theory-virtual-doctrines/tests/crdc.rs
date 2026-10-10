//! Public-API law witnesses.

#[cfg(test)]
mod tests
{
    use alloc::collections::BTreeSet;

    use anodized::spec;
    use gandr_theory_cell_complexes::Cat;
    use gandr_theory_cell_complexes::Cell;
    use gandr_theory_cell_complexes::CellAlphabet as _;
    use gandr_theory_cell_complexes::CellId;
    use gandr_theory_cell_complexes::CellProvenance;
    use gandr_theory_cell_complexes::CellStore;
    use gandr_theory_cell_complexes::CmdPat;
    use gandr_theory_cell_complexes::ConsPat;
    use gandr_theory_cell_complexes::ConsView;
    use gandr_theory_cell_complexes::MetaVar;
    use gandr_theory_cell_complexes::Node;
    use gandr_theory_cell_complexes::NodeRef;
    use gandr_theory_cell_complexes::Orientation;
    use gandr_theory_cell_complexes::Polarity;
    use gandr_theory_cell_complexes::Pos;
    use gandr_theory_cell_complexes::PositionStep;
    use gandr_theory_cell_complexes::ProdPat;
    use gandr_theory_cell_complexes::ProdView;
    use gandr_theory_cell_complexes::SequentAlphabet;
    use gandr_theory_cell_complexes::Subst;
    use gandr_theory_cell_complexes::Sym;
    use gandr_theory_cell_complexes::frame_defining_cell;
    use gandr_theory_cell_complexes::match_cmd;
    use gandr_theory_cell_complexes::splice_at;
    use gandr_theory_cell_complexes::subterm_at;
    use gandr_theory_cell_complexes::unify_cmd;
    use gandr_theory_coherent_resolutions::CellApp;
    use gandr_theory_coherent_resolutions::CompletionBudget;
    use gandr_theory_coherent_resolutions::NormalizationBudget;
    use gandr_theory_coherent_resolutions::Overlap;
    use gandr_theory_coherent_resolutions::OverlapKind;
    use gandr_theory_coherent_resolutions::OverlapRefusal;
    use gandr_theory_coherent_resolutions::PeakLegs;
    use gandr_theory_coherent_resolutions::Tracelet;
    use gandr_theory_coherent_resolutions::complete;
    use gandr_theory_coherent_resolutions::derive_fused;
    use gandr_theory_coherent_resolutions::enumerate_overlaps;
    use gandr_theory_coherent_resolutions::normalize;
    use gandr_theory_coherent_resolutions::peak_legs;
    use gandr_theory_coherent_resolutions::rewrite_at;
    use proptest::prelude::*;
    use quenchant_shape::shape::Maybe;

    use super::diagonal;
    use super::replay_path;
    use super::residue;
    use crate::require_present;

    /// The suite's proptest configuration: a modest native default so the
    /// merge wall stays fast, with `PROPTEST_CASES` overriding for longer
    /// shakeout runs (the `conformance.rs` posture).
    ///
    /// # Specification
    /// - ensures: the explicit suite count applies unless the environment
    ///   overrides it.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — the cospan laws check substitution images and
    ///   replayed conclusions; these local predicates check the returned
    ///   evidence, not completeness of enumeration.
    /// - witness: `tests::crdc::tests::composition_cospans_factor_uniquely`
    #[spec(ensures: |ret| std::env::var_os("PROPTEST_CASES").is_some() || ret.cases == cases.0)]
    fn crdc_config(cases: Cases) -> ProptestConfig
    {
        let mut config = ProptestConfig::default();
        if std::env::var_os("PROPTEST_CASES").is_none() {
            config.cases = cases.0;
        }
        config
    }

    /// A proptest case count (a semantic wrapper per the lint wall).
    #[derive(Clone, Copy, Debug)]
    #[repr(transparent)]
    struct Cases(u32);

    // ---- The suite surface (the component's T0 sketch, suite-local) ---------

    /// The outcome of factoring a match cospan through the enumerated family
    /// (axiom (i)'s `factor_cospan`; the sketch's `MultiSumFailure` is the two
    /// non-`Factored` variants).
    #[derive(Clone, Debug)]
    enum Factorization
    {
        /// Exactly one enumerated overlap admits a mediator: the family is
        /// multi-universal at this cospan.
        Factored
        {
            /// The overlap factored through.
            overlap: Box<Overlap>,
            /// The mediator: the unique substitution from the overlap's seam
            /// instance to the cospan's common instance.
            mediator: Subst,
        },
        /// No enumerated overlap admits a mediator, and the cospan is the
        /// **root diagonal** whose two legs provably coincide.
        ///
        /// The enumeration omits that peak deliberately, so this is the
        /// completeness claim's stated exception rather than a hole in it.
        /// It is a variant rather than a filter on the generator: a filtered
        /// case stops being exercised, and this one carries an obligation —
        /// the legs really do have to coincide, and the caller checks.
        TriviallyJoinable
        {
            /// The single term both contractions of the peak give.
            joined: Box<CmdPat>,
        },
        /// No enumerated overlap admits a mediator: enumeration is incomplete
        /// (a completeness bug).
        Incomplete,
        /// Several enumerated overlaps admit mediators: the family is not
        /// minimal (a universality bug).
        NonMinimal(Vec<Overlap>),
    }

    /// A cospan of matches: two pattern faces matched into one ground command.
    /// The left face is recoverable from the overlap and store; the right
    /// face is carried because the apartness-renamed face (what the unifier
    /// binds) needs the original to re-key the right leg.
    #[derive(Clone, Debug)]
    struct Cospan
    {
        /// The left leg: a match of the left face into `instance`.
        left_match: Subst,
        /// The right face (the right cell's `lhs`, before apartness renaming).
        right_face: CmdPat,
        /// The right leg: a match of `right_face` into `instance`.
        right_match: Subst,
        /// The common (ground) command both legs match into.
        instance: CmdPat,
    }

    /// A lifted cell — a member of a pushforward family (axioms (iv)/(v)).
    #[derive(Clone, Debug, Eq, PartialEq)]
    #[repr(transparent)]
    struct CellLift(Cell);

    /// The residue of a target pushforward on one ground instance: the
    /// post-normalization the composite still owes (Def 2.8's `post`; the
    /// as-built residue is a derivation — the record replay consumes — not a
    /// substitution, because the engine normalizes ground terms only).
    #[derive(Clone, Debug, Eq, PartialEq)]
    #[repr(transparent)]
    struct Residue
    {
        /// The owed normalization steps from the fired output to its normal
        /// form (empty when instantiation created no redexes).
        post: Vec<CellApp>,
    }

    /// Axiom (iii)'s factorization: a cell over a composed seam as a
    /// horizontal composition of per-frame cells plus the globular-iso
    /// witness (Remark 3.3 (11)).
    #[derive(Clone, Debug)]
    struct HorizontalFactorization
    {
        /// The per-frame cells, in firing order.
        frames: Vec<CellId>,
        /// The globular-iso witness: the fused ≡ two-step certificate.
        witness: Tracelet,
    }

    /// Whether two substitutions agree on a variable set (a suite-local
    /// verdict newtype; the lint wall forbids bare primitives in signatures).
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    #[repr(transparent)]
    struct Agreement(bool);

    impl From<bool> for Agreement
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

    impl From<Agreement> for bool
    {
        #[inline]
        /// Convert the boundary value without changing its representation.
        ///
        /// # Specification
        /// trivial.
        fn from(value: Agreement) -> Self
        {
            value.0
        }
    }

    /// A recursion-depth parameter for the generators (a semantic wrapper per
    /// the lint wall).
    #[derive(Clone, Copy, Debug)]
    #[repr(transparent)]
    struct Depth(u32);

    /// Number of Peano successors in generated Nat fixtures.
    #[repr(transparent)]
    #[derive(Clone, Copy)]
    struct NatSuccCount(u8);

    /// Proptest node budget for the pattern strategies.
    const PATTERN_NODE_BUDGET: u32 = 48;
    /// Proptest expected branch size for the pattern strategies.
    const PATTERN_BRANCH_SIZE: u32 = 3;
    /// Coin weight biasing generalization decisions toward sharing.
    const GENERALIZATION_COIN_WEIGHT: f64 = 0.25;
    /// Decision count drawn per generalization pair.
    const DECISION_COUNT: usize = 96;

    /// Factor `cospan` through the enumerated `family` (axiom (i)): find the
    /// overlaps of the ordered pair `(left, right)` of the given `kind` whose
    /// seam instance mediates the cospan, checking the leg factorizations.
    ///
    /// The mediator is computed by **matching** (one-sided) while the
    /// enumerated unifier comes from **unification** (two-sided) — the leg
    /// checks are a genuine cross-engine validation, not a restatement.
    ///
    /// Fragment scope: the composition reading assumes the cell-visible
    /// fragment's flat command grammar (the seam is always the root, so the
    /// unified pair is `(left.rhs(), right.lhs())` whole). A future fragment
    /// with nested commands must generalize the seam-instance computation
    /// to the subterm at `overlap.seam` — the row shape is unchanged.
    ///
    /// # Specification
    /// - ensures: a factored member has the requested faces and kind; the
    ///   diagonal exception is confluence of a cell with itself.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — the cospan laws check substitution images and
    ///   replayed conclusions; these local predicates check the returned
    ///   evidence, not completeness of enumeration.
    /// - witness: `tests::crdc::tests::composition_cospans_factor_uniquely`
    #[spec(ensures: |ret| match ret { Factorization::Factored { ref overlap, .. } => overlap.left == left && overlap.right == right && overlap.kind == kind, Factorization::TriviallyJoinable { .. } => left == right && kind == OverlapKind::Confluence, Factorization::NonMinimal(ref overlaps) => overlaps.len() > 1 && overlaps.iter().all(|overlap| overlap.left == left && overlap.right == right && overlap.kind == kind), Factorization::Incomplete => true })]
    fn factor_cospan(
        left: CellId,
        right: CellId,
        kind: OverlapKind,
        cospan: &Cospan,
        family: &[Overlap],
        store: &CellStore,
    ) -> Factorization
    {
        let mut mediators = Vec::new();
        for overlap in family {
            if overlap.kind != kind || overlap.left != left || overlap.right != right {
                continue;
            }
            let Ok(seam) = seam_instance(overlap, store)
            else {
                continue;
            };
            let Ok((left_pattern, right_pattern)) = overlap_faces(overlap, store)
            else {
                continue;
            };
            // The unifier must actually unify the two faces at the seam
            // instance (an engine self-check, not a suite assumption).
            if overlap.unifier.apply_cmd(left_pattern) != seam
                || overlap.unifier.apply_cmd(right_pattern) != seam
            {
                continue;
            }
            let mut mediator = Subst::new();
            if !bool::from(match_cmd(&seam, &cospan.instance, &mut mediator)) {
                continue;
            }
            let left_vars = cmd_vars(left_pattern);
            let left_composite = compose(&mediator, &overlap.unifier, &left_vars);
            if !bool::from(substs_agree_on(
                &cospan.left_match,
                &left_composite,
                &left_vars,
            )) {
                continue;
            }
            // The right leg reads against the original right cell; the
            // unifier binds the renamed cell — map the leg through the
            // apartness renaming (occurrence-parallel).
            let renamed_right_match =
                remap_match(&cospan.right_match, &cospan.right_face, right_pattern);
            let right_vars = cmd_vars(right_pattern);
            let right_composite = compose(&mediator, &overlap.unifier, &right_vars);
            if !bool::from(substs_agree_on(
                &renamed_right_match,
                &right_composite,
                &right_vars,
            )) {
                continue;
            }
            mediators.push((overlap.clone(), mediator));
        }
        match mediators.len() {
            | 0 => match trivially_joinable(left, right, kind, store) {
                | Maybe::Present(joined) => Factorization::TriviallyJoinable {
                    joined: Box::new(joined),
                },
                | Maybe::Absent(_) => Factorization::Incomplete,
            },
            | 1 => {
                let Some((overlap, mediator)) = mediators.pop()
                else {
                    return Factorization::Incomplete;
                };
                Factorization::Factored {
                    overlap: Box::new(overlap),
                    mediator,
                }
            },
            | _ => Factorization::NonMinimal(
                mediators.into_iter().map(|(overlap, _)| overlap).collect(),
            ),
        }
    }

    /// The completeness claim's exception, decided rather than assumed.
    ///
    /// An unmediated confluence cospan is the enumeration's stated exception
    /// exactly when its two cells are one cell — the root diagonal — and the
    /// peak's two contractions give the same term. **Both halves are checked
    /// here**, and the second is the one that matters: the exception's whole
    /// warrant is that the omitted peak joins in no steps, so if a diagonal
    /// peak ever had distinct reducts this returns `None` and the caller
    /// reports incompleteness, which is the loud failure the exception is
    /// entitled to be judged by.
    ///
    /// # Specification
    /// - ensures: only the issued, unifiable root diagonal with coincident
    ///   reducts yields a join.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — the cospan laws check substitution images and
    ///   replayed conclusions; these local predicates check the returned
    ///   evidence, not completeness of enumeration.
    /// - witness: `tests::crdc::tests::the_diagonal_cospan_of_a_deduplicated_cell_is_the_stated_exception`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(diagonal::Absent::NotDiagonal)) == (left != right || kind != OverlapKind::Confluence))]
    fn trivially_joinable(
        left: CellId,
        right: CellId,
        kind: OverlapKind,
        store: &CellStore,
    ) -> Maybe<CmdPat, diagonal::Absent>
    {
        if kind != OverlapKind::Confluence || left != right {
            return Maybe::Absent(diagonal::Absent::NotDiagonal);
        }
        let Maybe::Present(cell) = store.get(left)
        else {
            return Maybe::Absent(diagonal::Absent::Unissued);
        };
        let (renamed_lhs, renamed_rhs) =
            SequentAlphabet::rename_apart((cell.lhs(), cell.rhs()), (cell.lhs(), cell.rhs()));
        let mut unifier = Subst::new();
        if !bool::from(SequentAlphabet::unify_cmd(
            cell.lhs(),
            &renamed_lhs,
            &mut unifier,
        )) {
            return Maybe::Absent(diagonal::Absent::NotUnifiable);
        }
        if peak_legs::<SequentAlphabet>(&unifier, cell.rhs(), &renamed_rhs) != PeakLegs::Coincide {
            return Maybe::Absent(diagonal::Absent::DistinctReducts);
        }
        Maybe::Present(unifier.apply_cmd(cell.rhs()))
    }

    /// Axiom (iv): pushforward of a cell along a substitution on its input
    /// face — the discrete TRS[Σ] lift (apply the substitution to the whole
    /// cell), a singleton family.
    /// # Specification
    /// trivial.
    fn pushforward_src(
        cell: &Cell,
        sub: &Subst,
    ) -> Vec<CellLift>
    {
        vec![CellLift(lift_cell(cell, sub))]
    }

    /// Axiom (v): pushforward of a cell along a substitution on its output
    /// face — the same singleton lift; the residual part is per-instance (see
    /// [`residue_of`]) because the engine normalizes ground terms only.
    /// # Specification
    /// trivial.
    fn pushforward_tgt(
        cell: &Cell,
        sub: &Subst,
    ) -> Vec<CellLift>
    {
        vec![CellLift(lift_cell(cell, sub))]
    }

    /// The residue of a target pushforward on one ground `instance`: fire the
    /// lifted cell, then record the owed post-normalization (Def 2.8: lifts
    /// of `f` become lifts of `post ∘ f`).
    ///
    /// # Specification
    /// - ensures: the residue replays from the lifted contraction to the
    ///   returned normal form.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — the cospan laws check substitution images and
    ///   replayed conclusions; these local predicates check the returned
    ///   evidence, not completeness of enumeration.
    /// - witness: `tests::crdc::tests::residue_census_on_the_peano_family`
    #[spec(ensures: |ret| match ret { Maybe::Present((ref normal, ref residue)) => matches!(rewrite_at(&lifted.0, instance, &Pos::root()), Maybe::Present(ref fired) if matches!(run_path(store, fired, &residue.post), Maybe::Present(ref actual) if actual == normal)), Maybe::Absent(residue::Absent::DoesNotFire) => matches!(rewrite_at(&lifted.0, instance, &Pos::root()), Maybe::Absent(_)), Maybe::Absent(residue::Absent::Exhausted) => true })]
    fn residue_of(
        store: &CellStore,
        lifted: &CellLift,
        instance: &CmdPat,
        budget: NormalizationBudget,
    ) -> Maybe<(CmdPat, Residue), residue::Absent>
    {
        let Maybe::Present(fired) = rewrite_at(&lifted.0, instance, &Pos::root())
        else {
            return Maybe::Absent(residue::Absent::DoesNotFire);
        };
        let norm = normalize(store, &fired, budget);
        if bool::from(norm.exhausted) {
            return Maybe::Absent(residue::Absent::Exhausted);
        }
        Maybe::Present((norm.normal, Residue { post: norm.path }))
    }

    /// Axiom (iii): factor the fused cell of a composition overlap as the
    /// horizontal composition of its per-frame cells, witnessed by the
    /// fused ≡ two-step tracelet (the globular iso, strict on the boundary).
    ///
    /// # Specification
    /// - ensures: successful decomposition retains both ordered frames and a
    ///   replaying witness.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — the cospan laws check substitution images and
    ///   replayed conclusions; these local predicates check the returned
    ///   evidence, not completeness of enumeration.
    /// - witness: `tests::crdc::tests::two_step_composites_are_pro_representable`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |factor| factor.frames == [overlap.left, overlap.right] && bool::from(factor.witness.replay(store))))]
    fn decompose_horizontal(
        overlap: &Overlap,
        store: &mut CellStore,
    ) -> Result<HorizontalFactorization, OverlapRefusal>
    {
        let (_fused_id, witness) = derive_fused(overlap, store)?;
        Ok(HorizontalFactorization {
            frames: vec![overlap.left, overlap.right],
            witness,
        })
    }

    /// Instantiate a cell through a substitution (the TRS[Σ] lift).
    /// # Specification
    /// trivial.
    fn lift_cell(
        cell: &Cell,
        sub: &Subst,
    ) -> Cell
    {
        Cell::new(
            sub.apply_cmd(cell.lhs()),
            sub.apply_cmd(cell.rhs()),
            cell.orient(),
            cell.provenance(),
        )
    }

    // ---- Substitution algebra helpers ---------------------------------------

    /// The distinct metavariables of a command pattern.
    ///
    /// # Specification
    /// - ensures: the command metavariables occur once each; no absent variable
    ///   is introduced.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — the cospan laws check substitution images and
    ///   replayed conclusions; these local predicates check the returned
    ///   evidence, not completeness of enumeration.
    /// - witness: `tests::crdc::tests::composition_cospans_factor_uniquely`
    #[spec(ensures: |ret| cmd.metavars().all(|var| ret.contains(var)) && ret.iter().enumerate().all(|(index, var)| cmd.metavars().any(|found| found == var) && !ret.iter().skip(index.saturating_add(1)).any(|later| later == var)))]
    fn cmd_vars(cmd: &CmdPat) -> Vec<MetaVar>
    {
        let mut seen = BTreeSet::new();
        cmd.metavars()
            .filter(|mv| seen.insert(*mv))
            .cloned()
            .collect()
    }

    /// Apply a substitution to a producer metavariable read as a pattern.
    /// # Specification
    /// trivial.
    fn apply_prod_var(
        subst: &Subst,
        mv: &MetaVar,
    ) -> ProdPat
    {
        subst.apply_prod(&ProdPat::meta(mv.hole().clone()))
    }

    /// Apply a substitution to a consumer metavariable read as a pattern.
    /// # Specification
    /// trivial.
    fn apply_cons_var(
        subst: &Subst,
        mv: &MetaVar,
    ) -> ConsPat
    {
        subst.apply_cons(&ConsPat::meta(mv.hole().clone()))
    }

    /// The composite substitution `after ∘ before`, restricted to `vars`.
    ///
    /// # Specification
    /// - ensures: each listed variable maps through before and then after, at
    ///   its own polarity.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — the cospan laws check substitution images and
    ///   replayed conclusions; these local predicates check the returned
    ///   evidence, not completeness of enumeration.
    /// - witness: `tests::crdc::tests::composition_cospans_factor_uniquely`
    #[spec(ensures: |ret| vars.iter().all(|var| match var.cat() { Cat::Producer => apply_prod_var(&ret, var) == after.apply_prod(&apply_prod_var(before, var)), Cat::Consumer => apply_cons_var(&ret, var) == after.apply_cons(&apply_cons_var(before, var)) }))]
    fn compose(
        after: &Subst,
        before: &Subst,
        vars: &[MetaVar],
    ) -> Subst
    {
        let mut out = Subst::new();
        for mv in vars {
            match mv.cat() {
                | Cat::Producer => {
                    let image =
                        after.apply_prod(&before.apply_prod(&ProdPat::meta(mv.hole().clone())));
                    if image != ProdPat::meta(mv.hole().clone()) {
                        out.bind_prod(mv.clone(), image)
                            .expect("the fixture substitution is consistent");
                    }
                },
                | Cat::Consumer => {
                    let image =
                        after.apply_cons(&before.apply_cons(&ConsPat::meta(mv.hole().clone())));
                    if image != ConsPat::meta(mv.hole().clone()) {
                        out.bind_cons(mv.clone(), image)
                            .expect("the fixture substitution is consistent");
                    }
                },
            }
        }
        out
    }

    /// Whether two substitutions agree on every variable of `vars` (unbound
    /// reads as the identity).
    ///
    /// # Specification
    /// - ensures: agreement is equality of images at every listed variable and
    ///   its polarity.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — the cospan laws check substitution images and
    ///   replayed conclusions; these local predicates check the returned
    ///   evidence, not completeness of enumeration.
    /// - witness: `tests::crdc::tests::composition_cospans_factor_uniquely`
    #[spec(ensures: |ret| bool::from(ret) == vars.iter().all(|var| match var.cat() { Cat::Producer => apply_prod_var(a, var) == apply_prod_var(b, var), Cat::Consumer => apply_cons_var(a, var) == apply_cons_var(b, var) }))]
    fn substs_agree_on(
        a: &Subst,
        b: &Subst,
        vars: &[MetaVar],
    ) -> Agreement
    {
        Agreement::from(vars.iter().all(|mv| match mv.cat() {
            | Cat::Producer => apply_prod_var(a, mv) == apply_prod_var(b, mv),
            | Cat::Consumer => apply_cons_var(a, mv) == apply_cons_var(b, mv),
        }))
    }

    /// Re-key a match from `from_face`'s metavariables to `to_face`'s, where
    /// the faces are related by a structure-preserving renaming (occurrence-
    /// parallel metavariable lists).
    ///
    /// # Specification
    /// - ensures: bound images survive the occurrence-parallel renaming at both
    ///   polarities.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — the cospan laws check substitution images and
    ///   replayed conclusions; these local predicates check the returned
    ///   evidence, not completeness of enumeration.
    /// - witness: `tests::crdc::tests::composition_cospans_factor_uniquely`
    #[spec(ensures: |ret| from_face.metavars().zip(to_face.metavars()).all(|(from, to)| match from.cat() { Cat::Producer => matches!(m.get_prod(from), Maybe::Absent(_)) || ret.get_prod(to) == m.get_prod(from), Cat::Consumer => matches!(m.get_cons(from), Maybe::Absent(_)) || ret.get_cons(to) == m.get_cons(from) }))]
    fn remap_match(
        m: &Subst,
        from_face: &CmdPat,
        to_face: &CmdPat,
    ) -> Subst
    {
        let from_occurrences: Vec<_> = from_face.metavars().collect();
        let to_occurrences: Vec<_> = to_face.metavars().collect();
        debug_assert_eq!(
            from_occurrences.len(),
            to_occurrences.len(),
            "a structure-preserving renaming keeps occurrence lists parallel"
        );
        let mut out = Subst::new();
        for (from, to) in from_occurrences.into_iter().zip(to_occurrences) {
            match from.cat() {
                | Cat::Producer => {
                    if let Maybe::Present(image) = m.get_prod(from) {
                        out.bind_prod(to.clone(), image.clone())
                            .expect("the fixture substitution is consistent");
                    }
                },
                | Cat::Consumer => {
                    if let Maybe::Present(image) = m.get_cons(from) {
                        out.bind_cons(to.clone(), image.clone())
                            .expect("the fixture substitution is consistent");
                    }
                },
            }
        }
        out
    }

    /// The overlap's seam instance: the peak for confluence, the instantiated
    /// left right-hand side for composition.
    ///
    /// # Specification
    /// - ensures: confluence uses its peak; composition uses the left reduct.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — the cospan laws check substitution images and
    ///   replayed conclusions; these local predicates check the returned
    ///   evidence, not completeness of enumeration.
    /// - witness: `tests::crdc::tests::composition_cospans_factor_uniquely`
    #[spec(ensures: |ret| match overlap.kind { OverlapKind::Confluence => ret.as_ref() == Ok(&overlap.peak), OverlapKind::Composition => ret == overlap.left_reduct(store) })]
    fn seam_instance(
        overlap: &Overlap,
        store: &CellStore,
    ) -> Result<CmdPat, OverlapRefusal>
    {
        match overlap.kind {
            | OverlapKind::Confluence => Ok(overlap.peak.clone()),
            | OverlapKind::Composition => overlap.left_reduct(store),
        }
    }

    /// The two faces the overlap's unifier unifies: the left cell's `lhs`
    /// (confluence) or `rhs` (composition), and the renamed right cell's
    /// `lhs`.
    ///
    /// # Specification
    /// - ensures: the chosen left face and apartness-renamed right source form
    ///   the seam.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — the cospan laws check substitution images and
    ///   replayed conclusions; these local predicates check the returned
    ///   evidence, not completeness of enumeration.
    /// - witness: `tests::crdc::tests::composition_cospans_factor_uniquely`
    #[spec(ensures: |ret| match ret { Ok((left, right)) => right == overlap.right_renamed().lhs() && matches!(store.get(overlap.left), Maybe::Present(cell) if left == match overlap.kind { OverlapKind::Confluence => cell.lhs(), OverlapKind::Composition => cell.rhs() }), Err(_) => true })]
    fn overlap_faces<'store>(
        overlap: &'store Overlap,
        store: &'store CellStore,
    ) -> Result<(&'store CmdPat, &'store CmdPat), OverlapRefusal>
    {
        let left = store
            .get(overlap.left)
            .into_result(|_| OverlapRefusal::UnissuedCell(overlap.left))?;
        let face = match overlap.kind {
            | OverlapKind::Confluence => left.lhs(),
            | OverlapKind::Composition => left.rhs(),
        };
        Ok((face, overlap.right_renamed().lhs()))
    }

    /// Run a recorded path from `start`, firing each step by ground rewriting
    /// (the replay fold; `tracelet`'s own is private).
    ///
    /// # Specification
    /// - ensures: an empty recorded path is the identity on the starting
    ///   command.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — the cospan laws check substitution images and
    ///   replayed conclusions; these local predicates check the returned
    ///   evidence, not completeness of enumeration.
    /// - witness: `tests::crdc::tests::path_splittings_refine`
    #[spec(ensures: |ret| !path.is_empty() || matches!(ret, Maybe::Present(ref end) if end == start))]
    fn run_path(
        store: &CellStore,
        start: &CmdPat,
        path: &[CellApp],
    ) -> Maybe<CmdPat, replay_path::Absent>
    {
        let mut current = start.clone();
        for step in path {
            let Maybe::Present(cell) = store.get(step.cell)
            else {
                return Maybe::Absent(replay_path::Absent::UnissuedCell);
            };
            let Maybe::Present(next) = rewrite_at(cell, &current, &step.at)
            else {
                return Maybe::Absent(replay_path::Absent::DoesNotFire);
            };
            current = next;
        }
        Maybe::Present(current)
    }

    // ---- Generators ---------------------------------------------------------

    /// The metavariable pools generators draw from — the default pool and
    /// the apart pools (disjoint names, so no apartness renaming is needed
    /// across generated sides).
    #[derive(Clone, Copy, Debug)]
    enum Pool
    {
        /// The default pool: `x`,`y` producers; `a`,`b` consumers.
        Default,
        /// The second pool (`x2`, `y2`, `a2`, `b2`).
        Two,
        /// The third pool (`x3`, `y3`, `a3`, `b3`).
        Three,
    }

    impl Pool
    {
        /// The pool's metavariables (producers, consumers).
        /// # Specification
        /// trivial.
        fn vars(self) -> (Vec<MetaVar>, Vec<MetaVar>)
        {
            let suffix = match self {
                | Self::Default => "",
                | Self::Two => "2",
                | Self::Three => "3",
            };
            let prod = ["x", "y"]
                .into_iter()
                .map(|base| MetaVar::producer(format!("{base}{suffix}")))
                .collect();
            let cons = ["a", "b"]
                .into_iter()
                .map(|base| MetaVar::consumer(format!("{base}{suffix}")))
                .collect();
            (prod, cons)
        }
    }

    /// A producer-pattern leaf over the pool (metavariable-biased, so
    /// non-linear left-hand sides arise).
    ///
    /// # Specification
    /// - ensures: draws satisfy the fixture family described above; the
    ///   sampling distribution is unspecified.
    /// - executable: none — a strategy is a generator, not a generated value;
    ///   its support cannot be inspected without running a separate random
    ///   experiment.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the generated objects are checked by the consuming
    ///   laws; this does not establish exhaustive coverage of the generator's
    ///   support.
    /// - witness: `tests::crdc::tests::composition_cospans_factor_uniquely`
    fn prod_leaf(vars: &[MetaVar]) -> BoxedStrategy<ProdPat>
    {
        if vars.is_empty() {
            prop_oneof![
                Just(ProdPat::ctor("Zero", [])),
                Just(ProdPat::ctor("Nil", [])),
            ]
            .boxed()
        }
        else {
            prop_oneof![
                Just(ProdPat::ctor("Zero", [])),
                Just(ProdPat::ctor("Nil", [])),
                proptest::sample::select(vars.to_vec())
                    .prop_map(|var| ProdPat::meta(var.hole().clone())),
                proptest::sample::select(vars.to_vec())
                    .prop_map(|var| ProdPat::meta(var.hole().clone())),
            ]
            .boxed()
        }
    }

    /// Producer patterns over the pool, depth-capped (`Zero`/`Nil` nullary,
    /// `Succ` unary, `Cons` binary).
    ///
    /// # Specification
    /// - ensures: draws satisfy the fixture family described above; the
    ///   sampling distribution is unspecified.
    /// - executable: none — a strategy is a generator, not a generated value;
    ///   its support cannot be inspected without running a separate random
    ///   experiment.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the generated objects are checked by the consuming
    ///   laws; this does not establish exhaustive coverage of the generator's
    ///   support.
    /// - witness: `tests::crdc::tests::composition_cospans_factor_uniquely`
    fn arb_prodpat(
        vars: &[MetaVar],
        depth: Depth,
    ) -> BoxedStrategy<ProdPat>
    {
        prod_leaf(vars)
            .prop_recursive(depth.0, PATTERN_NODE_BUDGET, PATTERN_BRANCH_SIZE, |inner| {
                prop_oneof![
                    inner.clone().prop_map(|p| ProdPat::ctor("Succ", [p])),
                    (inner.clone(), inner)
                        .prop_map(|(l, r)| ProdPat::ctor("Cons", <[ProdPat; 2]>::from((l, r)))),
                ]
            })
            .boxed()
    }

    /// Consumer patterns over the pool, depth-capped (`★`, metavariables, the
    /// `add`/`f` operation frames, and the `Succ`/`Cons` return-side frames).
    ///
    /// # Specification
    /// - ensures: draws satisfy the fixture family described above; the
    ///   sampling distribution is unspecified.
    /// - executable: none — a strategy is a generator, not a generated value;
    ///   its support cannot be inspected without running a separate random
    ///   experiment.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the generated objects are checked by the consuming
    ///   laws; this does not establish exhaustive coverage of the generator's
    ///   support.
    /// - witness: `tests::crdc::tests::composition_cospans_factor_uniquely`
    fn arb_conspat(
        pvars: &[MetaVar],
        cvars: &[MetaVar],
        depth: Depth,
    ) -> BoxedStrategy<ConsPat>
    {
        let leaf = if cvars.is_empty() {
            Just(ConsPat::top()).boxed()
        }
        else {
            prop_oneof![
                Just(ConsPat::top()),
                proptest::sample::select(cvars.to_vec())
                    .prop_map(|var| ConsPat::meta(var.hole().clone())),
                proptest::sample::select(cvars.to_vec())
                    .prop_map(|var| ConsPat::meta(var.hole().clone())),
            ]
            .boxed()
        };
        let arg_vars = pvars.to_vec();
        leaf.prop_recursive(
            depth.0,
            PATTERN_NODE_BUDGET,
            PATTERN_BRANCH_SIZE,
            move |inner| {
                let arg = arb_prodpat(&arg_vars, Depth(2));
                prop_oneof![
                    inner.clone().prop_map(|ret| ConsPat::frame("Succ", ret)),
                    inner.clone().prop_map(|ret| ConsPat::frame("Cons", ret)),
                    (inner, arg.clone()).prop_map(|(ret, a)| ConsPat::op("add", [a], ret)),
                    arg.prop_map(|a| ConsPat::op("add", [a], ConsPat::top())),
                    Just(ConsPat::op("f", [], ConsPat::top())),
                ]
            },
        )
        .boxed()
    }

    /// A pool with each metavariable of the pool independently present.
    ///
    /// # Specification
    /// - ensures: draws satisfy the fixture family described above; the
    ///   sampling distribution is unspecified.
    /// - executable: none — a strategy is a generator, not a generated value;
    ///   its support cannot be inspected without running a separate random
    ///   experiment.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the generated objects are checked by the consuming
    ///   laws; this does not establish exhaustive coverage of the generator's
    ///   support.
    /// - witness: `tests::crdc::tests::composition_cospans_factor_uniquely`
    fn arb_pool_over(pool: Pool) -> BoxedStrategy<(Vec<MetaVar>, Vec<MetaVar>)>
    {
        proptest::collection::vec(any::<bool>(), 4)
            .prop_map(move |bits| {
                let (prods, conss) = pool.vars();
                let mut all = prods;
                all.extend(conss);
                let kept: Vec<MetaVar> = all
                    .into_iter()
                    .zip(bits)
                    .filter_map(|(mv, keep)| keep.then_some(mv))
                    .collect();
                split_vars(&kept)
            })
            .boxed()
    }

    /// Split a variable set by category.
    ///
    /// # Specification
    /// - ensures: the output partitions the input variables by producer and
    ///   consumer polarity.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — the cospan laws check substitution images and
    ///   replayed conclusions; these local predicates check the returned
    ///   evidence, not completeness of enumeration.
    /// - witness: `tests::crdc::tests::composition_cospans_factor_uniquely`
    #[spec(ensures: |ret| ret.0.iter().eq(vars.iter().filter(|var| var.cat() == Cat::Producer)) && ret.1.iter().eq(vars.iter().filter(|var| var.cat() == Cat::Consumer)))]
    fn split_vars(vars: &[MetaVar]) -> (Vec<MetaVar>, Vec<MetaVar>)
    {
        let prod = vars
            .iter()
            .filter(|mv| mv.cat() == Cat::Producer)
            .cloned()
            .collect();
        let cons = vars
            .iter()
            .filter(|mv| mv.cat() == Cat::Consumer)
            .cloned()
            .collect();
        (prod, cons)
    }

    /// A positive-polarity command pattern over the pool.
    ///
    /// # Specification
    /// - ensures: draws satisfy the fixture family described above; the
    ///   sampling distribution is unspecified.
    /// - executable: none — a strategy is a generator, not a generated value;
    ///   its support cannot be inspected without running a separate random
    ///   experiment.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the generated objects are checked by the consuming
    ///   laws; this does not establish exhaustive coverage of the generator's
    ///   support.
    /// - witness: `tests::crdc::tests::composition_cospans_factor_uniquely`
    fn arb_cmdpat(
        pvars: &[MetaVar],
        cvars: &[MetaVar],
        depth: Depth,
    ) -> BoxedStrategy<CmdPat>
    {
        (arb_prodpat(pvars, depth), arb_conspat(pvars, cvars, depth))
            .prop_map(|(prod, cons)| CmdPat::cut(Polarity::Positive, prod, cons))
            .boxed()
    }

    /// A generated surface-rule cell over the pool: positive polarity,
    /// right-hand-side variables drawn from the left-hand side's (the
    /// rewriting discipline, so generated cells can fire), non-linear
    /// left-hand sides admitted.
    ///
    /// # Specification
    /// - ensures: draws satisfy the fixture family described above; the
    ///   sampling distribution is unspecified.
    /// - executable: none — a strategy is a generator, not a generated value;
    ///   its support cannot be inspected without running a separate random
    ///   experiment.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the generated objects are checked by the consuming
    ///   laws; this does not establish exhaustive coverage of the generator's
    ///   support.
    /// - witness: `tests::crdc::tests::composition_cospans_factor_uniquely`
    fn arb_cell_over(pool: Pool) -> BoxedStrategy<Cell>
    {
        arb_pool_over(pool)
            .prop_flat_map(|(pvars, cvars)| {
                (
                    arb_prodpat(&pvars, Depth(3)),
                    arb_conspat(&pvars, &cvars, Depth(3)),
                )
            })
            .prop_flat_map(|(prod, cons)| {
                let lhs = CmdPat::cut(Polarity::Positive, prod, cons);
                let (pvars, cvars) = split_vars(&cmd_vars(&lhs));
                (
                    arb_prodpat(&pvars, Depth(2)),
                    arb_conspat(&pvars, &cvars, Depth(2)),
                )
                    .prop_map(move |(p, c)| (lhs.clone(), p, c))
            })
            .prop_map(|(lhs, prod, cons)| {
                let rhs = CmdPat::cut(Polarity::Positive, prod, cons);
                Cell::new(
                    lhs,
                    rhs,
                    Orientation::PolarityDerived,
                    CellProvenance::SurfaceRule,
                )
            })
            .boxed()
    }

    /// A generated surface-rule cell over the default pool.
    /// # Specification
    /// trivial.
    fn arb_cell() -> BoxedStrategy<Cell>
    {
        arb_cell_over(Pool::Default)
    }

    /// A substitution binding each variable of `vars` to a pattern over the
    /// target pools (empty target pools give a grounding substitution).
    ///
    /// # Specification
    /// - ensures: draws satisfy the fixture family described above; the
    ///   sampling distribution is unspecified.
    /// - executable: none — a strategy is a generator, not a generated value;
    ///   its support cannot be inspected without running a separate random
    ///   experiment.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the generated objects are checked by the consuming
    ///   laws; this does not establish exhaustive coverage of the generator's
    ///   support.
    /// - witness: `tests::crdc::tests::composition_cospans_factor_uniquely`
    fn arb_subst(
        vars: Vec<MetaVar>,
        ppool: &[MetaVar],
        cpool: &[MetaVar],
    ) -> BoxedStrategy<Subst>
    {
        let mut strategy = Just(Subst::new()).boxed();
        for mv in vars {
            strategy = match mv.cat() {
                | Cat::Producer => (strategy, arb_prodpat(ppool, Depth(2)))
                    .prop_map(move |(mut subst, image)| {
                        subst
                            .bind_prod(mv.clone(), image)
                            .expect("the fixture substitution is consistent");
                        subst
                    })
                    .boxed(),
                | Cat::Consumer => (strategy, arb_conspat(ppool, cpool, Depth(2)))
                    .prop_map(move |(mut subst, image)| {
                        subst
                            .bind_cons(mv.clone(), image)
                            .expect("the fixture substitution is consistent");
                        subst
                    })
                    .boxed(),
            };
        }
        strategy
    }

    /// A grounding substitution for `vars` (binds every variable to a
    /// metavariable-free pattern).
    /// # Specification
    /// trivial.
    fn arb_ground_subst(vars: Vec<MetaVar>) -> BoxedStrategy<Subst>
    {
        arb_subst(vars, &[], &[])
    }

    /// A generated cell pair plus a grounding of the pair's seam variables —
    /// the directed cospan cases (every enumerated overlap of the ordered
    /// pair gets its cospan factored).
    ///
    /// # Specification
    /// - ensures: draws satisfy the fixture family described above; the
    ///   sampling distribution is unspecified.
    /// - executable: none — a strategy is a generator, not a generated value;
    ///   its support cannot be inspected without running a separate random
    ///   experiment.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the generated objects are checked by the consuming
    ///   laws; this does not establish exhaustive coverage of the generator's
    ///   support.
    /// - witness: `tests::crdc::tests::composition_cospans_factor_uniquely`
    fn cospan_case(kind: OverlapKind) -> BoxedStrategy<(Cell, Cell, Subst)>
    {
        unifiable_cells(kind)
            .prop_flat_map(move |(a, b)| {
                let mut store = CellStore::new();
                let a_id = store.insert(a.clone());
                let b_id = store.insert(b.clone());
                let family = enumerate_overlaps(&store);
                let mut seam_vars = Vec::new();
                for overlap in &family {
                    if overlap.kind != kind || overlap.left != a_id || overlap.right != b_id {
                        continue;
                    }
                    if let Ok(seam) = seam_instance(overlap, &store) {
                        seam_vars.extend(cmd_vars(&seam));
                    }
                    if kind == OverlapKind::Composition {
                        seam_vars.extend(cmd_vars(&overlap.peak));
                    }
                }
                let mut dedup = BTreeSet::new();
                let seam_vars: Vec<MetaVar> = seam_vars
                    .into_iter()
                    .filter(|mv| dedup.insert(mv.clone()))
                    .collect();
                arb_ground_subst(seam_vars).prop_map(move |tau| (a.clone(), b.clone(), tau))
            })
            .boxed()
    }

    /// A cell pair whose designated faces are unifiable by construction (two
    /// independent generalizations of one seam): for confluence the two
    /// left-hand sides, for composition the left cell's right-hand side and
    /// the right cell's left-hand side.
    ///
    /// # Specification
    /// - ensures: draws satisfy the fixture family described above; the
    ///   sampling distribution is unspecified.
    /// - executable: none — a strategy is a generator, not a generated value;
    ///   its support cannot be inspected without running a separate random
    ///   experiment.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the generated objects are checked by the consuming
    ///   laws; this does not establish exhaustive coverage of the generator's
    ///   support.
    /// - witness: `tests::crdc::tests::composition_cospans_factor_uniquely`
    fn unifiable_cells(kind: OverlapKind) -> BoxedStrategy<(Cell, Cell)>
    {
        unifiable_faces()
            .prop_flat_map(move |(fa, fb)| match kind {
                | OverlapKind::Confluence => (cell_with_lhs(fa), cell_with_lhs(fb))
                    .prop_map(|(a, b)| (a, b))
                    .boxed(),
                | OverlapKind::Composition => (cell_with_rhs(fa), cell_with_lhs(fb))
                    .prop_map(|(a, b)| (a, b))
                    .boxed(),
            })
            .boxed()
    }

    /// A unifiable pair of command faces: independent generalizations of one
    /// generated seam, so the seam is a common instance and unification must
    /// succeed.
    ///
    /// # Specification
    /// - ensures: draws satisfy the fixture family described above; the
    ///   sampling distribution is unspecified.
    /// - executable: none — a strategy is a generator, not a generated value;
    ///   its support cannot be inspected without running a separate random
    ///   experiment.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the generated objects are checked by the consuming
    ///   laws; this does not establish exhaustive coverage of the generator's
    ///   support.
    /// - witness: `tests::crdc::tests::composition_cospans_factor_uniquely`
    fn unifiable_faces() -> BoxedStrategy<(CmdPat, CmdPat)>
    {
        let decisions = proptest::collection::vec(
            prop::bool::weighted(GENERALIZATION_COIN_WEIGHT),
            DECISION_COUNT,
        );
        arb_pool_over(Pool::Default)
            .prop_flat_map(move |(pvars, cvars)| {
                (
                    arb_prodpat(&pvars, Depth(3)),
                    arb_conspat(&pvars, &cvars, Depth(3)),
                    decisions.clone(),
                    decisions.clone(),
                )
            })
            .prop_map(|(prod, cons, d1, d2)| {
                let seam = CmdPat::cut(Polarity::Positive, prod, cons);
                (
                    generalize_cmd(&seam, GenPrefix::Left, &Decisions(d1)),
                    generalize_cmd(&seam, GenPrefix::Right, &Decisions(d2)),
                )
            })
            .boxed()
    }

    /// A cell with the given left-hand side; the right-hand side draws its
    /// variables from the left's (the rewriting discipline).
    ///
    /// # Specification
    /// - ensures: draws satisfy the fixture family described above; the
    ///   sampling distribution is unspecified.
    /// - executable: none — a strategy is a generator, not a generated value;
    ///   its support cannot be inspected without running a separate random
    ///   experiment.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the generated objects are checked by the consuming
    ///   laws; this does not establish exhaustive coverage of the generator's
    ///   support.
    /// - witness: `tests::crdc::tests::composition_cospans_factor_uniquely`
    fn cell_with_lhs(face: CmdPat) -> BoxedStrategy<Cell>
    {
        let (pvars, cvars) = split_vars(&cmd_vars(&face));
        (
            arb_prodpat(&pvars, Depth(2)),
            arb_conspat(&pvars, &cvars, Depth(2)),
        )
            .prop_map(move |(prod, cons)| {
                let rhs = CmdPat::cut(Polarity::Positive, prod, cons);
                Cell::new(
                    face.clone(),
                    rhs,
                    Orientation::PolarityDerived,
                    CellProvenance::SurfaceRule,
                )
            })
            .boxed()
    }

    /// A cell with the given right-hand side; the left-hand side mentions
    /// every variable of the right (the rewriting discipline, guaranteed by
    /// construction: producer variables folded into a `Cons` chain, the
    /// consumer variable forced as the return tail — a consumer spine carries
    /// at most one metavariable by grammar).
    ///
    /// # Specification
    /// - ensures: draws satisfy the fixture family described above; the
    ///   sampling distribution is unspecified.
    /// - executable: none — a strategy is a generator, not a generated value;
    ///   its support cannot be inspected without running a separate random
    ///   experiment.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the generated objects are checked by the consuming
    ///   laws; this does not establish exhaustive coverage of the generator's
    ///   support.
    /// - witness: `tests::crdc::tests::composition_cospans_factor_uniquely`
    fn cell_with_rhs(face: CmdPat) -> BoxedStrategy<Cell>
    {
        let (pvars, cvars) = split_vars(&cmd_vars(&face));
        let cons_tail = cvars.first().cloned();
        (arb_prodpat(&pvars, Depth(1)), arb_prodpat(&pvars, Depth(1)))
            .prop_map(move |(chain_base, arg)| {
                let mut prod = chain_base;
                for var in &pvars {
                    prod = ProdPat::ctor("Cons", [ProdPat::meta(var.hole().clone()), prod]);
                }
                let cons = match cons_tail.as_ref() {
                    | Some(tail) => ConsPat::op("add", [arg], ConsPat::meta(tail.hole().clone())),
                    | None => ConsPat::op("add", [arg], ConsPat::top()),
                };
                Cell::new(
                    CmdPat::cut(Polarity::Positive, prod, cons),
                    face.clone(),
                    Orientation::PolarityDerived,
                    CellProvenance::SurfaceRule,
                )
            })
            .boxed()
    }

    /// Every non-root position of a command pattern, shallowest first (an
    /// iterative worklist; [`generalize_cmd`] consumes it).
    ///
    /// # Specification
    /// - ensures: every returned position denotes a non-root node of the
    ///   original command.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — the cospan laws check substitution images and
    ///   replayed conclusions; these local predicates check the returned
    ///   evidence, not completeness of enumeration.
    /// - witness: `tests::crdc::tests::unification_computes_pattern_pullbacks`
    #[spec(ensures: |ret| ret.iter().all(|pos| *pos != Pos::root() && matches!(subterm_at(NodeRef::Cmd(cmd), pos), Maybe::Present(_))))]
    fn all_positions(cmd: &CmdPat) -> Vec<Pos>
    {
        let mut out = Vec::new();
        let mut work = vec![(Pos::root(), NodeRef::Cmd(cmd))];
        while let Some((pos, node)) = work.pop() {
            if !pos.steps().is_empty() {
                out.push(pos.clone());
            }
            match node {
                | NodeRef::Cmd(cmd) => {
                    work.push((
                        pos.child(PositionStep::from(0_usize)),
                        NodeRef::Prod(cmd.producer().to_ref()),
                    ));
                    work.push((
                        pos.child(PositionStep::from(1_usize)),
                        NodeRef::Cons(cmd.consumer().to_ref()),
                    ));
                },
                | NodeRef::Prod(prod) => {
                    if let ProdView::Ctor { args, .. } = prod.view() {
                        for (index, arg) in args.enumerate() {
                            work.push((pos.child(PositionStep::from(index)), NodeRef::Prod(arg)));
                        }
                    }
                },
                | NodeRef::Cons(cons) => match cons.view() {
                    | ConsView::Op { args, ret, .. } => {
                        let arity = args.len();
                        for (index, arg) in args.enumerate() {
                            work.push((pos.child(PositionStep::from(index)), NodeRef::Prod(arg)));
                        }
                        work.push((pos.child(PositionStep::from(arity)), NodeRef::Cons(ret)));
                    },
                    | ConsView::Frame { ret, .. } => {
                        work.push((pos.child(PositionStep::from(0_usize)), NodeRef::Cons(ret)));
                    },
                    | ConsView::Meta(_) | ConsView::Top => {},
                },
            }
        }
        out.sort_unstable_by_key(|pos| pos.steps().len());
        out
    }

    /// A generalization prefix for the fresh metavariable names
    /// [`generalize_cmd`] mints (disjoint across faces and sides).
    #[derive(Clone, Copy, Debug)]
    enum GenPrefix
    {
        /// The left generalization of a seam pair.
        Left,
        /// The right generalization of a seam pair.
        Right,
        /// The left-face generalization of a cell intersection partner.
        LhsFace,
        /// The right-face generalization of a cell intersection partner.
        RhsFace,
    }

    /// A decision vector for [`generalize_cmd`] (one bit per position).
    #[derive(Clone, Debug)]
    #[repr(transparent)]
    struct Decisions(Vec<bool>);

    /// Generalize a command pattern: replace a decision-driven subset of its
    /// subtrees by fresh metavariables (iterative, via the position
    /// machinery; the seam stays a common instance of the result).
    ///
    /// # Specification
    /// - ensures: the original command is a match instance of the
    ///   generalization.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — the cospan laws check substitution images and
    ///   replayed conclusions; these local predicates check the returned
    ///   evidence, not completeness of enumeration.
    /// - witness: `tests::crdc::tests::unification_computes_pattern_pullbacks`
    #[spec(requires: !decisions.0.is_empty(), ensures: |ret| bool::from(match_cmd(&ret, cmd, &mut Subst::new())))]
    fn generalize_cmd(
        cmd: &CmdPat,
        prefix: GenPrefix,
        decisions: &Decisions,
    ) -> CmdPat
    {
        let stem = match prefix {
            | GenPrefix::Left => "g2",
            | GenPrefix::Right => "g3",
            | GenPrefix::LhsFace => "g2l",
            | GenPrefix::RhsFace => "g2r",
        };
        let mut out = cmd.clone();
        let mut replaced: Vec<Pos> = Vec::new();
        let mut fresh = 0_usize;
        let mut cursor = 0_usize;
        for pos in all_positions(cmd) {
            if replaced.iter().any(|r| pos.steps().starts_with(r.steps())) {
                continue;
            }
            let replace = decisions.0[cursor
                .checked_rem(decisions.0.len())
                .expect("decisions are nonempty")];
            cursor = cursor.saturating_add(1);
            if !replace {
                continue;
            }
            let Maybe::Present(node) = subterm_at(NodeRef::Cmd(&out), &pos)
            else {
                continue;
            };
            let replacement = match node {
                | NodeRef::Prod(_) => Node::Prod(ProdPat::meta(format!("{stem}p{fresh}"))),
                | NodeRef::Cons(_) => Node::Cons(ConsPat::meta(format!("{stem}c{fresh}"))),
                | _ => continue,
            };
            fresh = fresh.saturating_add(1);
            let Ok(Node::Cmd(rebuilt)) = splice_at(NodeRef::Cmd(&out), &pos, replacement)
            else {
                continue;
            };
            out = rebuilt;
            replaced.push(pos);
        }
        out
    }

    /// The Peano `n` as `Succ^count(Zero)`.
    /// # Specification
    /// trivial.
    fn nat_of(count: NatSuccCount) -> ProdPat
    {
        let mut acc = ProdPat::ctor("Zero", []);
        for _ in 0 .. count.0 {
            acc = ProdPat::ctor("Succ", [acc]);
        }
        acc
    }

    /// (add-Z): `⟨Zero | add(n; α)⟩ ~> ⟨n | α⟩`.
    /// # Specification
    /// trivial.
    fn add_z() -> Cell
    {
        Cell::new(
            CmdPat::cut(
                Polarity::Positive,
                ProdPat::ctor("Zero", []),
                ConsPat::op("add", [ProdPat::meta("n")], ConsPat::meta("alpha")),
            ),
            CmdPat::cut(
                Polarity::Positive,
                ProdPat::meta("n"),
                ConsPat::meta("alpha"),
            ),
            Orientation::PolarityDerived,
            CellProvenance::SurfaceRule,
        )
    }

    /// (add-S): `⟨Succ(m) | add(n; α)⟩ ~> ⟨m | add(n; Succ⁻(α))⟩`.
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

    /// The Peano-add cell store: the `Succ⁻` frame cell, (add-Z), (add-S) —
    /// an orthogonal (no critical pairs), hence convergent, certified
    /// fragment.
    /// # Specification
    /// trivial.
    fn peano_store() -> CellStore
    {
        let mut store = CellStore::new();
        store.insert(frame_defining_cell(&Sym::new("Succ")));
        store.insert(add_z());
        store.insert(add_s());
        store
    }

    /// A joinable overlap system: two rules erasing `f`, whose reducts
    /// coincide; the completed store is convergent by the completion
    /// certificates.
    /// # Specification
    /// trivial.
    fn joinable_store() -> CellStore
    {
        let mut store = CellStore::new();
        // r1: ⟨Zero | f(α)⟩ ~> ⟨Zero | α⟩
        store.insert(Cell::new(
            CmdPat::cut(
                Polarity::Positive,
                ProdPat::ctor("Zero", []),
                ConsPat::op("f", [], ConsPat::meta("alpha")),
            ),
            CmdPat::cut(
                Polarity::Positive,
                ProdPat::ctor("Zero", []),
                ConsPat::meta("alpha"),
            ),
            Orientation::PolarityDerived,
            CellProvenance::SurfaceRule,
        ));
        // r2: ⟨x | f(α)⟩ ~> ⟨x | α⟩
        store.insert(Cell::new(
            CmdPat::cut(
                Polarity::Positive,
                ProdPat::meta("x"),
                ConsPat::op("f", [], ConsPat::meta("alpha")),
            ),
            CmdPat::cut(
                Polarity::Positive,
                ProdPat::meta("x"),
                ConsPat::meta("alpha"),
            ),
            Orientation::PolarityDerived,
            CellProvenance::SurfaceRule,
        ));
        store
    }

    /// The completed joinable store (convergent by construction).
    /// # Specification
    /// trivial.
    fn completed_joinable_store() -> CellStore
    {
        let outcome = complete(
            joinable_store(),
            CompletionBudget::new(64_usize.into(), 32_usize.into(), 128_usize.into()),
        );
        assert!(
            bool::from(outcome.is_completed()),
            "the joinable system completes"
        );
        outcome.store().clone()
    }

    /// A certified convergent store kind for the confluence-scoped rows.
    #[derive(Clone, Copy, Debug)]
    enum CertifiedStore
    {
        /// The Peano-add store (orthogonal, hence convergent).
        Peano,
        /// The completed joinable store (convergent by completion).
        Joinable,
    }

    /// A certified convergent store for the confluence-scoped rows.
    ///
    /// # Specification
    /// trivial.
    fn certified_store(kind: CertifiedStore) -> CellStore
    {
        match kind {
            | CertifiedStore::Peano => peano_store(),
            | CertifiedStore::Joinable => completed_joinable_store(),
        }
    }

    // ---- Axiom (i): multi-sums in the tight layer ---------------------------

    proptest! {
        #![proptest_config(crdc_config(Cases(2048)))]

        /// The family census: first-order syntactic unification makes the
        /// multi-sum family at most one per ordered pair per kind — the
        /// discrete TRS[Σ] case (the "multi" shape is degenerate here).
        #[test]
        fn multi_sum_families_are_degenerate_singletons(
            (a, b) in (arb_cell(), arb_cell()),
        ) {
            let mut store = CellStore::new();
            let a_id = store.insert(a);
            let b_id = store.insert(b);
            let family = enumerate_overlaps(&store);
            for kind in [OverlapKind::Confluence, OverlapKind::Composition] {
                for (left, right) in [(a_id, b_id), (b_id, a_id)] {
                    let count = family
                        .iter()
                        .filter(|o| o.kind == kind && o.left == left && o.right == right)
                        .count();
                    prop_assert!(
                        count <= 1,
                        "at most one {kind:?} overlap per ordered pair, found {count}"
                    );
                }
            }
        }

        /// Axiom (i), confluence: every cospan of left-face matches factors
        /// through exactly one enumerated overlap, uniquely (Def 2.1).
        #[test]
        fn confluence_cospans_factor_uniquely(
            (a, b, tau) in cospan_case(OverlapKind::Confluence),
        ) {
            let mut store = CellStore::new();
            let a_id = store.insert(a);
            let b_id = store.insert(b);
            let family = enumerate_overlaps(&store);
            let cospans = family
                .iter()
                .filter(|o| o.kind == OverlapKind::Confluence && o.left == a_id && o.right == b_id)
                .count();
            prop_assume!(cospans > 0);
            for overlap in &family {
                if overlap.kind != OverlapKind::Confluence
                    || overlap.left != a_id
                    || overlap.right != b_id
                {
                    continue;
                }
                let seam = overlap.peak.clone();
                let instance = tau.apply_cmd(&seam);
                let left_face = require_present(store.get(a_id)).lhs().clone();
                let left_vars = cmd_vars(&left_face);
                let left_match = compose(&tau, &overlap.unifier, &left_vars);
                let right_face = require_present(store.get(b_id)).lhs().clone();
                let renamed_right_vars = cmd_vars(overlap.right_renamed().lhs());
                let renamed_right_match = compose(&tau, &overlap.unifier, &renamed_right_vars);
                let right_match = remap_match(
                    &renamed_right_match,
                    overlap.right_renamed().lhs(),
                    &right_face,
                );
                let cospan = Cospan {
                    left_match,
                    right_face,
                    right_match,
                    instance,
                };
                let Factorization::Factored { overlap: factored, mediator } =
                    factor_cospan(a_id, b_id, OverlapKind::Confluence, &cospan, &family, &store)
                else {
                    panic!("the enumerated family must factor its own cospans");
                };
                prop_assert_eq!(
                    factored.as_ref(),
                    overlap,
                    "the unique factor is the overlap the cospan was built from"
                );
                let seam_vars = cmd_vars(&seam);
                prop_assert!(bool::from(substs_agree_on(&mediator, &tau, &seam_vars)));
            }
        }

        /// Axiom (i), composition: every cospan of (left `rhs`, right `lhs`)
        /// matches factors through exactly one enumerated overlap, uniquely.
        #[test]
        fn composition_cospans_factor_uniquely(
            (a, b, tau) in cospan_case(OverlapKind::Composition),
        ) {
            let mut store = CellStore::new();
            let a_id = store.insert(a);
            let b_id = store.insert(b);
            let family = enumerate_overlaps(&store);
            let cospans = family
                .iter()
                .filter(|o| o.kind == OverlapKind::Composition && o.left == a_id && o.right == b_id)
                .count();
            prop_assume!(cospans > 0);
            for overlap in &family {
                if overlap.kind != OverlapKind::Composition
                    || overlap.left != a_id
                    || overlap.right != b_id
                {
                    continue;
                }
                let Ok(seam) = seam_instance(overlap, &store) else {
                    continue;
                };
                let instance = tau.apply_cmd(&seam);
                let left_face = require_present(store.get(a_id)).rhs().clone();
                let left_vars = cmd_vars(&left_face);
                let left_match = compose(&tau, &overlap.unifier, &left_vars);
                let right_face = require_present(store.get(b_id)).lhs().clone();
                let renamed_right_vars = cmd_vars(overlap.right_renamed().lhs());
                let renamed_right_match = compose(&tau, &overlap.unifier, &renamed_right_vars);
                let right_match = remap_match(
                    &renamed_right_match,
                    overlap.right_renamed().lhs(),
                    &right_face,
                );
                let cospan = Cospan {
                    left_match,
                    right_face,
                    right_match,
                    instance,
                };
                let Factorization::Factored { overlap: factored, mediator } =
                    factor_cospan(a_id, b_id, OverlapKind::Composition, &cospan, &family, &store)
                else {
                    panic!("the enumerated family must factor its own cospans");
                };
                prop_assert_eq!(
                    factored.as_ref(),
                    overlap,
                    "the unique factor is the overlap the cospan was built from"
                );
                let seam_vars = cmd_vars(&seam);
                prop_assert!(bool::from(substs_agree_on(&mediator, &tau, &seam_vars)));
            }
        }

        /// Axiom (i), completeness in the wild (confluence): ground the left
        /// cell's left-hand side arbitrarily; whenever the right cell's
        /// left-hand side matches the same ground command, the pair is a
        /// cospan the enumerated family must explain (the independent
        /// direction — matching, never the enumerator, finds the cospan).
        ///
        /// **Explain, not mediate**, and the name says so. The claim has one
        /// exception — the root diagonal, whose peak joins in no steps and
        /// which the enumeration omits — so a cospan is explained either by a
        /// mediating overlap or by being that exception, with the exception
        /// *witnessed* rather than asserted. The property that named only
        /// mediation reported the exception as a completeness bug, which is
        /// how this was found.
        #[test]
        fn confluence_cospans_are_explained_by_the_family(
            (a, b, tau) in (arb_cell(), arb_cell()).prop_flat_map(|(a, b)| {
                arb_ground_subst(cmd_vars(a.lhs())).prop_map(move |tau| (a.clone(), b.clone(), tau))
            }),
        ) {
            let mut store = CellStore::new();
            let a_id = store.insert(a.clone());
            let b_id = store.insert(b.clone());
            let instance = tau.apply_cmd(a.lhs());
            let mut right_match = Subst::new();
            if !bool::from(match_cmd(b.lhs(), &instance, &mut right_match)) {
                return Ok(());
            }
            let family = enumerate_overlaps(&store);
            let cospan = Cospan {
                left_match: tau,
                right_face: b.lhs().clone(),
                right_match,
                instance,
            };
            match factor_cospan(a_id, b_id, OverlapKind::Confluence, &cospan, &family, &store)
            {
                | Factorization::Factored { .. } => {},
                | Factorization::TriviallyJoinable { ref joined } => {
                    // The completeness claim's stated exception. The cospan is
                    // the root diagonal, and `trivially_joinable` has already
                    // COMPUTED both contractions and found them equal -- the
                    // exception is witnessed here rather than assumed, and a
                    // diagonal peak with distinct reducts would have arrived
                    // as `Incomplete` instead.
                    prop_assert_eq!(a_id, b_id, "only the diagonal is excepted");
                    let cell = require_present(store.get(a_id));
                    prop_assert_ne!(
                        joined.as_ref(),
                        cell.lhs(),
                        "the joined term is the contraction, not the peak"
                    );
                },
                | Factorization::Incomplete => {
                    prop_assert!(false, "enumeration incomplete: no overlap mediates a matched cospan");
                },
                | Factorization::NonMinimal(members) => {
                    prop_assert!(
                        false,
                        "family not minimal: {} overlaps mediate one cospan",
                        members.len()
                    );
                },
            }
        }

        /// Axiom (i), completeness in the wild (composition): ground the left
        /// cell's right-hand side arbitrarily; whenever the right cell's
        /// left-hand side matches, the enumerated family must explain it.
        ///
        /// The composition branch has no diagonal exception — it is not
        /// guarded on the ids at all — so the exception arm here is
        /// unreachable and says so.
        #[test]
        fn composition_cospans_are_explained_by_the_family(
            (a, b, tau) in (arb_cell(), arb_cell()).prop_flat_map(|(a, b)| {
                arb_ground_subst(cmd_vars(a.rhs())).prop_map(move |tau| (a.clone(), b.clone(), tau))
            }),
        ) {
            let mut store = CellStore::new();
            let a_id = store.insert(a.clone());
            let b_id = store.insert(b.clone());
            let instance = tau.apply_cmd(a.rhs());
            let mut right_match = Subst::new();
            if !bool::from(match_cmd(b.lhs(), &instance, &mut right_match)) {
                return Ok(());
            }
            let family = enumerate_overlaps(&store);
            let cospan = Cospan {
                left_match: tau,
                right_face: b.lhs().clone(),
                right_match,
                instance,
            };
            match factor_cospan(a_id, b_id, OverlapKind::Composition, &cospan, &family, &store)
            {
                | Factorization::Factored { .. } => {},
                | Factorization::TriviallyJoinable { ref joined } => {
                    // The completeness claim's stated exception. The cospan is
                    // the root diagonal, and `trivially_joinable` has already
                    // COMPUTED both contractions and found them equal -- the
                    // exception is witnessed here rather than assumed, and a
                    // diagonal peak with distinct reducts would have arrived
                    // as `Incomplete` instead.
                    prop_assert_eq!(a_id, b_id, "only the diagonal is excepted");
                    let cell = require_present(store.get(a_id));
                    prop_assert_ne!(
                        joined.as_ref(),
                        cell.lhs(),
                        "the joined term is the contraction, not the peak"
                    );
                },
                | Factorization::Incomplete => {
                    prop_assert!(false, "enumeration incomplete: no overlap mediates a matched cospan");
                },
                | Factorization::NonMinimal(members) => {
                    prop_assert!(
                        false,
                        "family not minimal: {} overlaps mediate one cospan",
                        members.len()
                    );
                },
            }
        }
    }

    /// The counterexample that started this, pinned as an ordinary test.
    ///
    /// Found by [`confluence_cospans_are_explained_by_the_family`], whose seed
    /// lives only in a gitignored regression file — so the durable form of a
    /// case that was nearly lost with its worktree lives here instead.
    ///
    /// The store deduplicates structurally equal cells onto one id, so the
    /// property's two generated cells collapse to a single entry and the
    /// matched cospan is **diagonal**. The enumerator omits that peak, and
    /// factoring now reports the omission as the claim's stated exception with
    /// the term both legs give, rather than as incompleteness.
    ///
    /// **The name moved with the claim.** It asserted that the cospan
    /// *factors*, which is an outcome the repair deliberately does not
    /// deliver: the diagonal is not mediated, it is excepted.
    #[test]
    fn the_diagonal_cospan_of_a_deduplicated_cell_is_the_stated_exception()
    {
        let cell = Cell::new(
            CmdPat::cut(
                Polarity::Positive,
                nat_of(NatSuccCount(2)),
                ConsPat::op("f", [], ConsPat::top()),
            ),
            CmdPat::cut(
                Polarity::Positive,
                nat_of(NatSuccCount(1)),
                ConsPat::op("f", [], ConsPat::top()),
            ),
            Orientation::PolarityDerived,
            CellProvenance::SurfaceRule,
        );
        let tau = Subst::new();
        let mut store: CellStore = CellStore::new();
        let a_id = store.insert(cell.clone());
        let b_id = store.insert(cell);
        assert_eq!(
            a_id, b_id,
            "the store dedupes structural equals onto one id"
        );
        let lhs = require_present(store.get(a_id)).lhs().clone();
        let lhs_for_check = lhs.clone();
        let instance = tau.apply_cmd(&lhs);
        let mut right_match = Subst::new();
        assert!(
            bool::from(match_cmd(&lhs, &instance, &mut right_match)),
            "the ground left face matches its own instance"
        );
        let family = enumerate_overlaps(&store);
        let cospan = Cospan {
            left_match: tau,
            right_face: lhs,
            right_match,
            instance,
        };
        match factor_cospan(
            a_id,
            b_id,
            OverlapKind::Confluence,
            &cospan,
            &family,
            &store,
        ) {
            | Factorization::TriviallyJoinable { joined } => {
                assert_ne!(
                    joined.as_ref(),
                    &lhs_for_check,
                    "the exception carries the contraction, not the peak"
                );
            },
            | Factorization::Factored { .. } => {
                panic!("the diagonal is excepted, never mediated");
            },
            | Factorization::Incomplete => {
                panic!("enumeration incomplete: no overlap mediates a matched cospan");
            },
            | Factorization::NonMinimal(members) => {
                panic!(
                    "family not minimal: {} overlaps mediate one cospan",
                    members.len()
                );
            },
        }
    }

    // ---- Axiom (ii): pullbacks in the tight and cell layers -----------------

    /// A unifiable pattern pair (two generalizations of one seam) with a
    /// grounding of their joint seam variables.
    ///
    /// # Specification
    /// - ensures: draws satisfy the fixture family described above; the
    ///   sampling distribution is unspecified.
    /// - executable: none — a strategy is a generator, not a generated value;
    ///   its support cannot be inspected without running a separate random
    ///   experiment.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the generated objects are checked by the consuming
    ///   laws; this does not establish exhaustive coverage of the generator's
    ///   support.
    /// - witness: `tests::crdc::tests::matched_pattern_instances_pull_back`
    fn pattern_pullback_case() -> BoxedStrategy<(CmdPat, CmdPat, Subst)>
    {
        unifiable_faces()
            .prop_flat_map(|(p, q)| {
                let mut unifier = Subst::new();
                let seam = if bool::from(unify_cmd(&p, &q, &mut unifier)) {
                    // Guaranteed by construction (generalizations of one seam);
                    // the row asserts it independently.
                    unifier.apply_cmd(&p)
                }
                else {
                    p.clone()
                };
                arb_ground_subst(cmd_vars(&seam)).prop_map(move |tau| (p.clone(), q.clone(), tau))
            })
            .boxed()
    }

    proptest! {
        #![proptest_config(crdc_config(Cases(2048)))]

        /// Axiom (ii), tight layer: unification computes the pullback of two
        /// patterns over a common instance — the square commutes (σ(P) =
        /// σ(Q)) and every common instance factors through the most general
        /// unifier uniquely.
        #[test]
        fn unification_computes_pattern_pullbacks(
            (p, q, tau) in pattern_pullback_case(),
        ) {
            let mut unifier = Subst::new();
            prop_assert!(
                bool::from(unify_cmd(&p, &q, &mut unifier)),
                "generalizations of one seam must unify"
            );
            // The square commutes: the unifier unifies.
            let seam = unifier.apply_cmd(&p);
            prop_assert_eq!(
                &seam,
                &unifier.apply_cmd(&q),
                "the unifier equalizes the two patterns"
            );
            // Universality: the grounded common instance factors through the
            // seam, and the legs factor through the unifier.
            let instance = tau.apply_cmd(&seam);
            let mut mediator = Subst::new();
            prop_assert!(bool::from(match_cmd(&seam, &instance, &mut mediator)));
            let p_vars = cmd_vars(&p);
            let p_leg = compose(&tau, &unifier, &p_vars);
            let p_factored = compose(&mediator, &unifier, &p_vars);
            prop_assert!(bool::from(substs_agree_on(&p_leg, &p_factored, &p_vars)));
            let q_vars = cmd_vars(&q);
            let q_leg = compose(&tau, &unifier, &q_vars);
            let q_factored = compose(&mediator, &unifier, &q_vars);
            prop_assert!(bool::from(substs_agree_on(&q_leg, &q_factored, &q_vars)));
            // The mediator is the grounding itself on the seam variables.
            let seam_vars = cmd_vars(&seam);
            prop_assert!(bool::from(substs_agree_on(&mediator, &tau, &seam_vars)));
        }

        /// Axiom (ii), tight layer in the wild: a common instance found by
        /// matching (never by unification) must still factor through the most
        /// general unifier — completeness of the pullback construction.
        #[test]
        fn matched_pattern_instances_pull_back(
            (p, q, tau) in {
                let (p1, c1) = Pool::Default.vars();
                let (p2, c2) = Pool::Two.vars();
                (arb_cmdpat(&p1, &c1, Depth(3)), arb_cmdpat(&p2, &c2, Depth(3)))
                    .prop_flat_map(|(p, q)| {
                        arb_ground_subst(cmd_vars(&p)).prop_map(move |tau| {
                            (p.clone(), q.clone(), tau)
                        })
                    })
            },
        ) {
            let instance = tau.apply_cmd(&p);
            let mut q_match = Subst::new();
            if !bool::from(match_cmd(&q, &instance, &mut q_match)) {
                return Ok(());
            }
            // (τ, q_match) is a cospan: the pullback must exist and factor it.
            let mut unifier = Subst::new();
            prop_assert!(
                bool::from(unify_cmd(&p, &q, &mut unifier)),
                "a common instance exists, so the patterns must unify"
            );
            let seam = unifier.apply_cmd(&p);
            let mut mediator = Subst::new();
            prop_assert!(
                bool::from(match_cmd(&seam, &instance, &mut mediator)),
                "the common instance factors through the most general unifier"
            );
            let p_vars = cmd_vars(&p);
            let p_factored = compose(&mediator, &unifier, &p_vars);
            prop_assert!(bool::from(substs_agree_on(&tau, &p_factored, &p_vars)));
            let q_vars = cmd_vars(&q);
            let q_factored = compose(&mediator, &unifier, &q_vars);
            prop_assert!(bool::from(substs_agree_on(&q_match, &q_factored, &q_vars)));
        }

        /// Axiom (ii), cell layer: cells with a common instance cell pull
        /// back componentwise — the consistent pair-MGU exists, the
        /// intersection cell is well-formed, and the factorization is unique
        /// on both faces.
        #[test]
        fn cell_intersection_is_componentwise(
            (a, b, tau_a) in arb_cell().prop_flat_map(|a| {
                let mut vars = cmd_vars(a.lhs());
                vars.extend(cmd_vars(a.rhs()));
                let mut dedup = BTreeSet::new();
                let vars: Vec<MetaVar> = vars
                    .into_iter()
                    .filter(|mv| dedup.insert(mv.clone()))
                    .collect();
                let decisions = proptest::collection::vec(
                    prop::bool::weighted(GENERALIZATION_COIN_WEIGHT),
                    DECISION_COUNT,
                );
                (arb_ground_subst(vars), decisions.clone(), decisions).prop_map(
                    move |(tau, d1, d2)| {
                        // The common instance cell d = τ_a(a), and b a
                        // generalization of d (so d is an instance of b by
                        // construction; the two faces generalize with
                        // disjoint fresh names, or no shared hole could
                        // bind consistently).
                        let b: Cell = Cell::new(
                            generalize_cmd(
                                &tau.apply_cmd(a.lhs()),
                                GenPrefix::LhsFace,
                                &Decisions(d1),
                            ),
                            generalize_cmd(
                                &tau.apply_cmd(a.rhs()),
                                GenPrefix::RhsFace,
                                &Decisions(d2),
                            ),
                            Orientation::PolarityDerived,
                            CellProvenance::SurfaceRule,
                        );
                        (a.clone(), b, tau)
                    },
                )
            }),
        ) {
            // The common instance cell: d = τ_a(a) on both faces.
            let d_lhs = tau_a.apply_cmd(a.lhs());
            let d_rhs = tau_a.apply_cmd(a.rhs());
            // b admits d as an instance consistently (one substitution) —
            // guaranteed by the generalization construction.
            let mut b_match = Subst::new();
            prop_assert!(bool::from(match_cmd(b.lhs(), &d_lhs, &mut b_match)));
            prop_assert!(bool::from(match_cmd(b.rhs(), &d_rhs, &mut b_match)));
            // The pair-MGU: unify the left-hand sides, then the instantiated
            // right-hand sides, through one substitution.
            let mut unifier = Subst::new();
            prop_assert!(
                bool::from(unify_cmd(a.lhs(), b.lhs(), &mut unifier)),
                "a common instance exists, so the left-hand sides unify"
            );
            prop_assert!(
                bool::from(unify_cmd(
                    &unifier.apply_cmd(a.rhs()),
                    &unifier.apply_cmd(b.rhs()),
                    &mut unifier,
                )),
                "the right-hand sides unify through the same substitution"
            );
            // The intersection cell is well-formed: both faces agree.
            prop_assert_eq!(
                unifier.apply_cmd(a.lhs()),
                unifier.apply_cmd(b.lhs()),
                "the intersection's left face"
            );
            prop_assert_eq!(
                unifier.apply_cmd(a.rhs()),
                unifier.apply_cmd(b.rhs()),
                "the intersection's right face"
            );
            // The common instance factors through the intersection,
            // componentwise, and the legs factor uniquely.
            let i_lhs = unifier.apply_cmd(a.lhs());
            let i_rhs = unifier.apply_cmd(a.rhs());
            let mut mediator = Subst::new();
            prop_assert!(bool::from(match_cmd(&i_lhs, &d_lhs, &mut mediator)));
            prop_assert!(bool::from(match_cmd(&i_rhs, &d_rhs, &mut mediator)));
            let mut a_vars = cmd_vars(a.lhs());
            a_vars.extend(cmd_vars(a.rhs()));
            let mut dedup_a = BTreeSet::new();
            let a_vars: Vec<MetaVar> = a_vars
                .into_iter()
                .filter(|mv| dedup_a.insert(mv.clone()))
                .collect();
            let a_factored = compose(&mediator, &unifier, &a_vars);
            prop_assert!(bool::from(substs_agree_on(&tau_a, &a_factored, &a_vars)));
            let mut b_vars = cmd_vars(b.lhs());
            b_vars.extend(cmd_vars(b.rhs()));
            let mut dedup_b = BTreeSet::new();
            let b_vars: Vec<MetaVar> = b_vars
                .into_iter()
                .filter(|mv| dedup_b.insert(mv.clone()))
                .collect();
            let b_factored = compose(&mediator, &unifier, &b_vars);
            prop_assert!(bool::from(substs_agree_on(&b_match, &b_factored, &b_vars)));
        }
    }

    // ---- Axiom (iii): horizontal decomposition -------------------------------

    proptest! {
        #![proptest_config(crdc_config(Cases(1024)))]

        /// Axiom (iii): a cell over a composed seam factors, up to a globular
        /// iso, as a horizontal composition of per-frame cells — the fused
        /// cell decomposes as the two-step derivation, and the factorization
        /// is **strict** (the iso residue is the identity on the boundary).
        #[test]
        fn fused_cells_decompose_as_two_step_derivations(
            (a, b, tau) in cospan_case(OverlapKind::Composition),
        ) {
            let mut store = CellStore::new();
            let a_id = store.insert(a);
            let b_id = store.insert(b);
            let family = enumerate_overlaps(&store);
            let compositions = family
                .iter()
                .filter(|o| o.kind == OverlapKind::Composition)
                .count();
            prop_assume!(compositions > 0);
            for overlap in &family {
                if overlap.kind != OverlapKind::Composition
                    || overlap.left != a_id
                    || overlap.right != b_id
                {
                    continue;
                }
                let HorizontalFactorization { frames, witness } =
                    decompose_horizontal(overlap, &mut store)
                        .expect("the fused cell of a composition overlap exists");
                prop_assert_eq!(
                    frames.as_slice(),
                    &[overlap.left, overlap.right],
                    "the factorization is the per-frame two-step"
                );
                // The globular-iso witness replays (the fused ≡ two-step
                // certificate) and is strict: the recorded two-step path is
                // [left@root, right@seam], the one-step path is [fused@root],
                // and both land on the composite.
                prop_assert!(
                    bool::from(witness.replay(&store)),
                    "the fused ≡ two-step certificate replays"
                );
                prop_assert_eq!(witness.path_a.len(), 2, "the two-step path");
                prop_assert_eq!(witness.path_b.len(), 1, "the fused one-step path");
                // The differential: on ground instances of the peak, firing
                // the fused cell agrees with firing the frames in sequence.
                let instance = tau.apply_cmd(&overlap.peak);
                let fused_id = witness.path_b[0].cell;
                let fused_cell = require_present(store.get(fused_id));
                let via_fused = rewrite_at(fused_cell, &instance, &Pos::root());
                let left_cell = require_present(store.get(overlap.left));
                let right_cell = require_present(store.get(overlap.right));
                let via_two_step = rewrite_at(left_cell, &instance, &Pos::root())
                    .and_then(|mid| rewrite_at(right_cell, &mid, &Pos::root()));
                prop_assert!(matches!(via_fused, Maybe::Present(_)), "the fused cell fires on the instance");
                prop_assert_eq!(
                    via_fused,
                    via_two_step,
                    "the fused cell and the two-step composite agree"
                );
            }
        }
    }

    // ---- Axiom (iv): source a strong multi-opfibration ------------------------

    /// A generated cell, an instantiation of its variables, and a grounding
    /// of the instantiated left-hand side — the source-pushforward cases.
    ///
    /// # Specification
    /// - ensures: draws satisfy the fixture family described above; the
    ///   sampling distribution is unspecified.
    /// - executable: none — a strategy is a generator, not a generated value;
    ///   its support cannot be inspected without running a separate random
    ///   experiment.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the generated objects are checked by the consuming
    ///   laws; this does not establish exhaustive coverage of the generator's
    ///   support.
    /// - witness: `tests::crdc::tests::source_pushforward_factors_matches_uniquely`
    fn pushforward_case() -> BoxedStrategy<(Cell, Subst, Subst)>
    {
        arb_cell()
            .prop_flat_map(|cell| {
                let (p2, c2) = Pool::Two.vars();
                let vars = cmd_vars(cell.lhs());
                arb_subst(vars, &p2, &c2).prop_map(move |sigma| (cell.clone(), sigma))
            })
            .prop_flat_map(|(cell, sigma)| {
                let lifted_vars = cmd_vars(&sigma.apply_cmd(cell.lhs()));
                arb_ground_subst(lifted_vars).prop_map(move |m| (cell.clone(), sigma.clone(), m))
            })
            .boxed()
    }

    proptest! {
        #![proptest_config(crdc_config(Cases(2048)))]

        /// Axiom (iv): rewriting is substitution-stable — the lifted cell and
        /// the original cell agree on every ground instance of the lifted
        /// left-hand side (the TRS[Σ] discrete lift is sound).
        #[test]
        fn source_pushforward_is_substitution_stable(
            (cell, sigma, m) in pushforward_case(),
        ) {
            let lifts = pushforward_src(&cell, &sigma);
            prop_assert_eq!(lifts.len(), 1, "the source lift is discrete (a singleton)");
            let lifted = &lifts[0].0;
            let instance = m.apply_cmd(lifted.lhs());
            let via_lifted = rewrite_at(lifted, &instance, &Pos::root());
            let via_original = rewrite_at(&cell, &instance, &Pos::root());
            prop_assert!(matches!(via_lifted, Maybe::Present(_)), "the lifted cell fires on its instances");
            prop_assert_eq!(
                via_lifted,
                via_original,
                "the lifted cell and the original agree on the instance"
            );
        }

        /// Axiom (iv): the singleton lift is op-Cartesian — every match of
        /// the lifted left-hand side factors through the substitution,
        /// uniquely on the occurring variables (and matching is
        /// deterministic).
        #[test]
        fn source_pushforward_factors_matches_uniquely(
            (cell, sigma, m) in pushforward_case(),
        ) {
            let lifted = &pushforward_src(&cell, &sigma)[0].0;
            let instance = m.apply_cmd(lifted.lhs());
            let mut direct = Subst::new();
            prop_assert!(bool::from(match_cmd(cell.lhs(), &instance, &mut direct)));
            let mut through = Subst::new();
            prop_assert!(bool::from(match_cmd(lifted.lhs(), &instance, &mut through)));
            // The factorization: the direct match is the through-match
            // composed with the substitution, on the cell's variables.
            let cell_vars = cmd_vars(cell.lhs());
            let factored = compose(&through, &sigma, &cell_vars);
            prop_assert!(bool::from(substs_agree_on(&direct, &factored, &cell_vars)));
            // Determinism (uniqueness of the mediator): re-matching agrees.
            let mut again = Subst::new();
            prop_assert!(bool::from(match_cmd(lifted.lhs(), &instance, &mut again)));
            let through_vars = cmd_vars(lifted.lhs());
            prop_assert!(bool::from(substs_agree_on(&through, &again, &through_vars)));
        }
    }

    // ---- Axiom (v): target a residual multi-opfibration -----------------------

    proptest! {
        #![proptest_config(crdc_config(Cases(256)))]

        /// Axiom (v): the pushed-forward derivation exists on every ground
        /// instance — fire the lifted cell, then normalize; the residue
        /// records the owed post-normalization (Def 2.8's `post`). The
        /// budget is deliberately shallow: generated stores can loop-rewrite,
        /// and a divergent generated system is outside the convergent
        /// fragment, not an axiom failure.
        #[test]
        fn target_pushforward_exists_with_derivation_residue(
            (cell, sigma, m) in pushforward_case(),
        ) {
            let mut store = CellStore::new();
            store.insert(cell.clone());
            let lifted = pushforward_tgt(&cell, &sigma);
            prop_assert_eq!(lifted.len(), 1, "the target lift is a singleton family");
            let lift = lifted[0].clone();
            store.insert(lift.0.clone());
            let instance = m.apply_cmd(lift.0.lhs());
            let budget = NormalizationBudget::from(12_usize);
            let Maybe::Present((normal, residue)) = residue_of(&store, &lift, &instance, budget) else {
                // Budget exhaustion is a divergent generated system — outside
                // the convergent fragment, not an axiom failure.
                return Ok(());
            };
            // The residue is the derivation the composite still owes:
            // re-running it from the fired output lands on the normal form.
            let fired = require_present(rewrite_at(&lift.0, &instance, &Pos::root()));
            let replayed = run_path(&store, &fired, &residue.post);
            prop_assert_eq!(
                require_present(replayed),
                normal,
                "the residue path replays to the pushed output"
            );
        }

        /// Axiom (v): lifts compose functorially — pushing along τ after σ is
        /// pushing along τ ∘ σ (Def 2.8's `post ∘ f` bookkeeping at the lift
        /// level).
        #[test]
        fn target_pushforward_lifts_compose(
            (cell, sigma, tau) in arb_cell().prop_flat_map(|cell| {
                let (p2, c2) = Pool::Two.vars();
                arb_subst(cmd_vars(cell.lhs()), &p2, &c2)
                    .prop_map(move |sigma| (cell.clone(), sigma))
            })
            .prop_flat_map(|(cell, sigma)| {
                let (p3, c3) = Pool::Three.vars();
                let mut vars = cmd_vars(&sigma.apply_cmd(cell.lhs()));
                vars.extend(cmd_vars(&sigma.apply_cmd(cell.rhs())));
                let mut dedup = BTreeSet::new();
                let vars: Vec<MetaVar> = vars
                    .into_iter()
                    .filter(|mv| dedup.insert(mv.clone()))
                    .collect();
                arb_subst(vars, &p3, &c3).prop_map(move |tau| {
                    (cell.clone(), sigma.clone(), tau)
                })
            }),
        ) {
            let staged = pushforward_tgt(&pushforward_tgt(&cell, &sigma)[0].0, &tau);
            let mut vars = cmd_vars(cell.lhs());
            vars.extend(cmd_vars(cell.rhs()));
            let mut dedup = BTreeSet::new();
            let vars: Vec<MetaVar> = vars
                .into_iter()
                .filter(|mv| dedup.insert(mv.clone()))
                .collect();
            let direct = pushforward_tgt(&cell, &compose(&tau, &sigma, &vars));
            prop_assert_eq!(
                &staged[0].0,
                &direct[0].0,
                "τ ∘ (σ-lift) coincides with the (τ ∘ σ)-lift"
            );
        }

        /// Axiom (v): pushed derivations are confluence-unique on the
        /// certified convergent fragment — normalizing an instance directly
        /// and normalizing its pushed output reach the same normal form (the
        /// residual factorization over the convergent store).
        #[test]
        fn target_pushforward_is_confluence_unique(
            (joinable, cell, sigma, m) in (any::<bool>(), 0_usize .. 16)
                .prop_flat_map(|(joinable, pick)| {
                    let store = certified_store(if joinable {
                        CertifiedStore::Joinable
                    }
                    else {
                        CertifiedStore::Peano
                    });
                    let cells: Vec<Cell> =
                        store.iter().map(|(_, cell)| cell.clone()).collect();
                    let cell = cells[pick.checked_rem(cells.len()).expect("cells are nonempty")].clone();
                    let (p2, c2) = Pool::Two.vars();
                    arb_subst(cmd_vars(cell.lhs()), &p2, &c2)
                        .prop_map(move |sigma| (joinable, cell.clone(), sigma))
                })
                .prop_flat_map(|(joinable, cell, sigma)| {
                    let mut vars = cmd_vars(&sigma.apply_cmd(cell.lhs()));
                    vars.extend(cmd_vars(&sigma.apply_cmd(cell.rhs())));
                    let mut dedup = BTreeSet::new();
                    let vars: Vec<MetaVar> = vars
                        .into_iter()
                        .filter(|mv| dedup.insert(mv.clone()))
                        .collect();
                    arb_ground_subst(vars).prop_map(move |m| {
                        (joinable, cell.clone(), sigma.clone(), m)
                    })
                }),
        ) {
            let store = certified_store(if joinable {
                CertifiedStore::Joinable
            }
            else {
                CertifiedStore::Peano
            });
            let lifted = lift_cell(&cell, &sigma);
            let instance = m.apply_cmd(lifted.lhs());
            let pushed_output = m.apply_cmd(lifted.rhs());
            let budget = NormalizationBudget::from(64_usize);
            let direct = normalize(&store, &instance, budget);
            let pushed = normalize(&store, &pushed_output, budget);
            prop_assume!(!bool::from(direct.exhausted));
            prop_assume!(!bool::from(pushed.exhausted));
            prop_assert_eq!(
                direct.normal,
                pushed.normal,
                "the instance and its pushed output join on the convergent fragment"
            );
        }
    }

    /// The residue census on the Peano family (deterministic golden):
    /// instantiating (add-Z)'s output with a redex-bearing continuation
    /// forces a three-step residue; a non-redex instantiation owes nothing.
    /// This is the empirical answer to the open question of which cell
    /// classes exercise the residual part of axiom (v): exactly the
    /// instantiations that create redexes.
    #[test]
    fn residue_census_on_the_peano_family()
    {
        let store = peano_store();
        let budget = NormalizationBudget::from(64_usize);
        // σ redex-bearing: n ↦ Succ(Zero), α ↦ add(Zero; ★).
        let mut sigma = Subst::new();
        sigma
            .bind_prod(
                MetaVar::producer("n"),
                ProdPat::ctor("Succ", [ProdPat::ctor("Zero", [])]),
            )
            .expect("the fixture substitution is consistent");
        sigma
            .bind_cons(
                MetaVar::consumer("alpha"),
                ConsPat::op("add", [ProdPat::ctor("Zero", [])], ConsPat::top()),
            )
            .expect("the fixture substitution is consistent");
        let add_z_cell = add_z();
        let lifted = pushforward_tgt(&add_z_cell, &sigma);
        let instance = sigma.apply_cmd(add_z_cell.lhs());
        let (normal, residue) = require_present(residue_of(&store, &lifted[0], &instance, budget));
        assert_eq!(
            3,
            residue.post.len(),
            "the residue records three owed steps (add-S, add-Z, frame)"
        );
        assert_eq!(
            normal,
            CmdPat::cut(
                Polarity::Positive,
                ProdPat::ctor("Succ", [ProdPat::ctor("Zero", [])]),
                ConsPat::top(),
            ),
            "the pushed output is the normal form ⟨Succ(Zero) | ★⟩"
        );
        // σ trivial: n ↦ Zero, α ↦ ★ — no redex created, no residue.
        let mut trivial = Subst::new();
        trivial
            .bind_prod(MetaVar::producer("n"), ProdPat::ctor("Zero", []))
            .expect("the fixture substitution is consistent");
        trivial
            .bind_cons(MetaVar::consumer("alpha"), ConsPat::top())
            .expect("the fixture substitution is consistent");
        let lifted_trivial = pushforward_tgt(&add_z_cell, &trivial);
        let instance_trivial = trivial.apply_cmd(add_z_cell.lhs());
        let (_normal, residue_trivial) = require_present(residue_of(
            &store,
            &lifted_trivial[0],
            &instance_trivial,
            budget,
        ));
        assert!(
            residue_trivial.post.is_empty(),
            "a non-redex instantiation owes no residue"
        );
    }

    // ---- Virtual-side line items (Thompson–Carlson) ---------------------------

    /// The Peano instance arguments (successor depths).
    #[derive(Clone, Copy, Debug)]
    struct PeanoArgs(u8, u8);

    /// A Peano ground instance `⟨Succ^a(Zero) | Succ⁻(add(Succ^b(Zero); ★))⟩`
    /// with a nontrivial normalization path (frame, then `a+1` (add-S), then
    /// (add-Z), then `a+1` frames).
    /// # Specification
    /// trivial.
    fn peano_instance(args: PeanoArgs) -> CmdPat
    {
        CmdPat::cut(
            Polarity::Positive,
            nat_of(NatSuccCount(args.0)),
            ConsPat::frame(
                "Succ",
                ConsPat::op("add", [nat_of(NatSuccCount(args.1))], ConsPat::top()),
            ),
        )
    }

    proptest! {
        #![proptest_config(crdc_config(Cases(512)))]

        /// Virtual side, positive globular decompositions: every derivation
        /// path decomposes uniquely into its one-step cells (the free path
        /// algebra) and recomposes — the recorded path is the decomposition,
        /// and deterministic normalization makes it unique.
        #[test]
        fn paths_decompose_uniquely_into_steps(
            a in 0u8 .. 6,
            b in 0u8 .. 6,
        ) {
            let store = peano_store();
            let instance = peano_instance(PeanoArgs(a, b));
            let budget = NormalizationBudget::from(64_usize);
            let norm = normalize(&store, &instance, budget);
            prop_assume!(!bool::from(norm.exhausted));
            // Recomposition: the decomposition folds back to the normal form.
            let recomposed = run_path(&store, &instance, &norm.path);
            prop_assert_eq!(
                require_present(recomposed),
                norm.normal,
                "the path recomposes to the normal form"
            );
            // Uniqueness: normalization is deterministic, so the
            // decomposition is the unique one the engine produces.
            let again = normalize(&store, &instance, budget);
            prop_assert_eq!(&again.path, &norm.path, "the decomposition is unique");
            // Positivity: no step is a unit — every recorded step actually
            // fires (changes the term) at its position.
            let mut current = instance;
            for step in &norm.path {
                let cell = require_present(store.get(step.cell));
                let next = require_present(rewrite_at(cell, &current, &step.at));
                prop_assert_ne!(&next, &current, "no step is a unit");
                current = next;
            }
        }

        /// Virtual side, pro-representability: every two-step composite is
        /// representable — the fused cell exists as a cell of the store and
        /// represents the composite (the exponentiability chain's
        /// decomposable ⇔ pro-representable direction, Theorem 5.11).
        #[test]
        fn two_step_composites_are_pro_representable(
            (a, b, _tau) in cospan_case(OverlapKind::Composition),
        ) {
            let mut store = CellStore::new();
            store.insert(a);
            store.insert(b);
            let family = enumerate_overlaps(&store);
            let compositions = family
                .iter()
                .filter(|o| o.kind == OverlapKind::Composition)
                .count();
            prop_assume!(compositions > 0);
            for overlap in &family {
                if overlap.kind != OverlapKind::Composition {
                    continue;
                }
                let (fused_id, witness) = derive_fused(overlap, &mut store)
                    .expect("the composite is representable as a fused cell");
                let fused = require_present(store.get(fused_id));
                // The representable's boundary is the composite's boundary.
                prop_assert_eq!(fused.lhs(), &overlap.peak, "source is the peak");
                prop_assert_eq!(fused.rhs(), &witness.joins_at, "target is the composite");
            }
        }

        /// Virtual side, cellular Conduché (the 2-layer criterion, Theorem 4.14):
        /// path splittings refine — for a path split as p = p₁ · p₂ and a
        /// further split of p₁, the staged replays agree (concatenation is
        /// free, so the criterion holds strictly).
        #[test]
        fn path_splittings_refine(
            a in 1u8 .. 6,
            b in 1u8 .. 6,
            i_raw in any::<u8>(),
            j_raw in any::<u8>(),
        ) {
            let store = peano_store();
            let instance = peano_instance(PeanoArgs(a, b));
            let budget = NormalizationBudget::from(64_usize);
            let norm = normalize(&store, &instance, budget);
            prop_assume!(!bool::from(norm.exhausted));
            prop_assume!(norm.path.len() >= 2);
            let i = usize::from(i_raw).checked_rem(norm.path.len().saturating_add(1)).expect("saturating_add(1) is nonzero");
            let j = usize::from(j_raw).checked_rem(i.saturating_add(1)).expect("saturating_add(1) is nonzero");
            let (p1, p2) = norm.path.split_at(i);
            let (q1, q2) = p1.split_at(j);
            // Staged replay: q1, then q2, then p2.
            let staged = run_path(&store, &instance, q1)
                .and_then(|mid| run_path(&store, &mid, q2))
                .and_then(|mid| run_path(&store, &mid, p2));
            prop_assert_eq!(
                require_present(staged),
                norm.normal,
                "the refined splitting recomposes to the same normal form"
            );
        }
    }
}
quenchant_shape::reason_enum! { mod diagonal { #[derive(Debug)] pub enum Absent { NotDiagonal, Unissued, NotUnifiable, DistinctReducts } } }
quenchant_shape::reason_enum! { mod residue { #[derive(Debug)] pub enum Absent { DoesNotFire, Exhausted } } }
quenchant_shape::reason_enum! { mod replay_path { #[derive(Clone, Copy, Debug, Eq, PartialEq)] pub enum Absent { UnissuedCell, DoesNotFire } } }
