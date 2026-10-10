//! Formation, judgment and replay boundaries through the public interface.

use gandr_theory_cell_complexes::Cell;
use gandr_theory_cell_complexes::CellId;
use gandr_theory_cell_complexes::CellProvenance;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::CmdPat;
use gandr_theory_cell_complexes::ConsPat;
use gandr_theory_cell_complexes::Orientation;
use gandr_theory_cell_complexes::Polarity;
use gandr_theory_cell_complexes::Pos;
use gandr_theory_cell_complexes::PositionStep;
use gandr_theory_cell_complexes::ProdPat;
use gandr_theory_coherent_resolutions::OverlapKind;
use gandr_theory_coherent_resolutions::Tracelet;
use gandr_theory_coherent_resolutions::derive_fused;
use gandr_theory_coherent_resolutions::enumerate_overlaps;
use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::NameRef;
use gandr_theory_levitation::NominalId;
use gandr_theory_virtual_doctrines::CheckError;
use gandr_theory_virtual_doctrines::Checker;
use gandr_theory_virtual_doctrines::Context;
use gandr_theory_virtual_doctrines::Derivation;
use gandr_theory_virtual_doctrines::DerivationId;
use gandr_theory_virtual_doctrines::DerivationIndex;
use gandr_theory_virtual_doctrines::ProVar;
use gandr_theory_virtual_doctrines::Proterm;
use gandr_theory_virtual_doctrines::Protype;
use gandr_theory_virtual_doctrines::RelationRef;
use gandr_theory_virtual_doctrines::SignatureRef;
use gandr_theory_virtual_doctrines::TermRef;

/// # Specification
/// trivial.
fn signature(name: NameRef<'_>) -> SignatureRef
{
    SignatureRef::single(NominalId::new(0_u64.into(), name.as_ref()))
}
/// # Specification
/// trivial.
fn atom(name: NameRef<'_>) -> TermRef
{
    TermRef::new(FreeTerm::ctor(name.as_ref(), []))
}
/// # Specification
/// trivial.
fn variable(name: NameRef<'_>) -> ProVar
{
    ProVar::new(name)
}
/// # Specification
/// trivial.
fn path(sig: &SignatureRef) -> Protype
{
    Protype::path(
        sig.clone(),
        atom(NameRef::from("A")),
        atom(NameRef::from("A")),
    )
}
/// # Specification
/// trivial.
fn refl(sig: &SignatureRef) -> Proterm
{
    Proterm::refl(sig.clone(), atom(NameRef::from("A")))
}
/// # Specification
/// trivial.
fn relation(
    src: &SignatureRef,
    tgt: &SignatureRef,
    generators: Vec<CellId>,
) -> RelationRef
{
    RelationRef::new(
        NameRef::from("R"),
        src.clone(),
        tgt.clone(),
        generators.into_boxed_slice(),
    )
}
/// # Specification
/// trivial.
fn relation_type(rel: RelationRef) -> Protype
{
    Protype::rel(rel, atom(NameRef::from("A")), atom(NameRef::from("B")))
}
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

#[test]
fn formation_observes_names_generators_and_both_seam_boundaries()
{
    let a = signature(NameRef::from("A"));
    let b = signature(NameRef::from("B"));
    let c = signature(NameRef::from("C"));
    let mut cells = CellStore::new();
    let known = cells.insert(ground_step(NameRef::from("A"), NameRef::from("B")));
    let mut foreign = CellStore::new();
    foreign.insert(ground_step(NameRef::from("A"), NameRef::from("B")));
    let missing = foreign.insert(ground_step(NameRef::from("B"), NameRef::from("C")));
    let checker = Checker::new(&[], &cells);
    let ctx = Context::new()
        .with_dom(NameRef::from("x"), a.clone())
        .with_cod(NameRef::from("y"), b.clone());
    let framed = Protype::path(
        a.clone(),
        TermRef::new(FreeTerm::ctor("F", [FreeTerm::var("x")])),
        TermRef::new(FreeTerm::var("y")),
    );
    assert_eq!(checker.check_protype(&ctx, &framed), Ok(()));
    assert_eq!(
        checker.check_protype(
            &Context::new().with_cod(NameRef::from("y"), b.clone()),
            &framed
        ),
        Err(CheckError::UndeclaredTermVar(Name::from("x")))
    );
    assert_eq!(
        checker.check_protype(
            &Context::new().with_dom(NameRef::from("x"), a.clone()),
            &framed
        ),
        Err(CheckError::UndeclaredTermVar(Name::from("y")))
    );
    let left = relation_type(relation(&a, &b, vec![known]));
    let right = relation_type(relation(&b, &c, vec![known]));
    assert_eq!(
        checker.check_protype(
            &ctx,
            &Protype::compose(left.clone(), b.clone(), right.clone())
        ),
        Ok(())
    );
    let wrong_target = relation_type(relation(&a, &c, vec![known]));
    let wrong_source = relation_type(relation(&a, &c, vec![known]));
    assert_eq!(
        checker.check_protype(
            &ctx,
            &Protype::compose(wrong_target, b.clone(), right.clone())
        ),
        Err(CheckError::ComposeSeamMismatch)
    );
    assert_eq!(
        checker.check_protype(
            &ctx,
            &Protype::compose(left.clone(), b.clone(), wrong_source)
        ),
        Err(CheckError::ComposeSeamMismatch)
    );
    assert_eq!(
        checker.check_protype(&ctx, &Protype::compose(Protype::unit(), b.clone(), right)),
        Err(CheckError::ComposeSeamMismatch)
    );
    let present = relation(&a, &b, vec![known]);
    let absent = relation(&a, &b, vec![known, missing]);
    for valid in [
        relation_type(present.clone()),
        Protype::tabulate(present),
        Protype::unit(),
        Protype::product(left.clone(), framed.clone()),
        Protype::extend_r(left.clone(), framed.clone()),
        Protype::extend_l(framed, left),
    ] {
        assert_eq!(checker.check_protype(&ctx, &valid), Ok(()));
    }
    for invalid in [
        relation_type(absent.clone()),
        Protype::tabulate(absent.clone()),
        Protype::product(Protype::unit(), Protype::tabulate(absent.clone())),
        Protype::extend_r(Protype::tabulate(absent.clone()), Protype::unit()),
        Protype::extend_l(Protype::unit(), Protype::tabulate(absent)),
    ] {
        assert_eq!(
            checker.check_protype(&ctx, &invalid),
            Err(CheckError::UnknownRelationGenerator(missing))
        );
    }
}

#[test]
fn every_constructor_has_an_accepted_and_nearest_invalid_judgment()
{
    let sig = signature(NameRef::from("A"));
    let diagonal = path(&sig);
    let unit = Protype::unit();
    let cells = CellStore::new();
    let ctx = Context::new();
    let rel = relation(&sig, &sig, vec![]);
    let env = [Derivation::id(rel.clone())];
    let checker = Checker::new(&env, &cells);
    let unit_hyp = variable(NameRef::from("u"));
    let path_hyp = variable(NameRef::from("x"));
    let function_hyp = variable(NameRef::from("f"));
    let p = variable(NameRef::from("p"));
    let s = variable(NameRef::from("s"));
    let seam = Protype::compose(unit.clone(), sig.clone(), unit.clone());
    let product = Protype::product(unit.clone(), diagonal.clone());
    let function = Protype::extend_r(unit.clone(), diagonal.clone());
    let hyps = [
        (unit_hyp.clone(), unit.clone()),
        (path_hyp.clone(), diagonal.clone()),
        (function_hyp.clone(), function),
        (p.clone(), product.clone()),
        (s.clone(), seam.clone()),
    ];
    let id = DerivationId::new(DerivationIndex::from(0_usize));
    let pairs = vec![
        (
            Proterm::var(unit_hyp.clone()),
            unit.clone(),
            Proterm::var(variable(NameRef::from("absent"))),
            unit.clone(),
            CheckError::UnboundVar(variable(NameRef::from("absent"))),
        ),
        (
            refl(&sig),
            diagonal.clone(),
            refl(&sig),
            Protype::path(
                sig.clone(),
                atom(NameRef::from("A")),
                atom(NameRef::from("B")),
            ),
            CheckError::ReflOffDiagonal,
        ),
        (
            Proterm::path_ind(unit.clone(), Proterm::unit_term(), refl(&sig)),
            unit.clone(),
            Proterm::path_ind(
                unit.clone(),
                Proterm::unit_term(),
                Proterm::var(unit_hyp.clone()),
            ),
            unit.clone(),
            CheckError::ExpectedPath,
        ),
        (
            Proterm::pair(
                Proterm::unit_term(),
                atom(NameRef::from("A")),
                Proterm::unit_term(),
            ),
            seam,
            Proterm::pair(
                Proterm::unit_term(),
                atom(NameRef::from("A")),
                Proterm::unit_term(),
            ),
            unit.clone(),
            CheckError::ExpectedCompose,
        ),
        (
            Proterm::seam_ind(Proterm::var(s), Proterm::unit_term()),
            unit.clone(),
            Proterm::seam_ind(Proterm::var(unit_hyp.clone()), Proterm::unit_term()),
            unit.clone(),
            CheckError::NotASeam,
        ),
        (
            Proterm::lam(path_hyp.clone(), Proterm::var(path_hyp.clone())),
            Protype::extend_r(unit.clone(), unit.clone()),
            Proterm::lam(path_hyp.clone(), Proterm::var(path_hyp.clone())),
            unit.clone(),
            CheckError::ExpectedExtension,
        ),
        (
            Proterm::app(Proterm::var(function_hyp.clone()), Proterm::unit_term()),
            diagonal.clone(),
            Proterm::app(Proterm::var(function_hyp), refl(&sig)),
            diagonal.clone(),
            CheckError::ReflOffDiagonal,
        ),
        (
            Proterm::prod_intro(Proterm::unit_term(), refl(&sig)),
            product,
            Proterm::prod_intro(Proterm::unit_term(), refl(&sig)),
            unit.clone(),
            CheckError::ExpectedProduct,
        ),
        (
            Proterm::proj_l(Proterm::var(p.clone())),
            unit.clone(),
            Proterm::proj_l(Proterm::var(unit_hyp.clone())),
            unit.clone(),
            CheckError::ExpectedProduct,
        ),
        (
            Proterm::proj_r(Proterm::var(p)),
            diagonal.clone(),
            Proterm::proj_r(Proterm::var(unit_hyp)),
            diagonal.clone(),
            CheckError::ExpectedProduct,
        ),
        (
            Proterm::unit_term(),
            unit.clone(),
            Proterm::unit_term(),
            diagonal.clone(),
            CheckError::ExpectedUnit,
        ),
        (
            Proterm::cert(id),
            relation_type(rel),
            Proterm::cert(id),
            unit.clone(),
            CheckError::NotEngineBacked,
        ),
    ];
    for (accepted, expected, rejected, wrong_type, error) in pairs {
        assert_eq!(checker.check(&ctx, &hyps, &accepted, &expected), Ok(()));
        assert_eq!(
            checker.check(&ctx, &hyps, &rejected, &wrong_type),
            Err(error)
        );
    }
    let sibling = Proterm::prod_intro(
        Proterm::lam(path_hyp.clone(), Proterm::var(path_hyp.clone())),
        Proterm::var(path_hyp.clone()),
    );
    let expected = Protype::product(
        Protype::extend_r(unit.clone(), unit.clone()),
        diagonal.clone(),
    );
    assert_eq!(checker.check(&ctx, &hyps, &sibling, &expected), Ok(()));
    let nested = Proterm::lam(
        path_hyp.clone(),
        Proterm::lam(path_hyp.clone(), Proterm::var(path_hyp.clone())),
    );
    assert_eq!(
        checker.check(
            &ctx,
            &hyps,
            &nested,
            &Protype::extend_l(
                Protype::extend_r(diagonal.clone(), diagonal.clone()),
                unit.clone()
            )
        ),
        Ok(())
    );
    let left_extension = [(
        path_hyp.clone(),
        Protype::extend_l(diagonal.clone(), unit.clone()),
    )];
    assert_eq!(
        checker.synth(
            &ctx,
            &left_extension,
            &Proterm::app(Proterm::var(path_hyp.clone()), Proterm::unit_term())
        ),
        Ok(diagonal.clone())
    );
    assert_eq!(
        checker.synth(&ctx, &hyps, &refl(&sig)),
        Ok(diagonal.clone())
    );
    assert_eq!(
        checker.synth(
            &ctx,
            &[
                (path_hyp.clone(), diagonal),
                (path_hyp.clone(), unit.clone())
            ],
            &Proterm::var(path_hyp)
        ),
        Ok(unit.clone())
    );
    for term in [
        Proterm::unit_term(),
        Proterm::cert(id),
        Proterm::lam(variable(NameRef::from("q")), Proterm::unit_term()),
        Proterm::prod_intro(Proterm::unit_term(), Proterm::unit_term()),
        Proterm::pair(
            Proterm::unit_term(),
            atom(NameRef::from("A")),
            Proterm::unit_term(),
        ),
        Proterm::path_ind(unit, Proterm::unit_term(), refl(&sig)),
        Proterm::seam_ind(Proterm::unit_term(), Proterm::unit_term()),
    ] {
        assert_eq!(
            checker.synth(&ctx, &hyps, &term),
            Err(CheckError::CannotSynthesize)
        );
    }
}

/// # Specification
/// trivial.
fn certificate_fixture() -> (CellStore, Tracelet)
{
    let mut cells = CellStore::new();
    let left = cells.insert(ground_step(NameRef::from("A"), NameRef::from("B")));
    let right = cells.insert(ground_step(NameRef::from("B"), NameRef::from("C")));
    let overlap = enumerate_overlaps(&cells)
        .into_iter()
        .find(|overlap| {
            overlap.kind == OverlapKind::Composition
                && overlap.left == left
                && overlap.right == right
        })
        .expect("the ground seam overlaps");
    let (_, certificate) = derive_fused(&overlap, &mut cells).expect("a composition overlap fuses");
    (cells, certificate)
}

#[test]
fn certificate_judgments_follow_replay_under_field_corruption()
{
    let (cells, certificate) = certificate_fixture();
    let sig = signature(NameRef::from("A"));
    let rel = relation(&sig, &sig, vec![certificate.overlap.left]);
    let id = DerivationId::new(DerivationIndex::from(0_usize));
    let term = Proterm::cert(id);
    let ty = relation_type(rel.clone());
    let wrap = |certificate| Derivation::cert(certificate, Box::from([rel.clone()]), rel.clone());
    let env = [wrap(certificate.clone())];
    let checker = Checker::new(&env, &cells);
    assert_eq!(checker.check(&Context::new(), &[], &term, &ty), Ok(()));
    assert_eq!(
        checker.check(&Context::new(), &[], &term, &path(&sig)),
        Ok(())
    );
    let missing = DerivationId::new(DerivationIndex::from(1_usize));
    assert_eq!(
        checker.check(&Context::new(), &[], &Proterm::cert(missing), &ty),
        Err(CheckError::UnboundDerivation(missing))
    );
    let mut corruptions = Vec::new();
    let mut changed = certificate.clone();
    changed.overlap.peak = ground_step(NameRef::from("Z"), NameRef::from("Q"))
        .lhs()
        .clone();
    corruptions.push(changed);
    let mut changed = certificate.clone();
    changed.joins_at = ground_step(NameRef::from("Z"), NameRef::from("Q"))
        .rhs()
        .clone();
    corruptions.push(changed);
    let mut changed = certificate.clone();
    changed.path_a.clear();
    corruptions.push(changed);
    let mut changed = certificate.clone();
    changed.path_b.clear();
    corruptions.push(changed);
    let mut changed = certificate.clone();
    changed.path_a[0].cell = certificate.overlap.right;
    corruptions.push(changed);
    let mut changed = certificate;
    changed.path_b[0].at = Pos::root().child(PositionStep::from(0_usize));
    corruptions.push(changed);
    for changed in corruptions {
        assert!(!bool::from(changed.replay(&cells)));
        let env = [wrap(changed)];
        let checker = Checker::new(&env, &cells);
        assert_eq!(
            checker.check(&Context::new(), &[], &term, &ty),
            Err(CheckError::CertDoesNotReplay(id))
        );
    }
}

#[test]
fn deep_syntax_checks_and_drops_on_a_small_stack()
{
    std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(|| {
            let mut ty = Protype::unit();
            let mut term = Proterm::unit_term();
            for _ in 0_usize .. 10_000_usize {
                ty = Protype::product(Protype::unit(), ty);
                term = Proterm::prod_intro(Proterm::unit_term(), term);
            }
            let cells = CellStore::new();
            let checker = Checker::new(&[], &cells);
            assert_eq!(checker.check_protype(&Context::new(), &ty), Ok(()));
            assert_eq!(checker.check(&Context::new(), &[], &term, &ty), Ok(()));
        })
        .expect("the witness thread starts")
        .join()
        .expect("deep checking and destruction stay iterative");
}

#[test]
fn description_registry_retains_generic_grades_and_first_identity()
{
    use gandr_theory_levitation::Attrs;
    use gandr_theory_levitation::Code;
    use gandr_theory_levitation::CtorDesc;
    use gandr_theory_levitation::DeclPolarity;
    use gandr_theory_levitation::PrimTy;
    use gandr_theory_levitation::SignDesc;
    use gandr_theory_levitation::ValueTypeRef;
    use gandr_theory_virtual_doctrines::DescTable;
    use gandr_theory_virtual_doctrines::vdc::description_lookup;
    use quenchant_shape::shape::Maybe;
    let id = NominalId::new(7_u64.into(), "Graded");
    let field = Code::field(
        ValueTypeRef::prim(PrimTy::StringTy),
        Name::from("linear"),
        Attrs::empty(),
    );
    let original = SignDesc::new(
        id.clone(),
        [],
        [CtorDesc::new("Wrap", field, "Graded", Attrs::empty())],
        [],
        [],
        DeclPolarity::Data,
        Attrs::empty(),
    );
    let mut table = DescTable::<Name>::new();
    assert_eq!(
        table.get(&id),
        Maybe::Absent(description_lookup::Absent::Unregistered)
    );
    assert_eq!(
        table.insert(original.clone()),
        SignatureRef::single(id.clone())
    );
    let mut duplicate = original.clone();
    duplicate.ctors[0].code = Code::field(
        ValueTypeRef::prim(PrimTy::StringTy),
        Name::from("unrestricted"),
        Attrs::empty(),
    );
    table.insert(duplicate);
    assert_eq!(table.get(&id), Maybe::Present(&original));
    assert_eq!(
        table.get(&NominalId::new(8_u64.into(), "Graded")),
        Maybe::Absent(description_lookup::Absent::Unregistered)
    );
}
