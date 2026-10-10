//! Finite witnesses for the alphabet's content-faithfulness contract: paired
//! fixtures differ in one content component at a time, on both shipped
//! alphabets. The adversarial alphabets supply named exceptions; these cases
//! do not claim collision freedom for every possible cell.

use anodized::spec;
use gandr_theory_cell_complexes::Cell;
use gandr_theory_cell_complexes::CellAlphabet;
use gandr_theory_cell_complexes::CellProvenance;
use gandr_theory_cell_complexes::CmdPat;
use gandr_theory_cell_complexes::ConsPat;
use gandr_theory_cell_complexes::Orientation;
use gandr_theory_cell_complexes::Polarity;
use gandr_theory_cell_complexes::PositionOrder;
use gandr_theory_cell_complexes::ProdPat;
use gandr_theory_cell_complexes::SequentAlphabet;
use gandr_theory_cell_complexes_tools::CollidingAddresses;
use gandr_theory_cell_complexes_tools::IncomparablePositions;
use gandr_theory_cell_complexes_tools::Lying;
use gandr_theory_cell_complexes_tools::Toy;
use gandr_theory_cell_complexes_tools::ToyAlphabet;
use gandr_theory_cell_complexes_tools::ToyOrient;
use gandr_theory_cell_complexes_tools::ToyProv;
use gandr_theory_cell_complexes_tools::lying_cell;
use gandr_theory_cell_complexes_tools::reoriented_lying_cell;
use gandr_theory_cell_complexes_tools::toy_cell;
use gandr_theory_deep_inference::prim_address;

/// The two constructor names the sequent fixtures distinguish cells by.
#[derive(Clone, Copy)]
enum SequentCtor
{
    /// `Zero`.
    Zero,
    /// `Succ`.
    Succ,
}

/// Assert that two cells differ in content and that their root primitive
/// addresses differ too.
///
/// # Specification
/// - ensures: the inputs differ structurally and their root primitive addresses
///   differ.
/// - panics: when the cells are equal or their addresses coincide.
///
/// # Adequacy
/// - hypothesis: L3 — paired cells differing in the left face, right face,
///   orientation or provenance, for each shipped alphabet. Structural
///   inequality and the two root digests distinguish omitted content
///   components; the finite cases do not establish universal collision freedom.
/// - witness: `tests::content_faithfulness::production_alphabets_satisfy_content_faithfulness`
#[spec(ensures: left != right
    && prim_address(left, &A::root_position()) != prim_address(right, &A::root_position()))]
fn assert_digest_distinguishes<A>(
    left: &Cell<A>,
    right: &Cell<A>,
) where
    A: CellAlphabet,
{
    assert_ne!(left, right, "the cells must describe distinct content");
    let root = A::root_position();
    assert_ne!(
        prim_address(left, &root),
        prim_address(right, &root),
        "the cell content is omitted from the local ordering digest"
    );
}

/// A toy cell over `Zero ~> Zero` with a chosen orientation and provenance.
///
/// # Specification
/// trivial.
fn tagged_toy_cell(
    orient: ToyOrient,
    provenance: ToyProv,
) -> Cell<ToyAlphabet>
{
    Cell::new(Toy::zero(), Toy::zero(), orient, provenance)
}

/// A sequent cell `⟨lhs | ⊤⟩ ~> ⟨rhs | ⊤⟩` with a chosen orientation and
/// provenance.
///
/// # Specification
/// trivial.
fn sequent_cell(
    faces: (SequentCtor, SequentCtor),
    orientation: Orientation,
    provenance: CellProvenance,
) -> Cell<SequentAlphabet>
{
    let face = |ctor: SequentCtor| {
        let name = match ctor {
            | SequentCtor::Zero => "Zero",
            | SequentCtor::Succ => "Succ",
        };
        CmdPat::cut(Polarity::Positive, ProdPat::ctor(name, []), ConsPat::top())
    };
    Cell::new(face(faces.0), face(faces.1), orientation, provenance)
}

#[test]
fn production_alphabets_satisfy_content_faithfulness()
{
    let toy_base = toy_cell(Toy::zero(), Toy::zero());
    assert_digest_distinguishes(&toy_base, &toy_cell(Toy::succ(Toy::zero()), Toy::zero()));
    assert_digest_distinguishes(&toy_base, &toy_cell(Toy::zero(), Toy::succ(Toy::zero())));
    assert_digest_distinguishes(
        &toy_base,
        &tagged_toy_cell(ToyOrient::Derived, ToyProv::Rule),
    );
    assert_digest_distinguishes(
        &tagged_toy_cell(ToyOrient::Derived, ToyProv::Rule),
        &tagged_toy_cell(ToyOrient::Derived, ToyProv::Derived),
    );
    let zero_zero = (SequentCtor::Zero, SequentCtor::Zero);
    let sequent_base = sequent_cell(
        zero_zero,
        Orientation::PolarityDerived,
        CellProvenance::SurfaceRule,
    );
    assert_digest_distinguishes(
        &sequent_base,
        &sequent_cell(
            (SequentCtor::Succ, SequentCtor::Zero),
            Orientation::PolarityDerived,
            CellProvenance::SurfaceRule,
        ),
    );
    assert_digest_distinguishes(
        &sequent_base,
        &sequent_cell(
            (SequentCtor::Zero, SequentCtor::Succ),
            Orientation::PolarityDerived,
            CellProvenance::SurfaceRule,
        ),
    );
    assert_digest_distinguishes(
        &sequent_base,
        &sequent_cell(
            zero_zero,
            Orientation::CompletionDerived,
            CellProvenance::SurfaceRule,
        ),
    );
    assert_digest_distinguishes(
        &sequent_base,
        &sequent_cell(
            zero_zero,
            Orientation::PolarityDerived,
            CellProvenance::MuMuTilde,
        ),
    );
}

#[test]
fn adversarial_alphabets_are_explicitly_exempt()
{
    let given = lying_cell::<CollidingAddresses>(Toy::succ(Toy::zero()), Toy::zero());
    let derived = reoriented_lying_cell::<CollidingAddresses>(Toy::succ(Toy::zero()), Toy::zero());
    assert_ne!(given, derived, "the two cells differ in orientation");
    let root = <Lying<CollidingAddresses> as CellAlphabet>::root_position();
    assert_eq!(
        prim_address(&given, &root),
        prim_address(&derived, &root),
        "the named collision alphabet retains its obstruction witness"
    );
    let position = <Lying<IncomparablePositions> as CellAlphabet>::root_position();
    assert_eq!(
        PositionOrder::Incomparable,
        <Lying<IncomparablePositions> as CellAlphabet>::position_order(&position, &position),
        "the named irreflexive alphabet remains an explicit adversarial witness"
    );
}

#[test]
fn same_position_dependence_separates_multiplicity()
{
    let root = ToyAlphabet::root_position();
    assert_eq!(
        PositionOrder::Same,
        ToyAlphabet::position_order(&root, &root),
        "two occurrences at one position remain dependent"
    );
    assert_eq!(
        PositionOrder::Encloses,
        ToyAlphabet::position_order(&root, &at![0]),
        "the same primitive at nested positions receives a later causal layer"
    );
}
