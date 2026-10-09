//! Cell-admission linearity, reached through a description: the refusal of a
//! rule whose left-hand side copies a hole.
//!
//! - `the_idempotence_rule_written_with_a_repeated_hole_is_refused`: `rule
//!   and(x, x) ==> x`, refused with the copy named and the respelling pointed
//!   at.
//! - `the_cancellation_rule_written_with_a_repeated_hole_is_refused`: `rule
//!   sub(x, x) ==> Off`, refused for the same reason, so the diagnostic is not
//!   tied to one operation.
//! - `the_linear_companion_rule_is_admitted`: the respelled neighbour `rule
//!   and(x, y) ==> y` is admitted, so the refusal is the copy and not the
//!   operation.
//! - `a_refused_face_does_not_stop_its_linear_neighbours`: one refused face
//!   declines by index and the description's other rules still land.

use gandr_theory_cell_complexes::CellCount;
use gandr_theory_cell_complexes::MetaVar;
use gandr_theory_computads::DeclinedFaceIndex;
use gandr_theory_computads::ElaborateError;
use gandr_theory_computads::elaborate_data_desc;
use gandr_theory_levitation::Attrs;
use gandr_theory_levitation::Code;
use gandr_theory_levitation::CtorDesc;
use gandr_theory_levitation::DeclPolarity;
use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::NominalId;
use gandr_theory_levitation::NominalSerial;
use gandr_theory_levitation::RuleFace;
use gandr_theory_levitation::SignDesc;

use crate::fixture::Ungraded;
use crate::fixture::face;

#[test]
fn the_idempotence_rule_written_with_a_repeated_hole_is_refused()
{
    let (index, diagnostic) = sole_refusal(&bit_with([face(
        FreeTerm::op("and", [FreeTerm::var("x"), FreeTerm::var("x")]),
        FreeTerm::var("x"),
    )]));
    assert_eq!(
        DeclinedFaceIndex::from(0_usize),
        index,
        "the refusal is reported against the rule member"
    );
    assert!(
        diagnostic.contains("the producer hole `x`"),
        "the diagnostic names the copy: {diagnostic}"
    );
    assert!(
        diagnostic.contains("and(x, x) ==> x") && diagnostic.contains("x - x ==> 0"),
        "the diagnostic points at the idempotence and cancellation respellings: {diagnostic}"
    );
    assert!(
        diagnostic.contains("matching through the copying cell"),
        "the diagnostic says how to respell, not only that it refused: {diagnostic}"
    );
    assert!(
        diagnostic.contains("cocommutative comonoid"),
        "the diagnostic names the type-supplied hosting generalization: {diagnostic}"
    );
}

#[test]
fn the_cancellation_rule_written_with_a_repeated_hole_is_refused()
{
    let (_, diagnostic) = sole_refusal(&bit_with([face(
        FreeTerm::op("sub", [FreeTerm::var("x"), FreeTerm::var("x")]),
        FreeTerm::ctor("Off", []),
    )]));
    assert!(
        diagnostic.contains("the producer hole `x`"),
        "the same copy is named whatever the operation: {diagnostic}"
    );
}

#[test]
fn the_linear_companion_rule_is_admitted()
{
    let elaborated = elaborate_data_desc(&bit_with([face(
        FreeTerm::op("and", [FreeTerm::var("x"), FreeTerm::var("y")]),
        FreeTerm::var("y"),
    )]));
    assert!(
        elaborated.declined_faces.is_empty(),
        "a linear rule is admitted: {:?}",
        elaborated.declined_faces
    );
    assert_eq!(
        CellCount::from(2_usize),
        elaborated.store.len(),
        "the Off frame cell and the rule cell"
    );
}

#[test]
fn a_refused_face_does_not_stop_its_linear_neighbours()
{
    let elaborated = elaborate_data_desc(&bit_with([
        face(
            FreeTerm::op("and", [FreeTerm::var("x"), FreeTerm::var("y")]),
            FreeTerm::var("y"),
        ),
        face(
            FreeTerm::op("and", [FreeTerm::var("z"), FreeTerm::var("z")]),
            FreeTerm::var("z"),
        ),
    ]));
    let [(index, ElaborateError::NonLinear(ref refusal))] = *elaborated.declined_faces
    else {
        panic!(
            "only the copying face declines: {:?}",
            elaborated.declined_faces
        );
    };
    assert_eq!(
        DeclinedFaceIndex::from(1_usize),
        index,
        "the decline is indexed to the second member"
    );
    assert_eq!(
        &MetaVar::producer("z"),
        refusal.copied(),
        "the copy the second member wrote is the one named"
    );
    assert_eq!(
        CellCount::from(2_usize),
        elaborated.store.len(),
        "the frame cell and the linear rule still land"
    );
}

/// A one-constructor `Bit` description carrying the given rule members.
///
/// # Specification
/// trivial.
fn bit_with<C>(rules: C) -> SignDesc<Ungraded>
where
    C: Into<Box<[RuleFace]>>,
{
    SignDesc::new(
        NominalId::new(NominalSerial::from(0_u64), "Bit"),
        Vec::new(),
        [CtorDesc::new("Off", Code::unit(), "Bit", Attrs::empty())],
        Vec::new(),
        rules,
        DeclPolarity::Data,
        Attrs::empty(),
    )
}

/// The one refusal a description reports: its face index and the copy
/// diagnostic's rendering.
///
/// # Specification
/// - panics: when the description declines anything else, which is a fixture
///   defect.
fn sole_refusal(desc: &SignDesc<Ungraded>) -> (DeclinedFaceIndex, String)
{
    let elaborated = elaborate_data_desc(desc);
    let [(index, ElaborateError::NonLinear(ref refusal))] = *elaborated.declined_faces
    else {
        panic!(
            "exactly one face is declined, by the copy refusal: {:?}",
            elaborated.declined_faces
        );
    };
    (index, refusal.to_string())
}
