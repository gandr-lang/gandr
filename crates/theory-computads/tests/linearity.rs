//! Cell-admission linearity, reached through a description: the refusal of a
//! rule whose left-hand side copies a hole.

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
