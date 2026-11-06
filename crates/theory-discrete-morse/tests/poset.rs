//! A graded poset as a complex: the standing of a cell, and the faces of a
//! cell one rank down.

use gandr_theory_discrete_morse::Complex as _;
use gandr_theory_discrete_morse::Incidence;
use gandr_theory_discrete_morse::Standing;
use gandr_theory_graded_posets::GradedPoset;
use gandr_theory_stone_duality::DualityError;
use gandr_theory_stone_duality::Element;

use crate::faces::Points;
use crate::faces::face_poset;
use crate::faces::square;

/// The face poset of the corpus shape `Square`. Its points in name order are
/// `bl`, `br`, `tl` and `tr`, so its cells in mask order are the side
/// `bl br`, the corner `tl`, the side `tl bl`, the side `tr br`, the side
/// `tl tr` and the whole square.
///
/// # Specification
/// trivial.
fn square_poset() -> GradedPoset<Points>
{
    let shape = square();
    face_poset(shape.carrier, &shape.faces)
}

/// The cell of `poset` whose data is `mask`.
///
/// # Specification
/// trivial.
fn cell(
    poset: &GradedPoset<Points>,
    mask: Points,
) -> Element
{
    Element::from(
        poset
            .cells()
            .iter()
            .position(|&data| data == mask)
            .expect("a face of the square"),
    )
}

/// The faces of `of` in `poset`, as their data.
///
/// # Specification
/// trivial.
fn faces_of(
    poset: &GradedPoset<Points>,
    of: Element,
) -> Vec<(Points, Incidence)>
{
    let mut complex = poset;
    let mut faces = Vec::new();
    complex
        .faces(&of, &mut faces)
        .expect("a cell of the square");
    faces
        .into_iter()
        .map(|(face, incidence)| {
            let data = poset
                .cells()
                .get(usize::from(face))
                .copied()
                .expect("a cell of the square");
            (data, incidence)
        })
        .collect()
}

#[test]
fn the_faces_of_a_cell_lie_one_rank_down()
{
    let poset = square_poset();
    let one = Incidence::from(1_i64);
    // The whole square has rank two. Its faces are the two sides through the
    // corner `tl`, at rank one. The corner and the two other sides lie at
    // rank zero, below it but not one rank down.
    let whole = cell(&poset, Points(0b1111));
    assert_eq!(faces_of(&poset, whole), [
        (Points(0b0101), one),
        (Points(0b1100), one),
    ]);
    // A side through the corner has the corner as its one face.
    let side = cell(&poset, Points(0b0101));
    assert_eq!(faces_of(&poset, side), [(Points(0b0100), one)]);
    // A side that holds no corner has rank zero and no face.
    let bare = cell(&poset, Points(0b1010));
    assert_eq!(faces_of(&poset, bare), []);
}

#[test]
fn a_cell_past_the_count_lies_outside_the_poset()
{
    let poset = square_poset();
    let count = usize::from(poset.count());
    let mut complex = &poset;
    assert_eq!(
        complex.standing(&Element::from(count.saturating_sub(1))),
        Ok(Standing::Inside)
    );
    assert_eq!(
        complex.standing(&Element::from(count)),
        Ok(Standing::Outside)
    );
}

#[test]
fn a_cell_past_the_count_has_no_faces_to_read()
{
    let poset = square_poset();
    let past = Element::from(usize::from(poset.count()));
    let mut complex = &poset;
    let mut faces = Vec::new();
    assert_eq!(
        complex.faces(&past, &mut faces),
        Err(DualityError::ElementOutside(past))
    );
    assert!(faces.is_empty());
}
