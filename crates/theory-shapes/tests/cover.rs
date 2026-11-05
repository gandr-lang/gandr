//! Probe 6 of the presented-spaces frame: a face cover glued through a
//! cellular sheaf over the graded poset of its faces and their meets.
//!
//! A face cover splits a term over the faces of a finite shape, one arm for
//! each face. A face is a set of points, so two faces can overlap, and the two
//! arms must then agree on each point of the meet. The agreement check that
//! the face cover of #5106 names is this crate's [`UnionSquare::mediator`],
//! one square for each pair of faces. It refuses the first point of the meet
//! where the two arms differ.
//!
//! The probe states the same condition as gluing. The cells of the site are
//! the faces and their pairwise meets, ordered by inclusion of their points in
//! a graded poset of `gandr-theory-graded-posets`. The stalk at a cell is one
//! value for each of its points, and the restriction from a face to a meet
//! below it keeps the values at the meet's points. The arms are the sections
//! on the faces. They glue when, at the meet of each two faces, their
//! restrictions agree. The probe reads each meet from the poset's bit rows:
//! the cells below both faces, and the one of them whose closure is that set.
//!
//! The probe passes when the gluing and the agreement check give the same
//! verdict on each pair of each cover, and each refusal names the meet where
//! the two arms differ and its first point there.

use gandr_theory_graded_posets::GradedPoset;
use gandr_theory_shapes::Membership;
use gandr_theory_shapes::Point;
use gandr_theory_shapes::PointCount;
use gandr_theory_shapes::ShapeError;
use gandr_theory_shapes::Subshape;
use gandr_theory_shapes::UnionSquare;
use gandr_theory_stone_duality::Comparison;
use gandr_theory_stone_duality::Element;
use gandr_theory_stone_duality::ElementSet;

use crate::carriers::Mask;
use crate::carriers::points;
use crate::spectrum::corpus;
use crate::spectrum::included;

/// The value an arm takes at a point.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Value(u8);

/// The place of a face in its cover.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct FaceIndex(usize);

/// One face's arm: one value for each point of the face, in carrier order.
type Arm = Vec<Value>;

/// What a probe run names its cover by in a failure.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Named(&'static str);

/// Where two arms of a cover differ.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Disagreement
{
    /// The two faces, the earlier first.
    faces: (FaceIndex, FaceIndex),
    /// The meet of the two faces.
    meet: Mask,
    /// The first point of the meet where the arms differ.
    point: Point,
}

/// The site of a cover: the faces and their pairwise meets as the cells of a
/// graded poset, and each face's cell.
struct Site
{
    /// The cells, ordered by inclusion of their points.
    poset: GradedPoset<Mask>,
    /// The cell of each face of the cover.
    faces: Vec<Element>,
}

/// The site of the faces `faces` of one carrier.
///
/// # Specification
/// trivial.
fn site(faces: &[Mask]) -> Site
{
    let mut cells: Vec<Mask> = Vec::with_capacity(faces.len().saturating_mul(faces.len()));
    cells.extend_from_slice(faces);
    for (index, left) in faces.iter().enumerate() {
        for right in faces.iter().skip(index.saturating_add(1)) {
            cells.push(Mask(left.0 & right.0));
        }
    }
    cells.sort_unstable_by_key(|cell| cell.0);
    cells.dedup();
    let cell_of = |face: Mask| {
        Element::from(
            cells
                .binary_search_by_key(&face.0, |cell| cell.0)
                .expect("each face is a cell"),
        )
    };
    let face_cells = faces.iter().map(|&face| cell_of(face)).collect();
    let poset = GradedPoset::new(cells, |lower, upper| match included(*lower, *upper) {
        Membership::Inside => Comparison::Below,
        Membership::Outside => Comparison::NotBelow,
    })
    .expect("distinct cells of one carrier");
    Site {
        poset,
        faces: face_cells,
    }
}

/// The meet of two cells, read from the poset's bit rows: the cell whose
/// closure is the set of cells below both.
///
/// # Specification
/// trivial.
fn meet(
    poset: &GradedPoset<Mask>,
    left: Element,
    right: Element,
) -> Element
{
    let below = u64::from(poset.closure(left).expect("a cell"))
        & u64::from(poset.closure(right).expect("a cell"));
    ElementSet::from(below)
        .elements()
        .find(|&cell| u64::from(poset.closure(cell).expect("a cell")) == below)
        .expect("the meet of two faces is a cell")
}

/// The values of an arm on `face` at the points of `meet`, the restriction of
/// the sheaf from the face to the meet.
///
/// # Specification
/// trivial.
fn restriction(
    carrier: PointCount,
    (face, arm): (Mask, &[Value]),
    meet: Mask,
) -> Vec<(Point, Value)>
{
    points(carrier)
        .filter(|&point| face.at(point) == Membership::Inside)
        .zip(arm.iter().copied())
        .filter(|&(point, _)| meet.at(point) == Membership::Inside)
        .collect()
}

/// The gluing of `arms` over the site of `faces`: each pair of faces whose
/// restrictions to their meet differ, in pair order.
///
/// # Specification
/// trivial.
fn glued(
    carrier: PointCount,
    faces: &[Mask],
    arms: &[Arm],
) -> Vec<Disagreement>
{
    let site = site(faces);
    let mut refusals = Vec::new();
    for (first, (&left_cell, (&left, left_arm))) in
        site.faces.iter().zip(faces.iter().zip(arms)).enumerate()
    {
        for (second, (&right_cell, (&right, right_arm))) in site
            .faces
            .iter()
            .zip(faces.iter().zip(arms))
            .enumerate()
            .skip(first.saturating_add(1))
        {
            let cell = meet(&site.poset, left_cell, right_cell);
            let shared = *site
                .poset
                .cells()
                .get(usize::from(cell))
                .expect("a cell of the site");
            let differs = restriction(carrier, (left, left_arm), shared)
                .into_iter()
                .zip(restriction(carrier, (right, right_arm), shared))
                .find(|&((_, from_left), (_, from_right))| from_left != from_right);
            if let Some(((point, _), _)) = differs {
                refusals.push(Disagreement {
                    faces: (FaceIndex(first), FaceIndex(second)),
                    meet: shared,
                    point,
                });
            }
        }
    }
    refusals
}

/// The subshape of a mask's points.
///
/// # Specification
/// trivial.
fn subshape(
    carrier: PointCount,
    mask: Mask,
) -> Subshape
{
    let inside: Vec<Point> = points(carrier)
        .filter(|&point| mask.at(point) == Membership::Inside)
        .collect();
    Subshape::new(carrier, &inside).expect("a subset of the carrier")
}

/// The agreement check of the face cover: one union square for each pair of
/// faces, its mediator refusing the first point of the meet where the arms
/// differ. A pair the check cannot read is an error.
///
/// # Specification
/// trivial.
fn agreed(
    carrier: PointCount,
    faces: &[Mask],
    arms: &[Arm],
) -> Result<Vec<(FaceIndex, FaceIndex, Point)>, ShapeError>
{
    let shapes: Vec<Subshape> = faces.iter().map(|&face| subshape(carrier, face)).collect();
    let mut refusals = Vec::new();
    for (first, (left, left_arm)) in shapes.iter().zip(arms).enumerate() {
        for (second, (right, right_arm)) in shapes
            .iter()
            .zip(arms)
            .enumerate()
            .skip(first.saturating_add(1))
        {
            match UnionSquare::new(left, right)?.mediator(left_arm, right_arm) {
                Ok(_) => {},
                Err(ShapeError::Disagreement(point)) => {
                    refusals.push((FaceIndex(first), FaceIndex(second), point));
                },
                Err(error) => return Err(error),
            }
        }
    }
    Ok(refusals)
}

/// How a run of the probe over many covers stands.
#[derive(Debug, Default, Eq, PartialEq)]
struct Tally
{
    /// Covers with their arms, checked both ways.
    covers: usize,
    /// Pairs of faces whose arms agree on the meet.
    glued: usize,
    /// Pairs of faces whose arms differ on the meet.
    refused: usize,
}

/// Every choice of arms for `faces`, each value zero or one, in counting
/// order.
///
/// # Specification
/// trivial.
fn every_arms(
    carrier: PointCount,
    faces: &[Mask],
) -> Vec<Vec<Arm>>
{
    let sizes: Vec<usize> = faces
        .iter()
        .map(|&face| {
            points(carrier)
                .filter(|&point| face.at(point) == Membership::Inside)
                .count()
        })
        .collect();
    let width = u32::try_from(sizes.iter().sum::<usize>()).expect("a small cover");
    let count = 1_u64.checked_shl(width).expect("a small cover");
    (0 .. count)
        .map(|bits| {
            let mut offset = 0_u32;
            sizes
                .iter()
                .map(|&size| {
                    core::iter::repeat_with(|| {
                        let value = Value(u8::from(bits.checked_shr(offset).unwrap_or(0) & 1 == 1));
                        offset = offset.saturating_add(1);
                        value
                    })
                    .take(size)
                    .collect()
                })
                .collect()
        })
        .collect()
}

/// Checks every choice of arms on the cover `faces` both ways and adds the
/// verdicts to `tally`.
///
/// # Specification
/// trivial.
fn probe(
    named: Named,
    carrier: PointCount,
    faces: &[Mask],
    tally: &mut Tally,
)
{
    let Named(named) = named;
    let mut named_by_gluing: Vec<(FaceIndex, FaceIndex, Point)> = Vec::new();
    for arms in every_arms(carrier, faces) {
        let refusals = glued(carrier, faces, &arms);
        let checked = agreed(carrier, faces, &arms).unwrap_or_else(|error| {
            panic!("{named}: the agreement check cannot read {faces:?}: {error:?}")
        });
        named_by_gluing.clear();
        named_by_gluing.extend(
            refusals
                .iter()
                .map(|refusal| (refusal.faces.0, refusal.faces.1, refusal.point)),
        );
        assert_eq!(
            named_by_gluing, checked,
            "{named}: the gluing and the agreement check differ on {faces:?} with {arms:?}"
        );
        for refusal in &refusals {
            let (Some(left), Some(right)) =
                (faces.get(refusal.faces.0.0), faces.get(refusal.faces.1.0))
            else {
                panic!("{named}: a refusal names two faces of the cover");
            };
            assert_eq!(
                refusal.meet.0,
                left.0 & right.0,
                "{named}: a refusal names the meet of its two faces"
            );
            assert_eq!(
                refusal.meet.at(refusal.point),
                Membership::Inside,
                "{named}: a refusal names a point of the meet"
            );
        }
        let pairs: usize = (1 .. faces.len()).sum();
        tally.covers = tally.covers.saturating_add(1);
        tally.refused = tally.refused.saturating_add(refusals.len());
        tally.glued = tally
            .glued
            .saturating_add(pairs.saturating_sub(refusals.len()));
    }
}

#[test]
fn config_glues_on_port_and_refuses_naming_port()
{
    // The face cover of #5106: `secure = {port, tls}` and `addr = {host,
    // port}` over `{host, port, tls}`, the points in name order. The arms glue
    // when they agree at `port`, and the refusal names the meet `{port}`.
    let carrier = PointCount::from(3_usize);
    let (host, port, tls) = (
        Point::from(0_usize),
        Point::from(1_usize),
        Point::from(2_usize),
    );
    let secure = Mask(0b110);
    let addr = Mask(0b011);
    let faces = [secure, addr];
    let site = site(&faces);
    let shared = meet(&site.poset, site.faces[0], site.faces[1]);
    assert_eq!(
        site.poset.cells().get(usize::from(shared)),
        Some(&Mask(0b010)),
        "the meet of `secure` and `addr` is the cell of `port` alone"
    );
    let agreeing = [vec![Value(1), Value(0)], vec![Value(0), Value(1)]];
    assert_eq!(glued(carrier, &faces, &agreeing), []);
    assert_eq!(agreed(carrier, &faces, &agreeing), Ok(vec![]));
    let parting = [vec![Value(1), Value(0)], vec![Value(0), Value(0)]];
    assert_eq!(glued(carrier, &faces, &parting), [Disagreement {
        faces: (FaceIndex(0), FaceIndex(1)),
        meet: Mask(0b010),
        point: port,
    }]);
    assert_eq!(
        agreed(carrier, &faces, &parting),
        Ok(vec![(FaceIndex(0), FaceIndex(1), port)])
    );
    assert_ne!(host, tls, "the points outside the meet carry no condition");
}

#[test]
fn every_corpus_cover_glues_as_the_agreement_check_decides()
{
    // Each corpus shape's cover is its nonempty named faces, and every choice
    // of arms with values zero and one is glued both ways.
    let mut tally = Tally::default();
    let mut faces: Vec<Mask> = Vec::new();
    for shape in corpus() {
        faces.clear();
        faces.extend(shape.faces.members().filter(|face| face.0 != 0));
        probe(Named(shape.named), shape.carrier, &faces, &mut tally);
    }
    assert!(
        tally.glued > 0 && tally.refused > 0 && tally.covers > 0,
        "the corpus tally: both verdicts occur, so the comparison is not vacuous: {tally:?}"
    );
}

#[test]
fn every_small_cover_glues_as_the_agreement_check_decides()
{
    // Every cover of two or three distinct nonempty faces over a carrier of up
    // to three points, with every choice of arms with values zero and one.
    let mut tally = Tally::default();
    let mut faces: Vec<Mask> = Vec::new();
    for size in 1 ..= 3_usize {
        let carrier = PointCount::from(size);
        let width = u32::try_from(size).expect("a small carrier");
        let nonempty: Vec<Mask> = (1 .. 1_usize.checked_shl(width).expect("a small carrier"))
            .map(Mask)
            .collect();
        for (first, &one) in nonempty.iter().enumerate() {
            for (second, &two) in nonempty.iter().enumerate().skip(first.saturating_add(1)) {
                faces.clear();
                faces.extend([one, two]);
                probe(Named("a pair"), carrier, &faces, &mut tally);
                for &three in nonempty.iter().skip(second.saturating_add(1)) {
                    faces.clear();
                    faces.extend([one, two, three]);
                    probe(Named("a triple"), carrier, &faces, &mut tally);
                }
            }
        }
    }
    assert!(
        tally.glued > 0 && tally.refused > 0 && tally.covers > 0,
        "the generated tally: both verdicts occur, so the comparison is not vacuous: {tally:?}"
    );
}
