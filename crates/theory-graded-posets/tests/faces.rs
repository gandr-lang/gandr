//! Faces of a finite shape as cells: each face holds its points as data, and
//! inclusion of points orders the faces. The corpus shapes are stated here as
//! data, one point per name.

use gandr_theory_graded_posets::GradedPoset;
use gandr_theory_stone_duality::Comparison;
use gandr_theory_stone_duality::ElementCount;

/// A face: a set of points of a carrier of at most six points, as a bit mask.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Points(pub u64);

impl Points
{
    /// Whether every point of `self` is a point of `other`.
    ///
    /// # Specification
    /// trivial.
    pub fn within(
        self,
        other: Self,
    ) -> Comparison
    {
        if self.0 & !other.0 == 0 {
            Comparison::Below
        }
        else {
            Comparison::NotBelow
        }
    }
}

/// The number of points of a carrier.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Carrier(pub u32);

/// The face that holds every point of `carrier`.
///
/// # Specification
/// trivial.
pub fn whole(carrier: Carrier) -> Points
{
    Points(
        1_u64
            .checked_shl(carrier.0)
            .and_then(|bit| bit.checked_sub(1))
            .expect("a carrier below a word"),
    )
}

/// The face poset of `faces` over `carrier`: the nonempty faces and the
/// whole carrier, each one cell, in mask order, ordered by inclusion.
///
/// # Specification
/// trivial.
pub fn face_poset(
    carrier: Carrier,
    faces: &[Points],
) -> GradedPoset<Points>
{
    let mut cells: Vec<Points> = faces
        .iter()
        .copied()
        .filter(|face| face.0 != 0)
        .chain([whole(carrier)])
        .collect();
    cells.sort_unstable();
    cells.dedup();
    // A carrier of at most six points has at most 63 nonempty faces.
    GradedPoset::new(
        cells,
        |lower, upper| lower.within(*upper),
        ElementCount::from(64_usize),
    )
    .expect("a face poset of distinct faces")
}

/// A shape that the corpus states.
pub struct CorpusShape
{
    /// The shape's name, with the corpus source that states it.
    pub named: &'static str,
    /// The carrier, one point per name.
    pub carrier: Carrier,
    /// The named faces, as masks over the points in name order.
    pub faces: Vec<Points>,
}

/// The four shapes the corpus states, their points numbered in name order.
///
/// # Specification
/// trivial.
pub fn corpus() -> Vec<CorpusShape>
{
    let shape = |named: &'static str, names: &[&str], faces: &[&[&str]]| {
        let mut sorted = names.to_vec();
        sorted.sort_unstable();
        let mask = |face: &[&str]| {
            Points(face.iter().fold(0_u64, |bits, name| {
                let point = sorted.binary_search(name).expect("a name of the carrier");
                let shift = u32::try_from(point).expect("a small point");
                bits | 1_u64.checked_shl(shift).expect("a point below a word")
            }))
        };
        CorpusShape {
            named,
            carrier: Carrier(u32::try_from(sorted.len()).expect("a small carrier")),
            faces: faces.iter().map(|face| mask(face)).collect(),
        }
    };
    vec![
        shape(
            "Two, in model/extension/zero-fiber.gandr and four sources more",
            &["p", "q"],
            &[&["p"]],
        ),
        shape(
            "Three, in model/extension/generated.gandr",
            &["p", "q", "r"],
            &[&["p"]],
        ),
        shape(
            "Config, in model/desc/record-faces.gandr",
            &["host", "port", "tls"],
            &[&["port", "tls"], &["host", "port"]],
        ),
        shape(
            "Square, in model/desc/shaped-signature.gandr",
            &["tl", "tr", "bl", "br"],
            &[
                &["tl", "bl"],
                &["tr", "br"],
                &["tl", "tr"],
                &["bl", "br"],
                &["tl"],
                &[],
            ],
        ),
    ]
}

/// The corpus shape `Square`: four sides, the corner `tl` and the empty face.
///
/// # Specification
/// trivial.
pub fn square() -> CorpusShape
{
    corpus()
        .into_iter()
        .find(|shape| shape.named.starts_with("Square"))
        .expect("the corpus states `Square`")
}
