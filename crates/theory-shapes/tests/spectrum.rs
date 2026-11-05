//! The spectrum of the lattice that the faces of a shape generate, and the
//! face poset that the shape names.
//!
//! A family of faces over a finite carrier generates a lattice of subshapes.
//! Its operations are meet and union, and its bounds are the empty face and
//! the whole carrier. Birkhoff duality pairs this finite distributive lattice
//! with the poset of its join-irreducible elements, which is its spectrum. The
//! lattice is then the lattice of down-sets of its spectrum.
//!
//! Here the spectrum is the least face at each point. That face is the meet
//! of the carrier and of every face that holds the point. The suite computes
//! it with this crate's meet. The duality crate generates the lattice and
//! reads its spectrum apart from this crate, and the two must agree. This
//! crate's entailment decides the order of the spectrum. It also decides that
//! each element of the lattice is the column disjunction of the least faces
//! below it.
//!
//! The face poset of a shape is another poset. It holds the faces that the
//! shape names and the whole carrier, ordered by inclusion. It is the spectrum
//! only under two conditions. Each member of the face poset is the least face
//! of a point. Each least face is a member of the face poset. A face that is
//! the union of smaller faces is not join-irreducible. A meet of named faces
//! that no face names is join-irreducible. The corpus has shapes of both
//! kinds.

use gandr_theory_shapes::Evidence;
use gandr_theory_shapes::Formula;
use gandr_theory_shapes::Membership;
use gandr_theory_shapes::Node;
use gandr_theory_shapes::NodeId;
use gandr_theory_shapes::Point;
use gandr_theory_shapes::PointCount;
use gandr_theory_shapes::Problem;
use gandr_theory_shapes::SetOperation;
use gandr_theory_shapes::Subshape;
use gandr_theory_shapes::Variable;
use gandr_theory_shapes::decide;
use gandr_theory_stone_duality::Budget;
use gandr_theory_stone_duality::Comparison as Order;
use gandr_theory_stone_duality::Element;
use gandr_theory_stone_duality::ElementCount;
use gandr_theory_stone_duality::ElementSet;
use gandr_theory_stone_duality::SetRing;

use crate::carriers::Mask;
use crate::carriers::points;

/// The most members a lattice or a set of down-sets here may hold: every
/// subshape of a carrier of at most six points.
///
/// # Specification
/// trivial.
fn budget() -> Budget
{
    Budget::from(64)
}

/// A set of subshapes of a carrier of at most six points, as a bit mask over
/// their masks: the bit at a mask is set when the set holds that mask.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Family(u64);

impl Family
{
    /// The family that holds exactly one mask.
    ///
    /// # Specification
    /// trivial.
    pub fn single(mask: Mask) -> Self
    {
        let shift = u32::try_from(mask.0).expect("a small mask");
        Self(
            1_u64
                .checked_shl(shift)
                .expect("a mask of at most six points"),
        )
    }

    /// The family of every subshape of a carrier of at most five points.
    ///
    /// # Specification
    /// trivial.
    fn every(carrier: PointCount) -> Self
    {
        let width = u32::try_from(usize::from(carrier)).expect("a small carrier");
        let count = 1_u32.checked_shl(width).expect("a small carrier");
        Self(
            1_u64
                .checked_shl(count)
                .and_then(|bit| bit.checked_sub(1))
                .expect("a carrier of at most five points"),
        )
    }

    /// The family that also holds `mask`.
    ///
    /// # Specification
    /// trivial.
    fn with(
        self,
        mask: Mask,
    ) -> Self
    {
        Self(self.0 | Self::single(mask).0)
    }

    /// Whether the family holds `mask`.
    ///
    /// # Specification
    /// trivial.
    fn holds(
        self,
        mask: Mask,
    ) -> Membership
    {
        if self.0 & Self::single(mask).0 == 0 {
            Membership::Outside
        }
        else {
            Membership::Inside
        }
    }

    /// The masks the family holds, in mask order.
    ///
    /// # Specification
    /// trivial.
    pub fn members(self) -> impl Iterator<Item = Mask>
    {
        (0 .. 64_usize)
            .map(Mask)
            .filter(move |mask| self.holds(*mask) == Membership::Inside)
    }

    /// The masks of this family that `other` lacks.
    ///
    /// # Specification
    /// trivial.
    fn without(
        self,
        other: Self,
    ) -> Self
    {
        Self(self.0 & !other.0)
    }
}

/// The mask of every point of a carrier of fewer points than a word has
/// bits.
///
/// # Specification
/// trivial.
pub fn whole(carrier: PointCount) -> Mask
{
    let width = u32::try_from(usize::from(carrier)).expect("a small carrier");
    Mask(
        1_usize
            .checked_shl(width)
            .and_then(|bit| bit.checked_sub(1))
            .expect("a carrier of fewer points than a word has bits"),
    )
}

/// Whether every point of `lower` is a point of `upper`.
///
/// # Specification
/// trivial.
pub fn included(
    lower: Mask,
    upper: Mask,
) -> Membership
{
    if lower.0 & upper.0 == lower.0 {
        Membership::Inside
    }
    else {
        Membership::Outside
    }
}

/// The mask that holds exactly the points inside a subshape.
///
/// # Specification
/// trivial.
fn mask_of(shape: &Subshape) -> Mask
{
    let mut bits = 0_usize;
    for (point, decision) in shape.decisions().iter().enumerate() {
        if *decision == Membership::Inside {
            let shift = u32::try_from(point).expect("a small point");
            bits |= 1_usize.checked_shl(shift).expect("a point below a word");
        }
    }
    Mask(bits)
}

/// The subshape of a carrier that holds exactly the points of a mask.
///
/// # Specification
/// trivial.
fn shape_of(
    carrier: PointCount,
    mask: Mask,
) -> Subshape
{
    let inside: Vec<Point> = points(carrier)
        .filter(|point| mask.at(*point) == Membership::Inside)
        .collect();
    Subshape::new(carrier, &inside).expect("a subset of the carrier")
}

/// The element set of the duality crate that holds the points of a mask.
///
/// # Specification
/// trivial.
fn set_of(mask: Mask) -> ElementSet
{
    ElementSet::from(u64::try_from(mask.0).expect("a mask below a word"))
}

/// The family of the masks of some element sets of the duality crate.
///
/// # Specification
/// trivial.
fn family_of(sets: &[ElementSet]) -> Family
{
    sets.iter()
        .map(|set| Mask(usize::try_from(u64::from(*set)).expect("a mask below a word")))
        .fold(Family::default(), Family::with)
}

/// The least face at each point, by the crate's meet: the meet of the whole
/// carrier and of every face that holds the point.
///
/// # Specification
/// trivial.
fn least_faces(
    carrier: PointCount,
    faces: &[Subshape],
) -> Family
{
    let everything = shape_of(carrier, whole(carrier));
    let mut least = Family::default();
    for point in points(carrier) {
        // No face met yet stands for the whole carrier, so the carrier is
        // never copied.
        let mut meet: Option<Subshape> = None;
        for face in faces {
            if face.contains(point) == Ok(Membership::Inside) {
                let so_far = meet.as_ref().unwrap_or(&everything);
                meet = Some(
                    so_far
                        .combine(face, SetOperation::Meet)
                        .expect("faces of one carrier"),
                );
            }
        }
        least = least.with(meet.as_ref().map_or_else(|| whole(carrier), mask_of));
    }
    least
}

/// The answer of the crate's entailment.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Verdict
{
    /// The premise entails the conclusion.
    Holds,
    /// A point satisfies the premise and falsifies the conclusion.
    Refuted,
}

/// Decides `x ∈ P ⊢ x ∈ S₁ ∨ … ∨ x ∈ Sₙ` over one carrier with the crate's
/// entailment, and validates the evidence. The conclusion is `⊥` when the
/// family is empty.
///
/// # Specification
/// trivial.
pub fn entails(
    carrier: PointCount,
    premise: Mask,
    conclusion: Family,
) -> Verdict
{
    let atom = |mask: Mask| Node::Member(Variable::from(0_usize), shape_of(carrier, mask));
    let mut nodes: Vec<Node> = conclusion.members().map(atom).collect();
    let operands = nodes.len();
    if nodes.is_empty() {
        nodes.push(Node::Bottom);
    }
    let mut root = 0_usize;
    for operand in 1 .. operands {
        nodes.push(Node::Or(NodeId::from(root), NodeId::from(operand)));
        root = nodes.len().saturating_sub(1);
    }
    let premise = Formula::new(vec![atom(premise)]).expect("one atom");
    let conclusion = Formula::new(nodes).expect("an ordered table");
    let problem = Problem::new(vec![carrier], premise, conclusion).expect("a column query");
    match decide(&problem).expect("a decision") {
        Evidence::Holds(derivation) => {
            assert_eq!(derivation.validate(&problem), Ok(()));
            Verdict::Holds
        },
        Evidence::Refuted(model) => {
            assert_eq!(model.validate(&problem), Ok(()));
            Verdict::Refuted
        },
    }
}

/// Checks Birkhoff duality for one family of faces over a carrier, and
/// returns the spectrum.
///
/// The least faces are the join-irreducible elements of the lattice that the
/// duality crate generates. This crate's entailment orders them as the
/// duality crate's spectrum orders them. It decides each element of the
/// lattice equal to the column disjunction of the least faces below it. The
/// down-sets of the spectrum read back to distinct elements, and these
/// elements are the lattice.
///
/// # Specification
/// trivial.
fn spectrum(
    carrier: PointCount,
    faces: Family,
) -> Family
{
    let shapes: Vec<Subshape> = faces
        .members()
        .map(|face| shape_of(carrier, face))
        .collect();
    let least = least_faces(carrier, &shapes);
    let generators: Vec<ElementSet> = faces.members().map(set_of).collect();
    let elements = ElementCount::from(usize::from(carrier));
    let ring = SetRing::generated(elements, &generators, budget()).expect("a small lattice");
    let dual = ring.spectrum().expect("a spectrum");
    assert_eq!(
        least,
        family_of(dual.points()),
        "the least faces of {faces:?} over {carrier:?}"
    );
    for (lower, below) in dual.points().iter().enumerate() {
        for (upper, above) in dual.points().iter().enumerate() {
            let order = match dual
                .poset()
                .compare(Element::from(lower), Element::from(upper))
            {
                Ok(Order::Below) => Verdict::Holds,
                Ok(Order::NotBelow) => Verdict::Refuted,
                Err(error) => panic!("a point of the spectrum refused by {error:?}"),
            };
            let below = Mask(usize::try_from(u64::from(*below)).expect("a mask below a word"));
            let above = Mask(usize::try_from(u64::from(*above)).expect("a mask below a word"));
            assert_eq!(entails(carrier, below, Family::single(above)), order);
        }
    }
    let lattice = family_of(ring.members());
    for element in lattice.members() {
        let below = least
            .members()
            .filter(|face| included(*face, element) == Membership::Inside)
            .fold(Family::default(), Family::with);
        assert_eq!(entails(carrier, element, below), Verdict::Holds);
        for face in below.members() {
            assert_eq!(
                entails(carrier, face, Family::single(element)),
                Verdict::Holds
            );
        }
    }
    let downs = dual.poset().down_sets(budget()).expect("a small lattice");
    let unions: Vec<ElementSet> = downs
        .members()
        .iter()
        .map(|down| dual.member(*down).expect("a down-set of the spectrum"))
        .collect();
    let unions = family_of(&unions);
    assert_eq!(
        unions.members().count(),
        downs.members().len(),
        "two down-sets of {least:?} unite to one face"
    );
    assert_eq!(unions, lattice);
    least
}

/// How the face poset of a shape stands against the spectrum of its faces.
#[derive(Debug, Default, Eq, PartialEq)]
struct Comparison
{
    /// The members of the face poset that are no point's least face. Each is
    /// the union of the least faces below it.
    unions: Family,
    /// The least faces that the face poset lacks. Each is a meet of named
    /// faces.
    meets: Family,
}

/// Sets the face poset of a shape against the spectrum of its faces. The
/// face poset holds the nonempty named faces and the whole carrier.
///
/// # Specification
/// trivial.
fn compare(
    carrier: PointCount,
    faces: Family,
    spectrum: Family,
) -> Comparison
{
    let poset = faces.with(whole(carrier)).without(Family::single(Mask(0)));
    Comparison {
        unions: poset.without(spectrum),
        meets: spectrum.without(poset),
    }
}

/// A shape that the corpus states, with the comparison its faces give.
pub struct CorpusShape
{
    /// The shape's name, with the corpus source that states it.
    pub named: &'static str,
    /// The carrier, one point per name.
    pub carrier: PointCount,
    /// The named faces, as masks over the points in name order.
    pub faces: Family,
    /// The face poset against the spectrum.
    against: Comparison,
}

/// Every shape that the corpus states and checks, with its points in name
/// order. A record type without a face block is a family with no face, and
/// the exhaustive suite holds every such family of up to three labels.
///
/// # Specification
/// trivial.
pub fn corpus() -> Vec<CorpusShape>
{
    let shape = |named: &'static str,
                 names: &[&str],
                 faces: &[&[&str]],
                 unions: &[&[&str]],
                 meets: &[&[&str]]| {
        let mut sorted = names.to_vec();
        sorted.sort_unstable();
        let mask = |face: &[&str]| {
            Mask(face.iter().fold(0_usize, |bits, name| {
                let point = sorted.binary_search(name).expect("a name of the carrier");
                let shift = u32::try_from(point).expect("a small point");
                bits | 1_usize.checked_shl(shift).expect("a point below a word")
            }))
        };
        let family = |listed: &[&[&str]]| {
            listed
                .iter()
                .map(|face| mask(face))
                .fold(Family::default(), Family::with)
        };
        CorpusShape {
            named,
            carrier: PointCount::from(sorted.len()),
            faces: family(faces),
            against: Comparison {
                unions: family(unions),
                meets: family(meets),
            },
        }
    };
    vec![
        shape(
            "Two, in model/extension/zero-fiber.gandr and four sources more",
            &["p", "q"],
            &[&["p"]],
            &[],
            &[],
        ),
        shape(
            "Three, in model/extension/generated.gandr",
            &["p", "q", "r"],
            &[&["p"]],
            &[],
            &[],
        ),
        shape(
            "Config, in model/desc/record-faces.gandr",
            &["host", "port", "tls"],
            &[&["port", "tls"], &["host", "port"]],
            &[&["host", "port", "tls"]],
            &[&["port"]],
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
            &[
                &["tl", "bl"],
                &["tr", "br"],
                &["tl", "tr"],
                &["bl", "br"],
                &["tl", "tr", "bl", "br"],
            ],
            &[&["bl"], &["br"], &["tr"]],
        ),
    ]
}

#[test]
fn the_least_faces_are_the_spectrum_of_every_small_face_family()
{
    for size in 0 ..= 3_usize {
        let carrier = PointCount::from(size);
        let every = Family::every(carrier);
        for family in 0 ..= every.0 {
            let _spectrum = spectrum(carrier, Family(family));
        }
    }
}

#[test]
fn every_subshape_as_a_face_makes_the_points_the_spectrum()
{
    // An atom of a face formula takes any subshape of its carrier. Over one
    // variable these atoms generate every subshape, a Boolean algebra. Its
    // spectrum is the points, and no point is below another.
    for size in 0 ..= 4_usize {
        let carrier = PointCount::from(size);
        let singletons = points(carrier)
            .map(|point| {
                let shift = u32::try_from(usize::from(point)).expect("a small point");
                Mask(1_usize.checked_shl(shift).expect("a point below a word"))
            })
            .fold(Family::default(), Family::with);
        assert_eq!(spectrum(carrier, Family::every(carrier)), singletons);
    }
}

#[test]
fn the_face_poset_is_the_spectrum_only_where_each_face_is_a_least_face()
{
    // `Two` and `Three` agree. `Config` names two faces that meet at `port`
    // and unite to the carrier. `Square` names four sides that are unions of
    // corners, and one of its four corners.
    for shape in corpus() {
        let spectrum = spectrum(shape.carrier, shape.faces);
        assert_eq!(
            compare(shape.carrier, shape.faces, spectrum),
            shape.against,
            "{}",
            shape.named
        );
    }
}
