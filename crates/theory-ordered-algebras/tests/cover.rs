//! Covers by unimodular sequences: the face cover of a lattice of sets, a
//! cover of the integers by its coefficients, the gluing of local sections,
//! and the splitting of a cocycle.

use gandr_theory_ordered_algebras::Carrier;
use gandr_theory_ordered_algebras::Chart;
use gandr_theory_ordered_algebras::Cocycle;
use gandr_theory_ordered_algebras::CommutativeRing;
use gandr_theory_ordered_algebras::Comparison;
use gandr_theory_ordered_algebras::Cover;
use gandr_theory_ordered_algebras::CoverRefusal;
use gandr_theory_ordered_algebras::InstanceName;
use gandr_theory_ordered_algebras::OrderedSemiring;
use gandr_theory_ordered_algebras::Outside;
use gandr_theory_ordered_algebras::Reach;
use gandr_theory_ordered_algebras::check;
use gandr_theory_stone_duality::Budget;
use gandr_theory_stone_duality::ElementCount;
use gandr_theory_stone_duality::ElementSet;
use gandr_theory_stone_duality::SetRing;

/// An integer of the test's ring.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Whole(i128);

/// The ring of integers under the discrete order. A check reads the integers
/// from minus two to two.
struct Integers;

/// The integers a law check reads.
const SAMPLE: [Whole; 5] = [Whole(-2), Whole(-1), Whole(0), Whole(1), Whole(2)];

/// The integers given, in order, as a vector of the test's ring.
macro_rules! wholes {
    ($($value:expr),* $(,)?) => {{
        let values: Vec<Whole> = vec![$(Whole($value)),*];
        values
    }};
}

impl OrderedSemiring for Integers
{
    type Element = Whole;

    /// The ring's name.
    ///
    /// # Specification
    /// trivial.
    fn name(&self) -> InstanceName
    {
        InstanceName::from("integers")
    }

    /// The sample of integers.
    ///
    /// # Specification
    /// trivial.
    fn carrier(&self) -> Carrier<'_, Whole>
    {
        Carrier::Generated(&SAMPLE)
    }

    /// Zero.
    ///
    /// # Specification
    /// trivial.
    fn zero(&self) -> Whole
    {
        Whole(0)
    }

    /// One.
    ///
    /// # Specification
    /// trivial.
    fn one(&self) -> Whole
    {
        Whole(1)
    }

    /// The checked sum.
    ///
    /// # Specification
    /// trivial.
    fn add(
        &self,
        left: &Whole,
        right: &Whole,
    ) -> Result<Whole, Outside>
    {
        left.0.checked_add(right.0).map(Whole).ok_or(Outside)
    }

    /// The checked product.
    ///
    /// # Specification
    /// trivial.
    fn multiply(
        &self,
        left: &Whole,
        right: &Whole,
    ) -> Result<Whole, Outside>
    {
        left.0.checked_mul(right.0).map(Whole).ok_or(Outside)
    }

    /// The discrete order.
    ///
    /// # Specification
    /// trivial.
    fn compare(
        &self,
        lower: &Whole,
        upper: &Whole,
    ) -> Comparison
    {
        if lower == upper {
            Comparison::Below
        }
        else {
            Comparison::NotBelow
        }
    }
}

impl CommutativeRing for Integers
{
    /// The checked negation.
    ///
    /// # Specification
    /// trivial.
    fn negate(
        &self,
        element: &Whole,
    ) -> Result<Whole, Outside>
    {
        element.0.checked_neg().map(Whole).ok_or(Outside)
    }
}

/// `left · right − right' · left'` in the test's ring: the numerator over
/// `f g` of `b/g − a/f`, for `f = left`, `b = right`, `g = right'` and
/// `a = left'`.
///
/// # Specification
/// trivial.
fn cross(
    left: Whole,
    right: Whole,
    other_right: Whole,
    other_left: Whole,
) -> Whole
{
    let ring = Integers;
    let first = ring.multiply(&left, &right).expect("a small product");
    let second = ring
        .multiply(&other_right, &other_left)
        .expect("a small product");
    let second = ring.negate(&second).expect("a small negation");
    ring.add(&first, &second).expect("a small sum")
}

/// The faces of the carrier `{host, port, tls}`: `secure = {port, tls}` and
/// `addr = {host, port}`.
///
/// # Specification
/// trivial.
fn faces() -> [ElementSet; 2]
{
    [ElementSet::from(0b110_u64), ElementSet::from(0b011_u64)]
}

/// The lattice the two faces generate over three points.
///
/// # Specification
/// trivial.
fn face_lattice() -> SetRing
{
    SetRing::generated(
        ElementCount::from(3_usize),
        &faces(),
        Budget::from(64_usize),
    )
    .expect("the faces generate a lattice")
}

#[test]
fn a_lattice_of_sets_is_an_ordered_semiring()
{
    let lattice = face_lattice();
    let decided = check(&lattice).expect("every law holds");
    assert_eq!(decided.reach(), Reach::Whole);
    assert_eq!(usize::from(decided.laws()), 16);
    // The meet of the two faces is `{port}`, a member.
    let [secure, addr] = faces();
    assert_eq!(
        lattice.multiply(&secure, &addr),
        Ok(ElementSet::from(0b010_u64))
    );
    // `{tls}` is no member, so a join or a meet with it is refused.
    let tls = ElementSet::from(0b100_u64);
    assert_eq!(lattice.add(&tls, &ElementSet::EMPTY), Err(Outside));
    assert_eq!(lattice.multiply(&tls, &lattice.one()), Err(Outside));
}

#[test]
fn a_face_cover_is_unimodular_and_one_face_alone_names_its_ideal()
{
    let lattice = face_lattice();
    let [secure, addr] = faces();
    let cover = Cover::of_lattice(&lattice, vec![secure, addr]).expect("the faces cover");
    assert_eq!(cover.charts(), &[secure, addr]);
    assert_eq!(cover.coefficients(), &[lattice.one(), lattice.one()]);
    // One face alone generates the ideal below it.
    assert_eq!(
        Cover::of_lattice(&lattice, vec![secure]),
        Err(CoverRefusal::NotUnimodular(secure))
    );
    // `{tls}` is no member, so it is no chart.
    assert_eq!(
        Cover::of_lattice(&lattice, vec![secure, ElementSet::from(0b100_u64)]),
        Err(CoverRefusal::NotMember(Chart::from(1_usize)))
    );
    // Each family of members covers exactly when its join is the top.
    let members = lattice.members().to_vec();
    let families = u32::try_from(members.len())
        .ok()
        .and_then(|count| 1_u32.checked_shl(count))
        .expect("a few members");
    for family in 0 .. families {
        let charts: Vec<ElementSet> = members
            .iter()
            .enumerate()
            .filter(|&(position, _)| {
                u32::try_from(position)
                    .ok()
                    .and_then(|shift| family.checked_shr(shift))
                    .is_some_and(|rest| rest & 1 == 1)
            })
            .map(|(_, &member)| member)
            .collect();
        let join = charts
            .iter()
            .fold(ElementSet::EMPTY, |join, &chart| join.union(chart));
        let verdict = Cover::of_lattice(&lattice, charts);
        if join == lattice.one() {
            assert!(verdict.is_ok(), "family {family:#b} covers");
        }
        else {
            assert_eq!(verdict, Err(CoverRefusal::NotUnimodular(join)));
        }
    }
}

#[test]
fn each_agreeing_pair_of_face_sections_glues_to_the_one_member_that_restricts_to_both()
{
    let lattice = face_lattice();
    let [secure, addr] = faces();
    let cover = Cover::of_lattice(&lattice, vec![secure, addr]).expect("the faces cover");
    let mut restricting: Vec<ElementSet> = Vec::new();
    for &first in lattice.members() {
        for &second in lattice.members() {
            restricting.clear();
            restricting.extend(
                lattice
                    .members()
                    .iter()
                    .copied()
                    .filter(|member| member.meet(secure) == first && member.meet(addr) == second),
            );
            match cover.glue(&lattice, &[first, second]) {
                Ok(glued) => assert_eq!(restricting.as_slice(), [glued].as_slice()),
                Err(refusal) => {
                    assert_eq!(restricting, Vec::<ElementSet>::new());
                    assert_eq!(
                        refusal,
                        CoverRefusal::Disagree(Chart::from(0_usize), Chart::from(1_usize))
                    );
                },
            }
        }
    }
    assert_eq!(
        cover.glue(&lattice, &[secure]),
        Err(CoverRefusal::SectionCount)
    );
}

#[test]
fn a_ring_cover_replays_its_coefficients_and_refuses_others()
{
    // `2·3 − 5 = 1`.
    let cover = Cover::replayed(&Integers, wholes![3, 5], wholes![2, -1]).expect("a cover");
    assert_eq!(cover.coefficients(), wholes![2, -1].as_slice());
    assert_eq!(
        Cover::replayed(&Integers, wholes![3, 5], wholes![2, 1]),
        Err(CoverRefusal::NotUnimodular(Whole(11)))
    );
    // `2` and `4` generate the even integers, whatever the coefficients.
    assert_eq!(
        Cover::replayed(&Integers, wholes![2, 4], wholes![1, 0]),
        Err(CoverRefusal::NotUnimodular(Whole(2)))
    );
    assert_eq!(
        Cover::replayed(&Integers, wholes![3, 5], wholes![2]),
        Err(CoverRefusal::CoefficientCount)
    );
    assert_eq!(
        Cover::replayed(&Integers, wholes![i128::MAX, 1], wholes![2, 0]),
        Err(CoverRefusal::Outside)
    );
}

#[test]
fn a_ring_cover_glues_agreeing_sections_and_names_the_first_disagreement()
{
    let pair = Cover::replayed(&Integers, wholes![3, 5], wholes![2, -1]).expect("a cover");
    // `21/3` and `35/5` are both `7`.
    assert_eq!(pair.glue(&Integers, &wholes![21, 35]), Ok(Whole(7)));
    assert_eq!(
        pair.glue(&Integers, &wholes![21, 36]),
        Err(CoverRefusal::Disagree(
            Chart::from(0_usize),
            Chart::from(1_usize)
        ))
    );
    // `−2 + 3 = 1`, and the third chart's coefficient is zero.
    let triple = Cover::replayed(&Integers, wholes![2, 3, 5], wholes![-1, 1, 0]).expect("a cover");
    assert_eq!(triple.glue(&Integers, &wholes![14, 21, 35]), Ok(Whole(7)));
    assert_eq!(
        triple.glue(&Integers, &wholes![14, 21, 30]),
        Err(CoverRefusal::Disagree(
            Chart::from(0_usize),
            Chart::from(2_usize)
        ))
    );
}

#[test]
fn a_ring_cover_splits_each_coboundary_and_refuses_a_broken_cocycle()
{
    let charts = wholes![2, 3, 5];
    let cover = Cover::replayed(&Integers, charts.clone(), wholes![-1, 1, 0]).expect("a cover");
    let pairs = [(0_usize, 1_usize), (0, 2), (1, 2)];
    let grid = SAMPLE;
    for first in grid {
        for second in grid {
            for third in grid {
                // The coboundary of `vᵢ/fᵢ`: `mᵢₖ = fᵢ vₖ − fₖ vᵢ` over `fᵢ
                // fₖ`.
                let values = [first, second, third];
                let numerators =
                    pairs.map(|(i, k)| cross(charts[i], values[k], charts[k], values[i]));
                let split = cover
                    .split(&Integers, &Cocycle::new(numerators.to_vec()))
                    .expect("a coboundary splits");
                assert_eq!(split.len(), 3);
                for ((i, k), numerator) in pairs.into_iter().zip(numerators) {
                    assert_eq!(
                        cross(charts[i], split[k], charts[k], split[i]),
                        numerator,
                        "the pair ({i}, {k}) of {values:?}"
                    );
                }
            }
        }
    }
    // `m₀₁ = 1` breaks the condition on `0, 1, 2`. The split `(−1, −1, 0)`
    // holds at `(0, 1)` and fails first at `(0, 2)`.
    assert_eq!(
        cover.split(&Integers, &Cocycle::new(wholes![1, 0, 0])),
        Err(CoverRefusal::NotCocycle(
            Chart::from(0_usize),
            Chart::from(2_usize)
        ))
    );
    assert_eq!(
        cover.split(&Integers, &Cocycle::new(wholes![0, 0])),
        Err(CoverRefusal::CocycleCount)
    );
    assert_eq!(
        cover.split(&Integers, &Cocycle::new(wholes![0, 0, 0, 0])),
        Err(CoverRefusal::CocycleCount)
    );
}
