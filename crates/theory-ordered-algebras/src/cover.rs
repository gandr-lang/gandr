//! A cover of a presented algebra by a unimodular sequence, and what its
//! partition of unity glues and splits.
//!
//! A cover is a sequence of charts `f₁, …, fₙ` with coefficients `r₁, …, rₙ`
//! whose combination `Σ rᵢ fᵢ` is one. The coefficients are the certificate:
//! [`Cover::replayed`] forms the combination with no search, and refuses a
//! sequence that is not unimodular with the combination it reaches. On a
//! lattice the sum is the join, so [`Cover::of_lattice`] writes the top as
//! each coefficient. On a ring a solve outside this crate finds them.
//!
//! A section at `fᵢ` is a numerator `aᵢ` over `fᵢ`. Two sections agree when
//! `fⱼ aᵢ = fᵢ aⱼ`, and agreeing sections glue to `Σ rᵢ aᵢ`. A Čech cocycle
//! is a numerator `mᵢₖ` over `fᵢ fₖ` for each pair, and it splits to
//! `uᵢ = −Σₖ rₖ mᵢₖ` over `fᵢ`. Each equation is checked on numerators, the
//! strict form of the equation in the localisation.

use alloc::vec;
use alloc::vec::Vec;
use core::fmt;
use core::fmt::Debug;

use anodized::spec;
use gandr_theory_stone_duality::ElementSet;
use gandr_theory_stone_duality::Membership;
use gandr_theory_stone_duality::SetRing;

use crate::signature::CommutativeRing;
use crate::signature::OrderedSemiring;
use crate::signature::Outside;

/// A chart of a cover: its position in the cover's sequence, numbered from
/// zero.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Chart(usize);

impl From<usize> for Chart
{
    /// The chart at a position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(position: usize) -> Self
    {
        Self(position)
    }
}

impl From<Chart> for usize
{
    /// The position of a chart.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(chart: Chart) -> Self
    {
        chart.0
    }
}

/// A cover of an algebra: its charts, and the coefficients whose combination
/// with the charts is one.
///
/// # Specification
/// - ensures: the charts and the coefficients are of one number, and `Σ rᵢ fᵢ`
///   is one in the algebra that replayed them.
/// - provides: the gluing of local sections and the splitting of a cocycle by
///   the partition of unity.
/// - panics: none.
/// - executable: none — a type-level block: the invariant is
///   [`Cover::replayed`]'s, which makes each cover.
///
/// # Adequacy
/// - hypothesis: L3 — a face cover, the same family with one face removed, and
///   a ring cover with coefficients that miss one, separate a replay that does
///   not compare the combination with one.
/// - witness: `tests::cover::a_face_cover_is_unimodular_and_one_face_alone_names_its_ideal`
/// - witness: `tests::cover::a_ring_cover_replays_its_coefficients_and_refuses_others`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Cover<E>
{
    /// The charts `f₁, …, fₙ`, in the cover's order.
    charts: Vec<E>,
    /// The coefficients `r₁, …, rₙ`, one for each chart.
    coefficients: Vec<E>,
}

/// A Čech cocycle on a cover: the numerator `mᵢₖ` over `fᵢ fₖ` for each pair
/// of charts `i < k`, the pairs in lexicographic order.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Cocycle<E>
{
    /// The numerators of the pairs `i < k`, in lexicographic order.
    numerators: Vec<E>,
}

impl<E> Cocycle<E>
{
    /// The cocycle with the numerators of the pairs `i < k`, in lexicographic
    /// order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(numerators: Vec<E>) -> Self
    {
        Self { numerators }
    }

    /// The numerators of the pairs `i < k`, in lexicographic order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn numerators(&self) -> &[E]
    {
        &self.numerators
    }
}

/// Why a sequence makes no cover, why local sections glue to no section, or
/// why a family of numerators is no cocycle.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CoverRefusal<E>
{
    /// The coefficients and the charts differ in number.
    CoefficientCount,
    /// A chart is no member of its lattice.
    NotMember(Chart),
    /// The combination of the charts by the coefficients is this element and
    /// not one, so the charts generate the ideal it names.
    NotUnimodular(E),
    /// The local sections and the charts differ in number.
    SectionCount,
    /// The local sections at these two charts disagree on their overlap: the
    /// first such pair, in lexicographic order.
    Disagree(Chart, Chart),
    /// The numerators and the pairs of charts differ in number.
    CocycleCount,
    /// The split of the numerators fails at these two charts, so a triple
    /// through them breaks the cocycle condition: the first such pair, in
    /// lexicographic order.
    NotCocycle(Chart, Chart),
    /// An operation leaves the elements that the algebra represents.
    Outside,
}

impl<E> From<Outside> for CoverRefusal<E>
{
    /// The refusal of an operation that leaves the represented elements.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(_outside: Outside) -> Self
    {
        Self::Outside
    }
}

impl<E> fmt::Display for CoverRefusal<E>
{
    /// Renders the refusal and the charts it names. The element of a
    /// combination that is not one stays in the value, where a caller reads
    /// it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::CoefficientCount => f.write_str("coefficients and charts differ in number"),
            Self::NotMember(chart) => {
                write!(
                    f,
                    "chart {} is no member of its lattice",
                    usize::from(chart)
                )
            },
            Self::NotUnimodular(_) => {
                f.write_str("the charts generate a proper ideal: their combination is not one")
            },
            Self::SectionCount => f.write_str("sections and charts differ in number"),
            Self::Disagree(first, second) => write!(
                f,
                "sections at charts {} and {} disagree on their overlap",
                usize::from(first),
                usize::from(second)
            ),
            Self::CocycleCount => f.write_str("numerators and pairs of charts differ in number"),
            Self::NotCocycle(first, second) => write!(
                f,
                "numerators break the cocycle condition on a triple through charts {} and {}",
                usize::from(first),
                usize::from(second)
            ),
            Self::Outside => f.write_str("an operation leaves the represented elements"),
        }
    }
}

impl<E> core::error::Error for CoverRefusal<E> where E: Debug
{
}

/// The combination `Σ rᵢ vᵢ` of `values` by `coefficients`, pair by pair.
///
/// # Specification
/// - requires: `coefficients` and `values` are of one number; a longer side
///   keeps its extra elements out of the sum.
/// - ensures: the sum, from zero, of each product of a coefficient and its
///   value, in order.
/// - fails: an operation past the represented elements is refused.
/// - panics: none.
/// - executable: none — the sum and the product are the algebra's.
///
/// # Errors
/// - [`Outside`]: a product or a sum leaves the represented elements.
///
/// # Adequacy
/// - hypothesis: L3 — a ring cover whose combination is two, not one, separates
///   a sum that drops a product.
/// - witness: `tests::cover::a_ring_cover_replays_its_coefficients_and_refuses_others`
fn combination<A>(
    algebra: &A,
    coefficients: &[A::Element],
    values: &[A::Element],
) -> Result<A::Element, Outside>
where
    A: OrderedSemiring,
{
    let mut sum = algebra.zero();
    for (coefficient, value) in coefficients.iter().zip(values) {
        let product = algebra.multiply(coefficient, value)?;
        sum = algebra.add(&sum, &product)?;
    }
    Ok(sum)
}

impl<E> Cover<E>
where
    E: Clone + Debug + Eq,
{
    /// The cover of `charts` with `coefficients`, after the replay of
    /// `Σ rᵢ fᵢ = 1` in `algebra`.
    ///
    /// # Specification
    /// - ensures: the cover holds `charts` and `coefficients` as given.
    /// - fails: coefficients of another number than the charts, and a
    ///   combination other than one, are refused; the second names the
    ///   combination.
    /// - panics: none.
    /// - intension: one product and one sum for each chart, and no search.
    ///
    /// # Errors
    /// - [`CoverRefusal::CoefficientCount`]: the coefficients and the charts
    ///   differ in number.
    /// - [`CoverRefusal::NotUnimodular`]: the combination is not one.
    /// - [`CoverRefusal::Outside`]: an operation leaves the represented
    ///   elements.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a ring cover with its coefficients, with one
    ///   coefficient changed, and with one coefficient missing separates each
    ///   refusal from the replay.
    /// - witness: `tests::cover::a_ring_cover_replays_its_coefficients_and_refuses_others`
    #[spec(ensures: |ref ret| ret.is_ok() || matches!(*ret, Err(CoverRefusal::CoefficientCount | CoverRefusal::NotUnimodular(_) | CoverRefusal::Outside)))]
    #[inline]
    pub fn replayed<A>(
        algebra: &A,
        charts: Vec<E>,
        coefficients: Vec<E>,
    ) -> Result<Self, CoverRefusal<E>>
    where
        A: OrderedSemiring<Element = E>,
    {
        if charts.len() != coefficients.len() {
            return Err(CoverRefusal::CoefficientCount);
        }
        let reached = combination(algebra, &coefficients, &charts)?;
        if reached != algebra.one() {
            return Err(CoverRefusal::NotUnimodular(reached));
        }
        Ok(Self {
            charts,
            coefficients,
        })
    }

    /// The charts, in the cover's order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn charts(&self) -> &[E]
    {
        &self.charts
    }

    /// The coefficients, one for each chart.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn coefficients(&self) -> &[E]
    {
        &self.coefficients
    }

    /// The global section that the local sections `sections` glue to: the
    /// numerator `aᵢ` over each chart `fᵢ`, glued to `Σ rᵢ aᵢ`.
    ///
    /// # Specification
    /// - requires: `algebra` is the algebra that replayed the cover, and its
    ///   product is commutative.
    /// - ensures: the product of the result with each chart is that chart's
    ///   numerator.
    /// - fails: sections of another number than the charts are refused, and so
    ///   are sections that disagree on an overlap, by the first pair.
    /// - panics: none.
    /// - intension: two products for each pair of charts, then one product and
    ///   one sum for each chart.
    ///
    /// # Errors
    /// - [`CoverRefusal::SectionCount`]: the sections and the charts differ in
    ///   number.
    /// - [`CoverRefusal::Disagree`]: `fⱼ aᵢ ≠ fᵢ aⱼ` for the pair named, the
    ///   first in lexicographic order.
    /// - [`CoverRefusal::Outside`]: an operation leaves the represented
    ///   elements.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every pair of local sections of the face cover,
    ///   against the members that restrict to both, separates a gluing that
    ///   misses a disagreement or a section that does not restrict to its
    ///   numerators; L3 — a ring cover's sections, one of them changed,
    ///   separate the first disagreeing pair.
    /// - witness: `tests::cover::each_agreeing_pair_of_face_sections_glues_to_the_one_member_that_restricts_to_both`
    /// - witness: `tests::cover::a_ring_cover_glues_agreeing_sections_and_names_the_first_disagreement`
    #[spec(ensures: |ref ret| ret.is_ok() || matches!(*ret, Err(CoverRefusal::SectionCount | CoverRefusal::Disagree(_, _) | CoverRefusal::Outside)))]
    #[inline]
    pub fn glue<A>(
        &self,
        algebra: &A,
        sections: &[E],
    ) -> Result<E, CoverRefusal<E>>
    where
        A: OrderedSemiring<Element = E>,
    {
        if sections.len() != self.charts.len() {
            return Err(CoverRefusal::SectionCount);
        }
        for (first, (first_chart, first_section)) in self.charts.iter().zip(sections).enumerate() {
            let later = self
                .charts
                .iter()
                .zip(sections)
                .enumerate()
                .skip(first.saturating_add(1));
            for (second, (second_chart, second_section)) in later {
                let left = algebra.multiply(second_chart, first_section)?;
                let right = algebra.multiply(first_chart, second_section)?;
                if left != right {
                    return Err(CoverRefusal::Disagree(
                        Chart::from(first),
                        Chart::from(second),
                    ));
                }
            }
        }
        let glued = combination(algebra, &self.coefficients, sections)?;
        Ok(glued)
    }

    /// The splitting of `cocycle` by the partition of unity: the numerator
    /// `uᵢ = −Σₖ rₖ mᵢₖ` over each chart `fᵢ`, so that `uₖ − uᵢ` is the
    /// cocycle at each pair.
    ///
    /// # Specification
    /// - requires: `ring` is the ring that replayed the cover.
    /// - ensures: one numerator for each chart, and `fᵢ uₖ − fₖ uᵢ = mᵢₖ` for
    ///   each pair `i < k`.
    /// - fails: numerators of another number than the pairs are refused, and so
    ///   are numerators whose split fails at a pair, by the first pair `i < k`.
    ///   In a ring that keeps its laws, `fᵢ uₖ − fₖ uᵢ − mᵢₖ` is the sum over
    ///   `j` of `rⱼ` times `fₖ mᵢⱼ + fᵢ mⱼₖ − fⱼ mᵢₖ`. So each pair holds
    ///   exactly when each triple keeps the cocycle condition, and a pair that
    ///   fails has a triple through it that breaks the condition.
    /// - panics: none.
    /// - intension: one pass over the pairs gathers the split with two products
    ///   for each pair, and a second pass checks it with two products and a sum
    ///   for each pair; the split is the one allocation.
    ///
    /// # Errors
    /// - [`CoverRefusal::CocycleCount`]: the numerators and the pairs of charts
    ///   differ in number.
    /// - [`CoverRefusal::NotCocycle`]: the split fails at the pair named, the
    ///   first in lexicographic order.
    /// - [`CoverRefusal::Outside`]: an operation leaves the represented
    ///   elements.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the coboundary of every family of three numerators
    ///   from a grid of integers, split and read back pair by pair, separates a
    ///   sign or a coefficient lost in the splitting; L3 — one numerator
    ///   changed and one numerator missing separate the refusals.
    /// - witness: `tests::cover::a_ring_cover_splits_each_coboundary_and_refuses_a_broken_cocycle`
    #[spec(ensures: |ref ret| ret.as_ref().map_or_else(
        |refusal| matches!(*refusal, CoverRefusal::CocycleCount | CoverRefusal::NotCocycle(_, _) | CoverRefusal::Outside),
        |split| split.len() == self.charts.len(),
    ))]
    #[inline]
    pub fn split<R>(
        &self,
        ring: &R,
        cocycle: &Cocycle<E>,
    ) -> Result<Vec<E>, CoverRefusal<E>>
    where
        R: CommutativeRing<Element = E>,
    {
        let mut split = vec![ring.zero(); self.charts.len()];
        let mut numerators = cocycle.numerators.iter();
        for (first, first_coefficient) in self.coefficients.iter().enumerate() {
            let seconds = self
                .coefficients
                .iter()
                .enumerate()
                .skip(first.saturating_add(1));
            for (second, second_coefficient) in seconds {
                let numerator = numerators.next().ok_or(CoverRefusal::CocycleCount)?;
                // `uᵢ` gathers `−rₖ mᵢₖ`, and `uₖ` gathers `−rᵢ mₖᵢ`, which
                // is `rᵢ mᵢₖ`.
                let toward_first = ring.multiply(second_coefficient, numerator)?;
                let toward_first = ring.negate(&toward_first)?;
                let toward_second = ring.multiply(first_coefficient, numerator)?;
                let first_slot = split.get_mut(first).ok_or(CoverRefusal::CocycleCount)?;
                *first_slot = ring.add(first_slot, &toward_first)?;
                let second_slot = split.get_mut(second).ok_or(CoverRefusal::CocycleCount)?;
                *second_slot = ring.add(second_slot, &toward_second)?;
            }
        }
        if numerators.next().is_some() {
            return Err(CoverRefusal::CocycleCount);
        }
        let mut numerators = cocycle.numerators.iter();
        let charts = self.charts.iter().zip(&split).enumerate();
        for (first, (first_chart, first_split)) in charts {
            let seconds = self
                .charts
                .iter()
                .zip(&split)
                .enumerate()
                .skip(first.saturating_add(1));
            for (second, (second_chart, second_split)) in seconds {
                let numerator = numerators.next().ok_or(CoverRefusal::CocycleCount)?;
                let left = ring.multiply(first_chart, second_split)?;
                let shifted = ring.multiply(second_chart, first_split)?;
                let right = ring.add(numerator, &shifted)?;
                if left != right {
                    return Err(CoverRefusal::NotCocycle(
                        Chart::from(first),
                        Chart::from(second),
                    ));
                }
            }
        }
        Ok(split)
    }
}

impl Cover<ElementSet>
{
    /// The cover of a lattice of sets by `charts`, each coefficient the top:
    /// a family whose join is the whole carrier.
    ///
    /// # Specification
    /// - ensures: each coefficient is the whole carrier.
    /// - fails: a chart that is no member of `lattice` is refused by its
    ///   position, and a family whose join is not the whole carrier is refused
    ///   with that join, the generator of the ideal that the family generates.
    /// - panics: none.
    /// - intension: one search of the members for each chart, then the replay
    ///   of [`Cover::replayed`], which is one join and one meet for each chart.
    ///
    /// # Errors
    /// - [`CoverRefusal::NotMember`]: the chart named is no member.
    /// - [`CoverRefusal::NotUnimodular`]: the join of the charts is not the
    ///   whole carrier.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every family of members of the face lattice, against
    ///   its join, separates a cover refused or a family admitted; L3 — a set
    ///   outside the lattice separates the membership refusal.
    /// - witness: `tests::cover::a_face_cover_is_unimodular_and_one_face_alone_names_its_ideal`
    #[spec(ensures: |ref ret| ret.as_ref().map_or_else(
        |refusal| matches!(*refusal, CoverRefusal::NotMember(_) | CoverRefusal::NotUnimodular(_)),
        |cover| cover.coefficients.iter().all(|coefficient| *coefficient == lattice.one()),
    ))]
    #[inline]
    pub fn of_lattice(
        lattice: &SetRing,
        charts: Vec<ElementSet>,
    ) -> Result<Self, CoverRefusal<ElementSet>>
    {
        for (position, chart) in charts.iter().enumerate() {
            if lattice.holds(*chart) == Membership::Outside {
                return Err(CoverRefusal::NotMember(Chart::from(position)));
            }
        }
        let coefficients = vec![lattice.one(); charts.len()];
        Self::replayed(lattice, charts, coefficients)
    }
}
