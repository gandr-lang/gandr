//! A finite distributive lattice of sets as an ordered semiring: the join
//! adds, the meet multiplies, and the order is inclusion.
//!
//! The lattice is the lattice stratum of a cover. A sum of charts is their
//! join, so a family covers when its join is the top. The instance reads the
//! lattice of [`SetRing`], and its whole carrier is the lattice's members.
//! A join or a meet that leaves the members refuses with [`Outside`]. Only a
//! side that is no member reaches that refusal, since the members are closed
//! under both.

use anodized::spec;
use gandr_theory_stone_duality::ElementSet;
use gandr_theory_stone_duality::Membership;
use gandr_theory_stone_duality::SetRing;

use crate::signature::Carrier;
use crate::signature::Comparison;
use crate::signature::InstanceName;
use crate::signature::OrderedSemiring;
use crate::signature::Outside;

/// The member `set`, or the refusal of a set that is no member of `lattice`.
///
/// # Specification
/// - ensures: the result is `set` when `lattice` holds it.
/// - fails: a set that is no member is refused.
/// - panics: none.
///
/// # Errors
/// - [`Outside`]: `lattice` does not hold `set`.
///
/// # Adequacy
/// - hypothesis: L3 — a set outside the face lattice separates the refusal.
/// - witness: `tests::cover::a_lattice_of_sets_is_an_ordered_semiring`
#[spec(ensures: |ref ret| ret.as_ref().ok().is_none_or(|kept| *kept == set))]
fn member(
    lattice: &SetRing,
    set: ElementSet,
) -> Result<ElementSet, Outside>
{
    match lattice.holds(set) {
        Membership::Inside => Ok(set),
        Membership::Outside => Err(Outside),
    }
}

impl OrderedSemiring for SetRing
{
    type Element = ElementSet;

    /// The name of a lattice of sets as an instance.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn name(&self) -> InstanceName
    {
        InstanceName::from("lattice of sets")
    }

    /// The members, the whole carrier of the instance.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn carrier(&self) -> Carrier<'_, ElementSet>
    {
        Carrier::Whole(self.members())
    }

    /// The empty set, the unit of the join.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn zero(&self) -> ElementSet
    {
        ElementSet::EMPTY
    }

    /// The whole carrier, the unit of the meet: the greatest member.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn one(&self) -> ElementSet
    {
        self.members().last().copied().unwrap_or(ElementSet::EMPTY)
    }

    /// The join of two members: their union.
    ///
    /// # Specification
    /// - ensures: the union, when it is a member.
    /// - fails: a union that is no member is refused.
    /// - panics: none.
    /// - executable: none — the body is [`member`] of the union, which states
    ///   the check.
    ///
    /// # Errors
    /// - [`Outside`]: the union is no member, which needs a side that is no
    ///   member.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the law checker reads the join on every pair of
    ///   members of the face lattice.
    /// - witness: `tests::cover::a_lattice_of_sets_is_an_ordered_semiring`
    #[inline]
    fn add(
        &self,
        left: &ElementSet,
        right: &ElementSet,
    ) -> Result<ElementSet, Outside>
    {
        member(self, left.union(*right))
    }

    /// The meet of two members: their intersection.
    ///
    /// # Specification
    /// - ensures: the intersection, when it is a member.
    /// - fails: an intersection that is no member is refused.
    /// - panics: none.
    /// - executable: none — the body is [`member`] of the intersection, which
    ///   states the check.
    ///
    /// # Errors
    /// - [`Outside`]: the intersection is no member, which needs a side that is
    ///   no member.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the law checker reads the meet on every pair of
    ///   members of the face lattice.
    /// - witness: `tests::cover::a_lattice_of_sets_is_an_ordered_semiring`
    #[inline]
    fn multiply(
        &self,
        left: &ElementSet,
        right: &ElementSet,
    ) -> Result<ElementSet, Outside>
    {
        member(self, left.meet(*right))
    }

    /// Whether `lower` is included in `upper`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn compare(
        &self,
        lower: &ElementSet,
        upper: &ElementSet,
    ) -> Comparison
    {
        match lower.compare(*upper) {
            gandr_theory_stone_duality::Comparison::Below => Comparison::Below,
            gandr_theory_stone_duality::Comparison::NotBelow => Comparison::NotBelow,
        }
    }
}
