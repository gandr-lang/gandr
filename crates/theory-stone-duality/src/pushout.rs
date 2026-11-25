//! The pushout of two finite spaces along an open embedding, computed on
//! their algebras as a pullback.
//!
//! An open of a finite space is a member `u` of its lattice of sets. Its
//! algebra is the localisation `↓u`, which takes each member `a` to `a ∩ u`.
//! Two lattices glue along the opens `u` and `v` when a bijection of the
//! points of `u` onto the points of `v` takes the localisation at `u` onto
//! the localisation at `v`. The bijection keeps the order of the points: the
//! `i`-th point of `u` goes to the `i`-th point of `v`.
//!
//! The glued algebra is the pullback: the pairs of members whose restrictions
//! to the opens agree. Its carrier is the left carrier, then the right points
//! outside `v`. Its spectrum is the pushout of the two spectra along the
//! spectrum of the shared open. Distributive lattices and Boolean algebras
//! each have pullbacks, so on both strata the glued algebra is affine.

use alloc::vec::Vec;

use anodized::spec;

use crate::error::DualityError;
use crate::finite::ElementSet;
use crate::finite::SetRing;
use crate::finite::first;
use crate::index::Budget;
use crate::index::Element;
use crate::index::ElementCount;
use crate::index::Membership;
use crate::index::WIDEST;

/// The glued algebra of two lattices along an open of each, with its two
/// restriction homomorphisms.
///
/// # Specification
/// - ensures: the ring is the pullback of the two lattices over their shared
///   localisation; point `i` below the left carrier is the left point `i`, and
///   right point `j` is the point `right[j]`.
/// - provides: the restriction of each member to the left lattice and to the
///   right lattice, each a lattice homomorphism.
/// - panics: none.
/// - executable: none — a type-level block: the invariant is
///   [`SetRing::glued`]'s, which makes it.
///
/// # Adequacy
/// - hypothesis: L2 — two chains glued along their bottom point, and every pair
///   of Boolean algebras on up to three points glued along a common open,
///   against the pairs of members that agree, separate a lost or an extra
///   member and a restriction that is no homomorphism.
/// - witness: `tests::pushout::two_chains_glued_at_their_bottom_point_are_the_down_sets_of_a_fork`
/// - witness: `tests::pushout::each_glued_algebra_is_the_pullback_and_its_spectrum_the_pushout`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Glued
{
    /// The glued lattice.
    ring: SetRing,
    /// The number of points of the left carrier, the first points of the
    /// glued carrier.
    left: ElementCount,
    /// The glued point of each right point, in point order.
    right: Vec<Element>,
}

/// The points of `set` inside `open`, each numbered by its rank in `open`.
///
/// # Specification
/// - ensures: rank `i` is in the result exactly when the `i`-th point of `open`
///   is in `set`.
/// - fails: only on a rank past one machine word, which no set holds.
/// - panics: none.
///
/// # Errors
/// - [`DualityError::ElementOutside`]: unreachable, since a set of one machine
///   word has fewer than 64 ranks.
///
/// # Adequacy
/// - hypothesis: L2 — every localisation of the Boolean algebras on up to three
///   points, compared across two opens of one size, separates a rank taken for
///   a point.
/// - witness: `tests::pushout::each_glued_algebra_is_the_pullback_and_its_spectrum_the_pushout`
#[spec(ensures: |ref ret| ret.map_or(true, |ranked| ranked.count() == set.meet(open).count()))]
fn ranked(
    set: ElementSet,
    open: ElementSet,
) -> Result<ElementSet, DualityError>
{
    let mut ranked = ElementSet::EMPTY;
    for (rank, point) in open.elements().enumerate() {
        if set.contains(point) == Membership::Inside {
            let bit = ElementSet::single(Element::from(rank))?;
            ranked = ranked.union(bit);
        }
    }
    Ok(ranked)
}

/// The localisation of `lattice` at `open`, each member in the open's own
/// ranks, sorted and without repeats.
///
/// # Specification
/// - ensures: the result holds `ranked(a ∩ open, open)` for each member `a`,
///   and no other set.
/// - fails: as [`ranked`].
/// - panics: none.
///
/// # Errors
/// - [`DualityError::ElementOutside`]: as [`ranked`].
///
/// # Adequacy
/// - hypothesis: L2 — as [`ranked`].
/// - witness: `tests::pushout::each_glued_algebra_is_the_pullback_and_its_spectrum_the_pushout`
#[spec(ensures: |ref ret| ret.as_ref().map_or(true, |local| local.len() <= lattice.members().len()))]
fn localisation(
    lattice: &SetRing,
    open: ElementSet,
) -> Result<Vec<ElementSet>, DualityError>
{
    let mut local = Vec::with_capacity(lattice.members().len());
    for member in lattice.members() {
        let restricted = ranked(member.meet(open), open)?;
        local.push(restricted);
    }
    local.sort_unstable();
    local.dedup();
    Ok(local)
}

/// The glued set of the right points of `set`, each sent by `right`.
///
/// # Specification
/// - ensures: the result holds `right[j]` for each right point `j` of `set`.
/// - fails: a point past `right` is refused by name.
/// - panics: none.
///
/// # Errors
/// - [`DualityError::ElementOutside`]: a point of `set` has no glued point.
///
/// # Adequacy
/// - hypothesis: L2 — as [`Glued`].
/// - witness: `tests::pushout::each_glued_algebra_is_the_pullback_and_its_spectrum_the_pushout`
#[spec(ensures: |ref ret| ret.map_or(true, |placed| placed.count() == set.count()))]
fn placed(
    set: ElementSet,
    right: &[Element],
) -> Result<ElementSet, DualityError>
{
    let mut placed = ElementSet::EMPTY;
    for point in set.elements() {
        let glued = right
            .get(usize::from(point))
            .copied()
            .ok_or(DualityError::ElementOutside(point))?;
        let bit = ElementSet::single(glued)?;
        placed = placed.union(bit);
    }
    Ok(placed)
}

impl SetRing
{
    /// The lattice of this space glued to `other` along `open` here and
    /// `other_open` there: the pullback over the shared localisation.
    ///
    /// # Specification
    /// - ensures: the members are the sets `a ∪ b'` for each member `a` here
    ///   and each member `b` there whose restrictions to the opens agree, with
    ///   `b'` the glued points of `b` outside `other_open`; the carrier is this
    ///   carrier and the points of `other` outside `other_open`.
    /// - fails: an open that is no member, opens of two sizes, localisations
    ///   that differ, a glued carrier past one machine word, and a lattice past
    ///   `budget` members are refused.
    /// - panics: none.
    /// - intension: each right member is keyed by its localisation once, and
    ///   each left member reads the right members of its key by a binary
    ///   search, so the work is the members of both sides and the glued
    ///   members, each times the logarithm of the right side.
    ///
    /// # Errors
    /// - [`DualityError::NotMember`]: an open is no member of its lattice.
    /// - [`DualityError::OpenSizes`]: the opens hold another number of points
    ///   each.
    /// - [`DualityError::LocalisationsDiffer`]: one localisation holds the set
    ///   named and the other does not, the least such set.
    /// - [`DualityError::TooManyElements`]: the glued carrier holds more than
    ///   64 points.
    /// - [`DualityError::PastBudget`]: the glued lattice has more than `budget`
    ///   members.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every pair of Boolean algebras on up to three points
    ///   and every pair of opens of one size, against the agreeing pairs of
    ///   members, separates a lost or an extra member; L3 — an open outside its
    ///   lattice, opens of two sizes, two chains glued at their tops and a
    ///   budget one short separate each refusal.
    /// - witness: `tests::pushout::two_chains_glued_at_their_bottom_point_are_the_down_sets_of_a_fork`
    /// - witness: `tests::pushout::each_glued_algebra_is_the_pullback_and_its_spectrum_the_pushout`
    /// - witness: `tests::pushout::a_gluing_refuses_opens_that_do_not_match`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |glued| glued.ring.members().first() == Some(&ElementSet::EMPTY)))]
    #[inline]
    pub fn glued(
        &self,
        open: ElementSet,
        other: &Self,
        other_open: ElementSet,
        budget: Budget,
    ) -> Result<Glued, DualityError>
    {
        for (lattice, chosen) in [(self, open), (other, other_open)] {
            if lattice.holds(chosen) == Membership::Outside {
                return Err(DualityError::NotMember(chosen));
            }
        }
        let (size, other_size) = (open.count(), other_open.count());
        if size != other_size {
            return Err(DualityError::OpenSizes(size, other_size));
        }
        let local = localisation(self, open)?;
        let other_local = localisation(other, other_open)?;
        let missing = local
            .iter()
            .find(|set| other_local.binary_search(set).is_err());
        let extra = other_local
            .iter()
            .find(|set| local.binary_search(set).is_err());
        match (missing, extra) {
            (Some(&one), Some(&another)) => {
                return Err(DualityError::LocalisationsDiffer(one.min(another)));
            },
            (Some(&one), None) | (None, Some(&one)) => {
                return Err(DualityError::LocalisationsDiffer(one));
            },
            (None, None) => {},
        }
        let rest = usize::from(other.carrier()).saturating_sub(usize::from(other_size));
        let carrier = usize::from(self.carrier()).saturating_add(rest);
        if carrier > WIDEST {
            return Err(DualityError::TooManyElements(ElementCount::from(carrier)));
        }
        let shared: Vec<Element> = open.elements().collect();
        let mut right = Vec::with_capacity(usize::from(other.carrier()));
        let (mut rank, mut next) = (0_usize, usize::from(self.carrier()));
        for point in (0 .. usize::from(other.carrier())).map(Element::from) {
            if other_open.contains(point) == Membership::Inside {
                let glued = shared
                    .get(rank)
                    .copied()
                    .ok_or(DualityError::ElementOutside(point))?;
                right.push(glued);
                rank = rank.saturating_add(1);
            }
            else {
                right.push(Element::from(next));
                next = next.saturating_add(1);
            }
        }
        let mut keyed = Vec::with_capacity(other.members().len());
        for member in other.members() {
            let key = ranked(member.meet(other_open), other_open)?;
            let outside = placed(member.without(other_open), &right)?;
            keyed.push((key, outside));
        }
        keyed.sort_unstable();
        let mut members = Vec::new();
        for member in self.members() {
            let key = ranked(member.meet(open), open)?;
            let start = keyed.partition_point(|&(found, _)| found < key);
            let matching = keyed
                .iter()
                .skip(start)
                .take_while(|&&(found, _)| found == key);
            for &(_, outside) in matching {
                if members.len() >= usize::from(budget) {
                    return Err(DualityError::PastBudget(budget));
                }
                members.push(member.union(outside));
            }
        }
        members.sort_unstable();
        Ok(Glued {
            ring: Self::from_members(ElementCount::from(carrier), members),
            left: self.carrier(),
            right,
        })
    }
}

impl Glued
{
    /// The glued lattice.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn ring(&self) -> &SetRing
    {
        &self.ring
    }

    /// The glued point of each point of the right carrier, in point order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn right_points(&self) -> &[Element]
    {
        &self.right
    }

    /// The restriction of a glued member to the left lattice: its points
    /// below the left carrier.
    ///
    /// # Specification
    /// - ensures: the result is a member of the left lattice, and the map is a
    ///   lattice homomorphism.
    /// - fails: a set that is no glued member is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DualityError::NotMember`]: `member` is no glued member.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every glued member of every gluing of Boolean
    ///   algebras on up to three points, against the left member it came from,
    ///   separates a lost point.
    /// - witness: `tests::pushout::each_glued_algebra_is_the_pullback_and_its_spectrum_the_pushout`
    #[spec(ensures: |ref ret| ret.is_ok() || *ret == Err(DualityError::NotMember(member)))]
    #[inline]
    pub fn left(
        &self,
        member: ElementSet,
    ) -> Result<ElementSet, DualityError>
    {
        if self.ring.holds(member) == Membership::Outside {
            return Err(DualityError::NotMember(member));
        }
        let points = first(self.left)?;
        Ok(member.meet(points))
    }

    /// The restriction of a glued member to the right lattice: each right
    /// point whose glued point it holds.
    ///
    /// # Specification
    /// - ensures: the result is a member of the right lattice, and the map is a
    ///   lattice homomorphism.
    /// - fails: a set that is no glued member is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DualityError::NotMember`]: `member` is no glued member.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every glued member of every gluing of Boolean
    ///   algebras on up to three points, against the right member it came from,
    ///   separates a point read through the wrong glued point.
    /// - witness: `tests::pushout::each_glued_algebra_is_the_pullback_and_its_spectrum_the_pushout`
    #[spec(ensures: |ref ret| ret.is_ok() || *ret == Err(DualityError::NotMember(member)))]
    #[inline]
    pub fn right(
        &self,
        member: ElementSet,
    ) -> Result<ElementSet, DualityError>
    {
        if self.ring.holds(member) == Membership::Outside {
            return Err(DualityError::NotMember(member));
        }
        let mut restricted = ElementSet::EMPTY;
        for (point, &glued) in self.right.iter().enumerate() {
            if member.contains(glued) == Membership::Inside {
                let bit = ElementSet::single(Element::from(point))?;
                restricted = restricted.union(bit);
            }
        }
        Ok(restricted)
    }
}
