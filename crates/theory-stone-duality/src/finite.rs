//! Finite posets, the distributive lattices of sets they present, and the
//! duality between them.
//!
//! A down-set of a poset holds every element below each of its elements. The
//! down-sets of a finite poset form a distributive lattice under union and
//! intersection. Each finite distributive lattice of sets arises so: its
//! join-irreducible members, ordered by inclusion, form a poset whose
//! down-sets are the lattice again. A monotone map between two posets sends a
//! down-set of its target to a down-set of its source by preimage, and that
//! preimage is a lattice homomorphism in the other direction.

use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;

use crate::error::DualityError;
use crate::index::Budget;
use crate::index::Comparison;
use crate::index::Element;
use crate::index::ElementCount;
use crate::index::GeneratorCount;
use crate::index::Membership;
use crate::index::WIDEST;
use crate::index::WIDEST_CUBE;

wrapper! {
    /// A set of elements of a finite poset, or of points of a carrier, as a
    /// bit set.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct ElementSet(u64);
}

/// The set of one element, or the refusal of an element past one machine
/// word.
///
/// # Specification
/// - ensures: the set holds exactly `element`.
/// - fails: an element at or past 64 is refused by name.
/// - panics: none.
///
/// # Errors
/// - [`DualityError::ElementOutside`]: `element` is at or past 64.
///
/// # Adequacy
/// - hypothesis: L3 — elements 63 and 64 separate the word's bound.
/// - witness: `tests::finite::posets_close_their_relation_and_refuse_cycles`
#[spec(ensures: |ref ret| match *ret {
    Ok(set) => set.0.is_power_of_two(),
    Err(error) => error == DualityError::ElementOutside(element),
})]
fn element_bit(element: Element) -> Result<ElementSet, DualityError>
{
    let outside = DualityError::ElementOutside(element);
    let shift = u32::try_from(usize::from(element)).map_err(|_overflow| outside)?;
    1_u64.checked_shl(shift).map(ElementSet).ok_or(outside)
}

/// The set of the first `count` elements.
///
/// # Specification
/// - ensures: the set holds the elements below `count` and no other.
/// - fails: a count past 64 is refused.
/// - panics: none.
///
/// # Errors
/// - [`DualityError::TooManyElements`]: `count` is past 64.
///
/// # Adequacy
/// - hypothesis: L3 — counts 0, 64 and 65 separate the bounds.
/// - witness: `tests::finite::enumerations_refuse_past_their_budget`
#[spec(ensures: |ref ret| match *ret {
    Ok(set) => usize::try_from(set.0.count_ones()).ok() == Some(usize::from(count)),
    Err(error) => error == DualityError::TooManyElements(count),
})]
fn first(count: ElementCount) -> Result<ElementSet, DualityError>
{
    let too_many = DualityError::TooManyElements(count);
    let unused = WIDEST.checked_sub(usize::from(count)).ok_or(too_many)?;
    if unused == WIDEST {
        return Ok(ElementSet::EMPTY);
    }
    let shift = u32::try_from(unused).map_err(|_overflow| too_many)?;
    u64::MAX.checked_shr(shift).map(ElementSet).ok_or(too_many)
}

impl ElementSet
{
    /// The set of no element.
    pub const EMPTY: Self = Self(0);

    /// The set of one element.
    ///
    /// # Specification
    /// - ensures: the set holds exactly `element`.
    /// - fails: an element at or past 64 is refused by name.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DualityError::ElementOutside`]: `element` is at or past 64.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — elements 63 and 64 separate the word's bound.
    /// - witness: `tests::finite::posets_close_their_relation_and_refuse_cycles`
    #[inline]
    #[spec(ensures: |ref ret| match *ret {
        Ok(set) => set.0.is_power_of_two(),
        Err(error) => error == DualityError::ElementOutside(element),
    })]
    pub fn single(element: Element) -> Result<Self, DualityError>
    {
        element_bit(element)
    }

    /// Whether the set holds an element. An element past the word lies
    /// outside it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn contains(
        self,
        element: Element,
    ) -> Membership
    {
        match element_bit(element) {
            Ok(bit) if self.0 & bit.0 != 0 => Membership::Inside,
            Ok(_) | Err(_) => Membership::Outside,
        }
    }

    /// The union of two sets.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn union(
        self,
        other: Self,
    ) -> Self
    {
        Self(self.0 | other.0)
    }

    /// The intersection of two sets.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn meet(
        self,
        other: Self,
    ) -> Self
    {
        Self(self.0 & other.0)
    }

    /// Whether this set is included in `other`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn compare(
        self,
        other: Self,
    ) -> Comparison
    {
        if self.0 & other.0 == self.0 {
            Comparison::Below
        }
        else {
            Comparison::NotBelow
        }
    }

    /// The elements of the set, in increasing order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn elements(self) -> impl Iterator<Item = Element>
    {
        ones!(self.0, Element::from)
    }
}

/// A finite poset of at most 64 elements: the principal down-set of each
/// element, in element order.
///
/// # Specification
/// - ensures: the order is reflexive, transitive and antisymmetric, so each
///   principal down-set holds its element and each element below it.
/// - provides: the order, down-closure and the lattice of down-sets.
/// - panics: none.
/// - executable: none — a type-level block: the invariant is the constructors',
///   each of which checks it.
///
/// # Adequacy
/// - hypothesis: L2 — every relation on up to three elements, against a naive
///   transitive closure, separates a lost pair and a missed cycle.
/// - witness: `tests::finite::posets_close_their_relation_and_refuse_cycles`
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct FinitePoset
{
    /// The principal down-set of each element.
    below: Vec<ElementSet>,
}

impl FinitePoset
{
    /// The poset on `count` elements that the order closes `relation` to:
    /// each pair puts its first element below its second.
    ///
    /// # Specification
    /// - ensures: the order is the least reflexive and transitive relation
    ///   holding `relation`.
    /// - fails: more than 64 elements, a pair naming an element at or past
    ///   `count`, and a relation that closes to a cycle are refused, the last
    ///   by its least pair.
    /// - panics: none.
    /// - intension: one closure over bit sets, quadratic in `count`.
    ///
    /// # Errors
    /// - [`DualityError::TooManyElements`]: `count` is past 64.
    /// - [`DualityError::ElementOutside`]: a pair names an element at or past
    ///   `count`.
    /// - [`DualityError::Cycle`]: the closure puts each of two distinct
    ///   elements below the other.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every relation on up to three elements, against a
    ///   naive closure, separates a lost pair and a missed cycle; L3 — an
    ///   element equal to `count` and 65 elements separate the bounds.
    /// - witness: `tests::finite::posets_close_their_relation_and_refuse_cycles`
    #[spec(ensures: |ref ret| match *ret {
        Ok(ref poset) => poset.below.len() == usize::from(count),
        Err(error) => matches!(error, DualityError::TooManyElements(_) | DualityError::ElementOutside(_) | DualityError::Cycle(..)),
    })]
    #[inline]
    pub fn new(
        count: ElementCount,
        relation: &[(Element, Element)],
    ) -> Result<Self, DualityError>
    {
        let whole = first(count)?;
        let mut below = Vec::with_capacity(usize::from(count));
        for index in 0 .. usize::from(count) {
            let single = element_bit(Element::from(index))?;
            below.push(single);
        }
        for &(lower, upper) in relation {
            let lower_bit = element_bit(lower)?;
            if whole.contains(lower) == Membership::Outside {
                return Err(DualityError::ElementOutside(lower));
            }
            let slot = below
                .get_mut(usize::from(upper))
                .ok_or(DualityError::ElementOutside(upper))?;
            *slot = slot.union(lower_bit);
        }
        for pivot in 0 .. below.len() {
            let pivot_element = Element::from(pivot);
            let Some(&through) = below.get(pivot)
            else {
                break;
            };
            for set in &mut below {
                if set.contains(pivot_element) == Membership::Inside {
                    *set = set.union(through);
                }
            }
        }
        let poset = Self { below };
        poset.acyclic()?;
        Ok(poset)
    }

    /// Refuses a closed relation that puts two distinct elements each below
    /// the other, naming the least such pair.
    ///
    /// # Specification
    /// - ensures: no two distinct elements lie each below the other.
    /// - fails: the least pair in element order that does is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DualityError::Cycle`]: two distinct elements lie each below the
    ///   other.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a two-cycle and a three-cycle separate the check.
    /// - witness: `tests::finite::posets_close_their_relation_and_refuse_cycles`
    #[spec(ensures: |ref ret| ret.is_ok() || matches!(*ret, Err(DualityError::Cycle(..))))]
    fn acyclic(&self) -> Result<(), DualityError>
    {
        for (index, set) in self.below.iter().enumerate() {
            let element = Element::from(index);
            for lower in set.elements() {
                if lower >= element {
                    break;
                }
                let lower_set = self
                    .below
                    .get(usize::from(lower))
                    .copied()
                    .unwrap_or_default();
                if lower_set.contains(element) == Membership::Inside {
                    return Err(DualityError::Cycle(lower, element));
                }
            }
        }
        Ok(())
    }

    /// The cube on `axes` axes: the vertices `{0, 1}ⁿ`, ordered axis by
    /// axis, each element the mask of the axes at which it is `1`.
    ///
    /// # Specification
    /// - ensures: one vertex lies below another exactly when its axes are a
    ///   subset of the other's.
    /// - fails: a cube past six axes is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DualityError::TooWide`]: `axes` is past six.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the cubes on up to four axes, against the spectrum of
    ///   the free lattice, separate a reversed order; L3 — seven axes separate
    ///   the bound.
    /// - witness: `tests::finite::birkhoff_duality_round_trips_on_small_posets`
    #[spec(ensures: |ref ret| match *ret {
        Ok(ref cube) => cube.below.len().is_power_of_two(),
        Err(error) => error == DualityError::TooWide(axes),
    })]
    #[inline]
    pub fn cube(axes: GeneratorCount) -> Result<Self, DualityError>
    {
        let too_wide = DualityError::TooWide(axes);
        if usize::from(axes) > WIDEST_CUBE {
            return Err(too_wide);
        }
        let width = u32::try_from(usize::from(axes)).map_err(|_overflow| too_wide)?;
        let vertices = 1_usize.checked_shl(width).ok_or(too_wide)?;
        let mut below = Vec::with_capacity(vertices);
        for upper in 0 .. vertices {
            let mut set = ElementSet::EMPTY;
            for lower in 0 .. vertices {
                if lower & upper == lower {
                    let bit = element_bit(Element::from(lower))?;
                    set = set.union(bit);
                }
            }
            below.push(set);
        }
        Ok(Self { below })
    }

    /// The number of elements.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn count(&self) -> ElementCount
    {
        ElementCount::from(self.below.len())
    }

    /// The principal down-set of an element: the element and every element
    /// below it.
    ///
    /// # Specification
    /// - provides: the down-set stored for `element`.
    /// - fails: an element at or past the count is refused by name.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DualityError::ElementOutside`]: `element` is at or past the count.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the first element past the count separates the bound.
    /// - witness: `tests::finite::posets_close_their_relation_and_refuse_cycles`
    #[spec(ensures: |ref ret| match *ret {
        Ok(set) => set.contains(element) == Membership::Inside,
        Err(error) => error == DualityError::ElementOutside(element),
    })]
    #[inline]
    pub fn below(
        &self,
        element: Element,
    ) -> Result<ElementSet, DualityError>
    {
        self.below
            .get(usize::from(element))
            .copied()
            .ok_or(DualityError::ElementOutside(element))
    }

    /// Whether `lower` lies below `upper`.
    ///
    /// # Specification
    /// - ensures: every element lies below itself.
    /// - fails: an element at or past the count is refused by name.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DualityError::ElementOutside`]: `lower` or `upper` is at or past the
    ///   count.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every pair of every poset on up to three elements,
    ///   against a naive closure, separates a reversed order.
    /// - witness: `tests::finite::posets_close_their_relation_and_refuse_cycles`
    #[spec(ensures: |ref ret| match *ret {
        Ok(order) => lower != upper || order == Comparison::Below,
        Err(error) => matches!(error, DualityError::ElementOutside(_)),
    })]
    #[inline]
    pub fn compare(
        &self,
        lower: Element,
        upper: Element,
    ) -> Result<Comparison, DualityError>
    {
        let _lower = self.below(lower)?;
        let upper_set = self.below(upper)?;
        Ok(match upper_set.contains(lower) {
            Membership::Inside => Comparison::Below,
            Membership::Outside => Comparison::NotBelow,
        })
    }

    /// The least down-set that holds `set`: the union of the principal
    /// down-sets of its elements.
    ///
    /// # Specification
    /// - ensures: the result holds `set` and is a down-set; a down-set is its
    ///   own closure.
    /// - fails: an element at or past the count is refused by name.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DualityError::ElementOutside`]: `set` holds an element at or past
    ///   the count.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every set of every poset on up to three elements
    ///   separates a closure that misses an element below.
    /// - witness: `tests::finite::birkhoff_duality_round_trips_on_small_posets`
    #[spec(ensures: |ref ret| match *ret {
        Ok(closure) => set.compare(closure) == Comparison::Below,
        Err(error) => matches!(error, DualityError::ElementOutside(_)),
    })]
    #[inline]
    pub fn down_closure(
        &self,
        set: ElementSet,
    ) -> Result<ElementSet, DualityError>
    {
        let mut closure = ElementSet::EMPTY;
        for element in set.elements() {
            let down = self.below(element)?;
            closure = closure.union(down);
        }
        Ok(closure)
    }

    /// The lattice of the down-sets of the poset, each enumerated once.
    ///
    /// # Specification
    /// - ensures: the members are exactly the down-sets, in increasing order of
    ///   their bits.
    /// - fails: an enumeration that passes `budget` members is refused.
    /// - panics: none.
    /// - intension: the elements are taken in an order that puts every element
    ///   after those below it; each down-set is made once, from the down-set
    ///   without its last element, so the work is linear in the number of
    ///   down-sets times the count.
    ///
    /// # Errors
    /// - [`DualityError::PastBudget`]: the poset has more than `budget`
    ///   down-sets.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every poset on up to three elements, against the
    ///   subsets that are their own closure, separates a lost or a doubled
    ///   down-set; L3 — a budget one short of the count separates the refusal.
    /// - witness: `tests::finite::birkhoff_duality_round_trips_on_small_posets`
    /// - witness: `tests::finite::enumerations_refuse_past_their_budget`
    #[spec(ensures: |ref ret| match *ret {
        Ok(ref lattice) => lattice.carrier == self.count() && lattice.members.len() <= usize::from(budget),
        Err(error) => error == DualityError::PastBudget(budget),
    })]
    #[inline]
    pub fn down_sets(
        &self,
        budget: Budget,
    ) -> Result<SetRing, DualityError>
    {
        let past = DualityError::PastBudget(budget);
        if usize::from(budget) == 0 {
            return Err(past);
        }
        let mut order: Vec<Element> = (0 .. self.below.len()).map(Element::from).collect();
        order.sort_by_key(|element| {
            self.below
                .get(usize::from(*element))
                .map_or(0, |set| set.0.count_ones())
        });
        let mut members = vec![ElementSet::EMPTY];
        for element in order {
            let principal = self.below(element)?;
            let bit = element_bit(element)?;
            let strict = ElementSet(principal.0 & !bit.0);
            for index in 0 .. members.len() {
                let Some(&set) = members.get(index)
                else {
                    break;
                };
                if strict.compare(set) == Comparison::Below {
                    if members.len() >= usize::from(budget) {
                        return Err(past);
                    }
                    members.push(set.union(bit));
                }
            }
        }
        members.sort_unstable();
        Ok(SetRing {
            carrier: self.count(),
            members,
        })
    }
}

/// A finite distributive lattice of sets over a carrier of at most 64
/// points: the members in increasing order of their bits.
///
/// # Specification
/// - ensures: the members are closed under union and intersection and hold the
///   empty set and the whole carrier.
/// - provides: the least member at each point, and the spectrum.
/// - panics: none.
/// - executable: none — a type-level block: the invariant is the constructors',
///   each of which checks it.
///
/// # Adequacy
/// - hypothesis: L2 — every family of subsets of up to three points, against a
///   naive closure, separates a lost union or intersection.
/// - witness: `tests::finite::a_ring_of_sets_reads_back_from_its_spectrum`
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct SetRing
{
    /// The number of points of the carrier.
    carrier: ElementCount,
    /// The members, in increasing order of their bits.
    members: Vec<ElementSet>,
}

/// Inserts `set` into the sorted `members` unless it is already there.
///
/// # Specification
/// - ensures: `members` stays sorted and holds `set` once.
/// - fails: an insertion past `budget` members is refused.
/// - panics: none.
///
/// # Errors
/// - [`DualityError::PastBudget`]: `members` holds `budget` members and lacks
///   `set`.
///
/// # Adequacy
/// - hypothesis: L3 — a budget one short of the lattice separates the refusal.
/// - witness: `tests::finite::enumerations_refuse_past_their_budget`
#[spec(ensures: |ref ret| ret.is_ok() || matches!(*ret, Err(DualityError::PastBudget(_))))]
fn insert(
    members: &mut Vec<ElementSet>,
    set: ElementSet,
    budget: Budget,
) -> Result<(), DualityError>
{
    if let Err(position) = members.binary_search(&set) {
        if members.len() >= usize::from(budget) {
            return Err(DualityError::PastBudget(budget));
        }
        members.insert(position, set);
    }
    Ok(())
}

impl SetRing
{
    /// The least lattice of sets over `carrier` points that holds
    /// `generators`: their intersections first, then the unions of those.
    ///
    /// # Specification
    /// - ensures: the members are closed under union and intersection, hold the
    ///   empty set, the whole carrier and every generator, and no other set.
    /// - fails: more than 64 points, a generator holding a point at or past
    ///   `carrier`, and a lattice past `budget` members are refused.
    /// - panics: none.
    /// - intension: the intersections of the generators close first; the unions
    ///   of a family closed under intersection are closed under it too, by
    ///   distributivity, so one pass of unions completes the lattice.
    ///
    /// # Errors
    /// - [`DualityError::TooManyElements`]: `carrier` is past 64.
    /// - [`DualityError::ElementOutside`]: a generator holds a point at or past
    ///   `carrier`.
    /// - [`DualityError::PastBudget`]: the lattice has more than `budget`
    ///   members.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every family of subsets of up to three points,
    ///   against a naive fixed point of unions and intersections, separates a
    ///   lost member; L3 — a point equal to `carrier` and a budget one short
    ///   separate the refusals.
    /// - witness: `tests::finite::a_ring_of_sets_reads_back_from_its_spectrum`
    /// - witness: `tests::finite::enumerations_refuse_past_their_budget`
    #[spec(ensures: |ref ret| match *ret {
        Ok(ref lattice) => lattice.carrier == carrier && lattice.members.first() == Some(&ElementSet::EMPTY),
        Err(error) => matches!(error, DualityError::TooManyElements(_) | DualityError::ElementOutside(_) | DualityError::PastBudget(_)),
    })]
    #[inline]
    pub fn generated(
        carrier: ElementCount,
        generators: &[ElementSet],
        budget: Budget,
    ) -> Result<Self, DualityError>
    {
        let whole = first(carrier)?;
        for generator in generators {
            if let Some(outside) = ElementSet(generator.0 & !whole.0).elements().next() {
                return Err(DualityError::ElementOutside(outside));
            }
        }
        let mut meets = Vec::new();
        insert(&mut meets, whole, budget)?;
        let mut fresh = Vec::new();
        for &generator in generators {
            fresh.clear();
            fresh.extend(meets.iter().map(|met| met.meet(generator)));
            for &candidate in &fresh {
                insert(&mut meets, candidate, budget)?;
            }
        }
        let mut members = Vec::new();
        insert(&mut members, ElementSet::EMPTY, budget)?;
        for &met in &meets {
            fresh.clear();
            fresh.extend(members.iter().map(|member| member.union(met)));
            for &candidate in &fresh {
                insert(&mut members, candidate, budget)?;
            }
        }
        Ok(Self { carrier, members })
    }

    /// The number of points of the carrier.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn carrier(&self) -> ElementCount
    {
        self.carrier
    }

    /// The members, in increasing order of their bits.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn members(&self) -> &[ElementSet]
    {
        &self.members
    }

    /// The least member that holds a point: the intersection of every member
    /// that holds it.
    ///
    /// # Specification
    /// - ensures: the result is a member, holds `point`, and is included in
    ///   every member that holds `point`.
    /// - fails: a point at or past the carrier is refused by name.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DualityError::ElementOutside`]: `point` is at or past the carrier.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every point of every lattice over up to three points,
    ///   against the members that hold it, separates a union taken for the
    ///   intersection.
    /// - witness: `tests::finite::a_ring_of_sets_reads_back_from_its_spectrum`
    #[spec(ensures: |ref ret| match *ret {
        Ok(least) => least.contains(point) == Membership::Inside,
        Err(error) => error == DualityError::ElementOutside(point),
    })]
    #[inline]
    pub fn least_member(
        &self,
        point: Element,
    ) -> Result<ElementSet, DualityError>
    {
        let whole = first(self.carrier)?;
        if whole.contains(point) == Membership::Outside {
            return Err(DualityError::ElementOutside(point));
        }
        let mut least = whole;
        for member in &self.members {
            if member.contains(point) == Membership::Inside {
                least = least.meet(*member);
            }
        }
        Ok(least)
    }

    /// The spectrum: the join-irreducible members, which are the least
    /// members at the points, ordered by inclusion.
    ///
    /// # Specification
    /// - ensures: the points of the spectrum are the distinct least members, in
    ///   increasing order of their bits, and one lies below another exactly
    ///   when it is included in it.
    /// - fails: only on a broken invariant of the lattice.
    /// - panics: none.
    /// - intension: one intersection per point and member, so the work is the
    ///   carrier times the members, and no union is formed.
    ///
    /// # Errors
    /// - [`DualityError::TooManyElements`], [`DualityError::ElementOutside`]:
    ///   unreachable for a lattice [`SetRing::generated`] or
    ///   [`FinitePoset::down_sets`] makes.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every lattice over up to three points, against the
    ///   members that are no union of smaller members, separates a lost or an
    ///   extra point; the down-sets of every small poset read back to the
    ///   poset.
    /// - witness: `tests::finite::a_ring_of_sets_reads_back_from_its_spectrum`
    /// - witness: `tests::finite::birkhoff_duality_round_trips_on_small_posets`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |spectrum| spectrum.points.len() == spectrum.poset.below.len()))]
    #[inline]
    pub fn spectrum(&self) -> Result<Spectrum, DualityError>
    {
        let mut points = Vec::with_capacity(usize::from(self.carrier));
        for point in 0 .. usize::from(self.carrier) {
            let least = self.least_member(Element::from(point))?;
            points.push(least);
        }
        points.sort_unstable();
        points.dedup();
        let mut below = Vec::with_capacity(points.len());
        for upper in &points {
            let mut set = ElementSet::EMPTY;
            for (index, lower) in points.iter().enumerate() {
                if lower.compare(*upper) == Comparison::Below {
                    let bit = element_bit(Element::from(index))?;
                    set = set.union(bit);
                }
            }
            below.push(set);
        }
        Ok(Spectrum {
            points,
            poset: FinitePoset { below },
        })
    }
}

/// The spectrum of a finite distributive lattice of sets: its join-irreducible
/// members, and the poset they form under inclusion.
///
/// # Specification
/// - ensures: element `i` of the poset is point `i`, and the order is inclusion
///   of points.
/// - provides: the representation of each member as the down-set of the points
///   below it, and its inverse.
/// - panics: none.
/// - executable: none — a type-level block: the invariant is
///   [`SetRing::spectrum`]'s, which makes it.
///
/// # Adequacy
/// - hypothesis: L2 — every lattice over up to three points, sent to the
///   down-sets of its spectrum and back, separates a representation that is not
///   one to one.
/// - witness: `tests::finite::a_ring_of_sets_reads_back_from_its_spectrum`
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct Spectrum
{
    /// The join-irreducible members, in increasing order of their bits.
    points: Vec<ElementSet>,
    /// The points ordered by inclusion.
    poset: FinitePoset,
}

impl Spectrum
{
    /// The join-irreducible members, in increasing order of their bits.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn points(&self) -> &[ElementSet]
    {
        &self.points
    }

    /// The points ordered by inclusion.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn poset(&self) -> &FinitePoset
    {
        &self.poset
    }

    /// The down-set of the spectrum that represents a set: the points the
    /// set includes.
    ///
    /// # Specification
    /// - ensures: for a member of the lattice, [`Self::member`] reads the
    ///   member back.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every member of every lattice over up to three
    ///   points, read back, separates a point taken for its complement.
    /// - witness: `tests::finite::a_ring_of_sets_reads_back_from_its_spectrum`
    #[spec(ensures: |ret| usize::try_from(ret.0.count_ones()).is_ok_and(|ones| ones <= self.points.len()))]
    #[must_use]
    #[inline]
    pub fn below(
        &self,
        set: ElementSet,
    ) -> ElementSet
    {
        let mut down = ElementSet::EMPTY;
        for (index, point) in self.points.iter().enumerate() {
            if point.compare(set) == Comparison::Below {
                let bit = element_bit(Element::from(index)).unwrap_or_default();
                down = down.union(bit);
            }
        }
        down
    }

    /// The member a down-set of the spectrum represents: the union of its
    /// points.
    ///
    /// # Specification
    /// - ensures: the empty down-set is the empty member.
    /// - fails: an element at or past the number of points is refused by name.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DualityError::ElementOutside`]: `down` holds an element at or past
    ///   the number of points.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every down-set of every spectrum over up to three
    ///   points, mapped and read back, separates a lost point; L3 — an element
    ///   past the points separates the refusal.
    /// - witness: `tests::finite::a_ring_of_sets_reads_back_from_its_spectrum`
    #[spec(ensures: |ref ret| match *ret {
        Ok(member) => down != ElementSet::EMPTY || member == ElementSet::EMPTY,
        Err(error) => matches!(error, DualityError::ElementOutside(_)),
    })]
    #[inline]
    pub fn member(
        &self,
        down: ElementSet,
    ) -> Result<ElementSet, DualityError>
    {
        let mut member = ElementSet::EMPTY;
        for element in down.elements() {
            let point = self
                .points
                .get(usize::from(element))
                .ok_or(DualityError::ElementOutside(element))?;
            member = member.union(*point);
        }
        Ok(member)
    }
}

/// A monotone map from one finite poset to another: the image of each
/// element of the source, in element order.
///
/// # Specification
/// - ensures: the map keeps the order of the source.
/// - provides: the preimage homomorphism on down-sets, and the map read back
///   from such a homomorphism.
/// - panics: none.
/// - executable: none — a type-level block: the invariant is the constructors',
///   each of which checks it.
///
/// # Adequacy
/// - hypothesis: L2 — every map between posets on up to three elements, the
///   monotone ones read back from their preimages, separates a missed break of
///   order and a lost image.
/// - witness: `tests::finite::monotone_maps_and_preimages_go_one_to_one`
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct MonotoneMap
{
    /// The image of each element of the source.
    images: Vec<Element>,
}

impl MonotoneMap
{
    /// Admits a map from `source` to `target` given by the image of each
    /// element of the source.
    ///
    /// # Specification
    /// - ensures: the map's images are `images`, in element order.
    /// - fails: another number of images than the source's elements, an image
    ///   past the target, and a map that does not keep the order are refused,
    ///   the last by its least pair.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DualityError::ImageCount`]: `images` does not hold one image per
    ///   element of the source.
    /// - [`DualityError::ElementOutside`]: an image is at or past the target's
    ///   count.
    /// - [`DualityError::NotMonotone`]: the image of an element is not below
    ///   the image of an element above it.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every map between posets on up to three elements
    ///   separates a missed break of order; L3 — one image short and an image
    ///   past the target separate the other refusals.
    /// - witness: `tests::finite::monotone_maps_and_preimages_go_one_to_one`
    #[spec(ensures: |ref ret| match *ret {
        Ok(ref map) => map.images.len() == source.below.len(),
        Err(error) => matches!(error, DualityError::ImageCount | DualityError::ElementOutside(_) | DualityError::NotMonotone(..)),
    })]
    #[inline]
    pub fn new(
        source: &FinitePoset,
        target: &FinitePoset,
        images: Vec<Element>,
    ) -> Result<Self, DualityError>
    {
        if images.len() != source.below.len() {
            return Err(DualityError::ImageCount);
        }
        for &image in &images {
            let _down = target.below(image)?;
        }
        for (index, (&image, set)) in images.iter().zip(&source.below).enumerate() {
            let upper = Element::from(index);
            let image_down = target.below(image)?;
            for lower in set.elements() {
                let lower_image = images
                    .get(usize::from(lower))
                    .copied()
                    .ok_or(DualityError::ElementOutside(lower))?;
                if image_down.contains(lower_image) == Membership::Outside {
                    return Err(DualityError::NotMonotone(lower, upper));
                }
            }
        }
        Ok(Self { images })
    }

    /// The image of each element of the source, in element order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn images(&self) -> &[Element]
    {
        &self.images
    }

    /// The preimage of a set of the target: the elements of the source whose
    /// image it holds. It sends a down-set to a down-set, and it is a lattice
    /// homomorphism from the down-sets of the target to those of the source.
    ///
    /// # Specification
    /// - ensures: the empty set goes to the empty set.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every monotone map between posets on up to three
    ///   elements, on every down-set of its target, separates an image taken
    ///   for a preimage.
    /// - witness: `tests::finite::monotone_maps_and_preimages_go_one_to_one`
    #[spec(ensures: |ret| set != ElementSet::EMPTY || ret == ElementSet::EMPTY)]
    #[must_use]
    #[inline]
    pub fn preimage(
        &self,
        set: ElementSet,
    ) -> ElementSet
    {
        let mut preimage = ElementSet::EMPTY;
        for (index, image) in self.images.iter().enumerate() {
            if set.contains(*image) == Membership::Inside {
                let bit = element_bit(Element::from(index)).unwrap_or_default();
                preimage = preimage.union(bit);
            }
        }
        preimage
    }

    /// The monotone map a lattice homomorphism names, the homomorphism given
    /// by its image of each principal down-set of `target`: each element of
    /// the source goes to the least element whose down-set's image holds it.
    ///
    /// # Specification
    /// - ensures: [`Self::preimage`] of each principal down-set of `target` is
    ///   its given image.
    /// - fails: another number of images than the target's elements, an image
    ///   holding an element past the source, an element with no least image,
    ///   and images that are no preimages are refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DualityError::ImageCount`]: `preimages` does not hold one image per
    ///   element of the target.
    /// - [`DualityError::ElementOutside`]: an image holds an element at or past
    ///   the source's count.
    /// - [`DualityError::NoLeastImage`]: no least element of the target has a
    ///   down-set whose image holds this element of the source.
    /// - [`DualityError::NotHomomorphism`]: the image of this element's
    ///   down-set is not its preimage under the map read back.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every monotone map between posets on up to three
    ///   elements, read back from its preimages, separates a greatest element
    ///   taken for the least; L3 — preimages of a map that is not monotone and
    ///   images with a gap separate the refusals.
    /// - witness: `tests::finite::monotone_maps_and_preimages_go_one_to_one`
    #[spec(ensures: |ref ret| match *ret {
        Ok(ref map) => map.images.len() == source.below.len(),
        Err(error) => matches!(error, DualityError::ImageCount | DualityError::ElementOutside(_) | DualityError::NoLeastImage(_) | DualityError::NotHomomorphism(_) | DualityError::NotMonotone(..)),
    })]
    #[inline]
    pub fn of_preimages(
        source: &FinitePoset,
        target: &FinitePoset,
        preimages: &[ElementSet],
    ) -> Result<Self, DualityError>
    {
        if preimages.len() != target.below.len() {
            return Err(DualityError::ImageCount);
        }
        let whole = first(source.count())?;
        for preimage in preimages {
            if let Some(outside) = ElementSet(preimage.0 & !whole.0).elements().next() {
                return Err(DualityError::ElementOutside(outside));
            }
        }
        let mut above = vec![ElementSet::EMPTY; target.below.len()];
        for (index, set) in target.below.iter().enumerate() {
            let bit = element_bit(Element::from(index))?;
            for lower in set.elements() {
                if let Some(slot) = above.get_mut(usize::from(lower)) {
                    *slot = slot.union(bit);
                }
            }
        }
        let mut images = Vec::with_capacity(source.below.len());
        for index in 0 .. source.below.len() {
            let element = Element::from(index);
            let mut candidates = ElementSet::EMPTY;
            for (target_index, preimage) in preimages.iter().enumerate() {
                if preimage.contains(element) == Membership::Inside {
                    let bit = element_bit(Element::from(target_index))?;
                    candidates = candidates.union(bit);
                }
            }
            let least = candidates.elements().find(|candidate| {
                above
                    .get(usize::from(*candidate))
                    .is_some_and(|up| candidates.compare(*up) == Comparison::Below)
            });
            let image = least.ok_or(DualityError::NoLeastImage(element))?;
            images.push(image);
        }
        let map = Self::new(source, target, images)?;
        for (index, (preimage, set)) in preimages.iter().zip(&target.below).enumerate() {
            if map.preimage(*set) != *preimage {
                return Err(DualityError::NotHomomorphism(Element::from(index)));
            }
        }
        Ok(map)
    }
}
