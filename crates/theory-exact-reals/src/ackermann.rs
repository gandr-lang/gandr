//! Ackermann's code of the hereditarily finite sets, Tarau's operations on
//! them, and the real code of Cantone and Policriti as a plan.
//!
//! A hereditarily finite set is a finite set whose members are hereditarily
//! finite sets. Ackermann's code `N(x) = Σ_{y ∈ x} 2^N(y)` is a bijection
//! onto the natural numbers. A [`Sets`] table holds each set once, after its
//! members, so a fold over the members is one step up the table. After Tarau,
//! [`Sets::set`] folds the codes of the members, [`Sets::unrank`] unfolds the
//! bits of a code, and [`Sets::successor`] gives the next set from the
//! members alone.
//!
//! The real code `R(x) = Σ_{y ∈ x} 2^-R(y)` puts a minus sign on each
//! exponent. [`code`] writes it as a plan for a set of rank at most 3. Each
//! member of such a set has the code `0`, `1`, `1/2` or `3/2`, so each term is
//! a constant or the registered cut of a square root. A set of rank 4 reads
//! `2^-x` at an irrational `x`, and no node of a plan writes that.
//!
//! # Boundaries
//!
//! The fold carries over from `N` to `R`, and so does the successor: for the
//! `k` trailing ones of `i`, `R(h_{i+1}) = R(h_i) - R(h_{2^k - 1}) + R({h_k})`.
//! The unfold does not carry over. Its step needs a transformer that is a
//! bijection and that gives each member a smaller code than its set. `R` has
//! neither property: `R({{∅}}) = 1/2`, and its member has the code `1`. So a
//! real code reads back only by a search.
//!
//! On the sixteen sets of rank at most 3, the machine certifies a strict order
//! of each pair of codes, so `R` is injective there. The read-back of Cantone,
//! Omodeo and Policriti grows a cumulus by the set of least Ackermann code
//! whose union with the cumulus has a code at or below the real. That test
//! holds at its boundary, where no enclosure separates its two sides.
//!
//! So at a code that reads a cut, the machine certifies neither side, and the
//! read-back stalls. At a dyadic code, the machine certifies the equality, and
//! the read-back gives the set back. The least code comes first, so the
//! read-back of `R({{{∅}}})` takes `{{∅}}`, and then it needs a set of rank 4.
//!
//! # Items
//!
//! - [`Sets`], [`SetId`] — a table of hereditarily finite sets, and a set by
//!   its place in it.
//! - [`Ackermann`], [`Rank`] — Ackermann's code of a set, and its rank.
//! - [`code`], [`CodeError`] — the real code as a plan, and the refusals.
//!
//! # References
//!
//! - `Tarau-2008-functional_hitchhikers_guide_hereditarily_finite_sets_ackermann_encodings_pairing_functions` —
//!   exemplar: section 3 states Ackermann's code as the recursive use of a
//!   bijection from finite sets of naturals to naturals, and section 4 carries
//!   the successor and the arithmetic of the naturals to the sets. Paul Tarau,
//!   2008, `arXiv:0808.0754`.
//! - `Tarau-2008-ranking_catamorphisms_unranking_anamorphisms_hereditarily_finite_datatypes` —
//!   exemplar: section 2 states ranking as a fold and unranking as an unfold,
//!   and Proposition 1 asks of the transformer a bijection that gives each
//!   member a smaller code. Paul Tarau, 2008, `arXiv:0808.0753`.
//! - `vault:01a1b278-5641-7c20-95d3-093641459620` — exemplar: the source page
//!   of Domenico Cantone and Alberto Policriti, "Encoding Sets as Real
//!   Numbers", 2018, `arXiv:1806.09329`. Its extended version states the code
//!   `R` and the identity of its successor.

use alloc::vec::Vec;
use core::ops::Shl as _;

use foldhash::fast::FixedState;
use hashbrown::HashMap;
use num_bigint::BigInt;

use crate::dyadic::Dyadic;
use crate::dyadic::Exactness;
use crate::dyadic::Exponent;
use crate::dyadic::Precision;
use crate::dyadic::Rounding;
use crate::interval::Bound;
use crate::interval::NumericInterval;
use crate::interval::Orientation;
use crate::plan::Evidence;
use crate::plan::PlanBuilder;
use crate::plan::PlanError;
use crate::plan::Real;
use crate::plan::RealId;
use crate::schema::square_root;

/// Ackermann's code of a hereditarily finite set.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Ackermann(u64);

impl From<u64> for Ackermann
{
    /// Convert or project the represented value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: u64) -> Self
    {
        return Self(value);
    }
}

impl From<Ackermann> for u64
{
    /// Convert or project the represented value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: Ackermann) -> Self
    {
        return value.0;
    }
}

/// The rank of a hereditarily finite set: zero for the empty set, and one more
/// than the greatest rank of a member for any other set.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Rank(u32);

impl From<u32> for Rank
{
    /// Convert or project the represented value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: u32) -> Self
    {
        return Self(value);
    }
}

impl From<Rank> for u32
{
    /// Convert or project the represented value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: Rank) -> Self
    {
        return value.0;
    }
}

/// A hereditarily finite set: its place in the [`Sets`] table that holds it.
/// Two places of one table are equal exactly when their sets are equal.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SetId(u32);

/// Why a set has no place in a table, or no real code here.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum CodeError
{
    /// Ackermann's code of the set does not fit 64 bits.
    Wide,
    /// The table holds no set at the place.
    Unknown,
    /// The set's rank is above 3, so a term of its real code is `2^-x` at an
    /// irrational `x`.
    Rank,
    /// The builder holds no more nodes.
    Plan(PlanError),
}

/// One set of a table: its members, its code and its rank.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct Entry
{
    /// The members, each once, in the increasing order of their codes.
    members: Vec<SetId>,
    /// Ackermann's code of the set.
    ackermann: Ackermann,
    /// The rank of the set.
    rank: Rank,
}

/// A table of the hereditarily finite sets whose codes fit 64 bits: the sets
/// of rank at most 4, and some of rank 5.
///
/// # Specification
/// - invariant: each set stands once, after each of its members. Its members
///   stand in the increasing order of their codes. Its code is the sum of
///   `2^N(y)` over its members `y`, and its rank is one more than the rank of
///   its last member, or zero.
#[derive(Clone, Debug, Default)]
pub struct Sets
{
    /// The sets, each after its members.
    entries: Vec<Entry>,
    /// The place of each set, by its code.
    places: HashMap<Ackermann, SetId, FixedState>,
}

impl Sets
{
    /// The empty table.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new() -> Self
    {
        return Self::default();
    }

    /// The entry of the set at `set`.
    ///
    /// # Specification
    /// trivial.
    fn entry(
        &self,
        set: SetId,
    ) -> Result<&Entry, CodeError>
    {
        let index = usize::try_from(set.0).map_err(|_wide| CodeError::Unknown)?;
        return self.entries.get(index).ok_or(CodeError::Unknown);
    }

    /// The set of `members`, each once: Tarau's ranking, the fold of the codes
    /// of the members.
    ///
    /// # Specification
    /// - ensures: the place of the set whose members are the sets of `members`.
    ///   Its code is the sum of `2^N(y)` over its distinct members `y`. A set
    ///   that the table holds keeps its place.
    /// - fails: refuses a place that the table does not hold as
    ///   [`CodeError::Unknown`], and a set whose code does not fit 64 bits as
    ///   [`CodeError::Wide`].
    /// - panics: none.
    /// - executable: none — the clause restates the fold.
    /// - intension: one sort of the members, and one hash of the code.
    ///
    /// # Errors
    /// - [`CodeError::Unknown`]: a member has no place in the table.
    /// - [`CodeError::Wide`]: a member's code is 64 or more.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every set of rank at most 4, built again from its
    ///   members in reverse order with a repeat, keeps its place. L3 — a member
    ///   whose code is 64, and a place past the table.
    /// - witness: `tests::ackermann::tarau_operations_agree_with_the_codes`
    #[inline]
    pub fn set(
        &mut self,
        members: &[SetId],
    ) -> Result<SetId, CodeError>
    {
        let mut sorted = members
            .iter()
            .map(|&member| {
                let entry = self.entry(member)?;
                return Ok((entry.ackermann, entry.rank, member));
            })
            .collect::<Result<Vec<_>, CodeError>>()?;
        // Distinct sets have distinct codes, so the sort and the deduplication
        // read the codes alone.
        sorted.sort_unstable();
        sorted.dedup();
        let mut sum = 0_u64;
        for &(code, ..) in &sorted {
            let position = u32::try_from(code.0).map_err(|_wide| CodeError::Wide)?;
            let power = 1_u64.checked_shl(position).ok_or(CodeError::Wide)?;
            sum = sum.checked_add(power).ok_or(CodeError::Wide)?;
        }
        let ackermann = Ackermann(sum);
        if let Some(&place) = self.places.get(&ackermann) {
            return Ok(place);
        }
        let rank = sorted
            .last()
            .map_or(Rank(0), |&(_, rank, _)| Rank(rank.0.saturating_add(1)));
        let place = SetId(u32::try_from(self.entries.len()).map_err(|_full| CodeError::Wide)?);
        self.entries.push(Entry {
            members: sorted.into_iter().map(|(_, _, member)| member).collect(),
            ackermann,
            rank,
        });
        self.places.insert(ackermann, place);
        return Ok(place);
    }

    /// The members of the set at `set`, in the increasing order of their codes.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// - [`CodeError::Unknown`]: the table holds no set at the place.
    #[inline]
    pub fn members(
        &self,
        set: SetId,
    ) -> Result<&[SetId], CodeError>
    {
        return self.entry(set).map(|entry| entry.members.as_slice());
    }

    /// Ackermann's code of the set at `set`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// - [`CodeError::Unknown`]: the table holds no set at the place.
    #[inline]
    pub fn ackermann(
        &self,
        set: SetId,
    ) -> Result<Ackermann, CodeError>
    {
        return self.entry(set).map(|entry| entry.ackermann);
    }

    /// The rank of the set at `set`.
    ///
    /// # Specification
    /// - ensures: zero for the empty set, and one more than the rank of the
    ///   last member otherwise. The last member has the greatest code, and so
    ///   the greatest rank.
    /// - fails: refuses a place that the table does not hold.
    /// - panics: none.
    /// - executable: none — the clause restates the field.
    ///
    /// # Errors
    /// - [`CodeError::Unknown`]: the table holds no set at the place.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the sets of rank at most 3 are those whose codes are
    ///   below 16, and the sets of rank 4 those from 16 to 65535.
    /// - witness: `tests::ackermann::tarau_operations_agree_with_the_codes`
    #[inline]
    pub fn rank(
        &self,
        set: SetId,
    ) -> Result<Rank, CodeError>
    {
        return self.entry(set).map(|entry| entry.rank);
    }

    /// The set whose code is `code`: Tarau's unranking, the unfold of the bits
    /// of the code.
    ///
    /// # Specification
    /// - ensures: the place of the set whose members are the sets of the
    ///   positions of the set bits of `code`.
    /// - fails: refuses a table that holds `2^32` sets as [`CodeError::Wide`].
    /// - panics: none.
    /// - executable: none — the clause restates the unfold.
    /// - intension: one visit of each set bit of each code below `code` that
    ///   the unfold reaches and the table does not hold. Each position of a set
    ///   bit of a positive code lies below the code, so an explicit stack of at
    ///   most 64 codes a level replaces the recursion.
    ///
    /// # Errors
    /// - [`CodeError::Wide`]: the table holds no more sets.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — as [`Self::set`]: the fold inverts the unfold on
    ///   every code below 65536.
    /// - witness: `tests::ackermann::tarau_operations_agree_with_the_codes`
    #[inline]
    pub fn unrank(
        &mut self,
        code: Ackermann,
    ) -> Result<SetId, CodeError>
    {
        let mut waiting = alloc::vec![code];
        let mut members = Vec::new();
        while let Some(&top) = waiting.last() {
            if self.places.contains_key(&top) {
                waiting.pop();
                continue;
            }
            members.clear();
            let mut ready = true;
            let mut rest = top.0;
            while rest != 0 {
                let position = Ackermann(u64::from(rest.trailing_zeros()));
                // Clear the lowest set bit.
                rest &= rest.wrapping_sub(1);
                if let Some(&member) = self.places.get(&position) {
                    members.push(member);
                }
                else {
                    waiting.push(position);
                    ready = false;
                }
            }
            if ready {
                self.set(&members)?;
                waiting.pop();
            }
        }
        return self.places.get(&code).copied().ok_or(CodeError::Unknown);
    }

    /// The set whose code is one more: Tarau's successor, on the members
    /// alone.
    ///
    /// # Specification
    /// - ensures: with `k` the count of leading members `h_0, …, h_{k-1}`, the
    ///   trailing ones of the code, the set without them and with `h_k`. So its
    ///   code is the code of `set` plus one.
    /// - fails: refuses a place that the table does not hold, and a successor
    ///   whose code does not fit 64 bits.
    /// - panics: none.
    /// - executable: none — the clause restates the construction.
    /// - intension: one comparison of each leading member with its index, and
    ///   one copy of the other members.
    ///
    /// # Errors
    /// - [`CodeError::Unknown`]: the table holds no set at the place.
    /// - [`CodeError::Wide`]: the successor's code does not fit 64 bits.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the successor of each set whose code is below 65535
    ///   is the set of the next code.
    /// - witness: `tests::ackermann::tarau_operations_agree_with_the_codes`
    #[inline]
    pub fn successor(
        &mut self,
        set: SetId,
    ) -> Result<SetId, CodeError>
    {
        let members = self.members(set)?.to_vec();
        let mut ones = 0_u64;
        for &member in &members {
            if self.ackermann(member)? != Ackermann(ones) {
                break;
            }
            ones = ones.saturating_add(1);
        }
        let first = self.unrank(Ackermann(ones))?;
        let kept = usize::try_from(ones).map_err(|_wide| CodeError::Wide)?;
        let rest = members.get(kept ..).unwrap_or_default();
        let mut next = Vec::with_capacity(rest.len().saturating_add(1));
        next.push(first);
        next.extend_from_slice(rest);
        return self.set(&next);
    }
}

/// Build the real code `R(set) = Σ_{y ∈ set} 2^-R(y)` of the set at `set` of
/// `sets`, and return its node.
///
/// # Specification
/// - requires: the set's rank is at most 3.
/// - ensures: the sum of one term for each member, in the order of the members,
///   or zero for the empty set. A member whose code `d` is a whole number gives
///   the constant `2^-d`. A member whose code is `d = m/2` gives the registered
///   cut of the square root of `2^-m`, whose hull is the closed interval from
///   zero to one.
/// - fails: refuses a set of rank above 3 as [`CodeError::Rank`], a place that
///   the table does not hold as [`CodeError::Unknown`], and passes the
///   builder's failure on as [`CodeError::Plan`].
/// - panics: none.
/// - executable: none — the clause restates the construction.
/// - intension: one exact sum for the code of each member, and one node for
///   each term and each sum.
///
/// # Errors
/// - [`CodeError::Rank`]: the set's rank is above 3.
/// - [`CodeError::Unknown`]: the table holds no set at the place.
/// - [`CodeError::Plan`]: the builder holds no more nodes.
///
/// # Adequacy
/// - hypothesis: L2 — the code of each set of rank at most 3, enclosed by the
///   machine and held to its exact value. L3 — a set of rank 4.
/// - witness: `tests::ackermann::each_code_encloses_and_replays`
#[inline]
pub fn code(
    builder: &mut PlanBuilder,
    sets: &Sets,
    set: SetId,
    laws: Evidence,
) -> Result<RealId, CodeError>
{
    if sets.rank(set)? > Rank(3) {
        return Err(CodeError::Rank);
    }
    let mut sum: Option<RealId> = None;
    for &member in sets.members(set)? {
        // The member has rank at most 2, so each of its members is `∅` or
        // `{∅}`, whose code is its count of members.
        let mut exact = Dyadic::ZERO;
        for &inner in sets.members(member)? {
            let count =
                i64::try_from(sets.members(inner)?.len()).map_err(|_wide| CodeError::Rank)?;
            let added = exact
                .add(
                    &half_power(&Dyadic::from(count))?,
                    Precision::MAX,
                    Rounding::Floor,
                )
                .map_err(|_range| CodeError::Rank)?;
            if added.exactness() != Exactness::Exact {
                return Err(CodeError::Rank);
            }
            exact = added.into_value();
        }
        let term = term(builder, &exact, laws)?;
        sum = Some(match sum {
            None => term,
            Some(left) => builder
                .real(Real::Add(left, term))
                .map_err(CodeError::Plan)?,
        });
    }
    return sum.map_or_else(
        || {
            builder
                .real(Real::Constant(Dyadic::ZERO))
                .map_err(CodeError::Plan)
        },
        Ok,
    );
}

/// The node of `2^-d` for the dyadic code `d` of a member.
///
/// # Specification
/// - ensures: the constant `2^-d` for a whole `d`, and the registered cut of
///   the square root of `2^-m` for `d = m/2` with `m` odd.
/// - fails: refuses any other `d` as [`CodeError::Rank`], and passes the
///   builder's failure on as [`CodeError::Plan`].
/// - panics: none.
///
/// # Errors
/// - [`CodeError::Rank`]: `d` has more than one bit below the point.
/// - [`CodeError::Plan`]: the builder holds no more nodes.
///
/// # Adequacy
/// - hypothesis: L2 — as [`code`].
/// - witness: `tests::ackermann::each_code_encloses_and_replays`
fn term(
    builder: &mut PlanBuilder,
    code: &Dyadic,
    laws: Evidence,
) -> Result<RealId, CodeError>
{
    if i32::from(code.exponent()) >= 0_i32 {
        return builder
            .real(Real::Constant(half_power(code)?))
            .map_err(CodeError::Plan);
    }
    if i32::from(code.exponent()) != -1_i32 {
        return Err(CodeError::Rank);
    }
    // `2^-(m/2)` is the square root of `2^-m`, which lies between zero and
    // one, each a witness of its side.
    let doubled =
        Dyadic::new(code.mantissa(), Exponent::from(0_i32)).map_err(|_range| CodeError::Rank)?;
    let hull = NumericInterval::new(
        Bound::closed(Dyadic::ZERO),
        Bound::closed(Dyadic::ONE),
        Orientation::Proper,
    )
    .map_err(|_reversed| CodeError::Rank)?;
    return square_root(builder, half_power(&doubled)?, hull, laws).map_err(CodeError::Plan);
}

/// `2^-n` for a whole dyadic `n`.
///
/// # Specification
/// - ensures: the dyadic `1 · 2^-n`.
/// - fails: refuses an `n` that is not a whole number, or whose negation leaves
///   the range of [`Exponent`], as [`CodeError::Rank`].
/// - panics: none.
///
/// # Errors
/// - [`CodeError::Rank`]: `n` is not a whole number in range.
fn half_power(whole: &Dyadic) -> Result<Dyadic, CodeError>
{
    let shift = u32::try_from(i32::from(whole.exponent())).map_err(|_fraction| CodeError::Rank)?;
    let value = i32::try_from(whole.mantissa().shl(shift)).map_err(|_wide| CodeError::Rank)?;
    let exponent = value.checked_neg().ok_or(CodeError::Rank)?;
    return Dyadic::new(BigInt::from(1_u8), Exponent::from(exponent))
        .map_err(|_range| CodeError::Rank);
}
