//! A family of local tables over a cover, its gluing, and its possibility.
//!
//! The members of a family are tables over scopes, and its overlaps are the
//! pairs of members to compare. The sheaf of tables puts a table on each
//! scope and restricts it by its semiring sum over the variables left out:
//! marginalisation in the probability semiring. A family glues when each pair
//! of an overlap restricts to one table on the variables both hold, and that
//! table is its section there. A pair that differs gives a
//! [`Disagreement`]: the overlap, the first entry where the two restrictions
//! differ, and both weights.
//!
//! On the edges of a junction tree, a family that glues has a joint whose
//! marginals are its members. On a cycle of scopes it need not, and the
//! possibility check finds the witness: a local entry of positive weight that
//! no global assignment extends with positive weight at every member.

use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;
use gandr_theory_cellular_sheaves::CoverIndex;
use gandr_theory_cellular_sheaves::Entry;
use gandr_theory_ordered_algebras::OrderedSemiring;

use crate::error::InferenceError;
use crate::table::Scope;
use crate::table::Table;

/// Tables over scopes, with the pairs of them to compare.
///
/// # Specification
/// - ensures: each overlap names two members of the family.
/// - provides: the members and the overlaps, the gluing and the possibility.
/// - panics: none.
/// - executable: none — a type-level block: the invariant is [`Family::new`]'s.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Family<E>
{
    /// The local tables.
    members: Vec<Table<E>>,
    /// The pairs of members to compare.
    overlaps: Vec<(CoverIndex, CoverIndex)>,
}

/// Where two members of a family differ.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Disagreement<E>
{
    /// The two members, as the overlap names them.
    pub members: (CoverIndex, CoverIndex),
    /// The variables that both hold.
    pub overlap: Scope,
    /// The first entry of the overlap where their restrictions differ.
    pub entry: Entry,
    /// The two restrictions' weights at that entry.
    pub weights: (E, E),
}

/// The verdict on a family.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Gluing<E>
{
    /// Each pair restricts to one table on its overlap: these tables, one for
    /// each overlap in order. With the members they are the glued section.
    Glued(Vec<Table<E>>),
    /// The pairs that differ, in the order of the overlaps; never empty.
    Obstructed(Vec<Disagreement<E>>),
}

/// Whether each local entry of positive weight extends to a global
/// assignment.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Possibility
{
    /// Each entry of each member whose weight is not zero is the restriction
    /// of a global assignment whose restriction to every member has a weight
    /// that is not zero.
    Extends,
    /// The entry of the member has a weight that is not zero, and no global
    /// assignment restricts to it with a weight that is not zero at every
    /// member. So no joint has the members as marginals.
    Contextual
    {
        /// The member.
        member: CoverIndex,
        /// The entry of its table.
        entry: Entry,
    },
}

impl<E> Family<E>
{
    /// The family of `members` whose pairs `overlaps` names.
    ///
    /// # Specification
    /// - ensures: the family holds the members and the overlaps in order.
    /// - fails: an overlap that names a member past the list is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`InferenceError::NoMember`]: an overlap names a member past the list.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — an overlap with a fourth member of three is refused
    ///   by its number.
    /// - witness: `tests::inference::a_contextual_family_glues_and_is_refused_a_joint`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |family| family.overlaps.iter().all(|&(first, second)| usize::from(first) < family.members.len() && usize::from(second) < family.members.len())))]
    #[inline]
    pub fn new(
        members: Vec<Table<E>>,
        overlaps: Vec<(CoverIndex, CoverIndex)>,
    ) -> Result<Self, InferenceError>
    {
        if let Some(past) = overlaps
            .iter()
            .flat_map(|&pair| <[CoverIndex; 2]>::from(pair))
            .find(|&member| usize::from(member) >= members.len())
        {
            return Err(InferenceError::NoMember(past));
        }
        Ok(Self { members, overlaps })
    }

    /// The local tables.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn members(&self) -> &[Table<E>]
    {
        &self.members
    }

    /// The pairs of members to compare.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn overlaps(&self) -> &[(CoverIndex, CoverIndex)]
    {
        &self.overlaps
    }

    /// The member at `index`.
    ///
    /// # Specification
    /// trivial.
    fn member(
        &self,
        index: CoverIndex,
    ) -> Result<&Table<E>, InferenceError>
    {
        self.members
            .get(usize::from(index))
            .ok_or(InferenceError::NoMember(index))
    }
}

impl<E: Clone + Eq> Family<E>
{
    /// Glue the members on each overlap: restrict both members of each pair
    /// to the variables they share by `semiring`'s sum, and compare.
    ///
    /// # Specification
    /// - ensures: [`Gluing::Glued`] with each overlap's table when every pair
    ///   restricts to one table, and otherwise each pair that differs, with its
    ///   first differing entry and both weights.
    /// - fails: a variable with two arities, and a sum past the carrier, are
    ///   refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`InferenceError::Mismatched`]: a pair gives a variable two arities.
    /// - [`InferenceError::Overflow`]: a sum passes the carrier.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the calibrated cliques of the network glue on their
    ///   separator; each clique weight raised in turn is obstructed at the
    ///   separator entry it sums into; the contextual family glues.
    /// - witness: `tests::inference::the_clique_marginals_glue_and_a_changed_weight_is_obstructed`
    /// - witness: `tests::inference::a_contextual_family_glues_and_is_refused_a_joint`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |gluing| match *gluing { Gluing::Glued(ref tables) => tables.len() == self.overlaps.len(), Gluing::Obstructed(ref differences) => !differences.is_empty() }))]
    #[inline]
    pub fn glue<S>(
        &self,
        semiring: &S,
    ) -> Result<Gluing<E>, InferenceError>
    where
        S: OrderedSemiring<Element = E>,
    {
        let mut left = Vec::new();
        let mut right = Vec::new();
        let mut glued = Vec::with_capacity(self.overlaps.len());
        let mut obstructed = Vec::new();
        for &(first, second) in &self.overlaps {
            let (one, other) = (self.member(first)?, self.member(second)?);
            let overlap = one.scope().meet(other.scope())?;
            one.marginal_into(semiring, &overlap, &mut left)?;
            other.marginal_into(semiring, &overlap, &mut right)?;
            let differing = left
                .iter()
                .zip(&right)
                .enumerate()
                .find(|&(_, (mine, theirs))| mine != theirs);
            match differing {
                None => glued.push(Table::new(overlap, left.clone())?),
                Some((entry, (mine, theirs))) => obstructed.push(Disagreement {
                    members: (first, second),
                    overlap,
                    entry: Entry::from(entry),
                    weights: (mine.clone(), theirs.clone()),
                }),
            }
        }
        if obstructed.is_empty() {
            Ok(Gluing::Glued(glued))
        }
        else {
            Ok(Gluing::Obstructed(obstructed))
        }
    }

    /// Whether each entry of each member whose weight is not `semiring`'s
    /// zero is the restriction of a global assignment that every member
    /// weighs above zero: one pass over the assignments of every variable.
    ///
    /// # Specification
    /// - ensures: [`Possibility::Contextual`] with the first member and entry,
    ///   in order, of positive weight that no such assignment reaches;
    ///   otherwise [`Possibility::Extends`].
    /// - fails: a variable with two arities, and a joint scope past the
    ///   machine's integers, are refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`InferenceError::Mismatched`]: two members give a variable two
    ///   arities.
    /// - [`InferenceError::TooLarge`]: the assignments of every variable pass
    ///   the machine's integers.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the contextual family of three tables, each two
    ///   agreeing on their overlap, is contextual at its first entry of
    ///   positive weight; the calibrated cliques of the network extend.
    /// - witness: `tests::inference::a_contextual_family_glues_and_is_refused_a_joint`
    /// - witness: `tests::inference::the_clique_marginals_glue_and_a_changed_weight_is_obstructed`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |possibility| match *possibility { Possibility::Contextual { member, .. } => usize::from(member) < self.members.len(), Possibility::Extends => true }))]
    #[inline]
    pub fn possibility<S>(
        &self,
        semiring: &S,
    ) -> Result<Possibility, InferenceError>
    where
        S: OrderedSemiring<Element = E>,
    {
        let zero = semiring.zero();
        let joint = Scope::join(self.members.iter().map(Table::scope))?;
        let projections = self
            .members
            .iter()
            .map(|member| {
                joint
                    .projection(member.scope())
                    .ok_or(InferenceError::Uncovered)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let mut reached: Vec<Vec<bool>> = self
            .members
            .iter()
            .map(|member| vec![false; member.weights().len()])
            .collect();
        for global in 0 .. usize::from(joint.width()) {
            let global = Entry::from(global);
            let possible = self
                .members
                .iter()
                .zip(&projections)
                .all(|(member, projection)| {
                    projection
                        .entry(global)
                        .and_then(|entry| member.at(entry))
                        .is_some_and(|weight| *weight != zero)
                });
            if !possible {
                continue;
            }
            for (marks, projection) in reached.iter_mut().zip(&projections) {
                if let Some(mark) = projection
                    .entry(global)
                    .and_then(|entry| marks.get_mut(usize::from(entry)))
                {
                    *mark = true;
                }
            }
        }
        let contextual =
            self.members
                .iter()
                .zip(&reached)
                .enumerate()
                .find_map(|(member, (table, marks))| {
                    table
                        .weights()
                        .iter()
                        .zip(marks)
                        .position(|(weight, &mark)| *weight != zero && !mark)
                        .map(|entry| Possibility::Contextual {
                            member: CoverIndex::from(member),
                            entry: Entry::from(entry),
                        })
                });
        Ok(contextual.unwrap_or(Possibility::Extends))
    }
}
