//! The guarded template as a reduction: a family of certificates collapses
//! onto its template, and each member's row includes back as its instance.
//!
//! The source holds one cell for each member of the family. The target holds
//! one cell for each member too: its row, the guard of the arm that the member
//! holds at each entry. The template is the part that the rows share, and its
//! size is the size `s` that [`FamilyCostReport`](crate::FamilyCostReport)
//! gives. The collapse reads a member's row from its peak. The inclusion puts
//! the row's arms in place in the carrier. A row is exact, so each witness is
//! an identity, and it closes only between equal composites. The replay checks
//! that the collapse gives each row back after the inclusion, and that each
//! member equals its instance. The fold is untrusted, and the replay decides
//! it.
//!
//! # References
//!
//! - `Barrett-2025-proof_compression_subatomic_logic_guarded_substitutions` —
//!   exemplar: Definition 37 states a superposition and its projections by
//!   guarded substitutions. The template is the superposition, and a row is the
//!   guarded substitution that projects one member.
//! - `vault:01a1aa2d-a69c-7030-91e0-337d68d88151` — anchor: §
//!   presented-spaces-normal-forms. The superposition of a family is a
//!   reduction, and its rows compare by exact identity, so each witness is an
//!   identity.
//! - `vault:01a12723-951b-7183-87d8-4fbc83c6a779` — anchor: a row is one guard
//!   for each point of the template, as [`TemplateRow`] holds it.

use alloc::borrow::Cow;
use alloc::vec::Vec;

use anodized::spec;
use gandr_theory_cell_complexes::CellAlphabet;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_coherent_resolutions::Tracelet;
use gandr_theory_discrete_morse::Answer;
use gandr_theory_discrete_morse::Closure;
use gandr_theory_discrete_morse::MorseError;
use gandr_theory_discrete_morse::Reduction;
use gandr_theory_discrete_morse::Refusal;

use crate::boundary::MemberIndex;
use crate::boundary::NodeCount;
use crate::template::GuardedTemplate;
use crate::template::InheritanceCache;
use crate::template::TemplateObstruction;
use crate::template::TemplateRefusal;
use crate::template::TemplateRow;
use crate::template::anti_unify_tracelets;

/// A family of certificates read against a template: a [`Reduction`] from
/// the family onto the template's rows.
#[derive(Debug)]
pub struct TemplateReduction<'family, A: CellAlphabet>
{
    /// The template that the family folds into.
    template: GuardedTemplate<A>,
    /// The family, one certificate for each member.
    family: &'family [Tracelet<A>],
    /// One cell for each member, in family order.
    members: Vec<MemberIndex>,
}

/// A composite of a template reduction: a certificate, or a row of the
/// template.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Folded<'family, A: CellAlphabet>
{
    /// A certificate: a member of the family, borrowed, or an instance of the
    /// template.
    Member(Cow<'family, Tracelet<A>>),
    /// The guard of the arm at each entry of the template.
    Row(TemplateRow),
}

/// The witness of a template reduction: an identity, because a row is exact.
/// It closes only between equal composites.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct Identity;

/// Why a template reduction cannot answer.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FoldFault
{
    /// The family holds no member at this cell.
    NoMember(MemberIndex),
    /// The template does not read a member's peak, or does not rebuild a row.
    Obstruction(TemplateObstruction),
    /// A collapse or a section reads a member alone, and it received a row.
    NotAMember,
    /// An inclusion or a retraction reads a row alone, and it received a
    /// certificate.
    NotARow,
}

/// The refusal of a template reduction for `fault`.
///
/// # Specification
/// trivial.
const fn refused(fault: FoldFault) -> Refusal<MemberIndex, FoldFault>
{
    Refusal::Morse(MorseError::Complex(fault))
}

/// The refusal of a template reduction for the template's `obstruction`.
///
/// # Specification
/// trivial.
const fn obstructed(obstruction: TemplateObstruction) -> Refusal<MemberIndex, FoldFault>
{
    refused(FoldFault::Obstruction(obstruction))
}

impl<'family, A: CellAlphabet> TemplateReduction<'family, A>
{
    /// Fold `family` into its template, and read the family against it.
    ///
    /// # Specification
    /// - ensures: one cell for each member of `family`, in family order,
    ///   against the template that [`anti_unify_tracelets`] gives.
    /// - fails: each [`TemplateRefusal`] of the fold, by its own name.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — generated families that the template tests fold, each
    ///   a reduction whose replay passes; L3 — a family whose arms are all
    ///   distinct keeps [`TemplateRefusal::DoesNotPay`]. The cell observer
    ///   rejects a dropped or reordered member.
    /// - witness: `tests::template::every_folded_family_replays_as_a_reduction`
    /// - witness: `tests::template::a_family_that_does_not_pay_is_no_reduction`
    #[spec(ensures: |output| output.as_ref().ok().is_none_or(|reduction|
        reduction.members.len() == family.len()
            && reduction.members.iter().enumerate().all(|(index, cell)| usize::from(*cell) == index)))]
    #[inline]
    pub fn fold(
        family: &'family [Tracelet<A>],
        store: &CellStore<A>,
        cache: &mut InheritanceCache,
    ) -> Result<Self, TemplateRefusal>
    {
        Ok(Self::over(
            anti_unify_tracelets(family, store, cache)?,
            family,
        ))
    }

    /// Read `family` against `template`, wherever the template comes from:
    /// the replay decides whether it reduces the family.
    ///
    /// # Specification
    /// - ensures: one cell for each member of `family`, in family order.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the template of an honest family read against a
    ///   family with one member changed. The cell observer rejects a dropped or
    ///   reordered member.
    /// - witness: `tests::template::a_member_unlike_its_instance_is_refused_by_name`
    #[spec(ensures: |output| output.members.len() == family.len()
        && output.members.iter().enumerate().all(|(index, cell)| usize::from(*cell) == index))]
    #[inline]
    #[must_use]
    pub fn over(
        template: GuardedTemplate<A>,
        family: &'family [Tracelet<A>],
    ) -> Self
    {
        Self {
            template,
            family,
            members: (0 .. family.len()).map(MemberIndex::from).collect(),
        }
    }

    /// The template that the family is read against.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn template(&self) -> &GuardedTemplate<A>
    {
        &self.template
    }

    /// The size of the target: the template's size `s`, which counts the
    /// skeleton, every arm and one guard for each arm. A row is the choice of
    /// guards that a member's own peak makes, so it adds no node.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn size(&self) -> NodeCount
    {
        self.template.size()
    }
}

impl<'family, A: CellAlphabet> Reduction for TemplateReduction<'family, A>
{
    type Cell = MemberIndex;
    type Composite = Folded<'family, A>;
    type Fault = FoldFault;
    type Witness = Identity;

    /// The members of the family.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn source(&self) -> &[Self::Cell]
    {
        &self.members
    }

    /// The members of the family again: each keeps one row in the target.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn target(&self) -> &[Self::Cell]
    {
        &self.members
    }

    /// The member at `cell`, borrowed.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn generator(
        &mut self,
        cell: &Self::Cell,
    ) -> Answer<Self, Self::Composite>
    {
        let family: &'family [Tracelet<A>] = self.family;
        family
            .get(usize::from(*cell))
            .map(|member| Folded::Member(Cow::Borrowed(member)))
            .ok_or_else(|| refused(FoldFault::NoMember(*cell)))
    }

    /// The row that a certificate's peak gives.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn collapse(
        &mut self,
        composite: &Self::Composite,
    ) -> Answer<Self, Self::Composite>
    {
        match *composite {
            Folded::Member(ref member) => self
                .template
                .row(&member.overlap.peak)
                .map(Folded::Row)
                .map_err(obstructed),
            Folded::Row(_) => Err(refused(FoldFault::NotAMember)),
        }
    }

    /// The instance of a row.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn include(
        &mut self,
        composite: &Self::Composite,
    ) -> Answer<Self, Self::Composite>
    {
        match *composite {
            Folded::Row(ref row) => self
                .template
                .instance(row)
                .map(|instance| Folded::Member(Cow::Owned(instance)))
                .map_err(obstructed),
            Folded::Member(_) => Err(refused(FoldFault::NotARow)),
        }
    }

    /// The identity from a certificate to its instance, which closes only when
    /// the two are equal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn section(
        &mut self,
        composite: &Self::Composite,
    ) -> Answer<Self, Option<Self::Witness>>
    {
        match *composite {
            Folded::Member(_) => Ok(Some(Identity)),
            Folded::Row(_) => Err(refused(FoldFault::NotAMember)),
        }
    }

    /// None: the template is the generalization of its members, so the
    /// collapse gives each row back after the inclusion by construction, and
    /// the replay checks it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn retraction(
        &mut self,
        composite: &Self::Composite,
    ) -> Answer<Self, Option<Self::Witness>>
    {
        match *composite {
            Folded::Row(_) => Ok(None),
            Folded::Member(_) => Err(refused(FoldFault::NotARow)),
        }
    }

    /// The identity: it holds no cell to carry.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn include_witness(
        &mut self,
        _witness: &Self::Witness,
    ) -> Answer<Self, Self::Witness>
    {
        Ok(Identity)
    }

    /// The identity: it holds no cell to carry.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn collapse_witness(
        &mut self,
        _witness: &Self::Witness,
    ) -> Answer<Self, Self::Witness>
    {
        Ok(Identity)
    }

    /// The identity: two identities compose to one.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn compose(
        &mut self,
        _first: &Self::Witness,
        _second: &Self::Witness,
    ) -> Answer<Self, Self::Witness>
    {
        Ok(Identity)
    }

    /// Whether `source` and `target` are equal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn closes(
        &mut self,
        _witness: &Self::Witness,
        source: &Self::Composite,
        target: &Self::Composite,
    ) -> Answer<Self, Closure>
    {
        Ok(if source == target {
            Closure::Closes
        }
        else {
            Closure::Open
        })
    }

    /// Check each member in family order: its row and the boundary of its
    /// instance exist, the instance gives the row back, and the instance is
    /// the member.
    ///
    /// The replay never builds an instance whole. An instance's skeleton is
    /// the carrier's, so the replay compares the member's skeleton with the
    /// carrier's in place, and it rebuilds only the peak and the join. A
    /// rebuilt peak equal to the member's gives the member's row back, because
    /// a row is a function of its peak.
    ///
    /// # Specification
    /// - ensures: `Ok` exactly when each member's peak gives a row, the row
    ///   gives an instance, the instance's peak gives the same row, and the
    ///   instance equals the member.
    /// - fails: the first member that fails comes back by name: an obstruction
    ///   of the template as [`Refusal::Morse`], a row that the round trip moves
    ///   as [`Refusal::Unretracted`], and an instance that differs from its
    ///   member as [`Refusal::Forged`].
    /// - panics: none.
    /// - executable: none — the body is the predicate.
    /// - intension: one match of a peak and one fold of a row into the
    ///   carrier's peak and join for each member, with a second match only
    ///   where the rebuilt peak differs.
    ///
    /// # Errors
    /// - [`Refusal::Morse`]: the template does not read a peak or rebuild a
    ///   row.
    /// - [`Refusal::Unretracted`]: an instance's peak gives another row.
    /// - [`Refusal::Forged`]: an instance differs from its member.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — every family that the template tests fold replays; L3
    ///   — a member whose join differs from its instance's is refused as
    ///   forged, and a member of another shape by the template's obstruction.
    /// - witness: `tests::template::every_folded_family_replays_as_a_reduction`
    /// - witness: `tests::template::a_member_unlike_its_instance_is_refused_by_name`
    #[inline]
    fn replay(&mut self) -> Answer<Self, ()>
    {
        let carrier = self.template.carrier();
        for (index, member) in self.family.iter().enumerate() {
            let cell = MemberIndex::from(index);
            let row = self
                .template
                .row(&member.overlap.peak)
                .map_err(obstructed)?;
            let (peak, join) = self.template.boundary(&row).map_err(obstructed)?;
            if peak != member.overlap.peak {
                let back = self.template.row(&peak).map_err(obstructed)?;
                return Err(if back == row {
                    Refusal::Forged(cell)
                }
                else {
                    Refusal::Unretracted(cell)
                });
            }
            let skeleton = carrier.path_a == member.path_a
                && carrier.path_b == member.path_b
                && carrier.overlap.left == member.overlap.left
                && carrier.overlap.right == member.overlap.right
                && carrier.overlap.kind == member.overlap.kind
                && carrier.overlap.unifier == member.overlap.unifier
                && carrier.overlap.seam == member.overlap.seam
                && carrier.overlap.right_renamed() == member.overlap.right_renamed();
            if !skeleton || join != member.joins_at {
                return Err(Refusal::Forged(cell));
            }
        }
        Ok(())
    }
}
