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
//! A family of families reduces in two steps. The
//! [`Sum`](gandr_theory_discrete_morse::Sum) of the reductions of each family
//! comes first. [`TemplateFold`] comes second: it folds the member templates'
//! carriers into one template of templates, and it collapses a member's row
//! onto that row together with its template's row there. The fold of
//! templates pays only where it has more member templates than its own size,
//! so a smaller family of families keeps the sum alone.
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
use gandr_theory_discrete_morse::PartIndex;
use gandr_theory_discrete_morse::Reduction;
use gandr_theory_discrete_morse::Refusal;
use gandr_theory_discrete_morse::SumFault;
use gandr_theory_discrete_morse::Summand;

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
    /// The template that the family folds into, owned or borrowed.
    template: Cow<'family, GuardedTemplate<A>>,
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
    /// A row of a member template, with that template's row in a template of
    /// templates.
    Nested
    {
        /// The member template's row in the template of templates.
        outer: TemplateRow,
        /// The member's row in its own template.
        inner: TemplateRow,
    },
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
    /// An inclusion or a retraction reads a row alone, and it received another
    /// composite.
    NotARow,
    /// An inclusion or a retraction of a fold of templates reads a row with
    /// its template's row alone, and it received another composite.
    NotNested,
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
            Cow::Owned(anti_unify_tracelets(family, store, cache)?),
            family,
        ))
    }

    /// Read `family` against `template`, owned or borrowed, wherever the
    /// template comes from: the replay decides whether it reduces the family.
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
        template: Cow<'family, GuardedTemplate<A>>,
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
    pub fn template(&self) -> &GuardedTemplate<A>
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
    pub fn size(&self) -> NodeCount
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
            Folded::Row(_) | Folded::Nested { .. } => Err(refused(FoldFault::NotAMember)),
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
            Folded::Member(_) | Folded::Nested { .. } => Err(refused(FoldFault::NotARow)),
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
            Folded::Row(_) | Folded::Nested { .. } => Err(refused(FoldFault::NotAMember)),
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
            Folded::Member(_) | Folded::Nested { .. } => Err(refused(FoldFault::NotARow)),
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
        for (index, member) in self.family.iter().enumerate() {
            let cell = MemberIndex::from(index);
            match rebuilt(&self.template, member).map_err(obstructed)? {
                Rebuilt::Same => {},
                Rebuilt::Forged => return Err(Refusal::Forged(cell)),
                Rebuilt::Unretracted => return Err(Refusal::Unretracted(cell)),
            }
        }
        Ok(())
    }
}

/// How a certificate stands against the instance of its own row.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Rebuilt
{
    /// The instance is the certificate.
    Same,
    /// The instance gives the row back, and it differs from the certificate.
    Forged,
    /// The instance's peak gives another row.
    Unretracted,
}

/// How `certificate` stands against the instance of its own row in
/// `template`. The check compares the certificate's skeleton with the
/// carrier's in place, and it rebuilds only the peak and the join.
///
/// # Specification
/// trivial.
///
/// # Errors
/// - each [`TemplateObstruction`]: the template does not read a peak or rebuild
///   a row.
fn rebuilt<A>(
    template: &GuardedTemplate<A>,
    certificate: &Tracelet<A>,
) -> Result<Rebuilt, TemplateObstruction>
where
    A: CellAlphabet,
{
    let row = template.row(&certificate.overlap.peak)?;
    let (peak, join) = template.boundary(&row)?;
    if peak != certificate.overlap.peak {
        return Ok(if template.row(&peak)? == row {
            Rebuilt::Forged
        }
        else {
            Rebuilt::Unretracted
        });
    }
    let carrier = template.carrier();
    let skeleton = carrier.path_a == certificate.path_a
        && carrier.path_b == certificate.path_b
        && carrier.overlap.left == certificate.overlap.left
        && carrier.overlap.right == certificate.overlap.right
        && carrier.overlap.kind == certificate.overlap.kind
        && carrier.overlap.unifier == certificate.overlap.unifier
        && carrier.overlap.seam == certificate.overlap.seam
        && carrier.overlap.right_renamed() == certificate.overlap.right_renamed();
    Ok(if skeleton && join == certificate.joins_at {
        Rebuilt::Same
    }
    else {
        Rebuilt::Forged
    })
}

/// A family of guarded templates folded into one template of templates: a
/// [`Reduction`] from the rows of each family's members onto those rows with
/// their templates' rows in the template of templates.
///
/// Its cells are the cells of the [`Sum`](gandr_theory_discrete_morse::Sum)
/// of the families' template reductions, so the two compose through
/// [`Reduction::then`]. The sum collapses each member onto its row, and the
/// fold of templates adds the row of the member's template.
#[derive(Debug)]
pub struct TemplateFold<'family, A: CellAlphabet>
{
    /// The template of templates: the fold of the member templates' carriers.
    template: GuardedTemplate<A>,
    /// The member templates, one for each part.
    templates: &'family [GuardedTemplate<A>],
    /// The families, one for each member template.
    families: &'family [&'family [Tracelet<A>]],
    /// Each member template's row in the template of templates, read once
    /// from its carrier's peak.
    outer: Vec<Result<TemplateRow, TemplateObstruction>>,
    /// One cell for each member of each family, in part order.
    cells: Vec<Summand<MemberIndex>>,
}

/// The refusal of a fold of templates for `fault` in the part at `part`.
///
/// # Specification
/// trivial.
const fn refused_in(
    part: PartIndex,
    fault: FoldFault,
) -> Refusal<Summand<MemberIndex>, SumFault<FoldFault>>
{
    Refusal::Morse(MorseError::Complex(SumFault::Part { part, fault }))
}

/// The refusal of a fold of templates for a part that it does not hold.
///
/// # Specification
/// trivial.
const fn absent(part: PartIndex) -> Refusal<Summand<MemberIndex>, SumFault<FoldFault>>
{
    Refusal::Morse(MorseError::Complex(SumFault::NoPart(part)))
}

impl<'family, A: CellAlphabet> TemplateFold<'family, A>
{
    /// Fold the carriers of `templates` into one template of templates, and
    /// read each of `families` against its template.
    ///
    /// # Specification
    /// - ensures: one cell for each member of each family, in part order and
    ///   then in family order, against the template that
    ///   [`anti_unify_tracelets`] gives for the carriers of `templates`.
    /// - fails: each [`TemplateRefusal`] of the fold of the carriers, by its
    ///   own name: [`TemplateRefusal::DoesNotPay`] where the template of
    ///   templates does not pay.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a family of families with one skeleton that pays
    ///   folds, and the two templates of two families keep
    ///   [`TemplateRefusal::DoesNotPay`]. The cell observer rejects a dropped
    ///   part, a dropped member and two parts in the other order.
    /// - witness: `tests::template::a_family_of_families_reduces_in_two_steps`
    /// - witness: `tests::template::two_families_keep_the_sum_alone`
    #[spec(ensures: |output| output.as_ref().ok().is_none_or(|fold| fold.cells.iter()
        .map(|cell| (usize::from(cell.part()), usize::from(*cell.value())))
        .eq(families.iter().enumerate().flat_map(|(part, family)|
            (0 .. family.len()).map(move |member| (part, member))))))]
    #[inline]
    pub fn fold(
        templates: &'family [GuardedTemplate<A>],
        families: &'family [&'family [Tracelet<A>]],
        store: &CellStore<A>,
        cache: &mut InheritanceCache,
    ) -> Result<Self, TemplateRefusal>
    {
        let carriers: Vec<&Tracelet<A>> = templates.iter().map(GuardedTemplate::carrier).collect();
        Ok(Self::over(
            anti_unify_tracelets(&carriers, store, cache)?,
            templates,
            families,
        ))
    }

    /// Read `families` against `templates`, and the templates against the
    /// template of templates `template`, wherever it comes from: the replay
    /// decides whether it reduces them.
    ///
    /// # Specification
    /// - ensures: one cell for each member of each family, in part order and
    ///   then in family order.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the template of templates of an honest family of
    ///   families read against the templates of another. The cell observer
    ///   rejects a dropped part, a dropped member and two parts in the other
    ///   order.
    /// - witness: `tests::template::a_carrier_unlike_its_instance_is_refused_at_its_part`
    #[spec(ensures: |output| output.cells.iter()
        .map(|cell| (usize::from(cell.part()), usize::from(*cell.value())))
        .eq(families.iter().enumerate().flat_map(|(part, family)|
            (0 .. family.len()).map(move |member| (part, member)))))]
    #[inline]
    #[must_use]
    pub fn over(
        template: GuardedTemplate<A>,
        templates: &'family [GuardedTemplate<A>],
        families: &'family [&'family [Tracelet<A>]],
    ) -> Self
    {
        let cells = families
            .iter()
            .enumerate()
            .flat_map(|(part, family)| {
                let at = PartIndex::from(part);
                (0 .. family.len()).map(move |member| Summand::new(at, MemberIndex::from(member)))
            })
            .collect();
        let outer = templates
            .iter()
            .map(|member| template.row(&member.carrier().overlap.peak))
            .collect();
        Self {
            template,
            templates,
            families,
            outer,
            cells,
        }
    }

    /// The template of templates.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn template(&self) -> &GuardedTemplate<A>
    {
        &self.template
    }

    /// The size of the target: the size `s` of the template of templates.
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

impl<'family, A: CellAlphabet> Reduction for TemplateFold<'family, A>
{
    type Cell = Summand<MemberIndex>;
    type Composite = Summand<Folded<'family, A>>;
    type Fault = SumFault<FoldFault>;
    type Witness = Summand<Identity>;

    /// The members of each family, in part order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn source(&self) -> &[Self::Cell]
    {
        &self.cells
    }

    /// The members of each family again: each keeps its row, with its
    /// template's row, in the target.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn target(&self) -> &[Self::Cell]
    {
        &self.cells
    }

    /// The row that the member's own template gives for it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn generator(
        &mut self,
        cell: &Self::Cell,
    ) -> Answer<Self, Self::Composite>
    {
        let part = cell.part();
        let at = usize::from(part);
        let (Some(template), Some(family)) = (self.templates.get(at), self.families.get(at))
        else {
            return Err(absent(part));
        };
        let member = family
            .get(usize::from(*cell.value()))
            .ok_or_else(|| refused_in(part, FoldFault::NoMember(*cell.value())))?;
        template
            .row(&member.overlap.peak)
            .map(|row| Summand::new(part, Folded::Row(row)))
            .map_err(|obstruction| refused_in(part, FoldFault::Obstruction(obstruction)))
    }

    /// The member's row, with its template's row in the template of
    /// templates.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn collapse(
        &mut self,
        composite: &Self::Composite,
    ) -> Answer<Self, Self::Composite>
    {
        let part = composite.part();
        let Folded::Row(ref inner) = *composite.value()
        else {
            return Err(refused_in(part, FoldFault::NotARow));
        };
        let outer = self
            .outer
            .get(usize::from(part))
            .ok_or_else(|| absent(part))?
            .clone()
            .map_err(|obstruction| refused_in(part, FoldFault::Obstruction(obstruction)))?;
        Ok(Summand::new(part, Folded::Nested {
            outer,
            inner: inner.clone(),
        }))
    }

    /// The member's row alone.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn include(
        &mut self,
        composite: &Self::Composite,
    ) -> Answer<Self, Self::Composite>
    {
        let part = composite.part();
        match *composite.value() {
            Folded::Nested { ref inner, .. } => Ok(Summand::new(part, Folded::Row(inner.clone()))),
            Folded::Member(_) | Folded::Row(_) => Err(refused_in(part, FoldFault::NotNested)),
        }
    }

    /// The identity from a row to its inclusion after its collapse, which
    /// closes only when the two are equal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn section(
        &mut self,
        composite: &Self::Composite,
    ) -> Answer<Self, Option<Self::Witness>>
    {
        let part = composite.part();
        match *composite.value() {
            Folded::Row(_) => Ok(Some(Summand::new(part, Identity))),
            Folded::Member(_) | Folded::Nested { .. } => Err(refused_in(part, FoldFault::NotARow)),
        }
    }

    /// None: the replay checks that the collapse gives each row back after the
    /// inclusion.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn retraction(
        &mut self,
        composite: &Self::Composite,
    ) -> Answer<Self, Option<Self::Witness>>
    {
        match *composite.value() {
            Folded::Nested { .. } => Ok(None),
            Folded::Member(_) | Folded::Row(_) => {
                Err(refused_in(composite.part(), FoldFault::NotNested))
            },
        }
    }

    /// The identity in its own part: it holds no cell to carry.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn include_witness(
        &mut self,
        witness: &Self::Witness,
    ) -> Answer<Self, Self::Witness>
    {
        Ok(*witness)
    }

    /// The identity in its own part: it holds no cell to carry.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn collapse_witness(
        &mut self,
        witness: &Self::Witness,
    ) -> Answer<Self, Self::Witness>
    {
        Ok(*witness)
    }

    /// The identity in the witnesses' part. Two witnesses of two parts do not
    /// compose.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn compose(
        &mut self,
        first: &Self::Witness,
        second: &Self::Witness,
    ) -> Answer<Self, Self::Witness>
    {
        if first.part() == second.part() {
            Ok(*first)
        }
        else {
            Err(Refusal::Morse(MorseError::Complex(SumFault::Apart {
                first: first.part(),
                second: second.part(),
            })))
        }
    }

    /// Whether `source` and `target` are equal, part and all.
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

    /// Check each member template in part order: its carrier gives a row of
    /// the template of templates, and the instance of that row is the
    /// carrier. The members of each family are the sum's to check.
    ///
    /// # Specification
    /// - ensures: `Ok` exactly when the fold holds one template for each
    ///   family, and each carrier equals the instance of its own row.
    /// - fails: a count of templates unlike the count of families as
    ///   [`Refusal::Unmatched`] with no cell. Then the first carrier that
    ///   fails, at its part's first member: an obstruction as
    ///   [`Refusal::Morse`], a row that the round trip moves as
    ///   [`Refusal::Unretracted`], and an instance that differs from its
    ///   carrier as [`Refusal::Forged`].
    /// - panics: none.
    /// - executable: none — the body is the predicate.
    /// - intension: one match of a peak and one fold of a row into the peak and
    ///   the join of the template of templates for each member template, with a
    ///   second match only where the rebuilt peak differs.
    ///
    /// # Errors
    /// - [`Refusal::Unmatched`]: the counts of templates and families differ.
    /// - [`Refusal::Morse`]: the template of templates does not read a
    ///   carrier's peak or rebuild a row.
    /// - [`Refusal::Unretracted`]: an instance's peak gives another row.
    /// - [`Refusal::Forged`]: an instance differs from its carrier.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — the family of families that pays replays; L3 — a
    ///   template of templates read against templates whose carriers it does
    ///   not give is refused at the first such part.
    /// - witness: `tests::template::a_family_of_families_reduces_in_two_steps`
    /// - witness: `tests::template::a_carrier_unlike_its_instance_is_refused_at_its_part`
    #[inline]
    fn replay(&mut self) -> Answer<Self, ()>
    {
        if self.templates.len() != self.families.len() {
            return Err(Refusal::Unmatched(None));
        }
        for (index, member) in self.templates.iter().enumerate() {
            let part = PartIndex::from(index);
            let cell = Summand::new(part, MemberIndex::from(0_usize));
            match rebuilt(&self.template, member.carrier())
                .map_err(|obstruction| refused_in(part, FoldFault::Obstruction(obstruction)))?
            {
                Rebuilt::Same => {},
                Rebuilt::Forged => return Err(Refusal::Forged(cell)),
                Rebuilt::Unretracted => return Err(Refusal::Unretracted(cell)),
            }
        }
        Ok(())
    }
}
