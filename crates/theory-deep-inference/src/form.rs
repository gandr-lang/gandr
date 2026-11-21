//! The guarded form: a template that reads each member of a family as a row,
//! and rebuilds an instance from each row.
//!
//! A guarded form holds the part that the members of a family share, one
//! entry for each point where they differ, and one guarded arm for each body
//! at an entry. Four operations read a family against it: the member at a
//! cell, the row of a certificate, the instance of a row, and whether an
//! instance is its member. [`TemplateReduction`](crate::TemplateReduction)
//! reads these four and no other, so it reduces every guarded form onto its
//! rows alike.
//!
//! A form is a stateless marker type, as a cell alphabet is: each operation is
//! an associated function over the form's template. Each cell alphabet `A` is
//! a guarded form whose template is [`GuardedTemplate<A>`] and whose members
//! are tracelets. A form outside this crate holds its own template and its own
//! members, and reads no cell operation.
//!
//! # References
//!
//! - `Barrett-2025-proof_compression_subatomic_logic_guarded_substitutions` —
//!   exemplar: Definition 37 states a superposition and its projections by
//!   guarded substitutions. A guarded form is the superposition, and a row is
//!   the guarded substitution that projects one member.
//! - `vault:01a12723-951b-7183-87d8-4fbc83c6a779` — anchor: a row is one guard
//!   for each point of the template, as [`TemplateRow`] holds it.

use gandr_theory_cell_complexes::CellAlphabet;
use gandr_theory_coherent_resolutions::Tracelet;
use gandr_theory_discrete_morse::Closure;

use crate::template::GuardedTemplate;
use crate::template::TemplateObstruction;
use crate::template::TemplateRow;

/// A certificate whose row a guarded form reads: a member of a family, or an
/// instance that the form rebuilt, read at its peak.
#[derive(Debug)]
pub enum RowOf<'read, F: GuardedForm>
{
    /// A member of a family.
    Member(&'read F::Member),
    /// The peak of an instance that the form rebuilt.
    Instance(&'read F::End),
}

/// The guarded form of a family: the template that the members share, read
/// as rows.
///
/// # Specification
/// - requires: an implementor gives one guard for each entry of the template as
///   the row of a certificate, in entry order; it gives the template's skeleton
///   with the arms of a row in place as the instance of the row; and it closes
///   a member against an instance exactly when the two are equal.
/// - ensures: a reduction generic over the trait reads a family through these
///   operations alone, and it reads every decline as data, never a panic.
/// - panics: none.
/// - executable: none — a type-level block: the trait states laws of every
///   inhabitant, and its declarations have no bodies.
///
/// # Adequacy
/// - hypothesis: L1 — every tracelet family that the template tests fold
///   replays as a reduction over the alphabet's form; L3 — a member whose join
///   its arms do not give is refused as forged, and a member of another shape
///   by the template's obstruction. A staging family replays as a reduction
///   over the checker's form, and the checker's suite witnesses that form.
/// - witness: `tests::template::every_folded_family_replays_as_a_reduction`
/// - witness: `tests::template::a_member_unlike_its_instance_is_refused_by_name`
pub trait GuardedForm: Copy + Eq + core::fmt::Debug
{
    /// The template: the part that the members share, with its entries and
    /// its arms.
    type Template: Clone + core::fmt::Debug;
    /// A member of a family. A family holds one member at each cell.
    type Member: Clone + Eq + core::fmt::Debug;
    /// One end of an instance that the template rebuilds: its peak or its
    /// join.
    type End: Clone + Eq + core::fmt::Debug;
    /// Why the template does not read a certificate or rebuild a row.
    type Obstruction: Clone + Copy + Eq + core::fmt::Debug;

    /// The row of `certificate`: the guard of the arm that it holds at each
    /// entry of `template`, in entry order.
    ///
    /// # Specification
    /// - ensures: one guard for each entry of `template`, read from the
    ///   certificate's peak with no copy of its body.
    /// - fails: the template's obstruction where the certificate's peak is no
    ///   instance of the template's peak, or holds a body that no arm holds.
    /// - panics: none.
    /// - executable: none — a type-level block: a required method has no body
    ///   of its own, and each implementation states its own checks.
    ///
    /// # Errors
    /// - each `Obstruction`: the template does not read the certificate.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the trait: a member whose peak no arm reads is
    ///   refused by the template's obstruction.
    /// - declaration-only: the obligation is each implementation's row; the
    ///   trait has no body to witness.
    fn row(
        template: &Self::Template,
        certificate: RowOf<'_, Self>,
    ) -> Result<TemplateRow, Self::Obstruction>;

    /// The instance of `row` in `template`: the template's skeleton with the
    /// arm of each guard in place, held as its peak and its join.
    ///
    /// # Specification
    /// - ensures: the peak and the join of the instance, each with the arms of
    ///   `row` in place.
    /// - fails: the template's obstruction where `row` names no arm at an
    ///   entry, or holds another count of guards than the template's entries.
    /// - panics: none.
    /// - executable: none — a type-level block: a required method has no body
    ///   of its own, and each implementation states its own checks.
    ///
    /// # Errors
    /// - each `Obstruction`: the template does not rebuild the row.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the trait: the instance of a member's row gives
    ///   the row back.
    /// - declaration-only: the obligation is each implementation's instance;
    ///   the trait has no body to witness.
    fn instance(
        template: &Self::Template,
        row: &TemplateRow,
    ) -> Result<(Self::End, Self::End), Self::Obstruction>;

    /// Whether `member` is the instance whose peak is `peak` and whose join is
    /// `join`, read against `template`'s skeleton in place.
    ///
    /// # Specification
    /// - ensures: [`Closure::Closes`] exactly when the member equals the
    ///   instance; [`Closure::Open`] otherwise.
    /// - fails: the template's obstruction where it does not read the instance.
    /// - panics: none.
    /// - executable: none — a type-level block: a required method has no body
    ///   of its own, and each implementation states its own checks.
    ///
    /// # Errors
    /// - each `Obstruction`: the template does not read the instance.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the trait: a member whose join its arms do not
    ///   give holds no instance.
    /// - declaration-only: the obligation is each implementation's check; the
    ///   trait has no body to witness.
    fn holds(
        template: &Self::Template,
        member: &Self::Member,
        peak: &Self::End,
        join: &Self::End,
    ) -> Result<Closure, Self::Obstruction>;
}

impl<A: CellAlphabet> GuardedForm for A
{
    type End = A::Cmd;
    type Member = Tracelet<A>;
    type Obstruction = TemplateObstruction;
    type Template = GuardedTemplate<A>;

    /// The row that the certificate's peak gives.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn row(
        template: &Self::Template,
        certificate: RowOf<'_, Self>,
    ) -> Result<TemplateRow, Self::Obstruction>
    {
        match certificate {
            RowOf::Member(member) => template.row(&member.overlap.peak),
            RowOf::Instance(peak) => template.row(peak),
        }
    }

    /// The peak and the join of the instance, with the arms in place in the
    /// carrier's.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn instance(
        template: &Self::Template,
        row: &TemplateRow,
    ) -> Result<(Self::End, Self::End), Self::Obstruction>
    {
        template.boundary(row)
    }

    /// Whether the member has the instance's peak and join and the carrier's
    /// skeleton.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn holds(
        template: &Self::Template,
        member: &Self::Member,
        peak: &Self::End,
        join: &Self::End,
    ) -> Result<Closure, Self::Obstruction>
    {
        Ok(
            if member.overlap.peak == *peak && member.joins_at == *join {
                same_skeleton(template.carrier(), member)
            }
            else {
                Closure::Open
            },
        )
    }
}

/// The identity between `certificate` and the skeleton of `carrier`: it
/// closes when their paths are equal and their overlaps are equal but the peak.
///
/// # Specification
/// trivial.
fn same_skeleton<A>(
    carrier: &Tracelet<A>,
    certificate: &Tracelet<A>,
) -> Closure
where
    A: CellAlphabet,
{
    if carrier.path_a == certificate.path_a
        && carrier.path_b == certificate.path_b
        && carrier.overlap.left == certificate.overlap.left
        && carrier.overlap.right == certificate.overlap.right
        && carrier.overlap.kind == certificate.overlap.kind
        && carrier.overlap.unifier == certificate.overlap.unifier
        && carrier.overlap.seam == certificate.overlap.seam
        && carrier.overlap.right_renamed() == certificate.overlap.right_renamed()
    {
        Closure::Closes
    }
    else {
        Closure::Open
    }
}
