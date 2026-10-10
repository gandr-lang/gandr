//! Group equations by producer identity and shallow decision shape.

use alloc::vec::Vec;
use core::mem::Discriminant;

use anodized::spec;
use gandr_kernel_term::stage::Arena;
use gandr_kernel_term::stage::Certificate;
use gandr_kernel_term::stage::Rule;
use gandr_kernel_term::stage::StageError;
use gandr_kernel_term::stage::Step;
use gandr_kernel_term::stage::Term;
use gandr_kernel_term::stage::TermId;

use super::ProgramId;

/// A constructor-only shallow signature; payloads remain anti-unification's
/// job.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
struct Shape(Vec<Discriminant<Term>>);

/// One recurring decision region from a single meta-program.
///
/// # Specification
/// - provides: equations grouped by one producer, rule and shallow source shape
///   at harvest. Public member edits remain untrusted input to analyze.
/// - panics: none.
/// - executable: none — harvest checks the grouping; the mutable member
///   collection cannot retain that invariant after arbitrary caller edits.
///
/// # Adequacy
/// - hypothesis: L3 — two producer identities and distinct local decisions
///   distinguish grouping by source from merging unrelated certificates.
/// - witness: `template::tests::families_keep_programs_and_decisions_separate`
#[derive(Clone, Debug)]
pub struct Family
{
    /// The explicit program identity, never inferred from similar syntax.
    pub program: ProgramId,
    /// Equations in producer order.
    pub members: Vec<Step>,
    /// Rule and source shape; the result never determines a family.
    key: (Rule, Shape),
}

/// Observe root and immediate child constructors without numeral payloads.
///
/// # Specification
/// - ensures: the root tag precedes its immediate child tags in constructor
///   order.
/// - fails: the arena's lookup error for malformed source syntax.
/// - panics: none.
///
/// # Errors
/// Returns `StageError::UnknownTerm`.
///
/// # Adequacy
/// - hypothesis: L3 — repeated cancellation instances group together while beta
///   and different surrounding constructors stay in different families.
/// - witness: `template::tests::families_keep_programs_and_decisions_separate`
#[spec(ensures: |output| output.as_ref().ok().is_none_or(|shape|
    arena.term(root).is_ok_and(|term| shape.0.first() == Some(&core::mem::discriminant(&term))
        && shape.0.len() == 1_usize.saturating_add(term.children().into_iter().flatten().count()))))]
fn shape(
    arena: &Arena,
    root: TermId,
) -> Result<Shape, StageError>
{
    let root = arena.term(root)?;
    let mut tags = Vec::with_capacity(4);
    tags.push(core::mem::discriminant(&root));
    for child in root.children().into_iter().flatten() {
        let child = arena.term(child)?;
        tags.push(core::mem::discriminant(&child));
    }
    Ok(Shape(tags))
}
/// Harvest every equation, partitioning by decision and shallow source shape.
///
/// # Specification
/// - ensures: every equation belongs to exactly one family of this program;
///   family order is first occurrence and member order is producer order.
/// - fails: malformed arena references while observing side constructors.
/// - panics: none.
/// - intension: grouping is discovery only; anti-unification and inheritance
///   still decide whether any grouped family admits a guarded template.
///
/// # Errors
/// Returns `StageError::UnknownTerm`.
///
/// # Adequacy
/// - hypothesis: L2/L3 — exact partition coverage, separate producer identities
///   and different decisions distinguish dropped, merged or duplicated
///   equations.
/// - witness: `template::tests::families_keep_programs_and_decisions_separate`
/// - witness: `template::tests::empty_and_malformed_families_preserve_refusals`
#[spec(ensures: |output| output.as_ref().ok().is_none_or(|families|
    families.iter().all(|family| family.program == program && !family.members.is_empty()
        && family.members.iter().all(|step| step.rule == family.key.0))
        && families.iter().map(|family| family.members.len()).sum::<usize>()
            == certificates.iter().map(|certificate| certificate.steps.len()).sum::<usize>()))]
#[inline]
pub fn harvest(
    arena: &Arena,
    program: ProgramId,
    certificates: &[Certificate],
) -> Result<Vec<Family>, StageError>
{
    let mut families: Vec<Family> = Vec::new();
    for step in certificates
        .iter()
        .flat_map(|certificate| &certificate.steps)
    {
        let source = shape(arena, step.source)?;
        let key = (step.rule, source);
        if let Some(family) = families.iter_mut().find(|family| family.key == key) {
            family.members.push(*step);
        }
        else {
            families.push(Family {
                program,
                members: Vec::from([*step]),
                key,
            });
        }
    }
    Ok(families)
}
