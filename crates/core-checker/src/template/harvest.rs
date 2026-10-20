//! Group equations by producer identity and shallow decision shape.
//!
//! A program's equations are grouped one certificate at a time: a
//! [`Grouping`] reads one certificate's steps in the arena that holds them,
//! and a [`Harvest`] joins groupings in certificate order into the program's
//! families. A grouping names no coordinate, so a certificate may be grouped
//! where it was normalized and its steps joined after they move into the
//! program's arena.

use alloc::vec::Vec;
use core::mem::Discriminant;

use anodized::spec;
use gandr_kernel_term::stage::Arena;
use gandr_kernel_term::stage::Certificate;
use gandr_kernel_term::stage::Child;
use gandr_kernel_term::stage::Rule;
use gandr_kernel_term::stage::StageError;
use gandr_kernel_term::stage::Step;
use gandr_kernel_term::stage::Term;
use gandr_kernel_term::stage::TermId;

use super::ProgramId;

/// A constructor-only shallow signature: the root's constructor and each
/// child slot's, in constructor order; payloads remain anti-unification's job.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Shape
{
    /// The root's constructor.
    root: Discriminant<Term>,
    /// Each child slot's constructor; a slot the root leaves vacant has none.
    children: [Option<Discriminant<Term>>; 3],
}

/// What harvest groups a family by: its decision and its members' shallow
/// source shape, never its program.
///
/// # Specification
/// - provides: equality exactly when two families, from any programs, share
///   their rule and shallow source shape; the template memo's lookup key.
/// - panics: none.
/// - executable: none — a plain pair of private values with derived equality.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct FamilyKey
{
    /// The shared local decision.
    rule: Rule,
    /// The shared shallow source shape.
    shape: Shape,
}

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
    key: FamilyKey,
}

impl Family
{
    /// The key this family was harvested under.
    ///
    /// # Specification
    /// trivial.
    pub(super) const fn key(&self) -> &FamilyKey
    {
        &self.key
    }
}

/// Observe root and immediate child constructors without numeral payloads.
///
/// # Specification
/// - ensures: the root's tag, then a tag at exactly each child slot the root
///   occupies, in constructor order.
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
    arena.term(root).is_ok_and(|term| shape.root == core::mem::discriminant(&term)
        && shape.children.iter().zip(term.children()).all(|(tag, child)|
            tag.is_some() == matches!(child, Child::Present(_))))))]
fn shape(
    arena: &Arena,
    root: TermId,
) -> Result<Shape, StageError>
{
    let root = arena.term(root)?;
    let mut children = [None; 3];
    for (tag, child) in children.iter_mut().zip(root.children()) {
        if let Child::Present(child) = child {
            let child = arena.term(child)?;
            *tag = Some(core::mem::discriminant(&child));
        }
    }
    Ok(Shape {
        root: core::mem::discriminant(&root),
        children,
    })
}

/// A key's position among one certificate's distinct keys.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct GroupIndex(usize);

/// A family's position among a program's families.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct FamilyIndex(usize);

/// One certificate's equations grouped by decision and shallow source shape,
/// before they join a program's families.
///
/// # Specification
/// - provides: the certificate's distinct keys in first-occurrence order and,
///   for each step in order, its key's position among them. No coordinate is
///   retained, so the grouping holds wherever the certificate's terms move.
/// - panics: none.
/// - executable: none — [`Grouping::of`] checks the construction.
#[derive(Clone, Debug, Default)]
pub struct Grouping
{
    /// The distinct keys, in first-occurrence order.
    keys: Vec<FamilyKey>,
    /// Each step's key, by position in `keys`.
    steps: Vec<GroupIndex>,
}

impl Grouping
{
    /// Group one certificate's equations, reading their sources in `arena`.
    ///
    /// # Specification
    /// - ensures: one group position per step, each naming a key with the
    ///   step's rule; the keys are distinct and each first named by a step
    ///   after every key before it.
    /// - fails: malformed arena references while observing side constructors.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `StageError::UnknownTerm`.
    ///
    /// # Adequacy
    /// - hypothesis: L2/L3 — a program whose keys first occur in a later
    ///   certificate and interleave within one is harvested by certificate and
    ///   compared with grouping its concatenated steps at once, so a dropped,
    ///   merged or reordered key or member changes the families.
    /// - witness: `template::tests::grouping_by_certificate_keeps_first_occurrence_and_member_order`
    /// - witness: `template::tests::empty_and_malformed_families_preserve_refusals`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            linear_search_in_loop,
            reason = "bounded: a key is one of the seven rules with a shallow shape of four term constructors, a set the stage calculus fixes; a `Discriminant` has no order to key a map by and the crate takes no hasher"
        )
    )]
    #[spec(ensures: |output| output.as_ref().ok().is_none_or(|grouping|
        grouping.steps.len() == certificate.steps.len()
            && certificate.steps.iter().zip(&grouping.steps).all(|(step, group)|
                grouping.keys.get(group.0).is_some_and(|key| key.rule == step.rule))
            && grouping.keys.iter().enumerate().all(|(index, key)|
                grouping.keys.iter().skip(index.saturating_add(1)).all(|later| later != key)
                    && grouping.steps.iter().position(|group| group.0 == index)
                        < grouping.steps.iter().position(|group| group.0 == index.saturating_add(1))
                            .or(Some(usize::MAX)))))]
    pub(crate) fn of(
        arena: &Arena,
        certificate: &Certificate,
    ) -> Result<Self, StageError>
    {
        let mut keys: Vec<FamilyKey> = Vec::new();
        let mut steps = Vec::with_capacity(certificate.steps.len());
        for step in &certificate.steps {
            let shape = shape(arena, step.source)?;
            let key = FamilyKey {
                rule: step.rule,
                shape,
            };
            let group = keys
                .iter()
                .position(|known| *known == key)
                .unwrap_or_else(|| {
                    keys.push(key);
                    keys.len().saturating_sub(1)
                });
            steps.push(GroupIndex(group));
        }
        Ok(Self { keys, steps })
    }
}

/// A program's families, gathered from its certificates' groupings in
/// certificate order.
///
/// # Specification
/// - provides: after every certificate is joined, exactly the families grouping
///   the program's concatenated equations at once would give.
/// - panics: none.
/// - executable: none — [`Harvest::join`] checks each step.
#[derive(Clone, Debug)]
pub struct Harvest
{
    /// The program every family belongs to.
    program: ProgramId,
    /// The families so far, in first-occurrence order.
    families: Vec<Family>,
    /// The family each key of the grouping being joined belongs to.
    joined: Vec<FamilyIndex>,
}

impl Harvest
{
    /// A harvest of `program` holding no family yet.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn new(program: ProgramId) -> Self
    {
        Self {
            program,
            families: Vec::new(),
            joined: Vec::new(),
        }
    }

    /// Join the next certificate: `steps` are its equations as `grouping`
    /// read them, in the coordinates the families are kept in.
    ///
    /// # Specification
    /// - requires: `grouping` was read from the certificate whose equations
    ///   `steps` are, in order.
    /// - ensures: each step joins the family of its key, at the end of its
    ///   members; a key no family holds yet opens one after every existing
    ///   family, in the grouping's first-occurrence order.
    /// - fails: `Unbalanced` when `steps` and the grouping differ in length,
    ///   with the families unchanged.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `StageError::Unbalanced`.
    ///
    /// # Adequacy
    /// - hypothesis: L2/L3 — certificates whose keys first occur late and
    ///   interleave, joined one by one, are compared with grouping their
    ///   concatenation, and a mismatched step list is refused.
    /// - witness: `template::tests::grouping_by_certificate_keeps_first_occurrence_and_member_order`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body searches the families once per key of the grouping; the check sums the families' member counts twice"
        )
    )]
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            linear_search_in_loop,
            reason = "bounded: a family is one of the seven rules with a shallow shape of four term constructors, a set the stage calculus fixes; a `Discriminant` has no order to key a map by and the crate takes no hasher"
        )
    )]
    #[spec(captures: [members = self.families.iter().map(|family| family.members.len()).sum::<usize>()],
        ensures: |output| match output {
            Ok(()) => self.families.iter().map(|family| family.members.len()).sum::<usize>()
                == members.saturating_add(steps.len()),
            Err(_) => self.families.iter().map(|family| family.members.len()).sum::<usize>() == members,
        })]
    pub(crate) fn join(
        &mut self,
        grouping: &Grouping,
        steps: &[Step],
    ) -> Result<(), StageError>
    {
        if steps.len() != grouping.steps.len() {
            return Err(StageError::Unbalanced);
        }
        self.joined.clear();
        for key in &grouping.keys {
            let family =
                if let Some(family) = self.families.iter().position(|family| family.key == *key) {
                    family
                }
                else {
                    self.families.push(Family {
                        program: self.program,
                        members: Vec::new(),
                        key: *key,
                    });
                    self.families.len().saturating_sub(1)
                };
            self.joined.push(FamilyIndex(family));
        }
        for (step, group) in steps.iter().zip(&grouping.steps) {
            let family = self.joined.get(group.0).ok_or(StageError::Unbalanced)?;
            let family = self
                .families
                .get_mut(family.0)
                .ok_or(StageError::Unbalanced)?;
            family.members.push(*step);
        }
        Ok(())
    }

    /// The families gathered, in first-occurrence order.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn finish(self) -> Vec<Family>
    {
        self.families
    }
}

/// Harvest every equation, partitioning by decision and shallow source shape.
///
/// # Specification
/// - ensures: every equation belongs to exactly one family of this program;
///   family order is first occurrence and member order is producer order.
/// - fails: malformed arena references while observing side constructors.
/// - panics: none.
/// - intension: grouping is discovery only; anti-unification and inheritance
///   still decide whether any grouped family admits a guarded template. Each
///   certificate is grouped alone and joined in order, as a forked program
///   groups each where it was normalized.
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
/// - witness: `template::tests::grouping_by_certificate_keeps_first_occurrence_and_member_order`
#[spec(ensures: |output| output.as_ref().ok().is_none_or(|families|
    families.iter().all(|family| family.program == program && !family.members.is_empty()
        && family.members.iter().all(|step| step.rule == family.key.rule))
        && families.iter().map(|family| family.members.len()).sum::<usize>()
            == certificates.iter().map(|certificate| certificate.steps.len()).sum::<usize>()))]
#[inline]
pub fn harvest(
    arena: &Arena,
    program: ProgramId,
    certificates: &[Certificate],
) -> Result<Vec<Family>, StageError>
{
    let mut harvest = Harvest::new(program);
    for certificate in certificates {
        let grouping = Grouping::of(arena, certificate)?;
        harvest.join(&grouping, &certificate.steps)?;
    }
    Ok(harvest.finish())
}
