//! The staging template as a guarded form, read in place over the arena that
//! holds its members.
//!
//! A staging member is a step whose sides are arena terms. [`Staging`] reads a
//! member against a template's graph with no import: a pattern node and an
//! arena term compare head by head, and a classifier compares by its structure
//! across the two vocabularies. The row of a member is the guard of the arm
//! that its source holds at each entry. An instance is a side of the template
//! with an arm in place at each point, held as the side's root and the arms,
//! so the form builds no instance arena. A member holds its instance when its
//! decision is the template's and each of its sides reads as the instance's
//! side in place.
//!
//! The analysis's candidate and the produced template both read through
//! [`Bound`], so the producer's rows and the admission's peak substitution use
//! one matcher.

use alloc::collections::BTreeSet;
use alloc::rc::Rc;
use alloc::vec::Vec;
use core::marker::PhantomData;

use anodized::spec;
use gandr_kernel_term::stage::Arena;
use gandr_kernel_term::stage::Child;
use gandr_kernel_term::stage::Rule;
use gandr_kernel_term::stage::StageError;
use gandr_kernel_term::stage::Step;
use gandr_kernel_term::stage::TermId;
use gandr_theory_deep_inference::Closure;
use gandr_theory_deep_inference::GuardId;
use gandr_theory_deep_inference::GuardedForm;
use gandr_theory_deep_inference::RowOf;
use gandr_theory_deep_inference::TemplateRow;

use super::Entry;
use super::Graph;
use super::Head;
use super::Id;

/// The guarded form of a staging template over the arena that holds its
/// members.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(super) struct Staging<'family>(PhantomData<&'family Arena>);

/// A staging template's graph, sides, decision and entries, bound to the
/// arena that holds the members it reads.
#[derive(Clone, Copy, Debug)]
pub(super) struct Bound<'family>
{
    /// The pattern syntax and its arms.
    graph: &'family Graph,
    /// The generalized source and target.
    sides: [Id; 2],
    /// The shared decision.
    rule: Rule,
    /// The guard partition at each point, in point order.
    entries: &'family [Entry],
    /// The arena that holds the members.
    arena: &'family Arena,
}

/// One side of an instance: the template's side, with the arm at each point
/// that `arms` holds in point order.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct Side
{
    /// The root of the template's side.
    root: Id,
    /// The arm at each point, shared by the two sides of one instance.
    arms: Rc<[Id]>,
}

impl<'family> Bound<'family>
{
    /// Bind a template's parts to the arena that holds its members.
    ///
    /// # Specification
    /// trivial.
    pub(super) const fn of(
        graph: &'family Graph,
        sides: [Id; 2],
        rule: Rule,
        entries: &'family [Entry],
        arena: &'family Arena,
    ) -> Self
    {
        Self {
            graph,
            sides,
            rule,
            entries,
            arena,
        }
    }

    /// The arm that `source` holds at each entry, in point order, read in
    /// place.
    ///
    /// # Specification
    /// - ensures: one arm for each entry, each an arm of that entry whose
    ///   content is the source's body at every occurrence of the point.
    /// - fails: `InvalidCertificate` on a rigid mismatch, a body that no arm
    ///   holds or two bodies at one point; malformed graph or arena lookups.
    /// - panics: none.
    /// - intension: one visit of each distinct pattern node and arena term
    ///   pair; no import and no copy of the member.
    ///
    /// # Errors
    /// Returns `StageError::InvalidCertificate`, `StageError::Unbalanced` or
    /// the arena's lookup errors.
    ///
    /// # Adequacy
    /// - hypothesis: L2/L3 — every harvested member admits under its arms, and
    ///   a conflicting repeated point or a near miss is refused.
    /// - witness: `template::tests::every_member_admits_as_its_plain_replay`
    /// - witness: `template::tests::peak_choices_are_correlated`
    /// - witness: `template::tests::member_selection_and_complete_replay_reject_near_misses`
    #[spec(ensures: |output| output.as_ref().ok().is_none_or(|arms| arms.len() == self.entries.len()
        && arms.iter().zip(self.entries).all(|(arm, entry)| entry.arms.contains_key(arm))))]
    pub(super) fn arms(
        &self,
        source: TermId,
    ) -> Result<Vec<Id>, StageError>
    {
        let [peak, _] = self.sides;
        let mut chosen: Vec<Option<Id>> = alloc::vec![None; self.entries.len()];
        let mut pending = Vec::new();
        let mut seen = BTreeSet::new();
        let mut next = Some((peak, source));
        while let Some((pattern, term)) = next.take().or_else(|| pending.pop()) {
            let node = self.graph.node(pattern)?;
            let shared =
                node.children.0.iter().any(Option::is_some) || matches!(node.head, Head::Point(_));
            if shared && !seen.insert((pattern, term)) {
                continue;
            }
            if let Head::Point(point) = node.head {
                let entry = self
                    .entries
                    .get(usize::from(point))
                    .ok_or(StageError::Unbalanced)?;
                let mut selected = None;
                for arm in entry.arms.keys() {
                    match self.graph.reads(*arm, &[], self.arena, term) {
                        Ok(()) => {
                            selected = Some(*arm);
                            break;
                        },
                        Err(StageError::InvalidCertificate) => {},
                        Err(error) => return Err(error),
                    }
                }
                let selected = selected.ok_or(StageError::InvalidCertificate)?;
                let slot = chosen
                    .get_mut(usize::from(point))
                    .ok_or(StageError::Unbalanced)?;
                if slot.replace(selected).is_some_and(|old| old != selected) {
                    return Err(StageError::InvalidCertificate);
                }
                continue;
            }
            let actual = self.arena.term(term)?;
            self.graph.same_head(node.head, self.arena, actual)?;
            for pair in node.children.0.into_iter().zip(actual.children()) {
                match pair {
                    (Some(child), Child::Present(slot)) => {
                        if next.is_none() {
                            next = Some((child, slot));
                        }
                        else {
                            pending.push((child, slot));
                        }
                    },
                    (None, Child::Vacant) => {},
                    (Some(_), Child::Vacant) | (None, Child::Present(_)) => {
                        return Err(StageError::InvalidCertificate);
                    },
                }
            }
        }
        chosen
            .into_iter()
            .map(|arm| arm.ok_or(StageError::InvalidCertificate))
            .collect()
    }

    /// The guard of each arm in `arms`, in point order.
    ///
    /// # Specification
    /// - ensures: one guard for each entry: the guard of the entry's arm.
    /// - fails: `InvalidCertificate` when `arms` holds another count than the
    ///   entries, or an arm that its entry does not hold.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `StageError::InvalidCertificate`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the row of each harvested member is the row that the
    ///   analysis generalized, guard for guard.
    /// - witness: `template::tests::a_staging_member_holds_the_instance_of_its_row`
    #[spec(ensures: |output| output.as_ref().ok().is_none_or(|guards| guards.len() == self.entries.len()))]
    fn guards(
        &self,
        arms: &[Id],
    ) -> Result<Vec<GuardId>, StageError>
    {
        if arms.len() != self.entries.len() {
            return Err(StageError::InvalidCertificate);
        }
        self.entries
            .iter()
            .zip(arms)
            .map(|(entry, arm)| {
                entry
                    .arms
                    .get(arm)
                    .copied()
                    .ok_or(StageError::InvalidCertificate)
            })
            .collect()
    }
}

impl<'family> GuardedForm for Staging<'family>
{
    type End = Side;
    type Member = Step;
    type Obstruction = StageError;
    type Template = Bound<'family>;

    /// The guards of the arms that the member's source holds, or that the
    /// instance's peak holds.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn row(
        template: &Self::Template,
        certificate: RowOf<'_, Self>,
    ) -> Result<TemplateRow, Self::Obstruction>
    {
        let [peak, _] = template.sides;
        let guards = match certificate {
            RowOf::Member(member) => template.guards(&template.arms(member.source)?)?,
            RowOf::Instance(side) if side.root == peak => template.guards(&side.arms)?,
            RowOf::Instance(_) => return Err(StageError::InvalidCertificate),
        };
        Ok(TemplateRow::from(guards))
    }

    /// The template's sides with the arm of each guard in place, sharing one
    /// list of arms.
    ///
    /// # Specification
    /// - ensures: the peak's root and the join's root are the template's sides,
    ///   and the arm at each point holds the row's guard there.
    /// - fails: `InvalidCertificate` when the row holds another count than the
    ///   entries, or a guard that its entry does not hold.
    /// - panics: none.
    /// - intension: one allocation holds the arms of both sides.
    ///
    /// # Errors
    /// Returns `StageError::InvalidCertificate`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the instance of each harvested member's row holds the
    ///   member, and its peak gives the row back.
    /// - witness: `template::tests::a_staging_member_holds_the_instance_of_its_row`
    #[spec(ensures: |output| output.as_ref().ok().is_none_or(|ends|
        [ends.0.root, ends.1.root] == template.sides && ends.0.arms == ends.1.arms
            && ends.0.arms.len() == template.entries.len()))]
    #[inline]
    fn instance(
        template: &Self::Template,
        row: &TemplateRow,
    ) -> Result<(Self::End, Self::End), Self::Obstruction>
    {
        let guards = row.guards();
        if guards.len() != template.entries.len() {
            return Err(StageError::InvalidCertificate);
        }
        let arms = template
            .entries
            .iter()
            .zip(guards)
            .map(|(entry, guard)| {
                entry
                    .arms
                    .iter()
                    .find_map(|(arm, held)| (held == guard).then_some(*arm))
                    .ok_or(StageError::InvalidCertificate)
            })
            .collect::<Result<Rc<[Id]>, _>>()?;
        let [peak, join] = template.sides;
        Ok((
            Side {
                root: peak,
                arms: Rc::clone(&arms),
            },
            Side { root: join, arms },
        ))
    }

    /// Whether the member's decision is the template's and each of its sides
    /// reads as the instance's side, in place.
    ///
    /// # Specification
    /// - ensures: [`Closure::Closes`] exactly when the member's rule is the
    ///   template's, the ends are the template's sides, and the member's source
    ///   and target read as the peak and the join with their arms in place.
    /// - fails: malformed graph or arena lookups.
    /// - panics: none.
    /// - executable: none — the predicate is the in-place comparison of two
    ///   syntax trees, and a runtime check would repeat that comparison.
    /// - intension: one visit of each distinct pattern node and arena term
    ///   pair; no instance arena and no copy of the member.
    ///
    /// # Errors
    /// Returns `StageError::Unbalanced` or the arena's lookup errors.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each harvested member holds the instance of its row,
    ///   and a member whose target its arms do not give holds none.
    /// - witness: `template::tests::a_staging_member_holds_the_instance_of_its_row`
    #[inline]
    fn holds(
        template: &Self::Template,
        member: &Self::Member,
        peak: &Self::End,
        join: &Self::End,
    ) -> Result<Closure, Self::Obstruction>
    {
        if member.rule != template.rule || [peak.root, join.root] != template.sides {
            return Ok(Closure::Open);
        }
        for (side, term) in [(peak, member.source), (join, member.target)] {
            match template
                .graph
                .reads(side.root, &side.arms, template.arena, term)
            {
                Ok(()) => {},
                Err(StageError::InvalidCertificate) => return Ok(Closure::Open),
                Err(error) => return Err(error),
            }
        }
        Ok(Closure::Closes)
    }
}
