//! Guarded families of staging equations, with ordinary replay as authority.
//!
//! The family key is one producer program and one decision. Joint
//! anti-unification shares repeated columns across both sides. Pricing and the
//! inheritance cache are the same machinery used by tracelets. A declined
//! family stays plain. Congruence equations needing earlier premises stay in
//! the enclosing plain certificate unless their local inheritance replay
//! succeeds independently.
//!
//! `template::harvest` groups that producer's equations by program, decision
//! and shallow source shape. Joint anti-unification keeps peak choices
//! correlated; `template::produce` prices generalized sides, decisions and
//! guarded arms before replaying each distinct inheritance triple with the
//! other points rigid. Only `s < floor(F / s)` can emit a template. Admission
//! chooses arms from the member's peak and ordinary kernel replay remains
//! authoritative, even with a poisoned cache. Complete certificates retain
//! their original congruence premises.
//!
//! The peak-rooted representation retains no member list; one instance can be
//! materialized, replayed and dropped. Storing substitutions per member would
//! grow the template with the family. Source-only discovery avoids splitting
//! families by the answer they should prove; arithmetic relations between
//! varying literals are not inferred. Revisit that choice when a producer
//! supplies a checked parametric iteration schema. The `staging_templates`
//! release example reports strict power and double-product families separately
//! from repeated generated controls, including time, scoped heap high-water
//! marks and refusal reasons. Its module documentation specifies the allocator
//! choice and measurement limits.

mod harvest;
mod syntax;
pub use harvest::Family;
pub use harvest::harvest;
#[cfg(test)]
mod tests;

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use gandr_kernel_term::stage::Arena;
use gandr_kernel_term::stage::Budget;
use gandr_kernel_term::stage::Certificate;
use gandr_kernel_term::stage::Natural;
use gandr_kernel_term::stage::Rule;
use gandr_kernel_term::stage::Stage;
use gandr_kernel_term::stage::StageError;
use gandr_kernel_term::stage::Step;
use gandr_kernel_term::stage::Term;
use gandr_kernel_term::stage::TermId;
use gandr_kernel_term::stage::TypeId;
use gandr_theory_deep_inference::EntryIndex;
use gandr_theory_deep_inference::ExpansionFactor;
use gandr_theory_deep_inference::FamilyCostReport;
use gandr_theory_deep_inference::GuardId;
use gandr_theory_deep_inference::InheritanceCache;
use gandr_theory_deep_inference::InheritanceKey;
use gandr_theory_deep_inference::InheritanceVerdict;
use gandr_theory_deep_inference::MemberCount;
use gandr_theory_deep_inference::MemberIndex;
use gandr_theory_deep_inference::NodeCount;
use gandr_theory_deep_inference::ReplayStepCount;
use gandr_theory_deep_inference::TemplateAddress;
use gandr_theory_deep_inference::TemplateLeg;
use gandr_theory_deep_inference::TemplateRefusal;
use gandr_theory_deep_inference::inheritance_lookup;
use gandr_theory_deep_inference::price_family;
use quenchant_shape::shape::Maybe;
use syntax::Children;
use syntax::Graph;
use syntax::Head;
use syntax::Id;
use syntax::Node;

/// Producer identity within one readmission run; unrelated programs never
/// merge.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ProgramId(pub usize);

/// The member's choices, selected only by matching its own source.
#[repr(transparent)]
#[derive(Clone, Debug)]
pub struct Substitution(BTreeMap<EntryIndex, Id>);

/// One generalized point and its distinct guarded bodies.
#[derive(Clone, Debug)]
struct Entry
{
    /// Nominal variable at every occurrence of this column.
    point: EntryIndex,
    /// One nominal guard per exact body.
    arms: BTreeMap<Id, GuardId>,
}

/// A priced and inheritance-checked equation family, retaining no members.
#[derive(Clone, Debug)]
pub struct Template
{
    /// Only generalized sides and distinct arms remain resident.
    graph: Graph,
    /// Generalized source and target.
    sides: [Id; 2],
    /// Shared replay decision.
    rule: Rule,
    /// Guard partition at each point.
    entries: Vec<Entry>,
    /// The observed sizes and producer work.
    cost: FamilyCostReport,
}

/// A producer result; ordinary replay is selected whenever compression
/// declines.
#[derive(Clone, Debug)]
pub enum Production
{
    /// The family passed both price and inheritance.
    Go(Template),
    /// The family stays plain, with the measured price and exact refusal.
    Plain
    {
        /// The refusing gate.
        reason: TemplateRefusal,
        /// Measurements obtained before refusal.
        cost: FamilyCostReport,
    },
}

impl Production
{
    /// Return the same cost vocabulary for paying and declined families.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn cost(&self) -> FamilyCostReport
    {
        match *self {
            | Self::Go(ref template) => template.cost,
            | Self::Plain { cost, .. } => cost,
        }
    }
}

/// Work for a joint least general generalization.
struct Generalizer
{
    /// Exact syntax content and generalized nodes.
    graph: Graph,
    /// Equal columns must denote the same point on both sides.
    columns: BTreeMap<Vec<Id>, Id>,
    /// Distinct bodies for each introduced point.
    entries: Vec<Entry>,
    /// A point's body for each member; discarded after production.
    arms: Vec<Vec<Id>>,
}

impl Generalizer
{
    /// Generalize a column with an explicit worklist.
    ///
    /// # Specification
    /// - ensures: equal heads are retained; disagreeing heads become one point
    ///   per exact column, reused across all generalized sides.
    /// - fails: Unbalanced for empty columns or malformed graph edges.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `StageError::Unbalanced`.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — reconstruction of every member distinguishes lost
    ///   correlations, target-only points and unequal rigid payloads.
    /// - witness: `template::tests::every_member_admits_as_its_plain_replay`
    fn column(
        &mut self,
        column: Vec<Id>,
    ) -> Result<Id, StageError>
    {
        let root = column.clone();
        let mut pending = Vec::from([(column, false)]);
        while let Some((column, ready)) = pending.pop() {
            if self.columns.contains_key(&column) {
                continue;
            }
            let first = *column.first().ok_or(StageError::Unbalanced)?;
            if column.iter().all(|id| *id == first) {
                self.columns.insert(column, first);
                continue;
            }
            let nodes = column
                .iter()
                .map(|id| self.graph.node(*id))
                .collect::<Result<Vec<_>, _>>()?;
            let head = nodes.first().ok_or(StageError::Unbalanced)?.head;
            if !nodes.iter().all(|node| node.head == head) {
                let point = EntryIndex::from(self.entries.len());
                let arms = column
                    .iter()
                    .copied()
                    .collect::<BTreeSet<_>>()
                    .into_iter()
                    .enumerate()
                    .map(|(guard, id)| (id, GuardId::from(guard)))
                    .collect();
                let id = self.graph.intern(Node {
                    head: Head::Point(point),
                    children: Children([None; 3]),
                })?;
                self.entries.push(Entry { point, arms });
                self.arms.push(column.clone());
                self.columns.insert(column, id);
                continue;
            }
            let mut child_columns = Vec::new();
            for slot in 0 .. 3 {
                let child = nodes
                    .iter()
                    .filter_map(|node| node.children.0.get(slot).copied().flatten())
                    .collect::<Vec<_>>();
                if !child.is_empty() {
                    child_columns.push((slot, child));
                }
            }
            if !ready {
                pending.push((column, true));
                pending.extend(
                    child_columns
                        .into_iter()
                        .rev()
                        .map(|(_, child)| (child, false)),
                );
                continue;
            }
            let mut children = Children([None; 3]);
            for (slot, child) in child_columns {
                let id = *self.columns.get(&child).ok_or(StageError::Unbalanced)?;
                *children.0.get_mut(slot).ok_or(StageError::Unbalanced)? = Some(id);
            }
            let id = self.graph.intern(Node { head, children })?;
            self.columns.insert(column, id);
        }
        self.columns
            .get(&root)
            .copied()
            .ok_or(StageError::Unbalanced)
    }
}

/// Replay local equations using closed reflexive endpoints.
///
/// The kernel still checks every supplied equation. Reflexive endpoints avoid
/// imposing a fabricated typing context on equations recorded under binders;
/// complete readmission separately forms the real endpoints and their context.
///
/// # Specification
/// - ensures: success means the kernel checked every local equation; no cached
///   inheritance verdict or inferred type is accepted as equation authority.
/// - fails: the kernel's exact equation or budget refusal.
/// - panics: none.
///
/// # Errors
/// Propagates `StageError` from arena allocation and kernel replay.
///
/// # Adequacy
/// - hypothesis: L2/L3 — incorrect rule tags and discriminated points fail
///   despite the reflexive endpoint; honest beta and cancellation steps pass.
/// - witness: `template::tests::a_poisoned_inheritance_entry_is_caught_at_admission`
fn replay_equation(
    arena: &mut Arena,
    step: Step,
    budget: &mut Budget,
) -> Result<(), StageError>
{
    let endpoint = arena.alloc(Term::Natural(Stage::Outer, Natural(0)))?;
    let certificate = Certificate {
        source: endpoint,
        target: endpoint,
        steps: Vec::from([step]),
    };
    gandr_kernel_core::stage::replay(arena, &[], &certificate, budget)?;
    Ok(())
}

/// Rebuild one equation under selected points in an independent arena.
///
/// # Specification
/// - ensures: both sides use one graph export, preserving shared subterms.
/// - fails: malformed pattern dependencies or arena allocation errors.
/// - panics: none.
///
/// # Errors
/// Propagates `StageError`; Unbalanced if two roots are not returned.
///
/// # Adequacy
/// - hypothesis: L2 — projection is compared with independently replayed
///   inputs.
/// - witness: `template::tests::every_member_admits_as_its_plain_replay`
fn materialize(
    graph: &Graph,
    sides: [Id; 2],
    rule: Rule,
    bindings: &BTreeMap<EntryIndex, Id>,
) -> Result<(Arena, Step), StageError>
{
    let mut arena = Arena::default();
    let roots = graph.export(&mut arena, &sides, bindings)?;
    let mut roots = roots.into_iter();
    let source = roots.next().ok_or(StageError::Unbalanced)?;
    let target = roots.next().ok_or(StageError::Unbalanced)?;
    Ok((arena, Step {
        source,
        target,
        rule,
    }))
}

/// Anti-unify one program's equal-decision equation family, price, then replay.
///
/// # Specification
/// - ensures: Go has s < floor(F/s), every point occurs in the peak, and every
///   distinct region/point/body triple has an inherited verdict. No member map
///   or original certificate remains in an emitted template.
/// - ensures: a failed gate selects Plain, preserving its exact reason and
///   cost.
/// - fails: malformed input arena references or exhausted inheritance budget.
/// - panics: none.
/// - intension: pricing precedes all replay; cache checks are per distinct
///   triple.
///
/// # Errors
/// Propagates `StageError` from syntax import, materialization or budget
/// exhaustion.
///
/// # Adequacy
/// - hypothesis: L1/L2/L3 — independent sizes, plain replay, all three
///   adversarial classes and exact cache counts distinguish weakening any gate
///   clause.
/// - witness: `template::tests::a_template_is_emitted_only_below_its_expansion_factor`
/// - witness: `template::tests::every_member_admits_as_its_plain_replay`
/// - witness: `template::tests::a_skeleton_divergent_family_yields_no_template`
/// - witness: `template::tests::an_entry_a_decision_discriminates_on_yields_no_template`
/// - witness: `template::tests::a_family_with_no_shared_content_yields_no_template`
/// - witness: `template::tests::the_inheritance_check_runs_once_per_distinct_triple`
#[inline]
pub fn produce(
    arena: &Arena,
    program: ProgramId,
    family: &[Step],
    cache: &mut InheritanceCache,
    budget: &mut Budget,
) -> Result<Production, StageError>
{
    let mut cost = FamilyCostReport {
        members: MemberCount::from(family.len()),
        plain_replayed_steps: ReplayStepCount::from(family.len()),
        ..FamilyCostReport::default()
    };
    let Some(first) = family.first()
    else {
        return Ok(Production::Plain {
            reason: TemplateRefusal::EmptyFamily,
            cost,
        });
    };
    if let Some(member) = family.iter().position(|member| member.rule != first.rule) {
        return Ok(Production::Plain {
            reason: TemplateRefusal::SkeletonDivergence {
                member: MemberIndex::from(member),
            },
            cost,
        });
    }
    let mut generalizer = Generalizer {
        graph: Graph::default(),
        columns: BTreeMap::new(),
        entries: Vec::new(),
        arms: Vec::new(),
    };
    let roots = family
        .iter()
        .flat_map(|step| [step.source, step.target])
        .collect::<Vec<_>>();
    let roots = generalizer.graph.import(arena, &roots)?;
    let mut peaks = Vec::with_capacity(family.len());
    let mut joins = Vec::with_capacity(family.len());
    let mut plain = family.len();
    for pair in roots.chunks_exact(2) {
        let &[peak, join] = pair
        else {
            return Err(StageError::Unbalanced);
        };
        peaks.push(peak);
        joins.push(join);
        let peak_size = generalizer.graph.size(peak)?;
        let join_size = generalizer.graph.size(join)?;
        plain = plain
            .saturating_add(usize::from(peak_size))
            .saturating_add(usize::from(join_size));
    }
    cost.plain_size = NodeCount::from(plain);
    let peak = generalizer.column(peaks)?;
    let join = generalizer.column(joins)?;
    let sides = [peak, join];
    let mut points = BTreeSet::new();
    let mut seen = BTreeSet::new();
    let mut pending = Vec::from([peak]);
    while let Some(id) = pending.pop() {
        if !seen.insert(id) {
            continue;
        }
        let node = generalizer.graph.node(id)?;
        if let Head::Point(point) = node.head {
            points.insert(point);
        }
        pending.extend(node.children.0.into_iter().flatten());
    }
    let peak_size = generalizer.graph.size(peak)?;
    let join_size = generalizer.graph.size(join)?;
    let mut size = usize::from(peak_size)
        .saturating_add(usize::from(join_size))
        .saturating_add(1);
    for entry in &generalizer.entries {
        for arm in entry.arms.keys() {
            let arm_size = generalizer.graph.size(*arm)?;
            size = size.saturating_add(usize::from(arm_size)).saturating_add(1);
        }
    }
    cost.template_size = NodeCount::from(size);
    cost.expansion_factor = ExpansionFactor::from(plain.checked_div(size).unwrap_or_default());
    for entry in &generalizer.entries {
        if !points.contains(&entry.point) {
            return Ok(Production::Plain {
                reason: TemplateRefusal::EntryOutsidePeak { entry: entry.point },
                cost,
            });
        }
    }
    if let Err(reason) = price_family(cost.template_size, cost.plain_size) {
        return Ok(Production::Plain { reason, cost });
    }
    let peak_address = generalizer.graph.address(peak)?;
    let join_address = generalizer.graph.address(join)?;
    let region = TemplateAddress::of(&(
        program,
        core::mem::discriminant(&first.rule),
        generalizer.graph.vocabulary_address(),
        peak_address,
        join_address,
    ));
    let before = (usize::from(cache.checked()), usize::from(cache.hits()));
    // A ground carrier still owes replay; it has one region-only triple.
    let ground = generalizer
        .entries
        .is_empty()
        .then_some((EntryIndex::from(usize::MAX), peak));
    let checks = ground.into_iter().chain(
        generalizer
            .entries
            .iter()
            .zip(&generalizer.arms)
            .flat_map(|(entry, column)| column.iter().map(move |arm| (entry.point, *arm))),
    );
    for (point, arm) in checks {
        let key = InheritanceKey {
            region,
            entry: point,
            body: generalizer.graph.address(arm)?,
        };
        let verdict = match cache.lookup(&key) {
            | Maybe::Present(verdict) => verdict,
            | Maybe::Absent(inheritance_lookup::Absent::Unchecked) => {
                let bindings = BTreeMap::from([(point, arm)]);
                let (mut probe, step) =
                    materialize(&generalizer.graph, sides, first.rule, &bindings)?;
                let verdict = match replay_equation(&mut probe, step, budget) {
                    | Ok(()) => InheritanceVerdict::Inherited,
                    | Err(StageError::Exhausted) => return Err(StageError::Exhausted),
                    | Err(_) => InheritanceVerdict::MissesTheJoin {
                        leg: TemplateLeg::PathA,
                    },
                };
                if verdict == InheritanceVerdict::Inherited {
                    cost.replayed_steps =
                        ReplayStepCount::from(usize::from(cost.replayed_steps).saturating_add(1));
                }
                cache.record_check(key, verdict);
                verdict
            },
        };
        cost.triples_checked = gandr_theory_deep_inference::TripleCount::from(
            usize::from(cache.checked()).saturating_sub(before.0),
        );
        cost.cache_hits = gandr_theory_deep_inference::CacheHitCount::from(
            usize::from(cache.hits()).saturating_sub(before.1),
        );
        if verdict != InheritanceVerdict::Inherited {
            return Ok(Production::Plain {
                reason: TemplateRefusal::NotInherited { key, verdict },
                cost,
            });
        }
    }
    let mut retained = Vec::from(sides);
    retained.extend(
        generalizer
            .entries
            .iter()
            .flat_map(|entry| entry.arms.keys().copied()),
    );
    let (graph, map) = generalizer.graph.compact(&retained)?;
    let mut entries = generalizer.entries;
    for entry in &mut entries {
        entry.arms = entry
            .arms
            .iter()
            .map(|(id, guard)| {
                map.get(id)
                    .copied()
                    .map(|id| (id, *guard))
                    .ok_or(StageError::Unbalanced)
            })
            .collect::<Result<_, _>>()?;
    }
    let peak = *map.get(&peak).ok_or(StageError::Unbalanced)?;
    let join = *map.get(&join).ok_or(StageError::Unbalanced)?;
    let sides = [peak, join];
    Ok(Production::Go(Template {
        graph,
        sides,
        rule: first.rule,
        entries,
        cost,
    }))
}

impl Template
{
    /// Match the member's peak, choosing only arms present in this template.
    ///
    /// # Specification
    /// - ensures: every repeated point has one exact body, selected from the
    ///   member's own source; the target contributes no choices.
    /// - fails: `InvalidCertificate` on a rigid mismatch, conflicting point or
    ///   external arm; propagates malformed syntax lookups.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `StageError::InvalidCertificate` or syntax import errors.
    ///
    /// # Adequacy
    /// - hypothesis: L2/L3 — all harvested members and a conflicting repeated
    ///   point distinguish target-guided choice and unchecked external arms.
    /// - witness: `template::tests::every_member_admits_as_its_plain_replay`
    /// - witness: `template::tests::peak_choices_are_correlated`
    #[inline]
    pub fn peak_substitution(
        &self,
        arena: &Arena,
        source: TermId,
    ) -> Result<Substitution, StageError>
    {
        // Import only one peak; the template skeleton and arms stay borrowed.
        let mut graph = self.graph.member();
        let imported = graph.import(arena, &[source])?;
        let root = *imported.first().ok_or(StageError::Unbalanced)?;
        let [peak, _] = self.sides;
        let mut pending = Vec::from([(peak, root)]);
        let mut seen = BTreeSet::new();
        let mut bindings = BTreeMap::new();
        while let Some((pattern, actual)) = pending.pop() {
            if !seen.insert((pattern, actual)) {
                continue;
            }
            let pattern = self.graph.node(pattern)?;
            if let Head::Point(point) = pattern.head {
                let entry = self
                    .entries
                    .get(usize::from(point))
                    .ok_or(StageError::Unbalanced)?;
                let address = graph.address(actual)?;
                let mut selected = None;
                for arm in entry.arms.keys() {
                    if self.graph.address(*arm)? == address {
                        match self.graph.compare(*arm, &graph, actual) {
                            | Ok(()) => {
                                selected = Some(*arm);
                                break;
                            },
                            | Err(StageError::InvalidCertificate) => {},
                            | Err(error) => return Err(error),
                        }
                    }
                }
                let selected = selected.ok_or(StageError::InvalidCertificate)?;
                if bindings
                    .insert(point, selected)
                    .is_some_and(|old| old != selected)
                {
                    return Err(StageError::InvalidCertificate);
                }
                continue;
            }
            let actual = graph.node(actual)?;
            if pattern.head != actual.head {
                return Err(StageError::InvalidCertificate);
            }
            pending.extend(
                pattern
                    .children
                    .0
                    .into_iter()
                    .flatten()
                    .zip(actual.children.0.into_iter().flatten()),
            );
        }
        if bindings.len() != self.entries.len() {
            return Err(StageError::InvalidCertificate);
        }
        Ok(Substitution(bindings))
    }

    /// Materialize one member; the caller owns and drops its independent arena.
    ///
    /// # Specification
    /// - ensures: both sides and the decision come from the template and the
    ///   source-derived substitution, without consulting inheritance evidence.
    /// - fails: `InvalidCertificate` for missing or external arms; syntax
    ///   errors.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `StageError::InvalidCertificate` or materialization errors.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — independent plain replay observes each projected
    ///   member.
    /// - witness: `template::tests::every_member_admits_as_its_plain_replay`
    #[inline]
    pub fn instantiate(
        &self,
        substitution: &Substitution,
    ) -> Result<(Arena, Step), StageError>
    {
        for entry in &self.entries {
            if !substitution
                .0
                .get(&entry.point)
                .is_some_and(|id| entry.arms.contains_key(id))
            {
                return Err(StageError::InvalidCertificate);
            }
        }
        materialize(&self.graph, self.sides, self.rule, &substitution.0)
    }

    /// Independently replay one projected equation, never trusting the cache.
    ///
    /// # Specification
    /// - ensures: the projected equation passed kernel equation replay.
    /// - fails: matching, materialization or the kernel's exact replay error.
    /// - panics: none.
    /// - intension: at most one projected member arena is resident in this
    ///   call.
    ///
    /// # Errors
    /// Propagates `StageError` from matching, materialization and replay.
    ///
    /// # Adequacy
    /// - hypothesis: L2/L3 — plain replay agrees, including a poisoned cache's
    ///   incorrectly licensed member, which replay still refuses.
    /// - witness: `template::tests::every_member_admits_as_its_plain_replay`
    /// - witness: `template::tests::a_poisoned_inheritance_entry_is_caught_at_admission`
    #[inline]
    pub fn admit(
        &self,
        arena: &Arena,
        source: TermId,
        budget: &mut Budget,
    ) -> Result<(), StageError>
    {
        let substitution = self.peak_substitution(arena, source)?;
        let (mut instance, step) = self.instantiate(&substitution)?;
        replay_equation(&mut instance, step, budget)
    }
}

/// Replay a complete certificate, exercising paying equation templates first.
///
/// # Specification
/// - ensures: returns exactly ordinary complete replay's classifier or error
///   when projections match; original node identities and all congruence
///   premises remain intact. No local equation check replaces endpoint
///   formation.
/// - fails: projection mismatch or the kernel's typed replay refusal.
/// - panics: none.
///
/// # Errors
/// Propagates `StageError` from projection and complete replay.
///
/// # Adequacy
/// - hypothesis: L2 — every harvested complete certificate and altered targets
///   are compared with plain replay, including congruence-dependent equations.
/// - witness: `template::tests::every_member_admits_as_its_plain_replay`
#[inline]
pub fn readmit(
    arena: &mut Arena,
    context: &[TypeId],
    certificate: &Certificate,
    productions: &[Production],
    budget: &mut Budget,
) -> Result<TypeId, StageError>
{
    for production in productions {
        if let Production::Go(ref template) = *production {
            for step in &certificate.steps {
                if step.rule == template.rule {
                    // A program may have several families under one decision;
                    // a peak outside this family remains ordinary replay's job.
                    match template.peak_substitution(arena, step.source) {
                        | Ok(substitution) => {
                            let (instance, projected) = template.instantiate(&substitution)?;
                            // Full replay below checks this same equation with its
                            // original identities and every congruence premise.
                            let mut graph = Graph::default();
                            let expected = graph.import(arena, &[step.target])?;
                            let actual = graph.import(&instance, &[projected.target])?;
                            if expected != actual {
                                return Err(StageError::InvalidCertificate);
                            }
                        },
                        | Err(StageError::InvalidCertificate) => {},
                        | Err(error) => return Err(error),
                    }
                }
            }
        }
    }
    gandr_kernel_core::stage::replay(arena, context, certificate, budget)
}
