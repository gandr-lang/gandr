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
//! other points rigid. The original `s < floor(F / s)` price and the additional
//! `s + T*c < F` price remain separately selectable. The latter uses `c = s`
//! as an enforced per-check kernel-fuel allowance; an unfinished check declines
//! without memoizing a verdict. Neither price is a wall-clock bound. Admission
//! chooses arms from the member's peak and ordinary kernel replay remains
//! authoritative, even with a poisoned cache. Complete certificates retain
//! their original congruence premises.
//!
//! The peak-rooted representation retains no member list; one instance can be
//! materialized, replayed and dropped. Storing substitutions per member would
//! grow the template with the family. Source-only discovery avoids splitting
//! families by the answer they should prove. One producer-only relation is
//! recognized: a target column exactly one below a positive outer-numeral
//! source point becomes `pred(point)`, not another choice. Inner numerals,
//! zero predecessors and other offsets stay rigid. The `staging_templates`
//! release example reports strict power and double-product families separately
//! from repeated generated controls, including time, scoped heap high-water
//! marks and refusal reasons. Its module documentation specifies the allocator
//! choice and measurement limits.
//!
//! The design keeps the original price rather than quietly substituting a new
//! interpretation of its work assumption. The additional gate enforces its
//! allowance instead of assuming every staging rule costs at most s. Keeping
//! numeral payloads entirely rigid loses predecessor sharing; arbitrary
//! arithmetic inference or normalizing the kernel would change the contract.
//! Revisit the single relation only with a separately specified producer rule
//! whose instances ordinary replay can still check.

mod harvest;
mod image;
mod syntax;
pub use harvest::Family;
pub use harvest::harvest;
pub use image::plain_image;
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
    /// The candidate exhausted its advertised per-check work allowance.
    WorkBoundExceeded
    {
        /// Accounting before the unfinished check; no verdict was memoized.
        cost: FamilyCostReport,
        /// Maximum kernel fuel spent on this check.
        bound: NodeCount,
    },
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
            | Self::Plain { cost, .. } | Self::WorkBoundExceeded { cost, .. } => cost,
        }
    }
}

/// Which independently reported strict price authorizes an inheritance attempt.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PriceGate
{
    /// The unchanged s < floor(F/s) gate.
    Unmemoized,
    /// Combined storage and memoized work: s + T*c < F.
    Memoized,
}

/// Both prices, computed before any inheritance check.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct FamilyPrices
{
    /// Distinct obligations, including one for an entry-free carrier.
    pub triples: gandr_theory_deep_inference::TripleCount,
    /// Per-check kernel work allowance; the memoized route enforces this cap.
    pub check_bound: NodeCount,
    /// The unchanged original gate's answer.
    pub unmemoized: Result<ExpansionFactor, TemplateRefusal>,
    /// The combined charge, or the additional gate's precise refusal.
    pub memoized: Result<NodeCount, gandr_theory_deep_inference::MemoizedPriceRefusal>,
}

/// Preparation without replay, preserving malformed-family refusals.
pub enum Analysis
{
    /// A generalized candidate, not an admission capability.
    Candidate(Candidate),
    /// No uniform nonempty equation skeleton exists.
    Refused
    {
        /// Structural refusal, before a candidate exists.
        reason: TemplateRefusal,
        /// The available plain-family accounting.
        cost: FamilyCostReport,
    },
}

/// An untrusted candidate and transient discovery columns, before inheritance.
pub struct Candidate
{
    /// Joint pattern and arm syntax.
    graph: Graph,
    /// Generalized points and their guarded arms.
    entries: Vec<Entry>,
    /// Member arm columns needed until preflight is consumed.
    arms: Vec<Vec<Id>>,
    /// Generalized source and target.
    sides: [Id; 2],
    /// The common local rule.
    rule: Rule,
    /// Producer namespace within this run.
    program: ProgramId,
    /// Whether every entry is rooted in the source.
    peak_roots: PeakRoots,
    /// Node accounting before checks or admissions.
    cost: FamilyCostReport,
    /// Cold-cache obligation count, determined by distinct arm groups.
    triples: gandr_theory_deep_inference::TripleCount,
}

/// Peak-rooting is decided during analysis, before inheritance can run.
enum PeakRoots
{
    /// Every generalized entry is chosen by the source.
    Complete,
    /// The first entry that only the target could determine.
    Missing(EntryIndex),
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
        source_points: EntryIndex,
    ) -> Result<Id, StageError>
    {
        let root = column.clone();
        let mut pending = Vec::from([(column, false)]);
        while let Some((column, ready)) = pending.pop() {
            if self.columns.contains_key(&column) {
                continue;
            }
            let first = *column.first().ok_or(StageError::Unbalanced)?;
            // Non-numeral columns cannot use the producer's one arithmetic relation.
            let numeral_points = if matches!(self.graph.node(first)?.head, Head::OuterNatural(_)) {
                usize::from(source_points)
            }
            else {
                0
            };
            // Only a source point can justify the one supported numeral relation.
            let mut predecessor = None;
            for source in self.arms.iter().take(numeral_points) {
                if source.len() != column.len() {
                    continue;
                }
                let mut related = true;
                for (source, target) in source.iter().zip(&column) {
                    match (
                        self.graph.node(*source)?.head,
                        self.graph.node(*target)?.head,
                    ) {
                        | (Head::OuterNatural(Natural(n)), Head::OuterNatural(Natural(m)))
                            if n.checked_sub(1) == Some(m) => {},
                        | _ => {
                            related = false;
                            break;
                        },
                    }
                }
                if related {
                    predecessor = self.columns.get(source).copied();
                    break;
                }
            }
            if let Some(point) = predecessor {
                let id = self.graph.intern(Node {
                    head: Head::Predecessor,
                    children: Children([Some(point), None, None]),
                })?;
                self.columns.insert(column, id);
                continue;
            }
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

/// Anti-unify and price a uniform family without replay or admission authority.
///
/// # Specification
/// - ensures: retains exact source correlations, permits only the stated outer
///   predecessor relation, and counts distinct triples before any check. Empty
///   or mixed-rule families retain their structural refusal and cost.
/// - fails: malformed arena references or graph-size overflow.
/// - panics: none.
/// - intension: discovery indexes are released before returning; member arm
///   columns remain only until serialization or guarded production completes.
///
/// # Errors
/// Propagates `StageError` from syntax import and arithmetic.
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
pub fn analyze(
    arena: &Arena,
    program: ProgramId,
    family: &[Step],
) -> Result<Analysis, StageError>
{
    let mut cost = FamilyCostReport {
        members: MemberCount::from(family.len()),
        plain_replayed_steps: ReplayStepCount::from(family.len()),
        ..FamilyCostReport::default()
    };
    let Some(first) = family.first()
    else {
        return Ok(Analysis::Refused {
            reason: TemplateRefusal::EmptyFamily,
            cost,
        });
    };
    if let Some(member) = family.iter().position(|member| member.rule != first.rule) {
        return Ok(Analysis::Refused {
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
    let peak = generalizer.column(peaks, EntryIndex::from(0))?;
    let source_points = EntryIndex::from(generalizer.entries.len());
    let join = generalizer.column(joins, source_points)?;
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
    let triples = generalizer
        .entries
        .iter()
        .map(|entry| entry.arms.len())
        .try_fold(0_usize, |total, count| {
            total.checked_add(count).ok_or(StageError::Overflow)
        })?
        .max(1);
    let triples = gandr_theory_deep_inference::TripleCount::from(triples);
    let peak_roots = generalizer
        .entries
        .iter()
        .find(|entry| !points.contains(&entry.point))
        .map_or(PeakRoots::Complete, |entry| PeakRoots::Missing(entry.point));
    let Generalizer {
        graph,
        entries,
        arms,
        columns: _,
    } = generalizer;
    Ok(Analysis::Candidate(Candidate {
        graph,
        entries,
        arms,
        sides,
        rule: first.rule,
        program,
        peak_roots,
        cost,
        triples,
    }))
}

impl Candidate
{
    /// Observe both prices without consulting or changing a cache.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn prices(&self) -> FamilyPrices
    {
        FamilyPrices {
            triples: self.triples,
            check_bound: self.cost.template_size,
            unmemoized: price_family(self.cost.template_size, self.cost.plain_size),
            memoized: gandr_theory_deep_inference::price_family_memoized(
                self.cost.template_size,
                self.cost.plain_size,
                self.triples,
                self.cost.template_size,
            ),
        }
    }

    /// Observe candidate node accounting before replay.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn cost(&self) -> FamilyCostReport
    {
        self.cost
    }

    /// Observe the generalized points in stable entry order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn points(&self) -> impl Iterator<Item = EntryIndex> + '_
    {
        self.entries.iter().map(|entry| entry.point)
    }

    /// Apply one selected price, then discharge inheritance before emission.
    ///
    /// # Specification
    /// - ensures: Go passes the selected strict price, is peak-rooted and has
    ///   inherited every distinct triple. Memoized checks spend at most c each.
    /// - fails: caller budget exhaustion or malformed syntax; an insufficient
    ///   price-derived work allowance declines the candidate without caching a
    ///   lie.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns syntax or caller-budget `StageError`.
    ///
    /// # Adequacy
    /// - hypothesis: L2/L3 — independent replay, cold/warm caches and a bounded
    ///   check distinguish a price from unchecked admission or unbounded work.
    /// - witness: `template::tests::every_member_admits_as_its_plain_replay`
    /// - witness: `template::tests::memoized_checks_respect_the_priced_allowance`
    #[inline]
    pub fn produce(
        self,
        gate: PriceGate,
        cache: &mut InheritanceCache,
        budget: &mut Budget,
    ) -> Result<Production, StageError>
    {
        let prices = self.prices();
        let Self {
            graph,
            entries,
            arms,
            sides,
            rule,
            program,
            peak_roots,
            mut cost,
            triples: _,
        } = self;
        let [peak, join] = sides;
        if let PeakRoots::Missing(entry) = peak_roots {
            return Ok(Production::Plain {
                reason: TemplateRefusal::EntryOutsidePeak { entry },
                cost,
            });
        }
        let pays = match gate {
            | PriceGate::Unmemoized => prices.unmemoized.is_ok(),
            | PriceGate::Memoized => prices.memoized.is_ok(),
        };
        if !pays {
            return Ok(Production::Plain {
                reason: TemplateRefusal::DoesNotPay {
                    template_size: cost.template_size,
                    plain_size: cost.plain_size,
                },
                cost,
            });
        }
        let peak_address = graph.address(peak)?;
        let join_address = graph.address(join)?;
        let region = TemplateAddress::of(&(
            program,
            core::mem::discriminant(&rule),
            graph.vocabulary_address(),
            peak_address,
            join_address,
        ));
        let before = (usize::from(cache.checked()), usize::from(cache.hits()));
        // A ground carrier still owes replay; it has one region-only triple.
        let ground = entries
            .is_empty()
            .then_some((EntryIndex::from(usize::MAX), peak));
        let checks = ground.into_iter().chain(
            entries
                .iter()
                .zip(&arms)
                .flat_map(|(entry, column)| column.iter().map(move |arm| (entry.point, *arm))),
        );
        for (point, arm) in checks {
            let key = InheritanceKey {
                region,
                entry: point,
                body: graph.address(arm)?,
            };
            let verdict = match cache.lookup(&key) {
                | Maybe::Present(verdict) => verdict,
                | Maybe::Absent(inheritance_lookup::Absent::Unchecked) => {
                    let bindings = BTreeMap::from([(point, arm)]);
                    let (mut probe, step) = materialize(&graph, sides, rule, &bindings)?;
                    let checked = match gate {
                        | PriceGate::Unmemoized => replay_equation(&mut probe, step, budget),
                        | PriceGate::Memoized => {
                            let cap = usize::from(prices.check_bound);
                            let available = budget.0.min(cap);
                            let mut limited = Budget(available);
                            let result = replay_equation(&mut probe, step, &mut limited);
                            budget.0 = budget
                                .0
                                .checked_sub(available.saturating_sub(limited.0))
                                .ok_or(StageError::Exhausted)?;
                            if result == Err(StageError::Exhausted) && available == cap {
                                return Ok(Production::WorkBoundExceeded {
                                    cost,
                                    bound: prices.check_bound,
                                });
                            }
                            result
                        },
                    };
                    let verdict = match checked {
                        | Ok(()) => InheritanceVerdict::Inherited,
                        | Err(StageError::Exhausted) => return Err(StageError::Exhausted),
                        | Err(_) => InheritanceVerdict::MissesTheJoin {
                            leg: TemplateLeg::PathA,
                        },
                    };
                    if verdict == InheritanceVerdict::Inherited {
                        cost.replayed_steps = ReplayStepCount::from(
                            usize::from(cost.replayed_steps).saturating_add(1),
                        );
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
        retained.extend(entries.iter().flat_map(|entry| entry.arms.keys().copied()));
        let (graph, map) = graph.compact(&retained)?;
        let mut entries = entries;
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
            rule,
            entries,
            cost,
        }))
    }
}

/// Prepare a family and emit it only under the selected price and inheritance.
///
/// # Specification
/// - ensures: preserves structural refusals; otherwise uses the selected price
///   and the candidate's replay checks. Neither gate replaces the other.
/// - fails: malformed syntax or caller-budget exhaustion.
/// - panics: none.
///
/// # Errors
/// Propagates `StageError` from analysis and inheritance.
///
/// # Adequacy
/// - hypothesis: L1/L2/L3 — the original gate witnesses remain on the original
///   route; the numeral and memo witnesses exercise the additional route.
/// - witness: `template::tests::a_template_is_emitted_only_below_its_expansion_factor`
/// - witness: `template::tests::every_member_admits_as_its_plain_replay`
#[inline]
pub fn produce(
    arena: &Arena,
    program: ProgramId,
    family: &[Step],
    gate: PriceGate,
    cache: &mut InheritanceCache,
    budget: &mut Budget,
) -> Result<Production, StageError>
{
    match analyze(arena, program, family)? {
        | Analysis::Candidate(candidate) => candidate.produce(gate, cache, budget),
        | Analysis::Refused { reason, cost } => Ok(Production::Plain { reason, cost }),
    }
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
