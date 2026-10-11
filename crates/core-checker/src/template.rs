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
//! correlated. `template::analyze` generalizes a family's first and last
//! members before the rest: a point the two leave outside the peak stays
//! outside however many members join them, so the family is refused from
//! those two, and a family they leave open imports its other members into the
//! same graph. Members with equal sides generalize alike, so that family is
//! generalized over its distinct members, each imported once, and every member
//! reads its arms from its row. `template::produce` prices generalized sides,
//! decisions and guarded arms before replaying each distinct inheritance
//! triple with the other points rigid. The original `s < floor(F / s)` price
//! and the additional `s + T*c < F` price remain separately selectable. The
//! latter uses `c = s` as an enforced per-check kernel-fuel allowance; an
//! unfinished check declines without memoizing a verdict. Neither price is a
//! wall-clock bound. Admission chooses arms from the member's peak and
//! ordinary kernel replay remains authoritative, even with a poisoned cache.
//! Complete certificates retain their original congruence premises.
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
//! arithmetic inference or normalizing the kernel would change the
//! specification. Revisit the single relation only with a separately specified
//! producer rule whose instances ordinary replay can still check.

mod admission;
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

use anodized::spec;
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
///
/// # Specification
/// - ensures: one source-selected arm per generalized point; repeated
///   occurrences share that arm.
/// - panics: none.
/// - executable: none — the private map has no constructor call to instrument;
///   `peak_substitution` checks correlation and instantiate checks membership.
///
/// # Adequacy
/// - hypothesis: L3 — conflicting repeated points and absent arms must refuse
///   rather than select independent substitutions.
/// - witness: `template::tests::peak_choices_are_correlated`
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
///
/// # Specification
/// - ensures: retains generalized sides and distinct arms, not a member list.
///   Its selected price passed; cached inheritance never licenses admission
///   without ordinary kernel replay.
/// - panics: none.
/// - executable: none — this privately constructed aggregate is checked at
///   produce and admit; an aggregate attribute has no call to instrument.
///
/// # Adequacy
/// - hypothesis: L1/L3 — finite cancellation families and poisoned inheritance
///   distinguish a strict price from unchecked equation acceptance.
/// - witness: `template::tests::a_template_is_emitted_only_below_its_expansion_factor`
/// - witness: `template::tests::a_poisoned_inheritance_entry_is_caught_at_admission`
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
    /// No candidate exists: the family is empty or mixes rules, or a point of
    /// its generalization lies outside the peak.
    Refused
    {
        /// The refusal, decided before any price or inheritance check.
        reason: TemplateRefusal,
        /// The available plain-family accounting.
        cost: FamilyCostReport,
    },
}

/// An untrusted candidate and transient discovery columns, before inheritance.
///
/// # Specification
/// - ensures: carries joint source/target columns and distinct guarded arms;
///   the source chooses every point. Neither discovery nor serialization
///   certifies an equation.
/// - panics: none.
/// - executable: none — analyze owns construction; production and independent
///   image reconstruction check the relationships between its private fields.
///
/// # Adequacy
/// - hypothesis: L2/L3 — predecessor columns, independent decoded equations and
///   target-only refusals distinguish correlation from unchecked generality.
/// - witness: `template::tests::serialized_images_reconstruct_the_original_equations`
/// - witness: `template::tests::predecessor_discovery_refuses_zero_inner_and_other_offsets`
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
    /// Node accounting before checks or admissions.
    cost: FamilyCostReport,
    /// Cold-cache obligation count, determined by distinct arm groups.
    triples: gandr_theory_deep_inference::TripleCount,
}

/// Whether the source chooses every generalized point.
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
    #[spec(ensures: |output| output.as_ref().ok().is_none_or(|id|
        self.graph.node(*id).is_ok()))]
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
#[spec(captures: [available = budget.0], ensures: budget.0 <= available)]
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
#[spec(ensures: |output| output.as_ref().ok().is_none_or(|&(ref arena, step)|
    step.rule == rule && arena.term(step.source).is_ok()
        && arena.term(step.target).is_ok()))]
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

/// One family's imported sides, generalized together over one graph.
struct Generalization
{
    /// The graph, the columns, the points and every member's arm column.
    generalizer: Generalizer,
    /// Generalized source and target.
    sides: [Id; 2],
    /// The plain size `F`: every member's source and target, plus one
    /// decision per member.
    plain: NodeCount,
    /// Whether the source chooses every point.
    rooting: PeakRoots,
}

/// A member's index among its family's distinct members.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Row(usize);

/// A family's distinct members, and every member's row among them.
///
/// Members with one source and one target generalize alike. Two columns are
/// equal, agree on a constructor, or lie pointwise one below each other over
/// every member exactly when they do over one member of each distinct pair,
/// and a column's distinct bodies are the same set. So a family generalized
/// over its distinct members, each member reading its arms from its row, is
/// the family generalized over every member.
///
/// # Specification
/// - ensures: `firsts` holds, ascending, the family position of each distinct
///   source and target pair's first member; member `i`'s row indexes the entry
///   of `firsts` whose member has member `i`'s sides.
/// - panics: none.
/// - executable: none — this private aggregate has no call to instrument;
///   [`Distinct::of`] checks the relationship at construction.
///
/// # Adequacy
/// - hypothesis: L2 — every harvested staging family's candidate, generalized
///   over its distinct members, equals the candidate generalized over every
///   member, coordinates, points, guards and member arms included.
/// - witness: `template::tests::distinct_members_generalize_as_every_member`
struct Distinct
{
    /// The first member of each distinct pair, in family order.
    firsts: Vec<MemberIndex>,
    /// Each member's row, in family order.
    rows: Vec<Row>,
}

impl Distinct
{
    /// Group a family's members by their sides, in first-occurrence order.
    ///
    /// # Specification
    /// - ensures: one row per member; the member a row names has that member's
    ///   sides; first members ascend, so the first member is the first row.
    /// - panics: none.
    /// - intension: one ordered-map probe per member.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every harvested staging family's candidate,
    ///   generalized over its distinct members, equals the candidate
    ///   generalized over every member; a row naming another pair's member or a
    ///   member left out changes an arm column or a point.
    /// - witness: `template::tests::distinct_members_generalize_as_every_member`
    #[spec(ensures: |output| output.rows.len() == family.len()
        && output.firsts.windows(2).all(|pair| pair.first() < pair.get(1))
        && output.rows.iter().zip(family).all(|(row, step)| output.firsts.get(row.0)
            .and_then(|first| family.get(usize::from(*first)))
            .is_some_and(|first| first.source == step.source && first.target == step.target)))]
    fn of(family: &[Step]) -> Self
    {
        let mut seen = BTreeMap::new();
        let mut firsts = Vec::new();
        let mut rows = Vec::with_capacity(family.len());
        for (position, step) in family.iter().enumerate() {
            let next = Row(firsts.len());
            let row = *seen.entry((step.source, step.target)).or_insert(next);
            if row == next {
                firsts.push(MemberIndex::from(position));
            }
            rows.push(row);
        }
        Self { firsts, rows }
    }

    /// Every member its own row.
    ///
    /// # Specification
    /// trivial.
    fn each(count: MemberCount) -> Vec<Row>
    {
        (0 .. usize::from(count)).map(Row).collect()
    }
}

/// Import members' sources and targets into `graph`, interleaved in member
/// order.
///
/// # Specification
/// - ensures: position `2i` holds member `i`'s source and `2i + 1` its target;
///   content already in the graph keeps its coordinate.
/// - fails: the arena's lookup error for an absent side.
/// - panics: none.
///
/// # Errors
/// Returns `UnknownTerm`, `UnknownType` or Unbalanced from the import.
///
/// # Adequacy
/// - hypothesis: L2 — independent side sizes and plain replay of every member
///   distinguish a lost, duplicated or reordered side.
/// - witness: `template::tests::a_template_is_emitted_only_below_its_expansion_factor`
/// - witness: `template::tests::every_member_admits_as_its_plain_replay`
#[spec(ensures: |output| output.as_ref().ok().is_none_or(|ids|
    ids.len() == members.len().saturating_mul(2)))]
fn import_members(
    graph: &mut Graph,
    arena: &Arena,
    members: &[Step],
) -> Result<Vec<Id>, StageError>
{
    let roots = members
        .iter()
        .flat_map(|step| [step.source, step.target])
        .collect::<Vec<_>>();
    graph.import(arena, &roots)
}

/// Read interleaved imported sides as one source and target per member.
///
/// # Specification
/// - ensures: pair `i` holds positions `2i` and `2i + 1`.
/// - fails: Unbalanced for an odd count.
/// - panics: none.
///
/// # Errors
/// Returns `StageError::Unbalanced`.
///
/// # Adequacy
/// - hypothesis: L2 — plain replay of every member distinguishes a source
///   paired with another member's target.
/// - witness: `template::tests::every_member_admits_as_its_plain_replay`
#[spec(ensures: |output| output.as_ref().ok().is_none_or(|pairs|
    pairs.len().saturating_mul(2) == ids.len()))]
fn pairs(ids: &[Id]) -> Result<&[[Id; 2]], StageError>
{
    let (pairs, rest) = ids.as_chunks::<2>();
    if rest.is_empty() {
        Ok(pairs)
    }
    else {
        Err(StageError::Unbalanced)
    }
}

/// Generalize imported members' sources into the peak, then their targets
/// into the join, over the distinct members `rows` names.
///
/// # Specification
/// - requires: every row indexes `members`, and every member is some row's.
/// - ensures: the peak's points are its disagreeing source columns; a join
///   column equal to a peak point, or one below it by the stated predecessor
///   relation, reuses it, and any other disagreeing join column is a point
///   outside the peak. `rooting` names the first such point; `plain` charges
///   every row's sides and decision. Arm columns hold one arm per row, in row
///   order.
/// - fails: Unbalanced for no members, a row outside `members` or a malformed
///   graph edge.
/// - panics: none.
/// - intension: columns are as wide as `members`; only the arm columns are read
///   out to one entry per row.
///
/// # Errors
/// Returns `StageError::Unbalanced`.
///
/// # Adequacy
/// - hypothesis: L2/L3 — reconstruction of every member, independent sizes and
///   the predecessor near-misses distinguish lost correlations, undercharged
///   sides and a target-only point counted inside the peak; generalizing every
///   staged family over its distinct members and over every member
///   distinguishes an arm read from the wrong row or a duplicate charged once.
/// - witness: `template::tests::every_member_admits_as_its_plain_replay`
/// - witness: `template::tests::a_template_is_emitted_only_below_its_expansion_factor`
/// - witness: `template::tests::predecessor_discovery_refuses_zero_inner_and_other_offsets`
/// - witness: `template::tests::distinct_members_generalize_as_every_member`
#[spec(
    requires: rows.iter().all(|row| row.0 < members.len())
        && (0 .. members.len()).all(|member| rows.contains(&Row(member))),
    ensures: |output| output.as_ref().ok().is_none_or(|generalization|
        generalization.generalizer.entries.len() == generalization.generalizer.arms.len()
            && generalization.generalizer.arms.iter().all(|column| column.len() == rows.len())
            && match generalization.rooting {
                PeakRoots::Complete => true,
                PeakRoots::Missing(point) => generalization.generalizer.entries.iter()
                    .any(|entry| entry.point == point),
            }),
)]
fn generalize(
    graph: Graph,
    members: &[[Id; 2]],
    rows: &[Row],
) -> Result<Generalization, StageError>
{
    let mut generalizer = Generalizer {
        graph,
        columns: BTreeMap::new(),
        entries: Vec::new(),
        arms: Vec::new(),
    };
    let mut peaks = Vec::with_capacity(members.len());
    let mut joins = Vec::with_capacity(members.len());
    let mut charges = Vec::with_capacity(members.len());
    for &[peak, join] in members {
        peaks.push(peak);
        joins.push(join);
        let peak_size = generalizer.graph.size(peak)?;
        let join_size = generalizer.graph.size(join)?;
        charges.push(
            1_usize
                .saturating_add(usize::from(peak_size))
                .saturating_add(usize::from(join_size)),
        );
    }
    let mut plain = 0_usize;
    for row in rows {
        let charge = charges.get(row.0).copied().ok_or(StageError::Unbalanced)?;
        plain = plain.saturating_add(charge);
    }
    let peak = generalizer.column(peaks, EntryIndex::from(0))?;
    let source_points = EntryIndex::from(generalizer.entries.len());
    let join = generalizer.column(joins, source_points)?;
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
    let rooting = generalizer
        .entries
        .iter()
        .find(|entry| !points.contains(&entry.point))
        .map_or(PeakRoots::Complete, |entry| PeakRoots::Missing(entry.point));
    generalizer.arms = generalizer
        .arms
        .iter()
        .map(|column| {
            rows.iter()
                .map(|row| column.get(row.0).copied().ok_or(StageError::Unbalanced))
                .collect::<Result<Vec<_>, _>>()
        })
        .collect::<Result<_, _>>()?;
    Ok(Generalization {
        generalizer,
        sides: [peak, join],
        plain: NodeCount::from(plain),
        rooting,
    })
}

/// Import every member into a fresh graph and generalize them together.
///
/// # Specification
/// - ensures: the family's own generalization, no member skipped: its plain
///   size counts at least three nodes per member. The probe's refusals are
///   checked against it.
/// - fails: the arena's lookup error for an absent side; Unbalanced for an
///   empty family.
/// - panics: none.
///
/// # Errors
/// Returns `UnknownTerm`, `UnknownType` or Unbalanced.
///
/// # Adequacy
/// - hypothesis: L2 — harvested power and double-product families compare every
///   verdict and cost the probe's path reports against this one's.
/// - witness: `template::tests::staged_families_keep_their_verdicts_under_the_probe`
#[spec(ensures: |output| output.as_ref().ok().is_none_or(|all|
    usize::from(all.plain) >= family.len().saturating_mul(3)))]
fn generalize_all(
    arena: &Arena,
    family: &[Step],
) -> Result<Generalization, StageError>
{
    let mut graph = Graph::default();
    let ids = import_members(&mut graph, arena, family)?;
    let members = pairs(&ids)?;
    let rows = Distinct::each(MemberCount::from(members.len()));
    generalize(graph, members, &rows)
}

/// What a family's first and last members decide before the others are
/// imported.
enum Probe
{
    /// The two leave a point outside their peak, so the family does too.
    Outside(EntryIndex),
    /// Undecided: a graph holding the two members' imported sides and nothing
    /// generalized from them.
    Open
    {
        /// Both members' imported sides.
        graph: Graph,
        /// The first member's imported source and target.
        first: [Id; 2],
        /// The last member's imported source and target.
        last: [Id; 2],
    },
}

/// Generalize a family's first and last members alone, refusing the family
/// when they leave a point outside the peak.
///
/// A join point lies outside the peak when its column — the members'
/// subterms at one join position below agreeing constructors — disagrees,
/// equals no column the peak made a point, and is not pointwise one below
/// such a column. Adding members only splits agreement. Constructors that
/// disagree on two members disagree on all; subterms equal on all members are
/// equal on two; a column equals another, or lies pointwise one below it, only
/// if it does so on every member. Follow the join towards the two members'
/// outside point and stop where the family's members first disagree. Were the
/// family's column there a peak point's, the two members' columns there and
/// at that peak position would agree, so their peak would reach the same
/// columns their join reaches down to their outside point, which would then
/// lie inside their peak. Were it one below a peak point's, it would be a
/// numeral column, so the stop is the outside point itself, and the relation
/// would hold on the two members too. So the family leaves a point outside
/// its peak. The implication holds for any two members; the first and last
/// are the extremes of producer order.
///
/// # Specification
/// - requires: every member's sides are terms of `arena`.
/// - ensures: `Outside` only when the family's own generalization leaves a
///   point outside its peak; it names the first such point of the two members'
///   generalization. `Open` drops every node the two-member generalization
///   added, keeping their import.
/// - fails: Unbalanced for an empty family.
/// - panics: none.
///
/// # Errors
/// Returns `StageError::Unbalanced`.
///
/// # Adequacy
/// - hypothesis: L2/L3 — the full generalization judges the probe on every
///   harvested power and double-product family and on constructed families
///   whose first and last members are and are not the extreme ones, including
///   families the two leave open and the rest refuse. A probe that misreads the
///   predecessor relation, compares other members, keeps its pattern nodes or
///   loses a member's import changes a verdict or a cost there.
/// - witness: `template::tests::outside_peak_refusals_follow_from_the_first_and_last_members`
/// - witness: `template::tests::staged_families_keep_their_verdicts_under_the_probe`
#[spec(
    requires: family.iter().all(|step| arena.term(step.source).is_ok()
        && arena.term(step.target).is_ok()),
    ensures: |output| output.as_ref().ok().is_none_or(|probe|
        !matches!(*probe, Probe::Outside(_)) || generalize_all(arena, family)
            .is_ok_and(|all| matches!(all.rooting, PeakRoots::Missing(_)))),
)]
fn probe(
    arena: &Arena,
    family: &[Step],
) -> Result<Probe, StageError>
{
    let (Some(first), Some(last)) = (family.first(), family.last())
    else {
        return Err(StageError::Unbalanced);
    };
    let mut graph = Graph::default();
    let ids = import_members(&mut graph, arena, &[*first, *last])?;
    let end = graph.end();
    let &[first, last] = pairs(&ids)?
    else {
        return Err(StageError::Unbalanced);
    };
    let Generalization {
        generalizer,
        rooting,
        ..
    } = generalize(graph, &[first, last], &[Row(0), Row(1)])?;
    if let PeakRoots::Missing(point) = rooting {
        return Ok(Probe::Outside(point));
    }
    let mut graph = generalizer.graph;
    graph.truncate(end);
    Ok(Probe::Open { graph, first, last })
}

/// Import the distinct members a probe left open into its graph, and
/// generalize the family over its distinct members.
///
/// # Specification
/// - requires: `graph` holds the first and last members' import alone, at
///   `ends`, and the family has three or more members.
/// - ensures: the family's generalization: each distinct pair is imported once,
///   in family order after the two ends, so every node keeps the coordinate an
///   import of every member would give it, and every member's arms are its
///   row's.
/// - fails: the arena's lookup error for an absent side; Unbalanced for a
///   malformed graph edge.
/// - panics: none.
///
/// # Errors
/// Returns `UnknownTerm`, `UnknownType` or Unbalanced.
///
/// # Adequacy
/// - hypothesis: L2 — every harvested staging family's candidate equals the one
///   generalized over every member imported in the same order; an import out of
///   order moves a coordinate and a lost or extra member changes an arm column.
/// - witness: `template::tests::distinct_members_generalize_as_every_member`
#[spec(
    requires: family.len() >= 3,
    ensures: |output| output.as_ref().ok().is_none_or(|generalization|
        generalization.generalizer.arms.iter().all(|column| column.len() == family.len())),
)]
fn generalize_rest(
    mut graph: Graph,
    arena: &Arena,
    family: &[Step],
    ends: [[Id; 2]; 2],
) -> Result<Generalization, StageError>
{
    let distinct = Distinct::of(family);
    let first = MemberIndex::from(0_usize);
    let last = MemberIndex::from(family.len().saturating_sub(1));
    let middle = distinct
        .firsts
        .iter()
        .filter(|&&member| member != first && member != last)
        .map(|&member| {
            family
                .get(usize::from(member))
                .copied()
                .ok_or(StageError::Unbalanced)
        })
        .collect::<Result<Vec<_>, _>>()?;
    let ids = import_members(&mut graph, arena, &middle)?;
    let middle = pairs(&ids)?;
    let [first_sides, last_sides] = ends;
    let mut members = Vec::with_capacity(distinct.firsts.len());
    members.push(first_sides);
    members.extend_from_slice(middle);
    if distinct.firsts.last() == Some(&last) {
        members.push(last_sides);
    }
    generalize(graph, &members, &distinct.rows)
}

/// Anti-unify and price a uniform family without replay or admission authority.
///
/// # Specification
/// - ensures: retains exact source correlations, permits only the stated outer
///   predecessor relation, and counts distinct triples before any check. Empty
///   or mixed-rule families retain their structural refusal and cost. A point
///   outside the peak refuses the family: from its first and last members when
///   the two alone leave one, with the family's member counts and no sizes, and
///   otherwise from every member, with every size. A candidate's source chooses
///   every point.
/// - fails: the first absent side in member order, sources before targets,
///   whether or not the probe would skip its member; graph-size overflow.
/// - panics: none.
/// - intension: a family of three or more members imports and generalizes its
///   first and last members first; a family they leave open imports each other
///   distinct member once, into the same graph, and generalizes its distinct
///   members. Discovery indexes are released before returning; member arm
///   columns remain only until serialization or guarded production completes.
///
/// # Errors
/// Propagates `StageError` from syntax import and arithmetic.
///
/// # Adequacy
/// - hypothesis: L1/L2/L3 — independent sizes, plain replay, all three
///   adversarial classes and exact cache counts distinguish weakening any gate
///   clause; the full generalization judges every refusal for a point outside
///   the peak, and a malformed member the probe would skip still fails.
/// - witness: `template::tests::a_template_is_emitted_only_below_its_expansion_factor`
/// - witness: `template::tests::every_member_admits_as_its_plain_replay`
/// - witness: `template::tests::a_skeleton_divergent_family_yields_no_template`
/// - witness: `template::tests::an_entry_a_decision_discriminates_on_yields_no_template`
/// - witness: `template::tests::a_family_with_no_shared_content_yields_no_template`
/// - witness: `template::tests::the_inheritance_check_runs_once_per_distinct_triple`
/// - witness: `template::tests::empty_and_malformed_families_preserve_refusals`
/// - witness: `template::tests::outside_peak_refusals_follow_from_the_first_and_last_members`
/// - witness: `template::tests::staged_families_keep_their_verdicts_under_the_probe`
/// - witness: `template::tests::distinct_members_generalize_as_every_member`
#[spec(ensures: |output| output.as_ref().ok().is_none_or(|analysis| match *analysis {
    Analysis::Candidate(ref candidate) => usize::from(candidate.cost.members) == family.len()
        && candidate.entries.len() == candidate.arms.len()
        && candidate.arms.iter().all(|column| column.len() == family.len())
        && usize::from(candidate.triples) == candidate.entries.iter()
            .map(|entry| entry.arms.len()).sum::<usize>().max(1),
    Analysis::Refused { reason: TemplateRefusal::EmptyFamily, .. } => family.is_empty(),
    Analysis::Refused { reason: TemplateRefusal::SkeletonDivergence { member }, .. } =>
        family.first().zip(family.get(usize::from(member)))
            .is_some_and(|(first, member)| first.rule != member.rule),
    Analysis::Refused { reason: TemplateRefusal::EntryOutsidePeak { .. }, cost } =>
        usize::from(cost.members) == family.len() && generalize_all(arena, family)
            .is_ok_and(|all| matches!(all.rooting, PeakRoots::Missing(_))),
    Analysis::Refused { .. } => false,
}))]
#[inline]
pub fn analyze(
    arena: &Arena,
    program: ProgramId,
    family: &[Step],
) -> Result<Analysis, StageError>
{
    let cost = FamilyCostReport {
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
    // A member the probe skips still fails as its import would.
    for step in family {
        arena.term(step.source)?;
        arena.term(step.target)?;
    }
    let generalization = match *family {
        | [_, ref middle @ .., _] if !middle.is_empty() => match probe(arena, family)? {
            | Probe::Outside(entry) => {
                return Ok(Analysis::Refused {
                    reason: TemplateRefusal::EntryOutsidePeak { entry },
                    cost,
                });
            },
            | Probe::Open { graph, first, last } => {
                generalize_rest(graph, arena, family, [first, last])?
            },
        },
        | _ => generalize_all(arena, family)?,
    };
    conclude(generalization, program, first.rule, cost)
}

/// Size a family's generalization and price it as a candidate, refusing a
/// point outside the peak.
///
/// # Specification
/// - requires: `cost` counts the generalized family's members.
/// - ensures: charges `F`, `s`, `F / s` and the distinct triples; refuses
///   exactly when a point lies outside the peak, with every size, and otherwise
///   yields the candidate under `program` and `rule`.
/// - fails: Overflow when the distinct triples are unrepresentable; Unbalanced
///   for a malformed graph edge.
/// - panics: none.
///
/// # Errors
/// Returns `StageError::Overflow` or `StageError::Unbalanced`.
///
/// # Adequacy
/// - hypothesis: L1/L2 — independent tree counts, cancellation prices and the
///   staged families' fresh-import reference distinguish an undercharged size,
///   a lost triple and a refusal that drops its sizes.
/// - witness: `template::tests::a_template_is_emitted_only_below_its_expansion_factor`
/// - witness: `template::tests::staged_families_keep_their_verdicts_under_the_probe`
#[spec(captures: [plain_size = generalization.plain], ensures: |output| output.as_ref().ok().is_none_or(|analysis| match *analysis {
    Analysis::Candidate(ref candidate) => candidate.cost.plain_size == plain_size,
    Analysis::Refused { reason: TemplateRefusal::EntryOutsidePeak { .. }, cost } =>
        cost.plain_size == plain_size && usize::from(cost.template_size) > 0,
    Analysis::Refused { .. } => false,
}))]
fn conclude(
    generalization: Generalization,
    program: ProgramId,
    rule: Rule,
    mut cost: FamilyCostReport,
) -> Result<Analysis, StageError>
{
    let Generalization {
        generalizer,
        sides,
        plain,
        rooting,
    } = generalization;
    cost.plain_size = plain;
    let [peak, join] = sides;
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
    cost.expansion_factor =
        ExpansionFactor::from(usize::from(plain).checked_div(size).unwrap_or_default());
    let triples = generalizer
        .entries
        .iter()
        .map(|entry| entry.arms.len())
        .try_fold(0_usize, |total, count| {
            total.checked_add(count).ok_or(StageError::Overflow)
        })?
        .max(1);
    let triples = gandr_theory_deep_inference::TripleCount::from(triples);
    if let PeakRoots::Missing(entry) = rooting {
        return Ok(Analysis::Refused {
            reason: TemplateRefusal::EntryOutsidePeak { entry },
            cost,
        });
    }
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
        rule,
        program,
        cost,
        triples,
    }))
}

impl Candidate
{
    /// Observe both prices without consulting or changing a cache.
    ///
    /// # Specification
    /// - ensures: reports both strict cold-cache prices with c = s and every
    ///   distinct obligation, including the sole ground-carrier check.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the successor and ground beta families distinguish
    ///   the distinct-arm allowance from member counts or a warm-cache
    ///   discount.
    /// - witness: `template::tests::outer_predecessors_share_one_peak_point_and_replay`
    /// - witness: `template::tests::memoized_checks_respect_the_priced_allowance`
    #[spec(ensures: |output| output.triples == self.triples
        && output.check_bound == self.cost.template_size
        && output.unmemoized == price_family(self.cost.template_size, self.cost.plain_size)
        && output.memoized == gandr_theory_deep_inference::price_family_memoized(
            self.cost.template_size, self.cost.plain_size, self.triples, self.cost.template_size))]
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
    /// - ensures: Go passes the selected strict price and has inherited every
    ///   distinct triple. Memoized checks spend at most c each.
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
    #[spec(captures: [available = budget.0], ensures: |output|
        budget.0 <= available && output.as_ref().ok().is_none_or(|production| match *production {
            Production::Go(ref template) => {
                let s = usize::from(template.cost.template_size);
                let f = usize::from(template.cost.plain_size);
                match gate {
                    PriceGate::Unmemoized => f.checked_div(s).is_some_and(|factor| s < factor),
                    PriceGate::Memoized => template.entries.iter()
                        .map(|entry| entry.arms.len()).sum::<usize>().max(1)
                        .checked_mul(s).and_then(|work| s.checked_add(work))
                        .is_some_and(|charged| charged < f),
                }
            },
            Production::WorkBoundExceeded { bound, cost } => gate == PriceGate::Memoized
                && bound == cost.template_size,
            Production::Plain { .. } => true,
        }))]
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
            mut cost,
            triples: _,
        } = self;
        let [peak, join] = sides;
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
/// - witness: `template::tests::empty_and_malformed_families_preserve_refusals`
#[spec(captures: [available = budget.0], ensures: |output|
    budget.0 <= available && output.as_ref().ok().is_none_or(|production|
        usize::from(production.cost().members) == family.len()))]
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
    /// - witness: `template::tests::member_selection_and_complete_replay_reject_near_misses`
    #[spec(ensures: |output| output.as_ref().ok().is_none_or(|substitution|
        substitution.0.len() == self.entries.len() && self.entries.iter().all(|entry|
            substitution.0.get(&entry.point).is_some_and(|arm| entry.arms.contains_key(arm)))))]
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
    /// - witness: `template::tests::member_selection_and_complete_replay_reject_near_misses`
    #[spec(ensures: |output| output.as_ref().ok().is_none_or(|&(_, step)|
        step.rule == self.rule && self.entries.iter().all(|entry|
            substitution.0.get(&entry.point).is_some_and(|arm| entry.arms.contains_key(arm)))))]
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
    /// - witness: `template::tests::member_selection_and_complete_replay_reject_near_misses`
    #[spec(captures: [available = budget.0], ensures: budget.0 <= available)]
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
/// - witness: `template::tests::member_selection_and_complete_replay_reject_near_misses`
#[spec(captures: [available = budget.0], ensures: |output|
    budget.0 <= available && output.as_ref().ok().is_none_or(|ty| arena.ty(*ty).is_ok()))]
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
