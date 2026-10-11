//! A family drafted from an earlier run's template, without importing its
//! members.
//!
//! The walk compares each member's source, in the member's own arena, with
//! the template's peak. A rigid constructor must agree exactly; a point binds
//! the member's subterm there. The arm each point body selects is remembered
//! per draft, and so is the verdict on each point-free pattern subtree against
//! each arena term, so a body or a shared rigid subterm many members repeat is
//! compared once, not once per member and arm. An exact draft binds only the
//! template's own arms. A widened draft also binds a body no arm holds, and
//! imports each such body once. Arms no member selects are dropped, and the
//! rest are numbered by first selection in member order: the canonical arm
//! order a fresh run uses, so the drafted schema is a function of the members.
//!
//! A member whose source disagrees with a rigid part of the skeleton rebases
//! the template. The innermost binder enclosing the first disagreement, or the
//! disagreement itself outside any binder, is replaced at every occurrence on
//! both sides by the member's own subterm, and every member is walked again. A
//! replacement that would remove a point is refused, and at most [`REPAIRS`]
//! replacements are made per draft.
//!
//! A family every member of which matches is still offered to the kernel only
//! when the drafted schema is the one a fresh run would emit for the same
//! members and the producer's own price would emit it. The walk fixes the
//! skeleton above every point. A fresh run's joint generalization keeps a
//! point exactly where its members' bodies disagree at the head, gives two
//! positions one point exactly where their columns agree on every member, and
//! reuses a source point for a target column equal to it before it reads the
//! column as one below another. So a point whose arms share one head, two
//! points whose columns agree, or a predecessor whose column equals a point's
//! refuses the draft. Every check here is untrusted: the kernel decides the
//! schema and every member's row.

use alloc::borrow::Cow;
use alloc::collections::btree_map;
use core::time::Duration;

use gandr_kernel_core::admission::Choice;
use gandr_kernel_core::admission::Guard;
use gandr_kernel_core::admission::Point;
use gandr_kernel_core::admission::Proposal;
use gandr_kernel_term::stage::Child;
use gandr_kernel_term::stage::Type;
use gandr_theory_deep_inference::TripleCount;
use gandr_theory_deep_inference::price_family_memoized;

use super::Arena;
use super::BTreeMap;
use super::BTreeSet;
use super::Children;
use super::Entry;
use super::EntryIndex;
use super::ExpansionFactor;
use super::FamilyCostReport;
use super::Graph;
use super::GuardId;
use super::Head;
use super::Id;
use super::Maybe;
use super::MemberCount;
use super::MemberIndex;
use super::Natural;
use super::Node;
use super::NodeCount;
use super::PriceGate;
use super::ReplayStepCount;
use super::Stage;
use super::StageError;
use super::Step;
use super::Template;
use super::TemplateRefusal;
use super::Term;
use super::TermId;
use super::TypeId;
use super::Vec;
use super::memo::Clock;
use super::price_family;
use super::spec;

/// The most binder replacements one draft makes before it gives up.
pub(super) const REPAIRS: RepairCount = RepairCount(4);

/// How many points a template generalizes.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct PointCount(pub usize);

/// Each point's leaves in one pattern's unfolded tree.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Occurrences
{
    /// Bare point leaves, by point.
    bare: Vec<usize>,
    /// Predecessor-wrapped point leaves, by point.
    under: Vec<usize>,
}

/// How many binders a rebase replaced.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
pub struct RepairCount(pub usize);

/// How many arms a draft added to its template's.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
pub struct ArmCount(pub usize);

/// Why a walk left a member unmatched.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Miss
{
    /// The member's decision differs from the template's.
    Rule,
    /// A rigid constructor or payload of the skeleton disagrees, and no
    /// rebase repairs it.
    Skeleton,
    /// A repeated point would take two different bodies.
    Correlation,
    /// A point's body is none of the template's arms, in an exact draft.
    Arm,
}

/// Why a draft that matched every member is not offered to the kernel.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Unfit
{
    /// Every arm of this point has one head, so a fresh run would not make it
    /// a point.
    Collapsed(EntryIndex),
    /// These two points take equal bodies on every member, so a fresh run
    /// would make them one.
    Merged(EntryIndex, EntryIndex),
    /// The predecessor of the first point equals the second point's body on
    /// every member, so a fresh run would read the second point there.
    Shadowed(EntryIndex, EntryIndex),
    /// The selected price refuses the drafted family, as it would the
    /// producer's.
    DoesNotPay(TemplateRefusal),
}

/// How a draft departs from its template.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DraftKind
{
    /// The template's own skeleton and a subset of its arms.
    Exact,
    /// The template's skeleton, with new bodies appended as arms.
    Widened(ArmCount),
    /// A rebased skeleton, with any new bodies appended as arms.
    Rebased(RepairCount, ArmCount),
}

/// Whether a draft may bind a body none of the template's arms holds.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Widening
{
    /// Only the template's own arms bind.
    Exact,
    /// A new body binds as a new arm.
    Widened,
}

/// Whether a draft may rebase its template on a rigid disagreement.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Rebasing
{
    /// A rigid disagreement misses the member.
    Never,
    /// A rigid disagreement rebases the template, up to [`REPAIRS`] times.
    Allowed,
}

/// Which walked members a finished draft covers.
#[derive(Clone, Copy, Debug)]
pub(super) enum Coverage<'members>
{
    /// Every member: the draft must be the schema a fresh run would emit.
    Whole,
    /// Only these members, the rest refused: a subfamily of the template,
    /// never claimed to be a fresh run's schema.
    Partial(&'members [MemberIndex]),
}

/// Why a template was not rebased.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Unrebased
{
    /// The member agrees with every rigid part the walk reaches.
    Unlocated,
    /// The binder to replace holds a point.
    Pointed,
}

/// Whether two pieces of content agree.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Agreement
{
    /// Equal constructors, payloads and children.
    Equal,
    /// Some constructor, payload or child shape differs.
    Different,
}

/// Whether a pattern node's subtree holds a point.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Freedom
{
    /// No point or predecessor below or at the node.
    PointFree,
    /// A point or predecessor below or at the node.
    Pointed,
}

/// The arm a member's body at a point selects.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Arm
{
    /// The template's arm under this guard.
    Template(GuardId),
    /// A body no template arm holds, by its coordinate in the member's arena;
    /// the arena interns content, so equal bodies share a coordinate.
    Fresh(TermId),
}

/// One point's binding while a member is walked.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Binding
{
    /// The walk has not reached the point yet.
    Unbound,
    /// Every occurrence reached so far selects this arm.
    Bound(Arm),
}

/// What walking one member found.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Walked
{
    /// Every point is bound and every rigid part agrees.
    Matched,
    /// The member misses for this reason.
    Missed(Miss),
    /// A rigid part disagrees; a rebase may repair it.
    Disagrees,
}

/// Whether a matched draft is the schema a fresh run would emit.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Fitness
{
    /// No departure from a fresh run's generalization is found.
    Fits,
    /// This departure is found.
    Unfit(Unfit),
}

/// What walking a whole family found.
#[expect(
    clippy::large_enum_variant,
    reason = "one per drafted family, matched at once; boxing a rebased template would \
              allocate per family to shrink the miss"
)]
pub(super) enum Walk<'template>
{
    /// Every member matched this template, the memo's or a rebased one.
    Matched
    {
        /// The template every member matched.
        template: Cow<'template, Template>,
        /// How the draft departs from the memo's template.
        kind: DraftKind,
    },
    /// The first member that missed, and why.
    Missed(Miss),
}

/// How a ready draft changes the template it was walked from.
#[expect(
    clippy::large_enum_variant,
    reason = "one per drafted family, applied at once; boxing a replacement would allocate \
              per family to shrink the renumbering"
)]
#[derive(Clone, Debug)]
pub(super) enum Revision
{
    /// The walked template's graph and sides, with its selected arms
    /// renumbered canonically: nothing was imported and nothing became
    /// unreachable.
    Kept(Vec<Entry>),
    /// A new template: new bodies imported, or unselected arms or replaced
    /// binders compacted away.
    Replaced(Template),
}

/// Whether every node of a graph is reachable from the roots a template
/// retains.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Tidiness
{
    /// Every node is reachable.
    Compact,
    /// Some node is not.
    Garbage,
}

/// A draft the kernel has not judged.
pub(super) struct Draft
{
    /// The canonical schema the kernel checks.
    pub proposal: Proposal,
    /// One choice per point for each covered member, member after member.
    pub choices: Vec<Choice>,
    /// The draft's sizes and member count.
    pub cost: FamilyCostReport,
    /// The template the proposal was emitted from, as a change to the walked
    /// one, kept when the kernel admits the draft.
    pub revision: Revision,
}

/// The outcome of finishing a walked family.
#[expect(
    clippy::large_enum_variant,
    reason = "one per drafted family, matched at once; boxing the draft would allocate per \
              family to shrink the departure"
)]
pub(super) enum Finished
{
    /// A draft fit to offer to the kernel.
    Ready(Draft),
    /// Why the matched family is not offered.
    Unfit(Unfit),
}

/// Whether a node has been reached from a template's retained roots.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Reach
{
    /// Not reached yet.
    Unreached,
    /// Reached.
    Reached,
}

/// Buffers a drafter reuses across members and families, so walking a member
/// imports nothing and, once sized, allocates nothing.
#[derive(Clone, Debug, Default)]
pub(super) struct Drafter
{
    /// Aligned pattern and arena coordinates still to compare.
    pending: Vec<(Id, TermId)>,
    /// The same, for one content comparison.
    compare: Vec<(Id, TermId)>,
    /// Classifier pairs still to compare.
    classifiers: Vec<(TypeId, TypeId)>,
    /// Classifier comparisons already decided in this draft.
    classifier_agreement: Vec<(TypeId, TypeId, Agreement)>,
    /// The arm each point body selected in this draft.
    selected: BTreeMap<(EntryIndex, TermId), Arm>,
    /// Point-free pattern subtrees already compared with arena terms.
    rigid: BTreeMap<(Id, TermId), Agreement>,
    /// Whether each pattern node of the walked template holds a point.
    freedom: Vec<Freedom>,
    /// Every member's binding at every point, member after member.
    bindings: Vec<Binding>,
    /// The canonical guard of each selected arm, by point.
    canonical: BTreeMap<(EntryIndex, Arm), GuardId>,
    /// Each point's arms of the walked template, by guard.
    arms: Vec<Vec<Id>>,
    /// Each point's guard to try first: the one after the last a body
    /// selected.
    cursor: Vec<GuardId>,
    /// Paths from a root to each node, for counting occurrences.
    paths: Vec<usize>,
    /// Whether each node of a finished draft's graph is reachable.
    reach: Vec<Reach>,
    /// Nodes still to mark reachable.
    reaching: Vec<Id>,
    /// Time the last finished draft spent importing new bodies.
    importing: Duration,
}

impl Drafter
{
    /// Time the last finished draft spent importing new bodies.
    ///
    /// # Specification
    /// trivial.
    pub(super) const fn importing(&self) -> Duration
    {
        self.importing
    }

    /// Clear every per-draft memory and size the bindings for one template.
    ///
    /// # Specification
    /// - ensures: no memory of an earlier draft remains; every node of
    ///   `template`'s graph is classified by whether its subtree holds a point;
    ///   each point's arms are listed by guard, the first guard tried first;
    ///   every member's binding at every point is unbound.
    /// - fails: Unbalanced for a malformed graph edge or a guard outside its
    ///   point's arms.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `StageError::Unbalanced`.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a stale memory from another template or family would
    ///   bind a body to the wrong arm, which the kernel's row check and the
    ///   fresh-run comparison observe over the edit-pair corpus.
    /// - witness: `template::tests::drafts_equal_fresh_runs_across_the_edit_traces`
    #[spec(ensures: |output| output.is_err() || (self.selected.is_empty() && self.rigid.is_empty()
        && self.freedom.len() == template.graph.end().0
        && self.arms.len() == template.entries.len()
        && self.cursor.len() == template.entries.len()
        && self.bindings.len() == usize::from(members).saturating_mul(template.entries.len())
        && self.bindings.iter().all(|binding| *binding == Binding::Unbound)))]
    fn reset(
        &mut self,
        template: &Template,
        members: MemberCount,
    ) -> Result<(), StageError>
    {
        self.classifier_agreement.clear();
        self.selected.clear();
        self.rigid.clear();
        self.freedom.clear();
        for index in 0 .. template.graph.end().0 {
            let node = template.graph.node(Id(index))?;
            let mut freedom = match node.head {
                | Head::Point(_) | Head::Predecessor => Freedom::Pointed,
                | _ => Freedom::PointFree,
            };
            for child in node.children.0.iter().flatten() {
                let below = self.freedom.get(child.0).ok_or(StageError::Unbalanced)?;
                if *below == Freedom::Pointed {
                    freedom = Freedom::Pointed;
                }
            }
            self.freedom.push(freedom);
        }
        self.arms.resize_with(template.entries.len(), Vec::new);
        for (column, entry) in self.arms.iter_mut().zip(&template.entries) {
            column.clear();
            column.resize(entry.arms.len(), Id(0));
            for (id, guard) in &entry.arms {
                let slot = column
                    .get_mut(usize::from(*guard))
                    .ok_or(StageError::Unbalanced)?;
                *slot = *id;
            }
        }
        self.cursor.clear();
        self.cursor
            .resize(template.entries.len(), GuardId::from(0_usize));
        self.bindings.clear();
        self.bindings.resize(
            usize::from(members).saturating_mul(template.entries.len()),
            Binding::Unbound,
        );
        Ok(())
    }
}

/// Compare a pattern classifier with an arena classifier.
///
/// # Specification
/// - ensures: `Equal` exactly when both rooted classifier trees have equal
///   constructors and leaf payloads; the verdict is remembered for the pair.
/// - fails: either side's lookup error for an absent classifier.
/// - panics: none.
///
/// # Errors
/// Returns `StageError::Unbalanced` or `StageError::UnknownType`.
///
/// # Adequacy
/// - hypothesis: L2 — a binder domain compared wrongly either misses a member a
///   fresh run admits or binds one whose sides the kernel then refuses; the
///   edit-pair corpus's binders observe both.
/// - witness: `template::tests::drafts_equal_fresh_runs_across_the_edit_traces`
#[spec(ensures: |output| output.as_ref().ok().is_none_or(|agreement|
    known.iter().any(|&(l, r, a)| l == left && r == right && a == *agreement)))]
fn classifiers_agree(
    graph: &Graph,
    left: TypeId,
    arena: &Arena,
    right: TypeId,
    stack: &mut Vec<(TypeId, TypeId)>,
    known: &mut Vec<(TypeId, TypeId, Agreement)>,
) -> Result<Agreement, StageError>
{
    if let Some(&(_, _, agreement)) = known.iter().find(|&&(l, r, _)| l == left && r == right) {
        return Ok(agreement);
    }
    stack.clear();
    stack.push((left, right));
    let mut agreement = Agreement::Equal;
    while let Some((pattern, member)) = stack.pop() {
        let pattern = graph.ty(pattern)?;
        let member = arena.ty(member)?;
        match (pattern, member) {
            | (Type::Arrow(domain, codomain), Type::Arrow(other_domain, other_codomain)) => {
                stack.extend([(codomain, other_codomain), (domain, other_domain)]);
            },
            | (Type::Lift(inner), Type::Lift(other)) => stack.push((inner, other)),
            | (leaf @ (Type::In(_) | Type::Universe(_) | Type::Nat(_)), other) if leaf == other => {
            },
            | _ => {
                agreement = Agreement::Different;
                break;
            },
        }
    }
    known.push((left, right, agreement));
    Ok(agreement)
}

/// Compare one pattern constructor with one arena constructor, without
/// their children.
///
/// # Specification
/// - ensures: `Equal` exactly when the constructor and every payload agree,
///   classifiers compared by content; a point or predecessor never agrees.
/// - fails: a classifier lookup error.
/// - panics: none.
///
/// # Errors
/// Returns `StageError::Unbalanced` or `StageError::UnknownType`.
///
/// # Adequacy
/// - hypothesis: L2/L3 — numerals, variables and binder domains that differ in
///   payload alone must miss; the edit-pair corpus differs by exactly these,
///   and the kernel's side check observes a wrongly matched member.
/// - witness: `template::tests::drafts_equal_fresh_runs_across_the_edit_traces`
#[spec(ensures: |output| output.as_ref().ok().is_none_or(|agreement|
    !matches!(head, Head::Point(_) | Head::Predecessor) || *agreement == Agreement::Different))]
fn heads_agree(
    graph: &Graph,
    head: Head,
    arena: &Arena,
    term: Term,
    drafter: &mut Drafter,
) -> Result<Agreement, StageError>
{
    let classifiers = match (head, term) {
        | (Head::Code(left), Term::Code(right))
        | (Head::Lambda(left), Term::Lambda(right, _))
        | (Head::Eliminate(left), Term::Eliminate(_, right)) => Some((left, right)),
        | _ => None,
    };
    if let Some((left, right)) = classifiers {
        let agreement = classifiers_agree(
            graph,
            left,
            arena,
            right,
            &mut drafter.classifiers,
            &mut drafter.classifier_agreement,
        )?;
        return Ok(agreement);
    }
    let equal = match (head, term) {
        | (Head::Variable(left), Term::Variable(right)) => left == right,
        | (Head::OuterNatural(left), Term::Natural(Stage::Outer, right)) => left == right,
        | (
            Head::InnerNatural(left_model, left),
            Term::Natural(Stage::Inner(right_model), right),
        ) => left_model == right_model && left == right,
        | (Head::Apply, Term::Apply(..))
        | (Head::Multiply, Term::Multiply(..))
        | (Head::Quote, Term::Quote(_))
        | (Head::Splice, Term::Splice(_))
        | (Head::Iterate, Term::Iterate(..)) => true,
        | _ => false,
    };
    Ok(if equal {
        Agreement::Equal
    }
    else {
        Agreement::Different
    })
}

/// Compare point-free pattern content with an arena term.
///
/// # Specification
/// - requires: `pattern`'s subtree holds no point or predecessor.
/// - ensures: `Equal` exactly when both rooted trees agree constructor for
///   constructor, payload for payload and child for child.
/// - fails: either side's lookup error.
/// - panics: none.
///
/// # Errors
/// Returns `StageError::Unbalanced`, `StageError::UnknownTerm` or
/// `StageError::UnknownType`.
///
/// # Adequacy
/// - hypothesis: L2 — an arm or rigid subterm compared wrongly binds a member
///   to the wrong arm or misses one a fresh run admits; the kernel's row check
///   and the fresh-run comparison observe both over the edit-pair corpus.
/// - witness: `template::tests::drafts_equal_fresh_runs_across_the_edit_traces`
#[spec(ensures: |output| output.as_ref().ok().is_none_or(|agreement|
    *agreement == Agreement::Different || graph.size(pattern).is_ok()))]
fn content_agrees(
    graph: &Graph,
    pattern: Id,
    arena: &Arena,
    term: TermId,
    drafter: &mut Drafter,
) -> Result<Agreement, StageError>
{
    let mut compare = core::mem::take(&mut drafter.compare);
    compare.clear();
    compare.push((pattern, term));
    let mut agreement = Agreement::Equal;
    while let Some((left, right)) = compare.pop() {
        let node = graph.node(left)?;
        let other = arena.term(right)?;
        let heads = heads_agree(graph, node.head, arena, other, drafter)?;
        if heads == Agreement::Different {
            agreement = Agreement::Different;
            break;
        }
        for (left, right) in node.children.0.iter().zip(other.children()) {
            match (*left, right) {
                | (Some(left), Child::Present(right)) => compare.push((left, right)),
                | (None, Child::Vacant) => {},
                | _ => agreement = Agreement::Different,
            }
        }
        if agreement == Agreement::Different {
            break;
        }
    }
    drafter.compare = compare;
    Ok(agreement)
}

/// Rebuild a pattern root with replaced subtrees, every replaced occurrence
/// at once.
///
/// # Specification
/// - requires: `known` maps each node to replace to its replacement.
/// - ensures: the returned node is `root` with every occurrence of a key of
///   `known` replaced by its value; `known` also maps every rebuilt node.
/// - fails: Unbalanced for a malformed edge; an intern refusal.
/// - panics: none.
/// - intension: each reachable node is rebuilt once.
///
/// # Errors
/// Returns `StageError::Unbalanced` or the graph's intern refusal.
///
/// # Adequacy
/// - hypothesis: L2 — a rebase that misses an occurrence on either side leaves
///   the join disagreeing with the members' targets, which the kernel refuses
///   and the fresh-run comparison observes on the body edits.
/// - witness: `template::tests::drafts_equal_fresh_runs_across_the_edit_traces`
#[spec(ensures: |output| output.as_ref().ok().is_none_or(|id| known.get(&root) == Some(id)))]
fn replace(
    graph: &mut Graph,
    root: Id,
    known: &mut BTreeMap<Id, Id>,
) -> Result<Id, StageError>
{
    let mut pending = Vec::from([(root, false)]);
    while let Some((id, ready)) = pending.pop() {
        if known.contains_key(&id) {
            continue;
        }
        let node = graph.node(id)?;
        if !ready {
            pending.push((id, true));
            pending.extend(
                node.children
                    .0
                    .iter()
                    .flatten()
                    .map(|child| (*child, false)),
            );
            continue;
        }
        let mut children = Children([None; 3]);
        for (source, target) in node.children.0.iter().zip(&mut children.0) {
            if let Some(source) = *source {
                let rebuilt = known.get(&source).ok_or(StageError::Unbalanced)?;
                *target = Some(*rebuilt);
            }
        }
        let rebuilt = graph.intern(Node {
            head: node.head,
            children,
        })?;
        known.insert(id, rebuilt);
    }
    let rebuilt = known.get(&root).ok_or(StageError::Unbalanced)?;
    Ok(*rebuilt)
}

/// Count each point's occurrences in a pattern's unfolded tree, bare and
/// under a predecessor.
///
/// # Specification
/// - requires: every node's children precede it, as interning orders them.
/// - ensures: one bare and one predecessor count per point, each the number of
///   such leaves in the unfolded tree below `root`, saturating.
/// - fails: Unbalanced for a malformed or forward edge or an unknown point.
/// - panics: none.
/// - intension: one pass down the coordinates from `root`, carrying each node's
///   number of paths from `root` to its children.
///
/// # Errors
/// Returns `StageError::Unbalanced`.
///
/// # Adequacy
/// - hypothesis: L2 — a miscounted occurrence misprices the drafted family,
///   which the drafted cost compared with a fresh run's on the edit-pair corpus
///   observes.
/// - witness: `template::tests::drafts_equal_fresh_runs_across_the_edit_traces`
#[spec(ensures: |output| output.as_ref().ok().is_none_or(|occurrences|
    occurrences.bare.len() == points.0 && occurrences.under.len() == points.0))]
fn occurrences(
    graph: &Graph,
    root: Id,
    points: PointCount,
    drafter: &mut Drafter,
) -> Result<Occurrences, StageError>
{
    let mut bare = alloc::vec![0_usize; points.0];
    let mut under = alloc::vec![0_usize; points.0];
    let paths = &mut drafter.paths;
    paths.clear();
    paths.resize(root.0.saturating_add(1), 0);
    let top = paths.last_mut().ok_or(StageError::Unbalanced)?;
    *top = 1;
    for index in (0 ..= root.0).rev() {
        let count = paths.get(index).copied().ok_or(StageError::Unbalanced)?;
        if count == 0 {
            continue;
        }
        let node = graph.node(Id(index))?;
        match node.head {
            | Head::Point(point) => {
                let slot = bare
                    .get_mut(usize::from(point))
                    .ok_or(StageError::Unbalanced)?;
                *slot = slot.saturating_add(count);
            },
            | Head::Predecessor => {
                let child = node.children.0.first().copied().flatten();
                let child = child.ok_or(StageError::Unbalanced)?;
                let Head::Point(point) = graph.node(child)?.head
                else {
                    return Err(StageError::Unbalanced);
                };
                let slot = under
                    .get_mut(usize::from(point))
                    .ok_or(StageError::Unbalanced)?;
                *slot = slot.saturating_add(count);
            },
            | _ => {
                for child in node.children.0.iter().flatten() {
                    if child.0 >= index {
                        return Err(StageError::Unbalanced);
                    }
                    let below = paths.get_mut(child.0).ok_or(StageError::Unbalanced)?;
                    *below = below.saturating_add(count);
                }
            },
        }
    }
    Ok(Occurrences { bare, under })
}

/// Whether every node of `graph` is reachable from `roots`.
///
/// # Specification
/// - ensures: `Compact` exactly when every node of `graph` is a root or a
///   descendant of one.
/// - fails: Unbalanced for a malformed edge or a root outside `graph`.
/// - panics: none.
///
/// # Errors
/// Returns `StageError::Unbalanced`.
///
/// # Adequacy
/// - hypothesis: L2 — a graph called compact while it holds an unreachable node
///   keeps garbage the next walk resets over, and one called garbage while
///   compact rebuilds it; the multi-program traces keep, widen, prune and
///   rebase, and the fresh-run comparison observes every held template.
/// - witness: `template::tests::drafts_equal_fresh_runs_across_the_edit_traces`
#[spec(ensures: |output| output.as_ref().ok().is_none_or(|tidiness| *tidiness == Tidiness::Garbage
    || drafter.reach.iter().take(graph.end().0).all(|reach| *reach == Reach::Reached)))]
fn tidiness(
    graph: &Graph,
    roots: &[Id],
    drafter: &mut Drafter,
) -> Result<Tidiness, StageError>
{
    let end = graph.end().0;
    drafter.reach.clear();
    drafter.reach.resize(end, Reach::Unreached);
    let mut reaching = core::mem::take(&mut drafter.reaching);
    reaching.clear();
    reaching.extend_from_slice(roots);
    let mut reached = 0_usize;
    let mut outcome = Ok(());
    while let Some(id) = reaching.pop() {
        let Some(reach) = drafter.reach.get_mut(id.0)
        else {
            outcome = Err(StageError::Unbalanced);
            break;
        };
        if *reach == Reach::Reached {
            continue;
        }
        *reach = Reach::Reached;
        reached = reached.saturating_add(1);
        match graph.node(id) {
            | Ok(node) => reaching.extend(node.children.0.iter().flatten()),
            | Err(error) => {
                outcome = Err(error);
                break;
            },
        }
    }
    drafter.reaching = reaching;
    outcome?;
    Ok(if reached == end {
        Tidiness::Compact
    }
    else {
        Tidiness::Garbage
    })
}

impl Template
{
    /// Walk one member's source against this template's peak.
    ///
    /// # Specification
    /// - requires: the drafter was reset for this template, and `member`
    ///   indexes its bindings.
    /// - ensures: `Matched` exactly when the member's decision is this
    ///   template's, every rigid part of the peak agrees with the source, and
    ///   every point binds one arm at every occurrence: one of this template's
    ///   arms, or under widening any body none of them holds. The member's
    ///   bindings are left in the drafter.
    /// - fails: a lookup error on either side.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `StageError::Unbalanced`, `StageError::UnknownTerm` or
    /// `StageError::UnknownType`.
    ///
    /// # Adequacy
    /// - hypothesis: L2/L3 — the kernel checks every drafted member's sides and
    ///   choices, and the fresh-run comparison checks the schema; the edit-pair
    ///   corpus exercises new arms, exponent and body edits and correlated
    ///   points.
    /// - witness: `template::tests::drafts_equal_fresh_runs_across_the_edit_traces`
    /// - witness: `template::tests::drafts_refuse_what_a_fresh_run_would_generalize_differently`
    #[spec(ensures: |output| output.as_ref().ok().is_none_or(|walked|
        *walked != Walked::Matched || (step.rule == self.rule
            && drafter.bindings.iter().skip(usize::from(member).saturating_mul(self.entries.len()))
                .take(self.entries.len()).all(|binding| *binding != Binding::Unbound))))]
    fn walk_member(
        &self,
        arena: &Arena,
        step: Step,
        member: MemberIndex,
        widening: Widening,
        drafter: &mut Drafter,
    ) -> Result<Walked, StageError>
    {
        if step.rule != self.rule {
            return Ok(Walked::Missed(Miss::Rule));
        }
        let points = self.entries.len();
        let start = usize::from(member).saturating_mul(points);
        let [peak, _] = self.sides;
        let mut pending = core::mem::take(&mut drafter.pending);
        pending.clear();
        pending.push((peak, step.source));
        let mut walked = Walked::Matched;
        while let Some((pattern, actual)) = pending.pop() {
            let freedom = drafter
                .freedom
                .get(pattern.0)
                .ok_or(StageError::Unbalanced)?;
            if *freedom == Freedom::PointFree {
                let agreement = match drafter.rigid.get(&(pattern, actual)) {
                    | Some(agreement) => *agreement,
                    | None => {
                        let agreement =
                            content_agrees(&self.graph, pattern, arena, actual, drafter)?;
                        drafter.rigid.insert((pattern, actual), agreement);
                        agreement
                    },
                };
                if agreement == Agreement::Different {
                    walked = Walked::Disagrees;
                    break;
                }
                continue;
            }
            let node = self.graph.node(pattern)?;
            if let Head::Point(point) = node.head {
                let arm = self.select(point, arena, actual, drafter)?;
                if let (Arm::Fresh(_), Widening::Exact) = (arm, widening) {
                    walked = Walked::Missed(Miss::Arm);
                    break;
                }
                let index = start.saturating_add(usize::from(point));
                let slot = drafter
                    .bindings
                    .get_mut(index)
                    .ok_or(StageError::Unbalanced)?;
                match *slot {
                    | Binding::Unbound => *slot = Binding::Bound(arm),
                    | Binding::Bound(bound) if bound == arm => {},
                    | Binding::Bound(_) => {
                        walked = Walked::Missed(Miss::Correlation);
                        break;
                    },
                }
                continue;
            }
            let term = arena.term(actual)?;
            let heads = heads_agree(&self.graph, node.head, arena, term, drafter)?;
            if heads == Agreement::Different {
                walked = Walked::Disagrees;
                break;
            }
            for (left, right) in node.children.0.iter().zip(term.children()) {
                match (*left, right) {
                    | (Some(left), Child::Present(right)) => pending.push((left, right)),
                    | (None, Child::Vacant) => {},
                    | _ => walked = Walked::Disagrees,
                }
            }
            if walked == Walked::Disagrees {
                break;
            }
        }
        drafter.pending = pending;
        let unbound = drafter
            .bindings
            .iter()
            .skip(start)
            .take(points)
            .any(|binding| *binding == Binding::Unbound);
        if walked == Walked::Matched && unbound {
            return Ok(Walked::Missed(Miss::Skeleton));
        }
        Ok(walked)
    }

    /// The arm one point body selects, remembered for the draft.
    ///
    /// # Specification
    /// - requires: the drafter was reset for this template.
    /// - ensures: the template arm whose content equals `actual`, by its guard,
    ///   or `actual` itself as a body no arm holds.
    /// - fails: a lookup error on either side.
    /// - panics: none.
    /// - intension: arms are tried from the guard after the last one a body at
    ///   this point selected, so members that select arms in the order the
    ///   template numbered them compare one arm each; distinct arms never share
    ///   content, so the order changes no selection.
    ///
    /// # Errors
    /// Returns `StageError::Unbalanced`, `StageError::UnknownTerm` or
    /// `StageError::UnknownType`.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a body bound to a wrong arm is refused by the
    ///   kernel's row check, and an arm duplicated as fresh changes the schema
    ///   the fresh-run comparison observes on the edit-pair corpus.
    /// - witness: `template::tests::drafts_equal_fresh_runs_across_the_edit_traces`
    #[spec(ensures: |output| output.as_ref().ok().is_none_or(|arm| match *arm {
        Arm::Template(guard) => self.entries.get(usize::from(point))
            .is_some_and(|entry| entry.arms.values().any(|held| *held == guard)),
        Arm::Fresh(body) => body == actual,
    }))]
    fn select(
        &self,
        point: EntryIndex,
        arena: &Arena,
        actual: TermId,
        drafter: &mut Drafter,
    ) -> Result<Arm, StageError>
    {
        if let Some(arm) = drafter.selected.get(&(point, actual)) {
            return Ok(*arm);
        }
        let index = usize::from(point);
        let count = drafter.arms.get(index).map_or(0, Vec::len);
        let start = drafter
            .cursor
            .get(index)
            .map_or(0, |guard| usize::from(*guard));
        let mut arm = Arm::Fresh(actual);
        for offset in 0 .. count {
            let guard = start
                .saturating_add(offset)
                .checked_rem(count)
                .ok_or(StageError::Unbalanced)?;
            let held = drafter
                .arms
                .get(index)
                .and_then(|column| column.get(guard))
                .copied()
                .ok_or(StageError::Unbalanced)?;
            let agreement = content_agrees(&self.graph, held, arena, actual, drafter)?;
            if agreement == Agreement::Equal {
                arm = Arm::Template(GuardId::from(guard));
                let cursor = drafter
                    .cursor
                    .get_mut(index)
                    .ok_or(StageError::Unbalanced)?;
                *cursor = GuardId::from(guard.saturating_add(1));
                break;
            }
        }
        drafter.selected.insert((point, actual), arm);
        Ok(arm)
    }

    /// Walk every member, rebasing on a rigid disagreement when allowed.
    ///
    /// # Specification
    /// - ensures: `Matched` exactly when every member matches the returned
    ///   template, this one or a rebase of it by at most [`REPAIRS`] binder
    ///   replacements, under the given widening; its bindings are left in the
    ///   drafter, and its kind counts the replacements and the distinct bodies
    ///   no template arm held. Otherwise the first member's miss, in member
    ///   order.
    /// - fails: a lookup error on either side.
    /// - panics: none.
    /// - intension: stops at the first member that misses; a rebase restarts
    ///   the walk at the first member.
    ///
    /// # Errors
    /// Returns `StageError::Unbalanced`, `StageError::UnknownTerm` or
    /// `StageError::UnknownType`.
    ///
    /// # Adequacy
    /// - hypothesis: L2/L3 — body edits on the edit-pair corpus need a rebase
    ///   and appended exponents need widening; a family with a missing member
    ///   must not match; the fresh-run comparison and the kernel observe every
    ///   matched family.
    /// - witness: `template::tests::drafts_equal_fresh_runs_across_the_edit_traces`
    /// - witness: `template::tests::drafts_refuse_what_a_fresh_run_would_generalize_differently`
    #[spec(ensures: |output| output.as_ref().ok().is_none_or(|walk| match *walk {
        Walk::Matched { ref template, kind } => template.rule == self.rule
            && template.entries.len() == self.entries.len()
            && match kind {
                DraftKind::Exact => true,
                DraftKind::Widened(fresh) => widening == Widening::Widened && fresh.0 > 0,
                DraftKind::Rebased(repairs, _) => rebasing == Rebasing::Allowed
                    && repairs.0 > 0 && repairs <= REPAIRS,
            },
        Walk::Missed(miss) => widening == Widening::Exact || miss != Miss::Arm,
    }))]
    pub(super) fn walk(
        &self,
        arena: &Arena,
        members: &[Step],
        widening: Widening,
        rebasing: Rebasing,
        drafter: &mut Drafter,
    ) -> Result<Walk<'_>, StageError>
    {
        let mut template = Cow::Borrowed(self);
        let mut repairs = RepairCount(0);
        'restart: loop {
            drafter.reset(&template, MemberCount::from(members.len()))?;
            for (member, step) in members.iter().enumerate() {
                let walked = template.walk_member(
                    arena,
                    *step,
                    MemberIndex::from(member),
                    widening,
                    drafter,
                )?;
                match walked {
                    | Walked::Matched => {},
                    | Walked::Missed(miss) => return Ok(Walk::Missed(miss)),
                    | Walked::Disagrees => {
                        if rebasing == Rebasing::Never || repairs >= REPAIRS {
                            return Ok(Walk::Missed(Miss::Skeleton));
                        }
                        let rebased = template.rebase(arena, step.source, drafter)?;
                        let Maybe::Present(rebased) = rebased
                        else {
                            return Ok(Walk::Missed(Miss::Skeleton));
                        };
                        template = Cow::Owned(rebased);
                        repairs = RepairCount(repairs.0.saturating_add(1));
                        continue 'restart;
                    },
                }
            }
            break;
        }
        let mut fresh = BTreeSet::new();
        for binding in &drafter.bindings {
            if let Binding::Bound(Arm::Fresh(body)) = *binding {
                fresh.insert(body);
            }
        }
        let fresh = ArmCount(fresh.len());
        let kind = if repairs.0 > 0 {
            DraftKind::Rebased(repairs, fresh)
        }
        else if fresh.0 > 0 {
            DraftKind::Widened(fresh)
        }
        else {
            DraftKind::Exact
        };
        Ok(Walk::Matched { template, kind })
    }

    /// Walk every member exactly, keeping each that matches.
    ///
    /// # Specification
    /// - ensures: the members, by index and in order, that match this template
    ///   with its own arms; their bindings are left in the drafter.
    /// - fails: a lookup error on either side.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `StageError::Unbalanced`, `StageError::UnknownTerm` or
    /// `StageError::UnknownType`.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a member kept that does not match is refused by the
    ///   kernel's row check; one dropped that matches shrinks the admitted
    ///   subfamily the work-bound fallback reports.
    /// - witness: `template::tests::a_work_bound_family_admits_its_template_subfamily`
    #[spec(ensures: |output| output.as_ref().ok().is_none_or(|matched|
        matched.len() <= members.len() && matched.windows(2).all(|pair|
            pair.first().zip(pair.get(1)).is_some_and(|(a, b)| a < b))))]
    pub(super) fn walk_partial(
        &self,
        arena: &Arena,
        members: &[Step],
        drafter: &mut Drafter,
    ) -> Result<Vec<MemberIndex>, StageError>
    {
        drafter.reset(self, MemberCount::from(members.len()))?;
        let mut matched = Vec::new();
        for (member, step) in members.iter().enumerate() {
            let member = MemberIndex::from(member);
            let walked = self.walk_member(arena, *step, member, Widening::Exact, drafter)?;
            if walked == Walked::Matched {
                matched.push(member);
            }
        }
        Ok(matched)
    }

    /// Replace the binder enclosing a member's first rigid disagreement by the
    /// member's own subterm, on both sides.
    ///
    /// # Specification
    /// - requires: the drafter was reset for this template.
    /// - ensures: present exactly when the depth-first walk of the peak against
    ///   `source` finds a rigid disagreement and the innermost binder strictly
    ///   enclosing it, or the disagreement itself outside any binder, holds no
    ///   point; then that node is replaced by the member's subterm at every
    ///   occurrence on both sides, and the points and arms are unchanged.
    /// - fails: a lookup error on either side; an intern refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `StageError::Unbalanced`, `StageError::UnknownTerm`,
    /// `StageError::UnknownType` or the graph's intern refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L2/L3 — the body edits change a binder below every
    ///   family's peak and join; a replacement on one side only, or of the
    ///   wrong node, leaves sides the kernel refuses or a schema the fresh run
    ///   does not emit.
    /// - witness: `template::tests::drafts_equal_fresh_runs_across_the_edit_traces`
    #[spec(ensures: |output| output.as_ref().ok().is_none_or(|rebased| match *rebased {
        Maybe::Present(ref template) => template.rule == self.rule
            && template.entries.len() == self.entries.len(),
        Maybe::Absent(_) => true,
    }))]
    fn rebase(
        &self,
        arena: &Arena,
        source: TermId,
        drafter: &mut Drafter,
    ) -> Result<Maybe<Self, Unrebased>, StageError>
    {
        let [peak, join] = self.sides;
        let mut trail: Vec<(Id, TermId)> = Vec::new();
        let mut pending = Vec::from([(peak, source, 0_usize)]);
        let mut disagreement = None;
        while let Some((pattern, actual, depth)) = pending.pop() {
            trail.truncate(depth);
            trail.push((pattern, actual));
            let node = self.graph.node(pattern)?;
            if let Head::Point(_) = node.head {
                continue;
            }
            let term = arena.term(actual)?;
            let heads = heads_agree(&self.graph, node.head, arena, term, drafter)?;
            let mut pairs = Vec::new();
            let mut agreement = heads;
            for (left, right) in node.children.0.iter().zip(term.children()) {
                match (*left, right) {
                    | (Some(left), Child::Present(right)) => pairs.push((left, right)),
                    | (None, Child::Vacant) => {},
                    | _ => agreement = Agreement::Different,
                }
            }
            if agreement == Agreement::Different {
                disagreement = Some(trail.len());
                break;
            }
            let depth = depth.saturating_add(1);
            pending.extend(
                pairs
                    .into_iter()
                    .rev()
                    .map(|(left, right)| (left, right, depth)),
            );
        }
        let Some(length) = disagreement
        else {
            return Ok(Maybe::Absent(Unrebased::Unlocated));
        };
        let mut chosen = trail.last().copied().ok_or(StageError::Unbalanced)?;
        for &(pattern, actual) in trail.iter().take(length.saturating_sub(1)).rev() {
            let node = self.graph.node(pattern)?;
            if let Head::Lambda(_) = node.head {
                chosen = (pattern, actual);
                break;
            }
        }
        let (pattern, actual) = chosen;
        let freedom = drafter
            .freedom
            .get(pattern.0)
            .ok_or(StageError::Unbalanced)?;
        if *freedom == Freedom::Pointed {
            return Ok(Maybe::Absent(Unrebased::Pointed));
        }
        let mut graph = self.graph.clone();
        let imported = graph.import(arena, &[actual])?;
        let replacement = imported.first().copied().ok_or(StageError::Unbalanced)?;
        let mut known = BTreeMap::from([(pattern, replacement)]);
        let peak = replace(&mut graph, peak, &mut known)?;
        let join = replace(&mut graph, join, &mut known)?;
        Ok(Maybe::Present(Self {
            graph,
            sides: [peak, join],
            rule: self.rule,
            entries: self.entries.clone(),
            cost: self.cost,
        }))
    }

    /// Number the selected arms canonically, import new bodies, refuse what a
    /// fresh run would not emit or the price would not pay, and emit.
    ///
    /// # Specification
    /// - requires: every covered member's bindings are in the drafter, from a
    ///   walk of this template.
    /// - ensures: `Ready` carries the canonical proposal over this skeleton and
    ///   the arms the covered members select, numbered by first selection in
    ///   member order; one choice per point for each covered member, in order;
    ///   and the template it was emitted from, with this draft's cost. A whole
    ///   draft is ready only with no departure from a fresh run's
    ///   generalization; every ready draft passes the selected price. The time
    ///   spent importing new bodies is left in the drafter.
    /// - fails: a lookup error on either side; an intern refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `StageError::Unbalanced`, `StageError::UnknownTerm`,
    /// `StageError::UnknownType` or the graph's intern refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L2/L3 — drafted and fresh proposals and costs compare
    ///   equal over the edit-pair corpus; a collapsed, merged or shadowed
    ///   point, and a family the price refuses, are refused before the kernel.
    /// - witness: `template::tests::drafts_equal_fresh_runs_across_the_edit_traces`
    /// - witness: `template::tests::drafts_refuse_what_a_fresh_run_would_generalize_differently`
    /// - witness: `template::tests::a_work_bound_family_admits_its_template_subfamily`
    #[spec(ensures: |output| output.as_ref().ok().is_none_or(|finished| match *finished {
        Finished::Ready(ref draft) => draft.proposal.equation.rule == self.rule
            && draft.proposal.arms.len() == self.entries.len()
            && draft.choices.len() == usize::from(draft.cost.members)
                .saturating_mul(self.entries.len())
            && match gate {
                PriceGate::Unmemoized => price_family(draft.cost.template_size,
                    draft.cost.plain_size).is_ok(),
                PriceGate::Memoized => true,
            },
        Finished::Unfit(_) => true,
    }))]
    pub(super) fn finish<C>(
        &self,
        arena: &Arena,
        members: &[Step],
        coverage: Coverage<'_>,
        drafter: &mut Drafter,
        gate: PriceGate,
        clock: &mut C,
    ) -> Result<Finished, StageError>
    where
        C: Clock,
    {
        let points = self.entries.len();
        let covered: Vec<usize> = match coverage {
            | Coverage::Whole => (0 .. members.len()).collect(),
            | Coverage::Partial(matched) => {
                matched.iter().map(|member| usize::from(*member)).collect()
            },
        };
        let mut order: Vec<Vec<Arm>> = core::iter::repeat_with(Vec::new).take(points).collect();
        let mut choices = Vec::with_capacity(covered.len().saturating_mul(points));
        drafter.canonical.clear();
        for member in &covered {
            let start = member.saturating_mul(points);
            for (index, column) in order.iter_mut().enumerate() {
                let binding = drafter
                    .bindings
                    .get(start.saturating_add(index))
                    .ok_or(StageError::Unbalanced)?;
                let Binding::Bound(arm) = *binding
                else {
                    return Err(StageError::Unbalanced);
                };
                let guard = match drafter.canonical.entry((EntryIndex::from(index), arm)) {
                    | btree_map::Entry::Occupied(known) => *known.get(),
                    | btree_map::Entry::Vacant(slot) => {
                        let guard = GuardId::from(column.len());
                        column.push(arm);
                        *slot.insert(guard)
                    },
                };
                choices.push(Choice {
                    point: Point(index),
                    guard: Guard(usize::from(guard)),
                });
            }
        }
        let fresh: Vec<TermId> = order
            .iter()
            .flatten()
            .filter_map(|arm| match *arm {
                | Arm::Fresh(body) => Some(body),
                | Arm::Template(_) => None,
            })
            .collect();
        let mut graph = Cow::Borrowed(&self.graph);
        let begun = clock.now();
        let mut imported = Vec::new();
        if !fresh.is_empty() {
            imported = graph.to_mut().import(arena, &fresh)?;
        }
        drafter.importing = clock.now().saturating_sub(begun);
        let mut next = imported.iter();
        let mut arms: Vec<Vec<Id>> = Vec::with_capacity(points);
        for (entry, column) in self.entries.iter().zip(&order) {
            let held = entry.ordered()?;
            let mut ids = Vec::with_capacity(column.len());
            for arm in column {
                let id = match *arm {
                    | Arm::Template(guard) => held.get(usize::from(guard)),
                    | Arm::Fresh(_) => next.next(),
                };
                let id = id.ok_or(StageError::Unbalanced)?;
                ids.push(*id);
            }
            arms.push(ids);
        }
        let [peak, join] = self.sides;
        let source = occurrences(&graph, peak, PointCount(points), drafter)?;
        let target = occurrences(&graph, join, PointCount(points), drafter)?;
        if matches!(coverage, Coverage::Whole) {
            let fitness = departure(&graph, &target, &arms, &choices)?;
            if let Fitness::Unfit(unfit) = fitness {
                return Ok(Finished::Unfit(unfit));
            }
        }
        let peak_size = usize::from(graph.size(peak)?);
        let join_size = usize::from(graph.size(join)?);
        let mut sizes: Vec<Vec<usize>> = Vec::with_capacity(points);
        let mut template_size = peak_size.saturating_add(join_size).saturating_add(1);
        for column in &arms {
            let mut column_sizes = Vec::with_capacity(column.len());
            for arm in column {
                let size = usize::from(graph.size(*arm)?);
                template_size = template_size.saturating_add(size).saturating_add(1);
                column_sizes.push(size);
            }
            sizes.push(column_sizes);
        }
        let Occurrences {
            bare: source_bare, ..
        } = source;
        let Occurrences {
            bare: target_bare,
            under: target_under,
        } = target;
        let source_points: usize = source_bare
            .iter()
            .fold(0, |sum, count| sum.saturating_add(*count));
        let target_points =
            target_bare
                .iter()
                .zip(&target_under)
                .fold(0_usize, |sum, (bare, under)| {
                    sum.saturating_add(*bare)
                        .saturating_add(under.saturating_mul(2))
                });
        let source_base = peak_size
            .checked_sub(source_points)
            .ok_or(StageError::Unbalanced)?;
        let target_base = join_size
            .checked_sub(target_points)
            .ok_or(StageError::Unbalanced)?;
        let mut plain_size = 0_usize;
        for (row, _) in covered.iter().enumerate() {
            let mut source = source_base;
            let mut target = target_base;
            for point in 0 .. points {
                let choice = choices
                    .get(row.saturating_mul(points).saturating_add(point))
                    .ok_or(StageError::Unbalanced)?;
                let size = sizes
                    .get(point)
                    .and_then(|column| column.get(choice.guard.0))
                    .ok_or(StageError::Unbalanced)?;
                let bare = source_bare.get(point).ok_or(StageError::Unbalanced)?;
                source = source.saturating_add(bare.saturating_mul(*size));
                let bare = target_bare.get(point).ok_or(StageError::Unbalanced)?;
                let under = target_under.get(point).ok_or(StageError::Unbalanced)?;
                target = target
                    .saturating_add(bare.saturating_mul(*size))
                    .saturating_add(*under);
            }
            plain_size = plain_size
                .saturating_add(1)
                .saturating_add(source)
                .saturating_add(target);
        }
        let template_size = NodeCount::from(template_size);
        let plain_size = NodeCount::from(plain_size);
        let triples = TripleCount::from(arms.iter().map(Vec::len).sum::<usize>().max(1));
        let pays = match gate {
            | PriceGate::Unmemoized => price_family(template_size, plain_size).is_ok(),
            | PriceGate::Memoized => {
                price_family_memoized(template_size, plain_size, triples, template_size).is_ok()
            },
        };
        if !pays {
            return Ok(Finished::Unfit(Unfit::DoesNotPay(
                TemplateRefusal::DoesNotPay {
                    template_size,
                    plain_size,
                },
            )));
        }
        let proposal = graph.admission_proposal(self.sides, self.rule, &arms)?;
        let members = MemberCount::from(covered.len());
        let cost = FamilyCostReport {
            members,
            plain_size,
            template_size,
            expansion_factor: ExpansionFactor::from(
                usize::from(plain_size)
                    .checked_div(usize::from(template_size))
                    .unwrap_or_default(),
            ),
            plain_replayed_steps: ReplayStepCount::from(covered.len()),
            ..FamilyCostReport::default()
        };
        let mut retained = Vec::from(self.sides);
        retained.extend(arms.iter().flatten().copied());
        let tidiness = tidiness(&graph, &retained, drafter)?;
        let revision = match (tidiness, graph) {
            | (Tidiness::Compact, Cow::Borrowed(_)) => Revision::Kept(self.renumbered(&arms)),
            | (Tidiness::Compact, Cow::Owned(graph)) => Revision::Replaced(Self {
                graph,
                sides: self.sides,
                rule: self.rule,
                entries: self.renumbered(&arms),
                cost,
            }),
            | (Tidiness::Garbage, graph) => Revision::Replaced(self.rebuilt(&graph, &arms, cost)?),
        };
        Ok(Finished::Ready(Draft {
            proposal,
            choices,
            cost,
            revision,
        }))
    }

    /// Each point's arms, numbered by their order in `arms`.
    ///
    /// # Specification
    /// - requires: `arms` holds one column per point of this template.
    /// - ensures: one entry per point, its point kept, mapping each arm of its
    ///   column to the arm's index there.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a held template renumbered wrongly selects the wrong
    ///   guard for the next draft's members, which the kernel's row check and
    ///   the fresh-run comparison observe on the multi-program traces.
    /// - witness: `template::tests::drafts_equal_fresh_runs_across_the_edit_traces`
    #[spec(ensures: |output| output.len() == self.entries.len().min(arms.len())
        && output.iter().zip(arms).all(|(entry, column)| column.iter().enumerate()
            .all(|(guard, arm)| entry.arms.get(arm) == Some(&GuardId::from(guard)))))]
    fn renumbered(
        &self,
        arms: &[Vec<Id>],
    ) -> Vec<Entry>
    {
        self.entries
            .iter()
            .zip(arms)
            .map(|(entry, column)| Entry {
                point: entry.point,
                arms: column
                    .iter()
                    .enumerate()
                    .map(|(guard, arm)| (*arm, GuardId::from(guard)))
                    .collect(),
            })
            .collect()
    }

    /// A template over the part of `graph` this template's sides and `arms`
    /// reach, with those arms numbered in order.
    ///
    /// # Specification
    /// - requires: `graph` holds this template's sides and every arm of `arms`,
    ///   one column per point.
    /// - ensures: the returned graph holds exactly the nodes the sides and arms
    ///   reach, the sides and arms translated into it; the rule, the points and
    ///   `cost` are kept.
    /// - fails: Unbalanced for a malformed edge or a root outside `graph`; an
    ///   intern refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `StageError::Unbalanced` or the graph's intern refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a node lost or mistranslated in the rebuild changes
    ///   the next draft's proposal, which the fresh-run comparison observes on
    ///   the multi-program and body-edit traces.
    /// - witness: `template::tests::drafts_equal_fresh_runs_across_the_edit_traces`
    #[spec(ensures: |output| output.as_ref().ok().is_none_or(|template|
        template.rule == self.rule && template.cost == cost
            && template.entries.len() == self.entries.len().min(arms.len())))]
    fn rebuilt(
        &self,
        graph: &Graph,
        arms: &[Vec<Id>],
        cost: FamilyCostReport,
    ) -> Result<Self, StageError>
    {
        let mut retained = Vec::from(self.sides);
        retained.extend(arms.iter().flatten().copied());
        let (compact, map) = graph.compact(&retained)?;
        let translate = |id: &Id| map.get(id).copied().ok_or(StageError::Unbalanced);
        let mut columns = Vec::with_capacity(arms.len());
        for column in arms {
            let column = column
                .iter()
                .map(translate)
                .collect::<Result<Vec<Id>, _>>()?;
            columns.push(column);
        }
        let [peak, join] = self.sides;
        let sides = [translate(&peak)?, translate(&join)?];
        let entries = self.renumbered(&columns);
        Ok(Self {
            graph: compact,
            sides,
            rule: self.rule,
            entries,
            cost,
        })
    }

    /// This template over only the nodes its sides and arms reach.
    ///
    /// # Specification
    /// - ensures: the same sides, arms, guards, rule and cost over a graph
    ///   holding nothing they do not reach; its proposal is this template's.
    /// - fails: Unbalanced for a malformed edge or entry; an intern refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `StageError::Unbalanced` or the graph's intern refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every produced template the memo holds is compacted,
    ///   and its proposal is compared with a fresh run's after each admitted
    ///   family of the edit-pair corpus.
    /// - witness: `template::tests::drafts_equal_fresh_runs_across_the_edit_traces`
    #[spec(ensures: |output| output.as_ref().ok().is_none_or(|template|
        template.rule == self.rule && template.cost == self.cost
            && template.entries.len() == self.entries.len()))]
    pub(super) fn compacted(&self) -> Result<Self, StageError>
    {
        let arms = self
            .entries
            .iter()
            .map(Entry::ordered)
            .collect::<Result<Vec<Vec<Id>>, _>>()?;
        self.rebuilt(&self.graph, &arms, self.cost)
    }
}

impl Revision
{
    /// Apply this revision to the template it was drafted from.
    ///
    /// # Specification
    /// - ensures: a kept revision replaces `template`'s arms and cost and keeps
    ///   its graph and sides; a replacement replaces it whole.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the held template after each admitted draft is
    ///   compared with a fresh run's over the multi-program traces, which keep
    ///   and replace templates both.
    /// - witness: `template::tests::drafts_equal_fresh_runs_across_the_edit_traces`
    #[spec(ensures: |()| template.cost == cost)]
    pub(super) fn apply(
        self,
        template: &mut Template,
        cost: FamilyCostReport,
    )
    {
        match self {
            | Self::Kept(entries) => {
                template.entries = entries;
                template.cost = cost;
            },
            | Self::Replaced(replacement) => {
                *template = replacement;
                template.cost = cost;
            },
        }
    }
}

/// Find where a drafted generalization departs from a fresh run's.
///
/// # Specification
/// - requires: `choices` holds one choice per point for each member, member
///   after member, each indexing its point's arms; `target` counts the join's
///   occurrences.
/// - ensures: `Unfit` names a point whose arms share one head, two points whose
///   bodies agree on every member, or a predecessor whose numeral is a point's
///   body on every member; otherwise `Fits`.
/// - fails: Unbalanced for a malformed edge or choice.
/// - panics: none.
///
/// # Errors
/// Returns `StageError::Unbalanced`.
///
/// # Adequacy
/// - hypothesis: L2/L3 — each departure is constructed directly and must
///   refuse, and the edit-pair corpus's drafts must pass and equal the fresh
///   run.
/// - witness: `template::tests::drafts_refuse_what_a_fresh_run_would_generalize_differently`
/// - witness: `template::tests::drafts_equal_fresh_runs_across_the_edit_traces`
#[spec(ensures: |output| output.as_ref().ok().is_none_or(|fitness| match *fitness {
    Fitness::Unfit(Unfit::Collapsed(point)) => arms.get(usize::from(point)).is_some(),
    _ => true,
}))]
fn departure(
    graph: &Graph,
    target: &Occurrences,
    arms: &[Vec<Id>],
    choices: &[Choice],
) -> Result<Fitness, StageError>
{
    let points = arms.len();
    for (index, column) in arms.iter().enumerate() {
        let mut heads = BTreeSet::new();
        for arm in column {
            let node = graph.node(*arm)?;
            heads.insert(node.head);
        }
        if heads.len() < 2 {
            return Ok(Fitness::Unfit(Unfit::Collapsed(EntryIndex::from(index))));
        }
    }
    let body = |row: usize, point: usize| -> Result<Id, StageError> {
        let choice = choices
            .get(row.saturating_mul(points).saturating_add(point))
            .ok_or(StageError::Unbalanced)?;
        let id = arms
            .get(point)
            .and_then(|column| column.get(choice.guard.0))
            .ok_or(StageError::Unbalanced)?;
        Ok(*id)
    };
    let rows = choices.len().checked_div(points).unwrap_or_default();
    for first in 0 .. points {
        for second in first.saturating_add(1) .. points {
            let mut merged = true;
            for row in 0 .. rows {
                let left = body(row, first)?;
                let right = body(row, second)?;
                if left != right {
                    merged = false;
                    break;
                }
            }
            if merged {
                return Ok(Fitness::Unfit(Unfit::Merged(
                    EntryIndex::from(first),
                    EntryIndex::from(second),
                )));
            }
        }
    }
    for (point, count) in target.under.iter().enumerate() {
        if *count == 0 {
            continue;
        }
        for other in (0 .. points).filter(|other| *other != point) {
            let mut shadowed = true;
            for row in 0 .. rows {
                let upper = body(row, point)?;
                let lower = body(row, other)?;
                let upper = graph.node(upper)?;
                let lower = graph.node(lower)?;
                let below = match upper.head {
                    | Head::OuterNatural(Natural(value)) => value.checked_sub(1).map(Natural),
                    | _ => None,
                };
                if below.is_none_or(|below| lower.head != Head::OuterNatural(below)) {
                    shadowed = false;
                    break;
                }
            }
            if shadowed {
                return Ok(Fitness::Unfit(Unfit::Shadowed(
                    EntryIndex::from(point),
                    EntryIndex::from(other),
                )));
            }
        }
    }
    Ok(Fitness::Fits)
}
