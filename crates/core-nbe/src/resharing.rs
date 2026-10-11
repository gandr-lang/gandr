//! **Process re-sharing**: the key the conversion machine re-shares a goal on,
//! and the support edges each re-shared goal's answer rests on.
//!
//! # Re-sharing
//!
//! Courant and Leroy (§6.3) observe that convertibility processes are
//! duplicated wherever evaluations are shared — a pair whose two components
//! are one node decomposes into two goals over the same pair — and that the
//! duplication is exponential on recursive functions. The machine looks a
//! fresh goal's [`GoalSupport`] up in a
//! [`CheckMemo`](gandr_kernel_check_memo::CheckMemo) before starting it: a hit
//! hands back the process already comparing that pair, and the decomposition
//! waits on it instead of starting a copy. The memo lives for one run, because
//! its outcomes are that run's process ids.
//!
//! # The key
//!
//! A [`GoalSupport`] is the whole input of a goal the machine starts fresh: the
//! two sides, as weak heads in hand or as closures to open, and the binder
//! level. Nothing else enters, because a fresh goal has no frozen constant and
//! an empty unfolding chain, and the definitions and settings are the run's.
//! Agreement is identity of sides and level, so two goals over equal content
//! under distinct ids miss rather than meet: a miss costs a recomputation and
//! never a wrong answer. The digest is folded from content — a rigid side's
//! guard, a flexible neutral's head — so agreeing supports always share a
//! bucket.
//!
//! # Support edges
//!
//! Each memo entry records what its answer was read from: the definitions its
//! own derivation unfolded and the entries it rests on. They are the edges a
//! revision of the definitions validates before the entry is reused. An
//! acceptance is keyed on its winning derivation, which alone decides it; a
//! refusal is keyed on the union over the alternatives of every choice it
//! refutes through, because each alternative had to fail. A decomposition
//! refuted at one premise rests on that premise alone: the other premises are
//! conjuncts, not alternatives. An entry names an entry it rests on by one edge
//! rather than inheriting that entry's edges, so the edges a revision validates
//! grow with the derivation's distinct goals rather than with the square of
//! its depth.

use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_check_memo::ContentAgreement;
use gandr_kernel_check_memo::ContentDigest;
use gandr_kernel_check_memo::DigestWord;
use gandr_kernel_check_memo::MemoActivity;
use gandr_kernel_check_memo::MemoKey;
use gandr_kernel_check_memo::OrderedMemo;
use gandr_kernel_term::ConstantIndex;

use crate::arena::CompClosureId;
use crate::arena::DomainArena;
use crate::arena::DomainFault;
use crate::conv::ConversionFault;
use crate::domain::BinderLevel;
use crate::domain::DomainComp;
use crate::domain::DomainValue;
use crate::domain::Glued;
use crate::domain::NeutralHead;
use crate::guard::ContentHash;
use crate::guard::Guard;
use crate::machine::ProcessId;
use crate::rules::Settled;

/// The memo the conversion machine re-shares its goals through on the engine
/// path; [`NullMemo`](gandr_kernel_check_memo::NullMemo) is the memoless side
/// of the differential.
pub type ResharingMemo = OrderedMemo<GoalSupport, ProcessId>;

/// The accounting plane of a goal support: the machine keeps one.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ResharingPlane
{
    /// The conversion machine's goals.
    Goals,
}

/// The two sides of a goal the machine starts fresh.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum SupportSides
{
    /// Two weak heads in hand.
    Heads(Glued, Glued),
    /// Two closures, each to be opened under the fresh variable at the
    /// support's level.
    Opened(CompClosureId, CompClosureId),
    /// Two captured computations, entered without introducing a binder.
    Closed(CompClosureId, CompClosureId),
}

/// The whole input of a goal the machine starts fresh: its sides and the
/// binder level it starts at.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct GoalSupport
{
    /// The sides compared.
    sides: SupportSides,
    /// For two heads, the first binder level neither mentions; for two
    /// closures, the level they are opened at.
    level: BinderLevel,
    /// The digest folded from the sides' content and the level.
    digest: ContentDigest,
}

/// Which polarity a side stands in.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Polarity
{
    /// A value.
    Value,
    /// A computation.
    Computation,
}

/// The content of one side a digest is folded from.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum SideContent
{
    /// A side whose guard is rigid: the guard's hash, which already folds the
    /// polarity in through the node kind.
    Rigid(ContentHash),
    /// A flexible neutral, by its head.
    Neutral(Polarity, NeutralHead),
    /// A flexible former.
    Former(Polarity),
    /// A closure to be opened.
    Opened,
    /// A captured computation entered without a fresh binder.
    Closed,
}

impl GoalSupport
{
    /// The support of a goal comparing `sides` from `level`.
    ///
    /// # Specification
    /// - requires: every node `sides` names lives in `domain`.
    /// - ensures: a support that agrees with another exactly when both name the
    ///   same sides at the same level, with a digest folded from the sides'
    ///   content: a rigid side's guard, a flexible neutral's polarity and head,
    ///   a flexible former's polarity, and the level.
    /// - provides: the key the machine recalls and records a fresh goal under.
    /// - fails: [`ConversionFault::Domain`] for a node that does not resolve.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — repeated live supports agree, equal content at
    ///   different ids does not, and changing the level or polarity changes the
    ///   input; truncation refuses opened closures. Ignoring a key component or
    ///   accepting an absent closure changes agreement or construction.
    /// - witness: `resharing::tests::support_identity_and_digest_survive_forcing_without_conflating_inputs`
    /// - witness: `resharing::tests::opened_support_refuses_truncated_closures`
    ///
    /// # Errors
    /// - [`ConversionFault::Domain`] — a node does not resolve.
    #[inline]
    #[spec(ensures: |ret| {
        let resolving = match sides {
            SupportSides::Heads(left, right) => side_content(domain, left).is_ok() && side_content(domain, right).is_ok(),
            SupportSides::Opened(left,right) | SupportSides::Closed(left,right) => domain.comp_closure(left).is_some() && domain.comp_closure(right).is_some(),
        };
        if resolving { ret.as_ref().is_ok_and(|support| support.sides == sides && support.level == level) }
        else { ret == Err(ConversionFault::Domain(DomainFault::Dangling)) }
    })]
    pub(crate) fn new(
        domain: &DomainArena,
        sides: SupportSides,
        level: BinderLevel,
    ) -> Result<Self, ConversionFault>
    {
        let (left, right) = match sides {
            | SupportSides::Heads(left, right) => {
                let left = side_content(domain, left)?;
                let right = side_content(domain, right)?;
                (left, right)
            },
            | SupportSides::Opened(left, right) | SupportSides::Closed(left, right) => {
                domain
                    .comp_closure(left)
                    .ok_or(ConversionFault::Domain(DomainFault::Dangling))?;
                if left != right {
                    domain
                        .comp_closure(right)
                        .ok_or(ConversionFault::Domain(DomainFault::Dangling))?;
                }
                let content = match sides {
                    | SupportSides::Closed(..) => SideContent::Closed,
                    | _ => SideContent::Opened,
                };
                (content, content)
            },
        };
        let high = DigestWord::from(u64::from(ContentHash::of(&left)));
        let low = DigestWord::from(u64::from(ContentHash::of(&(right, level))));
        Ok(Self {
            sides,
            level,
            digest: ContentDigest::new(high, low),
        })
    }

    /// The sides compared.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn sides(&self) -> SupportSides
    {
        self.sides
    }

    /// The binder level the goal starts at.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn level(&self) -> BinderLevel
    {
        self.level
    }
}

impl MemoKey for GoalSupport
{
    type Plane = ResharingPlane;

    /// [`ResharingPlane::Goals`], the machine's one plane.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn plane(&self) -> Self::Plane
    {
        ResharingPlane::Goals
    }

    /// The digest folded at construction.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: equal for agreeing supports, because agreeing supports name
    ///   the same nodes at the same level, whose content folds to the same
    ///   words.
    /// - provides: the bucket a recall scans.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — repeated supports and a support rebuilt after forcing
    ///   the same neutral retain one digest, while identity agreement still
    ///   distinguishes equal-content nodes and levels; changing a stable key
    ///   word loses the shared bucket.
    /// - witness: `resharing::tests::support_identity_and_digest_survive_forcing_without_conflating_inputs`
    /// - witness: `machine::tests::re_sharing_runs_one_goal_per_distinct_pair`
    #[inline]
    #[spec(ensures: |ret| ret == self.digest)]
    fn digest(&self) -> ContentDigest
    {
        self.digest
    }

    /// Agree exactly when both name the same sides at the same level.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`ContentAgreement::Agree`] exactly when the sides and the
    ///   level are equal, so either goal is the other's whole input;
    ///   [`ContentAgreement::Differ`] otherwise, including for equal content
    ///   under distinct ids, which costs a recomputation and never an answer.
    /// - provides: the deciding comparison, an equivalence because it is
    ///   equality.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decision surface is the equality, separated by a
    ///   decomposition whose two premises name one pair, which meets one
    ///   process, against a run whose pairs are all distinct, which starts one
    ///   process per pair; process counts are asserted exactly against the
    ///   memoless run.
    /// - witness: `machine::tests::re_sharing_runs_one_goal_per_distinct_pair`
    /// - witness: `machine::tests::the_memo_never_moves_a_verdict`
    #[inline]
    #[spec(ensures: |ret| matches!(ret, ContentAgreement::Agree) == (self.sides == other.sides && self.level == other.level))]
    fn agreement(
        &self,
        other: &Self,
    ) -> ContentAgreement
    {
        if self.sides == other.sides && self.level == other.level {
            ContentAgreement::Agree
        }
        else {
            ContentAgreement::Differ
        }
    }
}

/// The content of `glued` a digest folds.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the guard's hash for a rigid side; the polarity and head for a
///   flexible neutral; the polarity for a flexible former.
/// - provides: the per-side half of a support's digest.
/// - fails: [`ConversionFault::Domain`] for a node that does not resolve.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — rigid equal-content values may share a digest without
///   agreeing by identity, while forcing a flexible neutral preserves its key
///   and value/computation polarity remains distinct; including the changing
///   unfolding face or discarding polarity changes those observations.
/// - witness: `resharing::tests::support_identity_and_digest_survive_forcing_without_conflating_inputs`
/// - witness: `machine::tests::the_memo_never_moves_a_verdict`
///
/// # Errors
/// - [`ConversionFault::Domain`] — a node does not resolve.
#[spec(ensures: |ret| match glued {
    Glued::Value(id) => match domain.value_guard(id) {
        Ok(Guard::Rigid(hash)) => ret == Ok(SideContent::Rigid(hash)),
        Ok(Guard::Flexible) => match domain.value(id) {
            Some(&DomainValue::Neutral { neutral, .. }) => domain.neutral(neutral).map_or_else(
                || ret == Err(ConversionFault::Domain(DomainFault::Dangling)),
                |node| ret == Ok(SideContent::Neutral(Polarity::Value, node.head()))),
            Some(_) => ret == Ok(SideContent::Former(Polarity::Value)),
            None => ret == Err(ConversionFault::Domain(DomainFault::Dangling)),
        },
        Err(fault) => ret == Err(ConversionFault::Domain(fault)),
    },
    Glued::Computation(id) => match domain.comp_guard(id) {
        Ok(Guard::Rigid(hash)) => ret == Ok(SideContent::Rigid(hash)),
        Ok(Guard::Flexible) => match domain.computation(id) {
            Some(&DomainComp::Neutral { neutral, .. }) => domain.neutral(neutral).map_or_else(
                || ret == Err(ConversionFault::Domain(DomainFault::Dangling)),
                |node| ret == Ok(SideContent::Neutral(Polarity::Computation, node.head()))),
            Some(_) => ret == Ok(SideContent::Former(Polarity::Computation)),
            None => ret == Err(ConversionFault::Domain(DomainFault::Dangling)),
        },
        Err(fault) => ret == Err(ConversionFault::Domain(fault)),
    },
})]
fn side_content(
    domain: &DomainArena,
    glued: Glued,
) -> Result<SideContent, ConversionFault>
{
    let (guard, polarity, neutral) = match glued {
        | Glued::Value(value) => {
            let guard = domain.value_guard(value).map_err(ConversionFault::Domain)?;
            let neutral = match domain.value(value) {
                | Some(&DomainValue::Neutral { neutral, .. }) => Some(neutral),
                | Some(_) => None,
                | None => return Err(ConversionFault::Domain(DomainFault::Dangling)),
            };
            (guard, Polarity::Value, neutral)
        },
        | Glued::Computation(comp) => {
            let guard = domain.comp_guard(comp).map_err(ConversionFault::Domain)?;
            let neutral = match domain.computation(comp) {
                | Some(&DomainComp::Neutral { neutral, .. }) => Some(neutral),
                | Some(_) => None,
                | None => return Err(ConversionFault::Domain(DomainFault::Dangling)),
            };
            (guard, Polarity::Computation, neutral)
        },
    };
    if let Guard::Rigid(hash) = guard {
        return Ok(SideContent::Rigid(hash));
    }
    let Some(neutral) = neutral
    else {
        return Ok(SideContent::Former(polarity));
    };
    let held = domain
        .neutral(neutral)
        .ok_or(ConversionFault::Domain(DomainFault::Dangling))?;
    Ok(SideContent::Neutral(polarity, held.head()))
}

/// How many support edges a run's memo entries hold.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct EdgeCount(usize);

impl From<EdgeCount> for usize
{
    /// How many edges `count` counts.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: EdgeCount) -> Self
    {
        count.0
    }
}

/// The support edges a run's memo entries hold, by the verdict each entry
/// answered: what a revision of the definitions validates before reusing them.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SupportEdges
{
    /// The edges of the entries that answered convertible.
    acceptance: EdgeCount,
    /// The edges of the entries that answered not convertible.
    refusal: EdgeCount,
}

impl SupportEdges
{
    /// The edges of the entries that answered convertible, each keyed on its
    /// winning derivation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn acceptance(&self) -> EdgeCount
    {
        self.acceptance
    }

    /// The edges of the entries that answered not convertible, each keyed on
    /// the union over the alternatives it refuted through.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn refusal(&self) -> EdgeCount
    {
        self.refusal
    }
}

/// One thing an answer was read from.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Edge
{
    /// A definition the derivation unfolded.
    Unfolding(ConstantIndex),
    /// A memo entry the derivation rests on.
    Entry(ProcessId),
}

/// Whether a process is a memo entry.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Standing
{
    /// It is: a goal started fresh and recorded.
    Entry,
    /// It is not: a choice's alternative or a channel.
    Inner,
}

/// One process's support: whether it is an entry, and the edges its answer
/// was read from.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Consulted
{
    /// Whether the process is a memo entry.
    standing: Standing,
    /// The edges, each once.
    edges: BTreeSet<Edge>,
}

/// The support edges of one run, one set per process, held only while the
/// memo is active.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Supports
{
    /// Whether the memo answers; nothing is stored when it does not.
    activity: MemoActivity,
    /// One support per process, by process id.
    store: Vec<Consulted>,
    /// The entries' edges counted so far, by verdict.
    totals: SupportEdges,
}

impl Supports
{
    /// An empty store for a memo of `activity`.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn new(activity: MemoActivity) -> Self
    {
        Self {
            activity,
            store: Vec::new(),
            totals: SupportEdges {
                acceptance: EdgeCount(0_usize),
                refusal: EdgeCount(0_usize),
            },
        }
    }

    /// The entries' edges counted so far.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: zero in both directions for an inactive memo; otherwise, per
    ///   verdict, the sum over the entries that answered it of the edges each
    ///   holds.
    /// - provides: the edges-per-revision measurement a run reports.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — inactive operations keep both counts zero; active
    ///   entries count inherited inner edges and referenced entry edges in the
    ///   verdict that settled them. Counting inactive work, inheriting an entry
    ///   transitively or mixing verdicts changes the totals.
    /// - witness: `machine::tests::support_store_refusals_preserve_state_and_inactive_operations_do_nothing`
    /// - witness: `machine::tests::support_entries_reference_entries_and_inherit_inner_edges`
    #[spec(ensures: |ret| ret.acceptance.0 == self.totals.acceptance.0
        && ret.refusal.0 == self.totals.refusal.0
        && (!matches!(self.activity, MemoActivity::Inactive)
            || ret.acceptance.0 == 0 && ret.refusal.0 == 0))]
    pub(crate) const fn totals(&self) -> SupportEdges
    {
        self.totals
    }

    /// Open the support of a process just started, as an inner process.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: when active, the store holds one more support, inner and
    ///   empty; otherwise nothing changes.
    /// - provides: the per-process slot, so the store stays indexed by process
    ///   id.
    /// - fails: [`ConversionFault::MachineInvariant`] when active and `process`
    ///   is not the next id the store expects.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the next process opens once; a duplicate or skipped
    ///   id refuses without changing the store, while inactive operation stores
    ///   nothing. Accepting an out-of-order id or mutating on refusal changes
    ///   the state.
    /// - witness: `machine::tests::support_store_refusals_preserve_state_and_inactive_operations_do_nothing`
    ///
    /// # Errors
    /// - [`ConversionFault::MachineInvariant`] — the ids and the store
    ///   disagree.
    #[spec(
        captures: entry_length = self.store.len(),
        ensures: |ret| if matches!(self.activity, MemoActivity::Inactive) {
            ret == Ok(()) && self.store.len() == entry_length
        } else if usize::from(process) == entry_length {
            ret == Ok(()) && self.store.len().checked_sub(1) == Some(entry_length)
                && self.store.last().is_some_and(|slot| slot.standing == Standing::Inner && slot.edges.is_empty())
        } else { ret == Err(ConversionFault::MachineInvariant) && self.store.len() == entry_length },
    )]
    pub(crate) fn open(
        &mut self,
        process: ProcessId,
    ) -> Result<(), ConversionFault>
    {
        if matches!(self.activity, MemoActivity::Inactive) {
            return Ok(());
        }
        if usize::from(process) != self.store.len() {
            return Err(ConversionFault::MachineInvariant);
        }
        self.store.push(Consulted {
            standing: Standing::Inner,
            edges: BTreeSet::new(),
        });
        Ok(())
    }

    /// The support of `process`, mutably.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the support at `process`.
    /// - provides: the one checked write of the store.
    /// - fails: [`ConversionFault::MachineInvariant`] for a process never
    ///   opened.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — entering or recording an unfolding for an unopened
    ///   process refuses without modifying existing support; an opened process
    ///   records its edge. Resolving the wrong slot or accepting a missing one
    ///   changes state or totals.
    /// - witness: `machine::tests::support_store_refusals_preserve_state_and_inactive_operations_do_nothing`
    ///
    /// # Errors
    /// - [`ConversionFault::MachineInvariant`] — no support for `process`.
    #[spec(
        captures: entry_present = usize::from(process) < self.store.len(),
        ensures: |ret| ret.is_ok() == entry_present
            && ret.as_ref().err().is_none_or(|fault| *fault == ConversionFault::MachineInvariant),
    )]
    fn consulted_mut(
        &mut self,
        process: ProcessId,
    ) -> Result<&mut Consulted, ConversionFault>
    {
        self.store
            .get_mut(usize::from(process))
            .ok_or(ConversionFault::MachineInvariant)
    }

    /// Mark `process` a memo entry.
    ///
    /// # Specification
    /// - requires: `process` was opened.
    /// - ensures: when active, `process` is an entry, so its edges are counted
    ///   when it answers and a parent names it by one edge; otherwise nothing
    ///   changes.
    /// - provides: the entry half of the support.
    /// - fails: [`ConversionFault::MachineInvariant`] when active and the
    ///   process was never opened.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — an entered process contributes its own edge count
    ///   when it settles and is represented by one edge in its parent; an inner
    ///   process is instead inherited. Losing the standing transition changes
    ///   both totals.
    /// - witness: `machine::tests::support_entries_reference_entries_and_inherit_inner_edges`
    /// - witness: `machine::tests::support_store_refusals_preserve_state_and_inactive_operations_do_nothing`
    ///
    /// # Errors
    /// - [`ConversionFault::MachineInvariant`] — no support for `process`.
    #[spec(ensures: |ret| if matches!(self.activity, MemoActivity::Inactive) { ret == Ok(()) }
        else { self.store.get(usize::from(process)).map_or_else(
            || ret == Err(ConversionFault::MachineInvariant),
            |slot| ret == Ok(()) && slot.standing == Standing::Entry) })]
    pub(crate) fn enter(
        &mut self,
        process: ProcessId,
    ) -> Result<(), ConversionFault>
    {
        if matches!(self.activity, MemoActivity::Inactive) {
            return Ok(());
        }
        let consulted = self.consulted_mut(process)?;
        consulted.standing = Standing::Entry;
        Ok(())
    }

    /// Record that `process` unfolded `constant`.
    ///
    /// # Specification
    /// - requires: `process` was opened.
    /// - ensures: when active, `process`'s edges hold the unfolding; otherwise
    ///   nothing changes.
    /// - provides: the definitional half of the support.
    /// - fails: [`ConversionFault::MachineInvariant`] when active and the
    ///   process was never opened.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — repeating one unfolding contributes one edge, an
    ///   inner child passes that edge to its parent, and an unopened process
    ///   refuses; duplicating, dropping or attributing the edge to another
    ///   process changes the counted support.
    /// - witness: `machine::tests::support_entries_reference_entries_and_inherit_inner_edges`
    /// - witness: `machine::tests::support_store_refusals_preserve_state_and_inactive_operations_do_nothing`
    ///
    /// # Errors
    /// - [`ConversionFault::MachineInvariant`] — no support for `process`.
    #[spec(ensures: |ret| if matches!(self.activity, MemoActivity::Inactive) { ret == Ok(()) }
        else { self.store.get(usize::from(process)).map_or_else(
            || ret == Err(ConversionFault::MachineInvariant),
            |slot| ret == Ok(()) && slot.edges.contains(&Edge::Unfolding(constant))) })]
    pub(crate) fn unfolded(
        &mut self,
        process: ProcessId,
        constant: ConstantIndex,
    ) -> Result<(), ConversionFault>
    {
        if matches!(self.activity, MemoActivity::Inactive) {
            return Ok(());
        }
        let consulted = self.consulted_mut(process)?;
        consulted.edges.insert(Edge::Unfolding(constant));
        Ok(())
    }

    /// Record that `process` answered `settled`, read from `basis`.
    ///
    /// # Specification
    /// - requires: `basis` is what the answer rests on: the winning children of
    ///   an acceptance, the refuted premise of a refuted decomposition, or
    ///   every alternative of a refuted choice.
    /// - ensures: when active, `process`'s edges gain one edge per entry in
    ///   `basis` and every edge of each inner process in `basis` as it stands;
    ///   an entry's edges are then added to the total for its verdict.
    ///   Otherwise nothing changes.
    /// - provides: the keying of both directions in one place.
    /// - fails: [`ConversionFault::MachineInvariant`] when active and a process
    ///   was never opened.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a parent inherits an inner process once even when
    ///   repeated in its basis, references an entry by one edge rather than its
    ///   unfolded definitions, and charges only its own verdict. Missing basis
    ///   or process ids refuse without changing totals; transitive entry
    ///   inheritance or duplicate edges changes the measured counts.
    /// - witness: `machine::tests::support_entries_reference_entries_and_inherit_inner_edges`
    /// - witness: `machine::tests::support_store_refusals_preserve_state_and_inactive_operations_do_nothing`
    /// - witness: `machine::tests::an_acceptance_is_keyed_on_its_winning_derivation`
    /// - witness: `machine::tests::a_refusal_is_keyed_on_the_union_over_its_branches`
    ///
    /// # Errors
    /// - [`ConversionFault::MachineInvariant`] — no support for a process.
    #[spec(
        captures: entry_totals = self.totals,
        ensures: |ret| if matches!(self.activity, MemoActivity::Inactive) {
            ret == Ok(()) && self.totals == entry_totals
        } else if let Some(slot) = self.store.get(usize::from(process)) {
            let complete_basis = basis.iter().all(|&child| self.store.get(usize::from(child)).is_some());
            if complete_basis {
                ret == Ok(()) && basis.iter().all(|&child| self.store.get(usize::from(child)).is_some_and(|source|
                    match source.standing {
                        Standing::Entry => slot.edges.contains(&Edge::Entry(child)),
                        Standing::Inner => source.edges.is_subset(&slot.edges),
                    })) && match (slot.standing, settled) {
                        (Standing::Entry, Settled::Convertible) =>
                            self.totals.acceptance.0 == entry_totals.acceptance.0.saturating_add(slot.edges.len())
                                && self.totals.refusal == entry_totals.refusal,
                        (Standing::Entry, Settled::NotConvertible) =>
                            self.totals.refusal.0 == entry_totals.refusal.0.saturating_add(slot.edges.len())
                                && self.totals.acceptance == entry_totals.acceptance,
                        (Standing::Inner, _) => self.totals == entry_totals,
                    }
            } else { ret == Err(ConversionFault::MachineInvariant) && self.totals == entry_totals }
        } else { ret == Err(ConversionFault::MachineInvariant) && self.totals == entry_totals },
    )]
    pub(crate) fn settle(
        &mut self,
        process: ProcessId,
        settled: Settled,
        basis: &[ProcessId],
    ) -> Result<(), ConversionFault>
    {
        if matches!(self.activity, MemoActivity::Inactive) {
            return Ok(());
        }
        let mut gathered = BTreeSet::new();
        for &child in basis {
            let held = self
                .store
                .get(usize::from(child))
                .ok_or(ConversionFault::MachineInvariant)?;
            match held.standing {
                | Standing::Entry => {
                    gathered.insert(Edge::Entry(child));
                },
                | Standing::Inner => gathered.extend(held.edges.iter().copied()),
            }
        }
        let consulted = self
            .store
            .get_mut(usize::from(process))
            .ok_or(ConversionFault::MachineInvariant)?;
        consulted.edges.append(&mut gathered);
        if consulted.standing == Standing::Entry {
            let total = match settled {
                | Settled::Convertible => &mut self.totals.acceptance,
                | Settled::NotConvertible => &mut self.totals.refusal,
            };
            total.0 = total.0.saturating_add(consulted.edges.len());
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests
{
    use alloc::vec::Vec;

    use gandr_core_term::CoreArena;
    use gandr_kernel_check_memo::ContentAgreement;
    use gandr_kernel_check_memo::MemoKey as _;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::GlobalIndex;

    use super::BinderLevel;
    use super::ConversionFault;
    use super::DomainArena;
    use super::DomainFault;
    use super::GoalSupport;
    use super::SupportSides;
    use crate::Environment;

    #[test]
    fn opened_support_refuses_truncated_closures()
    {
        let mut core = CoreArena::new();
        let value = core.value_unit();
        let body = core.computation_return(value);
        let mut domain = DomainArena::new();
        let floor = domain.watermark();
        let closure = domain.comp_closure_node(body, Environment::new());
        let sides = SupportSides::Opened(closure, closure);
        assert!(GoalSupport::new(&domain, sides, BinderLevel::FLOOR).is_ok());
        let first_only = domain.watermark();
        let second = domain.comp_closure_node(body, Environment::new());
        assert!(
            GoalSupport::new(
                &domain,
                SupportSides::Opened(closure, second),
                BinderLevel::FLOOR
            )
            .is_ok()
        );
        domain.truncate_to(first_only);
        for pair in [
            SupportSides::Opened(closure, second),
            SupportSides::Opened(second, closure),
        ] {
            assert_eq!(
                Err(ConversionFault::Domain(DomainFault::Dangling)),
                GoalSupport::new(&domain, pair, BinderLevel::FLOOR)
            );
        }
        domain.truncate_to(floor);
        assert_eq!(
            Err(ConversionFault::Domain(DomainFault::Dangling)),
            GoalSupport::new(&domain, sides, BinderLevel::FLOOR)
        );
    }

    #[test]
    fn support_identity_and_digest_survive_forcing_without_conflating_inputs()
    {
        let mut domain = DomainArena::new();
        let floor = domain.watermark();
        let first = domain.value_unit(crate::TermFace::Reduced);
        let second = domain.value_unit(crate::TermFace::Reduced);
        let level = BinderLevel::FLOOR;
        let forward = GoalSupport::new(
            &domain,
            SupportSides::Heads(crate::Glued::Value(first), crate::Glued::Value(second)),
            level,
        )
        .expect("both values live");
        let reverse = GoalSupport::new(
            &domain,
            SupportSides::Heads(crate::Glued::Value(second), crate::Glued::Value(first)),
            level,
        )
        .expect("both values live");
        assert_eq!(
            forward.digest(),
            reverse.digest(),
            "equal rigid contents share a bucket"
        );
        assert_eq!(
            ContentAgreement::Differ,
            forward.agreement(&reverse),
            "a bucket does not equate distinct inputs"
        );
        let raised = GoalSupport::new(&domain, forward.sides(), BinderLevel::from(1_u32))
            .expect("the values also live at the higher level");
        assert_eq!(ContentAgreement::Differ, forward.agreement(&raised));
        let repeated =
            GoalSupport::new(&domain, forward.sides(), level).expect("the same input remains live");
        assert_eq!(ContentAgreement::Agree, forward.agreement(&repeated));
        assert_eq!(forward.digest(), repeated.digest());

        let neutral = domain
            .neutral_node(
                crate::NeutralHead::Constant(ConstantIndex::from(0_usize)),
                Vec::new(),
                crate::Unfolding::Unforced(GlobalIndex::from(0_u32)),
            )
            .expect("a constant may unfold");
        let value = domain
            .value_neutral(neutral, crate::TermFace::Reduced)
            .expect("an empty spine is a value");
        let computation = domain.comp_neutral(neutral, crate::CompTermFace::Reduced);
        let value_sides =
            SupportSides::Heads(crate::Glued::Value(value), crate::Glued::Value(value));
        let comp_sides = SupportSides::Heads(
            crate::Glued::Computation(computation),
            crate::Glued::Computation(computation),
        );
        let before =
            GoalSupport::new(&domain, value_sides, level).expect("the value neutral lives");
        let before_comp =
            GoalSupport::new(&domain, comp_sides, level).expect("the computation neutral lives");
        assert_eq!(
            ContentAgreement::Differ,
            before.agreement(&before_comp),
            "polarity is part of the input"
        );
        domain
            .force_neutral(neutral, crate::Glued::Value(first))
            .expect("the body was not forced before");
        let after = GoalSupport::new(&domain, value_sides, level)
            .expect("forcing preserves the value node");
        let after_comp = GoalSupport::new(&domain, comp_sides, level)
            .expect("forcing preserves the computation node");
        assert_eq!(ContentAgreement::Agree, before.agreement(&after));
        assert_eq!(before.digest(), after.digest());
        assert_eq!(ContentAgreement::Agree, before_comp.agreement(&after_comp));
        assert_eq!(before_comp.digest(), after_comp.digest());

        domain.truncate_to(floor);
        for sides in [forward.sides(), value_sides, comp_sides] {
            assert_eq!(
                Err(ConversionFault::Domain(DomainFault::Dangling)),
                GoalSupport::new(&domain, sides, level)
            );
        }
    }
}
