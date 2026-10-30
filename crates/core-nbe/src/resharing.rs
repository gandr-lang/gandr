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
//! never a wrong answer. The digest is folded from the same sides and level,
//! so agreeing supports always share a bucket, and supports that differ share
//! one only by a hash collision.
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
//!
//! # Process re-sharing in the machine
//!
//! Courant and Leroy observe (§6.3) that convertibility processes are
//! duplicated wherever evaluations are shared: a pair whose two components are
//! one node decomposes into two goals over one pair, and on a recursive
//! function the copies multiply at every level. `decide` therefore looks every
//! goal it starts fresh — the root and each premise of a decomposition — up in
//! a `CheckMemo` before starting it, and a pending hit waits on the process
//! already comparing that pair. An answered hit reuses its result: a
//! decomposition polls immediately when a recalled refutation can settle it or
//! no pending child remains to wake it. A delayed decomposition whose premises
//! have already agreed therefore completes instead of reporting a false cycle.
//! Witness: `machine::tests::completed_premises_wake_a_later_decomposition`.
//! Choice alternatives are not re-shared, because they carry frozen constants
//! and an unfolding chain that are part of their input.
//!
//! **The key.** A `GoalSupport` is a fresh goal's whole input: its two sides,
//! as weak heads in hand or as closures opened under the fresh variable, and
//! the binder level. Agreement is identity of sides and level, and the digest
//! is folded from the same sides and level, so agreeing supports share a
//! bucket and a recall scans only the supports that collide with it. Two goals
//! over equal content under distinct ids miss rather than meet, which costs a
//! recomputation and never an answer. A digest folded from content put every
//! such copy in one bucket, and each recall scanned them all: the `shared-tree`
//! row holds `2^k` copies at depth `k`, and its recalls grew with their square.
//! Alternatives: content agreement, which would need structural equality over
//! flexible nodes — the comparison the machine exists to make — and
//! hash-consing the domain arena, which moves the decision into every mint.
//! Reversal: a measured family whose duplicated goals arrive under distinct
//! ids.
//!
//! Constructing a goal support resolves both sides, including closures to be
//! opened. Equal ids do not make a missing closure valid: truncating either
//! closure yields `ConversionFault::Domain(DomainFault::Dangling)`. The
//! boundary is witnessed by
//! `resharing::tests::opened_support_refuses_truncated_closures`;
//! `resharing::tests::support_identity_and_digest_survive_forcing_without_conflating_inputs`
//! pins the identity agreement and its digest as a neutral is forced.
//!
//! **The edges.** Each entry records what its answer was read from: the
//! definitions its own derivation unfolded, including through its alternatives,
//! and the entries it rests on, each named by one edge rather than by
//! inheriting that entry's edges. They are what a revision of the definitions
//! validates before reusing the entry, so the run reports their count by
//! verdict, and the measure is edges validated per revision rather than hit
//! rate: a key that gave every entry an edge to every definition below it would
//! be quadratic in the derivation's depth while every hit stayed correct. An
//! acceptance is keyed on its winning derivation, which alone decides it; a
//! refusal is keyed on the union over the alternatives of the choices it
//! refutes through, because every alternative had to fail, while a refuted
//! decomposition rests on its negative premise alone, its other premises being
//! conjuncts rather than alternatives. Alternatives: the union for both
//! directions, which pays the refusal side's density on acceptances the winning
//! derivation already decides; and gating the memo on a proof that acceptances
//! keyed this way stay sound under revision, which is research the machine need
//! not wait for, because a wrong key degrades to a miss and the differential
//! below catches a key that moves a verdict. Reversal: a measurement where the
//! refusal side's edges swallow the memo's payoff, or a soundness argument that
//! changes the key's shape.
//!
//! **One run, one memo.** The memo's outcomes are process ids, so `decide`
//! builds it empty for each run; nothing persists. `NullMemo` starts every goal
//! afresh and compiles the memo interaction away, so the memoless machine is
//! the same function at another type parameter, and the zero-drift differential
//! runs both on every catalogue pair and asserts one verdict. Re-sharing can
//! close a wait cycle — a goal whose premise is the goal itself — that the
//! memoless machine would unroll until its budget; a run whose queue empties
//! with the root still pending has only such cycles left, and declines with
//! `DeclineReason::Cycle`.

use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_check_memo::ContentAgreement;
use gandr_kernel_check_memo::ContentDigest;
use gandr_kernel_check_memo::DigestWord;
use gandr_kernel_check_memo::HashedMemo;
use gandr_kernel_check_memo::MemoActivity;
use gandr_kernel_check_memo::MemoKey;
use gandr_kernel_conversion_trace::ConversionSide;
use gandr_kernel_term::ConstantIndex;

use crate::arena::CompClosureId;
use crate::arena::DomainArena;
use crate::arena::DomainFault;
use crate::conv::ConversionFault;
use crate::domain::BinderLevel;
use crate::domain::DomainComp;
use crate::domain::DomainValue;
use crate::domain::Glued;
use crate::guard::ContentHash;
use crate::guard::Guard;
use crate::machine::ProcessId;
use crate::rules::Settled;

/// The memo the conversion machine re-shares its goals through on the engine
/// path; [`NullMemo`](gandr_kernel_check_memo::NullMemo) is the memoless side
/// of the differential.
pub type ResharingMemo = HashedMemo<GoalSupport, ProcessId>;

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
    /// Two closures opened under this many fresh binders: List cell branches
    /// under two, split bodies under their arity.
    OpenedUnder(
        CompClosureId,
        CompClosureId,
        gandr_core_term::ComponentCount,
    ),
    /// A closure on the named side, to be opened under the fresh variable at
    /// the support's level, against a weak head in hand on the other that
    /// mentions that variable.
    OpenedBeside(ConversionSide, CompClosureId, Glued),
    /// A captured computation on the named side, entered without introducing
    /// a binder, against a weak head in hand on the other.
    EnteredBeside(ConversionSide, CompClosureId, Glued),
}

/// The whole input of a goal the machine starts fresh: its sides and the
/// binder level it starts at.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct GoalSupport
{
    /// The sides compared.
    sides: SupportSides,
    /// For two heads, the first binder level neither mentions; for a closure,
    /// the level it is opened at.
    level: BinderLevel,
    /// The digest folded from the sides' content and the level.
    digest: ContentDigest,
}

impl GoalSupport
{
    /// The support of a goal comparing `sides` from `level`.
    ///
    /// # Specification
    /// - requires: every node `sides` names lives in `domain`.
    /// - ensures: a support that agrees with another exactly when both name the
    ///   same sides at the same level, with a digest folded from those sides
    ///   and that level.
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
            SupportSides::Heads(left, right) => resolves(domain, left).is_ok() && resolves(domain, right).is_ok(),
            SupportSides::Opened(left, right) | SupportSides::Closed(left, right) | SupportSides::OpenedUnder(left, right, _) => domain.comp_closure(left).is_some() && domain.comp_closure(right).is_some(),
            SupportSides::OpenedBeside(_, closure, head) | SupportSides::EnteredBeside(_, closure, head) => domain.comp_closure(closure).is_some() && resolves(domain, head).is_ok(),
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
        match sides {
            SupportSides::Heads(left, right) => {
                resolves(domain, left)?;
                resolves(domain, right)?;
            },
            SupportSides::OpenedBeside(_, closure, head)
            | SupportSides::EnteredBeside(_, closure, head) => {
                domain
                    .comp_closure(closure)
                    .ok_or(ConversionFault::Domain(DomainFault::Dangling))?;
                resolves(domain, head)?;
            },
            SupportSides::Opened(left, right)
            | SupportSides::Closed(left, right)
            | SupportSides::OpenedUnder(left, right, _) => {
                domain
                    .comp_closure(left)
                    .ok_or(ConversionFault::Domain(DomainFault::Dangling))?;
                if left != right {
                    domain
                        .comp_closure(right)
                        .ok_or(ConversionFault::Domain(DomainFault::Dangling))?;
                }
            },
        }
        let high = DigestWord::from(u64::from(ContentHash::of(&sides)));
        let low = DigestWord::from(u64::from(ContentHash::of(&(sides, level))));
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
    ///   the same sides at the same level, which fold to the same words.
    /// - provides: the bucket a recall scans.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — repeated supports and a support rebuilt after forcing
    ///   the same neutral retain one digest, while supports over equal content
    ///   at distinct ids or levels fall in distinct buckets; changing a stable
    ///   key word loses the shared bucket.
    /// - witness: `resharing::tests::support_identity_and_digest_survive_forcing_without_conflating_inputs`
    /// - witness: `machine::tests::re_sharing_runs_one_goal_per_distinct_pair`
    /// - witness: `resharing::tests::supports_that_do_not_agree_are_remembered_in_different_buckets`
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

/// Whether `glued` resolves in `domain`: its guard reads, its node lives, and
/// a flexible neutral's node lives.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `Ok` exactly when the guard reads, the node lives and, for a
///   flexible neutral, its neutral node lives.
/// - provides: the check a support's construction makes of each head.
/// - fails: [`ConversionFault::Domain`] for a node that does not resolve.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — a live head resolves, and a truncated one is refused;
///   accepting a dangling head or refusing a live one changes construction.
/// - witness: `resharing::tests::support_identity_and_digest_survive_forcing_without_conflating_inputs`
///
/// # Errors
/// - [`ConversionFault::Domain`] — a node does not resolve.
#[spec(ensures: |ret| match glued {
    Glued::Value(id) => match domain.value_guard(id) {
        Ok(Guard::Rigid(_)) => ret.is_ok(),
        Ok(Guard::Flexible) => match domain.value(id) {
            Some(&DomainValue::Neutral { neutral, .. }) => if domain.neutral(neutral).is_some() { ret.is_ok() }
                else { ret == Err(ConversionFault::Domain(DomainFault::Dangling)) },
            Some(_) => ret.is_ok(),
            None => ret == Err(ConversionFault::Domain(DomainFault::Dangling)),
        },
        Err(fault) => ret == Err(ConversionFault::Domain(fault)),
    },
    Glued::Computation(id) => match domain.comp_guard(id) {
        Ok(Guard::Rigid(_)) => ret.is_ok(),
        Ok(Guard::Flexible) => match domain.computation(id) {
            Some(&DomainComp::Neutral { neutral, .. }) => if domain.neutral(neutral).is_some() { ret.is_ok() }
                else { ret == Err(ConversionFault::Domain(DomainFault::Dangling)) },
            Some(_) => ret.is_ok(),
            None => ret == Err(ConversionFault::Domain(DomainFault::Dangling)),
        },
        Err(fault) => ret == Err(ConversionFault::Domain(fault)),
    },
})]
fn resolves(
    domain: &DomainArena,
    glued: Glued,
) -> Result<(), ConversionFault>
{
    let (guard, neutral) = match glued {
        Glued::Value(value) => {
            let guard = domain.value_guard(value).map_err(ConversionFault::Domain)?;
            let neutral = match domain.value(value) {
                Some(&DomainValue::Neutral { neutral, .. }) => Some(neutral),
                Some(_) => None,
                None => return Err(ConversionFault::Domain(DomainFault::Dangling)),
            };
            (guard, neutral)
        },
        Glued::Computation(comp) => {
            let guard = domain.comp_guard(comp).map_err(ConversionFault::Domain)?;
            let neutral = match domain.computation(comp) {
                Some(&DomainComp::Neutral { neutral, .. }) => Some(neutral),
                Some(_) => None,
                None => return Err(ConversionFault::Domain(DomainFault::Dangling)),
            };
            (guard, neutral)
        },
    };
    if let (Guard::Flexible, Some(neutral)) = (guard, neutral) {
        domain
            .neutral(neutral)
            .ok_or(ConversionFault::Domain(DomainFault::Dangling))?;
    }
    Ok(())
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
                Standing::Entry => {
                    gathered.insert(Edge::Entry(child));
                },
                Standing::Inner => gathered.extend(held.edges.iter().copied()),
            }
        }
        let consulted = self
            .store
            .get_mut(usize::from(process))
            .ok_or(ConversionFault::MachineInvariant)?;
        consulted.edges.append(&mut gathered);
        if consulted.standing == Standing::Entry {
            let total = match settled {
                Settled::Convertible => &mut self.totals.acceptance,
                Settled::NotConvertible => &mut self.totals.refusal,
            };
            total.0 = total.0.saturating_add(consulted.edges.len());
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests;
