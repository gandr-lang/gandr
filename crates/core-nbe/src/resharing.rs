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
    /// # Errors
    /// - [`ConversionFault::Domain`] — a node does not resolve.
    #[inline]
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
            | SupportSides::Opened(..) => (SideContent::Opened, SideContent::Opened),
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
    #[inline]
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
/// # Errors
/// - [`ConversionFault::Domain`] — a node does not resolve.
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
    /// # Errors
    /// - [`ConversionFault::MachineInvariant`] — the ids and the store
    ///   disagree.
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
    /// # Errors
    /// - [`ConversionFault::MachineInvariant`] — no support for `process`.
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
    /// # Errors
    /// - [`ConversionFault::MachineInvariant`] — no support for `process`.
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
    /// # Errors
    /// - [`ConversionFault::MachineInvariant`] — no support for `process`.
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
    /// # Errors
    /// - [`ConversionFault::MachineInvariant`] — no support for a process.
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
