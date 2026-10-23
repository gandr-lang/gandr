//! The rewrites a dependent type needs: shifting a type into a deeper context,
//! instantiating a dependent codomain at an argument, and strengthening a type
//! out from under the binder it was synthesized beneath — the first and the
//! last as updates of the relocation an id carries, the second as a walk.
//!
//! # Why a type is rewritten at all
//!
//! [`ValueType::Element`] and [`CompType::Element`] read a type off a code,
//! and a code can be a bound variable, so a type can carry a free de Bruijn
//! index. A type read from a context slot was formed where the slot was
//! opened and has to be shifted to the depth it is read at; a dependent
//! codomain is scoped under its binder and has to be instantiated at the
//! argument an application supplies; a type synthesized under a binder has to
//! be lowered back out of it, which fails exactly when the type mentions the
//! binder.
//!
//! # One engine, its rewrites
//!
//! The rewrites differ only at a variable occurrence; every other former is a
//! congruence that rewrites its children, each at the depth its position sits
//! at, and mints a node only where a child changed. The engine is iterative —
//! a heap task stack, children opened in reverse and closed in order — so a
//! deep type costs heap rather than stack, and memoized per node at the depth
//! it is reached at, so a shared subterm is rewritten once however many paths
//! reach it. A rewrite that acts only on free indices at or past the depth it
//! is at answers a node whose carried support stops below that depth with the
//! node itself, without entering it, so a walk visits only the paths that lead
//! to an index it moves.
//!
//! A substitution carries its replacement under the binders it crosses: at
//! depth `d` the occurrence the depth names becomes the replacement shifted by
//! `d`, scheduled through the same engine, which is what keeps a free variable
//! of the replacement from being captured by a binder it is carried under.
//!
//! Rebuilding goes through the arena's constructors, so a rewrite that turns a
//! decode's code into a quote yields the quoted type: instantiating `El x` at
//! `⌜A⌝` answers `A`.
//!
//! Only the intuitionistic zone is rewritten. No former binds into the linear
//! zone, so a linear index counts no binder these rewrites cross and stands.
//!
//! Three rewrites serve the hole surface rather than binding. A fill replaces
//! every hole of one name by its filling, which is written in the hole's own
//! context and so is carried unchanged. A wrap puts the marks an elaboration
//! recorded around the nodes they name. An environment substitution replaces
//! every free index at once by the entry an evaluation environment holds for
//! it, which is how a suspended body is read back in the context it is
//! displayed in.
//!
//! A renaming is the rewrite an instantiation needs. It names no binder: it
//! replaces a constant by another, an atom by a type and a bound region by a
//! region, wherever each stands, so a body written against one set of
//! declarations reads against another and a signature abstracted over its
//! caller's regions reads at one call's. Constants, the types replacing atoms
//! and regions are closed, so a renaming carries nothing under the binders it
//! crosses.
//!
//! A relevelling reads every decode of one binder at a level and leaves every
//! other node as it stands. The lowering decodes a transport's or a ride's
//! motive binder at level zero, the binder's type unknown to it; the checker
//! relevels the motive at the level of the universe the path or flow lives
//! in, the one level at which a decode of that binder is well formed.
//!
//! # Elaborating nested computations
//!
//! A computation written where a value is read stands in the core as
//! [`Value::Nested`] until the checker decides it by the type expected there,
//! and a written `run c` as [`Value::Run`]. [`elaborate_nested_traced`]
//! replaces both once the decisions are in: a suspended one by a thunk, and
//! the runs of each region by binds around it, in written order, the variable
//! of each bind standing where its run stood. A region is the innermost
//! computation a run stands in the values of, an application's head sharing
//! its spine's; a thunk's body, a case arm, a lambda's body and either half of
//! a bind are regions of their own, so no run leaves a suspension or a branch.
//! The elaboration is two more modes of the same engine: one rebuilds the body
//! by congruence, scheduling a region's runs beside its children, and one
//! carries a region's body under its new binds while answering each run by its
//! bind's variable. A region nested `k` deep is carried once per region
//! around it, so the cost is quadratic in the depth of nested regions with
//! runs and linear otherwise.
//!
//! # Binder machines
//!
//! A dependent arrow's codomain stands under one binder, so the checker shifts
//! and instantiates types. A shift and a strengthening are root updates: they
//! mint nothing, answering the subject's id under a [`Relocation`] — the raise
//! or lowering of every free intuitionistic index at or past a cutoff, fitted
//! to the node's carried support — that a later shift folds into where the two
//! fold, and [`Relocated::settle`] reads into a plain id by the one eager walk,
//! [`Rewrite::Relocate`], entering only nodes whose support reaches its
//! cutoff. `strengthen_comp_type` reads its answer off the carried support:
//! a type whose support selects the binder is refused with
//! `strengthening::Absent::MentionsBinder`, and any other is lowered.
//! `instantiate_comp_type` substitutes a value for the innermost index and
//! lowers the rest in one walk. A replacement carried under a binder is
//! shifted once per depth and recorded, so substitution avoids capture without
//! renaming anything. The linear zone is left alone: no former in the
//! vocabulary binds into it.
//!
//! Alternatives: recursive rewrites, which the workspace's recursion lint
//! forbids and which a deep type would overflow; a relocation composed into
//! every arena read, which changes every reader across the workspace and
//! hands each an owned node; and a relocation stored on every child edge,
//! which is not closed under composition (see [`crate::relocation`]) and so
//! would settle on every non-folding update anyway. Reversal: a measured
//! family whose cost is dominated by the settle at a consumer, which would
//! carry relocations through the readers that consumer reaches.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_strata::Level;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use quenchant_arith::arith;
use quenchant_shape::shape::Maybe;

use crate::arena::CompTypeId;
use crate::arena::ComputationId;
use crate::arena::CoreArena;
use crate::arena::ValueId;
use crate::arena::ValueTypeId;
use crate::effect::capability::Region;
use crate::effect::capability::RegionBinder;
use crate::hole::HoleId;
use crate::hole::MarkIndex;
use crate::hole::TermId;
use crate::relocation::Offset;
use crate::relocation::Relocated;
use crate::relocation::Relocation;
use crate::relocation::folding;
use crate::support::ThinningRef;
use crate::syntax::CompType;
use crate::syntax::ComponentCount;
use crate::syntax::Computation;
use crate::syntax::SplitMotive;
use crate::syntax::Value;
use crate::syntax::ValueType;
use crate::syntax::Zone;

/// A count of intuitionistic binders: how far a walk has descended, or how far
/// a shift raises a free index.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Binders(u32);

impl Binders
{
    /// No binder.
    pub const NONE: Self = Self(0_u32);
    /// One binder.
    pub const ONE: Self = Self(1_u32);

    /// One binder further in.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the count plus one, clamped at the representable ceiling,
    ///   which no context reaches.
    /// - provides: the step a walk takes past a binder.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero, one below the u32 ceiling and the ceiling
    ///   distinguish increment from saturation, through both binder-count entry
    ///   points.
    /// - witness: `rewrite::tests::binder_counts_clamp_at_the_ceiling`
    #[spec(ensures: |ret| ret.0 == self.0.saturating_add(1))]
    #[inline]
    #[must_use]
    pub fn deeper(self) -> Self
    {
        // reason: a binder count uses u32::MAX as its conservative ceiling.
        Self(u32::from(arith::saturating_add(
            arith::Int::from(self.0),
            arith::Int::from(1_u32),
        )))
    }

    /// The count past `count` binders further in, as a split's body is.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the count plus `count`, clamped at the representable ceiling,
    ///   which no context reaches.
    /// - provides: the step a walk takes past a split's binders.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero binders, one, and a count past the u32 ceiling
    ///   distinguish addition from increment and saturation.
    /// - witness: `rewrite::tests::binder_counts_clamp_at_the_ceiling`
    #[spec(ensures: |ret| u64::from(ret.0) == u64::from(self.0).saturating_add(u64::try_from(usize::from(count)).unwrap_or(u64::MAX)).min(u64::from(u32::MAX)))]
    #[inline]
    #[must_use]
    pub fn deeper_by(
        self,
        count: ComponentCount,
    ) -> Self
    {
        let raised = u32::try_from(usize::from(count)).unwrap_or(u32::MAX);
        // reason: a binder count uses u32::MAX as its conservative ceiling.
        Self(u32::from(arith::saturating_add(
            arith::Int::from(self.0),
            arith::Int::from(raised),
        )))
    }

    /// The count past `binders` more binders, as a former's child that
    /// [`crate::world::WorldForm::scoped`] reports under them is.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the sum of the two counts, clamped at the representable
    ///   ceiling, which no context reaches.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero, one and a sum past the u32 ceiling distinguish
    ///   addition from saturation.
    /// - witness: `rewrite::tests::binder_counts_clamp_at_the_ceiling`
    #[spec(ensures: |ret| ret.0 == self.0.saturating_add(binders.0))]
    #[inline]
    #[must_use]
    pub fn beyond(
        self,
        binders: Self,
    ) -> Self
    {
        // reason: a binder count uses u32::MAX as its conservative ceiling.
        Self(u32::from(arith::saturating_add(
            arith::Int::from(self.0),
            arith::Int::from(binders.0),
        )))
    }

    /// The count a variable at `index` reaches past: its index plus one.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `index + 1`, clamped at the representable ceiling.
    /// - provides: the shift a context slot's type takes when read through an
    ///   occurrence at `index`, since the slot was opened that many binders
    ///   further out.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero, one below the u32 ceiling and the ceiling
    ///   distinguish increment from saturation, through both binder-count entry
    ///   points.
    /// - witness: `rewrite::tests::binder_counts_clamp_at_the_ceiling`
    #[spec(ensures: |ret| ret.0 == u32::from(index).saturating_add(1))]
    #[inline]
    #[must_use]
    pub fn past(index: DeBruijnIndex) -> Self
    {
        Self(u32::from(index)).deeper()
    }
}

impl From<u32> for Binders
{
    /// Wraps a raw count as a binder count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: u32) -> Self
    {
        Self(count)
    }
}

impl From<Binders> for u32
{
    /// Unwraps a binder count to its raw value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: Binders) -> Self
    {
        count.0
    }
}

/// Why a renaming leaves a node as it stands.
mod renamed
{
    /// The single reason a node is not one a renaming names.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub(super) enum Absent
    {
        /// The node is not a constant or an atom the renaming names.
        Unnamed,
    }
}

/// Why a walk answers a node unread.
mod free
{
    /// The single reason a node carries no free index a walk acts on.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub(super) enum Absent
    {
        /// Every free index the node selects stands inside the depth.
        Inside,
    }
}

/// Why a node's support could not be read.
mod unminted
{
    /// The single reason a node carries no support.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub(super) enum Absent
    {
        /// The id names no node of the arena.
        Dangling,
    }
}

/// Why a strengthening answered nothing.
pub mod strengthening
{
    /// The single reason a type cannot be lowered out of its binder.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub enum Absent
    {
        /// The type mentions the binder it is being lowered out of.
        MentionsBinder,
    }
}

/// A node of any of the four families.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Node
{
    /// A value.
    Value(ValueId),
    /// A computation.
    Computation(ComputationId),
    /// A value type.
    ValueType(ValueTypeId),
    /// A computation type.
    CompType(CompTypeId),
}

/// What a walk does at a variable occurrence.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Rewrite
{
    /// Move every free index by the offset: the eager reading of a
    /// relocation, and the raise a replacement takes under the binders it is
    /// carried past.
    Relocate(Offset),
    /// Replace the index the depth names by the value, and lower every index
    /// outside it.
    Substitute(ValueId),
    /// Substitute the value as [`Rewrite::Substitute`] does, except at a
    /// decode whose returned code reads the binder: there the call runs
    /// ahead, bound as the lowering binds a type-read call argument, and the
    /// code reads the bind's variable for the binder.
    Instantiate(ValueId, ComputationId),
    /// Move the index the count names to the innermost free position, one
    /// past the depth, and raise every free index below it by one: the body
    /// of a decoded returned code carried under the bind
    /// [`Rewrite::Instantiate`] puts ahead of it.
    Rotate(Binders),
    /// Replace every hole of the name, in the filling's family, by the filling.
    Fill(HoleId, Node),
    /// Replace every value hole of the name by the value, written under the
    /// count of binders: an occurrence that many binders deep takes it as it
    /// stands, one deeper takes it raised past the binders between, and one
    /// shallower stands.
    Solve(HoleId, ValueId, Binders),
    /// Wrap every node the engine's sites name in the mark it names.
    Wrap,
    /// Replace every index outside the depth that counts into the engine's
    /// environment by its entry, and lower every index past the environment by
    /// the environment's length.
    Environment,
    /// Elaborate every nested computation the engine's survey found: suspend
    /// one the checker decided to thunk, and run the rest before their
    /// regions.
    Elaborate,
    /// Replace every constant and every atom the engine's renaming names by
    /// what it names for it.
    Rename,
    /// Replace every occurrence of the constant by the intuitionistic
    /// variable counting past the depth to the index.
    Abstract(ConstantIndex, DeBruijnIndex),
    /// Raise every free index by the count, as a relocation does, and answer
    /// each run the engine's slots name by the variable of the bind its region
    /// mints for it.
    Splice(Binders),
    /// Read every decode of the binder the depth names at the engine's level,
    /// and leave every other node as it stands.
    Relevel,
    /// Read the linear binder the count names, counted from the walk's root,
    /// as one intuitionistic binder just outside the root: its variable
    /// becomes the intuitionistic variable counting past the depth to that
    /// binder, and every free intuitionistic index rises by one. Every other
    /// linear index stands, the binder's own slot unread, so a session
    /// action's subject and a memory form's slot keep their names.
    Delinearise(Binders),
}

impl Rewrite
{
    /// The rewrite a child standing past `binders` linear binders takes.
    ///
    /// # Specification
    /// - ensures: a delinearisation counting `binders` more; every other
    ///   rewrite, which reads no linear index, unchanged.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a payload read under a nested receive and under a
    ///   fork's halves is the one the count names, and a payload of the nested
    ///   receive stays linear.
    /// - witness: `rewrite::tests::a_delinearised_payload_reads_its_binder_past_nested_linear_binders_1319`
    #[spec(ensures: |ret| match self {
        | Self::Delinearise(linear) => ret == Self::Delinearise(linear.beyond(binders)),
        | _ => ret == self,
    })]
    fn past_linear(
        self,
        binders: Binders,
    ) -> Self
    {
        match self {
            Self::Delinearise(linear) => Self::Delinearise(linear.beyond(binders)),
            Self::Relocate(_)
            | Self::Substitute(_)
            | Self::Instantiate(..)
            | Self::Rotate(_)
            | Self::Fill(..)
            | Self::Solve(..)
            | Self::Wrap
            | Self::Environment
            | Self::Elaborate
            | Self::Rename
            | Self::Abstract(..)
            | Self::Splice(_)
            | Self::Relevel => self,
        }
    }
}

/// Whether an instantiation met the binder it instantiates beneath a node.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Mention
{
    /// No occurrence named the binder.
    Absent,
    /// Some occurrence did.
    Present,
}

/// One unit of the engine's work.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Task
{
    /// Rewrite a node at a depth: answer it from the memo or a variable rule,
    /// or schedule its children and its close.
    Open(Node, Binders, Rewrite),
    /// Combine a node's rewritten children into its own result.
    Close(Node, Binders, Rewrite),
    /// Record the result on top of the stack as a node's own.
    Record(Node, Binders, Rewrite),
    /// Wrap an elaborated region's spliced body, on top of the stack, in the
    /// binds of its runs beneath it, outermost first.
    Hoist(ComputationId, Binders),
    /// Answer an instantiated decode by its call, raised, bound ahead of its
    /// code's body, rotated: the two results on top of the stack.
    BindAhead(Node, Binders, Rewrite),
}

/// What one variable occurrence rewrites to.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Occurrence
{
    /// The occurrence's rewritten value, final.
    Answered(ValueId),
    /// The replacement, still to be carried under this many binders.
    Carried(ValueId, Binders),
}

/// The engine's state for one rewrite of one subject.
struct Engine<'arena>
{
    /// The arena the subject lives in and the rewritten nodes are minted into.
    arena: &'arena mut CoreArena,
    /// Rewritten results, keyed by node, depth and rewrite.
    memo: BTreeMap<(Node, Binders, Rewrite), Node>,
    /// The pending work.
    tasks: Vec<Task>,
    /// The results of closed nodes, awaiting their parents.
    results: Vec<Node>,
    /// The nodes a wrap marks, each with its mark.
    sites: BTreeMap<Node, MarkIndex>,
    /// The values a crossing applies a reduct to, each with the reduct.
    crossings: BTreeMap<ValueId, ConstantIndex>,
    /// Each run a crossing minted beside the value it applies the reduct to,
    /// in minting order.
    crossed: Vec<(ValueId, ValueId)>,
    /// The entries an environment substitution replaces free indices by,
    /// innermost first.
    environment: Vec<ValueId>,
    /// How the checker decided each nested computation.
    nesting: BTreeMap<ValueId, Nesting>,
    /// Each region's runs beside their computations, in written order.
    regions: BTreeMap<ComputationId, Vec<(ValueId, ComputationId)>>,
    /// Each run's index among the binds its region mints, innermost zero.
    slots: BTreeMap<ValueId, Binders>,
    /// Each run beside the bind minted for it.
    binds: Vec<(ValueId, ComputationId)>,
    /// Each region beside the body it closed to, its runs standing as
    /// themselves, where the close rebuilt it: the node a splice copies, which
    /// no memo entry reports.
    closings: Vec<Carried>,
    /// The constants and atoms a renaming replaces; nothing outside one.
    renaming: &'arena Renaming,
    /// The nodes, each at its depth, an instantiation found reading the
    /// binder it instantiates.
    reads: alloc::collections::BTreeSet<(Node, Binders)>,
    /// Whether each node an instantiation has open reads its binder, the
    /// innermost last.
    reading: Vec<Mention>,
    /// The level a relevelling reads the binder's decodes at; zero outside
    /// one.
    level: Level,
}

impl<'arena> Engine<'arena>
{
    /// A fresh engine over `arena`.
    ///
    /// # Specification
    /// trivial.
    fn new(arena: &'arena mut CoreArena) -> Self
    {
        Self {
            arena,
            memo: BTreeMap::new(),
            tasks: Vec::new(),
            results: Vec::new(),
            sites: BTreeMap::new(),
            crossings: BTreeMap::new(),
            crossed: Vec::new(),
            environment: Vec::new(),
            nesting: BTreeMap::new(),
            regions: BTreeMap::new(),
            slots: BTreeMap::new(),
            binds: Vec::new(),
            closings: Vec::new(),
            renaming: &NOTHING_RENAMED,
            reads: alloc::collections::BTreeSet::new(),
            reading: Vec::new(),
            level: Level::zero(),
        }
    }

    /// Rewrite `subject` at the supplied binder cutoff.
    ///
    /// # Specification
    /// - requires: the subject graph is acyclic wherever its nodes resolve; the
    ///   pending and result stacks are empty. Unreadable ids are admitted.
    /// - ensures: the rewritten node, in the subject's family; an unreadable
    ///   subject, and one whose support the rewrite does not reach, answers
    ///   itself.
    /// - provides: the whole iterative walk, memoized per node and depth.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — 600 bounded generated codomains agree with a
    ///   level-based reference under open substitution. L3 — a shared product
    ///   chain observes once-per-key minting, and binding-site goldens separate
    ///   shadowing.
    /// - witness: `rewrite::tests::instantiating_a_codomain_avoids_capture`
    /// - witness: `rewrite::tests::a_shared_type_is_rewritten_once_per_node`
    /// - witness: `rewrite::tests::binding_sites_distinguish_free_bound_and_linear_indices`
    #[spec(
        requires: self.tasks.is_empty() && self.results.is_empty(),
        ensures: |ret| self.tasks.is_empty() && self.results.is_empty()
            && (self.memo.get(&(subject, depth, rewrite)) == Some(&ret) || ret == subject)
            && core::mem::discriminant(&ret) == core::mem::discriminant(&subject),
    )]
    fn run(
        &mut self,
        subject: Node,
        depth: Binders,
        rewrite: Rewrite,
    ) -> Node
    {
        self.tasks.push(Task::Open(subject, depth, rewrite));
        while let Some(task) = self.tasks.pop() {
            match task {
                Task::Open(node, depth, step) => self.open(node, depth, step),
                Task::Close(node, depth, step) => {
                    if let Rewrite::Instantiate(_, call) = step
                        && self.close_reading(node, depth, (step, call)) == Maybe::Present(())
                    {
                        continue;
                    }
                    let runs = self.elaborated_runs(node, step);
                    let rewritten = self.close(node);
                    if let (
                        Node::Computation(region),
                        Node::Computation(closed),
                        &[first, ref rest @ ..],
                    ) = (node, rewritten, runs.as_slice())
                    {
                        self.splice(region, depth, closed, first, rest);
                        continue;
                    }
                    let rewritten = self.wrapped(node, rewritten, step);
                    let _previous = self.memo.insert((node, depth, step), rewritten);
                    self.results.push(rewritten);
                },
                Task::Record(node, depth, step) => {
                    if let Some(&rewritten) = self.results.last() {
                        let _previous = self.memo.insert((node, depth, step), rewritten);
                    }
                },
                Task::Hoist(region, depth) => self.hoist(region, depth),
                Task::BindAhead(node, depth, step) => self.bind_ahead(node, depth, step),
            }
        }
        self.results.pop().unwrap_or(subject)
    }

    /// Open one node: answer it at once when the memo, its support or a
    /// variable rule can, and otherwise schedule its close after its children.
    ///
    /// A relocation, a substitution, an instantiation and an environment
    /// substitution act only on free indices at or past the depth, so a node
    /// whose carried support selects none answers itself unread.
    ///
    /// # Specification
    /// - requires: `depth` is the number of binders crossed to reach `node`.
    /// - ensures: pushes exactly one result for `node` by the time every task
    ///   this call schedules has run.
    /// - provides: the scheduling half of the engine.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a memo hit returns the stored result, a node whose
    ///   support stops below the depth answers itself without entering the
    ///   memo, a free occurrence answers immediately, and substitution beneath
    ///   a binder schedules a shifted replacement; the shared-chain, skip and
    ///   capture witnesses separate missing publication, duplicate work, a walk
    ///   into a closed child and premature replacement.
    /// - witness: `rewrite::tests::a_shared_type_is_rewritten_once_per_node`
    /// - witness: `rewrite::tests::a_walk_enters_only_nodes_whose_support_reaches_its_depth`
    /// - witness: `rewrite::tests::substitution_replaces_a_free_occurrence`
    /// - witness: `rewrite::tests::substitution_avoids_capture`
    /// - witness: `rewrite::tests::a_fill_replaces_exactly_the_named_holes`
    /// - witness: `rewrite::tests::a_solution_fills_a_type_raised_past_its_scope_1216`
    #[spec(
        captures: [pending = self.tasks.len(), ready = self.results.len()],
        ensures: (ready.checked_add(1) == Some(self.results.len()) && self.tasks.len() == pending
            && (self.memo.get(&(node, depth, rewrite)) == self.results.last()
                || self.results.last() == Some(&node)))
            || (self.results.len() == ready && self.tasks.len() > pending
                && matches!(self.tasks.get(pending), Some(Task::Close(held, at, step) | Task::Record(held, at, step))
                    if *held == node && *at == depth && *step == rewrite)),
    )]
    fn open(
        &mut self,
        node: Node,
        depth: Binders,
        rewrite: Rewrite,
    )
    {
        if let Some(&done) = self.memo.get(&(node, depth, rewrite)) {
            if let Rewrite::Instantiate(..) = rewrite
                && self.reads.contains(&(node, depth))
            {
                self.note_read(node, depth);
            }
            self.results.push(done);
            return;
        }
        if matches!(
            rewrite,
            Rewrite::Relocate(_)
                | Rewrite::Substitute(_)
                | Rewrite::Instantiate(..)
                | Rewrite::Environment
                | Rewrite::Relevel
        ) && self.outermost_free(node, depth) == Maybe::Absent(free::Absent::Inside)
        {
            self.results.push(node);
            return;
        }
        if let Maybe::Present(answer) = self.slotted(node, depth, rewrite) {
            let _previous = self.memo.insert((node, depth, rewrite), answer);
            self.results.push(answer);
            return;
        }
        if rewrite == Rewrite::Relevel
            && let Maybe::Present(relevelled) = self.relevelled(node, depth)
        {
            let _previous = self.memo.insert((node, depth, rewrite), relevelled);
            self.results.push(relevelled);
            return;
        }
        if rewrite == Rewrite::Elaborate
            && let Node::Computation(region) = node
            && let Some(runs) = self.regions.get(&region)
        {
            self.tasks.push(Task::Close(node, depth, rewrite));
            self.tasks.extend(
                runs.iter()
                    .rev()
                    .map(|&(_, nested)| Task::Open(Node::Computation(nested), depth, rewrite)),
            );
            self.push_children(node, depth, rewrite);
            return;
        }
        if let Rewrite::Fill(hole, filling) = rewrite
            && match node {
                Node::Value(id) => {
                    matches!(filling, Node::Value(_))
                        && self.arena.value(id) == Some(&Value::Hole(hole))
                },
                Node::Computation(id) => {
                    matches!(filling, Node::Computation(_))
                        && self.arena.computation(id) == Some(&Computation::Hole(hole))
                },
                Node::ValueType(_) | Node::CompType(_) => false,
            }
        {
            let _previous = self.memo.insert((node, depth, rewrite), filling);
            self.results.push(filling);
            return;
        }
        if let (Rewrite::Solve(hole, solution, scope), Node::Value(id)) = (rewrite, node)
            && self.arena.value(id) == Some(&Value::Hole(hole))
        {
            match depth.0.checked_sub(scope.0) {
                Some(0) => {
                    let _previous = self
                        .memo
                        .insert((node, depth, rewrite), Node::Value(solution));
                    self.results.push(Node::Value(solution));
                },
                Some(past) => {
                    self.tasks.push(Task::Record(node, depth, rewrite));
                    self.tasks.push(Task::Open(
                        Node::Value(solution),
                        Binders::NONE,
                        Rewrite::Relocate(Offset::raise(Binders(past))),
                    ));
                },
                None => {
                    let _previous = self.memo.insert((node, depth, rewrite), node);
                    self.results.push(node);
                },
            }
            return;
        }
        if rewrite == Rewrite::Rename
            && let Maybe::Present(renamed) = self.renamed(node)
        {
            let _previous = self.memo.insert((node, depth, rewrite), renamed);
            self.results.push(renamed);
            return;
        }
        if let (Rewrite::Abstract(constant, index), Node::Value(id)) = (rewrite, node)
            && self.arena.value(id) == Some(&Value::Constant(constant))
        {
            // reason: an index and a depth stay far below the u32 ceiling; a
            // saturating step keeps the walk total.
            let raised = u32::from(arith::saturating_add(
                arith::Int::from(u32::from(index)),
                arith::Int::from(depth.0),
            ));
            let abstracted = Node::Value(
                self.arena
                    .value_variable(Zone::Intuitionistic, DeBruijnIndex::from(raised)),
            );
            let _previous = self.memo.insert((node, depth, rewrite), abstracted);
            self.results.push(abstracted);
            return;
        }
        if let (Rewrite::Delinearise(linear), Node::Value(id)) = (rewrite, node)
            && self.arena.value(id)
                == Some(&Value::Variable {
                    zone: Zone::Linear,
                    index: DeBruijnIndex::from(linear.0),
                })
        {
            let read = Node::Value(
                self.arena
                    .value_variable(Zone::Intuitionistic, DeBruijnIndex::from(depth.0)),
            );
            let _previous = self.memo.insert((node, depth, rewrite), read);
            self.results.push(read);
            return;
        }
        if let Node::Value(id) = node
            && let Some(&Value::Variable {
                zone: Zone::Intuitionistic,
                index,
            }) = self.arena.value(id)
        {
            if let Rewrite::Instantiate(..) = rewrite
                && u32::from(index) == depth.0
            {
                self.note_read(node, depth);
            }
            match self.occurrence(id, index, depth, rewrite) {
                Occurrence::Answered(rewritten) => {
                    let rewritten = self.wrapped(node, Node::Value(rewritten), rewrite);
                    let _previous = self.memo.insert((node, depth, rewrite), rewritten);
                    self.results.push(rewritten);
                },
                Occurrence::Carried(replacement, under) => {
                    self.tasks.push(Task::Record(node, depth, rewrite));
                    self.tasks.push(Task::Open(
                        Node::Value(replacement),
                        Binders::NONE,
                        Rewrite::Relocate(Offset::raise(under)),
                    ));
                },
            }
            return;
        }
        if let Rewrite::Instantiate(..) = rewrite {
            self.reading.push(Mention::Absent);
        }
        self.tasks.push(Task::Close(node, depth, rewrite));
        self.push_children(node, depth, rewrite);
    }

    /// The outermost free intuitionistic index `node`'s carried support
    /// selects, when it stands at or past `depth`.
    ///
    /// # Specification
    /// - requires: nothing; a dangling node selects nothing.
    /// - ensures: the greatest selected intuitionistic index when it is at or
    ///   past `depth`; [`free::Absent::Inside`] when the support is empty or
    ///   stops below `depth`.
    /// - provides: the test that lets a walk answer a node without entering it:
    ///   read off the node, never a walk below it.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a closed child, a child free only below the depth and
    ///   one free at it separate the skip from the walk.
    /// - witness: `rewrite::tests::a_walk_enters_only_nodes_whose_support_reaches_its_depth`
    #[spec(ensures: |ret| match ret {
        Maybe::Present(outermost) => u32::from(outermost) >= depth.0,
        Maybe::Absent(free::Absent::Inside) => true,
    })]
    fn outermost_free(
        &self,
        node: Node,
        depth: Binders,
    ) -> Maybe<DeBruijnIndex, free::Absent>
    {
        let support = match node {
            Node::Value(id) => self.arena.value_support(id),
            Node::Computation(id) => self.arena.computation_support(id),
            Node::ValueType(id) => self.arena.value_type_support(id),
            Node::CompType(id) => self.arena.comp_type_support(id),
        };
        match support.and_then(|support| support.indices(Zone::Intuitionistic).next_back()) {
            Some(outermost) if u32::from(outermost) >= depth.0 => Maybe::Present(outermost),
            Some(_) | None => Maybe::Absent(free::Absent::Inside),
        }
    }

    /// Note that `node`, reached at `depth` by an instantiation, reads the
    /// binder it instantiates, and so does every node open around it.
    ///
    /// # Specification
    /// - requires: `node` is being opened or closed at `depth` by
    ///   [`Rewrite::Instantiate`].
    /// - ensures: `(node, depth)` is among the reads, and the innermost open
    ///   node's reading, if any, is [`Mention::Present`].
    /// - provides: the reading [`Self::close_reading`] decides a decode by,
    ///   kept per node and depth so a memo hit answers it as well.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a code reading the binder and one sparing it separate
    ///   a read noted from one missed: a missed read substitutes the call's
    ///   value where the bind belongs.
    /// - witness: `rewrite::tests::an_instantiation_at_a_call_binds_it_ahead_of_each_decode_reading_it`
    #[spec(ensures: self.reads.contains(&(node, depth))
        && self.reading.last().is_none_or(|&held| held == Mention::Present))]
    fn note_read(
        &mut self,
        node: Node,
        depth: Binders,
    )
    {
        let _first = self.reads.insert((node, depth));
        if let Some(open) = self.reading.last_mut() {
            *open = Mention::Present;
        }
    }

    /// Close an instantiation's node: a decode whose code is a returned call
    /// reading the binder schedules the call bound ahead of that code's body,
    /// `El ⟨c ← call; body[c / x]⟩`, and answers nothing yet.
    ///
    /// # Specification
    /// - requires: `node`'s close is due under [`Rewrite::Instantiate`] at
    ///   `call`, its children's results on top of the result stack and its own
    ///   reading on top of the reading stack.
    /// - ensures: the reading is popped and, when it is present, noted for
    ///   `node` and the node open around it. A decode whose code is a returned
    ///   computation that reads the binder drops its code's result and
    ///   schedules [`Task::BindAhead`] over that computation rotated at `depth`
    ///   ([`Rewrite::Rotate`]) and `call` raised by `depth`, answering
    ///   [`Maybe::Present`]; any other node answers absent, its children's
    ///   results left for the ordinary close.
    /// - provides: the one point an instantiation at a call differs from a
    ///   substitution of its value. Only a decode's code binds, because only a
    ///   call a type decodes runs its call arguments first in the lowering
    ///   (`mint_called`); a returned code elsewhere, a path endpoint say, holds
    ///   its calls in place and is substituted as written.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a decode reading the binder at depth zero and under
    ///   an inner binder, a decode that does not read it, and an endpoint
    ///   reading it separate the bind, the rotation and the plain substitution.
    /// - witness: `rewrite::tests::an_instantiation_at_a_call_binds_it_ahead_of_each_decode_reading_it`
    #[spec(captures: pending = self.tasks.len(),
        ensures: |ret| matches!(ret, Maybe::Absent(())) || self.tasks.len() == pending.saturating_add(3))]
    fn close_reading(
        &mut self,
        node: Node,
        depth: Binders,
        (rewrite, call): (Rewrite, ComputationId),
    ) -> Maybe<(), ()>
    {
        if self.reading.pop() != Some(Mention::Present) {
            return Maybe::Absent(());
        }
        self.note_read(node, depth);
        let code = match node {
            Node::ValueType(id) => {
                let Some(&ValueType::Element { code, .. }) = self.arena.value_type(id)
                else {
                    return Maybe::Absent(());
                };
                code
            },
            Node::CompType(id) => {
                let Some(&CompType::Element { code, .. }) = self.arena.comp_type(id)
                else {
                    return Maybe::Absent(());
                };
                code
            },
            Node::Value(_) | Node::Computation(_) => return Maybe::Absent(()),
        };
        if !self.reads.contains(&(Node::Value(code), depth)) {
            return Maybe::Absent(());
        }
        let Some(&Value::Returned(body)) = self.arena.value(code)
        else {
            return Maybe::Absent(());
        };
        let _substituted = self.results.pop();
        self.tasks.push(Task::BindAhead(node, depth, rewrite));
        self.tasks.push(Task::Open(
            Node::Computation(body),
            Binders::NONE,
            Rewrite::Rotate(depth),
        ));
        self.tasks.push(Task::Open(
            Node::Computation(call),
            Binders::NONE,
            Rewrite::Relocate(Offset::raise(depth)),
        ));
        Maybe::Present(())
    }

    /// Bind the raised call ahead of the rotated body on top of the result
    /// stack, and answer the decode `node` at that bind returned.
    ///
    /// # Specification
    /// - requires: the rotated body on top of the result stack, the raised call
    ///   beneath it, as [`Self::close_reading`] scheduled them.
    /// - ensures: both popped; the decode of one returned bind, at `node`'s
    ///   level, pushed and recorded as `node`'s answer at `depth` under
    ///   `rewrite`.
    /// - provides: the close of a decode an instantiation binds ahead.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the bind's two halves are distinct terms, so a
    ///   swapped or dropped half answers a different code.
    /// - witness: `rewrite::tests::an_instantiation_at_a_call_binds_it_ahead_of_each_decode_reading_it`
    #[spec(captures: ready = self.results.len(),
        ensures: self.results.len() == ready.saturating_sub(1)
            && self.memo.get(&(node, depth, rewrite)) == self.results.last())]
    fn bind_ahead(
        &mut self,
        node: Node,
        depth: Binders,
        rewrite: Rewrite,
    )
    {
        let read = self.results.pop();
        let ahead = self.results.pop();
        let code = match (ahead, read) {
            (Some(Node::Computation(ahead)), Some(Node::Computation(read))) => {
                let bound = self.arena.computation_bind(ahead, read);
                Maybe::Present(self.arena.value_returned(bound))
            },
            _ => Maybe::Absent(()),
        };
        let answer = match (node, code) {
            (Node::ValueType(id), Maybe::Present(code)) => match self.arena.value_type(id) {
                Some(&ValueType::Element { ref target, .. }) => {
                    let target = target.clone();
                    Node::ValueType(self.arena.value_type_element(code, target))
                },
                _ => node,
            },
            (Node::CompType(id), Maybe::Present(code)) => match self.arena.comp_type(id) {
                Some(&CompType::Element { ref target, .. }) => {
                    let target = target.clone();
                    Node::CompType(self.arena.comp_type_element(code, target))
                },
                _ => node,
            },
            _ => node,
        };
        let _previous = self.memo.insert((node, depth, rewrite), answer);
        self.results.push(answer);
    }

    /// What a renaming answers for `node` when `node` is a leaf it names.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: for a constant the renaming names, a constant node at the
    ///   position it names for it; for an atom it names, the type it names for
    ///   it; absent for every other node, a constant or atom it does not name
    ///   among them.
    /// - provides: the one point a renaming differs from a congruence.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a renamed constant, a renamed atom, a constant and an
    ///   atom the renaming does not name, and each under a binder, separate the
    ///   two leaf rules from identity.
    /// - witness: `rewrite::tests::a_renaming_replaces_exactly_the_named_constants_and_atoms`
    #[spec(ensures: |ret| match ret {
        | Maybe::Present(renamed) => core::mem::discriminant(&renamed) == core::mem::discriminant(&node),
        | Maybe::Absent(renamed::Absent::Unnamed) => true,
    })]
    fn renamed(
        &mut self,
        node: Node,
    ) -> Maybe<Node, renamed::Absent>
    {
        match node {
            Node::Value(id) => {
                if let Some(&Value::Constant(constant)) = self.arena.value(id)
                    && let Some(&target) = self.renaming.constants.get(&constant)
                {
                    return Maybe::Present(Node::Value(self.arena.value_constant(target)));
                }
            },
            Node::ValueType(id) => {
                if let Some(&ValueType::Abstract(atom)) = self.arena.value_type(id)
                    && let Some(&target) = self.renaming.atoms.get(&atom)
                {
                    return Maybe::Present(Node::ValueType(target));
                }
            },
            Node::Computation(_) | Node::CompType(_) => {},
        }
        Maybe::Absent(renamed::Absent::Unnamed)
    }

    /// The mark a wrap puts around `node`'s rewritten form, if its sites name
    /// it, or the thunk or returned value an elaboration stands a nested
    /// computation as, if the checker decided it so.
    ///
    /// # Specification
    /// - requires: `rewritten` is `node`'s rewritten form, in its family.
    /// - ensures: under a wrap, a fresh run of the reduct applied to
    ///   `rewritten` when the crossings name `node`, and otherwise a fresh mark
    ///   over `rewritten` when the sites name `node` and it is a term; under an
    ///   elaboration, a fresh thunk over the computation of `rewritten` when
    ///   `node` is a nested computation the checker decided to suspend, and a
    ///   fresh returned value over it when the checker decided it stands as
    ///   what it returns; `rewritten` itself otherwise.
    /// - provides: the one point a wrap differs from a congruence, and the one
    ///   point an elaboration suspends.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a marked leaf, a marked variable, a marked compound
    ///   whose child is marked too, and an unmarked sibling separate wrapping,
    ///   nesting and the identity on unnamed nodes; a suspended nested
    ///   computation beside a run one separates the two elaborations.
    /// - witness: `rewrite::tests::a_wrap_marks_exactly_the_named_nodes`
    /// - witness: `rewrite::tests::an_elaboration_suspends_and_runs_as_decided`
    #[spec(ensures: |ret| core::mem::discriminant(&ret) == core::mem::discriminant(&rewritten))]
    fn wrapped(
        &mut self,
        node: Node,
        rewritten: Node,
        rewrite: Rewrite,
    ) -> Node
    {
        if rewrite == Rewrite::Elaborate
            && let (Node::Value(held), Node::Value(id)) = (node, rewritten)
            && let Some(&decided) = self.nesting.get(&held)
            && let Some(&Value::Nested(nested)) = self.arena.value(id)
        {
            match decided {
                Nesting::Thunk => return Node::Value(self.arena.value_thunk(nested)),
                Nesting::Returned => return Node::Value(self.arena.value_returned(nested)),
                Nesting::Run => {},
            }
        }
        if rewrite != Rewrite::Wrap {
            return rewritten;
        }
        if let (Node::Value(held), Node::Value(id)) = (node, rewritten)
            && let Some(&reduct) = self.crossings.get(&held)
        {
            let constant = self.arena.value_constant(reduct);
            let forced = self.arena.computation_force(constant);
            let applied = self.arena.computation_application(forced, id);
            let run = self.arena.value_run(applied);
            self.crossed.push((id, run));
            return Node::Value(run);
        }
        let Some(&mark) = self.sites.get(&node)
        else {
            return rewritten;
        };
        match rewritten {
            Node::Value(id) => Node::Value(self.arena.value_mark(mark, id)),
            Node::Computation(id) => Node::Computation(self.arena.computation_mark(mark, id)),
            Node::ValueType(_) | Node::CompType(_) => rewritten,
        }
    }

    /// What a run stands as before its region splices it, and the variable a
    /// splice answers it by.
    ///
    /// # Specification
    /// - requires: `depth` is the number of binders crossed to reach `node`.
    /// - ensures: under an elaboration, a run answers itself, so its region's
    ///   splice finds it where it stands; under a splice, a run answers the
    ///   variable of its slot raised past `depth`; every other node and rewrite
    ///   answers nothing.
    /// - provides: the run half of the elaboration's open step.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two runs of one region splice to their two slots, the
    ///   first written the outer.
    /// - witness: `rewrite::tests::an_elaboration_runs_in_written_order_before_its_region`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(()))
        || matches!(node, Node::Value(id) if self.slots.contains_key(&id)))]
    fn slotted(
        &mut self,
        node: Node,
        depth: Binders,
        rewrite: Rewrite,
    ) -> Maybe<Node, ()>
    {
        let Node::Value(id) = node
        else {
            return Maybe::Absent(());
        };
        let Some(&slot) = self.slots.get(&id)
        else {
            return Maybe::Absent(());
        };
        match rewrite {
            Rewrite::Elaborate => Maybe::Present(node),
            Rewrite::Splice(_) => {
                // reason: a slot and a depth stay far below the u32 ceiling;
                // a saturating step keeps the walk total.
                let index = u32::from(arith::saturating_add(
                    arith::Int::from(slot.0),
                    arith::Int::from(depth.0),
                ));
                Maybe::Present(Node::Value(
                    self.arena
                        .value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index)),
                ))
            },
            Rewrite::Relocate(_)
            | Rewrite::Substitute(_)
            | Rewrite::Instantiate(..)
            | Rewrite::Rotate(_)
            | Rewrite::Fill(..)
            | Rewrite::Solve(..)
            | Rewrite::Wrap
            | Rewrite::Environment
            | Rewrite::Rename
            | Rewrite::Abstract(..)
            | Rewrite::Relevel
            | Rewrite::Delinearise(_) => Maybe::Absent(()),
        }
    }

    /// A decode of the binder the depth names, read at the engine's level.
    ///
    /// # Specification
    /// - requires: `depth` is the number of binders crossed to reach `node`.
    /// - ensures: a value or computation type decoding the intuitionistic
    ///   variable that counts to `depth` answers that variable's decode at the
    ///   engine's level, itself where it already reads there; every other node
    ///   answers nothing.
    /// - provides: the decode half of a relevelling's open step.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a family decoding its binder at level zero, under a
    ///   list, beside a decode of an outer variable and inside a computation
    ///   type, relevelled at one: only the binder's decodes move.
    /// - witness: `rewrite::tests::a_relevelling_reads_only_the_binders_decodes_at_its_level`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(())) || matches!(node, Node::ValueType(_) | Node::CompType(_)))]
    fn relevelled(
        &mut self,
        node: Node,
        depth: Binders,
    ) -> Maybe<Node, ()>
    {
        let binder = |arena: &CoreArena, code: ValueId| {
            matches!(arena.value(code), Some(&Value::Variable { zone: Zone::Intuitionistic, index })
                if u32::from(index) == depth.0)
        };
        match node {
            Node::ValueType(id) => {
                let Some(&ValueType::Element { code, ref target }) = self.arena.value_type(id)
                else {
                    return Maybe::Absent(());
                };
                if !binder(self.arena, code) {
                    return Maybe::Absent(());
                }
                if *target == self.level {
                    return Maybe::Present(node);
                }
                Maybe::Present(Node::ValueType(
                    self.arena.value_type_element(code, self.level.clone()),
                ))
            },
            Node::CompType(id) => {
                let Some(&CompType::Element { code, ref target }) = self.arena.comp_type(id)
                else {
                    return Maybe::Absent(());
                };
                if !binder(self.arena, code) {
                    return Maybe::Absent(());
                }
                if *target == self.level {
                    return Maybe::Present(node);
                }
                Maybe::Present(Node::CompType(
                    self.arena.comp_type_element(code, self.level.clone()),
                ))
            },
            Node::Value(_) | Node::Computation(_) => Maybe::Absent(()),
        }
    }

    /// The elaborated computations of a region's runs, popped from the top of
    /// the result stack, in written order.
    ///
    /// # Specification
    /// - requires: under an elaboration, `node`'s close is due with its runs'
    ///   elaborated computations on top of its children's results, as `open`
    ///   scheduled them.
    /// - ensures: one computation per run of the region `node` names under an
    ///   elaboration, the first written first; nothing for any other node or
    ///   rewrite, the stack untouched.
    /// - provides: the half of a region's close that reads its runs.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the region's splice.
    /// - witness: `rewrite::tests::an_elaboration_runs_in_written_order_before_its_region`
    #[spec(captures: ready = self.results.len(), ensures: |ret| self.results.len().saturating_add(ret.len()) == ready)]
    fn elaborated_runs(
        &mut self,
        node: Node,
        rewrite: Rewrite,
    ) -> Vec<ComputationId>
    {
        let (Rewrite::Elaborate, Node::Computation(region)) = (rewrite, node)
        else {
            return Vec::new();
        };
        let Some(runs) = self.regions.get(&region)
        else {
            return Vec::new();
        };
        let mut elaborated: Vec<ComputationId> = runs
            .iter()
            .rev()
            .map(|&(_, nested)| Self::computation(&mut self.results, nested))
            .collect();
        elaborated.reverse();
        elaborated
    }

    /// Schedule a region's splice: its closed body carried under one binder
    /// per run, every later run carried under the binders of the runs before
    /// it, and the hoist that binds them.
    ///
    /// # Specification
    /// - requires: `closed` is the region's body with its children elaborated
    ///   and its runs standing as themselves; `first` and `rest` are its runs'
    ///   elaborated computations, in written order, scoped where the region
    ///   stands.
    /// - ensures: `first` on the result stack, and tasks that leave each later
    ///   run's computation shifted past the binders before it and then the body
    ///   spliced past them all above it, and hoist them; `closed` reported
    ///   beside the region when the close rebuilt it.
    /// - provides: the scheduling half of a region's hoist.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the region's hoist.
    /// - witness: `rewrite::tests::an_elaboration_runs_in_written_order_before_its_region`
    #[spec(captures: [ready = self.results.len(), pending = self.tasks.len()],
        ensures: self.results.len() == ready.saturating_add(1)
            && self.tasks.len() == pending.saturating_add(rest.len()).saturating_add(2)
            && (closed == region || self.closings.last() == Some(&Carried::Computation(region, closed))))]
    fn splice(
        &mut self,
        region: ComputationId,
        depth: Binders,
        closed: ComputationId,
        first: ComputationId,
        rest: &[ComputationId],
    )
    {
        if closed != region {
            self.closings.push(Carried::Computation(region, closed));
        }
        self.results.push(Node::Computation(first));
        self.tasks.push(Task::Hoist(region, depth));
        let runs = Binders::ONE.deeper_by(ComponentCount::from(rest.len()));
        self.tasks.push(Task::Open(
            Node::Computation(closed),
            Binders::NONE,
            Rewrite::Splice(runs),
        ));
        for (before, &later) in rest.iter().enumerate().rev() {
            self.tasks.push(Task::Open(
                Node::Computation(later),
                Binders::NONE,
                Rewrite::Relocate(Offset::raise(
                    Binders::ONE.deeper_by(ComponentCount::from(before)),
                )),
            ));
        }
    }

    /// Bind a region's runs over its spliced body, the first written
    /// outermost, and answer the binds as the region's elaboration.
    ///
    /// # Specification
    /// - requires: the result stack holds, on top, the region's spliced body
    ///   and beneath it its runs' computations, each shifted past the runs
    ///   before it, the first written lowest.
    /// - ensures: consumes them, mints one bind per run from the innermost out,
    ///   records each run beside its bind, and records and answers the
    ///   outermost as the region's elaboration at `depth`.
    /// - provides: the minting half of a region's hoist.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two runs of one region bind in written order over the
    ///   body, which reads each through its slot.
    /// - witness: `rewrite::tests::an_elaboration_runs_in_written_order_before_its_region`
    #[spec(captures: recorded = self.binds.len(),
        ensures: self.binds.len() >= recorded
            && self.memo.contains_key(&(Node::Computation(region), depth, Rewrite::Elaborate)))]
    fn hoist(
        &mut self,
        region: ComputationId,
        depth: Binders,
    )
    {
        let runs: Vec<ValueId> = self
            .regions
            .get(&region)
            .map(|runs| runs.iter().map(|&(run, _)| run).collect())
            .unwrap_or_default();
        let mut bound = Self::computation(&mut self.results, region);
        let shifted: Vec<ComputationId> = runs
            .iter()
            .map(|_| Self::computation(&mut self.results, region))
            .collect();
        for (&run, nested) in runs.iter().rev().zip(shifted) {
            bound = self.arena.computation_bind(nested, bound);
            self.binds.push((run, bound));
        }
        let _previous = self.memo.insert(
            (Node::Computation(region), depth, Rewrite::Elaborate),
            Node::Computation(bound),
        );
        self.results.push(Node::Computation(bound));
    }

    /// The rewritten form of one intuitionistic occurrence.
    ///
    /// **This is the only place the binding rewrites differ.** A relocation
    /// moves an index at or past the depth by its offset and spares one inside
    /// it, and a splice raises one the same way; a substitution spares an
    /// index inside the depth, replaces the one the depth names and lowers
    /// every one past it; an environment substitution replaces every index
    /// past the depth by the entry it counts to, and lowers one past the
    /// environment by its length. A fill, a wrap, an elaboration and a
    /// renaming leave every occurrence as it stands.
    ///
    /// # Specification
    /// - requires: `depth` is the number of binders crossed to reach the
    ///   occurrence `id` at `index`.
    /// - ensures: the rule above; a substitution's replacement at a positive
    ///   depth is answered as a carry, to be raised by the depth.
    /// - provides: the whole variable rule of the rewrites.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — indices below, at and above depths zero and one
    ///   separate all three binding rewrite rules; a zero offset, a lowering, a
    ///   saturating raise and an open replacement distinguish identity, sign,
    ///   clamping and capture avoidance. An environment of two entries read at
    ///   depths zero and one separates an inner index, each entry and an index
    ///   past the environment.
    /// - witness: `rewrite::tests::occurrence_rules_separate_depth_boundaries`
    /// - witness: `rewrite::tests::an_environment_substitution_replaces_every_free_index`
    #[spec(
        ensures: |ret| match rewrite {
            | Rewrite::Relocate(offset) => if u32::from(index) < depth.0 || offset == Offset::ZERO {
                ret == Occurrence::Answered(id)
            } else {
                matches!(ret, Occurrence::Answered(answer) if matches!(self.arena.value(answer),
                    Some(Value::Variable { zone: Zone::Intuitionistic, index: actual })
                        if Binders(u32::from(*actual)) == offset.moved(Binders(u32::from(index)))))
            },
            | Rewrite::Splice(amount) => if u32::from(index) < depth.0 || amount == Binders::NONE {
                ret == Occurrence::Answered(id)
            } else {
                matches!(ret, Occurrence::Answered(answer) if matches!(self.arena.value(answer),
                    Some(Value::Variable { zone: Zone::Intuitionistic, index: actual })
                        if u32::from(*actual) == u32::from(index).saturating_add(amount.0)))
            },
            | Rewrite::Substitute(replacement) | Rewrite::Instantiate(replacement, _) => match u32::from(index).cmp(&depth.0) {
                | core::cmp::Ordering::Less => ret == Occurrence::Answered(id),
                | core::cmp::Ordering::Equal => if depth == Binders::NONE {
                    ret == Occurrence::Answered(replacement)
                } else { ret == Occurrence::Carried(replacement, depth) },
                | core::cmp::Ordering::Greater => matches!(ret, Occurrence::Answered(answer)
                    if matches!(self.arena.value(answer), Some(Value::Variable { zone: Zone::Intuitionistic, index: actual })
                        if u32::from(*actual).checked_add(1) == Some(u32::from(index)))),
            },
            | Rewrite::Rotate(band) => match u32::from(index).checked_sub(depth.0) {
                | Some(past) if past == band.0 => matches!(ret, Occurrence::Answered(answer) if matches!(self.arena.value(answer),
                    Some(Value::Variable { zone: Zone::Intuitionistic, index: actual }) if u32::from(*actual) == depth.0)),
                | Some(past) if past < band.0 => matches!(ret, Occurrence::Answered(answer) if matches!(self.arena.value(answer),
                    Some(Value::Variable { zone: Zone::Intuitionistic, index: actual })
                        if Some(u32::from(*actual)) == u32::from(index).checked_add(1))),
                | Some(_) | None => ret == Occurrence::Answered(id),
            },
            | Rewrite::Delinearise(_) => if u32::from(index) < depth.0 {
                ret == Occurrence::Answered(id)
            } else {
                matches!(ret, Occurrence::Answered(answer) if matches!(self.arena.value(answer),
                    Some(Value::Variable { zone: Zone::Intuitionistic, index: actual })
                        if Some(u32::from(*actual)) == u32::from(index).checked_add(1)))
            },
            | Rewrite::Fill(..) | Rewrite::Solve(..) | Rewrite::Wrap | Rewrite::Elaborate | Rewrite::Rename | Rewrite::Abstract(..) | Rewrite::Relevel => {
                ret == Occurrence::Answered(id)
            },
            | Rewrite::Environment => u32::from(index) >= depth.0 || ret == Occurrence::Answered(id),
        },
    )]
    fn occurrence(
        &mut self,
        id: ValueId,
        index: DeBruijnIndex,
        depth: Binders,
        rewrite: Rewrite,
    ) -> Occurrence
    {
        let position = Binders(u32::from(index));
        match rewrite {
            Rewrite::Relocate(offset) => {
                if position < depth || offset == Offset::ZERO {
                    Occurrence::Answered(id)
                }
                else {
                    let moved = offset.moved(position);
                    Occurrence::Answered(
                        self.arena
                            .value_variable(Zone::Intuitionistic, DeBruijnIndex::from(moved.0)),
                    )
                }
            },
            Rewrite::Splice(amount) => {
                if position < depth || amount == Binders::NONE {
                    Occurrence::Answered(id)
                }
                else {
                    // reason: a raised index clamps at the representable ceiling.
                    let raised = u32::from(arith::saturating_add(
                        arith::Int::from(position.0),
                        arith::Int::from(amount.0),
                    ));
                    Occurrence::Answered(
                        self.arena
                            .value_variable(Zone::Intuitionistic, DeBruijnIndex::from(raised)),
                    )
                }
            },
            Rewrite::Substitute(replacement) | Rewrite::Instantiate(replacement, _) => {
                match position.cmp(&depth) {
                    core::cmp::Ordering::Less => Occurrence::Answered(id),
                    core::cmp::Ordering::Equal if depth == Binders::NONE => {
                        Occurrence::Answered(replacement)
                    },
                    core::cmp::Ordering::Equal => Occurrence::Carried(replacement, depth),
                    core::cmp::Ordering::Greater => Occurrence::Answered(self.lowered(position)),
                }
            },
            Rewrite::Rotate(band) => match position.0.checked_sub(depth.0) {
                Some(past) if past == band.0 => Occurrence::Answered(
                    self.arena
                        .value_variable(Zone::Intuitionistic, DeBruijnIndex::from(depth.0)),
                ),
                Some(past) if past < band.0 => {
                    // reason: an index inside the band sits below the binder the
                    // band names, so one more stays representable.
                    let raised = u32::from(arith::saturating_add(
                        arith::Int::from(position.0),
                        arith::Int::from(1_u32),
                    ));
                    Occurrence::Answered(
                        self.arena
                            .value_variable(Zone::Intuitionistic, DeBruijnIndex::from(raised)),
                    )
                },
                Some(_) | None => Occurrence::Answered(id),
            },
            Rewrite::Delinearise(_) => {
                if position < depth {
                    Occurrence::Answered(id)
                }
                else {
                    // reason: a raised index clamps at the representable ceiling.
                    let raised = u32::from(arith::saturating_add(
                        arith::Int::from(position.0),
                        arith::Int::from(1_u32),
                    ));
                    Occurrence::Answered(
                        self.arena
                            .value_variable(Zone::Intuitionistic, DeBruijnIndex::from(raised)),
                    )
                }
            },
            Rewrite::Fill(..)
            | Rewrite::Solve(..)
            | Rewrite::Wrap
            | Rewrite::Elaborate
            | Rewrite::Rename
            | Rewrite::Abstract(..)
            | Rewrite::Relevel => Occurrence::Answered(id),
            Rewrite::Environment => {
                if position < depth {
                    return Occurrence::Answered(id);
                }
                // reason: position is at or past depth, so the difference is
                // the index counted from the environment's innermost entry.
                let counted = u32::from(arith::saturating_sub(
                    arith::Int::from(position.0),
                    arith::Int::from(depth.0),
                ));
                let entry = usize::try_from(counted)
                    .ok()
                    .and_then(|counted| self.environment.get(counted).copied());
                match entry {
                    Some(replacement) if depth == Binders::NONE => {
                        Occurrence::Answered(replacement)
                    },
                    Some(replacement) => Occurrence::Carried(replacement, depth),
                    None => {
                        // reason: an index past the environment counts out of
                        // it; the environment's length is far below the u32
                        // ceiling, and a saturating step keeps the walk total.
                        let length = u32::try_from(self.environment.len()).unwrap_or(u32::MAX);
                        let lowered = u32::from(arith::saturating_sub(
                            arith::Int::from(position.0),
                            arith::Int::from(length),
                        ));
                        Occurrence::Answered(
                            self.arena
                                .value_variable(Zone::Intuitionistic, DeBruijnIndex::from(lowered)),
                        )
                    },
                }
            },
        }
    }

    /// Mint the occurrence one binder further in than `position`.
    ///
    /// # Specification
    /// - requires: `position` is strictly above some depth, so it is positive.
    /// - ensures: a fresh intuitionistic variable at `position - 1`.
    /// - provides: the lowering half of substitution.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — lowering index one and an index above a crossed
    ///   binder distinguishes subtraction from identity and the wrong zone.
    /// - witness: `rewrite::tests::occurrence_rules_separate_depth_boundaries`
    #[spec(requires: position.0 > 0,
        ensures: |ret| matches!(self.arena.value(ret), Some(Value::Variable { zone: Zone::Intuitionistic, index })
            if u32::from(*index).checked_add(1) == Some(position.0)))]
    fn lowered(
        &mut self,
        position: Binders,
    ) -> ValueId
    {
        // reason: the caller established position > depth >= 0, and a
        // saturating step keeps the walk total on any input.
        let lowered = u32::from(arith::saturating_sub(
            arith::Int::from(position.0),
            arith::Int::from(1_u32),
        ));
        self.arena
            .value_variable(Zone::Intuitionistic, DeBruijnIndex::from(lowered))
    }

    /// Schedule `node`'s children, each at the depth its position sits at.
    ///
    /// **The binding positions are the whole content of this function.** A
    /// lambda binds for its body, a static lambda for its body, a bind for
    /// its body and not its bound computation, a case for each branch and not
    /// its scrutinee, a split for its body under one binder per component and
    /// for a dependent motive under one binder of the scrutinee, the
    /// dependent arrow for its codomain and not its domain, and the dependent
    /// pair for its second factor and not its first. A quote and a decode
    /// bind nothing: they cross between terms and types at the depth they
    /// stand at. Nor does a static Pi: its codomain stands in the ambient
    /// context.
    ///
    /// # Specification
    /// - requires: `depth` is the number of binders crossed to reach `node`.
    /// - ensures: one open task per child, pushed in reverse so the children
    ///   close in order, each at the depth its position sits at and under the
    ///   node's rewrite, a delinearisation counting the linear binder a session
    ///   action or a memory form opens over the child; a leaf and an unreadable
    ///   node push nothing.
    /// - provides: the only statement of where the core language binds.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — lambda and static lambda bind their bodies, bind
    ///   scopes only its continuation, case scopes both branches, a split
    ///   scopes its body under one binder per component, and Pi scopes only its
    ///   codomain; static Pi, arrow, quote and decode do not bind. Exact
    ///   rewritten indices distinguish each boundary and the untouched linear
    ///   zone; L2 generated codomains cover their nested combinations.
    /// - witness: `rewrite::tests::binding_sites_distinguish_free_bound_and_linear_indices`
    /// - witness: `rewrite::tests::instantiating_a_codomain_avoids_capture`
    #[spec(
        captures: [pending = self.tasks.len(), ready = self.results.len(), split = match node {
            | Node::Computation(id) => match self.arena.computation(id) {
                | Some(&Computation::Split { arity, .. }) => Some(depth.deeper_by(arity)),
                | _ => None,
            },
            | Node::Value(_) | Node::ValueType(_) | Node::CompType(_) => None,
        }, children = match node {
        | Node::Value(id) => self.arena.value(id).map_or(0_usize, |matched_native_node| match *matched_native_node {
Value::Reify(ref frames) => frames.iter().filter(|frame| !matches!(frame, crate::control::StackFrame::Project(_))).count(),
Value::Constructor { ref fields, .. } => fields.len().saturating_add(1),
Value::Record(ref fields) => fields.len(),
Value::Tuple(ref components) => components.len(),
Value::Recorded(ref moves) => moves.iter().filter(|movement| matches!(movement.payload(), quenchant_shape::shape::Maybe::Present(_))).count(),
Value::ListNil | Value::Primitive { .. } | Value::Variable { .. } | Value::Constant(_) | Value::Literal(_) | Value::Hole(_) => 0_usize,
Value::ListCons(..) | Value::StaticApplication(..) | Value::PathProduct(..) | Value::Funext(..) | Value::Equiv(..) | Value::Univalence(..) | Value::Ua { .. } | Value::Then(..) | Value::FlowProduct(..) | Value::FunctionFlow(..) | Value::Ascribe { .. } => 2,
Value::PathEquiv { .. } | Value::SessionRelated { .. } => 3,
Value::Injection(..) | Value::Thunk(_) | Value::Lift { .. } | Value::Quote(_) | Value::QuoteComputation(_) | Value::StaticLambda(_) | Value::PathRefl(_) | Value::Here(_) | Value::Stay(_) | Value::Forward(_) | Value::Returned(_) | Value::Nested(_) | Value::Run(_) | Value::Mark { .. } => 1,
}),
        | Node::Computation(id) => self.arena.computation(id).map_or(0_usize, |matched_native_node| match *matched_native_node {
Computation::Perform { ref signature, .. } => 1_usize.saturating_add(signature.types().count()),
Computation::Exercise { ref signature, .. } => 2_usize.saturating_add(signature.types().count()),
Computation::Handle { ref signature, ref clauses, .. } | Computation::Scope { ref signature, ref clauses, .. } => 2_usize.saturating_add(signature.types().count()).saturating_add(clauses.len()),
Computation::ListFold { .. } | Computation::TelescopeTransport { .. } => 5,
Computation::ListCase { .. } | Computation::PathTransport { .. } | Computation::Ride { .. } | Computation::Split { motive: SplitMotive::Scrutinee(_), .. } => 3,
Computation::Primitive { ref arguments, .. } => arguments.len(),
Computation::DataCase { ref branches, .. } => branches.len().saturating_add(2),
Computation::Reset(_) | Computation::Shift(_) | Computation::Project(..) | Computation::RecordProjection(..) | Computation::TupleProjection(..) | Computation::Lambda(_) | Computation::Fixpoint { .. } | Computation::Return(_) | Computation::Abandon(_) | Computation::Force(_) | Computation::Mark { .. } => 1,
Computation::Resume(..) | Computation::Application(..) | Computation::Bind(..) | Computation::Ascribe { .. } | Computation::Transport(..) | Computation::Split { motive: SplitMotive::Ambient, .. } => 2,
Computation::With(ref components) => components.len(),
Computation::Case { ref branches, .. } => branches.len().saturating_add(1),
Computation::Hole(_) => 0_usize,
Computation::Session(ref action) => action.values().count().saturating_add(action.computations().count()).saturating_add(action.value_types().count()),
Computation::Memory(ref form) => form.values().count().saturating_add(form.computations().count()),
Computation::World(ref form) => form.values().count().saturating_add(form.computations().count()),
}),
        | Node::ValueType(id) => self.arena.value_type(id).map_or(0_usize, |matched_native_node| match *matched_native_node {
ValueType::Data { ref arguments, .. } => arguments.len(),
ValueType::Record(ref fields) => fields.len(),
ValueType::Product(ref components) | ValueType::Sum(ref components) => components.len(),
ValueType::Base(_) | ValueType::Universe { .. } | ValueType::Abstract(_) | ValueType::Unknown | ValueType::Buffer => 0_usize,
ValueType::Session(ref session) => session.payloads().len(),
ValueType::Capability { ref authority, .. } => authority.types().count(),
ValueType::World(ref ty) => ty.types().count(),
ValueType::Stack { .. } | ValueType::StaticPi { .. } | ValueType::Sigma { .. } | ValueType::PathUniverse(..) => 2,
ValueType::Path { .. } | ValueType::Flow { .. } => 3,
ValueType::List(_) | ValueType::Thunk(_) | ValueType::Lift { .. } | ValueType::Element { .. } | ValueType::Run(_) | ValueType::Prefix(_) | ValueType::Staged { .. } | ValueType::Kept { .. } => 1,
}),
        | Node::CompType(id) => match self.arena.comp_type(id) {
            | None | Some(&CompType::Unknown) => 0_usize,
            | Some(&CompType::Returner { ref effects, .. }) => 1_usize.saturating_add(effects.types().count()),
            | Some(&CompType::Element { .. }) => 1,
            Some(&CompType::Arrow { .. } | &CompType::Pi { .. }) => 2,
            Some(&CompType::With(ref components)) => components.len(),
            Some(&CompType::Codata { ref arguments, .. }) => arguments.len(),
        },
    }],
        ensures: self.results.len() == ready && pending.checked_add(children) == Some(self.tasks.len())
            && self.tasks.get(pending..).is_some_and(|tasks| tasks.iter().all(|task|
                matches!(task, Task::Open(_, at, step) if (*step == rewrite || *step == rewrite.past_linear(Binders::ONE)) && (*at == depth || *at == depth.deeper() || *at == depth.deeper().deeper() || Some(*at) == split)))),
    )]
    fn push_children(
        &mut self,
        node: Node,
        depth: Binders,
        rewrite: Rewrite,
    )
    {
        let open = |node, at| Task::Open(node, at, rewrite);
        match node {
            Node::Value(id) => match self.arena.value(id) {
                Some(&Value::Constructor {
                    datatype,
                    ref fields,
                    ..
                }) => {
                    self.tasks.extend(
                        fields
                            .iter()
                            .rev()
                            .map(|&field| open(Node::Value(field), depth)),
                    );
                    self.tasks.push(open(Node::ValueType(datatype), depth));
                },
                Some(&Value::Record(ref fields)) => self.tasks.extend(
                    fields
                        .values()
                        .rev()
                        .map(|&field| open(Node::Value(field), depth)),
                ),
                Some(&Value::Reify(ref frames)) => {
                    for frame in frames.iter().rev() {
                        match *frame {
                            crate::control::StackFrame::Apply(value) => {
                                self.tasks.push(open(Node::Value(value), depth));
                            },
                            crate::control::StackFrame::Bind(body) => self
                                .tasks
                                .push(open(Node::Computation(body), depth.deeper())),
                            crate::control::StackFrame::Project(_) => {},
                        }
                    }
                },
                Some(
                    &Value::Primitive { .. }
                    | &Value::Variable { .. }
                    | &Value::Constant(_)
                    | &Value::ListNil
                    | &Value::Literal(_)
                    | &Value::Hole(_),
                )
                | None => {},
                Some(&Value::PathEquiv {
                    path_type,
                    forward,
                    backward,
                    ..
                }) => {
                    self.tasks.push(open(Node::Value(backward), depth));
                    self.tasks.push(open(Node::Value(forward), depth));
                    self.tasks.push(open(Node::ValueType(path_type), depth));
                },
                Some(&Value::Ascribe { value, ty }) => {
                    self.tasks.push(open(Node::ValueType(ty), depth));
                    self.tasks.push(open(Node::Value(value), depth));
                },
                Some(
                    &Value::PathRefl(body)
                    | &Value::Here(body)
                    | &Value::Injection(_, body)
                    | &Value::Stay(body)
                    | &Value::Forward(body)
                    | &Value::Lift { body, .. }
                    | &Value::Mark { body, .. },
                ) => self.tasks.push(open(Node::Value(body), depth)),
                Some(
                    &(Value::Returned(computation)
                    | Value::Nested(computation)
                    | Value::Run(computation)),
                ) => {
                    self.tasks.push(open(Node::Computation(computation), depth));
                },
                Some(
                    &Value::ListCons(first, second)
                    | &Value::PathProduct(first, second)
                    | &Value::Funext(first, second)
                    | &Value::Equiv(first, second)
                    | &Value::Univalence(first, second)
                    | &Value::Then(first, second)
                    | &Value::FlowProduct(first, second)
                    | &Value::FunctionFlow(first, second)
                    | &Value::Ua {
                        forward: first,
                        backward: second,
                        ..
                    }
                    | &Value::StaticApplication(first, second),
                ) => {
                    self.tasks.push(open(Node::Value(second), depth));
                    self.tasks.push(open(Node::Value(first), depth));
                },
                Some(&Value::SessionRelated {
                    source,
                    target,
                    payloads,
                    ..
                }) => {
                    self.tasks.push(open(Node::Value(payloads), depth));
                    self.tasks.push(open(Node::Value(target), depth));
                    self.tasks.push(open(Node::Value(source), depth));
                },
                Some(&Value::Tuple(ref components)) => self.tasks.extend(
                    components
                        .iter()
                        .rev()
                        .map(|&component| open(Node::Value(component), depth)),
                ),
                Some(&Value::Recorded(ref moves)) => self.tasks.extend(
                    moves
                        .iter()
                        .rev()
                        .filter_map(|movement| match movement.payload() {
                            quenchant_shape::shape::Maybe::Present(payload) => Some(payload),
                            quenchant_shape::shape::Maybe::Absent(_) => None,
                        })
                        .map(|payload| open(Node::Value(payload), depth)),
                ),
                Some(&Value::Thunk(body)) => {
                    self.tasks.push(open(Node::Computation(body), depth));
                },
                Some(&Value::Quote(quoted)) => {
                    self.tasks.push(open(Node::ValueType(quoted), depth));
                },
                Some(&Value::QuoteComputation(quoted)) => {
                    self.tasks.push(open(Node::CompType(quoted), depth));
                },
                Some(&Value::StaticLambda(body)) => {
                    self.tasks.push(open(Node::Value(body), depth.deeper()));
                },
            },
            Node::Computation(id) => match self.arena.computation(id) {
                Some(&Computation::Perform {
                    ref signature,
                    payload,
                    ..
                }) => {
                    self.tasks.push(open(Node::Value(payload), depth));
                    self.tasks.extend(
                        signature
                            .types()
                            .rev()
                            .map(|ty| open(Node::ValueType(ty), depth)),
                    );
                },
                Some(&Computation::Exercise {
                    capability,
                    ref signature,
                    payload,
                    ..
                }) => {
                    self.tasks.push(open(Node::Value(payload), depth));
                    self.tasks.push(open(Node::Value(capability), depth));
                    self.tasks.extend(
                        signature
                            .types()
                            .rev()
                            .map(|ty| open(Node::ValueType(ty), depth)),
                    );
                },
                Some(&Computation::Scope {
                    ref signature,
                    subject,
                    on_return,
                    ref clauses,
                }) => {
                    self.tasks.extend(clauses.iter().rev().map(|clause| {
                        open(Node::Computation(clause.body), depth.deeper().deeper())
                    }));
                    self.tasks
                        .push(open(Node::Computation(on_return), depth.deeper()));
                    self.tasks
                        .push(open(Node::Computation(subject), depth.deeper()));
                    self.tasks.extend(
                        signature
                            .types()
                            .rev()
                            .map(|ty| open(Node::ValueType(ty), depth)),
                    );
                },
                Some(&Computation::Handle {
                    ref signature,
                    subject,
                    on_return,
                    ref clauses,
                }) => {
                    self.tasks.extend(clauses.iter().rev().map(|clause| {
                        open(Node::Computation(clause.body), depth.deeper().deeper())
                    }));
                    self.tasks
                        .push(open(Node::Computation(on_return), depth.deeper()));
                    self.tasks.push(open(Node::Computation(subject), depth));
                    self.tasks.extend(
                        signature
                            .types()
                            .rev()
                            .map(|ty| open(Node::ValueType(ty), depth)),
                    );
                },
                Some(&Computation::Resume(stack, body)) => {
                    self.tasks.push(open(Node::Computation(body), depth));
                    self.tasks.push(open(Node::Value(stack), depth));
                },
                // A dependent split's motive binds the scrutinee; the body
                // binds every component.
                Some(&Computation::Split {
                    scrutinee,
                    arity,
                    motive,
                    body,
                }) => {
                    self.tasks
                        .push(open(Node::Computation(body), depth.deeper_by(arity)));
                    if let SplitMotive::Scrutinee(motive) = motive {
                        self.tasks
                            .push(open(Node::CompType(motive), depth.deeper()));
                    }
                    self.tasks.push(open(Node::Value(scrutinee), depth));
                },
                Some(&Computation::With(ref components)) => {
                    self.tasks.extend(
                        components
                            .iter()
                            .rev()
                            .map(|&component| open(Node::Computation(component), depth)),
                    );
                },
                Some(&Computation::Ascribe { body, ty }) => {
                    self.tasks.push(open(Node::CompType(ty), depth));
                    self.tasks.push(open(Node::Computation(body), depth));
                },
                Some(
                    &(Computation::Reset(body)
                    | Computation::Project(_, body)
                    | Computation::Mark { body, .. }),
                ) => {
                    self.tasks.push(open(Node::Computation(body), depth));
                },
                Some(&Computation::ListFold {
                    element,
                    result,
                    list,
                    on_nil,
                    on_cons,
                }) => {
                    self.tasks
                        .push(open(Node::Computation(on_cons), depth.deeper().deeper()));
                    self.tasks.push(open(Node::Computation(on_nil), depth));
                    self.tasks.push(open(Node::Value(list), depth));
                    self.tasks.push(open(Node::ValueType(result), depth));
                    self.tasks.push(open(Node::ValueType(element), depth));
                },
                Some(&Computation::ListCase {
                    list,
                    on_nil,
                    on_cons,
                }) => {
                    self.tasks
                        .push(open(Node::Computation(on_cons), depth.deeper().deeper()));
                    self.tasks.push(open(Node::Computation(on_nil), depth));
                    self.tasks.push(open(Node::Value(list), depth));
                },
                Some(&Computation::Primitive { ref arguments, .. }) => self.tasks.extend(
                    arguments
                        .iter()
                        .rev()
                        .map(|&argument| open(Node::Value(argument), depth)),
                ),
                Some(&Computation::DataCase {
                    scrutinee,
                    motive,
                    ref branches,
                    ..
                }) => {
                    self.tasks.extend(
                        branches
                            .iter()
                            .rev()
                            .map(|&branch| open(Node::Computation(branch), depth)),
                    );
                    self.tasks
                        .push(open(Node::CompType(motive), depth.deeper()));
                    self.tasks.push(open(Node::Value(scrutinee), depth));
                },
                Some(
                    &(Computation::RecordProjection(record, _)
                    | Computation::TupleProjection(record, _)),
                ) => {
                    self.tasks.push(open(Node::Value(record), depth));
                },
                None | Some(&Computation::Hole(_)) => {},
                Some(&Computation::Transport(path, value)) => {
                    self.tasks.push(open(Node::Value(value), depth));
                    self.tasks.push(open(Node::Value(path), depth));
                },
                Some(&Computation::PathTransport {
                    motive,
                    path,
                    value,
                }) => {
                    self.tasks.push(open(Node::Value(value), depth));
                    self.tasks.push(open(Node::Value(path), depth));
                    self.tasks
                        .push(open(Node::ValueType(motive), depth.deeper()));
                },
                Some(&Computation::Ride {
                    motive,
                    flow,
                    value,
                }) => {
                    self.tasks.push(open(Node::Value(value), depth));
                    self.tasks.push(open(Node::Value(flow), depth));
                    self.tasks
                        .push(open(Node::ValueType(motive), depth.deeper()));
                },
                // The motive's own arrows bind the telescope.
                Some(&Computation::TelescopeTransport {
                    motive,
                    path,
                    start,
                    over,
                    value,
                }) => {
                    for child in [value, over, start, path] {
                        self.tasks.push(open(Node::Value(child), depth));
                    }
                    self.tasks.push(open(Node::CompType(motive), depth));
                },
                Some(
                    &(Computation::Lambda(body)
                    | Computation::Fixpoint { body, .. }
                    | Computation::Shift(body)),
                ) => self
                    .tasks
                    .push(open(Node::Computation(body), depth.deeper())),
                Some(&Computation::Application(head, argument)) => {
                    self.tasks.push(open(Node::Value(argument), depth));
                    self.tasks.push(open(Node::Computation(head), depth));
                },
                Some(
                    &Computation::Return(value)
                    | &Computation::Abandon(value)
                    | &Computation::Force(value),
                ) => {
                    self.tasks.push(open(Node::Value(value), depth));
                },
                Some(&Computation::Bind(bound, body)) => {
                    self.tasks
                        .push(open(Node::Computation(body), depth.deeper()));
                    self.tasks.push(open(Node::Computation(bound), depth));
                },
                Some(&Computation::Case {
                    scrutinee,
                    ref branches,
                }) => {
                    self.tasks.extend(
                        branches
                            .iter()
                            .rev()
                            .map(|&branch| open(Node::Computation(branch), depth.deeper())),
                    );
                    self.tasks.push(open(Node::Value(scrutinee), depth));
                },
                // A fork binds into the linear zone: the intuitionistic depth
                // its child and parent stand at is the fork's own, and a
                // delinearisation counts the linear binders each child is past.
                Some(&Computation::Session(ref action)) => {
                    let step = rewrite.past_linear(action.child_binders());
                    self.tasks.extend(
                        action
                            .computations()
                            .rev()
                            .map(|child| Task::Open(Node::Computation(child), depth, step)),
                    );
                    self.tasks.extend(
                        action
                            .values()
                            .rev()
                            .map(|child| open(Node::Value(child), depth)),
                    );
                    self.tasks.extend(
                        action
                            .value_types()
                            .rev()
                            .map(|child| open(Node::ValueType(child), depth)),
                    );
                },
                // A memory form binds only into the linear zone: every child
                // stands at the form's own intuitionistic depth, past the
                // linear binders the form opens over it.
                Some(&Computation::Memory(ref form)) => {
                    self.tasks
                        .extend(form.scoped().rev().map(|(child, binders)| {
                            Task::Open(
                                Node::Computation(child),
                                depth,
                                rewrite.past_linear(binders),
                            )
                        }));
                    self.tasks.extend(
                        form.values()
                            .rev()
                            .map(|child| open(Node::Value(child), depth)),
                    );
                },
                // A `leta`'s body stands under the one intuitionistic binder
                // it opens; every other child stands at the form's depth.
                Some(&Computation::World(ref form)) => {
                    self.tasks
                        .extend(form.scoped().rev().map(|(child, binders)| {
                            open(Node::Computation(child), depth.beyond(binders))
                        }));
                    self.tasks.extend(
                        form.values()
                            .rev()
                            .map(|child| open(Node::Value(child), depth)),
                    );
                },
            },
            Node::ValueType(id) => {
                if let Some(matched_native_node) = self.arena.value_type(id) {
                    match *matched_native_node {
                        ValueType::Stack { input, output } => {
                            self.tasks.push(open(Node::CompType(output), depth));
                            self.tasks.push(open(Node::CompType(input), depth));
                        },
                        ValueType::List(element)
                        | ValueType::Staged { base: element, .. }
                        | ValueType::Kept { value: element, .. } => {
                            self.tasks.push(open(Node::ValueType(element), depth));
                        },
                        ValueType::Data { ref arguments, .. } => self.tasks.extend(
                            arguments
                                .iter()
                                .rev()
                                .map(|&argument| open(Node::Value(argument), depth)),
                        ),
                        ValueType::Record(ref fields) => self.tasks.extend(
                            fields
                                .values()
                                .rev()
                                .map(|&field| open(Node::ValueType(field), depth)),
                        ),
                        ValueType::Product(ref components) | ValueType::Sum(ref components) => {
                            self.tasks.extend(
                                components
                                    .iter()
                                    .rev()
                                    .map(|&component| open(Node::ValueType(component), depth)),
                            );
                        },
                        ValueType::Base(_)
                        | ValueType::Universe { .. }
                        | ValueType::Abstract(_)
                        | ValueType::Unknown
                        | ValueType::Buffer => {},
                        ValueType::Capability { ref authority, .. } => self.tasks.extend(
                            authority
                                .types()
                                .rev()
                                .map(|ty| open(Node::ValueType(ty), depth)),
                        ),
                        ValueType::World(ref ty) => self
                            .tasks
                            .extend(ty.types().map(|ty| open(Node::ValueType(ty), depth))),
                        ValueType::StaticPi {
                            domain: first,
                            codomain: second,
                        } => {
                            self.tasks.push(open(Node::ValueType(second), depth));
                            self.tasks.push(open(Node::ValueType(first), depth));
                        },
                        ValueType::Sigma { first, second } => {
                            self.tasks
                                .push(open(Node::ValueType(second), depth.deeper()));
                            self.tasks.push(open(Node::ValueType(first), depth));
                        },
                        ValueType::PathUniverse(source, target) => {
                            self.tasks.push(open(Node::Value(target), depth));
                            self.tasks.push(open(Node::Value(source), depth));
                        },
                        ValueType::Path {
                            carrier,
                            left,
                            right,
                        }
                        | ValueType::Flow {
                            carrier,
                            source: left,
                            target: right,
                        } => {
                            self.tasks.push(open(Node::Value(right), depth));
                            self.tasks.push(open(Node::Value(left), depth));
                            self.tasks.push(open(Node::ValueType(carrier), depth));
                        },
                        ValueType::Run(session) | ValueType::Prefix(session) => {
                            self.tasks.push(open(Node::Value(session), depth));
                        },
                        ValueType::Thunk(body) => {
                            self.tasks.push(open(Node::CompType(body), depth));
                        },
                        ValueType::Lift { inner, .. } => {
                            self.tasks.push(open(Node::ValueType(inner), depth));
                        },
                        ValueType::Element { code, .. } => {
                            self.tasks.push(open(Node::Value(code), depth));
                        },
                        ValueType::Session(ref session) => self.tasks.extend(
                            session
                                .payloads()
                                .iter()
                                .rev()
                                .map(|&payload| open(Node::ValueType(payload), depth)),
                        ),
                    }
                }
            },
            Node::CompType(id) => match self.arena.comp_type(id) {
                Some(&CompType::With(ref components)) => self.tasks.extend(
                    components
                        .iter()
                        .rev()
                        .map(|&component| open(Node::CompType(component), depth)),
                ),
                None | Some(&CompType::Unknown) => {},
                Some(&CompType::Codata { ref arguments, .. }) => self.tasks.extend(
                    arguments
                        .iter()
                        .rev()
                        .map(|&argument| open(Node::Value(argument), depth)),
                ),
                Some(&CompType::Returner {
                    result,
                    ref effects,
                }) => {
                    self.tasks.extend(
                        effects
                            .types()
                            .rev()
                            .map(|ty| open(Node::ValueType(ty), depth)),
                    );
                    self.tasks.push(open(Node::ValueType(result), depth));
                },
                Some(&CompType::Arrow { domain, codomain }) => {
                    self.tasks.push(open(Node::CompType(codomain), depth));
                    self.tasks.push(open(Node::ValueType(domain), depth));
                },
                Some(&CompType::Pi { domain, codomain }) => {
                    self.tasks
                        .push(open(Node::CompType(codomain), depth.deeper()));
                    self.tasks.push(open(Node::ValueType(domain), depth));
                },
                Some(&CompType::Element { code, .. }) => {
                    self.tasks.push(open(Node::Value(code), depth));
                },
            },
        }
    }

    /// Pop one child's result, read in `family`, or fall back to the child.
    ///
    /// The fallback is unreachable: an open pushed one result per child
    /// before its parent's close ran. Reading it as unchanged is the fail-safe
    /// direction, since it cannot fabricate a node.
    ///
    /// # Specification
    /// - requires: nothing; an empty stack is admissible.
    /// - ensures: removes and returns the last result, or `original` when
    ///   empty.
    /// - provides: the result-stack consumption shared by the family adapters.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — consumer-visible reconstruction separates wrong
    ///   family extraction and child order. Empty or mismatched internal stacks
    ///   are not reachable through the public rewrite operations.
    /// - witness: `rewrite::tests::congruences_preserve_formers_and_child_order`
    #[spec(captures: [top = results.last().copied(), ready = results.len()],
        ensures: |ret| ret == top.unwrap_or(original) && results.len() == ready.saturating_sub(1))]
    fn popped(
        results: &mut Vec<Node>,
        original: Node,
    ) -> Node
    {
        results.pop().unwrap_or(original)
    }

    /// Pop a value child's result.
    ///
    /// # Specification
    /// - requires: nothing; an empty or mismatched stack is admissible.
    /// - ensures: consumes one result if present; returns its id only in this
    ///   family, otherwise preserving `original`.
    /// - provides: the family-specific result-stack projection.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — consumer-visible reconstruction separates wrong
    ///   family extraction and child order. Empty or mismatched internal stacks
    ///   are not reachable through the public rewrite operations.
    /// - witness: `rewrite::tests::congruences_preserve_formers_and_child_order`
    #[spec(captures: [top = results.last().copied(), ready = results.len()],
        ensures: |ret| results.len() == ready.saturating_sub(1) && ret == match top {
            | Some(Node::Value(id)) => id,
            | Some(Node::Computation(_) | Node::ValueType(_) | Node::CompType(_)) | None => original,
        })]
    fn value(
        results: &mut Vec<Node>,
        original: ValueId,
    ) -> ValueId
    {
        match Self::popped(results, Node::Value(original)) {
            Node::Value(id) => id,
            Node::Computation(_) | Node::ValueType(_) | Node::CompType(_) => original,
        }
    }

    /// Pop a computation child's result.
    ///
    /// # Specification
    /// - requires: nothing; an empty or mismatched stack is admissible.
    /// - ensures: consumes one result if present; returns its id only in this
    ///   family, otherwise preserving `original`.
    /// - provides: the family-specific result-stack projection.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — consumer-visible reconstruction separates wrong
    ///   family extraction and child order. Empty or mismatched internal stacks
    ///   are not reachable through the public rewrite operations.
    /// - witness: `rewrite::tests::congruences_preserve_formers_and_child_order`
    #[spec(captures: [top = results.last().copied(), ready = results.len()],
        ensures: |ret| results.len() == ready.saturating_sub(1) && ret == match top {
            | Some(Node::Computation(id)) => id,
            | Some(Node::Value(_) | Node::ValueType(_) | Node::CompType(_)) | None => original,
        })]
    fn computation(
        results: &mut Vec<Node>,
        original: ComputationId,
    ) -> ComputationId
    {
        match Self::popped(results, Node::Computation(original)) {
            Node::Computation(id) => id,
            Node::Value(_) | Node::ValueType(_) | Node::CompType(_) => original,
        }
    }

    /// Pop a value-type child's result.
    ///
    /// # Specification
    /// - requires: nothing; an empty or mismatched stack is admissible.
    /// - ensures: consumes one result if present; returns its id only in this
    ///   family, otherwise preserving `original`.
    /// - provides: the family-specific result-stack projection.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — consumer-visible reconstruction separates wrong
    ///   family extraction and child order. Empty or mismatched internal stacks
    ///   are not reachable through the public rewrite operations.
    /// - witness: `rewrite::tests::congruences_preserve_formers_and_child_order`
    #[spec(captures: [top = results.last().copied(), ready = results.len()],
        ensures: |ret| results.len() == ready.saturating_sub(1) && ret == match top {
            | Some(Node::ValueType(id)) => id,
            | Some(Node::Value(_) | Node::Computation(_) | Node::CompType(_)) | None => original,
        })]
    fn value_type(
        results: &mut Vec<Node>,
        original: ValueTypeId,
    ) -> ValueTypeId
    {
        match Self::popped(results, Node::ValueType(original)) {
            Node::ValueType(id) => id,
            Node::Value(_) | Node::Computation(_) | Node::CompType(_) => original,
        }
    }

    /// Pop a computation-type child's result.
    ///
    /// # Specification
    /// - requires: nothing; an empty or mismatched stack is admissible.
    /// - ensures: consumes one result if present; returns its id only in this
    ///   family, otherwise preserving `original`.
    /// - provides: the family-specific result-stack projection.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — consumer-visible reconstruction separates wrong
    ///   family extraction and child order. Empty or mismatched internal stacks
    ///   are not reachable through the public rewrite operations.
    /// - witness: `rewrite::tests::congruences_preserve_formers_and_child_order`
    #[spec(captures: [top = results.last().copied(), ready = results.len()],
        ensures: |ret| results.len() == ready.saturating_sub(1) && ret == match top {
            | Some(Node::CompType(id)) => id,
            | Some(Node::Value(_) | Node::Computation(_) | Node::ValueType(_)) | None => original,
        })]
    fn comp_type(
        results: &mut Vec<Node>,
        original: CompTypeId,
    ) -> CompTypeId
    {
        match Self::popped(results, Node::CompType(original)) {
            Node::CompType(id) => id,
            Node::Value(_) | Node::Computation(_) | Node::ValueType(_) => original,
        }
    }

    /// Combine `node`'s rewritten children into its own result, minting only
    /// where a child changed.
    ///
    /// Children were scheduled to close in order, so the last child's result
    /// is on top: each arm pops in reverse.
    ///
    /// # Specification
    /// - requires: the results stack holds one result per child of `node`.
    /// - ensures: `node` itself when no child changed, and a node minted
    ///   through the arena's constructors over the changed children otherwise —
    ///   so a decode whose code became a quote answers the quoted type. A leaf,
    ///   a linear occurrence and an unreadable node answer themselves.
    /// - provides: the combining half of the engine.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — unchanged and changed children of every compound
    ///   former distinguish identity reuse, swapped children, wrong-family
    ///   results and missed quote decoding through exact reconstructed nodes.
    /// - witness: `rewrite::tests::congruences_preserve_formers_and_child_order`
    #[spec(ensures: |ret| core::mem::discriminant(&ret) == core::mem::discriminant(&node))]
    fn close(
        &mut self,
        node: Node,
    ) -> Node
    {
        match node {
            Node::Value(id) => Node::Value(self.close_value(id)),
            Node::Computation(id) => Node::Computation(self.close_computation(id)),
            Node::ValueType(id) => Node::ValueType(self.close_value_type(id)),
            Node::CompType(id) => Node::CompType(self.close_comp_type(id)),
        }
    }

    /// Pop a signature's rewritten type edges in reverse canonical order.
    ///
    /// # Specification
    /// - ensures: preserves interface identity and operation coverage.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — signatures beneath binders distinguish payload and
    ///   reply scope.
    /// - witness: `control::tests::stack_literals_preserve_binder_scope`
    #[spec(ensures: |ret| ret.name() == original.name() && ret.operations().len() == original.operations().len())]
    fn signature(
        results: &mut Vec<Node>,
        original: &crate::effect::EffectSig,
    ) -> crate::effect::EffectSig
    {
        match original.try_map_types(crate::effect::TypeOrder::Reverse, |ty| {
            Ok::<_, core::convert::Infallible>(Self::value_type(results, ty))
        }) {
            Ok(signature) => signature,
            Err(never) => match never {},
        }
    }

    /// Combine a value node.
    ///
    /// # Specification
    /// - requires: the result stack holds rewritten children in source order.
    /// - ensures: consumes those children; unchanged children reuse `id`, while
    ///   changed children preserve the former except for quote decoding.
    /// - provides: the family-specific reconstruction step.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — unchanged and changed children of each former are
    ///   read back exactly, with unequal children separating reversed stack
    ///   order. Matching quotes exercise decode-on-mint, while leaves and
    ///   missing children preserve their original identity.
    /// - witness: `rewrite::tests::congruences_preserve_formers_and_child_order`
    /// - witness: `rewrite::tests::every_former_is_kept_when_nothing_beneath_it_changes_and_carries_what_does`
    #[spec(
        captures: [ready = self.results.len(), children = self.arena.value(id).map_or(0_usize, |matched_native_node| match *matched_native_node {
Value::Reify(ref frames) => frames.iter().filter(|frame| !matches!(frame, crate::control::StackFrame::Project(_))).count(),
Value::Constructor { ref fields, .. } => fields.len().saturating_add(1),
Value::Record(ref fields) => fields.len(),
Value::Tuple(ref components) => components.len(),
Value::Recorded(ref moves) => moves.iter().filter(|movement| matches!(movement.payload(), quenchant_shape::shape::Maybe::Present(_))).count(),
Value::ListNil | Value::Primitive { .. } | Value::Variable { .. } | Value::Constant(_) | Value::Literal(_) | Value::Hole(_) => 0_usize,
Value::ListCons(..) | Value::StaticApplication(..) | Value::PathProduct(..) | Value::Funext(..) | Value::Equiv(..) | Value::Univalence(..) | Value::Ua { .. } | Value::Then(..) | Value::FlowProduct(..) | Value::FunctionFlow(..) | Value::Ascribe { .. } => 2,
Value::PathEquiv { .. } | Value::SessionRelated { .. } => 3,
Value::Injection(..) | Value::Thunk(_) | Value::Lift { .. } | Value::Quote(_) | Value::QuoteComputation(_) | Value::StaticLambda(_) | Value::PathRefl(_) | Value::Here(_) | Value::Stay(_) | Value::Forward(_) | Value::Returned(_) | Value::Nested(_) | Value::Run(_) | Value::Mark { .. } => 1,
})],
        ensures: |ret| self.results.len() == ready.saturating_sub(children)
            && (ret == id || self.arena.value(id).is_some_and(|original| self.arena.value(ret).is_some_and(|rewritten|
                core::mem::discriminant(original) == core::mem::discriminant(rewritten)))),
    )]
    fn close_value(
        &mut self,
        id: ValueId,
    ) -> ValueId
    {
        let Some(node) = self.arena.value(id)
        else {
            return id;
        };
        match *node {
            Value::Constructor {
                datatype,
                tag,
                ref fields,
            } => {
                let mut changed = None;
                for (index, original) in fields.iter().enumerate().rev() {
                    let rewritten = Self::value(&mut self.results, *original);
                    if rewritten != *original {
                        let changed = changed.get_or_insert_with(|| fields.clone());
                        if let Some(slot) = changed.get_mut(index) {
                            *slot = rewritten;
                        }
                    }
                }
                let rewritten_type = Self::value_type(&mut self.results, datatype);
                if changed.is_none() && rewritten_type == datatype {
                    id
                }
                else {
                    self.arena.value_constructor(
                        rewritten_type,
                        tag,
                        changed.unwrap_or_else(|| fields.clone()),
                    )
                }
            },
            Value::Record(ref fields) => {
                let mut changed = None;
                for (label, original) in fields.iter().rev() {
                    let rewritten = Self::value(&mut self.results, *original);
                    if rewritten != *original {
                        let changed = changed.get_or_insert_with(|| fields.clone());
                        if let Some(slot) = changed.get_mut(label) {
                            *slot = rewritten;
                        }
                    }
                }
                match changed {
                    Some(fields) => self.arena.value_record(fields),
                    None => id,
                }
            },
            Value::Reify(ref frames) => {
                let mut rewritten_frames = None;
                for (index, original) in frames.iter().copied().enumerate().rev() {
                    let rewritten = match original {
                        crate::control::StackFrame::Apply(value) => {
                            crate::control::StackFrame::Apply(Self::value(&mut self.results, value))
                        },
                        crate::control::StackFrame::Bind(body) => crate::control::StackFrame::Bind(
                            Self::computation(&mut self.results, body),
                        ),
                        crate::control::StackFrame::Project(side) => {
                            crate::control::StackFrame::Project(side)
                        },
                    };
                    if rewritten != original {
                        let changed =
                            rewritten_frames.get_or_insert_with(|| alloc::sync::Arc::clone(frames));
                        if let Some(slot) = alloc::sync::Arc::make_mut(changed).get_mut(index) {
                            *slot = rewritten;
                        }
                    }
                }
                match rewritten_frames {
                    Some(frames) => self.arena.value_reify(frames),
                    None => id,
                }
            },
            Value::PathRefl(code) => {
                let rewritten = Self::value(&mut self.results, code);
                if rewritten == code {
                    id
                }
                else {
                    self.arena.value_path_refl(rewritten)
                }
            },
            Value::Here(point) => {
                let rewritten = Self::value(&mut self.results, point);
                if rewritten == point {
                    id
                }
                else {
                    self.arena.value_here(rewritten)
                }
            },
            Value::Univalence(equivalence, forward) => {
                let rewritten_forward = Self::value(&mut self.results, forward);
                let rewritten_equivalence = Self::value(&mut self.results, equivalence);
                if (rewritten_equivalence, rewritten_forward) == (equivalence, forward) {
                    id
                }
                else {
                    self.arena
                        .value_univalence(rewritten_equivalence, rewritten_forward)
                }
            },
            Value::Returned(computation) => {
                let rewritten = Self::computation(&mut self.results, computation);
                if rewritten == computation {
                    id
                }
                else {
                    self.arena.value_returned(rewritten)
                }
            },
            Value::Nested(computation) => {
                let rewritten = Self::computation(&mut self.results, computation);
                if rewritten == computation {
                    id
                }
                else {
                    self.arena.value_nested(rewritten)
                }
            },
            Value::Run(computation) => {
                let rewritten = Self::computation(&mut self.results, computation);
                if rewritten == computation {
                    id
                }
                else {
                    self.arena.value_run(rewritten)
                }
            },
            Value::Ascribe { value, ty } => {
                let rewritten_ty = Self::value_type(&mut self.results, ty);
                let rewritten_value = Self::value(&mut self.results, value);
                if (rewritten_value, rewritten_ty) == (value, ty) {
                    id
                }
                else {
                    self.arena.value_ascribe(rewritten_value, rewritten_ty)
                }
            },
            Value::PathProduct(first, second) => {
                let rewritten_second = Self::value(&mut self.results, second);
                let rewritten_first = Self::value(&mut self.results, first);
                if (rewritten_first, rewritten_second) == (first, second) {
                    id
                }
                else {
                    self.arena
                        .value_path_product(rewritten_first, rewritten_second)
                }
            },
            Value::Funext(left, right) => {
                let rewritten_right = Self::value(&mut self.results, right);
                let rewritten_left = Self::value(&mut self.results, left);
                if (rewritten_left, rewritten_right) == (left, right) {
                    id
                }
                else {
                    self.arena.value_funext(rewritten_left, rewritten_right)
                }
            },
            Value::Equiv(forward, backward) => {
                let rewritten_backward = Self::value(&mut self.results, backward);
                let rewritten_forward = Self::value(&mut self.results, forward);
                if (rewritten_forward, rewritten_backward) == (forward, backward) {
                    id
                }
                else {
                    self.arena
                        .value_equiv(rewritten_forward, rewritten_backward)
                }
            },
            Value::SessionRelated {
                relation,
                source,
                target,
                payloads,
            } => {
                let rewritten_payloads = Self::value(&mut self.results, payloads);
                let rewritten_target = Self::value(&mut self.results, target);
                let rewritten_source = Self::value(&mut self.results, source);
                if (rewritten_source, rewritten_target, rewritten_payloads)
                    == (source, target, payloads)
                {
                    id
                }
                else {
                    self.arena.value_session_related(
                        relation,
                        rewritten_source,
                        rewritten_target,
                        rewritten_payloads,
                    )
                }
            },
            Value::Stay(point) => {
                let rewritten = Self::value(&mut self.results, point);
                if rewritten == point {
                    id
                }
                else {
                    self.arena.value_stay(rewritten)
                }
            },
            Value::Then(first, second) => {
                let rewritten_second = Self::value(&mut self.results, second);
                let rewritten_first = Self::value(&mut self.results, first);
                if (rewritten_first, rewritten_second) == (first, second) {
                    id
                }
                else {
                    self.arena.value_then(rewritten_first, rewritten_second)
                }
            },
            Value::FlowProduct(first, second) => {
                let rewritten_second = Self::value(&mut self.results, second);
                let rewritten_first = Self::value(&mut self.results, first);
                if (rewritten_first, rewritten_second) == (first, second) {
                    id
                }
                else {
                    self.arena
                        .value_flow_product(rewritten_first, rewritten_second)
                }
            },
            Value::Forward(translator) => {
                let rewritten = Self::value(&mut self.results, translator);
                if rewritten == translator {
                    id
                }
                else {
                    self.arena.value_forward(rewritten)
                }
            },
            Value::FunctionFlow(domain, codomain) => {
                let rewritten_codomain = Self::value(&mut self.results, codomain);
                let rewritten_domain = Self::value(&mut self.results, domain);
                if (rewritten_domain, rewritten_codomain) == (domain, codomain) {
                    id
                }
                else {
                    self.arena
                        .value_function_flow(rewritten_domain, rewritten_codomain)
                }
            },
            Value::Recorded(ref moves) => {
                let mut changed: Option<Vec<crate::session::RecordedMove>> = None;
                for (index, original) in moves.iter().enumerate().rev() {
                    let quenchant_shape::shape::Maybe::Present(payload) = original.payload()
                    else {
                        continue;
                    };
                    let rewritten = Self::value(&mut self.results, payload);
                    if rewritten != payload {
                        let changed = changed.get_or_insert_with(|| moves.to_vec());
                        if let Some(slot) = changed.get_mut(index) {
                            *slot = original.carrying(rewritten);
                        }
                    }
                }
                match changed {
                    Some(moves) => self.arena.value_recorded(alloc::sync::Arc::from(moves)),
                    None => id,
                }
            },
            Value::Ua {
                stratum,
                ref sides,
                forward,
                backward,
            } => {
                let rewritten_backward = Self::value(&mut self.results, backward);
                let rewritten_forward = Self::value(&mut self.results, forward);
                if (rewritten_forward, rewritten_backward) == (forward, backward) {
                    id
                }
                else {
                    self.arena.value_ua(
                        stratum,
                        alloc::sync::Arc::clone(sides),
                        rewritten_forward,
                        rewritten_backward,
                    )
                }
            },
            Value::PathEquiv {
                path_type,
                forward,
                backward,
                ref evidence,
            } => {
                let rewritten_backward = Self::value(&mut self.results, backward);
                let rewritten_forward = Self::value(&mut self.results, forward);
                let rewritten_type = Self::value_type(&mut self.results, path_type);
                if (rewritten_type, rewritten_forward, rewritten_backward)
                    == (path_type, forward, backward)
                {
                    id
                }
                else {
                    self.arena.value_path_equiv(
                        rewritten_type,
                        rewritten_forward,
                        rewritten_backward,
                        alloc::sync::Arc::clone(evidence),
                    )
                }
            },
            Value::Primitive { .. }
            | Value::Variable { .. }
            | Value::Constant(_)
            | Value::ListNil
            | Value::Literal(_)
            | Value::Hole(_) => id,
            Value::Mark { mark, body } => {
                let rewritten = Self::value(&mut self.results, body);
                if rewritten == body {
                    id
                }
                else {
                    self.arena.value_mark(mark, rewritten)
                }
            },
            Value::Tuple(ref components) => {
                let mut changed: Option<Vec<ValueId>> = None;
                for (index, original) in components.iter().enumerate().rev() {
                    let rewritten = Self::value(&mut self.results, *original);
                    if rewritten != *original {
                        let changed = changed.get_or_insert_with(|| components.to_vec());
                        if let Some(slot) = changed.get_mut(index) {
                            *slot = rewritten;
                        }
                    }
                }
                match changed {
                    Some(components) => self.arena.value_tuple(&components),
                    None => id,
                }
            },
            Value::ListCons(head, tail) => {
                let new_tail = Self::value(&mut self.results, tail);
                let new_head = Self::value(&mut self.results, head);
                if (new_head, new_tail) == (head, tail) {
                    id
                }
                else {
                    self.arena.value_list_cons(new_head, new_tail)
                }
            },
            Value::Injection(summand, body) => {
                let rewritten = Self::value(&mut self.results, body);
                if rewritten == body {
                    id
                }
                else {
                    self.arena.value_injection(summand, rewritten)
                }
            },
            Value::Thunk(body) => {
                let rewritten = Self::computation(&mut self.results, body);
                if rewritten == body {
                    id
                }
                else {
                    self.arena.value_thunk(rewritten)
                }
            },
            Value::Lift { ref target, body } => {
                let rewritten = Self::value(&mut self.results, body);
                if rewritten == body {
                    id
                }
                else {
                    self.arena.value_lift(target.clone(), rewritten)
                }
            },
            Value::Quote(quoted) => {
                let rewritten = Self::value_type(&mut self.results, quoted);
                if rewritten == quoted {
                    id
                }
                else {
                    self.arena.value_quote(rewritten)
                }
            },
            Value::QuoteComputation(quoted) => {
                let rewritten = Self::comp_type(&mut self.results, quoted);
                if rewritten == quoted {
                    id
                }
                else {
                    self.arena.value_quote_computation(rewritten)
                }
            },
            Value::StaticLambda(body) => {
                let rewritten = Self::value(&mut self.results, body);
                if rewritten == body {
                    id
                }
                else {
                    self.arena.value_static_lambda(rewritten)
                }
            },
            Value::StaticApplication(head, argument) => {
                let rewritten_argument = Self::value(&mut self.results, argument);
                let rewritten_head = Self::value(&mut self.results, head);
                if (rewritten_head, rewritten_argument) == (head, argument) {
                    id
                }
                else {
                    self.arena
                        .value_static_application(rewritten_head, rewritten_argument)
                }
            },
        }
    }

    /// Combine a computation node.
    ///
    /// # Specification
    /// - requires: the result stack holds rewritten children in source order.
    /// - ensures: consumes those children; unchanged children reuse `id`, while
    ///   changed children preserve the former except for quote decoding.
    /// - provides: the family-specific reconstruction step.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — unchanged and changed children of each former are
    ///   read back exactly, with unequal children separating reversed stack
    ///   order. Matching quotes exercise decode-on-mint, while leaves and
    ///   missing children preserve their original identity.
    /// - witness: `rewrite::tests::congruences_preserve_formers_and_child_order`
    /// - witness: `rewrite::tests::every_former_is_kept_when_nothing_beneath_it_changes_and_carries_what_does`
    #[spec(
        captures: [ready = self.results.len(), children = self.arena.computation(id).map_or(0_usize, |matched_native_node| match *matched_native_node {
Computation::Perform { ref signature, .. } => 1_usize.saturating_add(signature.types().count()),
Computation::Exercise { ref signature, .. } => 2_usize.saturating_add(signature.types().count()),
Computation::Handle { ref signature, ref clauses, .. } | Computation::Scope { ref signature, ref clauses, .. } => 2_usize.saturating_add(signature.types().count()).saturating_add(clauses.len()),
Computation::ListFold { .. } | Computation::TelescopeTransport { .. } => 5,
Computation::ListCase { .. } | Computation::PathTransport { .. } | Computation::Ride { .. } | Computation::Split { motive: SplitMotive::Scrutinee(_), .. } => 3,
Computation::Primitive { ref arguments, .. } => arguments.len(),
Computation::DataCase { ref branches, .. } => branches.len().saturating_add(2),
Computation::Reset(_) | Computation::Shift(_) | Computation::Project(..) | Computation::RecordProjection(..) | Computation::TupleProjection(..) | Computation::Lambda(_) | Computation::Fixpoint { .. } | Computation::Return(_) | Computation::Abandon(_) | Computation::Force(_) | Computation::Mark { .. } => 1,
Computation::Resume(..) | Computation::Application(..) | Computation::Bind(..) | Computation::Ascribe { .. } | Computation::Transport(..) | Computation::Split { motive: SplitMotive::Ambient, .. } => 2,
Computation::With(ref components) => components.len(),
Computation::Case { ref branches, .. } => branches.len().saturating_add(1),
Computation::Hole(_) => 0_usize,
Computation::Session(ref action) => action.values().count().saturating_add(action.computations().count()).saturating_add(action.value_types().count()),
Computation::Memory(ref form) => form.values().count().saturating_add(form.computations().count()),
Computation::World(ref form) => form.values().count().saturating_add(form.computations().count()),
})],
        ensures: |ret| self.results.len() == ready.saturating_sub(children)
            && (ret == id || self.arena.computation(id).is_some_and(|original| self.arena.computation(ret).is_some_and(|rewritten|
                core::mem::discriminant(original) == core::mem::discriminant(rewritten)))),
    )]
    fn close_computation(
        &mut self,
        id: ComputationId,
    ) -> ComputationId
    {
        let Some(node) = self.arena.computation(id)
        else {
            return id;
        };
        match *node {
            Computation::Perform {
                ref signature,
                ref operation,
                payload,
            } => {
                let rewritten = Self::value(&mut self.results, payload);
                let rewritten_signature = Self::signature(&mut self.results, signature);
                if rewritten == payload && rewritten_signature == *signature {
                    id
                }
                else {
                    self.arena.computation_perform(
                        rewritten_signature,
                        operation.clone(),
                        rewritten,
                    )
                }
            },
            Computation::Exercise {
                capability,
                ref signature,
                ref operation,
                payload,
            } => {
                let rewritten_payload = Self::value(&mut self.results, payload);
                let rewritten_capability = Self::value(&mut self.results, capability);
                let rewritten_signature = Self::signature(&mut self.results, signature);
                if rewritten_capability == capability
                    && rewritten_payload == payload
                    && rewritten_signature == *signature
                {
                    id
                }
                else {
                    self.arena.computation_exercise(
                        rewritten_capability,
                        rewritten_signature,
                        operation.clone(),
                        rewritten_payload,
                    )
                }
            },
            Computation::Scope {
                ref signature,
                subject,
                on_return,
                ref clauses,
            } => {
                let mut rewritten_clauses = None;
                for (index, clause) in clauses.iter().enumerate().rev() {
                    let rewritten = Self::computation(&mut self.results, clause.body);
                    if rewritten != clause.body {
                        let changed = rewritten_clauses
                            .get_or_insert_with(|| alloc::sync::Arc::clone(clauses));
                        if let Some(slot) = alloc::sync::Arc::make_mut(changed).get_mut(index) {
                            slot.body = rewritten;
                        }
                    }
                }
                let rewritten_return = Self::computation(&mut self.results, on_return);
                let rewritten_subject = Self::computation(&mut self.results, subject);
                let rewritten_signature = Self::signature(&mut self.results, signature);
                if rewritten_clauses.is_none()
                    && (rewritten_return, rewritten_subject) == (on_return, subject)
                    && rewritten_signature == *signature
                {
                    id
                }
                else {
                    self.arena.computation_scope(
                        rewritten_signature,
                        rewritten_subject,
                        rewritten_return,
                        rewritten_clauses.unwrap_or_else(|| alloc::sync::Arc::clone(clauses)),
                    )
                }
            },
            Computation::Handle {
                ref signature,
                subject,
                on_return,
                ref clauses,
            } => {
                let mut rewritten_clauses = None;
                for (index, clause) in clauses.iter().enumerate().rev() {
                    let rewritten = Self::computation(&mut self.results, clause.body);
                    if rewritten != clause.body {
                        let changed = rewritten_clauses
                            .get_or_insert_with(|| alloc::sync::Arc::clone(clauses));
                        if let Some(slot) = alloc::sync::Arc::make_mut(changed).get_mut(index) {
                            slot.body = rewritten;
                        }
                    }
                }
                let rewritten_return = Self::computation(&mut self.results, on_return);
                let rewritten_subject = Self::computation(&mut self.results, subject);
                let rewritten_signature = Self::signature(&mut self.results, signature);
                if rewritten_clauses.is_none()
                    && (rewritten_return, rewritten_subject) == (on_return, subject)
                    && rewritten_signature == *signature
                {
                    id
                }
                else {
                    self.arena.computation_handle(
                        rewritten_signature,
                        rewritten_subject,
                        rewritten_return,
                        rewritten_clauses.unwrap_or_else(|| alloc::sync::Arc::clone(clauses)),
                    )
                }
            },
            Computation::Resume(stack, body) => {
                let rewritten_body = Self::computation(&mut self.results, body);
                let rewritten_stack = Self::value(&mut self.results, stack);
                if (rewritten_stack, rewritten_body) == (stack, body) {
                    id
                }
                else {
                    self.arena
                        .computation_resume(rewritten_stack, rewritten_body)
                }
            },
            Computation::Split {
                scrutinee,
                arity,
                motive,
                body,
            } => {
                let rewritten_body = Self::computation(&mut self.results, body);
                let rewritten_motive = match motive {
                    SplitMotive::Ambient => SplitMotive::Ambient,
                    SplitMotive::Scrutinee(motive) => {
                        SplitMotive::Scrutinee(Self::comp_type(&mut self.results, motive))
                    },
                };
                let rewritten_scrutinee = Self::value(&mut self.results, scrutinee);
                if (rewritten_scrutinee, rewritten_motive, rewritten_body)
                    == (scrutinee, motive, body)
                {
                    id
                }
                else {
                    match rewritten_motive {
                        SplitMotive::Ambient => {
                            self.arena
                                .computation_split(rewritten_scrutinee, arity, rewritten_body)
                        },
                        SplitMotive::Scrutinee(motive) => self.arena.computation_dependent_split(
                            rewritten_scrutinee,
                            arity,
                            motive,
                            rewritten_body,
                        ),
                    }
                }
            },
            Computation::With(ref components) => {
                let mut changed: Option<Vec<ComputationId>> = None;
                for (index, original) in components.iter().enumerate().rev() {
                    let rewritten = Self::computation(&mut self.results, *original);
                    if rewritten != *original {
                        let changed = changed.get_or_insert_with(|| components.to_vec());
                        if let Some(slot) = changed.get_mut(index) {
                            *slot = rewritten;
                        }
                    }
                }
                match changed {
                    Some(components) => self.arena.computation_with(&components),
                    None => id,
                }
            },
            Computation::Ascribe { body, ty } => {
                let rewritten_ty = Self::comp_type(&mut self.results, ty);
                let rewritten_body = Self::computation(&mut self.results, body);
                if (rewritten_body, rewritten_ty) == (body, ty) {
                    id
                }
                else {
                    self.arena.computation_ascribe(rewritten_body, rewritten_ty)
                }
            },
            Computation::Reset(body) => {
                let rewritten = Self::computation(&mut self.results, body);
                if rewritten == body {
                    id
                }
                else {
                    self.arena.computation_reset(rewritten)
                }
            },
            Computation::Shift(body) => {
                let rewritten = Self::computation(&mut self.results, body);
                if rewritten == body {
                    id
                }
                else {
                    self.arena.computation_shift(rewritten)
                }
            },
            Computation::Project(component, body) => {
                let rewritten = Self::computation(&mut self.results, body);
                if rewritten == body {
                    id
                }
                else {
                    self.arena.computation_project(component, rewritten)
                }
            },
            Computation::ListFold {
                element,
                result,
                list,
                on_nil,
                on_cons,
            } => {
                let new_cons = Self::computation(&mut self.results, on_cons);
                let new_nil = Self::computation(&mut self.results, on_nil);
                let new_list = Self::value(&mut self.results, list);
                let new_result = Self::value_type(&mut self.results, result);
                let new_element = Self::value_type(&mut self.results, element);
                if (new_element, new_result, new_list, new_nil, new_cons)
                    == (element, result, list, on_nil, on_cons)
                {
                    id
                }
                else {
                    self.arena.computation_list_fold(
                        new_element,
                        new_result,
                        new_list,
                        new_nil,
                        new_cons,
                    )
                }
            },
            Computation::ListCase {
                list,
                on_nil,
                on_cons,
            } => {
                let new_cons = Self::computation(&mut self.results, on_cons);
                let new_nil = Self::computation(&mut self.results, on_nil);
                let new_list = Self::value(&mut self.results, list);
                if (new_list, new_nil, new_cons) == (list, on_nil, on_cons) {
                    id
                }
                else {
                    self.arena
                        .computation_list_case(new_list, new_nil, new_cons)
                }
            },
            Computation::Primitive {
                primitive,
                mut arguments,
            } => {
                let mut changed = false;
                for argument in arguments.iter_mut().rev() {
                    let rewritten = Self::value(&mut self.results, *argument);
                    changed |= rewritten != *argument;
                    *argument = rewritten;
                }
                if changed {
                    self.arena.computation_primitive(primitive, arguments)
                }
                else {
                    id
                }
            },
            Computation::DataCase {
                scrutinee,
                motive,
                ref branches,
                ref arities,
                equations,
            } => {
                let mut changed = None;
                for (index, original) in branches.iter().enumerate().rev() {
                    let rewritten = Self::computation(&mut self.results, *original);
                    if rewritten != *original {
                        let changed = changed.get_or_insert_with(|| branches.clone());
                        if let Some(slot) = changed.get_mut(index) {
                            *slot = rewritten;
                        }
                    }
                }
                let rewritten_motive = Self::comp_type(&mut self.results, motive);
                let rewritten_scrutinee = Self::value(&mut self.results, scrutinee);
                if changed.is_none()
                    && (rewritten_scrutinee, rewritten_motive) == (scrutinee, motive)
                {
                    id
                }
                else {
                    self.arena.computation_data_case_with_equations(
                        rewritten_scrutinee,
                        rewritten_motive,
                        (changed.unwrap_or_else(|| branches.clone()), arities.clone()),
                        equations,
                    )
                }
            },
            Computation::RecordProjection(record, ref label) => {
                let rewritten = Self::value(&mut self.results, record);
                if rewritten == record {
                    id
                }
                else {
                    self.arena
                        .computation_record_projection(rewritten, label.clone())
                }
            },
            Computation::TupleProjection(tuple, component) => {
                let rewritten = Self::value(&mut self.results, tuple);
                if rewritten == tuple {
                    id
                }
                else {
                    self.arena
                        .computation_tuple_projection(rewritten, component)
                }
            },
            Computation::Transport(path, value) => {
                let rewritten_value = Self::value(&mut self.results, value);
                let rewritten_path = Self::value(&mut self.results, path);
                if (rewritten_path, rewritten_value) == (path, value) {
                    id
                }
                else {
                    self.arena
                        .computation_transport(rewritten_path, rewritten_value)
                }
            },
            Computation::PathTransport {
                motive,
                path,
                value,
            } => {
                let rewritten_value = Self::value(&mut self.results, value);
                let rewritten_path = Self::value(&mut self.results, path);
                let rewritten_motive = Self::value_type(&mut self.results, motive);
                if (rewritten_motive, rewritten_path, rewritten_value) == (motive, path, value) {
                    id
                }
                else {
                    self.arena.computation_path_transport(
                        rewritten_motive,
                        rewritten_path,
                        rewritten_value,
                    )
                }
            },
            Computation::Ride {
                motive,
                flow,
                value,
            } => {
                let rewritten_value = Self::value(&mut self.results, value);
                let rewritten_flow = Self::value(&mut self.results, flow);
                let rewritten_motive = Self::value_type(&mut self.results, motive);
                if (rewritten_motive, rewritten_flow, rewritten_value) == (motive, flow, value) {
                    id
                }
                else {
                    self.arena
                        .computation_ride(rewritten_motive, rewritten_flow, rewritten_value)
                }
            },
            Computation::TelescopeTransport {
                motive,
                path,
                start,
                over,
                value,
            } => {
                let new_value = Self::value(&mut self.results, value);
                let new_over = Self::value(&mut self.results, over);
                let new_start = Self::value(&mut self.results, start);
                let new_path = Self::value(&mut self.results, path);
                let new_motive = Self::comp_type(&mut self.results, motive);
                if (new_motive, new_path, new_start, new_over, new_value)
                    == (motive, path, start, over, value)
                {
                    id
                }
                else {
                    self.arena.computation_telescope_transport(
                        new_motive, new_path, new_start, new_over, new_value,
                    )
                }
            },
            Computation::Lambda(body) => {
                let rewritten = Self::computation(&mut self.results, body);
                if rewritten == body {
                    id
                }
                else {
                    self.arena.computation_lambda(rewritten)
                }
            },
            Computation::Fixpoint { body, evidence } => {
                let rewritten = Self::computation(&mut self.results, body);
                if rewritten == body {
                    id
                }
                else {
                    self.arena.computation_fixpoint(rewritten, evidence)
                }
            },
            Computation::Application(head, argument) => {
                let rewritten_argument = Self::value(&mut self.results, argument);
                let rewritten_head = Self::computation(&mut self.results, head);
                if (rewritten_head, rewritten_argument) == (head, argument) {
                    id
                }
                else {
                    self.arena
                        .computation_application(rewritten_head, rewritten_argument)
                }
            },
            Computation::Return(value) => {
                let rewritten = Self::value(&mut self.results, value);
                if rewritten == value {
                    id
                }
                else {
                    self.arena.computation_return(rewritten)
                }
            },
            Computation::Abandon(stack) => {
                let rewritten = Self::value(&mut self.results, stack);
                if rewritten == stack {
                    id
                }
                else {
                    self.arena.computation_abandon(rewritten)
                }
            },
            Computation::Force(value) => {
                let rewritten = Self::value(&mut self.results, value);
                if rewritten == value {
                    id
                }
                else {
                    self.arena.computation_force(rewritten)
                }
            },
            Computation::Bind(bound, body) => {
                let rewritten_body = Self::computation(&mut self.results, body);
                let rewritten_bound = Self::computation(&mut self.results, bound);
                if (rewritten_bound, rewritten_body) == (bound, body) {
                    id
                }
                else {
                    self.arena.computation_bind(rewritten_bound, rewritten_body)
                }
            },
            Computation::Case {
                scrutinee,
                ref branches,
            } => {
                let mut changed: Option<Vec<ComputationId>> = None;
                for (index, original) in branches.iter().enumerate().rev() {
                    let rewritten = Self::computation(&mut self.results, *original);
                    if rewritten != *original {
                        let changed = changed.get_or_insert_with(|| branches.to_vec());
                        if let Some(slot) = changed.get_mut(index) {
                            *slot = rewritten;
                        }
                    }
                }
                let rewritten_scrutinee = Self::value(&mut self.results, scrutinee);
                if changed.is_none() && rewritten_scrutinee == scrutinee {
                    id
                }
                else if let Some(branches) = changed {
                    self.arena.computation_case(rewritten_scrutinee, &branches)
                }
                else {
                    let branches = branches.to_vec();
                    self.arena.computation_case(rewritten_scrutinee, &branches)
                }
            },
            Computation::Hole(_) => id,
            Computation::Mark { mark, body } => {
                let rewritten = Self::computation(&mut self.results, body);
                if rewritten == body {
                    id
                }
                else {
                    self.arena.computation_mark(mark, rewritten)
                }
            },
            Computation::Session(ref action) => {
                let rewritten = match action.try_map(
                    crate::session::ChildOrder::Reverse,
                    &mut self.results,
                    |results, value| {
                        Ok::<_, core::convert::Infallible>(Self::value(results, value))
                    },
                    |results, computation| Ok(Self::computation(results, computation)),
                    |results, ty| Ok(Self::value_type(results, ty)),
                ) {
                    Ok(rewritten) => rewritten,
                    Err(never) => match never {},
                };
                if rewritten == *action {
                    id
                }
                else {
                    self.arena.computation_session(rewritten)
                }
            },
            Computation::Memory(ref form) => {
                let rewritten = match form.try_map(
                    crate::session::ChildOrder::Reverse,
                    &mut self.results,
                    |results, value| {
                        Ok::<_, core::convert::Infallible>(Self::value(results, value))
                    },
                    |results, computation| Ok(Self::computation(results, computation)),
                ) {
                    Ok(rewritten) => rewritten,
                    Err(never) => match never {},
                };
                if rewritten == *form {
                    id
                }
                else {
                    self.arena.computation_memory(rewritten)
                }
            },
            Computation::World(ref form) => {
                let rewritten = match form.try_map(
                    crate::session::ChildOrder::Reverse,
                    &mut self.results,
                    |results, value| {
                        Ok::<_, core::convert::Infallible>(Self::value(results, value))
                    },
                    |results, computation| Ok(Self::computation(results, computation)),
                ) {
                    Ok(rewritten) => rewritten,
                    Err(never) => match never {},
                };
                if rewritten == *form {
                    id
                }
                else {
                    self.arena.computation_world(rewritten)
                }
            },
        }
    }

    /// Combine a value-type node.
    ///
    /// # Specification
    /// - requires: the result stack holds rewritten children in source order.
    /// - ensures: consumes those children; unchanged children reuse `id`, while
    ///   changed children preserve the former except for quote decoding.
    /// - provides: the family-specific reconstruction step.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — unchanged and changed children of each former are
    ///   read back exactly, with unequal children separating reversed stack
    ///   order. Matching quotes exercise decode-on-mint, while leaves and
    ///   missing children preserve their original identity.
    /// - witness: `rewrite::tests::congruences_preserve_formers_and_child_order`
    /// - witness: `rewrite::tests::every_former_is_kept_when_nothing_beneath_it_changes_and_carries_what_does`
    #[spec(
        captures: [ready = self.results.len(), children = self.arena.value_type(id).map_or(0_usize, |matched_native_node| match *matched_native_node {
ValueType::Data { ref arguments, .. } => arguments.len(),
ValueType::Record(ref fields) => fields.len(),
ValueType::Product(ref components) | ValueType::Sum(ref components) => components.len(),
ValueType::Base(_) | ValueType::Universe { .. } | ValueType::Abstract(_) | ValueType::Unknown | ValueType::Buffer => 0_usize,
ValueType::Session(ref session) => session.payloads().len(),
ValueType::Capability { ref authority, .. } => authority.types().count(),
ValueType::World(ref ty) => ty.types().count(),
ValueType::Stack { .. } | ValueType::StaticPi { .. } | ValueType::Sigma { .. } | ValueType::PathUniverse(..) => 2,
ValueType::Path { .. } | ValueType::Flow { .. } => 3,
ValueType::List(_) | ValueType::Thunk(_) | ValueType::Lift { .. } | ValueType::Element { .. } | ValueType::Run(_) | ValueType::Prefix(_) | ValueType::Staged { .. } | ValueType::Kept { .. } => 1,
})],
        ensures: |ret| self.results.len() == ready.saturating_sub(children)
            && (ret == id || self.arena.value_type(id).is_some_and(|original| self.arena.value_type(ret).is_some_and(|rewritten|
                matches!(original, ValueType::Element { .. }) || core::mem::discriminant(original) == core::mem::discriminant(rewritten)))),
    )]
    fn close_value_type(
        &mut self,
        id: ValueTypeId,
    ) -> ValueTypeId
    {
        let Some(node) = self.arena.value_type(id)
        else {
            return id;
        };
        match *node {
            ValueType::Data {
                declaration,
                ref arguments,
            } => {
                let mut changed = None;
                for (index, original) in arguments.iter().enumerate().rev() {
                    let rewritten = Self::value(&mut self.results, *original);
                    if rewritten != *original {
                        let changed = changed.get_or_insert_with(|| arguments.clone());
                        if let Some(slot) = changed.get_mut(index) {
                            *slot = rewritten;
                        }
                    }
                }
                match changed {
                    Some(arguments) => self.arena.value_type_data(declaration, arguments),
                    None => id,
                }
            },
            ValueType::Record(ref fields) => {
                let mut changed = None;
                for (label, original) in fields.iter().rev() {
                    let rewritten = Self::value_type(&mut self.results, *original);
                    if rewritten != *original {
                        let changed = changed.get_or_insert_with(|| fields.clone());
                        if let Some(slot) = changed.get_mut(label) {
                            *slot = rewritten;
                        }
                    }
                }
                match changed {
                    Some(fields) => self.arena.value_type_record(fields),
                    None => id,
                }
            },
            ValueType::Stack { input, output } => {
                let rewritten_output = Self::comp_type(&mut self.results, output);
                let rewritten_input = Self::comp_type(&mut self.results, input);
                if (rewritten_input, rewritten_output) == (input, output) {
                    id
                }
                else {
                    self.arena
                        .value_type_stack(rewritten_input, rewritten_output)
                }
            },
            ValueType::List(element) => {
                let rewritten = Self::value_type(&mut self.results, element);
                if rewritten == element {
                    id
                }
                else {
                    self.arena.value_type_list(rewritten)
                }
            },
            ValueType::Staged { base, stage } => {
                let rewritten = Self::value_type(&mut self.results, base);
                if rewritten == base {
                    id
                }
                else {
                    self.arena.value_type_staged(rewritten, stage)
                }
            },
            ValueType::Kept { value, region } => {
                let rewritten = Self::value_type(&mut self.results, value);
                let placed = self.renaming.placed(region);
                if (rewritten, placed) == (value, region) {
                    id
                }
                else {
                    self.arena.value_type_kept(rewritten, placed)
                }
            },
            ValueType::PathUniverse(source, target) => {
                let rewritten_target = Self::value(&mut self.results, target);
                let rewritten_source = Self::value(&mut self.results, source);
                if (rewritten_source, rewritten_target) == (source, target) {
                    id
                }
                else {
                    self.arena
                        .value_type_path_universe(rewritten_source, rewritten_target)
                }
            },
            ValueType::Path {
                carrier,
                left,
                right,
            } => {
                let rewritten_right = Self::value(&mut self.results, right);
                let rewritten_left = Self::value(&mut self.results, left);
                let rewritten_carrier = Self::value_type(&mut self.results, carrier);
                if (rewritten_carrier, rewritten_left, rewritten_right) == (carrier, left, right) {
                    id
                }
                else {
                    self.arena
                        .value_type_path(rewritten_carrier, rewritten_left, rewritten_right)
                }
            },
            ValueType::Flow {
                carrier,
                source,
                target,
            } => {
                let rewritten_target = Self::value(&mut self.results, target);
                let rewritten_source = Self::value(&mut self.results, source);
                let rewritten_carrier = Self::value_type(&mut self.results, carrier);
                if (rewritten_carrier, rewritten_source, rewritten_target)
                    == (carrier, source, target)
                {
                    id
                }
                else {
                    self.arena.value_type_flow(
                        rewritten_carrier,
                        rewritten_source,
                        rewritten_target,
                    )
                }
            },
            ValueType::Run(session) => {
                let rewritten = Self::value(&mut self.results, session);
                if rewritten == session {
                    id
                }
                else {
                    self.arena.value_type_run(rewritten)
                }
            },
            ValueType::Prefix(session) => {
                let rewritten = Self::value(&mut self.results, session);
                if rewritten == session {
                    id
                }
                else {
                    self.arena.value_type_prefix(rewritten)
                }
            },
            ValueType::Base(_)
            | ValueType::Universe { .. }
            | ValueType::Abstract(_)
            | ValueType::Unknown
            | ValueType::Buffer => id,
            ValueType::Capability {
                ref authority,
                grade,
                region,
            } => {
                let rewritten =
                    match authority.try_map_types(crate::effect::TypeOrder::Reverse, |ty| {
                        Ok::<_, core::convert::Infallible>(Self::value_type(&mut self.results, ty))
                    }) {
                        Ok(row) => row,
                        Err(never) => match never {},
                    };
                let placed = self.renaming.placed(region);
                if rewritten == *authority && placed == region {
                    id
                }
                else {
                    self.arena.value_type_capability(rewritten, grade, placed)
                }
            },
            ValueType::Product(ref components) | ValueType::Sum(ref components) => {
                let product = matches!(*node, ValueType::Product(_));
                let mut changed: Option<Vec<ValueTypeId>> = None;
                for (index, original) in components.iter().enumerate().rev() {
                    let rewritten = Self::value_type(&mut self.results, *original);
                    if rewritten != *original {
                        let changed = changed.get_or_insert_with(|| components.to_vec());
                        if let Some(slot) = changed.get_mut(index) {
                            *slot = rewritten;
                        }
                    }
                }
                match changed {
                    Some(components) if product => self.arena.value_type_product(&components),
                    Some(summands) => self.arena.value_type_sum(&summands),
                    None => id,
                }
            },
            ValueType::Thunk(body) => {
                let rewritten = Self::comp_type(&mut self.results, body);
                if rewritten == body {
                    id
                }
                else {
                    self.arena.value_type_thunk(rewritten)
                }
            },
            ValueType::Lift { inner, ref target } => {
                let rewritten = Self::value_type(&mut self.results, inner);
                if rewritten == inner {
                    id
                }
                else {
                    self.arena.value_type_lift(rewritten, target.clone())
                }
            },
            ValueType::Element { code, ref target } => {
                let rewritten = Self::value(&mut self.results, code);
                if rewritten == code {
                    id
                }
                else {
                    self.arena.value_type_element(rewritten, target.clone())
                }
            },
            ValueType::StaticPi { domain, codomain } => {
                let rewritten_codomain = Self::value_type(&mut self.results, codomain);
                let rewritten_domain = Self::value_type(&mut self.results, domain);
                if (rewritten_domain, rewritten_codomain) == (domain, codomain) {
                    id
                }
                else {
                    self.arena
                        .value_type_static_pi(rewritten_domain, rewritten_codomain)
                }
            },
            ValueType::Sigma { first, second } => {
                let rewritten_second = Self::value_type(&mut self.results, second);
                let rewritten_first = Self::value_type(&mut self.results, first);
                if (rewritten_first, rewritten_second) == (first, second) {
                    id
                }
                else {
                    self.arena
                        .value_type_sigma(rewritten_first, rewritten_second)
                }
            },
            ValueType::Session(ref session) => {
                let rewritten =
                    match session.try_map_payloads(crate::session::ChildOrder::Reverse, |payload| {
                        Ok::<_, core::convert::Infallible>(Self::value_type(
                            &mut self.results,
                            payload,
                        ))
                    }) {
                        Ok(rewritten) => rewritten,
                        Err(never) => match never {},
                    };
                if rewritten == *session {
                    id
                }
                else {
                    self.arena.value_type_session(rewritten)
                }
            },
            ValueType::World(ref ty) => {
                let rewritten = match ty.try_map(|inner| {
                    Ok::<_, core::convert::Infallible>(Self::value_type(&mut self.results, inner))
                }) {
                    Ok(rewritten) => rewritten,
                    Err(never) => match never {},
                };
                if rewritten == *ty {
                    id
                }
                else {
                    self.arena.value_type_world(rewritten)
                }
            },
        }
    }

    /// Combine a computation-type node.
    ///
    /// # Specification
    /// - requires: the result stack holds rewritten children in source order.
    /// - ensures: consumes those children; unchanged children reuse `id`, while
    ///   changed children preserve the former except for quote decoding.
    /// - provides: the family-specific reconstruction step.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — unchanged and changed children of each former are
    ///   read back exactly, with unequal children separating reversed stack
    ///   order. Matching quotes exercise decode-on-mint, while leaves and
    ///   missing children preserve their original identity.
    /// - witness: `rewrite::tests::congruences_preserve_formers_and_child_order`
    /// - witness: `rewrite::tests::every_former_is_kept_when_nothing_beneath_it_changes_and_carries_what_does`
    #[spec(
        captures: [ready = self.results.len(), children = match self.arena.comp_type(id) {
            | None | Some(&CompType::Unknown) => 0_usize,
            | Some(&CompType::Returner { ref effects, .. }) => 1_usize.saturating_add(effects.types().count()),
            | Some(&CompType::Element { .. }) => 1,
            Some(&CompType::Arrow { .. } | &CompType::Pi { .. }) => 2,
            Some(&CompType::With(ref components)) => components.len(),
            Some(&CompType::Codata { ref arguments, .. }) => arguments.len(),
        }],
        ensures: |ret| self.results.len() == ready.saturating_sub(children)
            && (ret == id || self.arena.comp_type(id).is_some_and(|original| self.arena.comp_type(ret).is_some_and(|rewritten|
                matches!(original, CompType::Element { .. }) || core::mem::discriminant(original) == core::mem::discriminant(rewritten)))),
    )]
    fn close_comp_type(
        &mut self,
        id: CompTypeId,
    ) -> CompTypeId
    {
        let Some(node) = self.arena.comp_type(id)
        else {
            return id;
        };
        match *node {
            CompType::With(ref components) => {
                let mut changed: Option<Vec<CompTypeId>> = None;
                for (index, original) in components.iter().enumerate().rev() {
                    let rewritten = Self::comp_type(&mut self.results, *original);
                    if rewritten != *original {
                        let changed = changed.get_or_insert_with(|| components.to_vec());
                        if let Some(slot) = changed.get_mut(index) {
                            *slot = rewritten;
                        }
                    }
                }
                match changed {
                    Some(components) => self.arena.comp_type_with(&components),
                    None => id,
                }
            },
            CompType::Returner {
                result,
                ref effects,
            } => {
                let rewritten_effects =
                    match effects.try_map_types(crate::effect::TypeOrder::Reverse, |ty| {
                        Ok::<_, core::convert::Infallible>(Self::value_type(&mut self.results, ty))
                    }) {
                        Ok(row) => row,
                        Err(never) => match never {},
                    };
                let rewritten = Self::value_type(&mut self.results, result);
                if rewritten == result && rewritten_effects == *effects {
                    id
                }
                else {
                    self.arena
                        .comp_type_returner_with_effects(rewritten, rewritten_effects)
                }
            },
            CompType::Arrow { domain, codomain } => {
                let rewritten_codomain = Self::comp_type(&mut self.results, codomain);
                let rewritten_domain = Self::value_type(&mut self.results, domain);
                if (rewritten_domain, rewritten_codomain) == (domain, codomain) {
                    id
                }
                else {
                    self.arena
                        .comp_type_arrow(rewritten_domain, rewritten_codomain)
                }
            },
            CompType::Pi { domain, codomain } => {
                let rewritten_codomain = Self::comp_type(&mut self.results, codomain);
                let rewritten_domain = Self::value_type(&mut self.results, domain);
                if (rewritten_domain, rewritten_codomain) == (domain, codomain) {
                    id
                }
                else {
                    self.arena
                        .comp_type_pi(rewritten_domain, rewritten_codomain)
                }
            },
            CompType::Element { code, ref target } => {
                let rewritten = Self::value(&mut self.results, code);
                if rewritten == code {
                    id
                }
                else {
                    self.arena.comp_type_element(rewritten, target.clone())
                }
            },
            CompType::Unknown => id,
            CompType::Codata {
                declaration,
                ref arguments,
            } => {
                let mut changed = None;
                for (index, original) in arguments.iter().enumerate().rev() {
                    let rewritten = Self::value(&mut self.results, *original);
                    if rewritten != *original {
                        let changed = changed.get_or_insert_with(|| arguments.clone());
                        if let Some(slot) = changed.get_mut(index) {
                            *slot = rewritten;
                        }
                    }
                }
                match changed {
                    Some(arguments) => self.arena.comp_type_codata(declaration, arguments),
                    None => id,
                }
            },
        }
    }
}

/// The support `node` carries, read in place.
///
/// # Specification
/// - requires: nothing; a dangling id is admissible.
/// - ensures: the node's carried support; [`unminted::Absent::Dangling`] when
///   `node` names no node of `arena`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as the arena's support reads, which it dispatches to.
/// - witness: `rewrite::tests::a_strengthening_reads_the_carried_support`
#[spec(ensures: |ret| match ret {
    Maybe::Present(_) => true,
    Maybe::Absent(unminted::Absent::Dangling) => match node {
        Node::Value(id) => arena.value(id).is_none(),
        Node::Computation(id) => arena.computation(id).is_none(),
        Node::ValueType(id) => arena.value_type(id).is_none(),
        Node::CompType(id) => arena.comp_type(id).is_none(),
    },
})]
fn carried(
    arena: &CoreArena,
    node: Node,
) -> Maybe<ThinningRef<'_>, unminted::Absent>
{
    let support = match node {
        Node::Value(id) => arena.value_support(id),
        Node::Computation(id) => arena.computation_support(id),
        Node::ValueType(id) => arena.value_type_support(id),
        Node::CompType(id) => arena.comp_type_support(id),
    };
    support.map_or(Maybe::Absent(unminted::Absent::Dangling), Maybe::Present)
}

/// Move `node`'s free indices past `scope` by `offset` at once, minting the
/// moved tree: the eager reading of a relocation, for one too wide to hold
/// and for [`Relocated::settle`].
///
/// # Specification
/// - requires: `offset` lowers no index of `node` past `scope` below `scope`.
/// - ensures: the moved node, in `node`'s family; `node` itself when its
///   support stops below `scope`.
/// - provides: the one walk the shifts and strengthenings keep.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — settled raises of generated trees agree with the
///   level-based reference read deeper. L3 — the binding sites and a lowering
///   separate scope, sign and the spared binders.
/// - witness: `rewrite::tests::a_settled_shift_agrees_with_the_level_reference`
/// - witness: `rewrite::tests::binding_sites_distinguish_free_bound_and_linear_indices`
#[spec(ensures: |ret| core::mem::discriminant(&ret) == core::mem::discriminant(&node))]
fn moved_eagerly(
    arena: &mut CoreArena,
    node: Node,
    scope: Binders,
    offset: Offset,
) -> Node
{
    Engine::new(arena).run(node, scope, Rewrite::Relocate(offset))
}

/// [`moved_eagerly`] by `at`, reporting every node it copied, each beside
/// its copy, into `carried`.
///
/// # Specification
/// - requires: as [`moved_eagerly`].
/// - ensures: as [`moved_eagerly`]; `carried` gains one entry per node the walk
///   replaced, and nothing for a relocation that moves nothing.
/// - provides: the settled copy a caller keeping metadata per node copies its
///   records onto.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a traced raise reports exactly the rewritten nodes, and
///   the identity reports nothing.
/// - witness: `rewrite::tests::a_traced_shift_raises_only_past_its_scope`
#[spec(captures: before = carried.len(), ensures: |ret| core::mem::discriminant(&ret) == core::mem::discriminant(&node)
    && carried.len() >= before)]
fn settled_traced(
    arena: &mut CoreArena,
    node: Node,
    at: Relocation,
    carried: &mut Vec<Carried>,
) -> Node
{
    if at == Relocation::IDENTITY {
        return node;
    }
    let mut engine = Engine::new(arena);
    let moved = engine.run(node, at.cutoff(), Rewrite::Relocate(at.offset()));
    report(&engine.memo, carried);
    moved
}

/// [`moved_eagerly`] by `at`: the node minted where the relocation reads it.
///
/// # Specification
/// trivial.
fn settled(
    arena: &mut CoreArena,
    node: Node,
    at: Relocation,
) -> Node
{
    if at == Relocation::IDENTITY {
        return node;
    }
    moved_eagerly(arena, node, at.cutoff(), at.offset())
}

/// `node` read through `at` and then through `next`, as an update of the
/// relocation at its root: the one relocation the two fold to on `node`'s
/// support, or else `node` settled through `at` and read through `next`. A
/// `next` too wide to hold moves the settled node eagerly by `offset` past
/// `scope`.
///
/// # Specification
/// - requires: `at` is fitted to `node`'s support; `next` and `offset` with
///   `scope` are one move of the scope `at` reads `node` into.
/// - ensures: a node and a relocation fitted to its support that read as `node`
///   through `at` and then `next`; `node` itself, nothing minted, whenever the
///   two fold.
/// - provides: the root update every shift and strengthening is.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a plain subject raised mints nothing, a relocated one
///   whose second raise folds mints nothing, and one whose second raise does
///   not fold reads back as the two raises in turn.
/// - witness: `rewrite::tests::a_shift_is_a_root_update`
/// - witness: `rewrite::tests::a_renaming_composes_on_a_child_read_and_applies_at_a_variable`
#[spec(ensures: |ret| core::mem::discriminant(&ret.0) == core::mem::discriminant(&node))]
fn updated(
    arena: &mut CoreArena,
    (node, at): (Node, Relocation),
    next: Maybe<Relocation, folding::Absent>,
    scope: Binders,
    offset: Offset,
) -> (Node, Relocation)
{
    let Maybe::Present(next) = next
    else {
        let plain = settled(arena, node, at);
        return (
            moved_eagerly(arena, plain, scope, offset),
            Relocation::IDENTITY,
        );
    };
    let folded = match carried(arena, node) {
        Maybe::Present(support) if at == Relocation::IDENTITY => {
            Maybe::Present(next.fitted(support))
        },
        Maybe::Present(support) => at.then(next, support),
        Maybe::Absent(unminted::Absent::Dangling) => Maybe::Present(at),
    };
    if let Maybe::Present(folded) = folded {
        return (node, folded);
    }
    let plain = settled(arena, node, at);
    match carried(arena, plain) {
        Maybe::Present(support) => (plain, next.fitted(support)),
        Maybe::Absent(unminted::Absent::Dangling) => (plain, next),
    }
}

impl Relocated<ValueId>
{
    /// The value minted where the relocation reads it: the boundary a
    /// consumer that holds plain ids crosses.
    ///
    /// # Specification
    /// - requires: the relocated id names a value of `arena`.
    /// - ensures: the node itself under the identity; otherwise the value with
    ///   every free index the relocation moves moved, minted where it changed,
    ///   entering only nodes whose support the relocation reaches.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — as the value types' [`Relocated::settle`].
    /// - witness: `rewrite::tests::a_settled_shift_agrees_with_the_level_reference`
    #[spec(ensures: |ret| (self.relocation() != Relocation::IDENTITY || ret == self.node())
        && (ret == self.node() || arena.value(ret).is_some()))]
    #[inline]
    #[must_use]
    pub fn settle(
        self,
        arena: &mut CoreArena,
    ) -> ValueId
    {
        match settled(arena, Node::Value(self.node()), self.relocation()) {
            Node::Value(id) => id,
            Node::Computation(_) | Node::ValueType(_) | Node::CompType(_) => self.node(),
        }
    }

    /// [`Self::settle`], reporting every node it copied into `carried`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn settle_traced(
        self,
        arena: &mut CoreArena,
        carried: &mut Vec<Carried>,
    ) -> ValueId
    {
        match settled_traced(arena, Node::Value(self.node()), self.relocation(), carried) {
            Node::Value(id) => id,
            Node::Computation(_) | Node::ValueType(_) | Node::CompType(_) => self.node(),
        }
    }
}

impl Relocated<ComputationId>
{
    /// The computation minted where the relocation reads it.
    ///
    /// # Specification
    /// - requires: the relocated id names a computation of `arena`.
    /// - ensures: as the values' [`Relocated::settle`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a traced raise of a computation past its scope.
    /// - witness: `rewrite::tests::a_traced_shift_raises_only_past_its_scope`
    #[spec(ensures: |ret| (self.relocation() != Relocation::IDENTITY || ret == self.node())
        && (ret == self.node() || arena.computation(ret).is_some()))]
    #[inline]
    #[must_use]
    pub fn settle(
        self,
        arena: &mut CoreArena,
    ) -> ComputationId
    {
        match settled(arena, Node::Computation(self.node()), self.relocation()) {
            Node::Computation(id) => id,
            Node::Value(_) | Node::ValueType(_) | Node::CompType(_) => self.node(),
        }
    }

    /// [`Self::settle`], reporting every node it copied into `carried`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn settle_traced(
        self,
        arena: &mut CoreArena,
        carried: &mut Vec<Carried>,
    ) -> ComputationId
    {
        match settled_traced(
            arena,
            Node::Computation(self.node()),
            self.relocation(),
            carried,
        ) {
            Node::Computation(id) => id,
            Node::Value(_) | Node::ValueType(_) | Node::CompType(_) => self.node(),
        }
    }
}

impl Relocated<ValueTypeId>
{
    /// The value type minted where the relocation reads it.
    ///
    /// # Specification
    /// - requires: the relocated id names a value type of `arena`.
    /// - ensures: the node itself under the identity; otherwise the type with
    ///   every free index the relocation moves moved, minted where it changed,
    ///   entering only nodes whose support the relocation reaches.
    /// - provides: the plain type a constructor, the normaliser or a side table
    ///   keyed by type takes.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — settled raises of generated trees agree with the
    ///   level-based reference read deeper, and settled lowerings with it read
    ///   shallower.
    /// - witness: `rewrite::tests::a_settled_shift_agrees_with_the_level_reference`
    /// - witness: `rewrite::tests::a_strengthening_reads_the_carried_support`
    #[spec(ensures: |ret| (self.relocation() != Relocation::IDENTITY || ret == self.node())
        && (ret == self.node() || arena.value_type(ret).is_some()))]
    #[inline]
    #[must_use]
    pub fn settle(
        self,
        arena: &mut CoreArena,
    ) -> ValueTypeId
    {
        match settled(arena, Node::ValueType(self.node()), self.relocation()) {
            Node::ValueType(id) => id,
            Node::Value(_) | Node::Computation(_) | Node::CompType(_) => self.node(),
        }
    }

    /// [`Self::settle`], reporting every node it copied into `carried`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn settle_traced(
        self,
        arena: &mut CoreArena,
        carried: &mut Vec<Carried>,
    ) -> ValueTypeId
    {
        match settled_traced(
            arena,
            Node::ValueType(self.node()),
            self.relocation(),
            carried,
        ) {
            Node::ValueType(id) => id,
            Node::Value(_) | Node::Computation(_) | Node::CompType(_) => self.node(),
        }
    }
}

impl Relocated<CompTypeId>
{
    /// The computation type minted where the relocation reads it.
    ///
    /// # Specification
    /// - requires: the relocated id names a computation type of `arena`.
    /// - ensures: as the value types' [`Relocated::settle`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — as the value types' [`Relocated::settle`].
    /// - witness: `rewrite::tests::a_settled_shift_agrees_with_the_level_reference`
    #[spec(ensures: |ret| (self.relocation() != Relocation::IDENTITY || ret == self.node())
        && (ret == self.node() || arena.comp_type(ret).is_some()))]
    #[inline]
    #[must_use]
    pub fn settle(
        self,
        arena: &mut CoreArena,
    ) -> CompTypeId
    {
        match settled(arena, Node::CompType(self.node()), self.relocation()) {
            Node::CompType(id) => id,
            Node::Value(_) | Node::Computation(_) | Node::ValueType(_) => self.node(),
        }
    }

    /// [`Self::settle`], reporting every node it copied into `carried`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn settle_traced(
        self,
        arena: &mut CoreArena,
        carried: &mut Vec<Carried>,
    ) -> CompTypeId
    {
        match settled_traced(
            arena,
            Node::CompType(self.node()),
            self.relocation(),
            carried,
        ) {
            Node::CompType(id) => id,
            Node::Value(_) | Node::Computation(_) | Node::ValueType(_) => self.node(),
        }
    }
}

/// Shift a value type `amount` binders deeper: every free intuitionistic index
/// rises by `amount`, as an update of the relocation at its root.
///
/// # Specification
/// - requires: `subject` names a value type of `arena`, formed in some context
///   `Γ`, plain or read through a relocation.
/// - ensures: the same type read in `Γ` extended by `amount` further binders,
///   as the subject's node under its relocation and then the raise, folded to
///   one relocation fitted to its support, so a closed type, or any type at a
///   zero `amount`, answers the subject as it stands; nothing is minted unless
///   the two do not fold or `amount` passes what a relocation holds.
/// - provides: the read of a context slot's type at an occurrence.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a raise of an open type leaves every family's length
///   where it was and reads back raised; a closed type and a zero amount answer
///   the subject plain. L2 — settled, it agrees with the level-based reference.
/// - witness: `rewrite::tests::a_shift_is_a_root_update`
/// - witness: `rewrite::tests::a_settled_shift_agrees_with_the_level_reference`
#[spec(ensures: |ret| (amount != Binders::NONE || ret == Into::<Relocated<ValueTypeId>>::into(subject))
    && (ret.node() == Into::<Relocated<ValueTypeId>>::into(subject).node()
        || arena.value_type(ret.node()).is_some()))]
#[inline]
#[must_use]
pub fn shift_value_type<Subject>(
    arena: &mut CoreArena,
    subject: Subject,
    amount: Binders,
) -> Relocated<ValueTypeId>
where
    Subject: Into<Relocated<ValueTypeId>> + Copy,
{
    shift_value_type_under(arena, subject, Binders::NONE, amount)
}

/// Abstract the constant `constant` out of the value type `subject` as the
/// variable `index`: every occurrence becomes the intuitionistic variable
/// counting past the binders it stands under to `index`.
///
/// # Specification
/// - requires: `subject` names a value type of `arena`, and `index` is free in
///   the context `subject` is read in.
/// - ensures: `subject` with every `constant` replaced by that variable, every
///   other node kept, and `subject` itself when it names no `constant`.
/// - provides: the identification a mutual block's definition reads its
///   families' fields by inside its own fixpoint: its constant there is its
///   self binder.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a constant under no binder and under one become the
///   variable at the index and one past it, and a type naming another constant
///   is kept.
/// - witness: `rewrite::tests::an_abstraction_replaces_its_constant_by_a_variable_under_binders`
#[spec(ensures: |ret| ret == subject || arena.value_type(ret).is_some())]
#[inline]
#[must_use]
pub fn abstract_constant_value_type(
    arena: &mut CoreArena,
    subject: ValueTypeId,
    constant: ConstantIndex,
    index: DeBruijnIndex,
) -> ValueTypeId
{
    match Engine::new(arena).run(
        Node::ValueType(subject),
        Binders::NONE,
        Rewrite::Abstract(constant, index),
    ) {
        Node::ValueType(id) => id,
        Node::Value(_) | Node::Computation(_) | Node::CompType(_) => subject,
    }
}

/// Read a receive's body with its payload bound intuitionistically.
///
/// Every read of the payload's linear binder becomes the variable of one
/// intuitionistic binder just outside `body`, and every free intuitionistic
/// index rises past it.
///
/// # Specification
/// - requires: `body` names a computation of `arena` read under the payload's
///   linear binder, innermost.
/// - ensures: `body` read under one intuitionistic binder more, innermost,
///   which each read of the payload names; every other linear index stands, so
///   a session action's subject and a memory form's slot keep their names and
///   the payload's linear slot stays, unread.
/// - provides: the continuation a receive's erasure binds its payload in.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a payload read at the root, under a nested receive and
///   under a fork's halves becomes the one new binder counted past the
///   intuitionistic binders between; a free intuitionistic index rises by one;
///   the nested receive's own payload and every action subject stay as they
///   were.
/// - witness: `rewrite::tests::a_delinearised_payload_reads_its_binder_past_nested_linear_binders_1319`
#[spec(ensures: |ret| ret == body || arena.computation(ret).is_some())]
#[inline]
#[must_use]
pub fn delinearise(
    arena: &mut CoreArena,
    body: ComputationId,
) -> ComputationId
{
    match Engine::new(arena).run(
        Node::Computation(body),
        Binders::NONE,
        Rewrite::Delinearise(Binders::NONE),
    ) {
        Node::Computation(id) => id,
        Node::Value(_) | Node::ValueType(_) | Node::CompType(_) => body,
    }
}

/// Shift a computation type `amount` binders deeper, as an update of the
/// relocation at its root.
///
/// # Specification
/// - requires: `subject` names a computation type of `arena`, formed in some
///   context `Γ`, plain or read through a relocation.
/// - ensures: the same type read in `Γ` extended by `amount` further binders,
///   as [`shift_value_type`] reads a value type.
/// - provides: the expected type a binder's body is checked against when the
///   binder does not scope the type.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — free and bound indices separated within one subject, read
///   back through the relocation and settled.
/// - witness: `rewrite::tests::shifting_raises_free_indices_and_spares_bound_ones`
/// - witness: `rewrite::tests::a_shift_is_a_root_update`
#[spec(ensures: |ret| (amount != Binders::NONE || ret == Into::<Relocated<CompTypeId>>::into(subject))
    && (ret.node() == Into::<Relocated<CompTypeId>>::into(subject).node()
        || arena.comp_type(ret.node()).is_some()))]
#[inline]
#[must_use]
pub fn shift_comp_type<Subject>(
    arena: &mut CoreArena,
    subject: Subject,
    amount: Binders,
) -> Relocated<CompTypeId>
where
    Subject: Into<Relocated<CompTypeId>> + Copy,
{
    shift_comp_type_under(arena, subject, Binders::NONE, amount)
}

/// Instantiate a dependent codomain at an argument: `C[v / x]`.
///
/// # Specification
/// - requires: `codomain` names a computation type of `arena` scoped under one
///   binder beyond some context `Γ`, and `argument` a value of `arena` in `Γ`.
/// - ensures: the codomain in `Γ`, with every occurrence of its binder replaced
///   by the argument carried under the binders it crosses, every index outside
///   the binder lowered by one, and every decode whose code became a quote read
///   as the quoted type.
/// - provides: the result type of applying a dependent arrow.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — 600 deterministic bounded codomains agree with a
///   capture-free level-based reference at open arguments; the finite
///   comparisons do not establish equivalence for ungenerated types.
/// - witness: `rewrite::tests::instantiating_a_codomain_avoids_capture`
/// - witness: `rewrite::tests::instantiating_a_decode_at_a_quote_decodes`
#[spec(ensures: |ret| ret == codomain || arena.comp_type(ret).is_some())]
#[inline]
#[must_use]
pub fn instantiate_comp_type(
    arena: &mut CoreArena,
    codomain: CompTypeId,
    argument: ValueId,
) -> CompTypeId
{
    match Engine::new(arena).run(
        Node::CompType(codomain),
        Binders::NONE,
        Rewrite::Substitute(argument),
    ) {
        Node::CompType(id) => id,
        Node::Value(_) | Node::Computation(_) | Node::ValueType(_) => codomain,
    }
}

/// Instantiate a dependent codomain at an argument written as a call, in the
/// form the lowering writes a type-read call argument in.
///
/// The lowering binds a call a type decodes ahead of the call it stands in,
/// `c ← g(x); f(c)` (`mint_called`), so a type written `f(g(x))` decodes that
/// bind. An instantiation at the same call binds it the same way: each decode
/// whose returned code reads the binder becomes `El ⟨c ← call; body[c / x]⟩`,
/// and everywhere else the call stands for its value, `argument` — in a path
/// endpoint, say, where the lowering holds a call in place. The type-position
/// form of a call argument is therefore one form, and conversion compares it
/// as syntax (#720). Alternatives: reading `⟨c ← M; N⟩` as `N[⟨M⟩]` in the
/// conversion, a kernel conversion extension with a soundness argument of
/// its own; and lowering the call in place, which loses the bound variable
/// standing below the stage. Reversal: a type repeating one call argument
/// mints one bind per decode that reads it, so a measured cost from sharing
/// lost between those binds would hold the call once, outside them.
///
/// # Specification
/// - requires: as [`instantiate_comp_type`]; `argument` stands for the value
///   `call` returns, and `call` is scoped where `argument` is.
/// - ensures: as [`instantiate_comp_type`] at `argument`, except that every
///   decode whose returned code reads the binder decodes a returned bind of
///   `call`, raised past the binders between, into that code's computation with
///   the binder read as the bind's variable.
/// - provides: the result type of applying a dependent arrow to a call.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a decode reading the binder at depth zero and under an
///   inner binder, a decode that does not read it, and a path endpoint reading
///   it separate the bind, the rotation and the plain substitution.
/// - witness: `rewrite::tests::an_instantiation_at_a_call_binds_it_ahead_of_each_decode_reading_it`
#[spec(ensures: |ret| ret == codomain || arena.comp_type(ret).is_some())]
#[inline]
#[must_use]
pub fn instantiate_comp_type_at_call(
    arena: &mut CoreArena,
    codomain: CompTypeId,
    argument: ValueId,
    call: ComputationId,
) -> CompTypeId
{
    match Engine::new(arena).run(
        Node::CompType(codomain),
        Binders::NONE,
        Rewrite::Instantiate(argument, call),
    ) {
        Node::CompType(id) => id,
        Node::Value(_) | Node::Computation(_) | Node::ValueType(_) => codomain,
    }
}

/// Instantiate a value scoped under one binder at an argument: `v[a / x]`,
/// the reduct of a static redex `(λ. v) a`.
///
/// # Specification
/// - requires: `body` names a value of `arena` scoped under one binder beyond
///   some context `Γ`, and `argument` a value of `arena` in `Γ`.
/// - ensures: the body in `Γ`, with every occurrence of its binder replaced by
///   the argument carried under the binders it crosses, every index outside the
///   binder lowered by one, and every decode whose code became a quote read as
///   the quoted type; `body` itself when nothing in it changed.
/// - provides: the one substitution static beta takes, shared by the
///   normaliser's certificates and every walk that unfolds a static definition
///   at an instance.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the three substitution boundaries, each asserted as the
///   exact rewritten term: a free occurrence replaced, an occurrence under a
///   shadowing static lambda spared, and an open argument carried under a
///   binder without capture.
/// - witness: `rewrite::tests::substitution_replaces_a_free_occurrence`
/// - witness: `rewrite::tests::substitution_stops_at_a_shadowing_binder`
/// - witness: `rewrite::tests::substitution_avoids_capture`
#[inline]
#[must_use]
#[spec(ensures: |ret| ret == body || arena.value(ret).is_some())]
pub fn instantiate_value(
    arena: &mut CoreArena,
    body: ValueId,
    argument: ValueId,
) -> ValueId
{
    match Engine::new(arena).run(
        Node::Value(body),
        Binders::NONE,
        Rewrite::Substitute(argument),
    ) {
        Node::Value(id) => id,
        Node::Computation(_) | Node::ValueType(_) | Node::CompType(_) => body,
    }
}

/// Instantiate an ambient variable beneath local binders in a value type.
///
/// # Specification
/// - requires: `body` is scoped beneath `under` local binders and one captured
///   binder; `argument` is scoped outside all those binders.
/// - ensures: the captured binder is replaced without capturing local
///   variables; further ambient indices decrease by one, and decoded quotes
///   reduce.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a type with both a local and a captured code
///   distinguishes substitution at the requested depth from substitution at
///   zero.
/// - witness: `rewrite::tests::annotation_substitution_protects_local_binders`
#[inline]
#[must_use]
#[spec(ensures: |ret| ret == body || arena.value_type(ret).is_some())]
pub fn instantiate_value_type_under(
    arena: &mut CoreArena,
    body: ValueTypeId,
    argument: ValueId,
    under: Binders,
) -> ValueTypeId
{
    match Engine::new(arena).run(Node::ValueType(body), under, Rewrite::Substitute(argument)) {
        Node::ValueType(id) => id,
        Node::Value(_) | Node::Computation(_) | Node::CompType(_) => body,
    }
}

/// Lower a computation type out from under its innermost binder, as an
/// update of the relocation at its root.
///
/// # Specification
/// - requires: `subject` names a computation type of `arena` formed in some
///   context `Γ` extended by one binder.
/// - ensures: as [`strengthen_value_type`] past one binder.
/// - provides: the result type of a bind or a case, synthesized under the
///   binder its continuation introduces.
/// - fails: never; a mention is a named absence.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a type that mentions the binder and one that mentions
///   only an outer index separate the two answers, the second read back lowered
///   and minting nothing.
/// - witness: `rewrite::tests::strengthening_refuses_a_mention_and_lowers_the_rest`
/// - witness: `rewrite::tests::a_strengthening_reads_the_carried_support`
#[spec(ensures: |ret| match ret {
    | Maybe::Present(lowered) => lowered.node() == subject || arena.comp_type(lowered.node()).is_some(),
    | Maybe::Absent(strengthening::Absent::MentionsBinder) => true,
})]
#[inline]
pub fn strengthen_comp_type(
    arena: &mut CoreArena,
    subject: CompTypeId,
) -> Maybe<Relocated<CompTypeId>, strengthening::Absent>
{
    if let Maybe::Absent(reason) = mentions_none_below(arena, Node::CompType(subject), Binders::ONE)
    {
        return Maybe::Absent(reason);
    }
    let lowered = updated(
        arena,
        (Node::CompType(subject), Relocation::IDENTITY),
        Relocation::lowering(Binders::ONE),
        Binders::ONE,
        Offset::lower(Binders::ONE),
    );
    Maybe::Present(match lowered {
        (Node::CompType(id), at) => Relocated::pending(id, at),
        (Node::Value(_) | Node::Computation(_) | Node::ValueType(_), _) => Relocated::from(subject),
    })
}

/// Whether `node`'s carried support selects none of the innermost `past`
/// intuitionistic binders: the whole of a strengthening's decision.
///
/// The support decides the syntactic strengthening the bind rule has always
/// made — a type that mentions the binder is refused, wherever the mention
/// stands — and nothing beyond it: whether a type that mentions its binder
/// could still be lowered is the judgement's question, and it stays the
/// refusal it is.
///
/// # Specification
/// - requires: nothing; a dangling node mentions nothing.
/// - ensures: present exactly when no selected intuitionistic index is below
///   `past`; [`strengthening::Absent::MentionsBinder`] otherwise.
/// - provides: the test every strengthening reads, off the node.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a type naming the binder deep under other formers, one
///   naming only an outer index and a closed one separate the answers.
/// - witness: `rewrite::tests::a_strengthening_reads_the_carried_support`
#[spec(ensures: |ret| match ret {
    Maybe::Present(()) => true,
    Maybe::Absent(strengthening::Absent::MentionsBinder) => past != Binders::NONE,
})]
fn mentions_none_below(
    arena: &CoreArena,
    node: Node,
    past: Binders,
) -> Maybe<(), strengthening::Absent>
{
    match carried(arena, node) {
        Maybe::Present(support) => match support.indices(Zone::Intuitionistic).next() {
            Some(innermost) if u32::from(innermost) < past.0 => {
                Maybe::Absent(strengthening::Absent::MentionsBinder)
            },
            Some(_) | None => Maybe::Present(()),
        },
        Maybe::Absent(unminted::Absent::Dangling) => Maybe::Present(()),
    }
}

/// Lower a value type out from under its `past` innermost binders, as an
/// update of the relocation at its root.
///
/// # Specification
/// - requires: `subject` names a value type of `arena` formed in some context
///   `Γ` extended by `past` binders.
/// - ensures: when the subject's carried support selects none of the `past`
///   binders, the same type in `Γ`: `subject` under a lowering by `past` fitted
///   to its support, minting nothing; the subject plain past no binder.
///   [`strengthening::Absent::MentionsBinder`] when the support selects one.
/// - provides: a constructor field's type read outside the binders of the
///   fields before it, where it names none of them.
/// - fails: never; a mention is a named absence.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a type that mentions a binder and one that mentions only
///   an outer index separate the two answers, past one binder and past two, the
///   second read back lowered with every family's length unchanged.
/// - witness: `rewrite::tests::a_value_type_strengthens_unless_it_names_a_binder`
/// - witness: `rewrite::tests::a_strengthening_reads_the_carried_support`
#[spec(ensures: |ret| match ret {
    | Maybe::Present(lowered) => lowered.node() == subject || arena.value_type(lowered.node()).is_some(),
    | Maybe::Absent(strengthening::Absent::MentionsBinder) => past != Binders::NONE,
})]
#[inline]
pub fn strengthen_value_type(
    arena: &mut CoreArena,
    subject: ValueTypeId,
    past: Binders,
) -> Maybe<Relocated<ValueTypeId>, strengthening::Absent>
{
    if let Maybe::Absent(reason) = mentions_none_below(arena, Node::ValueType(subject), past) {
        return Maybe::Absent(reason);
    }
    let lowered = updated(
        arena,
        (Node::ValueType(subject), Relocation::IDENTITY),
        Relocation::lowering(past),
        past,
        Offset::lower(past),
    );
    Maybe::Present(match lowered {
        (Node::ValueType(id), at) => Relocated::pending(id, at),
        (Node::Value(_) | Node::Computation(_) | Node::CompType(_), _) => Relocated::from(subject),
    })
}

/// Lower a value out from under its `past` innermost binders, as an update of
/// the relocation at its root.
///
/// # Specification
/// - requires: `subject` names a value of `arena` formed in some context `Γ`
///   extended by `past` binders.
/// - ensures: as [`strengthen_value_type`], for a value.
/// - provides: a solution found under binders a metavariable's context does not
///   hold, read in that context.
/// - fails: never; a mention is a named absence.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a value naming the inner of two binders, one naming only
///   past both and a closed one separate the answers, the second read back
///   lowered.
/// - witness: `rewrite::tests::a_value_strengthens_unless_it_names_a_binder`
#[spec(ensures: |ret| match ret {
    | Maybe::Present(lowered) => lowered.node() == subject || arena.value(lowered.node()).is_some(),
    | Maybe::Absent(strengthening::Absent::MentionsBinder) => past != Binders::NONE,
})]
#[inline]
pub fn strengthen_value(
    arena: &mut CoreArena,
    subject: ValueId,
    past: Binders,
) -> Maybe<Relocated<ValueId>, strengthening::Absent>
{
    if let Maybe::Absent(reason) = mentions_none_below(arena, Node::Value(subject), past) {
        return Maybe::Absent(reason);
    }
    let lowered = updated(
        arena,
        (Node::Value(subject), Relocation::IDENTITY),
        Relocation::lowering(past),
        past,
        Offset::lower(past),
    );
    Maybe::Present(match lowered {
        (Node::Value(id), at) => Relocated::pending(id, at),
        (Node::Computation(_) | Node::ValueType(_) | Node::CompType(_), _) => {
            Relocated::from(subject)
        },
    })
}

/// The classifier of a constructor of `family` over the field telescope
/// `fields`.
///
/// It reads `U (A₀ → … → F family)`, an arrow where the rest names no binder
/// of the field it crosses and a dependent arrow where it does.
///
/// # Specification
/// - requires: `family` and the first field are scoped in one context `Γ`, each
///   later field under `Γ` and the fields before it.
/// - ensures: in `Γ`, the thunk of the chain over every field, `family` at the
///   end; each field's binder dropped where nothing after it names it, so a
///   telescope of independent fields reads as a chain of plain arrows.
/// - provides: what a constructor's name answers at, wherever a constructor is
///   shown as a function from its fields.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// - reason: a `for` loop over the fields, innermost first.
/// - measure: the fields left.
///
/// # Adequacy
/// - hypothesis: L3 — a list's `cons` reads as plain arrows, and a field the
///   next one names as a dependent arrow binding it.
/// - witness: `rewrite::tests::a_constructor_classifier_binds_only_the_fields_named_after_them`
#[spec(ensures: |ret| matches!(arena.value_type(ret), Some(&ValueType::Thunk(_))))]
#[inline]
pub fn constructor_classifier(
    arena: &mut CoreArena,
    family: ValueTypeId,
    fields: &[ValueTypeId],
) -> ValueTypeId
{
    let past = Binders::from(u32::try_from(fields.len()).unwrap_or(u32::MAX));
    let shifted = shift_value_type(arena, family, past).settle(arena);
    let mut chain = arena.comp_type_returner(shifted);
    for &field in fields.iter().rev() {
        chain = match strengthen_comp_type(arena, chain) {
            Maybe::Present(lowered) => {
                let lowered = lowered.settle(arena);
                arena.comp_type_arrow(field, lowered)
            },
            Maybe::Absent(_) => arena.comp_type_pi(field, chain),
        };
    }
    arena.value_type_thunk(chain)
}

/// Shift free value occurrences, preserving variables bound within the
/// value, as an update of the relocation at its root.
///
/// # Specification
/// - requires: the subject is live in this arena, plain or read through a
///   relocation.
/// - ensures: as [`shift_value_type`], for a value.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — nominal arguments and record fields retain their ambient
///   scope.
/// - witness: `rewrite::tests::native_motives_preserve_binder_and_field_order`
#[spec(ensures: |ret| (amount != Binders::NONE || ret == Into::<Relocated<ValueId>>::into(subject))
    && (ret.node() == Into::<Relocated<ValueId>>::into(subject).node()
        || arena.value(ret.node()).is_some()))]
#[must_use]
#[inline]
pub fn shift_value<Subject>(
    arena: &mut CoreArena,
    subject: Subject,
    amount: Binders,
) -> Relocated<ValueId>
where
    Subject: Into<Relocated<ValueId>> + Copy,
{
    let subject = subject.into();
    let scope = Binders::NONE;
    match updated(
        arena,
        (Node::Value(subject.node()), subject.relocation()),
        Relocation::raise(amount, scope),
        scope,
        Offset::raise(amount),
    ) {
        (Node::Value(id), at) => Relocated::pending(id, at),
        (Node::Computation(_) | Node::ValueType(_) | Node::CompType(_), _) => subject,
    }
}

/// Substitute an argument for a value type's innermost intuitionistic binder.
///
/// # Specification
/// - requires: the subject is scoped under one binder beyond the argument.
/// - ensures: the binder is removed without capturing the argument's free
///   indices.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — nominal argument substitution separates local and ambient
///   indices.
/// - witness: `rewrite::tests::native_motives_preserve_binder_and_field_order`
#[spec(ensures: |ret| ret == subject || arena.value_type(ret).is_some())]
#[must_use]
#[inline]
pub fn instantiate_value_type(
    arena: &mut CoreArena,
    subject: ValueTypeId,
    argument: ValueId,
) -> ValueTypeId
{
    match Engine::new(arena).run(
        Node::ValueType(subject),
        Binders::NONE,
        Rewrite::Substitute(argument),
    ) {
        Node::ValueType(id) => id,
        Node::Computation(_) | Node::Value(_) | Node::CompType(_) => subject,
    }
}

/// Shift a computation type while preserving a prefix of local binders, as an
/// update of the relocation at its root.
///
/// # Specification
/// - requires: the subject is live, plain or read through a relocation; scope
///   counts the local intuitionistic binders.
/// - ensures: the subject's node under its relocation and then a raise by
///   `amount` past `scope`, folded to one relocation fitted to its support, so
///   only indices outside that scope rise; the subject as it stands at a zero
///   amount or where nothing outside the scope is free.
/// - provides: insertion of constructor fields outside a case motive's
///   scrutinee binder.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a motive distinguishes its scrutinee binder from an
///   ambient index.
/// - witness: `rewrite::tests::native_motives_preserve_binder_and_field_order`
#[spec(ensures: |ret| (amount != Binders::NONE || ret == Into::<Relocated<CompTypeId>>::into(subject))
    && (ret.node() == Into::<Relocated<CompTypeId>>::into(subject).node()
        || arena.comp_type(ret.node()).is_some()))]
#[must_use]
#[inline]
pub fn shift_comp_type_under<Subject>(
    arena: &mut CoreArena,
    subject: Subject,
    scope: Binders,
    amount: Binders,
) -> Relocated<CompTypeId>
where
    Subject: Into<Relocated<CompTypeId>> + Copy,
{
    let subject = subject.into();
    match updated(
        arena,
        (Node::CompType(subject.node()), subject.relocation()),
        Relocation::raise(amount, scope),
        scope,
        Offset::raise(amount),
    ) {
        (Node::CompType(id), at) => Relocated::pending(id, at),
        (Node::Value(_) | Node::Computation(_) | Node::ValueType(_), _) => subject,
    }
}

/// Shift a value type while preserving a prefix of local binders, as an
/// update of the relocation at its root.
///
/// # Specification
/// - requires: the subject is live, plain or read through a relocation; scope
///   counts the local intuitionistic binders.
/// - ensures: as [`shift_comp_type_under`].
/// - provides: a family under its own binder carried under one binder more, as
///   the identity at a dependent pair carries its second factor under the first
///   coordinate's path.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a family keeps its own binder and lifts an ambient index.
/// - witness: `rewrite::tests::a_value_type_under_its_binder_lifts_only_the_ambient_index`
#[spec(ensures: |ret| (amount != Binders::NONE || ret == Into::<Relocated<ValueTypeId>>::into(subject))
    && (ret.node() == Into::<Relocated<ValueTypeId>>::into(subject).node()
        || arena.value_type(ret.node()).is_some()))]
#[must_use]
#[inline]
pub fn shift_value_type_under<Subject>(
    arena: &mut CoreArena,
    subject: Subject,
    scope: Binders,
    amount: Binders,
) -> Relocated<ValueTypeId>
where
    Subject: Into<Relocated<ValueTypeId>> + Copy,
{
    let subject = subject.into();
    match updated(
        arena,
        (Node::ValueType(subject.node()), subject.relocation()),
        Relocation::raise(amount, scope),
        scope,
        Offset::raise(amount),
    ) {
        (Node::ValueType(id), at) => Relocated::pending(id, at),
        (Node::Value(_) | Node::Computation(_) | Node::CompType(_), _) => subject,
    }
}

/// Shift a computation while preserving a prefix of local binders, as an
/// update of the relocation at its root.
///
/// # Specification
/// - requires: the subject is live, plain or read through a relocation; scope
///   counts the local intuitionistic binders.
/// - ensures: as [`shift_comp_type_under`].
/// - provides: a computation moved under binders a lowering puts around it.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a computation's own binder, an index inside the scope and
///   one past it, settled with its copies reported.
/// - witness: `rewrite::tests::a_traced_shift_raises_only_past_its_scope`
#[spec(ensures: |ret| (amount != Binders::NONE || ret == Into::<Relocated<ComputationId>>::into(subject))
    && (ret.node() == Into::<Relocated<ComputationId>>::into(subject).node()
        || arena.computation(ret.node()).is_some()))]
#[must_use]
#[inline]
pub fn shift_computation_under<Subject>(
    arena: &mut CoreArena,
    subject: Subject,
    scope: Binders,
    amount: Binders,
) -> Relocated<ComputationId>
where
    Subject: Into<Relocated<ComputationId>> + Copy,
{
    let subject = subject.into();
    match updated(
        arena,
        (Node::Computation(subject.node()), subject.relocation()),
        Relocation::raise(amount, scope),
        scope,
        Offset::raise(amount),
    ) {
        (Node::Computation(id), at) => Relocated::pending(id, at),
        (Node::Value(_) | Node::ValueType(_) | Node::CompType(_), _) => subject,
    }
}

/// The engine node a term id names.
///
/// # Specification
/// trivial.
const fn term_node(term: TermId) -> Node
{
    match term {
        TermId::Value(id) => Node::Value(id),
        TermId::Computation(id) => Node::Computation(id),
    }
}

/// The term id an engine result names, in `subject`'s family.
///
/// # Specification
/// trivial.
const fn node_term(
    node: Node,
    subject: TermId,
) -> TermId
{
    match (node, subject) {
        (Node::Value(id), TermId::Value(_)) => TermId::Value(id),
        (Node::Computation(id), TermId::Computation(_)) => TermId::Computation(id),
        (Node::Value(_) | Node::Computation(_) | Node::ValueType(_) | Node::CompType(_), _) => {
            subject
        },
    }
}

/// Fill every hole named `hole` in `subject` by `filling`.
///
/// # Specification
/// - requires: `subject` and `filling` are live in `arena`, and `filling` is
///   written in the context the holes of the name stand in.
/// - ensures: `subject` with every hole of the name in `filling`'s family
///   replaced by `filling` itself, not carried under the binders it stands
///   beneath; a hole of the other family or of another name stands; `subject`
///   itself when it holds no such hole, in the same family.
/// - provides: the syntactic half of filling: a program, or a suspended body,
///   read with the hole written.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a hole under a binder, a hole of another name, a
///   computation hole of the same name and a hole-free subterm separate the
///   filled position, the name check, the family check and identity reuse.
/// - witness: `rewrite::tests::a_fill_replaces_exactly_the_named_holes`
#[spec(ensures: |ret| core::mem::discriminant(&ret) == core::mem::discriminant(&subject))]
#[inline]
#[must_use]
pub fn fill_hole(
    arena: &mut CoreArena,
    subject: TermId,
    hole: HoleId,
    filling: TermId,
) -> TermId
{
    let filled = Engine::new(arena).run(
        term_node(subject),
        Binders::NONE,
        Rewrite::Fill(hole, term_node(filling)),
    );
    node_term(filled, subject)
}

/// Fill every value hole named `hole` in the value type `subject`, read under
/// `under` binders, by `solution`, written under `scope` binders: a
/// metavariable's solution read into a type that mentions it.
///
/// # Specification
/// - requires: `subject` and `solution` are live in `arena`.
/// - ensures: `subject` with each occurrence of the hole that stands under
///   exactly `scope` binders, counting `under`, replaced by `solution`, and
///   each deeper one by `solution` raised past the binders between; an
///   occurrence shallower than `scope`, a computation hole and a hole of
///   another name stand; `subject` itself when it holds no such hole.
/// - provides: a type the checker recorded while a metavariable stood unsolved,
///   read with its solution.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an occurrence at the scope, one a binder past it inside
///   the type, one read shallower than the scope and a hole-free type separate
///   the placement, the raise, the standing occurrence and identity reuse.
/// - witness: `rewrite::tests::a_solution_fills_a_type_raised_past_its_scope_1216`
#[spec(ensures: |ret| ret == subject || arena.value_type(ret).is_some())]
#[inline]
#[must_use]
pub fn fill_value_type_hole(
    arena: &mut CoreArena,
    (subject, under): (ValueTypeId, Binders),
    hole: HoleId,
    (solution, scope): (ValueId, Binders),
) -> ValueTypeId
{
    match Engine::new(arena).run(
        Node::ValueType(subject),
        under,
        Rewrite::Solve(hole, solution, scope),
    ) {
        Node::ValueType(id) => id,
        Node::Value(_) | Node::Computation(_) | Node::CompType(_) => subject,
    }
}

/// [`fill_value_type_hole`] at a value: a body whose holes stand for
/// metavariables, read with their solutions.
///
/// # Specification
/// - requires: as [`fill_value_type_hole`].
/// - ensures: as [`fill_value_type_hole`], at a value.
/// - provides: a body the checker judged with metavariables standing, read with
///   their solutions; a solution mentioning another hole raises that hole's
///   solution past the binders between their scopes.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`fill_value_type_hole`].
/// - witness: `rewrite::tests::a_solution_fills_a_type_raised_past_its_scope_1216`
#[spec(ensures: |ret| ret == subject || arena.value(ret).is_some())]
#[inline]
#[must_use]
pub fn fill_value_hole(
    arena: &mut CoreArena,
    (subject, under): (ValueId, Binders),
    hole: HoleId,
    (solution, scope): (ValueId, Binders),
) -> ValueId
{
    match Engine::new(arena).run(
        Node::Value(subject),
        under,
        Rewrite::Solve(hole, solution, scope),
    ) {
        Node::Value(id) => id,
        Node::Computation(_) | Node::ValueType(_) | Node::CompType(_) => subject,
    }
}

/// [`fill_value_type_hole`] at a computation type.
///
/// # Specification
/// - requires: as [`fill_value_type_hole`].
/// - ensures: as [`fill_value_type_hole`], at a computation type.
/// - provides: as [`fill_value_type_hole`].
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`fill_value_type_hole`].
/// - witness: `rewrite::tests::a_solution_fills_a_type_raised_past_its_scope_1216`
#[spec(ensures: |ret| ret == subject || arena.comp_type(ret).is_some())]
#[inline]
#[must_use]
pub fn fill_comp_type_hole(
    arena: &mut CoreArena,
    (subject, under): (CompTypeId, Binders),
    hole: HoleId,
    (solution, scope): (ValueId, Binders),
) -> CompTypeId
{
    match Engine::new(arena).run(
        Node::CompType(subject),
        under,
        Rewrite::Solve(hole, solution, scope),
    ) {
        Node::CompType(id) => id,
        Node::Value(_) | Node::Computation(_) | Node::ValueType(_) => subject,
    }
}

/// Wrap every term `sites` names, within `subject`, in its mark.
///
/// # Specification
/// - requires: `subject` is live in `arena`.
/// - ensures: `subject` rebuilt with every named term — wherever it is reached,
///   types' codes included — wrapped in the mark `sites` gives it, its own
///   children wrapped first; `subject` itself when `sites` names nothing it
///   reaches.
/// - provides: the marked elaboration a total judgement answers, built once
///   from the marks it recorded.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a marked leaf, a marked variable, a marked compound whose
///   child is marked too, and an unmarked sibling separate wrapping, nesting
///   and the identity on unnamed nodes.
/// - witness: `rewrite::tests::a_wrap_marks_exactly_the_named_nodes`
#[spec(ensures: |ret| core::mem::discriminant(&ret) == core::mem::discriminant(&subject))]
#[inline]
#[must_use]
pub fn wrap_marks(
    arena: &mut CoreArena,
    subject: TermId,
    sites: &BTreeMap<TermId, MarkIndex>,
) -> TermId
{
    let mut engine = Engine::new(arena);
    engine.sites = sites
        .iter()
        .map(|(&site, &mark)| (term_node(site), mark))
        .collect();
    let wrapped = engine.run(term_node(subject), Binders::NONE, Rewrite::Wrap);
    node_term(wrapped, subject)
}

/// Apply, within `subject`, the reduct `crossings` gives each value it names
/// to that value, as a run, reporting every node it rewrote and every run it
/// minted.
///
/// # Specification
/// - requires: `subject` is live in `arena`.
/// - ensures: `subject` rebuilt with every named value `v`, its own children
///   rebuilt first, standing as the run `run(r(v))` of its reduct `r`;
///   `subject` itself when `crossings` names nothing it reaches; `carried`
///   gains one pair per node the rebuild carried over — a named value beside
///   the value it stands as inside its run, when that is another — and `runs`
///   each run minted, in minting order.
/// - provides: the body whose runs the nested elaboration binds before their
///   regions, as a run the source wrote.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a crossed argument of a call and an uncrossed sibling
///   separate the run minted at the one from the identity on the other.
/// - witness: `rewrite::tests::a_crossing_runs_its_reduct_at_exactly_the_named_values`
#[spec(captures: [held = carried.len(), minted = runs.len()],
    ensures: |ret| carried.len() >= held && runs.len() >= minted
        && (runs.len() > minted || ret == subject))]
#[inline]
pub fn cross_reducts(
    arena: &mut CoreArena,
    subject: ValueId,
    crossings: &BTreeMap<ValueId, ConstantIndex>,
    carried: &mut Vec<Carried>,
    runs: &mut Vec<ValueId>,
) -> ValueId
{
    let mut engine = Engine::new(arena);
    engine.crossings = crossings.clone();
    let crossed = engine.run(Node::Value(subject), Binders::NONE, Rewrite::Wrap);
    // A crossed value is carried to what stands for it inside its run, so a
    // decision or an origin read through `carried` stays at the value.
    let inside: BTreeMap<ValueId, ValueId> = engine
        .crossed
        .iter()
        .map(|&(within, run)| (run, within))
        .collect();
    let mut reported = Vec::new();
    report(&engine.memo, &mut reported);
    carried.extend(reported.into_iter().filter_map(|pair| match pair {
        Carried::Value(held, written) => match inside.get(&written) {
            Some(&within) if within == held => None,
            Some(&within) => Some(Carried::Value(held, within)),
            None => Some(pair),
        },
        Carried::Computation(..) | Carried::ValueType(..) | Carried::CompType(..) => Some(pair),
    }));
    runs.extend(engine.crossed.iter().map(|&(_, run)| run));
    match crossed {
        Node::Value(id) => id,
        Node::Computation(_) | Node::ValueType(_) | Node::CompType(_) => subject,
    }
}

/// How the checker decided a computation written where a value is read.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Nesting
{
    /// Expected at a thunk type, it is suspended, as a written thunk is.
    Thunk,
    /// Expected at any other type, it runs before its region and stands for
    /// the value it returns.
    Run,
    /// Run purely where a type after it reads it — a dependent pair's first
    /// component, a dependent function's argument — it stands as the value it
    /// returns, `⟨c⟩`, so that type reads the computation rather than a bound
    /// variable it could not see through.
    Returned,
}

/// A run with no computation enclosing it to run before.
///
/// It stands in a definition's own value, beneath a static lambda or a static
/// application, which are erased before anything runs, or in a type, where
/// nothing runs.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Unenclosed
{
    /// The run.
    run: ValueId,
}

impl Unenclosed
{
    /// The run that found no computation to run before.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn run(self) -> ValueId
    {
        self.run
    }
}

/// A position the survey reads, beside where a run met there would hoist.
#[derive(Clone, Copy, Debug)]
enum Position
{
    /// A value, and the computation it stands in the values of, if any.
    Value(ValueId, Maybe<ComputationId, ()>),
    /// A computation, and the region of the application spine it heads, if
    /// it heads one.
    Computation(ComputationId, Maybe<ComputationId, ()>),
}

/// Every run `subject` holds, grouped by the region it runs before, each
/// region's in written order.
///
/// A run's region is the innermost computation whose values it stands in:
/// an application's head shares its spine's region, so `f(g(x), h(y))` runs
/// `g` and then `h` before the whole call; every other computation child —
/// a thunk's body, a case arm, a lambda's body, either half of a bind — is a
/// region of its own, so no run leaves a suspension or a branch. Written
/// order is the region's values read left to right, a head before its
/// argument, a run before the runs nested in its own computation, which
/// form that computation's region. A record's fields read in label order,
/// the order the core holds them in.
///
/// # Specification
/// - requires: `subject` is live in `arena`.
/// - ensures: every `Run`, and every `Nested` that `nesting` decides to run,
///   reachable from `subject` through terms, listed once under its region
///   beside its computation; types are not entered.
/// - provides: the regions an elaboration hoists into.
/// - fails: [`Unenclosed`] for the first run, in written order, that stands in
///   no computation's values, and then for the first node `nesting` decides
///   that no term of `subject` reaches — one standing in a type.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — runs beside a thunk, in a case arm, in an application
///   spine and in a definition's own value separate the region rule, the
///   boundaries and the refusal; every former of the shared fixture, with no
///   run beneath it, surveys to no region.
/// - witness: `rewrite::tests::an_elaboration_never_hoists_out_of_a_thunk_or_an_arm`
/// - witness: `rewrite::tests::a_run_in_no_computation_is_unenclosed`
/// - witness: `rewrite::tests::a_decision_no_term_reaches_is_unenclosed`
/// - witness: `rewrite::tests::an_undecided_elaboration_keeps_every_former_but_the_run`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |regions| regions.values().all(|runs| !runs.is_empty())))]
fn survey(
    arena: &CoreArena,
    subject: ValueId,
    nesting: &BTreeMap<ValueId, Nesting>,
) -> Result<BTreeMap<ComputationId, Vec<(ValueId, ComputationId)>>, Unenclosed>
{
    let mut regions: BTreeMap<ComputationId, Vec<(ValueId, ComputationId)>> = BTreeMap::new();
    let mut met = alloc::collections::BTreeSet::new();
    let mut pending = alloc::vec![Position::Value(subject, Maybe::Absent(()))];
    while let Some(position) = pending.pop() {
        let ready = pending.len();
        match position {
            Position::Value(id, region) => {
                let Some(value) = arena.value(id)
                else {
                    continue;
                };
                if matches!(*value, Value::Nested(_) | Value::Run(_)) {
                    let _first = met.insert(id);
                }
                survey_value(value, id, region, nesting, &mut regions, &mut pending)?;
            },
            Position::Computation(id, spine) => {
                let Some(computation) = arena.computation(id)
                else {
                    continue;
                };
                let region = Maybe::Present(match spine {
                    Maybe::Present(region) => region,
                    Maybe::Absent(()) => id,
                });
                survey_computation(computation, region, &mut pending);
            },
        }
        if let Some(written) = pending.get_mut(ready ..) {
            written.reverse();
        }
    }
    if let Some(&run) = nesting.keys().find(|decided| !met.contains(*decided)) {
        return Err(Unenclosed { run });
    }
    Ok(regions)
}

/// Read one value for the survey: record it if it runs, and list its
/// children in written order beside their regions.
///
/// # Specification
/// - requires: `value` is the node `id` names, standing in `region`'s values.
/// - ensures: a run is appended to `region`'s list; `next` gains the value's
///   term children, in order, a value child in `region` unless a static former
///   erases it and a computation child heading its own region.
/// - provides: the value half of the survey.
/// - fails: [`Unenclosed`] when the value runs and `region` is absent.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`survey`].
/// - witness: `rewrite::tests::an_elaboration_never_hoists_out_of_a_thunk_or_an_arm`
#[spec(captures: before = next.len(), ensures: |ret| ret.is_err() || next.len() >= before)]
fn survey_value(
    value: &Value,
    id: ValueId,
    region: Maybe<ComputationId, ()>,
    nesting: &BTreeMap<ValueId, Nesting>,
    regions: &mut BTreeMap<ComputationId, Vec<(ValueId, ComputationId)>>,
    next: &mut Vec<Position>,
) -> Result<(), Unenclosed>
{
    let own = Maybe::Absent(());
    match *value {
        Value::Nested(nested) | Value::Run(nested) => {
            if matches!(*value, Value::Run(_)) || nesting.get(&id) == Some(&Nesting::Run) {
                let Maybe::Present(enclosing) = region
                else {
                    return Err(Unenclosed { run: id });
                };
                regions.entry(enclosing).or_default().push((id, nested));
            }
            next.push(Position::Computation(nested, own));
        },
        Value::Primitive { body, .. } | Value::Returned(body) | Value::Thunk(body) => {
            next.push(Position::Computation(body, own));
        },
        Value::PathRefl(inner)
        | Value::Here(inner)
        | Value::Stay(inner)
        | Value::Forward(inner)
        | Value::Injection(_, inner)
        | Value::Lift { body: inner, .. }
        | Value::Ascribe { value: inner, .. }
        | Value::Mark { body: inner, .. } => next.push(Position::Value(inner, region)),
        Value::PathProduct(left, right)
        | Value::Funext(left, right)
        | Value::Equiv(left, right)
        | Value::Univalence(left, right)
        | Value::Then(left, right)
        | Value::FlowProduct(left, right)
        | Value::FunctionFlow(left, right)
        | Value::ListCons(left, right)
        | Value::PathEquiv {
            forward: left,
            backward: right,
            ..
        }
        | Value::Ua {
            forward: left,
            backward: right,
            ..
        } => next.extend([
            Position::Value(left, region),
            Position::Value(right, region),
        ]),
        Value::StaticLambda(body) => next.push(Position::Value(body, own)),
        Value::StaticApplication(head, argument) => {
            next.extend([Position::Value(head, own), Position::Value(argument, own)]);
        },
        Value::SessionRelated {
            source,
            target,
            payloads,
            ..
        } => {
            next.extend([
                Position::Value(source, own),
                Position::Value(target, own),
                Position::Value(payloads, region),
            ]);
        },
        Value::Recorded(ref moves) => {
            next.extend(
                moves
                    .iter()
                    .filter_map(|movement| match movement.payload() {
                        Maybe::Present(payload) => Some(Position::Value(payload, region)),
                        Maybe::Absent(_) => None,
                    }),
            );
        },
        Value::Tuple(ref components) => next.extend(
            components
                .iter()
                .map(|&component| Position::Value(component, region)),
        ),
        Value::Constructor { ref fields, .. } => {
            next.extend(fields.iter().map(|&field| Position::Value(field, region)));
        },
        Value::Record(ref fields) => {
            next.extend(fields.values().map(|&field| Position::Value(field, region)));
        },
        Value::Reify(ref frames) => {
            next.extend(frames.iter().filter_map(|frame| match *frame {
                crate::control::StackFrame::Apply(argument) => {
                    Some(Position::Value(argument, region))
                },
                crate::control::StackFrame::Bind(body) => Some(Position::Computation(body, own)),
                crate::control::StackFrame::Project(_) => None,
            }));
        },
        Value::Variable { .. }
        | Value::Constant(_)
        | Value::Literal(_)
        | Value::ListNil
        | Value::Quote(_)
        | Value::QuoteComputation(_)
        | Value::Hole(_) => {},
    }
    Ok(())
}

/// List one computation's term children for the survey, in written order,
/// beside their regions.
///
/// # Specification
/// - requires: `region` is where the computation's own values hoist: its
///   spine's region when it heads an application, itself otherwise.
/// - ensures: `next` gains the computation's term children in order: a value in
///   `region`, an application's head carrying `region` as its spine, and every
///   other computation child heading its own region.
/// - provides: the computation half of the survey.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`survey`].
/// - witness: `rewrite::tests::an_elaboration_runs_in_written_order_before_its_region`
#[spec(captures: before = next.len(), ensures: next.len() >= before)]
fn survey_computation(
    computation: &Computation,
    region: Maybe<ComputationId, ()>,
    next: &mut Vec<Position>,
)
{
    let own = Maybe::Absent(());
    match *computation {
        Computation::Application(head, argument) => next.extend([
            Position::Computation(head, region),
            Position::Value(argument, region),
        ]),
        Computation::Primitive { ref arguments, .. } => next.extend(
            arguments
                .iter()
                .map(|&argument| Position::Value(argument, region)),
        ),
        Computation::Transport(path, value)
        | Computation::PathTransport { path, value, .. }
        | Computation::Ride {
            flow: path, value, ..
        } => {
            next.extend([
                Position::Value(path, region),
                Position::Value(value, region),
            ]);
        },
        Computation::TelescopeTransport {
            path,
            start,
            over,
            value,
            ..
        } => next.extend([
            Position::Value(path, region),
            Position::Value(start, region),
            Position::Value(over, region),
            Position::Value(value, region),
        ]),
        Computation::Return(value)
        | Computation::Abandon(value)
        | Computation::Force(value)
        | Computation::RecordProjection(value, _)
        | Computation::TupleProjection(value, _)
        | Computation::Perform { payload: value, .. } => next.push(Position::Value(value, region)),
        Computation::Exercise {
            capability,
            payload,
            ..
        } => next.extend([
            Position::Value(capability, region),
            Position::Value(payload, region),
        ]),
        Computation::Lambda(body)
        | Computation::Fixpoint { body, .. }
        | Computation::Reset(body)
        | Computation::Shift(body)
        | Computation::Project(_, body)
        | Computation::Mark { body, .. }
        | Computation::Ascribe { body, .. } => next.push(Position::Computation(body, own)),
        Computation::Bind(first, second) => {
            next.extend([
                Position::Computation(first, own),
                Position::Computation(second, own),
            ]);
        },
        Computation::With(ref components) => next.extend(
            components
                .iter()
                .map(|&component| Position::Computation(component, own)),
        ),
        Computation::Case {
            scrutinee,
            ref branches,
        } => {
            next.push(Position::Value(scrutinee, region));
            next.extend(
                branches
                    .iter()
                    .map(|&branch| Position::Computation(branch, own)),
            );
        },
        Computation::DataCase {
            scrutinee,
            ref branches,
            ..
        } => {
            next.push(Position::Value(scrutinee, region));
            next.extend(
                branches
                    .iter()
                    .map(|&branch| Position::Computation(branch, own)),
            );
        },
        Computation::Split {
            scrutinee, body, ..
        } => next.extend([
            Position::Value(scrutinee, region),
            Position::Computation(body, own),
        ]),
        Computation::ListFold {
            list,
            on_nil,
            on_cons,
            ..
        }
        | Computation::ListCase {
            list,
            on_nil,
            on_cons,
            ..
        } => next.extend([
            Position::Value(list, region),
            Position::Computation(on_nil, own),
            Position::Computation(on_cons, own),
        ]),
        Computation::Handle {
            subject,
            on_return,
            ref clauses,
            ..
        }
        | Computation::Scope {
            subject,
            on_return,
            ref clauses,
            ..
        } => {
            next.extend([
                Position::Computation(subject, own),
                Position::Computation(on_return, own),
            ]);
            next.extend(
                clauses
                    .iter()
                    .map(|clause| Position::Computation(clause.body, own)),
            );
        },
        Computation::Resume(stack, body) => {
            next.extend([
                Position::Value(stack, region),
                Position::Computation(body, own),
            ]);
        },
        Computation::Session(ref action) => {
            next.extend(
                action
                    .values()
                    .map(|payload| Position::Value(payload, region)),
            );
            next.extend(
                action
                    .computations()
                    .map(|body| Position::Computation(body, own)),
            );
        },
        Computation::Memory(ref form) => {
            next.extend(form.values().map(|value| Position::Value(value, region)));
            next.extend(
                form.computations()
                    .map(|body| Position::Computation(body, own)),
            );
        },
        Computation::World(ref form) => {
            next.extend(form.values().map(|value| Position::Value(value, region)));
            next.extend(
                form.computations()
                    .map(|body| Position::Computation(body, own)),
            );
        },
        Computation::Hole(_) => {},
    }
}

/// Elaborate every computation `subject` holds written where a value is
/// read, as `nesting` decides it, reporting every node it rewrote.
///
/// A suspended one becomes the thunk of its elaborated computation. The runs
/// of each region become binds wrapping it, the first written outermost,
/// each over its elaborated computation, and each run stands as the variable
/// its bind binds. A `Run` always runs. The order and the regions are
/// [`survey`]'s.
///
/// # Specification
/// - requires: `subject` is live in `arena`; `nesting` decides every `Nested`
///   reachable from it through terms.
/// - ensures: `subject` with every decided `Nested` and every `Run` reachable
///   through terms elaborated; `subject` itself when it holds none; `carried`
///   gains one pair per node the elaboration rebuilt, the nodes it was built
///   from first, and `binds` one pair per run beside the bind minted for it.
/// - provides: the elaborated body a checker answers, built once from the
///   decisions it recorded.
/// - fails: [`Unenclosed`] when a run stands in no computation's values, or a
///   decision names a node no term of `subject` reaches.
/// - panics: none.
///
/// # Errors
/// [`Unenclosed`] for the first run, in written order, that stands in no
/// computation's values, then for the first decided node no term reaches.
///
/// # Adequacy
/// - hypothesis: L3 — two runs in one spine, a suspension beside a run, a run
///   in a thunk, a run in a case arm, a run nested in another's computation and
///   a run in a definition's own value separate written order, the two
///   decisions, the boundaries, nesting and the refusal; the suspension beside
///   a run, which rebuilds the region before its splice, separates a report of
///   every node minted from one that drops the region's closed body.
/// - witness: `rewrite::tests::an_elaboration_runs_in_written_order_before_its_region`
/// - witness: `rewrite::tests::an_elaboration_suspends_and_runs_as_decided`
/// - witness: `rewrite::tests::an_elaboration_never_hoists_out_of_a_thunk_or_an_arm`
/// - witness: `rewrite::tests::a_run_in_no_computation_is_unenclosed`
/// - witness: `rewrite::tests::a_decision_no_term_reaches_is_unenclosed`
/// - witness: `rewrite::tests::an_undecided_elaboration_keeps_every_former_but_the_run`
#[spec(captures: [entry = arena.watermark(), held = carried.len(), minted = binds.len()],
    ensures: |ret| ret.is_err() || carried.len() >= held && binds.len() >= minted
        && (binds.len() > minted || carried.len() > held || ret == Ok(subject) && arena.watermark() == entry))]
#[inline]
pub fn elaborate_nested_traced(
    arena: &mut CoreArena,
    subject: ValueId,
    nesting: &BTreeMap<ValueId, Nesting>,
    carried: &mut Vec<Carried>,
    binds: &mut Vec<(ValueId, ComputationId)>,
) -> Result<ValueId, Unenclosed>
{
    let regions = survey(arena, subject, nesting)?;
    let mut engine = Engine::new(arena);
    engine.slots = regions
        .values()
        .flat_map(|runs| {
            runs.iter().rev().enumerate().map(|(inner, &(run, _))| {
                (run, Binders::NONE.deeper_by(ComponentCount::from(inner)))
            })
        })
        .collect();
    engine.nesting = nesting.clone();
    engine.regions = regions;
    let elaborated = engine.run(Node::Value(subject), Binders::NONE, Rewrite::Elaborate);
    report(&engine.memo, carried);
    carried.append(&mut engine.closings);
    binds.append(&mut engine.binds);
    match elaborated {
        Node::Value(id) => Ok(id),
        Node::Computation(_) | Node::ValueType(_) | Node::CompType(_) => Ok(subject),
    }
}

/// Replace every free intuitionistic index of `subject` by the environment
/// entry it counts to.
///
/// # Specification
/// - requires: `subject` is live in `arena` and scoped in a context whose
///   innermost `environment.len()` binders the entries stand for, innermost
///   first; each entry is a value of `arena` in the context the result is read
///   in.
/// - ensures: `subject` with an index counting to entry `i` replaced by that
///   entry carried under the binders it stands beneath, and an index counting
///   past the environment lowered by its length; `subject` itself when the
///   environment is empty.
/// - provides: the substitution a suspended body — a hole's or a mark's closure
///   — is read back through, all at once rather than one binder at a time.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an environment of two entries read at depths zero and one
///   separates an inner index, each entry, an entry carried under a binder and
///   an index past the environment.
/// - witness: `rewrite::tests::an_environment_substitution_replaces_every_free_index`
#[spec(captures: entry = arena.watermark(), ensures: |ret| core::mem::discriminant(&ret) == core::mem::discriminant(&subject)
    && (!environment.is_empty() || (ret == subject && arena.watermark() == entry)))]
#[inline]
#[must_use]
pub fn substitute_environment(
    arena: &mut CoreArena,
    subject: TermId,
    environment: &[ValueId],
) -> TermId
{
    if environment.is_empty() {
        return subject;
    }
    let mut engine = Engine::new(arena);
    engine.environment = environment.to_vec();
    let substituted = engine.run(term_node(subject), Binders::NONE, Rewrite::Environment);
    node_term(substituted, subject)
}

/// A node a rewrite minted, beside the node of its subject it rewrote.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: both ids name nodes of one family.
/// - provides: what a caller keeping metadata per node, a source origin say,
///   copies from the node it held to the node a rewrite put in its place.
/// - executable: none — the pair holds no arena to check either id against.
///
/// # Adequacy
/// - hypothesis: L3 — a substitution under a binder reports the lambda, the
///   return and the variable it rewrote and none of the nodes it kept.
/// - witness: `rewrite::tests::a_traced_substitution_reports_every_node_it_rewrote`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Carried
{
    /// A value of the subject and the value standing for it.
    Value(ValueId, ValueId),
    /// A computation of the subject and the computation standing for it.
    Computation(ComputationId, ComputationId),
    /// A value type of the subject and the value type standing for it.
    ValueType(ValueTypeId, ValueTypeId),
    /// A computation type of the subject and the computation type standing
    /// for it.
    CompType(CompTypeId, CompTypeId),
}

/// [`substitute_environment`], reporting every node it rewrote beside the
/// node it rewrote it from.
///
/// # Specification
/// - requires: as [`substitute_environment`].
/// - ensures: the result [`substitute_environment`] answers; `carried` gains
///   one pair per node of the subject reached at a depth where the rewrite
///   changed it, and per entry carried under a binder, in ascending order of
///   the node rewritten, so a node reached at two depths is reported twice; a
///   node the rewrite kept is never reported, and an empty environment mints
///   and reports nothing.
/// - provides: the substitution for a caller that keeps a table beside the
///   arena, which a rewritten node inherits from the node it stands for.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a lambda over a pair of its own index and a free index
///   beside a closed constant reports exactly the variable, the pair, the
///   return and the lambda; an empty environment reports nothing.
/// - witness: `rewrite::tests::a_traced_substitution_reports_every_node_it_rewrote`
#[spec(captures: entry = (arena.watermark(), carried.len()), ensures: |ret| core::mem::discriminant(&ret) == core::mem::discriminant(&subject)
    && carried.len() >= entry.1
    && (!environment.is_empty() || (ret == subject && arena.watermark() == entry.0 && carried.len() == entry.1)))]
#[inline]
#[must_use]
pub fn substitute_environment_traced(
    arena: &mut CoreArena,
    subject: TermId,
    environment: &[ValueId],
    carried: &mut Vec<Carried>,
) -> TermId
{
    if environment.is_empty() {
        return subject;
    }
    let mut engine = Engine::new(arena);
    engine.environment = environment.to_vec();
    let substituted = engine.run(term_node(subject), Binders::NONE, Rewrite::Environment);
    report(&engine.memo, carried);
    node_term(substituted, subject)
}

/// The constants, atoms and bound regions one instantiation replaces: each
/// constant by another, each atom by a type, each bound region by a region.
///
/// # Specification
/// - requires: nothing to construct this data; a replacing type is a closed
///   type of the arena the renaming is applied in.
/// - ensures: a later entry for a name replaces an earlier one, so the renaming
///   is a function on constants, on atoms and on bound regions.
/// - provides: what [`rename_value_traced`] and [`rename_value_type_traced`]
///   read.
/// - fails: not applicable to the data item.
/// - panics: not applicable to the data item.
/// - executable: none — the maps are private; the renaming functions state what
///   they replace.
///
/// # Adequacy
/// - hypothesis: L3 — as [`rename_value_traced`].
/// - witness: `rewrite::tests::a_renaming_replaces_exactly_the_named_constants_and_atoms`
/// - witness: `rewrite::tests::a_renaming_places_each_named_bound_region_wherever_it_stands`
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Renaming
{
    /// Each constant replaced, with the constant replacing it.
    constants: BTreeMap<ConstantIndex, ConstantIndex>,
    /// Each atom replaced, with the type replacing it.
    atoms: BTreeMap<ConstantIndex, ValueTypeId>,
    /// Each bound region replaced, with the region replacing it.
    regions: BTreeMap<RegionBinder, Region>,
}

impl Renaming
{
    /// The renaming that replaces nothing.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new() -> Self
    {
        Self {
            constants: BTreeMap::new(),
            atoms: BTreeMap::new(),
            regions: BTreeMap::new(),
        }
    }

    /// Replace the constant `from` by the constant `to`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn constant(
        &mut self,
        from: ConstantIndex,
        to: ConstantIndex,
    )
    {
        let _replaced = self.constants.insert(from, to);
    }

    /// Replace the atom `from` by the type `to`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn atom(
        &mut self,
        from: ConstantIndex,
        to: ValueTypeId,
    )
    {
        let _replaced = self.atoms.insert(from, to);
    }

    /// Replace the bound region `from` by the region `to`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn region(
        &mut self,
        from: RegionBinder,
        to: Region,
    )
    {
        let _replaced = self.regions.insert(from, to);
    }

    /// The region `region` stands at under this renaming: the one it names
    /// for a bound region it replaces, `region` itself otherwise.
    ///
    /// # Specification
    /// - ensures: [`Region::Bound`] at a binder the renaming names is the
    ///   region named for it; every other region is itself.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`rename_value_type_traced`].
    /// - witness: `rewrite::tests::a_renaming_places_each_named_bound_region_wherever_it_stands`
    #[spec(ensures: |ret| match region {
        Region::Bound(binder) => ret == self.regions.get(&binder).copied().unwrap_or(region),
        Region::Held | Region::Scoped(_) => ret == region,
    })]
    #[inline]
    #[must_use]
    fn placed(
        &self,
        region: Region,
    ) -> Region
    {
        match region {
            Region::Bound(binder) => self.regions.get(&binder).copied().unwrap_or(region),
            Region::Held | Region::Scoped(_) => region,
        }
    }
}

/// The renaming every rewrite but a renaming carries: it names nothing.
static NOTHING_RENAMED: Renaming = Renaming::new();

/// Rename the constants and atoms of the value `subject` by `renaming`,
/// reporting every node it rewrote beside the node it rewrote it from.
///
/// # Specification
/// - requires: `subject` is live in `arena`; every type `renaming` replaces an
///   atom by is a closed type of `arena`.
/// - ensures: `subject` with every constant the renaming names replaced by the
///   constant it names for it and every atom it names by the type it names for
///   it, at every depth and in every family the walk reaches — a quoted type's
///   atoms and a decode's constant among them; every other node kept, and a
///   node none of whose descendants changed is `subject`'s own; `carried` gains
///   one pair per node the renaming changed, as
///   [`substitute_environment_traced`] reports them.
/// - provides: instantiating a body written against one set of declarations at
///   another, for a caller that keeps a table beside the arena.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a lambda whose body pairs a renamed constant, a kept
///   constant and a quoted renamed atom renames exactly the two named leaves,
///   keeps the bound variable, and reports the rewritten nodes; an atom kept by
///   the renaming stands.
/// - witness: `rewrite::tests::a_renaming_replaces_exactly_the_named_constants_and_atoms`
#[spec(captures: before = carried.len(), ensures: |ret| carried.len() >= before && (ret == subject || arena.value(ret).is_some()))]
#[inline]
#[must_use]
pub fn rename_value_traced(
    arena: &mut CoreArena,
    subject: ValueId,
    renaming: &Renaming,
    carried: &mut Vec<Carried>,
) -> ValueId
{
    let mut engine = Engine::new(arena);
    engine.renaming = renaming;
    let renamed = engine.run(Node::Value(subject), Binders::NONE, Rewrite::Rename);
    report(&engine.memo, carried);
    match renamed {
        Node::Value(id) => id,
        Node::Computation(_) | Node::ValueType(_) | Node::CompType(_) => subject,
    }
}

/// Rename the constants and atoms of the value type `subject` by `renaming`,
/// reporting every node it rewrote beside the node it rewrote it from.
///
/// # Specification
/// - requires: as [`rename_value_traced`].
/// - ensures: as [`rename_value_traced`], for a value type: an atom the
///   renaming names standing as the whole subject is the type it names for it,
///   and a kept type or a capability at a bound region it names stands at the
///   region it names for it.
/// - provides: instantiating a declared type, a kind or a representation, and a
///   signature abstracted over regions at one call's.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`rename_value_traced`]; a function type keeping a
///   value at a bound region in its domain and inside its returner's thunk,
///   renamed at a scoped region, keeps both there and keeps an unnamed bound
///   region and a scoped one as they stand.
/// - witness: `rewrite::tests::a_renaming_replaces_exactly_the_named_constants_and_atoms`
/// - witness: `rewrite::tests::a_renaming_places_each_named_bound_region_wherever_it_stands`
#[spec(captures: before = carried.len(), ensures: |ret| carried.len() >= before && (ret == subject || arena.value_type(ret).is_some()))]
#[inline]
#[must_use]
pub fn rename_value_type_traced(
    arena: &mut CoreArena,
    subject: ValueTypeId,
    renaming: &Renaming,
    carried: &mut Vec<Carried>,
) -> ValueTypeId
{
    let mut engine = Engine::new(arena);
    engine.renaming = renaming;
    let renamed = engine.run(Node::ValueType(subject), Binders::NONE, Rewrite::Rename);
    report(&engine.memo, carried);
    match renamed {
        Node::ValueType(id) => id,
        Node::Value(_) | Node::Computation(_) | Node::CompType(_) => subject,
    }
}

/// Read every decode of the binder `family` stands under at `level`: the
/// family a transport or a ride forms its motive as where its path or flow
/// lives in the universe at `level`.
///
/// # Specification
/// - requires: `family` is a value type of `arena` scoped beneath one binder.
/// - ensures: `family` with every decode whose code is that binder's variable,
///   as a value or a computation type at any depth beneath it, read at `level`;
///   every other node as it stands, so a family that reads its binder at
///   `level` already, or never decodes it, answers itself.
/// - provides: the motive of a transport or a ride above level zero.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as the engine's decode step.
/// - witness: `rewrite::tests::a_relevelling_reads_only_the_binders_decodes_at_its_level`
#[spec(ensures: |ret| ret == family || arena.value_type(ret).is_some())]
#[inline]
#[must_use]
pub fn relevel_value_type(
    arena: &mut CoreArena,
    family: ValueTypeId,
    level: Level,
) -> ValueTypeId
{
    let mut engine = Engine::new(arena);
    engine.level = level;
    match engine.run(Node::ValueType(family), Binders::NONE, Rewrite::Relevel) {
        Node::ValueType(id) => id,
        Node::Value(_) | Node::Computation(_) | Node::CompType(_) => family,
    }
}

/// Instantiate the binder of `body` at `argument`, reporting every node it
/// rewrote beside the node it rewrote it from.
///
/// # Specification
/// - requires: `body` is a computation of `arena` scoped beneath one binder in
///   some context `Γ`, and `argument` a value of `arena` in `Γ`.
/// - ensures: as [`instantiate_value`], for a computation: every occurrence of
///   the binder replaced by the argument carried under the binders it crosses
///   and every index outside it lowered by one; `carried` gains one pair per
///   node the substitution changed, as [`substitute_environment_traced`]
///   reports them.
/// - provides: the beta step `x ← return v; N ≡ N[v/x]` for a caller that keeps
///   a table beside the arena.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a lambda over its own index, the binder and an index past
///   it replaces the binder by the argument carried under the lambda, lowers
///   the outer index, and reports exactly the rewritten nodes.
/// - witness: `rewrite::tests::a_traced_instantiation_replaces_its_binder`
#[spec(captures: before = carried.len(), ensures: |ret| carried.len() >= before && (ret == body || arena.computation(ret).is_some()))]
#[inline]
#[must_use]
pub fn instantiate_computation_traced(
    arena: &mut CoreArena,
    body: ComputationId,
    argument: ValueId,
    carried: &mut Vec<Carried>,
) -> ComputationId
{
    let mut engine = Engine::new(arena);
    let instantiated = engine.run(
        Node::Computation(body),
        Binders::NONE,
        Rewrite::Substitute(argument),
    );
    report(&engine.memo, carried);
    match instantiated {
        Node::Computation(id) => id,
        Node::Value(_) | Node::ValueType(_) | Node::CompType(_) => body,
    }
}

/// Report every rewrite `memo` holds that changed its node.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `carried` gains one pair per entry of `memo` whose result is
///   another node of its own family, in the memo's order.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`substitute_environment_traced`].
/// - witness: `rewrite::tests::a_traced_substitution_reports_every_node_it_rewrote`
/// - witness: `rewrite::tests::a_traced_instantiation_reports_no_computation_or_type_it_kept`
#[spec(captures: before = carried.len(), ensures: carried.len() >= before && carried.len() <= before.saturating_add(memo.len()))]
fn report(
    memo: &BTreeMap<(Node, Binders, Rewrite), Node>,
    carried: &mut Vec<Carried>,
)
{
    carried.extend(
        memo.iter()
            .filter_map(|(&(from, _depth, _rewrite), &to)| match (from, to) {
                (Node::Value(held), Node::Value(written)) if held != written => {
                    Some(Carried::Value(held, written))
                },
                (Node::Computation(held), Node::Computation(written)) if held != written => {
                    Some(Carried::Computation(held, written))
                },
                (Node::ValueType(held), Node::ValueType(written)) if held != written => {
                    Some(Carried::ValueType(held, written))
                },
                (Node::CompType(held), Node::CompType(written)) if held != written => {
                    Some(Carried::CompType(held, written))
                },
                _ => None,
            }),
    );
}

#[cfg(test)]
pub mod tests;
