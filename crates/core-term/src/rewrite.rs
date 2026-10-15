//! The rewrites a dependent type needs: shifting a type into a deeper context,
//! instantiating a dependent codomain at an argument, and strengthening a type
//! out from under the binder it was synthesized beneath.
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
//! # One engine, three rewrites
//!
//! The three differ only at a variable occurrence; every other former is a
//! congruence that rewrites its children, each at the depth its position sits
//! at, and mints a node only where a child changed. The engine is iterative —
//! a heap task stack, children opened in reverse and closed in order — so a
//! deep type costs heap rather than stack, and memoized per node at the depth
//! it is reached at, so a shared subterm is rewritten once however many paths
//! reach it.
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
//! replaces a constant by another and an atom by a type, wherever either
//! stands, so a body written against one set of declarations reads against
//! another. Constants and the types replacing atoms are closed, so a renaming
//! carries nothing under the binders it crosses.
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
//! and instantiates types. `shift_value_type` and `shift_comp_type` raise the
//! free indices of the intuitionistic zone at or past a cutoff;
//! `instantiate_comp_type` substitutes a value for the innermost index and
//! lowers the rest; `strengthen_comp_type` lowers a type out of one binder or
//! refuses with `strengthening::Absent::MentionsBinder` when the type mentions
//! it. Each runs on a heap task stack, never recursing, and memoizes per node
//! and binder depth, so a shared subterm is rewritten once per depth it is
//! reached at. A replacement carried under a binder is shifted once per depth
//! and recorded, so substitution avoids capture without renaming anything. The
//! linear zone is left alone: no former in the vocabulary binds into it.
//!
//! Alternatives: recursive rewrites, which the workspace's recursion lint
//! forbids and which a deep type would overflow; and explicit substitutions
//! held lazily in the arena, which every reader would then have to push
//! through. Reversal: a measured family whose cost is dominated by the eager
//! rewrite, which would hold substitutions as closures the way the normalizer
//! already does.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use quenchant_arith::arith;
use quenchant_shape::shape::Maybe;

use crate::arena::CompTypeId;
use crate::arena::ComputationId;
use crate::arena::CoreArena;
use crate::arena::ValueId;
use crate::arena::ValueTypeId;
use crate::hole::HoleId;
use crate::hole::MarkIndex;
use crate::hole::TermId;
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
    /// Raise every free index by the count.
    Shift(Binders),
    /// Replace the index the depth names by the value, and lower every index
    /// outside it.
    Substitute(ValueId),
    /// Lower every index outside the depth, recording a mention of the index
    /// the depth names.
    Lower,
    /// Replace every hole of the name, in the filling's family, by the filling.
    Fill(HoleId, Node),
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
    /// Raise every free index by the count, as a shift does, and answer each
    /// run the engine's slots name by the variable of the bind its region
    /// mints for it.
    Splice(Binders),
}

/// Whether a lowering met the binder it lowers out of.
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
    /// Whether a lowering met its binder.
    mention: Mention,
    /// The nodes a wrap marks, each with its mark.
    sites: BTreeMap<Node, MarkIndex>,
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
            mention: Mention::Absent,
            sites: BTreeMap::new(),
            environment: Vec::new(),
            nesting: BTreeMap::new(),
            regions: BTreeMap::new(),
            slots: BTreeMap::new(),
            binds: Vec::new(),
            closings: Vec::new(),
            renaming: &NOTHING_RENAMED,
        }
    }

    /// Rewrite `subject` at the supplied binder cutoff.
    ///
    /// # Specification
    /// - requires: the subject graph is acyclic wherever its nodes resolve; the
    ///   pending and result stacks are empty. Unreadable ids are admitted.
    /// - ensures: the rewritten node, in the subject's family; an unreadable
    ///   subject answers itself.
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
            && self.memo.get(&(subject, depth, rewrite)) == Some(&ret)
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
                | Task::Open(node, depth, step) => self.open(node, depth, step),
                | Task::Close(node, depth, step) => {
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
                | Task::Record(node, depth, step) => {
                    if let Some(&rewritten) = self.results.last() {
                        let _previous = self.memo.insert((node, depth, step), rewritten);
                    }
                },
                | Task::Hoist(region, depth) => self.hoist(region, depth),
            }
        }
        self.results.pop().unwrap_or(subject)
    }

    /// Open one node: answer it at once when the memo or a variable rule can,
    /// and otherwise schedule its close after its children.
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
    /// - hypothesis: L3 — a memo hit returns the stored result, a free
    ///   occurrence answers immediately, and substitution beneath a binder
    ///   schedules a shifted replacement; the shared-chain and capture
    ///   witnesses separate missing publication, duplicate work and premature
    ///   replacement.
    /// - witness: `rewrite::tests::a_shared_type_is_rewritten_once_per_node`
    /// - witness: `rewrite::tests::substitution_replaces_a_free_occurrence`
    /// - witness: `rewrite::tests::substitution_avoids_capture`
    #[spec(
        captures: [pending = self.tasks.len(), ready = self.results.len()],
        ensures: (ready.checked_add(1) == Some(self.results.len()) && self.tasks.len() == pending
            && self.memo.get(&(node, depth, rewrite)) == self.results.last())
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
            self.results.push(done);
            return;
        }
        if let Maybe::Present(answer) = self.slotted(node, depth, rewrite) {
            let _previous = self.memo.insert((node, depth, rewrite), answer);
            self.results.push(answer);
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
                | Node::Value(id) => {
                    matches!(filling, Node::Value(_))
                        && self.arena.value(id) == Some(&Value::Hole(hole))
                },
                | Node::Computation(id) => {
                    matches!(filling, Node::Computation(_))
                        && self.arena.computation(id) == Some(&Computation::Hole(hole))
                },
                | Node::ValueType(_) | Node::CompType(_) => false,
            }
        {
            let _previous = self.memo.insert((node, depth, rewrite), filling);
            self.results.push(filling);
            return;
        }
        if rewrite == Rewrite::Rename
            && let Maybe::Present(renamed) = self.renamed(node)
        {
            let _previous = self.memo.insert((node, depth, rewrite), renamed);
            self.results.push(renamed);
            return;
        }
        if let Node::Value(id) = node
            && let Some(&Value::Variable {
                zone: Zone::Intuitionistic,
                index,
            }) = self.arena.value(id)
        {
            match self.occurrence(id, index, depth, rewrite) {
                | Occurrence::Answered(rewritten) => {
                    let rewritten = self.wrapped(node, Node::Value(rewritten), rewrite);
                    let _previous = self.memo.insert((node, depth, rewrite), rewritten);
                    self.results.push(rewritten);
                },
                | Occurrence::Carried(replacement, under) => {
                    self.tasks.push(Task::Record(node, depth, rewrite));
                    self.tasks.push(Task::Open(
                        Node::Value(replacement),
                        Binders::NONE,
                        Rewrite::Shift(under),
                    ));
                },
            }
            return;
        }
        self.tasks.push(Task::Close(node, depth, rewrite));
        self.push_children(node, depth, rewrite);
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
            | Node::Value(id) => {
                if let Some(&Value::Constant(constant)) = self.arena.value(id)
                    && let Some(&target) = self.renaming.constants.get(&constant)
                {
                    return Maybe::Present(Node::Value(self.arena.value_constant(target)));
                }
            },
            | Node::ValueType(id) => {
                if let Some(&ValueType::Abstract(atom)) = self.arena.value_type(id)
                    && let Some(&target) = self.renaming.atoms.get(&atom)
                {
                    return Maybe::Present(Node::ValueType(target));
                }
            },
            | Node::Computation(_) | Node::CompType(_) => {},
        }
        Maybe::Absent(renamed::Absent::Unnamed)
    }

    /// The mark a wrap puts around `node`'s rewritten form, if its sites name
    /// it, or the thunk an elaboration suspends a nested computation into, if
    /// the checker decided it so.
    ///
    /// # Specification
    /// - requires: `rewritten` is `node`'s rewritten form, in its family.
    /// - ensures: under a wrap, a fresh mark over `rewritten` when the sites
    ///   name `node` and it is a term; under an elaboration, a fresh thunk over
    ///   the computation of `rewritten` when `node` is a nested computation the
    ///   checker decided to suspend; `rewritten` itself otherwise.
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
            && self.nesting.get(&held) == Some(&Nesting::Thunk)
            && let Some(&Value::Nested(suspended)) = self.arena.value(id)
        {
            return Node::Value(self.arena.value_thunk(suspended));
        }
        if rewrite != Rewrite::Wrap {
            return rewritten;
        }
        let Some(&mark) = self.sites.get(&node)
        else {
            return rewritten;
        };
        match rewritten {
            | Node::Value(id) => Node::Value(self.arena.value_mark(mark, id)),
            | Node::Computation(id) => Node::Computation(self.arena.computation_mark(mark, id)),
            | Node::ValueType(_) | Node::CompType(_) => rewritten,
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
            | Rewrite::Elaborate => Maybe::Present(node),
            | Rewrite::Splice(_) => {
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
            | Rewrite::Shift(_)
            | Rewrite::Substitute(_)
            | Rewrite::Lower
            | Rewrite::Fill(..)
            | Rewrite::Wrap
            | Rewrite::Environment
            | Rewrite::Rename => Maybe::Absent(()),
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
                Rewrite::Shift(Binders::ONE.deeper_by(ComponentCount::from(before))),
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
    /// **This is the only place the binding rewrites differ.** A shift and a
    /// splice raise an index at or past the depth and spare one inside it; a
    /// substitution spares an index inside the depth, replaces the one the
    /// depth names and lowers every one past it; a lowering does the same with
    /// no replacement, recording that the named index occurred; an environment
    /// substitution replaces every index past the depth by the entry it counts
    /// to, and lowers one past the environment by its length. A fill, a wrap,
    /// an elaboration and a renaming leave every occurrence as it stands.
    ///
    /// # Specification
    /// - requires: `depth` is the number of binders crossed to reach the
    ///   occurrence `id` at `index`.
    /// - ensures: the rule above; a substitution's replacement at a positive
    ///   depth is answered as a carry, to be shifted by the depth.
    /// - provides: the whole variable rule of the rewrites.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — indices below, at and above depths zero and one
    ///   separate all three binding rewrite rules; a zero shift, a saturating
    ///   shift and an open replacement distinguish identity, clamping and
    ///   capture avoidance. An environment of two entries read at depths zero
    ///   and one separates an inner index, each entry and an index past the
    ///   environment.
    /// - witness: `rewrite::tests::occurrence_rules_separate_depth_boundaries`
    /// - witness: `rewrite::tests::an_environment_substitution_replaces_every_free_index`
    #[spec(
        captures: mentioned = self.mention,
        ensures: |ret| match rewrite {
            | Rewrite::Shift(amount) | Rewrite::Splice(amount) => self.mention == mentioned && if u32::from(index) < depth.0 || amount == Binders::NONE {
                ret == Occurrence::Answered(id)
            } else {
                matches!(ret, Occurrence::Answered(answer) if matches!(self.arena.value(answer),
                    Some(Value::Variable { zone: Zone::Intuitionistic, index: actual })
                        if u32::from(*actual) == u32::from(index).saturating_add(amount.0)))
            },
            | Rewrite::Substitute(replacement) => self.mention == mentioned && match u32::from(index).cmp(&depth.0) {
                | core::cmp::Ordering::Less => ret == Occurrence::Answered(id),
                | core::cmp::Ordering::Equal => if depth == Binders::NONE {
                    ret == Occurrence::Answered(replacement)
                } else { ret == Occurrence::Carried(replacement, depth) },
                | core::cmp::Ordering::Greater => matches!(ret, Occurrence::Answered(answer)
                    if matches!(self.arena.value(answer), Some(Value::Variable { zone: Zone::Intuitionistic, index: actual })
                        if u32::from(*actual).checked_add(1) == Some(u32::from(index)))),
            },
            | Rewrite::Lower => match u32::from(index).cmp(&depth.0) {
                | core::cmp::Ordering::Less => ret == Occurrence::Answered(id) && self.mention == mentioned,
                | core::cmp::Ordering::Equal => ret == Occurrence::Answered(id) && self.mention == Mention::Present,
                | core::cmp::Ordering::Greater => self.mention == mentioned
                    && matches!(ret, Occurrence::Answered(answer) if matches!(self.arena.value(answer),
                        Some(Value::Variable { zone: Zone::Intuitionistic, index: actual })
                            if u32::from(*actual).checked_add(1) == Some(u32::from(index)))),
            },
            | Rewrite::Fill(..) | Rewrite::Wrap | Rewrite::Elaborate | Rewrite::Rename => {
                self.mention == mentioned && ret == Occurrence::Answered(id)
            },
            | Rewrite::Environment => self.mention == mentioned
                && (u32::from(index) >= depth.0 || ret == Occurrence::Answered(id)),
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
            | Rewrite::Shift(amount) | Rewrite::Splice(amount) => {
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
            | Rewrite::Substitute(replacement) => match position.cmp(&depth) {
                | core::cmp::Ordering::Less => Occurrence::Answered(id),
                | core::cmp::Ordering::Equal if depth == Binders::NONE => {
                    Occurrence::Answered(replacement)
                },
                | core::cmp::Ordering::Equal => Occurrence::Carried(replacement, depth),
                | core::cmp::Ordering::Greater => Occurrence::Answered(self.lowered(position)),
            },
            | Rewrite::Lower => match position.cmp(&depth) {
                | core::cmp::Ordering::Less => Occurrence::Answered(id),
                | core::cmp::Ordering::Equal => {
                    self.mention = Mention::Present;
                    Occurrence::Answered(id)
                },
                | core::cmp::Ordering::Greater => Occurrence::Answered(self.lowered(position)),
            },
            | Rewrite::Fill(..) | Rewrite::Wrap | Rewrite::Elaborate | Rewrite::Rename => {
                Occurrence::Answered(id)
            },
            | Rewrite::Environment => {
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
                    | Some(replacement) if depth == Binders::NONE => {
                        Occurrence::Answered(replacement)
                    },
                    | Some(replacement) => Occurrence::Carried(replacement, depth),
                    | None => {
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
    /// - provides: the lowering half of substitution and strengthening.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — lowering index one and an index above a crossed
    ///   binder distinguishes subtraction from identity and the wrong zone; the
    ///   occurrence matrix also preserves a previously recorded mention.
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
    ///   close in order, each at the depth its position sits at; a leaf and an
    ///   unreadable node push nothing.
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
Value::ListCons(..) | Value::StaticApplication(..) | Value::PathProduct(..) | Value::Funext(..) | Value::Equiv(..) | Value::Ua { .. } | Value::SessionRelated { .. } | Value::Then(..) | Value::FlowProduct(..) | Value::FunctionFlow(..) => 2,
Value::PathEquiv { .. } => 3,
Value::Injection(..) | Value::Thunk(_) | Value::Lift { .. } | Value::Quote(_) | Value::QuoteComputation(_) | Value::StaticLambda(_) | Value::PathRefl(_) | Value::Here(_) | Value::Stay(_) | Value::Forward(_) | Value::Returned(_) | Value::Nested(_) | Value::Run(_) | Value::Mark { .. } => 1,
}),
        | Node::Computation(id) => self.arena.computation(id).map_or(0_usize, |matched_native_node| match *matched_native_node {
Computation::Perform { ref signature, .. } => 1_usize.saturating_add(signature.types().count()),
Computation::Exercise { ref signature, .. } => 2_usize.saturating_add(signature.types().count()),
Computation::Handle { ref signature, ref clauses, .. } | Computation::Scope { ref signature, ref clauses, .. } => 2_usize.saturating_add(signature.types().count()).saturating_add(clauses.len()),
Computation::ListFold { .. } | Computation::TelescopeTransport { .. } => 5,
Computation::PathTransport { .. } | Computation::Ride { .. } | Computation::Split { motive: SplitMotive::Scrutinee(_), .. } => 3,
Computation::Primitive { ref arguments, .. } => arguments.len(),
Computation::DataCase { ref branches, .. } => branches.len().saturating_add(2),
Computation::Reset(_) | Computation::Shift(_) | Computation::Project(..) | Computation::RecordProjection(..) | Computation::TupleProjection(..) | Computation::Lambda(_) | Computation::Fixpoint { .. } | Computation::Return(_) | Computation::Force(_) | Computation::Mark { .. } => 1,
Computation::Resume(..) | Computation::With(..) | Computation::Application(..) | Computation::Bind(..) | Computation::Transport(..) | Computation::Split { motive: SplitMotive::Ambient, .. } => 2,
Computation::Case { ref branches, .. } => branches.len().saturating_add(1),
Computation::Hole(_) => 0_usize,
Computation::Session(ref action) => action.values().count().saturating_add(action.computations().count()).saturating_add(action.value_types().count()),
}),
        | Node::ValueType(id) => self.arena.value_type(id).map_or(0_usize, |matched_native_node| match *matched_native_node {
ValueType::Data { ref arguments, .. } => arguments.len(),
ValueType::Record(ref fields) => fields.len(),
ValueType::Product(ref components) | ValueType::Sum(ref components) => components.len(),
ValueType::Base(_) | ValueType::Universe { .. } | ValueType::Abstract(_) | ValueType::Unknown => 0_usize,
ValueType::Session(ref session) => session.payloads().len(),
ValueType::Capability { ref authority, .. } => authority.types().count(),
ValueType::Stack { .. } | ValueType::StaticPi { .. } | ValueType::Sigma { .. } | ValueType::PathUniverse(..) => 2,
ValueType::Path { .. } | ValueType::Flow { .. } => 3,
ValueType::List(_) | ValueType::Thunk(_) | ValueType::Lift { .. } | ValueType::Element { .. } | ValueType::Run(_) => 1,
}),
        | Node::CompType(id) => match self.arena.comp_type(id) {
            | None | Some(&CompType::Unknown) => 0_usize,
            | Some(&CompType::Returner { ref effects, .. }) => 1_usize.saturating_add(effects.types().count()),
            | Some(&CompType::Element { .. }) => 1,
            Some(&CompType::With(..) | &CompType::Arrow { .. } | &CompType::Pi { .. }) => 2,
        },
    }],
        ensures: self.results.len() == ready && pending.checked_add(children) == Some(self.tasks.len())
            && self.tasks.get(pending..).is_some_and(|tasks| tasks.iter().all(|task|
                matches!(task, Task::Open(_, at, step) if *step == rewrite && (*at == depth || *at == depth.deeper() || *at == depth.deeper().deeper() || Some(*at) == split)))),
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
            | Node::Value(id) => match self.arena.value(id) {
                | Some(&Value::Constructor {
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
                | Some(&Value::Record(ref fields)) => self.tasks.extend(
                    fields
                        .values()
                        .rev()
                        .map(|&field| open(Node::Value(field), depth)),
                ),
                | Some(&Value::Reify(ref frames)) => {
                    for frame in frames.iter().rev() {
                        match *frame {
                            | crate::control::StackFrame::Apply(value) => {
                                self.tasks.push(open(Node::Value(value), depth));
                            },
                            | crate::control::StackFrame::Bind(body) => self
                                .tasks
                                .push(open(Node::Computation(body), depth.deeper())),
                            | crate::control::StackFrame::Project(_) => {},
                        }
                    }
                },
                | Some(
                    &Value::Primitive { .. }
                    | &Value::Variable { .. }
                    | &Value::Constant(_)
                    | &Value::ListNil
                    | &Value::Literal(_)
                    | &Value::Hole(_),
                )
                | None => {},
                | Some(&Value::PathEquiv {
                    path_type,
                    forward,
                    backward,
                    ..
                }) => {
                    self.tasks.push(open(Node::Value(backward), depth));
                    self.tasks.push(open(Node::Value(forward), depth));
                    self.tasks.push(open(Node::ValueType(path_type), depth));
                },
                | Some(
                    &Value::PathRefl(body)
                    | &Value::Here(body)
                    | &Value::Injection(_, body)
                    | &Value::Stay(body)
                    | &Value::Forward(body)
                    | &Value::Lift { body, .. }
                    | &Value::Mark { body, .. },
                ) => self.tasks.push(open(Node::Value(body), depth)),
                | Some(
                    &(Value::Returned(computation)
                    | Value::Nested(computation)
                    | Value::Run(computation)),
                ) => {
                    self.tasks.push(open(Node::Computation(computation), depth));
                },
                | Some(
                    &Value::ListCons(first, second)
                    | &Value::PathProduct(first, second)
                    | &Value::Funext(first, second)
                    | &Value::Equiv(first, second)
                    | &Value::Then(first, second)
                    | &Value::FlowProduct(first, second)
                    | &Value::FunctionFlow(first, second)
                    | &Value::SessionRelated {
                        source: first,
                        target: second,
                        ..
                    }
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
                | Some(&Value::Tuple(ref components)) => self.tasks.extend(
                    components
                        .iter()
                        .rev()
                        .map(|&component| open(Node::Value(component), depth)),
                ),
                | Some(&Value::Recorded(ref moves)) => self.tasks.extend(
                    moves
                        .iter()
                        .rev()
                        .filter_map(|movement| match movement.payload() {
                            | quenchant_shape::shape::Maybe::Present(payload) => Some(payload),
                            | quenchant_shape::shape::Maybe::Absent(_) => None,
                        })
                        .map(|payload| open(Node::Value(payload), depth)),
                ),
                | Some(&Value::Thunk(body)) => {
                    self.tasks.push(open(Node::Computation(body), depth));
                },
                | Some(&Value::Quote(quoted)) => {
                    self.tasks.push(open(Node::ValueType(quoted), depth));
                },
                | Some(&Value::QuoteComputation(quoted)) => {
                    self.tasks.push(open(Node::CompType(quoted), depth));
                },
                | Some(&Value::StaticLambda(body)) => {
                    self.tasks.push(open(Node::Value(body), depth.deeper()));
                },
            },
            | Node::Computation(id) => match self.arena.computation(id) {
                | Some(&Computation::Perform {
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
                | Some(&Computation::Exercise {
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
                | Some(&Computation::Scope {
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
                | Some(&Computation::Handle {
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
                | Some(&Computation::Resume(stack, body)) => {
                    self.tasks.push(open(Node::Computation(body), depth));
                    self.tasks.push(open(Node::Value(stack), depth));
                },
                // A dependent split's motive binds the scrutinee; the body
                // binds every component.
                | Some(&Computation::Split {
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
                | Some(&Computation::With(first, second)) => {
                    self.tasks.push(open(Node::Computation(second), depth));
                    self.tasks.push(open(Node::Computation(first), depth));
                },
                | Some(
                    &(Computation::Reset(body)
                    | Computation::Project(_, body)
                    | Computation::Mark { body, .. }),
                ) => {
                    self.tasks.push(open(Node::Computation(body), depth));
                },
                | Some(&Computation::ListFold {
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
                | Some(&Computation::Primitive { ref arguments, .. }) => self.tasks.extend(
                    arguments
                        .iter()
                        .rev()
                        .map(|&argument| open(Node::Value(argument), depth)),
                ),
                | Some(&Computation::DataCase {
                    scrutinee,
                    motive,
                    ref branches,
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
                | Some(
                    &(Computation::RecordProjection(record, _)
                    | Computation::TupleProjection(record, _)),
                ) => {
                    self.tasks.push(open(Node::Value(record), depth));
                },
                | None | Some(&Computation::Hole(_)) => {},
                | Some(&Computation::Transport(path, value)) => {
                    self.tasks.push(open(Node::Value(value), depth));
                    self.tasks.push(open(Node::Value(path), depth));
                },
                | Some(&Computation::PathTransport {
                    motive,
                    path,
                    value,
                }) => {
                    self.tasks.push(open(Node::Value(value), depth));
                    self.tasks.push(open(Node::Value(path), depth));
                    self.tasks
                        .push(open(Node::ValueType(motive), depth.deeper()));
                },
                | Some(&Computation::Ride {
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
                | Some(&Computation::TelescopeTransport {
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
                | Some(
                    &(Computation::Lambda(body)
                    | Computation::Fixpoint { body, .. }
                    | Computation::Shift(body)),
                ) => self
                    .tasks
                    .push(open(Node::Computation(body), depth.deeper())),
                | Some(&Computation::Application(head, argument)) => {
                    self.tasks.push(open(Node::Value(argument), depth));
                    self.tasks.push(open(Node::Computation(head), depth));
                },
                | Some(&Computation::Return(value) | &Computation::Force(value)) => {
                    self.tasks.push(open(Node::Value(value), depth));
                },
                | Some(&Computation::Bind(bound, body)) => {
                    self.tasks
                        .push(open(Node::Computation(body), depth.deeper()));
                    self.tasks.push(open(Node::Computation(bound), depth));
                },
                | Some(&Computation::Case {
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
                // its child and parent stand at is the fork's own.
                | Some(&Computation::Session(ref action)) => {
                    self.tasks.extend(
                        action
                            .computations()
                            .rev()
                            .map(|child| open(Node::Computation(child), depth)),
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
            },
            | Node::ValueType(id) => match self.arena.value_type(id) {
                | Some(matched_native_node) => match *matched_native_node {
                    | ValueType::Stack { input, output } => {
                        self.tasks.push(open(Node::CompType(output), depth));
                        self.tasks.push(open(Node::CompType(input), depth));
                    },
                    | ValueType::List(element) => {
                        self.tasks.push(open(Node::ValueType(element), depth));
                    },
                    | ValueType::Data { ref arguments, .. } => self.tasks.extend(
                        arguments
                            .iter()
                            .rev()
                            .map(|&argument| open(Node::Value(argument), depth)),
                    ),
                    | ValueType::Record(ref fields) => self.tasks.extend(
                        fields
                            .values()
                            .rev()
                            .map(|&field| open(Node::ValueType(field), depth)),
                    ),
                    | ValueType::Product(ref components) | ValueType::Sum(ref components) => {
                        self.tasks.extend(
                            components
                                .iter()
                                .rev()
                                .map(|&component| open(Node::ValueType(component), depth)),
                        );
                    },
                    | ValueType::Base(_)
                    | ValueType::Universe { .. }
                    | ValueType::Abstract(_)
                    | ValueType::Unknown => {},
                    | ValueType::Capability { ref authority, .. } => self.tasks.extend(
                        authority
                            .types()
                            .rev()
                            .map(|ty| open(Node::ValueType(ty), depth)),
                    ),
                    | ValueType::StaticPi {
                        domain: first,
                        codomain: second,
                    } => {
                        self.tasks.push(open(Node::ValueType(second), depth));
                        self.tasks.push(open(Node::ValueType(first), depth));
                    },
                    | ValueType::Sigma { first, second } => {
                        self.tasks
                            .push(open(Node::ValueType(second), depth.deeper()));
                        self.tasks.push(open(Node::ValueType(first), depth));
                    },
                    | ValueType::PathUniverse(source, target) => {
                        self.tasks.push(open(Node::Value(target), depth));
                        self.tasks.push(open(Node::Value(source), depth));
                    },
                    | ValueType::Path {
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
                    | ValueType::Run(session) => {
                        self.tasks.push(open(Node::Value(session), depth));
                    },
                    | ValueType::Thunk(body) => {
                        self.tasks.push(open(Node::CompType(body), depth));
                    },
                    | ValueType::Lift { inner, .. } => {
                        self.tasks.push(open(Node::ValueType(inner), depth));
                    },
                    | ValueType::Element { code, .. } => {
                        self.tasks.push(open(Node::Value(code), depth));
                    },
                    | ValueType::Session(ref session) => self.tasks.extend(
                        session
                            .payloads()
                            .iter()
                            .rev()
                            .map(|&payload| open(Node::ValueType(payload), depth)),
                    ),
                },
                | None => {},
            },
            | Node::CompType(id) => match self.arena.comp_type(id) {
                | Some(&CompType::With(first, second)) => {
                    self.tasks.push(open(Node::CompType(second), depth));
                    self.tasks.push(open(Node::CompType(first), depth));
                },
                | None | Some(&CompType::Unknown) => {},
                | Some(&CompType::Returner {
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
                | Some(&CompType::Arrow { domain, codomain }) => {
                    self.tasks.push(open(Node::CompType(codomain), depth));
                    self.tasks.push(open(Node::ValueType(domain), depth));
                },
                | Some(&CompType::Pi { domain, codomain }) => {
                    self.tasks
                        .push(open(Node::CompType(codomain), depth.deeper()));
                    self.tasks.push(open(Node::ValueType(domain), depth));
                },
                | Some(&CompType::Element { code, .. }) => {
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
            | Node::Value(id) => id,
            | Node::Computation(_) | Node::ValueType(_) | Node::CompType(_) => original,
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
            | Node::Computation(id) => id,
            | Node::Value(_) | Node::ValueType(_) | Node::CompType(_) => original,
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
            | Node::ValueType(id) => id,
            | Node::Value(_) | Node::Computation(_) | Node::CompType(_) => original,
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
            | Node::CompType(id) => id,
            | Node::Value(_) | Node::Computation(_) | Node::ValueType(_) => original,
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
            | Node::Value(id) => Node::Value(self.close_value(id)),
            | Node::Computation(id) => Node::Computation(self.close_computation(id)),
            | Node::ValueType(id) => Node::ValueType(self.close_value_type(id)),
            | Node::CompType(id) => Node::CompType(self.close_comp_type(id)),
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
            | Ok(signature) => signature,
            | Err(never) => match never {},
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
    #[spec(
        captures: [ready = self.results.len(), children = self.arena.value(id).map_or(0_usize, |matched_native_node| match *matched_native_node {
Value::Reify(ref frames) => frames.iter().filter(|frame| !matches!(frame, crate::control::StackFrame::Project(_))).count(),
Value::Constructor { ref fields, .. } => fields.len().saturating_add(1),
Value::Record(ref fields) => fields.len(),
Value::Tuple(ref components) => components.len(),
Value::Recorded(ref moves) => moves.iter().filter(|movement| matches!(movement.payload(), quenchant_shape::shape::Maybe::Present(_))).count(),
Value::ListNil | Value::Primitive { .. } | Value::Variable { .. } | Value::Constant(_) | Value::Literal(_) | Value::Hole(_) => 0_usize,
Value::ListCons(..) | Value::StaticApplication(..) | Value::PathProduct(..) | Value::Funext(..) | Value::Equiv(..) | Value::Ua { .. } | Value::SessionRelated { .. } | Value::Then(..) | Value::FlowProduct(..) | Value::FunctionFlow(..) => 2,
Value::PathEquiv { .. } => 3,
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
            | Value::Constructor {
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
            | Value::Record(ref fields) => {
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
                    | Some(fields) => self.arena.value_record(fields),
                    | None => id,
                }
            },
            | Value::Reify(ref frames) => {
                let mut rewritten_frames = None;
                for (index, original) in frames.iter().copied().enumerate().rev() {
                    let rewritten = match original {
                        | crate::control::StackFrame::Apply(value) => {
                            crate::control::StackFrame::Apply(Self::value(&mut self.results, value))
                        },
                        | crate::control::StackFrame::Bind(body) => {
                            crate::control::StackFrame::Bind(Self::computation(
                                &mut self.results,
                                body,
                            ))
                        },
                        | crate::control::StackFrame::Project(side) => {
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
                    | Some(frames) => self.arena.value_reify(frames),
                    | None => id,
                }
            },
            | Value::PathRefl(code) => {
                let rewritten = Self::value(&mut self.results, code);
                if rewritten == code {
                    id
                }
                else {
                    self.arena.value_path_refl(rewritten)
                }
            },
            | Value::Here(point) => {
                let rewritten = Self::value(&mut self.results, point);
                if rewritten == point {
                    id
                }
                else {
                    self.arena.value_here(rewritten)
                }
            },
            | Value::Returned(computation) => {
                let rewritten = Self::computation(&mut self.results, computation);
                if rewritten == computation {
                    id
                }
                else {
                    self.arena.value_returned(rewritten)
                }
            },
            | Value::Nested(computation) => {
                let rewritten = Self::computation(&mut self.results, computation);
                if rewritten == computation {
                    id
                }
                else {
                    self.arena.value_nested(rewritten)
                }
            },
            | Value::Run(computation) => {
                let rewritten = Self::computation(&mut self.results, computation);
                if rewritten == computation {
                    id
                }
                else {
                    self.arena.value_run(rewritten)
                }
            },
            | Value::PathProduct(first, second) => {
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
            | Value::Funext(left, right) => {
                let rewritten_right = Self::value(&mut self.results, right);
                let rewritten_left = Self::value(&mut self.results, left);
                if (rewritten_left, rewritten_right) == (left, right) {
                    id
                }
                else {
                    self.arena.value_funext(rewritten_left, rewritten_right)
                }
            },
            | Value::Equiv(forward, backward) => {
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
            | Value::SessionRelated {
                relation,
                source,
                target,
            } => {
                let rewritten_target = Self::value(&mut self.results, target);
                let rewritten_source = Self::value(&mut self.results, source);
                if (rewritten_source, rewritten_target) == (source, target) {
                    id
                }
                else {
                    self.arena
                        .value_session_related(relation, rewritten_source, rewritten_target)
                }
            },
            | Value::Stay(point) => {
                let rewritten = Self::value(&mut self.results, point);
                if rewritten == point {
                    id
                }
                else {
                    self.arena.value_stay(rewritten)
                }
            },
            | Value::Then(first, second) => {
                let rewritten_second = Self::value(&mut self.results, second);
                let rewritten_first = Self::value(&mut self.results, first);
                if (rewritten_first, rewritten_second) == (first, second) {
                    id
                }
                else {
                    self.arena.value_then(rewritten_first, rewritten_second)
                }
            },
            | Value::FlowProduct(first, second) => {
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
            | Value::Forward(translator) => {
                let rewritten = Self::value(&mut self.results, translator);
                if rewritten == translator {
                    id
                }
                else {
                    self.arena.value_forward(rewritten)
                }
            },
            | Value::FunctionFlow(domain, codomain) => {
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
            | Value::Recorded(ref moves) => {
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
                    | Some(moves) => self.arena.value_recorded(alloc::sync::Arc::from(moves)),
                    | None => id,
                }
            },
            | Value::Ua {
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
            | Value::PathEquiv {
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
            | Value::Primitive { .. }
            | Value::Variable { .. }
            | Value::Constant(_)
            | Value::ListNil
            | Value::Literal(_)
            | Value::Hole(_) => id,
            | Value::Mark { mark, body } => {
                let rewritten = Self::value(&mut self.results, body);
                if rewritten == body {
                    id
                }
                else {
                    self.arena.value_mark(mark, rewritten)
                }
            },
            | Value::Tuple(ref components) => {
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
                    | Some(components) => self.arena.value_tuple(&components),
                    | None => id,
                }
            },
            | Value::ListCons(head, tail) => {
                let new_tail = Self::value(&mut self.results, tail);
                let new_head = Self::value(&mut self.results, head);
                if (new_head, new_tail) == (head, tail) {
                    id
                }
                else {
                    self.arena.value_list_cons(new_head, new_tail)
                }
            },
            | Value::Injection(summand, body) => {
                let rewritten = Self::value(&mut self.results, body);
                if rewritten == body {
                    id
                }
                else {
                    self.arena.value_injection(summand, rewritten)
                }
            },
            | Value::Thunk(body) => {
                let rewritten = Self::computation(&mut self.results, body);
                if rewritten == body {
                    id
                }
                else {
                    self.arena.value_thunk(rewritten)
                }
            },
            | Value::Lift { ref target, body } => {
                let rewritten = Self::value(&mut self.results, body);
                if rewritten == body {
                    id
                }
                else {
                    self.arena.value_lift(target.clone(), rewritten)
                }
            },
            | Value::Quote(quoted) => {
                let rewritten = Self::value_type(&mut self.results, quoted);
                if rewritten == quoted {
                    id
                }
                else {
                    self.arena.value_quote(rewritten)
                }
            },
            | Value::QuoteComputation(quoted) => {
                let rewritten = Self::comp_type(&mut self.results, quoted);
                if rewritten == quoted {
                    id
                }
                else {
                    self.arena.value_quote_computation(rewritten)
                }
            },
            | Value::StaticLambda(body) => {
                let rewritten = Self::value(&mut self.results, body);
                if rewritten == body {
                    id
                }
                else {
                    self.arena.value_static_lambda(rewritten)
                }
            },
            | Value::StaticApplication(head, argument) => {
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
    #[spec(
        captures: [ready = self.results.len(), children = self.arena.computation(id).map_or(0_usize, |matched_native_node| match *matched_native_node {
Computation::Perform { ref signature, .. } => 1_usize.saturating_add(signature.types().count()),
Computation::Exercise { ref signature, .. } => 2_usize.saturating_add(signature.types().count()),
Computation::Handle { ref signature, ref clauses, .. } | Computation::Scope { ref signature, ref clauses, .. } => 2_usize.saturating_add(signature.types().count()).saturating_add(clauses.len()),
Computation::ListFold { .. } | Computation::TelescopeTransport { .. } => 5,
Computation::PathTransport { .. } | Computation::Ride { .. } | Computation::Split { motive: SplitMotive::Scrutinee(_), .. } => 3,
Computation::Primitive { ref arguments, .. } => arguments.len(),
Computation::DataCase { ref branches, .. } => branches.len().saturating_add(2),
Computation::Reset(_) | Computation::Shift(_) | Computation::Project(..) | Computation::RecordProjection(..) | Computation::TupleProjection(..) | Computation::Lambda(_) | Computation::Fixpoint { .. } | Computation::Return(_) | Computation::Force(_) | Computation::Mark { .. } => 1,
Computation::Resume(..) | Computation::With(..) | Computation::Application(..) | Computation::Bind(..) | Computation::Transport(..) | Computation::Split { motive: SplitMotive::Ambient, .. } => 2,
Computation::Case { ref branches, .. } => branches.len().saturating_add(1),
Computation::Hole(_) => 0_usize,
Computation::Session(ref action) => action.values().count().saturating_add(action.computations().count()).saturating_add(action.value_types().count()),
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
            | Computation::Perform {
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
            | Computation::Exercise {
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
            | Computation::Scope {
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
            | Computation::Handle {
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
            | Computation::Resume(stack, body) => {
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
            | Computation::Split {
                scrutinee,
                arity,
                motive,
                body,
            } => {
                let rewritten_body = Self::computation(&mut self.results, body);
                let rewritten_motive = match motive {
                    | SplitMotive::Ambient => SplitMotive::Ambient,
                    | SplitMotive::Scrutinee(motive) => {
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
                        | SplitMotive::Ambient => {
                            self.arena
                                .computation_split(rewritten_scrutinee, arity, rewritten_body)
                        },
                        | SplitMotive::Scrutinee(motive) => self.arena.computation_dependent_split(
                            rewritten_scrutinee,
                            arity,
                            motive,
                            rewritten_body,
                        ),
                    }
                }
            },
            | Computation::With(first, second) => {
                let rewritten_second = Self::computation(&mut self.results, second);
                let rewritten_first = Self::computation(&mut self.results, first);
                if (rewritten_first, rewritten_second) == (first, second) {
                    id
                }
                else {
                    self.arena
                        .computation_with(rewritten_first, rewritten_second)
                }
            },
            | Computation::Reset(body) => {
                let rewritten = Self::computation(&mut self.results, body);
                if rewritten == body {
                    id
                }
                else {
                    self.arena.computation_reset(rewritten)
                }
            },
            | Computation::Shift(body) => {
                let rewritten = Self::computation(&mut self.results, body);
                if rewritten == body {
                    id
                }
                else {
                    self.arena.computation_shift(rewritten)
                }
            },
            | Computation::Project(side, body) => {
                let rewritten = Self::computation(&mut self.results, body);
                if rewritten == body {
                    id
                }
                else {
                    self.arena.computation_project(side, rewritten)
                }
            },
            | Computation::ListFold {
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
            | Computation::Primitive {
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
            | Computation::DataCase {
                scrutinee,
                motive,
                ref branches,
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
                    self.arena.computation_data_case(
                        rewritten_scrutinee,
                        rewritten_motive,
                        changed.unwrap_or_else(|| branches.clone()),
                    )
                }
            },
            | Computation::RecordProjection(record, ref label) => {
                let rewritten = Self::value(&mut self.results, record);
                if rewritten == record {
                    id
                }
                else {
                    self.arena
                        .computation_record_projection(rewritten, label.clone())
                }
            },
            | Computation::TupleProjection(tuple, component) => {
                let rewritten = Self::value(&mut self.results, tuple);
                if rewritten == tuple {
                    id
                }
                else {
                    self.arena
                        .computation_tuple_projection(rewritten, component)
                }
            },
            | Computation::Transport(path, value) => {
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
            | Computation::PathTransport {
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
            | Computation::Ride {
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
            | Computation::TelescopeTransport {
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
            | Computation::Lambda(body) => {
                let rewritten = Self::computation(&mut self.results, body);
                if rewritten == body {
                    id
                }
                else {
                    self.arena.computation_lambda(rewritten)
                }
            },
            | Computation::Fixpoint { body, evidence } => {
                let rewritten = Self::computation(&mut self.results, body);
                if rewritten == body {
                    id
                }
                else {
                    self.arena.computation_fixpoint(rewritten, evidence)
                }
            },
            | Computation::Application(head, argument) => {
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
            | Computation::Return(value) => {
                let rewritten = Self::value(&mut self.results, value);
                if rewritten == value {
                    id
                }
                else {
                    self.arena.computation_return(rewritten)
                }
            },
            | Computation::Force(value) => {
                let rewritten = Self::value(&mut self.results, value);
                if rewritten == value {
                    id
                }
                else {
                    self.arena.computation_force(rewritten)
                }
            },
            | Computation::Bind(bound, body) => {
                let rewritten_body = Self::computation(&mut self.results, body);
                let rewritten_bound = Self::computation(&mut self.results, bound);
                if (rewritten_bound, rewritten_body) == (bound, body) {
                    id
                }
                else {
                    self.arena.computation_bind(rewritten_bound, rewritten_body)
                }
            },
            | Computation::Case {
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
                else {
                    match changed {
                        | Some(branches) => {
                            self.arena.computation_case(rewritten_scrutinee, &branches)
                        },
                        | None => {
                            let branches = branches.to_vec();
                            self.arena.computation_case(rewritten_scrutinee, &branches)
                        },
                    }
                }
            },
            | Computation::Hole(_) => id,
            | Computation::Mark { mark, body } => {
                let rewritten = Self::computation(&mut self.results, body);
                if rewritten == body {
                    id
                }
                else {
                    self.arena.computation_mark(mark, rewritten)
                }
            },
            | Computation::Session(ref action) => {
                let rewritten = match action.try_map(
                    crate::session::ChildOrder::Reverse,
                    &mut self.results,
                    |results, value| {
                        Ok::<_, core::convert::Infallible>(Self::value(results, value))
                    },
                    |results, computation| Ok(Self::computation(results, computation)),
                    |results, ty| Ok(Self::value_type(results, ty)),
                ) {
                    | Ok(rewritten) => rewritten,
                    | Err(never) => match never {},
                };
                if rewritten == *action {
                    id
                }
                else {
                    self.arena.computation_session(rewritten)
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
    #[spec(
        captures: [ready = self.results.len(), children = self.arena.value_type(id).map_or(0_usize, |matched_native_node| match *matched_native_node {
ValueType::Data { ref arguments, .. } => arguments.len(),
ValueType::Record(ref fields) => fields.len(),
ValueType::Product(ref components) | ValueType::Sum(ref components) => components.len(),
ValueType::Base(_) | ValueType::Universe { .. } | ValueType::Abstract(_) | ValueType::Unknown => 0_usize,
ValueType::Session(ref session) => session.payloads().len(),
ValueType::Capability { ref authority, .. } => authority.types().count(),
ValueType::Stack { .. } | ValueType::StaticPi { .. } | ValueType::Sigma { .. } | ValueType::PathUniverse(..) => 2,
ValueType::Path { .. } | ValueType::Flow { .. } => 3,
ValueType::List(_) | ValueType::Thunk(_) | ValueType::Lift { .. } | ValueType::Element { .. } | ValueType::Run(_) => 1,
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
            | ValueType::Data {
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
                    | Some(arguments) => self.arena.value_type_data(declaration, arguments),
                    | None => id,
                }
            },
            | ValueType::Record(ref fields) => {
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
                    | Some(fields) => self.arena.value_type_record(fields),
                    | None => id,
                }
            },
            | ValueType::Stack { input, output } => {
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
            | ValueType::List(element) => {
                let rewritten = Self::value_type(&mut self.results, element);
                if rewritten == element {
                    id
                }
                else {
                    self.arena.value_type_list(rewritten)
                }
            },
            | ValueType::PathUniverse(source, target) => {
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
            | ValueType::Path {
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
            | ValueType::Flow {
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
            | ValueType::Run(session) => {
                let rewritten = Self::value(&mut self.results, session);
                if rewritten == session {
                    id
                }
                else {
                    self.arena.value_type_run(rewritten)
                }
            },
            | ValueType::Base(_)
            | ValueType::Universe { .. }
            | ValueType::Abstract(_)
            | ValueType::Unknown => id,
            | ValueType::Capability {
                ref authority,
                grade,
                region,
            } => {
                let rewritten =
                    match authority.try_map_types(crate::effect::TypeOrder::Reverse, |ty| {
                        Ok::<_, core::convert::Infallible>(Self::value_type(&mut self.results, ty))
                    }) {
                        | Ok(row) => row,
                        | Err(never) => match never {},
                    };
                if rewritten == *authority {
                    id
                }
                else {
                    self.arena.value_type_capability(rewritten, grade, region)
                }
            },
            | ValueType::Product(ref components) | ValueType::Sum(ref components) => {
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
                    | Some(components) if product => self.arena.value_type_product(&components),
                    | Some(summands) => self.arena.value_type_sum(&summands),
                    | None => id,
                }
            },
            | ValueType::Thunk(body) => {
                let rewritten = Self::comp_type(&mut self.results, body);
                if rewritten == body {
                    id
                }
                else {
                    self.arena.value_type_thunk(rewritten)
                }
            },
            | ValueType::Lift { inner, ref target } => {
                let rewritten = Self::value_type(&mut self.results, inner);
                if rewritten == inner {
                    id
                }
                else {
                    self.arena.value_type_lift(rewritten, target.clone())
                }
            },
            | ValueType::Element { code, ref target } => {
                let rewritten = Self::value(&mut self.results, code);
                if rewritten == code {
                    id
                }
                else {
                    self.arena.value_type_element(rewritten, target.clone())
                }
            },
            | ValueType::StaticPi { domain, codomain } => {
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
            | ValueType::Sigma { first, second } => {
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
            | ValueType::Session(ref session) => {
                let rewritten =
                    match session.try_map_payloads(crate::session::ChildOrder::Reverse, |payload| {
                        Ok::<_, core::convert::Infallible>(Self::value_type(
                            &mut self.results,
                            payload,
                        ))
                    }) {
                        | Ok(rewritten) => rewritten,
                        | Err(never) => match never {},
                    };
                if rewritten == *session {
                    id
                }
                else {
                    self.arena.value_type_session(rewritten)
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
    #[spec(
        captures: [ready = self.results.len(), children = match self.arena.comp_type(id) {
            | None | Some(&CompType::Unknown) => 0_usize,
            | Some(&CompType::Returner { ref effects, .. }) => 1_usize.saturating_add(effects.types().count()),
            | Some(&CompType::Element { .. }) => 1,
            Some(&CompType::With(..) | &CompType::Arrow { .. } | &CompType::Pi { .. }) => 2,
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
            | CompType::With(first, second) => {
                let rewritten_second = Self::comp_type(&mut self.results, second);
                let rewritten_first = Self::comp_type(&mut self.results, first);
                if (rewritten_first, rewritten_second) == (first, second) {
                    id
                }
                else {
                    self.arena.comp_type_with(rewritten_first, rewritten_second)
                }
            },
            | CompType::Returner {
                result,
                ref effects,
            } => {
                let rewritten_effects =
                    match effects.try_map_types(crate::effect::TypeOrder::Reverse, |ty| {
                        Ok::<_, core::convert::Infallible>(Self::value_type(&mut self.results, ty))
                    }) {
                        | Ok(row) => row,
                        | Err(never) => match never {},
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
            | CompType::Arrow { domain, codomain } => {
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
            | CompType::Pi { domain, codomain } => {
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
            | CompType::Element { code, ref target } => {
                let rewritten = Self::value(&mut self.results, code);
                if rewritten == code {
                    id
                }
                else {
                    self.arena.comp_type_element(rewritten, target.clone())
                }
            },
            | CompType::Unknown => id,
        }
    }
}

/// Shift a value type `amount` binders deeper: every free intuitionistic index
/// rises by `amount`.
///
/// # Specification
/// - requires: `subject` names a value type of `arena`, formed in some context
///   `Γ`.
/// - ensures: the same type read in `Γ` extended by `amount` further binders;
///   `subject` itself when it is closed or `amount` is zero, so a closed type
///   costs no minting.
/// - provides: the read of a context slot's type at an occurrence.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — 600 deterministic bounded codomains agree with a
///   capture-free level-based reference under open substitution, with L3
///   free/bound index boundaries and closed-type identity.
/// - witness: `rewrite::tests::instantiating_a_codomain_avoids_capture`
/// - witness: `rewrite::tests::shifting_raises_free_indices_and_spares_bound_ones`
#[spec(captures: entry = arena.watermark(),
    ensures: |ret| (amount != Binders::NONE || (ret == subject && arena.watermark() == entry))
        && (ret == subject || arena.value_type(ret).is_some()))]
#[inline]
#[must_use]
pub fn shift_value_type(
    arena: &mut CoreArena,
    subject: ValueTypeId,
    amount: Binders,
) -> ValueTypeId
{
    if amount == Binders::NONE {
        return subject;
    }
    match Engine::new(arena).run(
        Node::ValueType(subject),
        Binders::NONE,
        Rewrite::Shift(amount),
    ) {
        | Node::ValueType(id) => id,
        | Node::Value(_) | Node::Computation(_) | Node::CompType(_) => subject,
    }
}

/// Shift a computation type `amount` binders deeper.
///
/// # Specification
/// - requires: `subject` names a computation type of `arena`, formed in some
///   context `Γ`.
/// - ensures: the same type read in `Γ` extended by `amount` further binders;
///   `subject` itself when it is closed or `amount` is zero.
/// - provides: the expected type a binder's body is checked against when the
///   binder does not scope the type.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — free and bound indices separated within one subject.
/// - witness: `rewrite::tests::shifting_raises_free_indices_and_spares_bound_ones`
#[spec(captures: entry = arena.watermark(),
    ensures: |ret| (amount != Binders::NONE || (ret == subject && arena.watermark() == entry))
        && (ret == subject || arena.comp_type(ret).is_some()))]
#[inline]
#[must_use]
pub fn shift_comp_type(
    arena: &mut CoreArena,
    subject: CompTypeId,
    amount: Binders,
) -> CompTypeId
{
    if amount == Binders::NONE {
        return subject;
    }
    match Engine::new(arena).run(
        Node::CompType(subject),
        Binders::NONE,
        Rewrite::Shift(amount),
    ) {
        | Node::CompType(id) => id,
        | Node::Value(_) | Node::Computation(_) | Node::ValueType(_) => subject,
    }
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
        | Node::CompType(id) => id,
        | Node::Value(_) | Node::Computation(_) | Node::ValueType(_) => codomain,
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
        | Node::Value(id) => id,
        | Node::Computation(_) | Node::ValueType(_) | Node::CompType(_) => body,
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
        | Node::ValueType(id) => id,
        | Node::Value(_) | Node::Computation(_) | Node::CompType(_) => body,
    }
}

/// Lower a computation type out from under its innermost binder.
///
/// # Specification
/// - requires: `subject` names a computation type of `arena` formed in some
///   context `Γ` extended by one binder.
/// - ensures: the same type in `Γ`, every index outside the binder lowered by
///   one, when no occurrence names the binder;
///   [`strengthening::Absent::MentionsBinder`] when one does.
/// - provides: the result type of a bind or a case, synthesized under the
///   binder its continuation introduces.
/// - fails: never; a mention is a named absence.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a type that mentions the binder and one that mentions
///   only an outer index separate the two answers.
/// - witness: `rewrite::tests::strengthening_refuses_a_mention_and_lowers_the_rest`
#[spec(ensures: |ret| match ret {
    | Maybe::Present(id) => id == subject || arena.comp_type(id).is_some(),
    | Maybe::Absent(strengthening::Absent::MentionsBinder) => true,
})]
#[inline]
pub fn strengthen_comp_type(
    arena: &mut CoreArena,
    subject: CompTypeId,
) -> Maybe<CompTypeId, strengthening::Absent>
{
    let mut engine = Engine::new(arena);
    let lowered = engine.run(Node::CompType(subject), Binders::NONE, Rewrite::Lower);
    match (engine.mention, lowered) {
        | (Mention::Present, _) => Maybe::Absent(strengthening::Absent::MentionsBinder),
        | (Mention::Absent, Node::CompType(id)) => Maybe::Present(id),
        | (Mention::Absent, Node::Value(_) | Node::Computation(_) | Node::ValueType(_)) => {
            Maybe::Present(subject)
        },
    }
}

/// Shift free value occurrences, preserving variables bound within the value.
///
/// # Specification
/// - requires: the subject is live in this arena.
/// - ensures: free intuitionistic indices rise by the amount; zero is identity.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — nominal arguments and record fields retain their ambient
///   scope.
/// - witness: `rewrite::tests::native_motives_preserve_binder_and_field_order`
#[spec(captures: entry = arena.watermark(), ensures: |ret| (amount != Binders::NONE || (ret == subject && arena.watermark() == entry)) && (ret == subject || arena.value(ret).is_some()))]
#[must_use]
#[inline]
pub fn shift_value(
    arena: &mut CoreArena,
    subject: ValueId,
    amount: Binders,
) -> ValueId
{
    if amount == Binders::NONE {
        return subject;
    }
    match Engine::new(arena).run(Node::Value(subject), Binders::NONE, Rewrite::Shift(amount)) {
        | Node::Value(id) => id,
        | Node::Computation(_) | Node::ValueType(_) | Node::CompType(_) => subject,
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
        | Node::ValueType(id) => id,
        | Node::Computation(_) | Node::Value(_) | Node::CompType(_) => subject,
    }
}

/// Shift a computation type while preserving a prefix of local binders.
///
/// # Specification
/// - requires: the subject is live; scope counts the local intuitionistic
///   binders.
/// - ensures: only indices outside that scope rise by the amount; zero is
///   identity.
/// - provides: insertion of constructor fields outside a case motive's
///   scrutinee binder.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a motive distinguishes its scrutinee binder from an
///   ambient index.
/// - witness: `rewrite::tests::native_motives_preserve_binder_and_field_order`
#[spec(captures: entry = arena.watermark(), ensures: |ret| (amount != Binders::NONE || (ret == subject && arena.watermark() == entry)) && (ret == subject || arena.comp_type(ret).is_some()))]
#[must_use]
#[inline]
pub fn shift_comp_type_under(
    arena: &mut CoreArena,
    subject: CompTypeId,
    scope: Binders,
    amount: Binders,
) -> CompTypeId
{
    if amount == Binders::NONE {
        return subject;
    }
    match Engine::new(arena).run(Node::CompType(subject), scope, Rewrite::Shift(amount)) {
        | Node::CompType(id) => id,
        | Node::Computation(_) | Node::ValueType(_) | Node::Value(_) => subject,
    }
}

/// Shift a value type while preserving a prefix of local binders.
///
/// # Specification
/// - requires: the subject is live; scope counts the local intuitionistic
///   binders.
/// - ensures: only indices outside that scope rise by the amount; zero is
///   identity.
/// - provides: a family under its own binder carried under one binder more, as
///   the identity at a dependent pair carries its second factor under the first
///   coordinate's path.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a family keeps its own binder and lifts an ambient index.
/// - witness: `rewrite::tests::a_value_type_under_its_binder_lifts_only_the_ambient_index`
#[spec(captures: entry = arena.watermark(), ensures: |ret| (amount != Binders::NONE || (ret == subject && arena.watermark() == entry)) && (ret == subject || arena.value_type(ret).is_some()))]
#[must_use]
#[inline]
pub fn shift_value_type_under(
    arena: &mut CoreArena,
    subject: ValueTypeId,
    scope: Binders,
    amount: Binders,
) -> ValueTypeId
{
    if amount == Binders::NONE {
        return subject;
    }
    match Engine::new(arena).run(Node::ValueType(subject), scope, Rewrite::Shift(amount)) {
        | Node::ValueType(id) => id,
        | Node::Computation(_) | Node::CompType(_) | Node::Value(_) => subject,
    }
}

/// The engine node a term id names.
///
/// # Specification
/// trivial.
const fn term_node(term: TermId) -> Node
{
    match term {
        | TermId::Value(id) => Node::Value(id),
        | TermId::Computation(id) => Node::Computation(id),
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
        | (Node::Value(id), TermId::Value(_)) => TermId::Value(id),
        | (Node::Computation(id), TermId::Computation(_)) => TermId::Computation(id),
        | (Node::Value(_) | Node::Computation(_) | Node::ValueType(_) | Node::CompType(_), _) => {
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

/// How the checker decided a computation written where a value is read.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Nesting
{
    /// Expected at a thunk type, it is suspended, as a written thunk is.
    Thunk,
    /// Expected at any other type, it runs before its region and stands for
    /// the value it returns.
    Run,
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
///   boundaries and the refusal.
/// - witness: `rewrite::tests::an_elaboration_never_hoists_out_of_a_thunk_or_an_arm`
/// - witness: `rewrite::tests::a_run_in_no_computation_is_unenclosed`
/// - witness: `rewrite::tests::a_decision_no_term_reaches_is_unenclosed`
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
            | Position::Value(id, region) => {
                let Some(value) = arena.value(id)
                else {
                    continue;
                };
                if matches!(*value, Value::Nested(_) | Value::Run(_)) {
                    let _first = met.insert(id);
                }
                survey_value(value, id, region, nesting, &mut regions, &mut pending)?;
            },
            | Position::Computation(id, spine) => {
                let Some(computation) = arena.computation(id)
                else {
                    continue;
                };
                let region = Maybe::Present(match spine {
                    | Maybe::Present(region) => region,
                    | Maybe::Absent(()) => id,
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
        | Value::Nested(nested) | Value::Run(nested) => {
            if matches!(*value, Value::Run(_)) || nesting.get(&id) == Some(&Nesting::Run) {
                let Maybe::Present(enclosing) = region
                else {
                    return Err(Unenclosed { run: id });
                };
                regions.entry(enclosing).or_default().push((id, nested));
            }
            next.push(Position::Computation(nested, own));
        },
        | Value::Primitive { body, .. } | Value::Returned(body) | Value::Thunk(body) => {
            next.push(Position::Computation(body, own));
        },
        | Value::PathRefl(inner)
        | Value::Here(inner)
        | Value::Stay(inner)
        | Value::Forward(inner)
        | Value::Injection(_, inner)
        | Value::Lift { body: inner, .. }
        | Value::Mark { body: inner, .. } => next.push(Position::Value(inner, region)),
        | Value::PathProduct(left, right)
        | Value::Funext(left, right)
        | Value::Equiv(left, right)
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
        | Value::StaticLambda(body) => next.push(Position::Value(body, own)),
        | Value::StaticApplication(head, argument) => {
            next.extend([Position::Value(head, own), Position::Value(argument, own)]);
        },
        | Value::SessionRelated { source, target, .. } => {
            next.extend([Position::Value(source, own), Position::Value(target, own)]);
        },
        | Value::Recorded(ref moves) => {
            next.extend(
                moves
                    .iter()
                    .filter_map(|movement| match movement.payload() {
                        | Maybe::Present(payload) => Some(Position::Value(payload, region)),
                        | Maybe::Absent(_) => None,
                    }),
            );
        },
        | Value::Tuple(ref components) => next.extend(
            components
                .iter()
                .map(|&component| Position::Value(component, region)),
        ),
        | Value::Constructor { ref fields, .. } => {
            next.extend(fields.iter().map(|&field| Position::Value(field, region)));
        },
        | Value::Record(ref fields) => {
            next.extend(fields.values().map(|&field| Position::Value(field, region)));
        },
        | Value::Reify(ref frames) => {
            next.extend(frames.iter().filter_map(|frame| match *frame {
                | crate::control::StackFrame::Apply(argument) => {
                    Some(Position::Value(argument, region))
                },
                | crate::control::StackFrame::Bind(body) => Some(Position::Computation(body, own)),
                | crate::control::StackFrame::Project(_) => None,
            }));
        },
        | Value::Variable { .. }
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
        | Computation::Application(head, argument) => next.extend([
            Position::Computation(head, region),
            Position::Value(argument, region),
        ]),
        | Computation::Primitive { ref arguments, .. } => next.extend(
            arguments
                .iter()
                .map(|&argument| Position::Value(argument, region)),
        ),
        | Computation::Transport(path, value)
        | Computation::PathTransport { path, value, .. }
        | Computation::Ride {
            flow: path, value, ..
        } => {
            next.extend([
                Position::Value(path, region),
                Position::Value(value, region),
            ]);
        },
        | Computation::TelescopeTransport {
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
        | Computation::Return(value)
        | Computation::Force(value)
        | Computation::RecordProjection(value, _)
        | Computation::TupleProjection(value, _)
        | Computation::Perform { payload: value, .. } => next.push(Position::Value(value, region)),
        | Computation::Exercise {
            capability,
            payload,
            ..
        } => next.extend([
            Position::Value(capability, region),
            Position::Value(payload, region),
        ]),
        | Computation::Lambda(body)
        | Computation::Fixpoint { body, .. }
        | Computation::Reset(body)
        | Computation::Shift(body)
        | Computation::Project(_, body)
        | Computation::Mark { body, .. } => next.push(Position::Computation(body, own)),
        | Computation::Bind(first, second) | Computation::With(first, second) => {
            next.extend([
                Position::Computation(first, own),
                Position::Computation(second, own),
            ]);
        },
        | Computation::Case {
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
        | Computation::DataCase {
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
        | Computation::Split {
            scrutinee, body, ..
        } => next.extend([
            Position::Value(scrutinee, region),
            Position::Computation(body, own),
        ]),
        | Computation::ListFold {
            list,
            on_nil,
            on_cons,
            ..
        } => next.extend([
            Position::Value(list, region),
            Position::Computation(on_nil, own),
            Position::Computation(on_cons, own),
        ]),
        | Computation::Handle {
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
        | Computation::Resume(stack, body) => {
            next.extend([
                Position::Value(stack, region),
                Position::Computation(body, own),
            ]);
        },
        | Computation::Session(ref action) => {
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
        | Computation::Hole(_) => {},
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
        | Node::Value(id) => Ok(id),
        | Node::Computation(_) | Node::ValueType(_) | Node::CompType(_) => Ok(subject),
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

/// The constants and atoms one instantiation replaces: each constant by
/// another, each atom by a type.
///
/// # Specification
/// - requires: nothing to construct this data; a replacing type is a closed
///   type of the arena the renaming is applied in.
/// - ensures: a later entry for a name replaces an earlier one, so the renaming
///   is a function on constants and a function on atoms.
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
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Renaming
{
    /// Each constant replaced, with the constant replacing it.
    constants: BTreeMap<ConstantIndex, ConstantIndex>,
    /// Each atom replaced, with the type replacing it.
    atoms: BTreeMap<ConstantIndex, ValueTypeId>,
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
        | Node::Value(id) => id,
        | Node::Computation(_) | Node::ValueType(_) | Node::CompType(_) => subject,
    }
}

/// Rename the constants and atoms of the value type `subject` by `renaming`,
/// reporting every node it rewrote beside the node it rewrote it from.
///
/// # Specification
/// - requires: as [`rename_value_traced`].
/// - ensures: as [`rename_value_traced`], for a value type: an atom the
///   renaming names standing as the whole subject is the type it names for it.
/// - provides: instantiating a declared type, a kind or a representation.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`rename_value_traced`].
/// - witness: `rewrite::tests::a_renaming_replaces_exactly_the_named_constants_and_atoms`
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
        | Node::ValueType(id) => id,
        | Node::Value(_) | Node::Computation(_) | Node::CompType(_) => subject,
    }
}

/// Raise every free intuitionistic index of `subject` past its innermost
/// `scope` binders by `amount`, reporting every node it rewrote beside the
/// node it rewrote it from.
///
/// # Specification
/// - requires: `subject` is live in `arena`.
/// - ensures: `subject` with every free index counting past its innermost
///   `scope` binders raised by `amount` and every index below kept; `carried`
///   gains one pair per node the shift changed, as
///   [`substitute_environment_traced`] reports them; `subject` itself, nothing
///   minted and nothing reported when `amount` is none.
/// - provides: carrying a computation under binders placed between its own
///   innermost `scope` binders and the rest of its context, for a caller that
///   keeps a table beside the arena.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a lambda over its own index, an index below the scope and
///   one past it raises only the last, and reports the variable, the triple,
///   the return and the lambda; no amount mints and reports nothing.
/// - witness: `rewrite::tests::a_traced_shift_raises_only_past_its_scope`
#[spec(captures: entry = (arena.watermark(), carried.len()), ensures: |ret| carried.len() >= entry.1
    && (amount != Binders::NONE || (ret == subject && arena.watermark() == entry.0 && carried.len() == entry.1)))]
#[inline]
#[must_use]
pub fn shift_computation_under_traced(
    arena: &mut CoreArena,
    subject: ComputationId,
    scope: Binders,
    amount: Binders,
    carried: &mut Vec<Carried>,
) -> ComputationId
{
    if amount == Binders::NONE {
        return subject;
    }
    let mut engine = Engine::new(arena);
    let shifted = engine.run(Node::Computation(subject), scope, Rewrite::Shift(amount));
    report(&engine.memo, carried);
    match shifted {
        | Node::Computation(id) => id,
        | Node::Value(_) | Node::ValueType(_) | Node::CompType(_) => subject,
    }
}

/// [`shift_comp_type_under`], reporting every node it rewrote beside the node
/// it rewrote it from.
///
/// # Specification
/// - requires: `subject` is live in `arena`.
/// - ensures: `subject` with every free index counting past its innermost
///   `scope` binders raised by `amount` and every index below kept; `carried`
///   gains one pair per node the shift changed, as
///   [`substitute_environment_traced`] reports them; `subject` itself, nothing
///   minted and nothing reported when `amount` is none.
/// - provides: carrying a written type under binders, for a caller that keeps a
///   table beside the arena and answers each copy where its source was written.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a path type between an index inside the scope and one
///   past it raises only the second endpoint, and reports it, the path and the
///   returner; no amount mints and reports nothing.
/// - witness: `rewrite::tests::a_traced_type_shift_reports_each_copy`
#[spec(captures: entry = (arena.watermark(), carried.len()), ensures: |ret| carried.len() >= entry.1
    && (amount != Binders::NONE || (ret == subject && arena.watermark() == entry.0 && carried.len() == entry.1)))]
#[inline]
#[must_use]
pub fn shift_comp_type_under_traced(
    arena: &mut CoreArena,
    subject: CompTypeId,
    scope: Binders,
    amount: Binders,
    carried: &mut Vec<Carried>,
) -> CompTypeId
{
    if amount == Binders::NONE {
        return subject;
    }
    let mut engine = Engine::new(arena);
    let shifted = engine.run(Node::CompType(subject), scope, Rewrite::Shift(amount));
    report(&engine.memo, carried);
    match shifted {
        | Node::CompType(id) => id,
        | Node::Value(_) | Node::ValueType(_) | Node::Computation(_) => subject,
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
        | Node::Computation(id) => id,
        | Node::Value(_) | Node::ValueType(_) | Node::CompType(_) => body,
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
#[spec(captures: before = carried.len(), ensures: carried.len() >= before && carried.len() <= before.saturating_add(memo.len()))]
fn report(
    memo: &BTreeMap<(Node, Binders, Rewrite), Node>,
    carried: &mut Vec<Carried>,
)
{
    carried.extend(
        memo.iter()
            .filter_map(|(&(from, _depth, _rewrite), &to)| match (from, to) {
                | (Node::Value(held), Node::Value(written)) if held != written => {
                    Some(Carried::Value(held, written))
                },
                | (Node::Computation(held), Node::Computation(written)) if held != written => {
                    Some(Carried::Computation(held, written))
                },
                | (Node::ValueType(held), Node::ValueType(written)) if held != written => {
                    Some(Carried::ValueType(held, written))
                },
                | (Node::CompType(held), Node::CompType(written)) if held != written => {
                    Some(Carried::CompType(held, written))
                },
                | _ => None,
            }),
    );
}

#[cfg(test)]
mod tests
{
    use alloc::collections::BTreeMap;
    #[test]
    fn annotation_substitution_protects_local_binders()
    {
        let mut arena = CoreArena::new();
        let local = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let captured = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
        let local_type = arena.value_type_element(local, Level::zero());
        let captured_type = arena.value_type_element(captured, Level::zero());
        let pair = arena.value_type_product(&[local_type, captured_type]);
        let unit = arena.value_type_unit();
        let code = arena.value_quote(unit);
        let closed = super::instantiate_value_type_under(&mut arena, pair, code, Binders::ONE);
        assert_eq!(
            arena.value_type(closed),
            Some(&ValueType::Product([local_type, unit].into()))
        );
    }
    use alloc::format;
    use alloc::string::String;
    use alloc::vec;
    use alloc::vec::Vec;

    use anodized::spec;
    use gandr_kernel_strata::Level;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::DeBruijnIndex;
    use quenchant_shape::shape::Maybe;

    use super::Binders;
    use super::Carried;
    use super::Nesting;
    use super::Node;
    use super::Renaming;
    use super::Unenclosed;
    use super::elaborate_nested_traced;
    use super::fill_hole;
    use super::instantiate_comp_type;
    use super::instantiate_value;
    use super::rename_value_traced;
    use super::rename_value_type_traced;
    use super::shift_comp_type;
    use super::shift_value_type;
    use super::strengthen_comp_type;
    use super::strengthening;
    use super::substitute_environment;
    use super::substitute_environment_traced;
    use super::wrap_marks;
    use crate::arena::CompTypeId;
    use crate::arena::ComputationId;
    use crate::arena::CoreArena;
    use crate::arena::ValueId;
    use crate::arena::ValueTypeId;
    use crate::hole::HoleId;
    use crate::hole::MarkIndex;
    use crate::hole::TermId;
    use crate::syntax::CompType;
    use crate::syntax::Computation;
    use crate::syntax::Value;
    use crate::syntax::ValueType;
    use crate::syntax::Zone;

    #[test]
    fn native_motives_preserve_binder_and_field_order()
    {
        let mut arena = CoreArena::new();
        let zero = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0));
        let one = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1));
        let nominal = ConstantIndex::from(7);
        let datatype = arena.value_type_data(nominal, vec![zero, one]);
        let motive = arena.comp_type_returner(datatype);
        let shifted =
            super::shift_comp_type_under(&mut arena, motive, Binders::ONE, Binders::from(2));
        let Some(&CompType::Returner {
            result: shifted, ..
        }) = arena.comp_type(shifted)
        else {
            panic!("returner motive");
        };
        let Some(matched_native_node) = arena.value_type(shifted)
        else {
            panic!("nominal motive");
        };
        let ValueType::Data {
            ref declaration,
            ref arguments,
        } = *matched_native_node
        else {
            panic!("nominal motive");
        };
        assert_eq!(*declaration, nominal);
        assert_eq!(
            arena.value(arguments[0]),
            Some(&Value::Variable {
                zone: Zone::Intuitionistic,
                index: DeBruijnIndex::from(0)
            })
        );
        assert_eq!(
            arena.value(arguments[1]),
            Some(&Value::Variable {
                zone: Zone::Intuitionistic,
                index: DeBruijnIndex::from(3)
            })
        );

        let instantiated = super::instantiate_value_type(&mut arena, datatype, one);
        let Some(matched_native_node) = arena.value_type(instantiated)
        else {
            panic!("nominal substitution");
        };
        let ValueType::Data { ref arguments, .. } = *matched_native_node
        else {
            panic!("nominal substitution");
        };
        assert_eq!(
            arena.value(arguments[0]),
            Some(&Value::Variable {
                zone: Zone::Intuitionistic,
                index: DeBruijnIndex::from(1)
            })
        );
        assert_eq!(
            arena.value(arguments[1]),
            Some(&Value::Variable {
                zone: Zone::Intuitionistic,
                index: DeBruijnIndex::from(0)
            })
        );

        let constructor =
            arena.value_constructor(datatype, gandr_kernel_term::ConstructorTag::from(1), vec![
                zero, one,
            ]);
        let label = gandr_kernel_term::FieldLabel::from(alloc::string::String::from("field"));
        let record = arena.value_record(alloc::collections::BTreeMap::from([(
            label.clone(),
            constructor,
        )]));
        let shifted = super::shift_value(&mut arena, record, Binders::from(2));
        let Some(matched_native_node) = arena.value(shifted)
        else {
            panic!("record shift");
        };
        let Value::Record(ref fields) = *matched_native_node
        else {
            panic!("record shift");
        };
        let Some(matched_native_node) = arena.value(fields[&label])
        else {
            panic!("constructor shift");
        };
        let Value::Constructor {
            ref tag,
            ref fields,
            ..
        } = *matched_native_node
        else {
            panic!("constructor shift");
        };
        assert_eq!(*tag, gandr_kernel_term::ConstructorTag::from(1));
        assert_eq!(
            arena.value(fields[0]),
            Some(&Value::Variable {
                zone: Zone::Intuitionistic,
                index: DeBruijnIndex::from(2)
            })
        );
        assert_eq!(
            arena.value(fields[1]),
            Some(&Value::Variable {
                zone: Zone::Intuitionistic,
                index: DeBruijnIndex::from(3)
            })
        );
    }

    /// A family under its own binder lifted past one more binder keeps its
    /// own index and lifts the ambient one; a lift of nothing is the family
    /// itself.
    #[test]
    fn a_value_type_under_its_binder_lifts_only_the_ambient_index()
    {
        let mut arena = CoreArena::new();
        let own = variable(&mut arena, DeBruijnIndex::from(0));
        let ambient = variable(&mut arena, DeBruijnIndex::from(1));
        let nominal = ConstantIndex::from(7);
        let family = arena.value_type_data(nominal, vec![own, ambient]);
        assert_eq!(
            super::shift_value_type_under(&mut arena, family, Binders::ONE, Binders::NONE),
            family
        );
        let lifted = super::shift_value_type_under(&mut arena, family, Binders::ONE, Binders::ONE);
        let Some(lifted) = arena.value_type(lifted)
        else {
            panic!("the family is in the arena");
        };
        let ValueType::Data { ref arguments, .. } = *lifted
        else {
            panic!("the family keeps its former");
        };
        let indices: Vec<Option<&Value>> = arguments
            .iter()
            .map(|&argument| arena.value(argument))
            .collect();
        assert_eq!(indices, [
            Some(&Value::Variable {
                zone: Zone::Intuitionistic,
                index: DeBruijnIndex::from(0)
            }),
            Some(&Value::Variable {
                zone: Zone::Intuitionistic,
                index: DeBruijnIndex::from(2)
            }),
        ]);
    }

    /// An intuitionistic occurrence at `index`.
    ///
    /// # Specification
    /// trivial.
    fn variable(
        arena: &mut CoreArena,
        index: DeBruijnIndex,
    ) -> ValueId
    {
        arena.value_variable(Zone::Intuitionistic, index)
    }

    /// The value type `El x` at the variable `index`.
    ///
    /// # Specification
    /// trivial.
    fn decoded(
        arena: &mut CoreArena,
        index: DeBruijnIndex,
    ) -> ValueTypeId
    {
        let code = variable(arena, index);
        arena.value_type_element(code, Level::zero())
    }

    /// One token of a type's pre-order spelling.
    #[derive(Clone, Debug, Eq, PartialEq)]
    enum Token
    {
        Returner,
        Arrow,
        Pi,
        CompElement,
        Base(BaseType),
        Element,
        Thunk,
        Product,
        Variable(u32),
        Constant(ConstantIndex),
        Pair,
        Quote,
        QuoteComputation,
        StaticLambda,
        StaticApplication,
        Other,
    }

    /// A node the spelling walk visits.
    #[derive(Clone, Copy)]
    enum Visit
    {
        Value(ValueId),
        ValueType(ValueTypeId),
        CompType(CompTypeId),
    }

    /// The pre-order spelling of a computation type, through the formers the
    /// generator writes: two types spell alike exactly when they are equal up
    /// to node identity.
    ///
    /// # Specification
    /// trivial.
    fn spelling(
        arena: &CoreArena,
        root: CompTypeId,
    ) -> Vec<Token>
    {
        spelling_of(arena, Visit::CompType(root))
    }

    /// The pre-order spelling of a value, through the formers the static
    /// tests write.
    ///
    /// # Specification
    /// trivial.
    fn value_spelling(
        arena: &CoreArena,
        root: ValueId,
    ) -> Vec<Token>
    {
        spelling_of(arena, Visit::Value(root))
    }

    /// The pre-order spelling of any node the walk visits.
    ///
    /// # Specification
    /// - requires: an acyclic arena graph in the reference fragment.
    /// - ensures: a pre-order token sequence; unsupported or missing nodes emit
    ///   `Other`, so the observer does not separate those forms.
    /// - provides: an identity-independent reading for finite reference checks.
    /// - panics: none for the admitted graph.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an asymmetric dependent tree and a static application
    ///   have exact pre-order token sequences; these separate root-family
    ///   confusion, reversed child order and omitted variable payloads. Only
    ///   the generator and static-test fragment has a separating spelling.
    /// - witness: `rewrite::tests::reference_helpers_have_ground_and_asymmetric_goldens`
    /// - witness: `rewrite::tests::substitution_replaces_a_free_occurrence`
    #[spec(ensures: |ret| ret.first() == Some(&match root {
        | Visit::CompType(id) => match arena.comp_type(id) {
            | Some(&CompType::Returner { .. }) => Token::Returner,
            | Some(&CompType::Arrow { .. }) => Token::Arrow,
            | Some(&CompType::Pi { .. }) => Token::Pi,
            | Some(&CompType::Element { .. }) => Token::CompElement,
            | Some(&CompType::Unknown | &CompType::With(..)) | None => Token::Other,
        },
        | Visit::ValueType(id) => match arena.value_type(id) {
            | Some(&ValueType::Base(base)) => Token::Base(base),
            | Some(&ValueType::Element { .. }) => Token::Element,
            | Some(&ValueType::Thunk(_)) => Token::Thunk,
            | Some(&ValueType::Product(..)) => Token::Product,
            Some(&ValueType::Stack { .. } | &ValueType::List(_) | &ValueType::Data { .. } | &ValueType::Record(_) |
&ValueType::Sum(..) | &ValueType::PathUniverse(..) | &ValueType::Path { .. } | &ValueType::Universe { ..
} | &ValueType::Lift { .. } | &ValueType::Abstract(_) | &ValueType::StaticPi { .. } | &ValueType::Sigma {
.. } | &ValueType::Capability { .. } | &ValueType::Unknown | &ValueType::Session(_) | &ValueType::Flow { .. } | &ValueType::Run(_)) | None => Token::Other,
            },
        | Visit::Value(id) => match arena.value(id) {
            | Some(&Value::Variable { index, .. }) => Token::Variable(u32::from(index)),
            | Some(&Value::Constant(constant)) => Token::Constant(constant),
            | Some(&Value::Tuple(_)) => Token::Pair,
            | Some(&Value::Quote(_)) => Token::Quote,
            | Some(&Value::QuoteComputation(_)) => Token::QuoteComputation,
            | Some(&Value::StaticLambda(_)) => Token::StaticLambda,
            | Some(&Value::StaticApplication(..)) => Token::StaticApplication,
            Some(&Value::Reify(_) | &Value::ListNil | &Value::ListCons(..) | &Value::Constructor { .. } | &Value::Record(_) | &Value::Primitive { .. }
| &Value::Literal(_) | &Value::Injection(..) | &Value::Thunk(_)
| &Value::Lift { .. } | &Value::PathRefl(_) | &Value::Here(_) | &Value::Funext(..) | &Value::Equiv(..) | &Value::Ua { .. } | &Value::Returned(_) | &Value::Nested(_) | &Value::Run(_) | &Value::PathProduct(..) |
&Value::SessionRelated { .. } | &Value::Stay(_) | &Value::Then(..) | &Value::FlowProduct(..) | &Value::Forward(_) | &Value::FunctionFlow(..) | &Value::Recorded(_) |
&Value::PathEquiv { .. } | &Value::Hole(_) | &Value::Mark { .. }) | None => Token::Other,
            },
    }))]
    fn spelling_of(
        arena: &CoreArena,
        root: Visit,
    ) -> Vec<Token>
    {
        let mut tokens = Vec::new();
        let mut pending = vec![root];
        while let Some(visit) = pending.pop() {
            match visit {
                | Visit::CompType(id) => match arena.comp_type(id) {
                    | Some(&CompType::Returner { result, .. }) => {
                        tokens.push(Token::Returner);
                        pending.push(Visit::ValueType(result));
                    },
                    | Some(&CompType::Arrow { domain, codomain }) => {
                        tokens.push(Token::Arrow);
                        pending.push(Visit::CompType(codomain));
                        pending.push(Visit::ValueType(domain));
                    },
                    | Some(&CompType::Pi { domain, codomain }) => {
                        tokens.push(Token::Pi);
                        pending.push(Visit::CompType(codomain));
                        pending.push(Visit::ValueType(domain));
                    },
                    | Some(&CompType::Element { code, .. }) => {
                        tokens.push(Token::CompElement);
                        pending.push(Visit::Value(code));
                    },
                    | Some(&CompType::Unknown | &CompType::With(..)) | None => {
                        tokens.push(Token::Other);
                    },
                },
                | Visit::ValueType(id) => match arena.value_type(id) {
                    | Some(&ValueType::Base(base)) => tokens.push(Token::Base(base)),
                    | Some(&ValueType::Element { code, .. }) => {
                        tokens.push(Token::Element);
                        pending.push(Visit::Value(code));
                    },
                    | Some(&ValueType::Thunk(body)) => {
                        tokens.push(Token::Thunk);
                        pending.push(Visit::CompType(body));
                    },
                    | Some(&ValueType::Product(ref components)) => {
                        tokens.push(Token::Product);
                        pending.extend(
                            components
                                .iter()
                                .rev()
                                .map(|&component| Visit::ValueType(component)),
                        );
                    },
                    | Some(_) | None => tokens.push(Token::Other),
                },
                | Visit::Value(id) => match arena.value(id) {
                    | Some(&Value::Variable { index, .. }) => {
                        tokens.push(Token::Variable(u32::from(index)));
                    },
                    | Some(&Value::Constant(constant)) => tokens.push(Token::Constant(constant)),
                    | Some(&Value::Tuple(ref components)) => {
                        tokens.push(Token::Pair);
                        pending.extend(
                            components
                                .iter()
                                .rev()
                                .map(|&component| Visit::Value(component)),
                        );
                    },
                    | Some(&Value::Quote(quoted)) => {
                        tokens.push(Token::Quote);
                        pending.push(Visit::ValueType(quoted));
                    },
                    | Some(&Value::QuoteComputation(quoted)) => {
                        tokens.push(Token::QuoteComputation);
                        pending.push(Visit::CompType(quoted));
                    },
                    | Some(&Value::StaticLambda(body)) => {
                        tokens.push(Token::StaticLambda);
                        pending.push(Visit::Value(body));
                    },
                    | Some(&Value::StaticApplication(head, argument)) => {
                        tokens.push(Token::StaticApplication);
                        pending.push(Visit::Value(argument));
                        pending.push(Visit::Value(head));
                    },
                    | Some(_) | None => tokens.push(Token::Other),
                },
            }
        }
        tokens
    }

    /// What a generated node is.
    #[derive(Clone, Copy, Debug)]
    enum Shape
    {
        Returner,
        Arrow,
        Pi,
        CompElement,
        Integer,
        Element,
        Thunk,
        Product,
        /// A variable of the context the tree is placed in, by level: level
        /// zero is the outermost binder.
        Free(u32),
        /// A variable bound inside the tree, by level counted from the
        /// tree's own outermost binder.
        Local(u32),
        Quote,
        QuoteComputation,
    }

    /// What a pending slot of the generator must be filled with.
    #[derive(Clone, Copy, Debug)]
    enum Kind
    {
        Comp,
        ValueType,
        ValueCode,
        CompCode,
    }

    /// One generated node: its shape, its children in order, and how many of
    /// the tree's own binders stand above it.
    #[derive(Clone, Debug)]
    struct GeneratedNode
    {
        shape: Shape,
        children: Vec<usize>,
        binders: u32,
    }

    /// A generated tree, in pre-order: every child after its parent.
    #[repr(transparent)]
    #[derive(Clone, Debug, Default)]
    struct Tree
    {
        nodes: Vec<GeneratedNode>,
    }

    /// A count the generator draws, bounds or places by.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
    struct Count(u32);

    /// A deterministic xorshift stream.
    #[repr(transparent)]
    struct Stream(u64);

    impl Stream
    {
        /// The next draw below `bound`, which must be positive.
        ///
        /// # Specification
        /// - requires: `bound` is positive.
        /// - ensures: the next deterministic draw is strictly below `bound`.
        /// - provides: a bounded choice for the reference generator.
        /// - panics: none for the admitted positive bound.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — singleton, two-element and maximal positive
        ///   ranges distinguish the exclusive bound; bounded generated
        ///   codomains exercise the resulting choices against an independent
        ///   reference.
        /// - witness: `rewrite::tests::reference_helpers_have_ground_and_asymmetric_goldens`
        /// - witness: `rewrite::tests::instantiating_a_codomain_avoids_capture`
        #[spec(requires: bound.0 > 0, ensures: |ret| ret.0 < bound.0)]
        fn below(
            &mut self,
            bound: Count,
        ) -> Count
        {
            self.0 ^= self.0.wrapping_shl(13);
            self.0 ^= self.0.wrapping_shr(7);
            self.0 ^= self.0.wrapping_shl(17);
            Count(u32::try_from(self.0.checked_rem(u64::from(bound.0)).unwrap()).unwrap())
        }
    }

    /// Generate a tree of `kind` over `frees` context levels, using `fuel` to
    /// bound compound choices before completing a terminal code or type.
    ///
    /// # Specification
    /// - requires: `frees + fuel` fits u32.
    /// - ensures: a nonempty pre-order tree of `kind`; children follow their
    ///   parent, free levels are below `frees`, and local levels are bound.
    /// - provides: bounded compound choices; zero fuel still permits the
    ///   terminal code/type formers needed to reach a variable or base type.
    /// - panics: none for the admitted counts.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the 600 deterministic generated trees feed
    ///   independent level-based and de Bruijn substitution readings. L3 — zero
    ///   fuel and no free variables have fixed ground spellings in every
    ///   requested family, distinguishing malformed terminal shapes and child
    ///   arities.
    /// - witness: `rewrite::tests::instantiating_a_codomain_avoids_capture`
    /// - witness: `rewrite::tests::reference_helpers_have_ground_and_asymmetric_goldens`
    #[spec(
        requires: frees.0.checked_add(fuel.0).is_some(),
        ensures: |ret| ret.nodes.first().is_some_and(|root| root.binders == 0 && match kind {
            | Kind::Comp => matches!(root.shape, Shape::Returner | Shape::Arrow | Shape::Pi | Shape::CompElement),
            | Kind::ValueType => matches!(root.shape, Shape::Integer | Shape::Element | Shape::Thunk | Shape::Product),
            | Kind::ValueCode => matches!(root.shape, Shape::Free(_) | Shape::Local(_) | Shape::Quote),
            | Kind::CompCode => matches!(root.shape, Shape::Free(_) | Shape::Local(_) | Shape::QuoteComputation),
        }) && ret.nodes.iter().enumerate().all(|(here, node)| node.binders <= fuel.0
            && node.children.iter().all(|child| *child > here && *child < ret.nodes.len())
            && match node.shape {
                | Shape::Free(level) => level < frees.0 && node.children.is_empty(),
                | Shape::Local(level) => level < node.binders && node.children.is_empty(),
                | Shape::Integer => node.children.is_empty(),
                | Shape::Arrow | Shape::Pi | Shape::Product => node.children.len() == 2,
                | Shape::Returner | Shape::CompElement | Shape::Element | Shape::Thunk | Shape::Quote | Shape::QuoteComputation => node.children.len() == 1,
            }),
    )]
    fn generate(
        stream: &mut Stream,
        kind: Kind,
        frees: Count,
        fuel: Count,
    ) -> Tree
    {
        let frees = frees.0;
        let mut tree = Tree::default();
        // (parent, kind, binders above, fuel left)
        let mut pending: Vec<(Option<usize>, Kind, u32, u32)> = vec![(None, kind, 0, fuel.0)];
        while let Some((parent, kind, binders, fuel)) = pending.pop() {
            let here = tree.nodes.len();
            if let Some(parent) = parent {
                tree.nodes[parent].children.push(here);
            }
            let variables = frees.checked_add(binders).unwrap();
            let leaf = fuel == 0;
            let less = fuel.saturating_sub(1);
            let variable_shape = |stream: &mut Stream| {
                let pick = stream.below(Count(variables)).0;
                if pick < frees {
                    Shape::Free(pick)
                }
                else {
                    Shape::Local(pick.checked_sub(frees).unwrap())
                }
            };
            // Children are pushed in reverse so they are generated in order.
            let (shape, children): (Shape, Vec<(Kind, u32)>) = match kind {
                | Kind::Comp => match (leaf, stream.below(Count(4)).0) {
                    | (true, _) | (false, 0) => (Shape::Returner, vec![(Kind::ValueType, binders)]),
                    | (false, 1) => (Shape::Arrow, vec![
                        (Kind::ValueType, binders),
                        (Kind::Comp, binders),
                    ]),
                    | (false, 2) => (Shape::Pi, vec![
                        (Kind::ValueType, binders),
                        (Kind::Comp, binders.checked_add(1).unwrap()),
                    ]),
                    | (false, _) => (Shape::CompElement, vec![(Kind::CompCode, binders)]),
                },
                | Kind::ValueType => match (leaf, stream.below(Count(4)).0) {
                    | (true, 0) | (_, 1) if variables > 0 => {
                        (Shape::Element, vec![(Kind::ValueCode, binders)])
                    },
                    | (true, _) => (Shape::Integer, Vec::new()),
                    | (false, 0) => (Shape::Thunk, vec![(Kind::Comp, binders)]),
                    | (false, 2) => (Shape::Product, vec![
                        (Kind::ValueType, binders),
                        (Kind::ValueType, binders),
                    ]),
                    | (false, _) => (Shape::Element, vec![(Kind::ValueCode, binders)]),
                },
                | Kind::ValueCode => match (leaf, stream.below(Count(3)).0) {
                    | (true, _) | (false, 0 | 1) if variables > 0 => {
                        (variable_shape(stream), Vec::new())
                    },
                    | (..) => (Shape::Quote, vec![(Kind::ValueType, binders)]),
                },
                | Kind::CompCode => match (leaf, stream.below(Count(3)).0) {
                    | (true, _) | (false, 0 | 1) if variables > 0 => {
                        (variable_shape(stream), Vec::new())
                    },
                    | (..) => (Shape::QuoteComputation, vec![(Kind::Comp, binders)]),
                },
            };
            tree.nodes.push(GeneratedNode {
                shape,
                children: Vec::new(),
                binders,
            });
            for &(child, child_binders) in children.iter().rev() {
                pending.push((Some(here), child, child_binders, less));
            }
        }
        tree
    }

    /// A node the builder minted.
    #[derive(Clone, Copy, Debug)]
    enum Built
    {
        Value(ValueId),
        ValueType(ValueTypeId),
        CompType(CompTypeId),
    }

    /// How the builder reads a free variable.
    #[derive(Clone, Copy)]
    enum Reading<'tree>
    {
        /// As an index at the depth it is reached at.
        Plain,
        /// The context level `binder` is replaced by the argument, built
        /// beforehand at every depth below the tree's own binders:
        /// `arguments[n]` stands under `n` of them. Levels past it drop by one.
        Spliced
        {
            binder: u32,
            arguments: &'tree [ValueId],
        },
    }

    /// Mint `tree` into `arena` with its root at absolute depth `placement`,
    /// reading free variables as `reading` says.
    ///
    /// # Specification
    /// - requires: a nonempty well-formed generated tree; `placement` contains
    ///   its unspliced free levels and every needed replacement depth exists.
    /// - ensures: a live arena root interpreting each level at its placement,
    ///   with the designated spliced level replaced without variable capture.
    /// - provides: the level-based reference, independent of the rewrite
    ///   engine.
    /// - panics: none for an admitted tree and placement.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the level-based builder is the independent reading
    ///   used by 600 bounded substitution comparisons. L3 — ground roots of all
    ///   three output families and a dependent asymmetric tree pin the oracle
    ///   against dropped children, reversed order and a misplaced binder.
    /// - witness: `rewrite::tests::instantiating_a_codomain_avoids_capture`
    /// - witness: `rewrite::tests::reference_helpers_have_ground_and_asymmetric_goldens`
    #[spec(requires: !tree.nodes.is_empty(), ensures: |ret| match ret {
        | Built::Value(id) => arena.value(id).is_some(),
        | Built::ValueType(id) => arena.value_type(id).is_some(),
        | Built::CompType(id) => arena.comp_type(id).is_some(),
    })]
    fn build(
        arena: &mut CoreArena,
        tree: &Tree,
        placement: Count,
        reading: Reading<'_>,
    ) -> Built
    {
        let mut built: Vec<Option<Built>> = vec![None; tree.nodes.len()];
        for here in (0 .. tree.nodes.len()).rev() {
            let node = &tree.nodes[here];
            let depth = placement.0.checked_add(node.binders).unwrap();
            let child = |position: usize| built[node.children[position]].unwrap();
            let value_type = |position: usize| match child(position) {
                | Built::ValueType(id) => id,
                | Built::Value(_) | Built::CompType(_) => panic!("a value-type child"),
            };
            let comp_type = |position: usize| match child(position) {
                | Built::CompType(id) => id,
                | Built::Value(_) | Built::ValueType(_) => panic!("a computation-type child"),
            };
            let value = |position: usize| match child(position) {
                | Built::Value(id) => id,
                | Built::ValueType(_) | Built::CompType(_) => panic!("a value child"),
            };
            let minted = match node.shape {
                | Shape::Returner => Built::CompType(arena.comp_type_returner(value_type(0))),
                | Shape::Arrow => {
                    Built::CompType(arena.comp_type_arrow(value_type(0), comp_type(1)))
                },
                | Shape::Pi => Built::CompType(arena.comp_type_pi(value_type(0), comp_type(1))),
                | Shape::CompElement => {
                    Built::CompType(arena.comp_type_element(value(0), Level::zero()))
                },
                | Shape::Integer => Built::ValueType(arena.value_type_base(BaseType::Integer)),
                | Shape::Element => {
                    Built::ValueType(arena.value_type_element(value(0), Level::zero()))
                },
                | Shape::Thunk => Built::ValueType(arena.value_type_thunk(comp_type(0))),
                | Shape::Product => {
                    Built::ValueType(arena.value_type_product(&[value_type(0), value_type(1)]))
                },
                | Shape::Quote => Built::Value(arena.value_quote(value_type(0))),
                | Shape::QuoteComputation => {
                    Built::Value(arena.value_quote_computation(comp_type(0)))
                },
                | Shape::Local(level) => {
                    let index = node
                        .binders
                        .checked_sub(1)
                        .unwrap()
                        .checked_sub(level)
                        .unwrap();
                    Built::Value(variable(arena, DeBruijnIndex::from(index)))
                },
                | Shape::Free(level) => match reading {
                    | Reading::Spliced { binder, arguments } if level == binder => {
                        Built::Value(arguments[usize::try_from(node.binders).unwrap()])
                    },
                    | Reading::Spliced { binder, .. } if level > binder => {
                        let lowered = level.checked_sub(1).unwrap();
                        let index = depth.checked_sub(1).unwrap().checked_sub(lowered).unwrap();
                        Built::Value(variable(arena, DeBruijnIndex::from(index)))
                    },
                    | Reading::Plain | Reading::Spliced { .. } => {
                        let index = depth.checked_sub(1).unwrap().checked_sub(level).unwrap();
                        Built::Value(variable(arena, DeBruijnIndex::from(index)))
                    },
                },
            };
            built[here] = Some(minted);
        }
        built[0].unwrap()
    }

    #[test]
    fn instantiating_a_codomain_avoids_capture()
    {
        let mut stream = Stream(0x9E37_79B9_7F4A_7C15);
        for round in 0 .. 600_u32 {
            let outer = round.checked_rem(3).unwrap();
            // The codomain reads the outer context and the dependent arrow's
            // own binder, at level `outer`; the argument reads the outer
            // context alone.
            let codomain = generate(
                &mut stream,
                Kind::Comp,
                Count(outer.checked_add(1).unwrap()),
                Count(4),
            );
            let argument = generate(&mut stream, Kind::ValueCode, Count(outer), Count(3));
            let mut arena = CoreArena::new();
            let Built::CompType(scoped) = build(
                &mut arena,
                &codomain,
                Count(outer.checked_add(1).unwrap()),
                Reading::Plain,
            )
            else {
                panic!("a computation type");
            };
            let Built::Value(supplied) = build(&mut arena, &argument, Count(outer), Reading::Plain)
            else {
                panic!("a value");
            };
            let machine = instantiate_comp_type(&mut arena, scoped, supplied);
            let deepest = codomain
                .nodes
                .iter()
                .map(|node| node.binders)
                .max()
                .unwrap();
            let arguments: Vec<ValueId> = (0 ..= deepest)
                .map(|binders| {
                    let placement = Count(outer.checked_add(binders).unwrap());
                    match build(&mut arena, &argument, placement, Reading::Plain) {
                        | Built::Value(id) => id,
                        | Built::ValueType(_) | Built::CompType(_) => panic!("a value"),
                    }
                })
                .collect();
            let Built::CompType(reference) =
                build(&mut arena, &codomain, Count(outer), Reading::Spliced {
                    binder: outer,
                    arguments: &arguments,
                })
            else {
                panic!("a computation type");
            };
            assert_eq!(
                spelling(&arena, reference),
                spelling(&arena, machine),
                "round {round}: the machine agrees with the capture-free reference for {codomain:?} at {argument:?}"
            );
        }
    }

    #[test]
    fn shifting_raises_free_indices_and_spares_bound_ones()
    {
        let mut arena = CoreArena::new();
        // Π (_ : El #0). El #0 → F (El #1): the domain's #0 is free, the
        // codomain's #0 is the arrow's own binder and its #1 is free.
        let domain = decoded(&mut arena, DeBruijnIndex::from(0));
        let bound = decoded(&mut arena, DeBruijnIndex::from(0));
        let free = decoded(&mut arena, DeBruijnIndex::from(1));
        let result = arena.comp_type_returner(free);
        let codomain = arena.comp_type_arrow(bound, result);
        let subject = arena.comp_type_pi(domain, codomain);
        let shifted = shift_comp_type(&mut arena, subject, Binders::from(2_u32));

        let expected_domain = decoded(&mut arena, DeBruijnIndex::from(2));
        let expected_bound = decoded(&mut arena, DeBruijnIndex::from(0));
        let expected_free = decoded(&mut arena, DeBruijnIndex::from(3));
        let expected_result = arena.comp_type_returner(expected_free);
        let expected_codomain = arena.comp_type_arrow(expected_bound, expected_result);
        let expected = arena.comp_type_pi(expected_domain, expected_codomain);
        assert_eq!(
            spelling(&arena, expected),
            spelling(&arena, shifted),
            "free indices rise by the amount and the bound one stands"
        );

        let integer = arena.value_type_base(BaseType::Integer);
        assert_eq!(
            integer,
            shift_value_type(&mut arena, integer, Binders::from(2_u32)),
            "a closed type shifts to itself"
        );
    }

    #[test]
    fn instantiating_a_decode_at_a_quote_decodes()
    {
        let mut arena = CoreArena::new();
        let decode = decoded(&mut arena, DeBruijnIndex::from(0));
        let codomain = arena.comp_type_returner(decode);
        let integer = arena.value_type_base(BaseType::Integer);
        let code = arena.value_quote(integer);
        let instantiated = instantiate_comp_type(&mut arena, codomain, code);
        assert_eq!(
            Some(&CompType::Returner {
                result: integer,
                effects: crate::effect::EffectRow::EMPTY
            }),
            arena.comp_type(instantiated),
            "F (El x) at ⌜Integer⌝ is F Integer, with the decode read off the quote"
        );
    }

    #[test]
    fn strengthening_refuses_a_mention_and_lowers_the_rest()
    {
        let mut arena = CoreArena::new();
        let mentioning = decoded(&mut arena, DeBruijnIndex::from(0));
        let mentioning = arena.comp_type_returner(mentioning);
        assert_eq!(
            Maybe::Absent(strengthening::Absent::MentionsBinder),
            strengthen_comp_type(&mut arena, mentioning),
            "a type that reads the binder cannot leave it"
        );

        let outer = decoded(&mut arena, DeBruijnIndex::from(1));
        let outer = arena.comp_type_returner(outer);
        let Maybe::Present(lowered) = strengthen_comp_type(&mut arena, outer)
        else {
            panic!("a type that reads only an outer index leaves the binder");
        };
        let expected = decoded(&mut arena, DeBruijnIndex::from(0));
        let expected = arena.comp_type_returner(expected);
        assert_eq!(
            spelling(&arena, expected),
            spelling(&arena, lowered),
            "and its outer index lowers by one"
        );
    }

    #[test]
    fn a_shared_type_is_rewritten_once_per_node()
    {
        /// A product chain of sixty-four doublings over `El #index`, whose
        /// unfolding is exponential and whose node count is linear.
        ///
        /// # Specification
        /// - requires: nothing.
        /// - ensures: sixty-four product levels, each sharing both children,
        ///   above a decode of the intuitionistic variable at `index`.
        /// - provides: a linear representation with an exponential unfolding.
        /// - panics: none.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — a shift over sixty-four shared product levels has
        ///   exactly the watermark of the original plus one rewritten chain,
        ///   distinguishing loss of sharing from expansion of the exponentially
        ///   large unfolding.
        /// - witness: `rewrite::tests::a_shared_type_is_rewritten_once_per_node`
        #[spec(ensures: |ret| {
            let mut current = ret;
            let mut valid = true;
            for _ in 0_u32..64_u32 {
                if let Some(held) = arena.value_type(current) && let ValueType::Product(ref components) = *held && let [first, second] = **components {
                    valid &= first == second;
                    current = first;
                } else { valid = false; }
            }
            valid && matches!(arena.value_type(current), Some(ValueType::Element { code, .. })
                if arena.value(*code) == Some(&Value::Variable { zone: Zone::Intuitionistic, index }))
        })]
        fn chain(
            arena: &mut CoreArena,
            index: DeBruijnIndex,
        ) -> ValueTypeId
        {
            let mut shared = decoded(arena, index);
            for _ in 0 .. 64_u32 {
                shared = arena.value_type_product(&[shared, shared]);
            }
            shared
        }

        let mut arena = CoreArena::new();
        let subject = chain(&mut arena, DeBruijnIndex::from(0));
        let shifted = shift_value_type(&mut arena, subject, Binders::ONE);
        assert_ne!(subject, shifted, "the free index was raised");

        let mut reference = CoreArena::new();
        let _original = chain(&mut reference, DeBruijnIndex::from(0));
        let _raised = chain(&mut reference, DeBruijnIndex::from(1));
        assert_eq!(
            reference.watermark(),
            arena.watermark(),
            "the shift minted exactly one more copy of the shared chain, never its unfolding"
        );
    }

    #[test]
    fn substitution_replaces_a_free_occurrence()
    {
        let mut arena = CoreArena::new();
        // F #0 #1 under one binder, at G: the binder's #0 becomes G and the
        // outer #1 lowers to #0.
        let operator = arena.value_constant(ConstantIndex::from(0_usize));
        let bound = variable(&mut arena, DeBruijnIndex::from(0));
        let outer = variable(&mut arena, DeBruijnIndex::from(1));
        let inner = arena.value_static_application(operator, bound);
        let body = arena.value_static_application(inner, outer);
        let argument = arena.value_constant(ConstantIndex::from(1_usize));
        let reduct = instantiate_value(&mut arena, body, argument);
        assert_eq!(
            vec![
                Token::StaticApplication,
                Token::StaticApplication,
                Token::Constant(ConstantIndex::from(0_usize)),
                Token::Constant(ConstantIndex::from(1_usize)),
                Token::Variable(0),
            ],
            value_spelling(&arena, reduct),
            "the free occurrence is the argument and the outer index lowers by one"
        );
    }

    #[test]
    fn substitution_stops_at_a_shadowing_binder()
    {
        let mut arena = CoreArena::new();
        // λ. ⟨#0, #1⟩ under one binder: the inner #0 is the lambda's own and
        // stays; the inner #1 is the substituted binder.
        let own = variable(&mut arena, DeBruijnIndex::from(0));
        let substituted = variable(&mut arena, DeBruijnIndex::from(1));
        let pair = arena.value_tuple(&[own, substituted]);
        let body = arena.value_static_lambda(pair);
        let argument = arena.value_constant(ConstantIndex::from(1_usize));
        let reduct = instantiate_value(&mut arena, body, argument);
        assert_eq!(
            vec![
                Token::StaticLambda,
                Token::Pair,
                Token::Variable(0),
                Token::Constant(ConstantIndex::from(1_usize)),
            ],
            value_spelling(&arena, reduct),
            "the shadowing lambda's own occurrence is spared"
        );

        let only_own = variable(&mut arena, DeBruijnIndex::from(0));
        let closed = arena.value_static_lambda(only_own);
        assert_eq!(
            closed,
            instantiate_value(&mut arena, closed, argument),
            "and a body that never reads the binder is returned as it stands"
        );
    }

    #[test]
    fn substitution_avoids_capture()
    {
        let mut arena = CoreArena::new();
        // λ. #1 under one binder, at the open argument #0: carried under the
        // lambda the argument is #1, not the lambda's own #0.
        let substituted = variable(&mut arena, DeBruijnIndex::from(1));
        let body = arena.value_static_lambda(substituted);
        let argument = variable(&mut arena, DeBruijnIndex::from(0));
        let reduct = instantiate_value(&mut arena, body, argument);
        assert_eq!(
            vec![Token::StaticLambda, Token::Variable(1)],
            value_spelling(&arena, reduct),
            "the open argument rises past the binder it crosses"
        );
    }

    #[test]
    fn binder_counts_clamp_at_the_ceiling()
    {
        for (input, expected) in [
            (0_u32, 1_u32),
            (u32::MAX - 1, u32::MAX),
            (u32::MAX, u32::MAX),
        ] {
            assert_eq!(Binders::from(expected), Binders::from(input).deeper());
            assert_eq!(
                Binders::from(expected),
                Binders::past(DeBruijnIndex::from(input))
            );
        }
        for (input, count, expected) in [
            (3_u32, 0_usize, 3_u32),
            (3_u32, 1_usize, 4_u32),
            (3_u32, 4_usize, 7_u32),
            (u32::MAX - 1, 4_usize, u32::MAX),
            (0_u32, usize::MAX, u32::MAX),
        ] {
            assert_eq!(
                Binders::from(expected),
                Binders::from(input).deeper_by(crate::ComponentCount::from(count)),
                "{input} binders past {count} more"
            );
        }
    }

    #[test]
    fn occurrence_rules_separate_depth_boundaries()
    {
        use super::Engine;
        use super::Mention;
        use super::Occurrence;
        use super::Rewrite;
        let mut arena = CoreArena::new();
        let replacement = arena.value_constant(ConstantIndex::from(7_usize));
        // depth, index, shift by one, lowering (None marks the removed binder).
        for (depth, index, raised, lowered) in [
            (0_u32, 0_u32, 1_u32, None),
            (0, 1, 2, Some(0)),
            (1, 0, 0, Some(0)),
            (1, 1, 2, None),
            (1, 2, 3, Some(1)),
            (1, u32::MAX, u32::MAX, Some(u32::MAX - 1)),
        ] {
            let id = variable(&mut arena, DeBruijnIndex::from(index));
            let mut engine = Engine::new(&mut arena);
            let zero_shift = engine.occurrence(
                id,
                DeBruijnIndex::from(index),
                Binders::from(depth),
                Rewrite::Shift(Binders::NONE),
            );
            assert_eq!(Occurrence::Answered(id), zero_shift);
            let Occurrence::Answered(shifted) = engine.occurrence(
                id,
                DeBruijnIndex::from(index),
                Binders::from(depth),
                Rewrite::Shift(Binders::ONE),
            )
            else {
                panic!("a shift answers directly");
            };
            assert_eq!(
                Some(&Value::Variable {
                    zone: Zone::Intuitionistic,
                    index: DeBruijnIndex::from(raised)
                }),
                engine.arena.value(shifted)
            );
            if index < depth {
                assert_eq!(id, shifted);
            }
            let substituted = engine.occurrence(
                id,
                DeBruijnIndex::from(index),
                Binders::from(depth),
                Rewrite::Substitute(replacement),
            );
            match lowered {
                | None if depth == 0 => assert_eq!(Occurrence::Answered(replacement), substituted),
                | None => assert_eq!(
                    Occurrence::Carried(replacement, Binders::from(depth)),
                    substituted
                ),
                | Some(expected) => {
                    let Occurrence::Answered(answer) = substituted
                    else {
                        panic!("an unselected index is not carried");
                    };
                    assert_eq!(
                        Some(&Value::Variable {
                            zone: Zone::Intuitionistic,
                            index: DeBruijnIndex::from(expected)
                        }),
                        engine.arena.value(answer)
                    );
                    if index < depth {
                        assert_eq!(id, answer);
                    }
                },
            }
            for prior in [Mention::Absent, Mention::Present] {
                engine.mention = prior;
                let Occurrence::Answered(answer) = engine.occurrence(
                    id,
                    DeBruijnIndex::from(index),
                    Binders::from(depth),
                    Rewrite::Lower,
                )
                else {
                    panic!("lowering never carries a replacement");
                };
                if let Some(expected) = lowered {
                    assert_eq!(prior, engine.mention);
                    assert_eq!(
                        Some(&Value::Variable {
                            zone: Zone::Intuitionistic,
                            index: DeBruijnIndex::from(expected)
                        }),
                        engine.arena.value(answer)
                    );
                }
                else {
                    assert_eq!(id, answer);
                    assert_eq!(Mention::Present, engine.mention);
                }
            }
        }
    }

    #[test]
    fn reference_helpers_have_ground_and_asymmetric_goldens()
    {
        let mut stream = Stream(0x9E37_79B9_7F4A_7C15);
        for bound in [1_u32, 2, u32::MAX] {
            for _ in 0_u32 .. 32_u32 {
                assert!(stream.below(Count(bound)).0 < bound);
            }
        }
        for (kind, expected) in [
            (Kind::Comp, vec![
                Token::Returner,
                Token::Base(BaseType::Integer),
            ]),
            (Kind::ValueType, vec![Token::Base(BaseType::Integer)]),
            (Kind::ValueCode, vec![
                Token::Quote,
                Token::Base(BaseType::Integer),
            ]),
            (Kind::CompCode, vec![
                Token::QuoteComputation,
                Token::Returner,
                Token::Base(BaseType::Integer),
            ]),
        ] {
            let tree = generate(&mut stream, kind, Count(0), Count(0));
            let mut arena = CoreArena::new();
            let built = build(&mut arena, &tree, Count(0), Reading::Plain);
            let visit = match built {
                | Built::Value(id) => Visit::Value(id),
                | Built::ValueType(id) => Visit::ValueType(id),
                | Built::CompType(id) => Visit::CompType(id),
            };
            assert_eq!(expected, spelling_of(&arena, visit));
        }
        let tree = Tree {
            nodes: vec![
                GeneratedNode {
                    shape: Shape::Pi,
                    children: vec![1, 2],
                    binders: 0,
                },
                GeneratedNode {
                    shape: Shape::Integer,
                    children: vec![],
                    binders: 0,
                },
                GeneratedNode {
                    shape: Shape::CompElement,
                    children: vec![3],
                    binders: 1,
                },
                GeneratedNode {
                    shape: Shape::Local(0),
                    children: vec![],
                    binders: 1,
                },
            ],
        };
        let mut arena = CoreArena::new();
        let Built::CompType(root) = build(&mut arena, &tree, Count(0), Reading::Plain)
        else {
            panic!("the Pi is a computation type");
        };
        assert_eq!(
            vec![
                Token::Pi,
                Token::Base(BaseType::Integer),
                Token::CompElement,
                Token::Variable(0)
            ],
            spelling(&arena, root)
        );
    }

    #[test]
    fn congruences_preserve_formers_and_child_order()
    {
        use super::Engine;
        use super::Node;
        let mut arena = CoreArena::new();
        let v0 = variable(&mut arena, DeBruijnIndex::from(0));
        let v1 = variable(&mut arena, DeBruijnIndex::from(1));
        let w0 = variable(&mut arena, DeBruijnIndex::from(3));
        let w1 = variable(&mut arena, DeBruijnIndex::from(5));
        let c0 = arena.computation_return(v0);
        let c1 = arena.computation_return(v1);
        let d0 = arena.computation_return(w0);
        let d1 = arena.computation_return(w1);
        let t0 = arena.value_type_element(v0, Level::zero());
        let t1 = arena.value_type_element(v1, Level::zero());
        let u0 = arena.value_type_base(BaseType::Integer);
        let u1 = arena.value_type_unit();
        let k0 = arena.comp_type_returner(t0);
        let k1 = arena.comp_type_returner(t1);
        let l0 = arena.comp_type_returner(u0);
        let l1 = arena.comp_type_returner(u1);
        let level = Level::zero().succ().expect("one");
        for (original, unchanged, changed, expected) in [
            (
                arena.value_tuple(&[v0, v1]),
                vec![Node::Value(v0), Node::Value(v1)],
                vec![Node::Value(w0), Node::Value(w1)],
                Value::Tuple([w0, w1].into()),
            ),
            (
                arena.value_injection(gandr_kernel_term::Side::Left.into(), v0),
                vec![Node::Value(v0)],
                vec![Node::Value(w0)],
                Value::Injection(gandr_kernel_term::Side::Left.into(), w0),
            ),
            (
                arena.value_injection(gandr_kernel_term::Side::Right.into(), v1),
                vec![Node::Value(v1)],
                vec![Node::Value(w1)],
                Value::Injection(gandr_kernel_term::Side::Right.into(), w1),
            ),
            (
                arena.value_thunk(c0),
                vec![Node::Computation(c0)],
                vec![Node::Computation(d0)],
                Value::Thunk(d0),
            ),
            (
                arena.value_lift(level.clone(), v0),
                vec![Node::Value(v0)],
                vec![Node::Value(w0)],
                Value::Lift {
                    target: level.clone(),
                    body: w0,
                },
            ),
            (
                arena.value_quote(t0),
                vec![Node::ValueType(t0)],
                vec![Node::ValueType(u0)],
                Value::Quote(u0),
            ),
            (
                arena.value_quote_computation(k0),
                vec![Node::CompType(k0)],
                vec![Node::CompType(l0)],
                Value::QuoteComputation(l0),
            ),
            (
                arena.value_static_lambda(v0),
                vec![Node::Value(v0)],
                vec![Node::Value(w0)],
                Value::StaticLambda(w0),
            ),
            (
                arena.value_static_application(v0, v1),
                vec![Node::Value(v0), Node::Value(v1)],
                vec![Node::Value(w0), Node::Value(w1)],
                Value::StaticApplication(w0, w1),
            ),
        ] {
            let mark = arena.watermark();
            let mut engine = Engine::new(&mut arena);
            engine.results.extend(unchanged);
            assert_eq!(Node::Value(original), engine.close(Node::Value(original)));
            assert_eq!(mark, engine.arena.watermark());
            engine.results.extend(changed);
            let Node::Value(rewritten) = engine.close(Node::Value(original))
            else {
                panic!("the family is preserved");
            };
            assert_ne!(original, rewritten);
            assert_eq!(Some(&expected), engine.arena.value(rewritten));
            assert!(engine.results.is_empty());
        }
        for (original, unchanged, changed, expected) in [
            (
                arena.computation_lambda(c0),
                vec![Node::Computation(c0)],
                vec![Node::Computation(d0)],
                crate::Computation::Lambda(d0),
            ),
            (
                arena.computation_application(c0, v0),
                vec![Node::Computation(c0), Node::Value(v0)],
                vec![Node::Computation(d0), Node::Value(w0)],
                crate::Computation::Application(d0, w0),
            ),
            (
                arena.computation_return(v0),
                vec![Node::Value(v0)],
                vec![Node::Value(w0)],
                crate::Computation::Return(w0),
            ),
            (
                arena.computation_force(v1),
                vec![Node::Value(v1)],
                vec![Node::Value(w1)],
                crate::Computation::Force(w1),
            ),
            (
                arena.computation_bind(c0, c1),
                vec![Node::Computation(c0), Node::Computation(c1)],
                vec![Node::Computation(d0), Node::Computation(d1)],
                crate::Computation::Bind(d0, d1),
            ),
            (
                arena.computation_case(v0, &[c0, c1]),
                vec![
                    Node::Value(v0),
                    Node::Computation(c0),
                    Node::Computation(c1),
                ],
                vec![
                    Node::Value(w0),
                    Node::Computation(d0),
                    Node::Computation(d1),
                ],
                crate::Computation::Case {
                    scrutinee: w0,
                    branches: [d0, d1].into(),
                },
            ),
        ] {
            let mark = arena.watermark();
            let mut engine = Engine::new(&mut arena);
            engine.results.extend(unchanged);
            assert_eq!(
                Node::Computation(original),
                engine.close(Node::Computation(original))
            );
            assert_eq!(mark, engine.arena.watermark());
            engine.results.extend(changed);
            let Node::Computation(rewritten) = engine.close(Node::Computation(original))
            else {
                panic!("the family is preserved");
            };
            assert_ne!(original, rewritten);
            assert_eq!(Some(&expected), engine.arena.computation(rewritten));
            assert!(engine.results.is_empty());
        }
        for (original, unchanged, changed, expected) in [
            (
                arena.value_type_product(&[t0, t1]),
                vec![Node::ValueType(t0), Node::ValueType(t1)],
                vec![Node::ValueType(u0), Node::ValueType(u1)],
                ValueType::Product([u0, u1].into()),
            ),
            (
                arena.value_type_sum(&[t0, t1]),
                vec![Node::ValueType(t0), Node::ValueType(t1)],
                vec![Node::ValueType(u0), Node::ValueType(u1)],
                ValueType::Sum([u0, u1].into()),
            ),
            (
                arena.value_type_static_pi(t0, t1),
                vec![Node::ValueType(t0), Node::ValueType(t1)],
                vec![Node::ValueType(u0), Node::ValueType(u1)],
                ValueType::StaticPi {
                    domain: u0,
                    codomain: u1,
                },
            ),
            (
                arena.value_type_thunk(k0),
                vec![Node::CompType(k0)],
                vec![Node::CompType(l0)],
                ValueType::Thunk(l0),
            ),
            (
                arena.value_type_lift(t0, level.clone()),
                vec![Node::ValueType(t0)],
                vec![Node::ValueType(u0)],
                ValueType::Lift {
                    inner: u0,
                    target: level.clone(),
                },
            ),
            (
                arena.value_type_element(v0, level.clone()),
                vec![Node::Value(v0)],
                vec![Node::Value(w0)],
                ValueType::Element {
                    code: w0,
                    target: level.clone(),
                },
            ),
        ] {
            let mark = arena.watermark();
            let mut engine = Engine::new(&mut arena);
            engine.results.extend(unchanged);
            assert_eq!(
                Node::ValueType(original),
                engine.close(Node::ValueType(original))
            );
            assert_eq!(mark, engine.arena.watermark());
            engine.results.extend(changed);
            let Node::ValueType(rewritten) = engine.close(Node::ValueType(original))
            else {
                panic!("the family is preserved");
            };
            assert_ne!(original, rewritten);
            assert_eq!(Some(&expected), engine.arena.value_type(rewritten));
            assert!(engine.results.is_empty());
        }
        for (original, unchanged, changed, expected) in [
            (
                arena.comp_type_returner(t0),
                vec![Node::ValueType(t0)],
                vec![Node::ValueType(u0)],
                CompType::Returner {
                    result: u0,
                    effects: crate::effect::EffectRow::EMPTY,
                },
            ),
            (
                arena.comp_type_arrow(t0, k0),
                vec![Node::ValueType(t0), Node::CompType(k0)],
                vec![Node::ValueType(u0), Node::CompType(l0)],
                CompType::Arrow {
                    domain: u0,
                    codomain: l0,
                },
            ),
            (
                arena.comp_type_pi(t1, k1),
                vec![Node::ValueType(t1), Node::CompType(k1)],
                vec![Node::ValueType(u1), Node::CompType(l1)],
                CompType::Pi {
                    domain: u1,
                    codomain: l1,
                },
            ),
            (
                arena.comp_type_element(v1, level.clone()),
                vec![Node::Value(v1)],
                vec![Node::Value(w1)],
                CompType::Element {
                    code: w1,
                    target: level,
                },
            ),
        ] {
            let mark = arena.watermark();
            let mut engine = Engine::new(&mut arena);
            engine.results.extend(unchanged);
            assert_eq!(
                Node::CompType(original),
                engine.close(Node::CompType(original))
            );
            assert_eq!(mark, engine.arena.watermark());
            engine.results.extend(changed);
            let Node::CompType(rewritten) = engine.close(Node::CompType(original))
            else {
                panic!("the family is preserved");
            };
            assert_ne!(original, rewritten);
            assert_eq!(Some(&expected), engine.arena.comp_type(rewritten));
            assert!(engine.results.is_empty());
        }
        let quoted_value = arena.value_quote(u0);
        let quoted_comp = arena.value_quote_computation(l0);
        let undecoded_comp = arena.comp_type_element(v0, Level::zero());
        let mark = arena.watermark();
        let mut engine = Engine::new(&mut arena);
        engine.results.push(Node::Value(quoted_value));
        assert_eq!(Node::ValueType(u0), engine.close(Node::ValueType(t0)));
        engine.results.push(Node::Value(quoted_comp));
        assert_eq!(
            Node::CompType(l0),
            engine.close(Node::CompType(undecoded_comp))
        );
        assert_eq!(mark, engine.arena.watermark());
    }

    #[test]
    fn binding_sites_distinguish_free_bound_and_linear_indices()
    {
        use super::Engine;
        use super::Node;
        use super::Rewrite;
        let mut arena = CoreArena::new();
        let zero = variable(&mut arena, DeBruijnIndex::from(0));
        let one = variable(&mut arena, DeBruijnIndex::from(1));
        let linear = arena.value_variable(Zone::Linear, DeBruijnIndex::from(0));
        let pair = arena.value_tuple(&[zero, one]);
        let shared = arena.computation_return(pair);
        let linear_branch = arena.computation_return(linear);
        let case = arena.computation_case(zero, &[shared, linear_branch]);
        let bind = arena.computation_bind(shared, shared);
        let lambda = arena.computation_lambda(shared);
        let split = arena.computation_split(one, crate::ComponentCount::from(2_usize), shared);
        let empty_split =
            arena.computation_split(zero, crate::ComponentCount::from(0_usize), shared);
        for (root, expected) in [
            (case, vec![1_u32, 0, 2]),
            (bind, vec![1, 2, 0, 2]),
            (lambda, vec![0, 2]),
            (split, vec![2, 0, 1]),
            (empty_split, vec![1, 1, 2]),
        ] {
            let Node::Computation(rewritten) = Engine::new(&mut arena).run(
                Node::Computation(root),
                Binders::NONE,
                Rewrite::Shift(Binders::ONE),
            )
            else {
                panic!("computation");
            };
            let mut pending = vec![Node::Computation(rewritten)];
            let mut actual = Vec::new();
            let mut linear_seen = Vec::new();
            while let Some(node) = pending.pop() {
                match node {
                    | Node::Value(id) => match *arena.value(id).expect("a value child") {
                        | Value::Variable {
                            zone: Zone::Intuitionistic,
                            index,
                        } => actual.push(u32::from(index)),
                        | Value::Variable {
                            zone: Zone::Linear,
                            index,
                        } => linear_seen.push(u32::from(index)),
                        | Value::Tuple(ref components) => {
                            pending.extend(
                                components
                                    .iter()
                                    .rev()
                                    .map(|&component| Node::Value(component)),
                            );
                        },
                        | _ => panic!("the golden uses variables and pairs"),
                    },
                    | Node::Computation(id) => {
                        match *arena.computation(id).expect("a computation child") {
                            | crate::Computation::Lambda(body) => {
                                pending.push(Node::Computation(body));
                            },
                            | crate::Computation::Return(value) => {
                                pending.push(Node::Value(value));
                            },
                            | crate::Computation::Bind(bound, body) => {
                                pending.extend([Node::Computation(body), Node::Computation(bound)]);
                            },
                            | crate::Computation::Case {
                                scrutinee,
                                ref branches,
                            } => {
                                pending.extend(
                                    branches
                                        .iter()
                                        .rev()
                                        .map(|&branch| Node::Computation(branch)),
                                );
                                pending.push(Node::Value(scrutinee));
                            },
                            | crate::Computation::Split {
                                scrutinee, body, ..
                            } => {
                                pending.extend([Node::Computation(body), Node::Value(scrutinee)]);
                            },
                            | _ => panic!("the golden uses binding computations and return"),
                        }
                    },
                    | Node::ValueType(_) | Node::CompType(_) => panic!("the golden contains terms"),
                }
            }
            assert_eq!(expected, actual);
            assert_eq!(if root == case { vec![0] } else { vec![] }, linear_seen);
        }
        let domain = arena.value_type_element(zero, Level::zero());
        let codomain = arena.value_type_element(one, Level::zero());
        let static_pi = arena.value_type_static_pi(domain, codomain);
        let result = arena.comp_type_returner(domain);
        let mark = arena.watermark();
        assert_eq!(
            static_pi,
            shift_value_type(&mut arena, static_pi, Binders::NONE)
        );
        assert_eq!(result, shift_comp_type(&mut arena, result, Binders::NONE));
        assert_eq!(mark, arena.watermark());
        let shifted = shift_value_type(&mut arena, static_pi, Binders::ONE);
        let Some(&ValueType::StaticPi { domain, codomain }) = arena.value_type(shifted)
        else {
            panic!("static Pi");
        };
        for (child, index) in [(domain, 1_u32), (codomain, 2_u32)] {
            let Some(&ValueType::Element { code, .. }) = arena.value_type(child)
            else {
                panic!("a neutral decode");
            };
            assert_eq!(
                Some(&Value::Variable {
                    zone: Zone::Intuitionistic,
                    index: DeBruijnIndex::from(index)
                }),
                arena.value(code)
            );
        }
        let linear_type = arena.comp_type_element(linear, Level::zero());
        let mark = arena.watermark();
        assert_eq!(
            Maybe::Present(linear_type),
            strengthen_comp_type(&mut arena, linear_type)
        );
        assert_eq!(mark, arena.watermark());
    }

    #[test]
    fn a_fill_replaces_exactly_the_named_holes()
    {
        let mut arena = CoreArena::new();
        let named = arena.value_hole(HoleId::from(1_u32));
        let other = arena.value_hole(HoleId::from(2_u32));
        let computation_named = arena.computation_hole(HoleId::from(1_u32));
        let pair = arena.value_tuple(&[named, other]);
        let returned = arena.computation_return(pair);
        let subject = arena.computation_bind(computation_named, returned);
        let filling = variable(&mut arena, DeBruijnIndex::from(0_u32));
        let TermId::Computation(filled) = fill_hole(
            &mut arena,
            TermId::Computation(subject),
            HoleId::from(1_u32),
            TermId::Value(filling),
        )
        else {
            panic!("a fill keeps the subject's family");
        };
        let Some(&Computation::Bind(bound, body)) = arena.computation(filled)
        else {
            panic!("a filled bind");
        };
        assert_eq!(
            bound, computation_named,
            "a hole of the other family stands"
        );
        let Some(&Computation::Return(value)) = arena.computation(body)
        else {
            panic!("a filled return");
        };
        assert_eq!(
            arena.value(value),
            Some(&Value::Tuple([filling, other].into())),
            "the named hole takes the filling uncarried, and another name stands"
        );
        let unit = arena.value_unit();
        let mark = arena.watermark();
        assert_eq!(
            fill_hole(
                &mut arena,
                TermId::Value(unit),
                HoleId::from(1_u32),
                TermId::Value(filling)
            ),
            TermId::Value(unit)
        );
        assert_eq!(mark, arena.watermark(), "a hole-free subject mints nothing");
    }

    #[test]
    fn a_wrap_marks_exactly_the_named_nodes()
    {
        let mut arena = CoreArena::new();
        let occurrence = variable(&mut arena, DeBruijnIndex::from(0_u32));
        let unit = arena.value_unit();
        let pair = arena.value_tuple(&[occurrence, unit]);
        let returned = arena.computation_return(pair);
        let sites = BTreeMap::from([
            (TermId::Value(occurrence), MarkIndex::from(0_u32)),
            (TermId::Value(pair), MarkIndex::from(1_u32)),
            (TermId::Computation(returned), MarkIndex::from(2_u32)),
        ]);
        let TermId::Computation(wrapped) =
            wrap_marks(&mut arena, TermId::Computation(returned), &sites)
        else {
            panic!("a wrap keeps the subject's family");
        };
        let Some(&Computation::Mark { mark, body }) = arena.computation(wrapped)
        else {
            panic!("the named computation is marked");
        };
        assert_eq!(mark, MarkIndex::from(2_u32));
        let Some(&Computation::Return(value)) = arena.computation(body)
        else {
            panic!("the mark wraps the rebuilt return");
        };
        let Some(&Value::Mark { mark, body }) = arena.value(value)
        else {
            panic!("the named pair is marked");
        };
        assert_eq!(mark, MarkIndex::from(1_u32));
        let Some(&[first, second]) = arena.value(body).and_then(Value::components)
        else {
            panic!("the mark wraps the rebuilt pair");
        };
        assert_eq!(second, unit, "an unnamed sibling stands");
        assert_eq!(
            arena.value(first),
            Some(&Value::Mark {
                mark: MarkIndex::from(0_u32),
                body: occurrence,
            }),
            "a named variable is marked in place"
        );
        let mark = arena.watermark();
        assert_eq!(
            wrap_marks(&mut arena, TermId::Value(unit), &sites),
            TermId::Value(unit)
        );
        assert_eq!(mark, arena.watermark(), "an unnamed subject mints nothing");
    }

    /// Apply the constant `callee`, forced, to `argument`.
    ///
    /// # Specification
    /// trivial.
    fn call(
        arena: &mut CoreArena,
        callee: ConstantIndex,
        argument: ValueId,
    ) -> ComputationId
    {
        let callee = arena.value_constant(callee);
        let forced = arena.computation_force(callee);
        arena.computation_application(forced, argument)
    }

    /// A compact pre-order reading of the term formers the elaboration tests
    /// write, so a rebuilt term compares with the spelling it should have.
    ///
    /// # Specification
    /// trivial.
    fn term_text(
        arena: &CoreArena,
        root: ValueId,
    ) -> String
    {
        enum Piece
        {
            Value(ValueId),
            Computation(ComputationId),
            Text(&'static str),
        }
        let mut text = String::new();
        let mut pending = vec![Piece::Value(root)];
        while let Some(piece) = pending.pop() {
            let (head, children): (String, Vec<Piece>) = match piece {
                | Piece::Text(written) => {
                    text.push_str(written);
                    continue;
                },
                | Piece::Value(id) => match arena.value(id) {
                    | Some(&Value::Variable { index, .. }) => {
                        (format!("v{}", u32::from(index)), Vec::new())
                    },
                    | Some(&Value::Constant(constant)) => {
                        (format!("#{}", usize::from(constant)), Vec::new())
                    },
                    | Some(&Value::Thunk(body)) => ("thunk".into(), vec![Piece::Computation(body)]),
                    | Some(&Value::Nested(body)) => {
                        ("nested".into(), vec![Piece::Computation(body)])
                    },
                    | Some(&Value::Run(body)) => ("run".into(), vec![Piece::Computation(body)]),
                    | Some(&Value::Tuple(ref components)) => (
                        "tuple".into(),
                        components
                            .iter()
                            .map(|&component| Piece::Value(component))
                            .collect(),
                    ),
                    | Some(&Value::StaticApplication(head, argument)) => ("static".into(), vec![
                        Piece::Value(head),
                        Piece::Value(argument),
                    ]),
                    | _ => ("?".into(), Vec::new()),
                },
                | Piece::Computation(id) => match arena.computation(id) {
                    | Some(&Computation::Lambda(body)) => {
                        ("lambda".into(), vec![Piece::Computation(body)])
                    },
                    | Some(&Computation::Bind(bound, body)) => ("bind".into(), vec![
                        Piece::Computation(bound),
                        Piece::Computation(body),
                    ]),
                    | Some(&Computation::Return(value)) => {
                        ("return".into(), vec![Piece::Value(value)])
                    },
                    | Some(&Computation::Force(value)) => {
                        ("force".into(), vec![Piece::Value(value)])
                    },
                    | Some(&Computation::Application(head, argument)) => ("apply".into(), vec![
                        Piece::Computation(head),
                        Piece::Value(argument),
                    ]),
                    | Some(&Computation::Case {
                        scrutinee,
                        ref branches,
                    }) => (
                        "case".into(),
                        core::iter::once(Piece::Value(scrutinee))
                            .chain(branches.iter().map(|&branch| Piece::Computation(branch)))
                            .collect(),
                    ),
                    | _ => ("?".into(), Vec::new()),
                },
            };
            text.push_str(&head);
            if children.is_empty() {
                continue;
            }
            text.push('(');
            pending.push(Piece::Text(")"));
            for (position, child) in children.into_iter().enumerate().rev() {
                pending.push(child);
                if position > 0 {
                    pending.push(Piece::Text(","));
                }
            }
        }
        text
    }

    #[test]
    fn an_elaboration_runs_in_written_order_before_its_region()
    {
        let mut arena = CoreArena::new();
        let [first_x, inner_x, last_x] =
            [(); 3].map(|()| variable(&mut arena, DeBruijnIndex::from(0_u32)));
        let first = call(&mut arena, ConstantIndex::from(1_usize), first_x);
        let first = arena.value_nested(first);
        let inner = call(&mut arena, ConstantIndex::from(3_usize), inner_x);
        let inner = arena.value_nested(inner);
        let second = call(&mut arena, ConstantIndex::from(2_usize), inner);
        let second = arena.value_run(second);
        let head = call(&mut arena, ConstantIndex::from(0_usize), first);
        let spine = arena.computation_application(head, second);
        let region = arena.computation_application(spine, last_x);
        let lambda = arena.computation_lambda(region);
        let subject = arena.value_thunk(lambda);
        let nesting = BTreeMap::from([(first, Nesting::Run), (inner, Nesting::Run)]);
        let mut carried = Vec::new();
        let mut binds = Vec::new();
        let Ok(elaborated) =
            elaborate_nested_traced(&mut arena, subject, &nesting, &mut carried, &mut binds)
        else {
            panic!("every run stands in a computation");
        };
        assert_eq!(
            term_text(&arena, elaborated),
            "thunk(lambda(bind(apply(force(#1),v0),bind(bind(apply(force(#3),v1),apply(force(#2),v0)),apply(apply(apply(force(#0),v1),v0),v2)))))",
            "the head's run binds outermost, the argument's next carried past it, the run nested in the argument's own call binds inside that call, and the body reads each run by its bind and every free index past them all",
        );
        let runs: Vec<ValueId> = binds.iter().map(|&(run, _)| run).collect();
        assert_eq!(
            runs,
            [inner, second, first],
            "binds are minted innermost first"
        );
        let Some(&(_, outermost)) = binds.last()
        else {
            panic!("three binds");
        };
        assert!(
            carried.contains(&Carried::Computation(region, outermost)),
            "the region is reported as the binds that wrap it"
        );
    }

    #[test]
    fn an_elaboration_suspends_and_runs_as_decided()
    {
        let mut arena = CoreArena::new();
        let [suspended_x, run_x] =
            [(); 2].map(|()| variable(&mut arena, DeBruijnIndex::from(0_u32)));
        let suspended = call(&mut arena, ConstantIndex::from(1_usize), suspended_x);
        let suspended = arena.value_nested(suspended);
        let run = call(&mut arena, ConstantIndex::from(2_usize), run_x);
        let run = arena.value_nested(run);
        let pair = arena.value_tuple(&[suspended, run]);
        let returned = arena.computation_return(pair);
        let lambda = arena.computation_lambda(returned);
        let subject = arena.value_thunk(lambda);
        let nesting = BTreeMap::from([(suspended, Nesting::Thunk), (run, Nesting::Run)]);
        let mut carried = Vec::new();
        let mut binds = Vec::new();
        let minted = arena.watermark();
        let Ok(elaborated) =
            elaborate_nested_traced(&mut arena, subject, &nesting, &mut carried, &mut binds)
        else {
            panic!("every run stands in a computation");
        };
        let reported: Vec<Node> = carried
            .iter()
            .map(|pair| match *pair {
                | Carried::Value(_, written) => Node::Value(written),
                | Carried::Computation(_, written) => Node::Computation(written),
                | Carried::ValueType(_, written) => Node::ValueType(written),
                | Carried::CompType(_, written) => Node::CompType(written),
            })
            .chain(binds.iter().map(|&(_, bind)| Node::Computation(bind)))
            .collect();
        let unreported: Vec<Node> = arena
            .values_since(minted)
            .map(Node::Value)
            .chain(arena.computations_since(minted).map(Node::Computation))
            .filter(|node| !reported.contains(node))
            .collect();
        assert_eq!(
            unreported,
            [],
            "every node the elaboration minted is reported beside a node it stands for, the \
             region's body closed around the suspension among them"
        );
        assert_eq!(
            term_text(&arena, elaborated),
            "thunk(lambda(bind(apply(force(#2),v0),return(tuple(thunk(apply(force(#1),v1)),v0)))))",
            "the suspension stays in place as a thunk, carried past the run's bind",
        );
        assert_eq!(binds.len(), 1, "only the run mints a bind");
        let mark = arena.watermark();
        let Ok(unchanged) = elaborate_nested_traced(
            &mut arena,
            pair,
            &BTreeMap::new(),
            &mut Vec::new(),
            &mut binds,
        )
        else {
            panic!("an undecided nested computation is not a run");
        };
        assert_eq!(unchanged, pair, "nothing decided, nothing rebuilt");
        assert_eq!(mark, arena.watermark(), "and nothing minted");
    }

    #[test]
    fn an_elaboration_never_hoists_out_of_a_thunk_or_an_arm()
    {
        let mut arena = CoreArena::new();
        let [scrutinee, armed_x, suspended_x] =
            [(); 3].map(|()| variable(&mut arena, DeBruijnIndex::from(0_u32)));
        let armed = call(&mut arena, ConstantIndex::from(1_usize), armed_x);
        let armed = arena.value_nested(armed);
        let suspended = call(&mut arena, ConstantIndex::from(2_usize), suspended_x);
        let suspended = arena.value_nested(suspended);
        let first_arm = arena.computation_return(armed);
        let inner = arena.computation_return(suspended);
        let thunk = arena.value_thunk(inner);
        let second_arm = arena.computation_return(thunk);
        let case = arena.computation_case(scrutinee, &[first_arm, second_arm]);
        let lambda = arena.computation_lambda(case);
        let subject = arena.value_thunk(lambda);
        let nesting = BTreeMap::from([(armed, Nesting::Run), (suspended, Nesting::Run)]);
        let Ok(elaborated) = elaborate_nested_traced(
            &mut arena,
            subject,
            &nesting,
            &mut Vec::new(),
            &mut Vec::new(),
        )
        else {
            panic!("every run stands in a computation");
        };
        assert_eq!(
            term_text(&arena, elaborated),
            "thunk(lambda(case(v0,bind(apply(force(#1),v0),return(v0)),return(thunk(bind(apply(force(#2),v0),return(v0)))))))",
            "an arm's run binds inside the arm and a thunk's inside the thunk; the case stands as written",
        );
    }

    #[test]
    fn a_run_in_no_computation_is_unenclosed()
    {
        let mut arena = CoreArena::new();
        let argument = variable(&mut arena, DeBruijnIndex::from(0_u32));
        let computation = call(&mut arena, ConstantIndex::from(1_usize), argument);
        let nested = arena.value_nested(computation);
        let definition = arena.value_tuple(&[nested]);
        let refused = elaborate_nested_traced(
            &mut arena,
            definition,
            &BTreeMap::from([(nested, Nesting::Run)]),
            &mut Vec::new(),
            &mut Vec::new(),
        );
        assert_eq!(
            refused.map_err(Unenclosed::run),
            Err(nested),
            "a definition's own value has no computation to run before"
        );
        let Ok(suspended) = elaborate_nested_traced(
            &mut arena,
            definition,
            &BTreeMap::from([(nested, Nesting::Thunk)]),
            &mut Vec::new(),
            &mut Vec::new(),
        )
        else {
            panic!("a suspension needs no computation around it");
        };
        assert_eq!(
            term_text(&arena, suspended),
            "tuple(thunk(apply(force(#1),v0)))"
        );
        let operator = arena.value_constant(ConstantIndex::from(0_usize));
        let run = arena.value_run(computation);
        let erased = arena.value_static_application(operator, run);
        let returned = arena.computation_return(erased);
        let subject = arena.value_thunk(returned);
        let refused = elaborate_nested_traced(
            &mut arena,
            subject,
            &BTreeMap::new(),
            &mut Vec::new(),
            &mut Vec::new(),
        );
        assert_eq!(
            refused.map_err(Unenclosed::run),
            Err(run),
            "static content is erased before anything runs, so no run hoists out of it"
        );
    }

    #[test]
    fn a_decision_no_term_reaches_is_unenclosed()
    {
        let mut arena = CoreArena::new();
        let argument = variable(&mut arena, DeBruijnIndex::from(0_u32));
        let computation = call(&mut arena, ConstantIndex::from(1_usize), argument);
        let nested = arena.value_nested(computation);
        let indexed = arena.value_type_element(nested, Level::zero());
        let constructed = arena.value_constructor(
            indexed,
            gandr_kernel_term::ConstructorTag::from(0_usize),
            alloc::vec::Vec::new(),
        );
        let returned = arena.computation_return(constructed);
        let subject = arena.value_thunk(returned);
        for decided in [Nesting::Run, Nesting::Thunk] {
            assert_eq!(
                elaborate_nested_traced(
                    &mut arena,
                    subject,
                    &BTreeMap::from([(nested, decided)]),
                    &mut Vec::new(),
                    &mut Vec::new(),
                )
                .map_err(Unenclosed::run),
                Err(nested),
                "a computation standing in a type has nothing to run before or suspend in"
            );
        }
    }

    #[test]
    fn an_environment_substitution_replaces_every_free_index()
    {
        let mut arena = CoreArena::new();
        let entries = [
            arena.value_constant(ConstantIndex::from(5_usize)),
            variable(&mut arena, DeBruijnIndex::from(0_u32)),
        ];
        let [zero, one, two, three] =
            [0_u32, 1, 2, 3].map(|index| variable(&mut arena, DeBruijnIndex::from(index)));
        let top = arena.value_tuple(&[zero, one]);
        let TermId::Value(at_top) =
            substitute_environment(&mut arena, TermId::Value(top), &entries)
        else {
            panic!("a substitution keeps the subject's family");
        };
        assert_eq!(
            arena.value(at_top),
            Some(&Value::Tuple([entries[0], entries[1]].into()))
        );
        let inner = arena.value_tuple(&[zero, one]);
        let outer = arena.value_tuple(&[two, three]);
        let both = arena.value_tuple(&[inner, outer]);
        let returned = arena.computation_return(both);
        let lambda = arena.computation_lambda(returned);
        let TermId::Computation(substituted) =
            substitute_environment(&mut arena, TermId::Computation(lambda), &entries)
        else {
            panic!("a substitution keeps the subject's family");
        };
        let Some(&Computation::Lambda(body)) = arena.computation(substituted)
        else {
            panic!("a substituted lambda");
        };
        let Some(&Computation::Return(value)) = arena.computation(body)
        else {
            panic!("a substituted return");
        };
        let Some(&[inner, outer]) = arena.value(value).and_then(Value::components)
        else {
            panic!("a substituted pair");
        };
        let index_of = |arena: &CoreArena, id| match arena.value(id) {
            | Some(&Value::Variable {
                zone: Zone::Intuitionistic,
                index,
            }) => Some(u32::from(index)),
            | Some(_) | None => None,
        };
        let Some(&[bound, first_entry]) = arena.value(inner).and_then(Value::components)
        else {
            panic!("the inner pair");
        };
        assert_eq!(
            index_of(&arena, bound),
            Some(0),
            "the lambda's own index stands"
        );
        assert_eq!(first_entry, entries[0], "a closed entry is placed as it is");
        let Some(&[second_entry, past]) = arena.value(outer).and_then(Value::components)
        else {
            panic!("the outer pair");
        };
        assert_eq!(
            index_of(&arena, second_entry),
            Some(1),
            "an open entry is carried under the binder"
        );
        assert_eq!(
            index_of(&arena, past),
            Some(1),
            "an index past the environment is lowered by its length"
        );
        let mark = arena.watermark();
        assert_eq!(
            substitute_environment(&mut arena, TermId::Computation(lambda), &[]),
            TermId::Computation(lambda)
        );
        assert_eq!(
            mark,
            arena.watermark(),
            "an empty environment mints nothing"
        );
    }

    #[test]
    fn a_traced_substitution_reports_every_node_it_rewrote()
    {
        let mut arena = CoreArena::new();
        let entry = variable(&mut arena, DeBruijnIndex::from(4_u32));
        let closed = arena.value_constant(ConstantIndex::from(5_usize));
        let [bound, free] =
            [0_u32, 1].map(|index| variable(&mut arena, DeBruijnIndex::from(index)));
        let triple = arena.value_tuple(&[bound, free, closed]);
        let returned = arena.computation_return(triple);
        let lambda = arena.computation_lambda(returned);
        let mut carried = Vec::new();
        let TermId::Computation(substituted) = substitute_environment_traced(
            &mut arena,
            TermId::Computation(lambda),
            &[entry],
            &mut carried,
        )
        else {
            panic!("a substitution keeps the subject's family");
        };
        let Some(&Computation::Lambda(body)) = arena.computation(substituted)
        else {
            panic!("a substituted lambda");
        };
        let Some(&Computation::Return(value)) = arena.computation(body)
        else {
            panic!("a substituted return");
        };
        let Some(&[kept, shifted, constant]) = arena.value(value).and_then(Value::components)
        else {
            panic!("a substituted triple");
        };
        assert_eq!(kept, bound, "the lambda's own index is kept");
        assert_eq!(constant, closed, "a closed value is kept");
        assert_eq!(
            arena.value(shifted),
            Some(&Value::Variable {
                zone: Zone::Intuitionistic,
                index: DeBruijnIndex::from(5_u32),
            }),
            "the entry is carried under the lambda"
        );
        carried.sort_unstable();
        let mut expected = vec![
            Carried::Value(entry, shifted),
            Carried::Value(free, shifted),
            Carried::Value(triple, value),
            Carried::Computation(returned, body),
            Carried::Computation(lambda, substituted),
        ];
        expected.sort_unstable();
        assert_eq!(
            carried, expected,
            "every rewritten node is reported beside its source, and no kept one"
        );
        let mark = arena.watermark();
        let mut none = Vec::new();
        assert_eq!(
            substitute_environment_traced(&mut arena, TermId::Computation(lambda), &[], &mut none),
            TermId::Computation(lambda)
        );
        assert!(
            none.is_empty() && mark == arena.watermark(),
            "an empty environment mints and reports nothing"
        );
    }

    #[test]
    fn a_renaming_replaces_exactly_the_named_constants_and_atoms()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let renamed_atom = arena.value_type_abstract(ConstantIndex::from(0_usize));
        let kept_atom = arena.value_type_abstract(ConstantIndex::from(1_usize));
        let renamed_constant = arena.value_constant(ConstantIndex::from(2_usize));
        let kept_constant = arena.value_constant(ConstantIndex::from(3_usize));
        let bound = variable(&mut arena, DeBruijnIndex::from(0_u32));
        let quoted = arena.value_quote(renamed_atom);
        let kept_quote = arena.value_quote(kept_atom);
        let tuple =
            arena.value_tuple(&[bound, renamed_constant, kept_constant, quoted, kept_quote]);
        let returned = arena.computation_return(tuple);
        let lambda = arena.computation_lambda(returned);
        let thunk = arena.value_thunk(lambda);
        let mut renaming = Renaming::new();
        renaming.constant(ConstantIndex::from(2_usize), ConstantIndex::from(7_usize));
        renaming.atom(ConstantIndex::from(0_usize), integer);
        let mut carried = Vec::new();
        let renamed = rename_value_traced(&mut arena, thunk, &renaming, &mut carried);
        let Some(&Value::Thunk(body)) = arena.value(renamed)
        else {
            panic!("a renamed thunk");
        };
        let Some(&Computation::Lambda(inner)) = arena.computation(body)
        else {
            panic!("a renamed lambda");
        };
        let Some(&Computation::Return(value)) = arena.computation(inner)
        else {
            panic!("a renamed return");
        };
        let Some(&[variable_kept, constant, other, code, other_code]) =
            arena.value(value).and_then(Value::components)
        else {
            panic!("a renamed tuple");
        };
        assert_eq!(variable_kept, bound, "a bound variable is no constant");
        assert_eq!(
            arena.value(constant),
            Some(&Value::Constant(ConstantIndex::from(7_usize))),
            "the named constant is replaced at every depth"
        );
        assert_eq!(
            other, kept_constant,
            "a constant the renaming does not name stands"
        );
        assert_eq!(
            arena.value(code),
            Some(&Value::Quote(integer)),
            "a quoted atom reads as the type it is renamed to"
        );
        assert_eq!(
            other_code, kept_quote,
            "an atom the renaming does not name stands"
        );
        carried.sort_unstable();
        let mut expected = vec![
            Carried::Value(renamed_constant, constant),
            Carried::ValueType(renamed_atom, integer),
            Carried::Value(quoted, code),
            Carried::Value(tuple, value),
            Carried::Computation(returned, inner),
            Carried::Computation(lambda, body),
            Carried::Value(thunk, renamed),
        ];
        expected.sort_unstable();
        assert_eq!(
            carried, expected,
            "every rewritten node is reported, and no kept one"
        );
        let mut type_carried = Vec::new();
        assert_eq!(
            rename_value_type_traced(&mut arena, renamed_atom, &renaming, &mut type_carried),
            integer,
            "an atom standing alone is the type it is renamed to"
        );
        assert_eq!(
            rename_value_type_traced(&mut arena, kept_atom, &renaming, &mut type_carried),
            kept_atom
        );
        assert_eq!(type_carried, vec![Carried::ValueType(
            renamed_atom,
            integer
        )]);
    }

    #[test]
    fn a_traced_shift_raises_only_past_its_scope()
    {
        let mut arena = CoreArena::new();
        let [own, kept, past] =
            [0_u32, 1, 2].map(|index| variable(&mut arena, DeBruijnIndex::from(index)));
        let triple = arena.value_tuple(&[own, kept, past]);
        let returned = arena.computation_return(triple);
        let lambda = arena.computation_lambda(returned);
        let mut carried = Vec::new();
        let shifted = super::shift_computation_under_traced(
            &mut arena,
            lambda,
            Binders::ONE,
            Binders::from(2_u32),
            &mut carried,
        );
        let Some(&Computation::Lambda(body)) = arena.computation(shifted)
        else {
            panic!("a shifted lambda");
        };
        let Some(&Computation::Return(value)) = arena.computation(body)
        else {
            panic!("a shifted return");
        };
        let Some(&[first, second, raised]) = arena.value(value).and_then(Value::components)
        else {
            panic!("a shifted triple");
        };
        assert_eq!(
            (first, second),
            (own, kept),
            "the lambda's own index and the one inside the scope stand"
        );
        assert_eq!(
            arena.value(raised),
            Some(&Value::Variable {
                zone: Zone::Intuitionistic,
                index: DeBruijnIndex::from(4_u32),
            }),
            "an index past the scope is raised by the amount"
        );
        carried.sort_unstable();
        let mut expected = vec![
            Carried::Value(past, raised),
            Carried::Value(triple, value),
            Carried::Computation(returned, body),
            Carried::Computation(lambda, shifted),
        ];
        expected.sort_unstable();
        assert_eq!(
            carried, expected,
            "exactly the rewritten nodes are reported"
        );
        let mark = arena.watermark();
        let mut none = Vec::new();
        assert_eq!(
            super::shift_computation_under_traced(
                &mut arena,
                lambda,
                Binders::ONE,
                Binders::NONE,
                &mut none
            ),
            lambda
        );
        assert!(
            none.is_empty() && mark == arena.watermark(),
            "no amount mints and reports nothing"
        );
    }

    #[test]
    fn a_traced_type_shift_reports_each_copy()
    {
        let mut arena = CoreArena::new();
        let [kept, past] = [0_u32, 1].map(|index| variable(&mut arena, DeBruijnIndex::from(index)));
        let carrier = arena.value_type_unit();
        let path = arena.value_type_path(carrier, kept, past);
        let returner = arena.comp_type_returner(path);
        let mut carried = Vec::new();
        let shifted = super::shift_comp_type_under_traced(
            &mut arena,
            returner,
            Binders::ONE,
            Binders::ONE,
            &mut carried,
        );
        let Some(&CompType::Returner { result, .. }) = arena.comp_type(shifted)
        else {
            panic!("a shifted returner");
        };
        let Some(&ValueType::Path { left, right, .. }) = arena.value_type(result)
        else {
            panic!("a shifted path type");
        };
        assert_eq!(left, kept, "the endpoint inside the scope stands");
        assert_eq!(
            arena.value(right),
            Some(&Value::Variable {
                zone: Zone::Intuitionistic,
                index: DeBruijnIndex::from(2_u32),
            }),
            "the endpoint past the scope is raised"
        );
        carried.sort_unstable();
        let mut expected = vec![
            Carried::Value(past, right),
            Carried::ValueType(path, result),
            Carried::CompType(returner, shifted),
        ];
        expected.sort_unstable();
        assert_eq!(
            carried, expected,
            "exactly the rewritten nodes are reported"
        );
        let mark = arena.watermark();
        let mut none = Vec::new();
        assert_eq!(
            super::shift_comp_type_under_traced(
                &mut arena,
                returner,
                Binders::ONE,
                Binders::NONE,
                &mut none
            ),
            returner
        );
        assert!(
            none.is_empty() && mark == arena.watermark(),
            "no amount mints and reports nothing"
        );
    }

    #[test]
    fn a_traced_instantiation_replaces_its_binder()
    {
        let mut arena = CoreArena::new();
        let argument = variable(&mut arena, DeBruijnIndex::from(3_u32));
        let [own, binder, outer] =
            [0_u32, 1, 2].map(|index| variable(&mut arena, DeBruijnIndex::from(index)));
        let triple = arena.value_tuple(&[own, binder, outer]);
        let returned = arena.computation_return(triple);
        let lambda = arena.computation_lambda(returned);
        let mut carried = Vec::new();
        let instantiated =
            super::instantiate_computation_traced(&mut arena, lambda, argument, &mut carried);
        let Some(&Computation::Lambda(body)) = arena.computation(instantiated)
        else {
            panic!("an instantiated lambda");
        };
        let Some(&Computation::Return(value)) = arena.computation(body)
        else {
            panic!("an instantiated return");
        };
        let Some(&[kept, placed, lowered]) = arena.value(value).and_then(Value::components)
        else {
            panic!("an instantiated triple");
        };
        let index_of = |arena: &CoreArena, id| match arena.value(id) {
            | Some(&Value::Variable {
                zone: Zone::Intuitionistic,
                index,
            }) => Some(u32::from(index)),
            | Some(_) | None => None,
        };
        assert_eq!(kept, own, "the lambda's own index stands");
        assert_eq!(
            index_of(&arena, placed),
            Some(4),
            "the binder is the argument, carried under the lambda"
        );
        assert_eq!(
            index_of(&arena, lowered),
            Some(1),
            "an index past the binder is lowered by one"
        );
        carried.sort_unstable();
        let mut expected = vec![
            Carried::Value(argument, placed),
            Carried::Value(binder, placed),
            Carried::Value(outer, lowered),
            Carried::Value(triple, value),
            Carried::Computation(returned, body),
            Carried::Computation(lambda, instantiated),
        ];
        expected.sort_unstable();
        assert_eq!(
            carried, expected,
            "exactly the rewritten nodes are reported"
        );
    }
}
