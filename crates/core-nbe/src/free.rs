//! Outward counts: the free de Bruijn indices of a core term, and the sorted
//! sets the duplication walk and the overlay evaluator read them through.
//!
//! # One answer per node, computed once
//!
//! [`FreeIndices`] walks a core term in post-order over a heap task stack and
//! keeps one answer per node it reaches, so a node a DAG reaches along many
//! paths is answered once and the walk costs the DAG, never its unfolding. A
//! binder's body contributes its indices one lower, the binder's own index
//! dropped: a lambda's body, a bind's continuation and each branch of a case
//! bind one intuitionistic variable. No former binds into the linear zone, so a
//! linear index passes every binder unchanged.
//!
//! # A set is a sorted vector
//!
//! [`Outward`] holds its counts sorted and once each, so a union is a merge and
//! a membership test a binary search.
//!
//! `economy: one owned set per node answered, so a term whose every node reads
//! many indices costs their product in memory; share the sets as an
//! id-addressed persistent structure when a workload meets it`.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use core::cmp::Ordering;

use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::Zone;
use gandr_kernel_term::DeBruijnIndex;

/// Whether a set holds a count.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Membership
{
    /// The set holds it.
    Held,
    /// The set does not.
    Absent,
}

/// How many binders or frames a set is read past: the amount each of its
/// counts is lowered by, the counts below it dropped.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Lowering(u32);

impl Lowering
{
    /// Past no binder.
    pub(crate) const NONE: Self = Self(0_u32);
    /// Past one binder or one frame.
    pub(crate) const ONE: Self = Self(1_u32);
}

impl From<Lowering> for u32
{
    /// How many binders or frames `lowering` reads past.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(lowering: Lowering) -> Self
    {
        lowering.0
    }
}

/// A sorted set of outward counts, each held once: the free indices of a term,
/// or the share distances an overlay subtree's occurrences reach past it.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Outward<Count>
{
    /// The counts, ascending, each once.
    counts: Vec<Count>,
}

impl<Count> Default for Outward<Count>
{
    /// The empty set.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self { counts: Vec::new() }
    }
}

impl<Count> Outward<Count>
where
    Count: Copy + Ord + From<u32>,
    u32: From<Count>,
{
    /// The set holding `count` alone.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn single(count: Count) -> Self
    {
        Self {
            counts: Vec::from([count]),
        }
    }

    /// Whether the set holds `count`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Membership::Held`] exactly when `count` is among the
    ///   counts.
    /// - provides: the binary search a rib test and a configuration key read a
    ///   set through.
    /// - fails: never.
    /// - panics: none.
    pub(crate) fn holds(
        &self,
        count: Count,
    ) -> Membership
    {
        match self.counts.binary_search(&count) {
            | Ok(_) => Membership::Held,
            | Err(_) => Membership::Absent,
        }
    }

    /// The least count, when the set holds any.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn least(&self) -> Option<Count>
    {
        self.counts.first().copied()
    }

    /// The counts, ascending.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn counts(&self) -> &[Count]
    {
        &self.counts
    }

    /// Add every count of `other`, each lowered by `lowering`, the counts
    /// below `lowering` dropped.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the set is the union of what it held and the lowered counts
    ///   of `other`, ascending and each once.
    /// - provides: the one combinator a node's set is built from its children's
    ///   with: a binder lowers its body's indices by one, a share its body's
    ///   distances by one, and every other child joins at no lowering.
    /// - fails: never.
    /// - panics: none.
    /// - intension: one merge of two ascending sequences, so the cost is the
    ///   two sizes summed.
    pub(crate) fn join_lowered(
        &mut self,
        other: &Self,
        lowering: Lowering,
    )
    {
        if other.counts.is_empty() {
            return;
        }
        let mut lowered = other
            .counts
            .iter()
            .filter_map(|&count| u32::from(count).checked_sub(lowering.0).map(Count::from))
            .peekable();
        let mut held = self.counts.iter().copied().peekable();
        let mut merged = Vec::with_capacity(self.counts.len().saturating_add(other.counts.len()));
        loop {
            match (held.peek().copied(), lowered.peek().copied()) {
                | (None, None) => break,
                | (Some(mine), None) => {
                    merged.push(mine);
                    held.next();
                },
                | (None, Some(theirs)) => {
                    merged.push(theirs);
                    lowered.next();
                },
                | (Some(mine), Some(theirs)) => match mine.cmp(&theirs) {
                    | Ordering::Less => {
                        merged.push(mine);
                        held.next();
                    },
                    | Ordering::Greater => {
                        merged.push(theirs);
                        lowered.next();
                    },
                    | Ordering::Equal => {
                        merged.push(mine);
                        held.next();
                        lowered.next();
                    },
                },
            }
        }
        self.counts = merged;
    }
}

/// A core value or computation, by id: the two families a free index can occur
/// in.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum CoreTerm
{
    /// A core value.
    Value(ValueId),
    /// A core computation.
    Computation(ComputationId),
}

/// The free indices of one core term, per zone, each counted from where the
/// term stands.
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct Free
{
    /// The free intuitionistic indices.
    intuitionistic: Outward<DeBruijnIndex>,
    /// The free linear indices.
    linear: Outward<DeBruijnIndex>,
}

impl Free
{
    /// The free intuitionistic indices.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn intuitionistic(&self) -> &Outward<DeBruijnIndex>
    {
        &self.intuitionistic
    }

    /// The free linear indices.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn linear(&self) -> &Outward<DeBruijnIndex>
    {
        &self.linear
    }

    /// The free indices of one variable.
    ///
    /// # Specification
    /// trivial.
    fn variable(
        zone: Zone,
        index: DeBruijnIndex,
    ) -> Self
    {
        match zone {
            | Zone::Intuitionistic => Self {
                intuitionistic: Outward::single(index),
                linear: Outward::default(),
            },
            | Zone::Linear => Self {
                intuitionistic: Outward::default(),
                linear: Outward::single(index),
            },
        }
    }

    /// Add the free indices of a child standing under `binders`
    /// intuitionistic binders.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the intuitionistic indices gain the child's lowered by
    ///   `binders`, its bound ones dropped; the linear indices gain the child's
    ///   unchanged, since no former binds into the linear zone.
    /// - provides: the one step a node's answer is assembled from its
    ///   children's.
    /// - fails: never.
    /// - panics: none.
    fn join_under(
        &mut self,
        child: &Self,
        binders: Lowering,
    )
    {
        self.intuitionistic
            .join_lowered(&child.intuitionistic, binders);
        self.linear.join_lowered(&child.linear, Lowering::NONE);
    }
}

/// Why a term's free indices could not be read.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum FreeFault
{
    /// A term id named no node of the core arena.
    Dangling,
    /// A node was assembled before a child it reads was answered. Unreachable
    /// while every assembly is pushed beneath its children's entries; kept so
    /// the walk fails closed rather than answering.
    MachineInvariant,
}

/// One pending step of the analysis.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Visit
{
    /// Answer a node, or queue its children and its assembly.
    Enter(CoreTerm),
    /// Assemble a node's answer from its children's.
    Assemble(CoreTerm),
}

/// The free indices of every core term asked, each node computed once.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct FreeIndices
{
    /// One answer per node reached so far.
    answered: BTreeMap<CoreTerm, Free>,
}

impl FreeIndices
{
    /// The free indices of `term` in `core`.
    ///
    /// # Specification
    /// - requires: every term asked of one analysis lives in `core`.
    /// - ensures: on success, the indices of each zone that `term` reads
    ///   without binding, counted from where `term` stands; every node the walk
    ///   reached keeps its answer, so a later question over a shared node costs
    ///   nothing.
    /// - provides: the free-index reading the duplication walk tests a rib with
    ///   and the overlay evaluator keys a configuration with.
    /// - fails: [`FreeFault::Dangling`] when a reached id names no node of
    ///   `core`, [`FreeFault::MachineInvariant`] when the walk's own order
    ///   breaks.
    /// - panics: none.
    /// - intension: one post-order walk on a heap stack, entering each node
    ///   once.
    ///
    /// # Errors
    /// - [`FreeFault::Dangling`] — a reached id does not resolve.
    /// - [`FreeFault::MachineInvariant`] — the walk's order broke.
    ///
    /// # Termination
    /// - reason: the `while let` below pops one visit per iteration and pushes
    ///   only the children of a node the core arena holds.
    /// - measure: the visits pending plus twice the nodes not yet answered.
    /// - boundedness: a node is entered at most once per parent edge before it
    ///   is answered, and never past it, so the walk is bounded by the term's
    ///   DAG.
    /// - input recursion: none.
    pub(crate) fn of(
        &mut self,
        core: &CoreArena,
        term: CoreTerm,
    ) -> Result<&Free, FreeFault>
    {
        if !self.answered.contains_key(&term) {
            self.answer(core, term)?;
        }
        self.answered.get(&term).ok_or(FreeFault::MachineInvariant)
    }

    /// Answer `term` and everything beneath it not yet answered.
    ///
    /// # Specification
    /// - requires: as [`FreeIndices::of`].
    /// - ensures: on success `term` and every node beneath it are answered.
    /// - provides: the walk behind [`FreeIndices::of`].
    /// - fails: as [`FreeIndices::of`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`FreeIndices::of`].
    fn answer(
        &mut self,
        core: &CoreArena,
        term: CoreTerm,
    ) -> Result<(), FreeFault>
    {
        let mut visits = Vec::from([Visit::Enter(term)]);
        while let Some(visit) = visits.pop() {
            match visit {
                | Visit::Enter(node) => {
                    if self.answered.contains_key(&node) {
                        continue;
                    }
                    let below = Children::of(core, node)?;
                    visits.push(Visit::Assemble(node));
                    for (child, _) in below.listed.into_iter().rev().flatten() {
                        visits.push(Visit::Enter(child));
                    }
                },
                | Visit::Assemble(node) => {
                    if self.answered.contains_key(&node) {
                        continue;
                    }
                    let free = self.assemble(core, node)?;
                    self.answered.insert(node, free);
                },
            }
        }
        Ok(())
    }

    /// Assemble `node`'s answer from its children's.
    ///
    /// # Specification
    /// - requires: every child of `node` is answered.
    /// - ensures: a variable reads its own index in its zone; a leaf reads
    ///   nothing; a lambda's body, a bind's continuation and a case's branches
    ///   join one binder lower; every other child joins unchanged.
    /// - provides: the per-former rule of the analysis.
    /// - fails: [`FreeFault::Dangling`] when `node` does not resolve, and
    ///   [`FreeFault::MachineInvariant`] when a child is not answered.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`FreeFault::Dangling`] — `node` does not resolve.
    /// - [`FreeFault::MachineInvariant`] — a child is not answered.
    fn assemble(
        &self,
        core: &CoreArena,
        node: CoreTerm,
    ) -> Result<Free, FreeFault>
    {
        let mut free = Free::default();
        if let CoreTerm::Value(id) = node {
            let held = core.value(id).ok_or(FreeFault::Dangling)?;
            if let Value::Variable { zone, index } = *held {
                free = Free::variable(zone, index);
            }
        }
        let below = Children::of(core, node)?;
        for (child, binders) in below.listed.into_iter().flatten() {
            let answered = self.read(child)?;
            free.join_under(answered, binders);
        }
        Ok(free)
    }

    /// The answer a child already has.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the answer kept for `child`.
    /// - provides: the checked read [`FreeIndices::assemble`] reads children
    ///   through.
    /// - fails: [`FreeFault::MachineInvariant`] when `child` is not answered.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`FreeFault::MachineInvariant`] — `child` is not answered.
    fn read(
        &self,
        child: CoreTerm,
    ) -> Result<&Free, FreeFault>
    {
        self.answered.get(&child).ok_or(FreeFault::MachineInvariant)
    }
}

/// A core term's children, left to right, each with the intuitionistic binders
/// it stands under.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Children
{
    /// Up to three children, the absent ones last.
    listed: [Option<(CoreTerm, Lowering)>; 3],
}

impl Children
{
    /// The children of `node`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each child the core former names, left to right: a lambda's
    ///   body, a bind's continuation and a case's branches under one binder,
    ///   every other child under none, and a leaf none.
    /// - provides: the one reading of the core formers' arity and binding the
    ///   walk and the assembly share.
    /// - fails: [`FreeFault::Dangling`] when `node` does not resolve.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`FreeFault::Dangling`] — `node` does not resolve.
    fn of(
        core: &CoreArena,
        node: CoreTerm,
    ) -> Result<Self, FreeFault>
    {
        let listed = match node {
            | CoreTerm::Value(id) => {
                let held = core.value(id).ok_or(FreeFault::Dangling)?;
                match *held {
                    | Value::Variable { .. }
                    | Value::Constant(_)
                    | Value::Unit
                    | Value::Literal(_) => [None, None, None],
                    | Value::Pair(first, second) => [
                        Some((CoreTerm::Value(first), Lowering::NONE)),
                        Some((CoreTerm::Value(second), Lowering::NONE)),
                        None,
                    ],
                    | Value::Injection(_, body) | Value::Lift { body, .. } => {
                        [Some((CoreTerm::Value(body), Lowering::NONE)), None, None]
                    },
                    | Value::Thunk(body) => [
                        Some((CoreTerm::Computation(body), Lowering::NONE)),
                        None,
                        None,
                    ],
                }
            },
            | CoreTerm::Computation(id) => {
                let held = core.computation(id).ok_or(FreeFault::Dangling)?;
                match *held {
                    | Computation::Lambda(body) => [
                        Some((CoreTerm::Computation(body), Lowering::ONE)),
                        None,
                        None,
                    ],
                    | Computation::Application(head, argument) => [
                        Some((CoreTerm::Computation(head), Lowering::NONE)),
                        Some((CoreTerm::Value(argument), Lowering::NONE)),
                        None,
                    ],
                    | Computation::Return(value) | Computation::Force(value) => {
                        [Some((CoreTerm::Value(value), Lowering::NONE)), None, None]
                    },
                    | Computation::Bind(bound, body) => [
                        Some((CoreTerm::Computation(bound), Lowering::NONE)),
                        Some((CoreTerm::Computation(body), Lowering::ONE)),
                        None,
                    ],
                    | Computation::Case {
                        scrutinee,
                        on_left,
                        on_right,
                    } => [
                        Some((CoreTerm::Value(scrutinee), Lowering::NONE)),
                        Some((CoreTerm::Computation(on_left), Lowering::ONE)),
                        Some((CoreTerm::Computation(on_right), Lowering::ONE)),
                    ],
                }
            },
        };
        Ok(Self { listed })
    }
}
