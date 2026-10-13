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
//! bind one intuitionistic variable. A quote carries a type into a term, and a
//! type reads indices through the codes its decodes hold, so the walk descends
//! through the quoted type too, a dependent arrow's codomain binding one
//! variable. A session fork binds one linear variable in its child and one in
//! its parent, and every other session action reads its endpoint as a linear
//! occurrence; every other binder leaves a linear index unchanged.
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

use anodized::spec;
use gandr_core_term::CompType;
use gandr_core_term::CompTypeId;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::session::SessionAction;
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
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the finite set model probes present counts and holes
    ///   at zero, interior positions and the ceiling; reversing membership or
    ///   searching a malformed order changes an answer. The predicate reads the
    ///   one slot the ascending order places `count` at, found by a lower-bound
    ///   partition rather than the body's equality search.
    /// - witness: `free::tests::lowered_union_agrees_with_a_set_model`
    #[spec(ensures: |ret| matches!(ret, Membership::Held)
        == (self.counts.get(self.counts.partition_point(|held| *held < count)) == Some(&count)))]
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
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every pair of subsets of four boundary counts is
    ///   joined at zero, one, two and maximal lowering against an independent
    ///   ordered-set union; dropping an old count, retaining a bound count,
    ///   duplicating an overlap or wrapping subtraction changes the set.
    /// - witness: `free::tests::lowered_union_agrees_with_a_set_model`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body merges both sequences once; the check reads the merged set once and searches it once per count of `other`"
        )
    )]
    #[spec(
        captures: entry_length = self.counts.len(),
        ensures: self.counts.len() >= entry_length
            && self.counts.windows(2).all(|pair| matches!(pair, [left, right] if left < right))
            && other.counts.iter().all(|&count| u32::from(count).checked_sub(lowering.0)
                .is_none_or(|lowered| self.counts.binary_search(&Count::from(lowered)).is_ok())),
    )]
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
    /// intuitionistic binders and `linear` linear ones.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each zone's indices gain the child's lowered by that zone's
    ///   binders, its bound ones dropped.
    /// - provides: the one step a node's answer is assembled from its
    ///   children's.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a lambda binds the nearest intuitionistic occurrence
    ///   and lowers a farther one while leaving a linear occurrence unchanged;
    ///   a dependent quoted arrow lowers only its codomain; a fork binds the
    ///   nearest linear occurrence of its child and parent and lowers a farther
    ///   one. Binding both zones or lowering the domain changes the exact free
    ///   sets.
    /// - witness: `free::tests::binders_lower_only_their_own_intuitionistic_occurrences`
    /// - witness: `free::tests::a_quoted_dependent_arrow_binds_only_its_codomain`
    /// - witness: `free::tests::a_fork_binds_one_endpoint_in_each_half`
    #[spec(ensures: child.linear.counts.iter().all(|&index| u32::from(index).checked_sub(linear.0)
            .is_none_or(|lowered| self.linear.counts.binary_search(&DeBruijnIndex::from(lowered)).is_ok()))
        && child.intuitionistic.counts.iter().all(|&index| u32::from(index).checked_sub(binders.0)
            .is_none_or(|lowered| self.intuitionistic.counts.binary_search(&DeBruijnIndex::from(lowered)).is_ok())))]
    fn join_under(
        &mut self,
        child: &Self,
        binders: Lowering,
        linear: Lowering,
    )
    {
        self.intuitionistic
            .join_lowered(&child.intuitionistic, binders);
        self.linear.join_lowered(&child.linear, linear);
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
    Enter(Reached),
    /// Assemble a node's answer from its children's.
    Assemble(Reached),
}

/// The free indices of every core term asked, each node computed once.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct FreeIndices
{
    /// One answer per node reached so far, a quoted type's nodes included.
    answered: BTreeMap<Reached, Free>,
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
    ///
    /// # Adequacy
    /// - hypothesis: L2 — open terms distinguish bound and outward indices in
    ///   both zones, including a quote crossing into types; a missing root is
    ///   refused. Erasing a zone, binding the wrong child or accepting an
    ///   absent root changes the free set or refusal.
    /// - witness: `free::tests::binders_lower_only_their_own_intuitionistic_occurrences`
    /// - witness: `free::tests::a_quoted_dependent_arrow_binds_only_its_codomain`
    /// - witness: `free::tests::missing_nodes_and_unanswered_children_have_distinct_refusals`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |free| match term {
        CoreTerm::Value(id) => core.value(id).is_some_and(|held| match *held {
            Value::Variable { zone: Zone::Intuitionistic, index } =>
                free.intuitionistic.counts.as_slice() == [index] && free.linear.counts.is_empty(),
            Value::Variable { zone: Zone::Linear, index } =>
                free.linear.counts.as_slice() == [index] && free.intuitionistic.counts.is_empty(),
            Value::Tuple(ref components) if components.is_empty() =>
                free.intuitionistic.counts.is_empty() && free.linear.counts.is_empty(),
            Value::Constant(_) | Value::Literal(_) =>
                free.intuitionistic.counts.is_empty() && free.linear.counts.is_empty(),
            _ => true,
        }),
        CoreTerm::Computation(id) => core.computation(id).is_some(),
    }))]
    pub(crate) fn of(
        &mut self,
        core: &CoreArena,
        term: CoreTerm,
    ) -> Result<&Free, FreeFault>
    {
        let reached = Reached::Term(term);
        if !self.answered.contains_key(&reached) {
            self.answer(core, reached)?;
        }
        self.answered
            .get(&reached)
            .ok_or(FreeFault::MachineInvariant)
    }

    /// The free indices of the value type `ty` in `core`.
    ///
    /// # Specification
    /// - requires: as [`FreeIndices::of`].
    /// - ensures: on success, the indices of each zone that `ty` reads without
    ///   binding, through the codes its decodes hold and the codomains its
    ///   dependent arrows bind, counted from where `ty` stands; a base type
    ///   reads none.
    /// - provides: the reading the singleton transport tests its family's
    ///   carrier against the family's binder with.
    /// - fails: as [`FreeIndices::of`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`FreeIndices::of`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a carrier closed over the binder lets the singleton
    ///   transport compute and a carrier that reads it keeps the transport
    ///   stuck.
    /// - witness: `identity::tests::transport_in_the_singleton_returns_the_path`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |free| !matches!(core.value_type(ty), Some(&ValueType::Base(_)))
        || (free.intuitionistic.counts.is_empty() && free.linear.counts.is_empty())))]
    pub(crate) fn of_type(
        &mut self,
        core: &CoreArena,
        ty: ValueTypeId,
    ) -> Result<&Free, FreeFault>
    {
        let reached = Reached::ValueType(ty);
        if !self.answered.contains_key(&reached) {
            self.answer(core, reached)?;
        }
        self.answered
            .get(&reached)
            .ok_or(FreeFault::MachineInvariant)
    }

    /// The free linear indices of `term`, ascending: the endpoints it reads
    /// without binding, counted from where it stands.
    ///
    /// # Specification
    /// - requires: as [`FreeIndices::of`].
    /// - ensures: on success, the linear half of [`FreeIndices::of`]'s answer,
    ///   ascending and each once: a session action's endpoint, and a fork's
    ///   child and parent each read one linear binder lower.
    /// - provides: the reading a checker splits the linear zone at a fork and
    ///   finds an endpoint a thunk captures with.
    /// - fails: as [`FreeIndices::of`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`FreeIndices::of`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a fork whose child and parent each use their own end
    ///   and an outer endpoint reads the outer one alone, one binder lower; a
    ///   send reads its endpoint and its payload's.
    /// - witness: `free::tests::a_fork_binds_one_endpoint_in_each_half`
    #[spec(ensures: |ret| ret.is_err() || ret.is_ok_and(|counts| counts.windows(2).all(|pair| matches!(pair, [left, right] if left < right))))]
    #[inline]
    pub fn linear(
        &mut self,
        core: &CoreArena,
        term: CoreTerm,
    ) -> Result<&[DeBruijnIndex], FreeFault>
    {
        Ok(self.of(core, term)?.linear.counts())
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
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a shared open subtree is reached through a binder and
    ///   a quote and its variables survive at the correct depth; absent roots
    ///   fail without inventing an answer. Omitting an assembly or clearing
    ///   earlier answers changes the retained result.
    /// - witness: `free::tests::binders_lower_only_their_own_intuitionistic_occurrences`
    /// - witness: `free::tests::a_quoted_dependent_arrow_binds_only_its_codomain`
    /// - witness: `free::tests::missing_nodes_and_unanswered_children_have_distinct_refusals`
    #[spec(
        captures: entry_answers = self.answered.len(),
        ensures: |ret| self.answered.len() >= entry_answers
            && (ret.is_err() || self.answered.contains_key(&term)),
    )]
    fn answer(
        &mut self,
        core: &CoreArena,
        term: Reached,
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
                    for (child, _) in below.iter().rev() {
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
    ///
    /// # Adequacy
    /// - hypothesis: L2 — assembling before its child is answered reports the
    ///   machine invariant, while walking the same live term produces its exact
    ///   free set; a dangling root has a different refusal. Reversing the
    ///   traversal order or conflating the refusals changes an observation.
    /// - witness: `free::tests::missing_nodes_and_unanswered_children_have_distinct_refusals`
    /// - witness: `free::tests::binders_lower_only_their_own_intuitionistic_occurrences`
    #[spec(ensures: |ret| match ret {
        Ok(_) => Children::of(core, node).is_ok_and(|children|
            children.iter().all(|(child, _)| self.answered.contains_key(&child))),
        Err(FreeFault::Dangling) => Children::of(core, node).is_err(),
        Err(FreeFault::MachineInvariant) => Children::of(core, node).is_ok_and(|children|
            children.iter().any(|(child, _)| !self.answered.contains_key(&child))),
    })]
    fn assemble(
        &self,
        core: &CoreArena,
        node: Reached,
    ) -> Result<Free, FreeFault>
    {
        let mut free = Free::default();
        // A fork's child and parent each stand under one linear binder.
        let mut forked = Lowering::NONE;
        match node {
            | Reached::Term(CoreTerm::Value(id)) => {
                let held = core.value(id).ok_or(FreeFault::Dangling)?;
                if let Value::Variable { zone, index } = *held {
                    free = Free::variable(zone, index);
                }
            },
            | Reached::Term(CoreTerm::Computation(id)) => {
                let held = core.computation(id).ok_or(FreeFault::Dangling)?;
                if let Computation::Session(ref action) = *held {
                    match *action {
                        | SessionAction::Fork { .. } => forked = Lowering::ONE,
                        | SessionAction::Send { endpoint, .. }
                        | SessionAction::Receive { endpoint }
                        | SessionAction::Select { endpoint, .. }
                        | SessionAction::Offer { endpoint, .. }
                        | SessionAction::Close { endpoint } => {
                            free = Free::variable(Zone::Linear, endpoint);
                        },
                    }
                }
            },
            | Reached::ValueType(_) | Reached::CompType(_) => {},
        }
        let below = Children::of(core, node)?;
        for (child, binders) in below.iter() {
            let answered = self.read(child)?;
            let linear = match child {
                | Reached::Term(CoreTerm::Computation(_)) => forked,
                | Reached::Term(CoreTerm::Value(_))
                | Reached::ValueType(_)
                | Reached::CompType(_) => Lowering::NONE,
            };
            free.join_under(answered, binders, linear);
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
    ///
    /// # Adequacy
    /// - hypothesis: L2 — an unanswered child is refused before traversal and
    ///   becomes readable with its precise outward index afterward; a
    ///   fabricated answer or a wrong refusal changes the result.
    /// - witness: `free::tests::missing_nodes_and_unanswered_children_have_distinct_refusals`
    #[spec(ensures: |ret| ret.is_ok() == self.answered.contains_key(&child)
        && ret.as_ref().err().is_none_or(|fault| *fault == FreeFault::MachineInvariant))]
    fn read(
        &self,
        child: Reached,
    ) -> Result<&Free, FreeFault>
    {
        self.answered.get(&child).ok_or(FreeFault::MachineInvariant)
    }
}

/// A node the walk reaches: a term, or a type a quote carries into one.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Reached
{
    /// A core value or computation.
    Term(CoreTerm),
    /// A value type inside a quote.
    ValueType(ValueTypeId),
    /// A computation type inside a quote.
    CompType(CompTypeId),
}

/// A borrowed variable-arity tail of native children.
#[derive(Clone, Debug)]
enum ExtraChildren<'arena>
{
    /// No variable-arity children.
    Empty,
    /// Constructor fields or nominal arguments.
    Values(core::slice::Iter<'arena, ValueId>),
    /// Case field functions; their own lambdas introduce their binders.
    Computations(core::slice::Iter<'arena, ComputationId>),
    /// Sum case branches, each beneath its one payload binder.
    Branches(core::slice::Iter<'arena, ComputationId>),
    /// Record literal fields in label order.
    RecordValues(
        alloc::collections::btree_map::Values<'arena, gandr_core_term::FieldLabel, ValueId>,
    ),
    /// Record classifier fields in label order.
    RecordTypes(
        alloc::collections::btree_map::Values<'arena, gandr_core_term::FieldLabel, ValueTypeId>,
    ),
    /// Product components or sum summands, in order.
    Types(core::slice::Iter<'arena, ValueTypeId>),
    /// Offer arms in label order; each binds nothing.
    Arms(alloc::collections::btree_map::Values<'arena, gandr_core_term::FieldLabel, ComputationId>),
    /// A recorded run's moves; a send's or a receive's payload is a value.
    Moves(core::slice::Iter<'arena, gandr_core_term::session::RecordedMove>),
}

impl Iterator for ExtraChildren<'_>
{
    type Item = (Reached, Lowering);

    /// Read the next native child without changing its scope.
    ///
    /// # Specification
    /// trivial.
    fn next(&mut self) -> Option<Self::Item>
    {
        match *self {
            | Self::Empty => None,
            | Self::Values(ref mut values) => values
                .next()
                .map(|id| (Reached::Term(CoreTerm::Value(*id)), Lowering::NONE)),
            | Self::Computations(ref mut values) => values
                .next()
                .map(|id| (Reached::Term(CoreTerm::Computation(*id)), Lowering::NONE)),
            | Self::Branches(ref mut branches) => branches
                .next()
                .map(|id| (Reached::Term(CoreTerm::Computation(*id)), Lowering::ONE)),
            | Self::RecordValues(ref mut values) => values
                .next()
                .map(|id| (Reached::Term(CoreTerm::Value(*id)), Lowering::NONE)),
            | Self::RecordTypes(ref mut values) => values
                .next()
                .map(|id| (Reached::ValueType(*id), Lowering::NONE)),
            | Self::Types(ref mut types) => types
                .next()
                .map(|id| (Reached::ValueType(*id), Lowering::NONE)),
            | Self::Arms(ref mut arms) => arms
                .next()
                .map(|id| (Reached::Term(CoreTerm::Computation(*id)), Lowering::NONE)),
            | Self::Moves(ref mut moves) => moves
                .find_map(recorded_payload)
                .map(|id| (Reached::Term(CoreTerm::Value(id)), Lowering::NONE)),
        }
    }
}

impl DoubleEndedIterator for ExtraChildren<'_>
{
    /// Read the last native child for the explicit reverse scheduling stack.
    ///
    /// # Specification
    /// trivial.
    fn next_back(&mut self) -> Option<Self::Item>
    {
        match *self {
            | Self::Empty => None,
            | Self::Values(ref mut values) => values
                .next_back()
                .map(|id| (Reached::Term(CoreTerm::Value(*id)), Lowering::NONE)),
            | Self::Computations(ref mut values) => values
                .next_back()
                .map(|id| (Reached::Term(CoreTerm::Computation(*id)), Lowering::NONE)),
            | Self::Arms(ref mut arms) => arms
                .next_back()
                .map(|id| (Reached::Term(CoreTerm::Computation(*id)), Lowering::NONE)),
            | Self::Branches(ref mut branches) => branches
                .next_back()
                .map(|id| (Reached::Term(CoreTerm::Computation(*id)), Lowering::ONE)),
            | Self::RecordValues(ref mut values) => values
                .next_back()
                .map(|id| (Reached::Term(CoreTerm::Value(*id)), Lowering::NONE)),
            | Self::RecordTypes(ref mut values) => values
                .next_back()
                .map(|id| (Reached::ValueType(*id), Lowering::NONE)),
            | Self::Types(ref mut types) => types
                .next_back()
                .map(|id| (Reached::ValueType(*id), Lowering::NONE)),
            | Self::Moves(ref mut moves) => moves
                .rev()
                .find_map(recorded_payload)
                .map(|id| (Reached::Term(CoreTerm::Value(id)), Lowering::NONE)),
        }
    }
}

/// The payload value a recorded send or receive carries.
///
/// # Specification
/// trivial.
fn recorded_payload(movement: &gandr_core_term::session::RecordedMove) -> Option<ValueId>
{
    match *movement {
        | gandr_core_term::session::RecordedMove::Sent(payload)
        | gandr_core_term::session::RecordedMove::Received(payload) => Some(payload),
        | gandr_core_term::session::RecordedMove::Selected(_)
        | gandr_core_term::session::RecordedMove::Offered(_)
        | gandr_core_term::session::RecordedMove::Closed => None,
    }
}

/// A node's children, left to right, each with the intuitionistic binders it
/// stands under.
#[derive(Clone, Debug)]
struct Children<'arena>
{
    /// Up to five children, the absent ones last.
    listed: [Option<(Reached, Lowering)>; 5],
    /// Signature type edges beyond the fixed-arity syntax children.
    effects: Option<&'arena gandr_core_term::effect::EffectRow>,
    /// An inline operation or handler interface.
    signature: Option<&'arena gandr_core_term::effect::EffectSig>,
    /// Literal stack frames, each with its own local scope.
    frames: &'arena [gandr_core_term::control::StackFrame],
    /// Handler clauses beneath payload and resumption binders.
    clauses: &'arena [gandr_core_term::control::EffectClause],
    /// Borrowed variable-arity children following the fixed prefix.
    extra: ExtraChildren<'arena>,
}

impl<'arena> Children<'arena>
{
    /// Visit all syntax and signature children without allocating an edge list.
    ///
    /// # Specification
    /// trivial.
    fn iter(&self) -> impl DoubleEndedIterator<Item = (Reached, Lowering)> + '_
    {
        self.listed
            .iter()
            .copied()
            .flatten()
            .chain(self.extra.clone())
            .chain(self.effects.into_iter().flat_map(|row| {
                row.types()
                    .map(|ty| (Reached::ValueType(ty), Lowering::NONE))
            }))
            .chain(self.signature.into_iter().flat_map(|signature| {
                signature
                    .types()
                    .map(|ty| (Reached::ValueType(ty), Lowering::NONE))
            }))
            .chain(self.frames.iter().filter_map(|frame| match *frame {
                | gandr_core_term::control::StackFrame::Apply(value) => {
                    Some((Reached::Term(CoreTerm::Value(value)), Lowering::NONE))
                },
                | gandr_core_term::control::StackFrame::Bind(body) => {
                    Some((Reached::Term(CoreTerm::Computation(body)), Lowering::ONE))
                },
                | gandr_core_term::control::StackFrame::Project(_) => None,
            }))
            .chain(self.clauses.iter().map(|clause| {
                (
                    Reached::Term(CoreTerm::Computation(clause.body)),
                    Lowering(2_u32),
                )
            }))
    }

    /// The children of `node`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each child the core former names, left to right: a lambda's
    ///   body, a static lambda's body, a bind's continuation, a case's branches
    ///   and a dependent arrow's codomain under one binder, a List fold's cell
    ///   branch under two, every other child under none, and a leaf none. A
    ///   quote's child is its type and a decode's its code, so the indices a
    ///   type reads through a code are the quote's own.
    /// - provides: the one reading of the core formers' arity and binding the
    ///   walk and the assembly share.
    /// - fails: [`FreeFault::Dangling`] when `node` does not resolve.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`FreeFault::Dangling`] — `node` does not resolve.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — value and computation binders, quoted types and a
    ///   dependent codomain produce different free-index projections; absent
    ///   roots are refused. Dropping a quote edge or marking the wrong child as
    ///   bound changes the resulting set.
    /// - witness: `free::tests::binders_lower_only_their_own_intuitionistic_occurrences`
    /// - witness: `free::tests::a_quoted_dependent_arrow_binds_only_its_codomain`
    /// - witness: `free::tests::missing_nodes_and_unanswered_children_have_distinct_refusals`
    /// - witness: `full_laziness::full_laziness::an_open_configuration_is_evaluated_per_occurrence`
    /// - witness: `eval::tests::native_transport_sequences_product_components`
    #[spec(ensures: |ret| (ret.is_ok() == match node {
        Reached::Term(CoreTerm::Value(id)) => core.value(id).is_some(),
        Reached::Term(CoreTerm::Computation(id)) => core.computation(id).is_some(),
        Reached::ValueType(id) => core.value_type(id).is_some(),
        Reached::CompType(id) => core.comp_type(id).is_some(),
    } && ret.as_ref().err().is_none_or(|fault| *fault == FreeFault::Dangling)) && (match ret {
Ok(ref children) => children.listed.iter().skip_while(|item| item.is_some()).all(Option::is_none) && match node {
            Reached::Term(CoreTerm::Value(id)) => match core.value(id) {
                Some(&Value::PathRefl(code)) => children.listed == [Some((Reached::Term(CoreTerm::Value(code)), Lowering::NONE)), None, None, None, None],
                Some(&Value::PathProduct(a, b)) => children.listed == [Some((Reached::Term(CoreTerm::Value(a)), Lowering::NONE)), Some((Reached::Term(CoreTerm::Value(b)), Lowering::NONE)), None, None, None],
                Some(&Value::PathEquiv { path_type, forward, backward, .. }) => children.listed == [Some((Reached::ValueType(path_type), Lowering::NONE)), Some((Reached::Term(CoreTerm::Value(forward)), Lowering::NONE)), Some((Reached::Term(CoreTerm::Value(backward)), Lowering::NONE)), None, None],
                _ => true,
            },
            Reached::Term(CoreTerm::Computation(id)) => match core.computation(id) { Some(&Computation::Transport(path, value)) => children.listed == [Some((Reached::Term(CoreTerm::Value(path)), Lowering::NONE)), Some((Reached::Term(CoreTerm::Value(value)), Lowering::NONE)), None, None, None], _ => true },
            _ => true,
        },
Err(FreeFault::Dangling) => match node { Reached::Term(CoreTerm::Value(id)) => core.value(id).is_none(), Reached::Term(CoreTerm::Computation(id)) => core.computation(id).is_none(), Reached::ValueType(id) => core.value_type(id).is_none(), Reached::CompType(id) => core.comp_type(id).is_none() },
Err(_) => false,
}))]
    fn of(
        core: &'arena CoreArena,
        node: Reached,
    ) -> Result<Self, FreeFault>
    {
        let one =
            |child: Reached, binders: Lowering| [Some((child, binders)), None, None, None, None];
        let two = |first: Reached, second: Reached, binders: Lowering| {
            [
                Some((first, Lowering::NONE)),
                Some((second, binders)),
                None,
                None,
                None,
            ]
        };
        let value = |id: ValueId| Reached::Term(CoreTerm::Value(id));
        let computation = |id: ComputationId| Reached::Term(CoreTerm::Computation(id));
        let mut extra = ExtraChildren::Empty;
        let mut effects = None;
        let mut signature = None;
        let mut frames = &[][..];
        let mut clauses = &[][..];
        let listed = match node {
            | Reached::Term(CoreTerm::Value(id)) => {
                let held = core.value(id).ok_or(FreeFault::Dangling)?;
                match *held {
                    | Value::Constructor {
                        datatype,
                        ref fields,
                        ..
                    } => {
                        extra = ExtraChildren::Values(fields.iter());
                        one(Reached::ValueType(datatype), Lowering::NONE)
                    },
                    | Value::Tuple(ref components) => {
                        extra = ExtraChildren::Values(components.iter());
                        [None, None, None, None, None]
                    },
                    | Value::Recorded(ref moves) => {
                        extra = ExtraChildren::Moves(moves.iter());
                        [None, None, None, None, None]
                    },
                    | Value::Record(ref fields) => {
                        extra = ExtraChildren::RecordValues(fields.values());
                        [None, None, None, None, None]
                    },
                    | Value::Reify(ref held) => {
                        frames = held;
                        [None, None, None, None, None]
                    },
                    | Value::Variable { .. }
                    | Value::Primitive { .. }
                    | Value::Constant(_)
                    | Value::ListNil
                    | Value::Literal(_)
                    | Value::Hole(_) => [None, None, None, None, None],
                    | Value::Mark { body, .. } => one(value(body), Lowering::NONE),
                    | Value::PathEquiv {
                        path_type,
                        forward,
                        backward,
                        ..
                    } => [
                        Some((Reached::ValueType(path_type), Lowering::NONE)),
                        Some((value(forward), Lowering::NONE)),
                        Some((value(backward), Lowering::NONE)),
                        None,
                        None,
                    ],
                    | Value::PathRefl(code)
                    | Value::Here(code)
                    | Value::Stay(code)
                    | Value::Forward(code) => one(value(code), Lowering::NONE),
                    | Value::PathProduct(first, second)
                    | Value::Funext(first, second)
                    | Value::Equiv(first, second)
                    | Value::Then(first, second)
                    | Value::FunctionFlow(first, second)
                    | Value::SessionRelated {
                        source: first,
                        target: second,
                        ..
                    }
                    | Value::Ua {
                        forward: first,
                        backward: second,
                        ..
                    }
                    | Value::ListCons(first, second)
                    | Value::StaticApplication(first, second) => {
                        two(value(first), value(second), Lowering::NONE)
                    },
                    | Value::StaticLambda(body) => one(value(body), Lowering::ONE),
                    | Value::Injection(_, body) | Value::Lift { body, .. } => {
                        one(value(body), Lowering::NONE)
                    },
                    | Value::Returned(body)
                    | Value::Nested(body)
                    | Value::Run(body)
                    | Value::Thunk(body) => one(computation(body), Lowering::NONE),
                    | Value::Quote(quoted) => one(Reached::ValueType(quoted), Lowering::NONE),
                    | Value::QuoteComputation(quoted) => {
                        one(Reached::CompType(quoted), Lowering::NONE)
                    },
                }
            },
            | Reached::Term(CoreTerm::Computation(id)) => {
                let held = core.computation(id).ok_or(FreeFault::Dangling)?;
                match *held {
                    | Computation::Perform {
                        signature: ref held,
                        payload,
                        ..
                    } => {
                        signature = Some(held);
                        one(value(payload), Lowering::NONE)
                    },
                    | Computation::Handle {
                        signature: ref held,
                        subject,
                        on_return,
                        clauses: ref operations,
                    } => {
                        signature = Some(held);
                        clauses = operations;
                        two(computation(subject), computation(on_return), Lowering::ONE)
                    },
                    | Computation::Exercise {
                        capability,
                        signature: ref held,
                        payload,
                        ..
                    } => {
                        signature = Some(held);
                        two(value(capability), value(payload), Lowering::NONE)
                    },
                    | Computation::Scope {
                        signature: ref held,
                        subject,
                        on_return,
                        clauses: ref operations,
                    } => {
                        signature = Some(held);
                        clauses = operations;
                        [
                            Some((computation(subject), Lowering::ONE)),
                            Some((computation(on_return), Lowering::ONE)),
                            None,
                            None,
                            None,
                        ]
                    },
                    | Computation::Resume(stack, body) => {
                        two(value(stack), computation(body), Lowering::NONE)
                    },
                    | Computation::Split {
                        scrutinee,
                        arity,
                        body,
                    } => two(
                        value(scrutinee),
                        computation(body),
                        Lowering(u32::try_from(usize::from(arity)).unwrap_or(u32::MAX)),
                    ),
                    | Computation::With(first, second) => {
                        two(computation(first), computation(second), Lowering::NONE)
                    },
                    | Computation::Reset(body) | Computation::Project(_, body) => {
                        one(computation(body), Lowering::NONE)
                    },
                    | Computation::Shift(body) | Computation::Lambda(body) => {
                        one(computation(body), Lowering::ONE)
                    },
                    | Computation::ListFold {
                        element,
                        result,
                        list,
                        on_nil,
                        on_cons,
                    } => [
                        Some((Reached::ValueType(element), Lowering::NONE)),
                        Some((Reached::ValueType(result), Lowering::NONE)),
                        Some((value(list), Lowering::NONE)),
                        Some((computation(on_nil), Lowering::NONE)),
                        Some((computation(on_cons), Lowering(2_u32))),
                    ],
                    | Computation::Primitive { arguments, .. } => match arguments {
                        | gandr_core_term::primitive::Arguments::Unary(argument) => {
                            one(value(argument), Lowering::NONE)
                        },
                        | gandr_core_term::primitive::Arguments::Binary([first, second]) => {
                            two(value(first), value(second), Lowering::NONE)
                        },
                    },
                    | Computation::DataCase {
                        scrutinee,
                        motive,
                        ref branches,
                    } => {
                        extra = ExtraChildren::Computations(branches.iter());
                        two(value(scrutinee), Reached::CompType(motive), Lowering::ONE)
                    },
                    | Computation::RecordProjection(record, _)
                    | Computation::TupleProjection(record, _) => one(value(record), Lowering::NONE),
                    | Computation::Transport(path, operand) => {
                        two(value(path), value(operand), Lowering::NONE)
                    },
                    | Computation::PathTransport {
                        motive,
                        path,
                        value: operand,
                    } => [
                        Some((Reached::ValueType(motive), Lowering::ONE)),
                        Some((value(path), Lowering::NONE)),
                        Some((value(operand), Lowering::NONE)),
                        None,
                        None,
                    ],
                    | Computation::Ride {
                        motive,
                        flow,
                        value: operand,
                    } => [
                        Some((Reached::ValueType(motive), Lowering::ONE)),
                        Some((value(flow), Lowering::NONE)),
                        Some((value(operand), Lowering::NONE)),
                        None,
                        None,
                    ],
                    | Computation::TelescopeTransport {
                        motive,
                        path,
                        start,
                        over,
                        value: operand,
                    } => [
                        Some((Reached::CompType(motive), Lowering::NONE)),
                        Some((value(path), Lowering::NONE)),
                        Some((value(start), Lowering::NONE)),
                        Some((value(over), Lowering::NONE)),
                        Some((value(operand), Lowering::NONE)),
                    ],
                    | Computation::Fixpoint { body, .. } => one(computation(body), Lowering::ONE),
                    | Computation::Application(head, argument) => {
                        two(computation(head), value(argument), Lowering::NONE)
                    },
                    | Computation::Return(value_term) | Computation::Force(value_term) => {
                        one(value(value_term), Lowering::NONE)
                    },
                    | Computation::Bind(bound, body) => {
                        two(computation(bound), computation(body), Lowering::ONE)
                    },
                    | Computation::Case {
                        scrutinee,
                        ref branches,
                    } => {
                        extra = ExtraChildren::Branches(branches.iter());
                        one(value(scrutinee), Lowering::NONE)
                    },
                    | Computation::Hole(_) => [None, None, None, None, None],
                    | Computation::Mark { body, .. } => one(computation(body), Lowering::NONE),
                    | Computation::Session(ref action) => match *action {
                        | SessionAction::Send { payload, .. } => {
                            one(value(payload), Lowering::NONE)
                        },
                        | SessionAction::Offer { ref arms, .. } => {
                            extra = ExtraChildren::Arms(arms.values());
                            [None, None, None, None, None]
                        },
                        | SessionAction::Fork {
                            protocol,
                            child,
                            parent,
                        } => [
                            Some((Reached::ValueType(protocol), Lowering::NONE)),
                            Some((computation(child), Lowering::NONE)),
                            Some((computation(parent), Lowering::NONE)),
                            None,
                            None,
                        ],
                        | SessionAction::Receive { .. }
                        | SessionAction::Select { .. }
                        | SessionAction::Close { .. } => [None, None, None, None, None],
                    },
                }
            },
            | Reached::ValueType(id) => {
                let held = core.value_type(id).ok_or(FreeFault::Dangling)?;
                match *held {
                    | ValueType::Data { ref arguments, .. } => {
                        extra = ExtraChildren::Values(arguments.iter());
                        [None, None, None, None, None]
                    },
                    | ValueType::Record(ref fields) => {
                        extra = ExtraChildren::RecordTypes(fields.values());
                        [None, None, None, None, None]
                    },
                    | ValueType::Stack { input, output } => two(
                        Reached::CompType(input),
                        Reached::CompType(output),
                        Lowering::NONE,
                    ),
                    | ValueType::List(element) => one(Reached::ValueType(element), Lowering::NONE),
                    | ValueType::PathUniverse(source, target) => {
                        two(value(source), value(target), Lowering::NONE)
                    },
                    | ValueType::Path {
                        carrier,
                        left,
                        right,
                    } => [
                        Some((Reached::ValueType(carrier), Lowering::NONE)),
                        Some((value(left), Lowering::NONE)),
                        Some((value(right), Lowering::NONE)),
                        None,
                        None,
                    ],
                    | ValueType::Flow {
                        carrier,
                        source,
                        target,
                    } => [
                        Some((Reached::ValueType(carrier), Lowering::NONE)),
                        Some((value(source), Lowering::NONE)),
                        Some((value(target), Lowering::NONE)),
                        None,
                        None,
                    ],
                    | ValueType::Run(session) => one(value(session), Lowering::NONE),
                    | ValueType::Product(ref components) | ValueType::Sum(ref components) => {
                        extra = ExtraChildren::Types(components.iter());
                        [None, None, None, None, None]
                    },
                    | ValueType::Session(ref session) => {
                        extra = ExtraChildren::Types(session.payloads().iter());
                        [None, None, None, None, None]
                    },
                    | ValueType::Base(_)
                    | ValueType::Universe { .. }
                    | ValueType::Abstract(_)
                    | ValueType::Unknown => [None, None, None, None, None],
                    | ValueType::Capability { ref authority, .. } => {
                        effects = Some(authority);
                        [None, None, None, None, None]
                    },
                    | ValueType::StaticPi {
                        domain: first,
                        codomain: second,
                    } => two(
                        Reached::ValueType(first),
                        Reached::ValueType(second),
                        Lowering::NONE,
                    ),
                    | ValueType::Thunk(body) => one(Reached::CompType(body), Lowering::NONE),
                    | ValueType::Lift { inner, .. } => {
                        one(Reached::ValueType(inner), Lowering::NONE)
                    },
                    | ValueType::Element { code, .. } => one(value(code), Lowering::NONE),
                }
            },
            | Reached::CompType(id) => {
                let held = core.comp_type(id).ok_or(FreeFault::Dangling)?;
                match *held {
                    | CompType::With(first, second) => two(
                        Reached::CompType(first),
                        Reached::CompType(second),
                        Lowering::NONE,
                    ),
                    | CompType::Returner {
                        result,
                        effects: ref row,
                    } => {
                        effects = Some(row);
                        one(Reached::ValueType(result), Lowering::NONE)
                    },
                    | CompType::Arrow { domain, codomain } => two(
                        Reached::ValueType(domain),
                        Reached::CompType(codomain),
                        Lowering::NONE,
                    ),
                    | CompType::Pi { domain, codomain } => two(
                        Reached::ValueType(domain),
                        Reached::CompType(codomain),
                        Lowering::ONE,
                    ),
                    | CompType::Element { code, .. } => one(value(code), Lowering::NONE),
                    | CompType::Unknown => [None, None, None, None, None],
                }
            },
        };
        Ok(Self {
            listed,
            effects,
            signature,
            frames,
            clauses,
            extra,
        })
    }
}

#[cfg(test)]
mod tests
{
    use alloc::collections::BTreeSet;
    use alloc::vec::Vec;

    use gandr_core_term::CoreArena;
    use gandr_core_term::Zone;
    use gandr_kernel_strata::Level;
    use gandr_kernel_term::DeBruijnIndex;

    use super::CoreTerm;
    use super::FreeFault;
    use super::FreeIndices;
    use super::Lowering;
    use super::Membership;
    use super::Outward;
    use super::Reached;

    #[test]
    fn lowered_union_agrees_with_a_set_model()
    {
        let universe = [0_u32, 1, 3, u32::MAX];
        for held_mask in 0_u8 .. 16 {
            for other_mask in 0_u8 .. 16 {
                for lowering in [0_u32, 1, 2, u32::MAX] {
                    let held: Vec<_> = universe
                        .iter()
                        .copied()
                        .enumerate()
                        .filter_map(|(bit, count)| (held_mask & (1 << bit) != 0).then_some(count))
                        .collect();
                    let other: Vec<_> = universe
                        .iter()
                        .copied()
                        .enumerate()
                        .filter_map(|(bit, count)| (other_mask & (1 << bit) != 0).then_some(count))
                        .collect();
                    let expected: BTreeSet<_> = held
                        .iter()
                        .copied()
                        .chain(other.iter().filter_map(|count| count.checked_sub(lowering)))
                        .collect();
                    let mut actual = Outward { counts: held };
                    actual.join_lowered(&Outward { counts: other }, Lowering(lowering));
                    assert_eq!(expected.iter().copied().collect::<Vec<_>>(), actual.counts);
                    for count in [0_u32, 1, 2, 3, u32::MAX - 1, u32::MAX] {
                        let membership = if expected.contains(&count) {
                            Membership::Held
                        }
                        else {
                            Membership::Absent
                        };
                        assert_eq!(membership, actual.holds(count));
                    }
                }
            }
        }
    }

    #[test]
    fn a_fork_binds_one_endpoint_in_each_half()
    {
        use gandr_core_term::session::SessionAction;
        let mut core = CoreArena::new();
        let unit = core.value_unit();
        let protocol = core.value_type_unit();
        // Inside the child its own end is 0 and the outer endpoint 1.
        let to_outer = core.computation_session(SessionAction::Send {
            endpoint: DeBruijnIndex::from(1_u32),
            payload: unit,
        });
        let own_close = core.computation_session(SessionAction::Close {
            endpoint: DeBruijnIndex::from(0_u32),
        });
        let child = core.computation_bind(to_outer, own_close);
        let parent = core.computation_session(SessionAction::Close {
            endpoint: DeBruijnIndex::from(0_u32),
        });
        let fork = core.computation_session(SessionAction::Fork {
            protocol,
            child,
            parent,
        });
        let mut analysis = FreeIndices::default();
        assert_eq!(
            Ok([DeBruijnIndex::from(0_u32), DeBruijnIndex::from(1_u32)].as_slice()),
            analysis.linear(&core, CoreTerm::Computation(child)),
            "the child reads its own end and the outer endpoint"
        );
        assert_eq!(
            Ok([DeBruijnIndex::from(0_u32)].as_slice()),
            analysis.linear(&core, CoreTerm::Computation(fork)),
            "the fork binds both ends and reads the outer endpoint one lower"
        );
        let carried = core.value_variable(Zone::Linear, DeBruijnIndex::from(3_u32));
        let delegate = core.computation_session(SessionAction::Send {
            endpoint: DeBruijnIndex::from(2_u32),
            payload: carried,
        });
        assert_eq!(
            Ok([DeBruijnIndex::from(2_u32), DeBruijnIndex::from(3_u32)].as_slice()),
            analysis.linear(&core, CoreTerm::Computation(delegate)),
            "a send reads its endpoint and its payload's"
        );
    }

    #[test]
    fn binders_lower_only_their_own_intuitionistic_occurrences()
    {
        let mut core = CoreArena::new();
        let near = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let far = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(2_u32));
        let linear = core.value_variable(Zone::Linear, DeBruijnIndex::from(2_u32));
        let decoded = core.value_type_element(far, Level::zero());
        let quote = core.value_quote(decoded);
        let shared = core.value_tuple(&[quote, linear]);
        let body = core.value_tuple(&[near, shared]);
        let returned = core.computation_return(body);
        let lambda = core.computation_lambda(returned);
        let static_lambda = core.value_static_lambda(body);
        let mut analysis = FreeIndices::default();
        for term in [
            CoreTerm::Computation(lambda),
            CoreTerm::Value(static_lambda),
        ] {
            let free = analysis
                .of(&core, term)
                .expect("a live open term has free indices");
            assert_eq!([DeBruijnIndex::from(1_u32)], free.intuitionistic.counts());
            assert_eq!([DeBruijnIndex::from(2_u32)], free.linear.counts());
        }
        let free = analysis
            .of(&core, CoreTerm::Value(far))
            .expect("the shared answer remains");
        assert_eq!([DeBruijnIndex::from(2_u32)], free.intuitionistic.counts());
        assert!(free.linear.counts().is_empty());
        let free = analysis
            .of(&core, CoreTerm::Value(linear))
            .expect("the linear leaf remains");
        assert_eq!([DeBruijnIndex::from(2_u32)], free.linear.counts());
        assert!(free.intuitionistic.counts().is_empty());
        let unit = core.value_unit();
        let free = analysis
            .of(&core, CoreTerm::Value(unit))
            .expect("unit is closed");
        assert!(free.intuitionistic.counts().is_empty());
        assert!(free.linear.counts().is_empty());
    }

    #[test]
    fn a_quoted_dependent_arrow_binds_only_its_codomain()
    {
        let mut core = CoreArena::new();
        let near = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let far = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(2_u32));
        let domain = core.value_type_element(far, Level::zero());
        let bound = core.value_type_element(near, Level::zero());
        let product = core.value_type_product(&[bound, domain]);
        let result = core.comp_type_returner(product);
        let arrow = core.comp_type_pi(domain, result);
        let quote = core.value_quote_computation(arrow);
        let mut analysis = FreeIndices::default();
        let free = analysis
            .of(&core, CoreTerm::Value(quote))
            .expect("quoted types are traversed");
        assert_eq!(
            [DeBruijnIndex::from(1_u32), DeBruijnIndex::from(2_u32)],
            free.intuitionistic.counts()
        );
        assert!(free.linear.counts().is_empty());
    }

    #[test]
    fn missing_nodes_and_unanswered_children_have_distinct_refusals()
    {
        let mut core = CoreArena::new();
        let child = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(3_u32));
        let parent = core.computation_return(child);
        let reached = Reached::Term(CoreTerm::Value(child));
        let mut analysis = FreeIndices::default();
        assert_eq!(Err(FreeFault::MachineInvariant), analysis.read(reached));
        assert_eq!(
            Err(FreeFault::MachineInvariant),
            analysis.assemble(&core, Reached::Term(CoreTerm::Computation(parent)))
        );
        let free = analysis
            .of(&core, CoreTerm::Computation(parent))
            .expect("postorder answers children");
        assert_eq!([DeBruijnIndex::from(3_u32)], free.intuitionistic.counts());
        assert_eq!(
            [DeBruijnIndex::from(3_u32)],
            analysis
                .read(reached)
                .expect("the child was answered")
                .intuitionistic
                .counts()
        );
        let empty = CoreArena::new();
        let mut missing = FreeIndices::default();
        assert_eq!(
            Err(FreeFault::Dangling),
            missing.of(&empty, CoreTerm::Value(child))
        );
        assert_eq!(Err(FreeFault::Dangling), missing.assemble(&empty, reached));
    }

    #[test]
    fn control_scopes_keep_only_ambient_indices()
    {
        use gandr_core_term::control::EffectClause;
        use gandr_core_term::control::StackFrame;
        use gandr_core_term::effect::EffectName;
        use gandr_core_term::effect::EffectOp;
        use gandr_core_term::effect::EffectSig;
        use gandr_core_term::effect::OperationName;
        let mut core = CoreArena::new();
        let zero = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let one = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
        let two = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(2_u32));
        let three = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(3_u32));
        let four = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(4_u32));
        let unit = core.value_type_unit();
        let decoded = core.value_type_element(four, Level::zero());
        let operation = OperationName::from("get");
        let signature = EffectSig::new(EffectName::from("State"), [EffectOp {
            name: operation.clone(),
            payload: unit,
            reply: decoded,
        }])
        .unwrap();
        let performed = core.computation_perform(signature.clone(), operation.clone(), two);
        let on_return = core.computation_return(one);
        let pair = core.value_tuple(&[one, three]);
        let clause = core.computation_return(pair);
        let handled = core.computation_handle(
            signature,
            performed,
            on_return,
            alloc::sync::Arc::from([EffectClause {
                operation,
                body: clause,
            }]),
        );
        let pair = core.value_tuple(&[zero, four]);
        let body = core.computation_return(pair);
        let stack = core.value_reify(alloc::sync::Arc::from([
            StackFrame::Apply(two),
            StackFrame::Bind(body),
            StackFrame::Project(gandr_kernel_term::Side::Left),
        ]));
        let body = core.computation_return(four);
        let resumed = core.computation_resume(zero, body);
        let shifted = core.computation_shift(resumed);
        let reset = core.computation_reset(shifted);
        let mut analysis = FreeIndices::default();
        for (term, expected) in [
            (CoreTerm::Computation(handled), &[0_u32, 1, 2, 4][..]),
            (CoreTerm::Value(stack), &[2_u32, 3][..]),
            (CoreTerm::Computation(reset), &[3_u32][..]),
        ] {
            let free = analysis.of(&core, term).unwrap();
            assert_eq!(
                free.intuitionistic
                    .counts()
                    .iter()
                    .copied()
                    .map(u32::from)
                    .collect::<alloc::vec::Vec<_>>(),
                expected
            );
            assert!(free.linear.counts().is_empty());
        }
    }
}
