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
//! variable. No former binds into the linear zone, so a linear index passes
//! every binder unchanged.
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
    ///   searching a malformed order changes an answer.
    /// - witness: `free::tests::lowered_union_agrees_with_a_set_model`
    #[spec(ensures: |ret| matches!(ret, Membership::Held) == self.counts.contains(&count))]
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
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a lambda binds the nearest intuitionistic occurrence
    ///   and lowers a farther one while leaving a linear occurrence unchanged;
    ///   a dependent quoted arrow lowers only its codomain. Binding both zones
    ///   or lowering the domain changes the exact free sets.
    /// - witness: `free::tests::binders_lower_only_their_own_intuitionistic_occurrences`
    /// - witness: `free::tests::a_quoted_dependent_arrow_binds_only_its_codomain`
    #[spec(ensures: child.linear.counts.iter().all(|count| self.linear.counts.contains(count))
        && child.intuitionistic.counts.iter().all(|&index| u32::from(index).checked_sub(binders.0)
            .is_none_or(|lowered| self.intuitionistic.counts.contains(&DeBruijnIndex::from(lowered)))))]
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
            Value::Unit | Value::Constant(_) | Value::Literal(_) =>
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
            children.listed.iter().flatten().all(|&(child, _)| self.answered.contains_key(&child))),
        Err(FreeFault::Dangling) => Children::of(core, node).is_err(),
        Err(FreeFault::MachineInvariant) => Children::of(core, node).is_ok_and(|children|
            children.listed.iter().flatten().any(|&(child, _)| !self.answered.contains_key(&child))),
    })]
    fn assemble(
        &self,
        core: &CoreArena,
        node: Reached,
    ) -> Result<Free, FreeFault>
    {
        let mut free = Free::default();
        if let Reached::Term(CoreTerm::Value(id)) = node {
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

/// A node's children, left to right, each with the intuitionistic binders it
/// stands under.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Children
{
    /// Up to three children, the absent ones last.
    listed: [Option<(Reached, Lowering)>; 3],
}

impl Children
{
    /// The children of `node`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each child the core former names, left to right: a lambda's
    ///   body, a static lambda's body, a bind's continuation, a case's branches
    ///   and a dependent arrow's codomain under one binder, every other child
    ///   under none, and a leaf none. A quote's child is its type and a
    ///   decode's its code, so the indices a type reads through a code are the
    ///   quote's own.
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
        Ok(children) => children.listed.iter().skip_while(|item| item.is_some()).all(Option::is_none) && match node {
            Reached::Term(CoreTerm::Value(id)) => match core.value(id) {
                Some(&Value::PathRefl(code)) => children.listed == [Some((Reached::Term(CoreTerm::Value(code)), Lowering::NONE)), None, None],
                Some(&Value::PathProduct(a, b)) => children.listed == [Some((Reached::Term(CoreTerm::Value(a)), Lowering::NONE)), Some((Reached::Term(CoreTerm::Value(b)), Lowering::NONE)), None],
                Some(&Value::PathEquiv { path_type, forward, backward, .. }) => children.listed == [Some((Reached::ValueType(path_type), Lowering::NONE)), Some((Reached::Term(CoreTerm::Value(forward)), Lowering::NONE)), Some((Reached::Term(CoreTerm::Value(backward)), Lowering::NONE))],
                _ => true,
            },
            Reached::Term(CoreTerm::Computation(id)) => match core.computation(id) { Some(&Computation::Transport(path, value)) => children.listed == [Some((Reached::Term(CoreTerm::Value(path)), Lowering::NONE)), Some((Reached::Term(CoreTerm::Value(value)), Lowering::NONE)), None], _ => true },
            _ => true,
        },
        Err(FreeFault::Dangling) => match node { Reached::Term(CoreTerm::Value(id)) => core.value(id).is_none(), Reached::Term(CoreTerm::Computation(id)) => core.computation(id).is_none(), Reached::ValueType(id) => core.value_type(id).is_none(), Reached::CompType(id) => core.comp_type(id).is_none() },
        Err(_) => false,
    }))]
    fn of(
        core: &CoreArena,
        node: Reached,
    ) -> Result<Self, FreeFault>
    {
        let one = |child: Reached, binders: Lowering| [Some((child, binders)), None, None];
        let two = |first: Reached, second: Reached, binders: Lowering| {
            [Some((first, Lowering::NONE)), Some((second, binders)), None]
        };
        let value = |id: ValueId| Reached::Term(CoreTerm::Value(id));
        let computation = |id: ComputationId| Reached::Term(CoreTerm::Computation(id));
        let listed = match node {
            | Reached::Term(CoreTerm::Value(id)) => {
                let held = core.value(id).ok_or(FreeFault::Dangling)?;
                match *held {
                    | Value::Variable { .. }
                    | Value::Primitive { .. }
                    | Value::Constant(_)
                    | Value::Unit
                    | Value::Literal(_) => [None, None, None],
                    | Value::PathEquiv {
                        path_type,
                        forward,
                        backward,
                        ..
                    } => [
                        Some((Reached::ValueType(path_type), Lowering::NONE)),
                        Some((value(forward), Lowering::NONE)),
                        Some((value(backward), Lowering::NONE)),
                    ],
                    | Value::PathRefl(code) => one(value(code), Lowering::NONE),
                    | Value::PathProduct(first, second)
                    | Value::Pair(first, second)
                    | Value::StaticApplication(first, second) => {
                        two(value(first), value(second), Lowering::NONE)
                    },
                    | Value::StaticLambda(body) => one(value(body), Lowering::ONE),
                    | Value::Injection(_, body) | Value::Lift { body, .. } => {
                        one(value(body), Lowering::NONE)
                    },
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
                    | Computation::Primitive { arguments, .. } => match arguments {
                        | gandr_core_term::primitive::Arguments::Unary(argument) => {
                            one(value(argument), Lowering::NONE)
                        },
                        | gandr_core_term::primitive::Arguments::Binary([first, second]) => {
                            two(value(first), value(second), Lowering::NONE)
                        },
                    },
                    | Computation::Transport(path, operand) => {
                        two(value(path), value(operand), Lowering::NONE)
                    },
                    | Computation::Lambda(body) => one(computation(body), Lowering::ONE),
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
                        on_left,
                        on_right,
                    } => [
                        Some((value(scrutinee), Lowering::NONE)),
                        Some((computation(on_left), Lowering::ONE)),
                        Some((computation(on_right), Lowering::ONE)),
                    ],
                }
            },
            | Reached::ValueType(id) => {
                let held = core.value_type(id).ok_or(FreeFault::Dangling)?;
                match *held {
                    | ValueType::PathUniverse(source, target) => {
                        two(value(source), value(target), Lowering::NONE)
                    },
                    | ValueType::Base(_)
                    | ValueType::Unit
                    | ValueType::Universe { .. }
                    | ValueType::Abstract(_) => [None, None, None],
                    | ValueType::Product(first, second)
                    | ValueType::Sum(first, second)
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
                    | CompType::Returner(result) => one(Reached::ValueType(result), Lowering::NONE),
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
                }
            },
        };
        Ok(Self { listed })
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

    use super::Children;
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
    fn binders_lower_only_their_own_intuitionistic_occurrences()
    {
        let mut core = CoreArena::new();
        let near = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let far = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(2_u32));
        let linear = core.value_variable(Zone::Linear, DeBruijnIndex::from(2_u32));
        let decoded = core.value_type_element(far, Level::zero());
        let quote = core.value_quote(decoded);
        let shared = core.value_pair(quote, linear);
        let body = core.value_pair(near, shared);
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
        let product = core.value_type_product(bound, domain);
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
        assert_eq!(
            Err(FreeFault::Dangling),
            Children::of(&empty, Reached::Term(CoreTerm::Computation(parent)))
        );
    }
}
