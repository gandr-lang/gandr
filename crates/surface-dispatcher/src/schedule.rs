//! The concurrent schedule of a composition's runs (#2954): the writers a run
//! may start before their binders' bodies, read off the checker's typings.
//!
//! A bind `x ← M; N` is independent when its writer `M` performs no operation,
//! so running `M` early reorders no effect. The checker types `M` as a
//! returner, and the returner's row names the operations `M` may perform.
//! [`independent`] names `M` a writer when every typing of `M` is a returner
//! with the closed empty row, and when `M`'s captures and answer lay out in a
//! store of its own. Focus then names each such writer apart and marks its
//! binder, and `gandr_core_sequent::spawn_independent` spawns it.
//!
//! # Boundaries
//!
//! - **Every typing agrees, or the head stays fused.** The core arena shares
//!   one term between the sites that write it, and each site may type it with a
//!   row of its own. A head is a writer only when each of its typings is pure.
//! - **A head the checker did not type stays fused.** The rule reads only the
//!   typings the judgement kept.
//! - **A capture that does not lay out keeps the bind fused.** A writer runs
//!   over a store of its own, so its captures copy there and its answer copies
//!   back. Five kinds of value belong to the run that holds them: a stack, a
//!   capability, a session's endpoint, a buffer, and a kept value, which may
//!   capture a view the run lent. The copy refuses them, or a run apart cannot
//!   act on them. The rule marks no writer that captures a linear binder, since
//!   the linear zone holds stacks, endpoints, buffers, held slots and views. It
//!   marks no writer that captures an intuitionistic binder whose type holds a
//!   run's own value through a record, a product, a sum, a list, a stage, a
//!   lift or a handle. It marks no writer whose answer's type holds one.
//! - **A binder is read by its level, over each declaration's typings.** A
//!   typing keeps no context, so the rule reads a binder's type off the typings
//!   of the variables that name it. Two sibling scopes may bind different types
//!   at one level, and the rule then reads both. So a level that holds a stack
//!   or a capability in one scope keeps every writer capturing that level
//!   fused, in either scope.
//! - **A thunk's or a datatype's captures are not read.** A thunk's type
//!   records no summary of what its environment holds, and a datatype's fields
//!   are its declaration's. A writer that captures a thunk over a capability is
//!   marked, and its spawn declines at the copy.
//!
//! # References
//!
//! - `vault:01a178aa-6b8e-7d60-a533-ec9379c0462a` — lineage: the futures design
//!   (§ futures-in-gandr item 1): a cut whose writer performs no operation is
//!   independent.
//! - `vault:01a178aa-6917-7983-b5cd-86e2af86b3ec` — lineage: the kernel
//!   reassessment (§ kernel-reassessment-design item 4): a closure's type
//!   records the summaries of its captures, which reads a thunk's captures.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use gandr_core_checker::TermNode;
use gandr_core_checker::TypeNode;
use gandr_core_checker::TypedModule;
use gandr_core_checker::Typing;
use gandr_core_sequent::Writers;
use gandr_core_term::BinderDepth;
use gandr_core_term::CompType;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::effect::EffectRow;
use gandr_core_term::world::WorldType;
use gandr_kernel_term::DeBruijnIndex;
use quenchant_shape::shape::Maybe;

use crate::pool::Pool;

/// Which schedule a composition's runs give their independent cuts.
#[derive(Clone, Copy, Debug)]
pub enum Scheduling<'pool>
{
    /// Each writer runs where its binder binds it, on the caller's thread.
    Sequential,
    /// Each independent writer starts as a job of the pool, and each read
    /// waits for its writer.
    Concurrent(&'pool Pool),
}

/// The writers `typed` shows to run apart: the head of each bind it typed,
/// when every typing of that head is a returner with the closed empty row
/// whose captures and answer lay out in a store of its own.
///
/// # Specification
/// - requires: `typed` is the typed run of a module judged over `core`.
/// - ensures: a computation is named exactly when it is the head of a bind
///   `typed` typed, every typing of it is a returner with the closed empty row,
///   and under each typing its answer's type and each intuitionistic binder it
///   captures holds no run's own value, as the module's boundaries read them,
///   and it captures no linear binder.
/// - panics: none.
/// - executable: none — unwitnessable provenance: the typings must be the run
///   of a module over `core`, and the call holds no judgement to check them
///   against.
///
/// # Adequacy
/// - hypothesis: L3 — over the tree sum, the recursive calls are named and the
///   call that prints is not. A writer that captures a capability's binder
///   stays fused while its sibling over an integer is named. A writer whose
///   answer is a kept value stays fused. A flipped row test, a dropped capture
///   test, a level read off the wrong depth, or a kept value laid out changes
///   the set. L2 — the corpus differential composes every source on both
///   schedules, `gandr-surface-dispatcher`'s
///   `tests::corpus::sweeps::the_concurrent_schedule_settles_the_corpus_alike_2954`.
/// - witness: `schedule::tests::the_tree_sum_names_each_pure_call`
/// - witness: `schedule::tests::a_writer_over_a_capability_stays_fused`
/// - witness: `schedule::tests::a_writer_answering_a_kept_value_stays_fused_2954`
pub fn independent(
    core: &CoreArena,
    typed: &TypedModule,
) -> Writers
{
    let mut standing: BTreeMap<ComputationId, Standing> = BTreeMap::new();
    for typings in typed.typings().values() {
        let unlaid = unlaid_levels(core, typings.typings());
        for typing in typings.typings() {
            let TermNode::Computation(term) = typing.term
            else {
                continue;
            };
            let judged = judged(core, (term, typing), &unlaid);
            let held = standing.entry(term).or_insert(Standing::Independent);
            if judged == Standing::Dependent {
                *held = Standing::Dependent;
            }
        }
    }
    standing
        .keys()
        .filter_map(|&term| match core.computation(term) {
            Some(&Computation::Bind(head, _)) => Some(head),
            Some(_) | None => None,
        })
        .filter(|head| matches!(standing.get(head), Some(Standing::Independent)))
        .collect()
}

/// Whether a computation may run apart from its binder.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Standing
{
    /// It performs nothing, and its captures and answer lay out apart.
    Independent,
    /// It may perform, or something it holds belongs to its run.
    Dependent,
}

/// The binder level a variable names: the binders open outside it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Level(usize);

quenchant_shape::reason_enum! {
    /// Why an index names no binder level.
    mod named {
        /// The index reaches no open binder.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The index counts past the outermost binder open where it
            /// stands.
            Outside,
        }
    }
}

impl Level
{
    /// The level the intuitionistic index `index` names under `depth`
    /// binders.
    ///
    /// # Specification
    /// trivial.
    fn named(
        depth: BinderDepth,
        index: DeBruijnIndex,
    ) -> Maybe<Self, named::Absent>
    {
        usize::try_from(u32::from(index))
            .ok()
            .and_then(|index| usize::from(depth).checked_sub(index)?.checked_sub(1))
            .map_or(Maybe::Absent(named::Absent::Outside), |level| {
                Maybe::Present(Self(level))
            })
    }
}

/// The intuitionistic levels one declaration's `typings` bind to a type
/// that holds a run's own value, read off the variables that name them.
///
/// # Specification
/// trivial.
fn unlaid_levels(
    core: &CoreArena,
    typings: &[Typing],
) -> BTreeSet<Level>
{
    typings
        .iter()
        .filter_map(|typing| {
            let (TermNode::Value(value), TypeNode::Value(ty)) = (typing.term, typing.ty)
            else {
                return None;
            };
            let Some(&Value::Variable {
                zone: Zone::Intuitionistic,
                index,
            }) = core.value(value)
            else {
                return None;
            };
            match (layout(core, ty), Level::named(typing.depth, index)) {
                (Layout::Unlaid, Maybe::Present(level)) => Some(level),
                (Layout::Lays, _) | (Layout::Unlaid, Maybe::Absent(named::Absent::Outside)) => None,
            }
        })
        .collect()
}

/// How `term` stands under one of its typings, `typing`: dependent unless it
/// is a returner with the closed empty row whose answer lays out and whose
/// captures name no linear binder and no level of `unlaid`.
///
/// # Specification
/// trivial.
fn judged(
    core: &CoreArena,
    (term, typing): (ComputationId, &Typing),
    unlaid: &BTreeSet<Level>,
) -> Standing
{
    let TypeNode::Computation(ty) = typing.ty
    else {
        return Standing::Dependent;
    };
    let Some(&CompType::Returner {
        result,
        ref effects,
    }) = core.comp_type(ty)
    else {
        return Standing::Dependent;
    };
    if *effects != EffectRow::EMPTY || layout(core, result) == Layout::Unlaid {
        return Standing::Dependent;
    }
    let Some(support) = core.computation_support(term)
    else {
        return Standing::Dependent;
    };
    if support.indices(Zone::Linear).next().is_some() {
        return Standing::Dependent;
    }
    let captures_unlaid = support.indices(Zone::Intuitionistic).any(|index| {
        match Level::named(typing.depth, index) {
            Maybe::Present(level) => unlaid.contains(&level),
            Maybe::Absent(named::Absent::Outside) => true,
        }
    });
    if captures_unlaid {
        Standing::Dependent
    }
    else {
        Standing::Independent
    }
}

/// Whether a value of a type lays out in a store of its own.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Layout
{
    /// It copies into another store, and a run there holds it.
    Lays,
    /// It holds a stack, a capability, an endpoint, a buffer or a kept value.
    Unlaid,
}

/// Whether a value of `ty` lays out apart: unlaid when `ty` holds a stack, a
/// capability, an endpoint, a buffer or a kept value through a record, a
/// product, a sum, a dependent pair, a list, a stage, a lift or a handle.
///
/// # Specification
/// trivial.
fn layout(
    core: &CoreArena,
    ty: ValueTypeId,
) -> Layout
{
    let mut pending: Vec<ValueTypeId> = Vec::from([ty]);
    let mut seen: BTreeSet<ValueTypeId> = BTreeSet::new();
    while let Some(ty) = pending.pop() {
        if !seen.insert(ty) {
            continue;
        }
        match core.value_type(ty) {
            Some(
                &(ValueType::Stack { .. }
                | ValueType::Capability { .. }
                | ValueType::Session(_)
                | ValueType::Buffer
                | ValueType::Kept { .. }
                | ValueType::World(WorldType::Capability(_))),
            ) => return Layout::Unlaid,
            Some(&ValueType::Record(ref fields)) => pending.extend(fields.values().copied()),
            Some(&(ValueType::Product(ref components) | ValueType::Sum(ref components))) => {
                pending.extend(components.iter().copied());
            },
            Some(&ValueType::Sigma { first, second }) => pending.extend([first, second]),
            Some(
                &(ValueType::List(inner)
                | ValueType::Staged { base: inner, .. }
                | ValueType::Lift { inner, .. }
                | ValueType::World(WorldType::At { inner, .. })),
            ) => pending.push(inner),
            Some(
                &(ValueType::Data { .. }
                | ValueType::PathUniverse(..)
                | ValueType::Path { .. }
                | ValueType::Flow { .. }
                | ValueType::Bridge { .. }
                | ValueType::Run(_)
                | ValueType::Prefix(_)
                | ValueType::Dialogue(_)
                | ValueType::Web
                | ValueType::Base(_)
                | ValueType::Thunk(_)
                | ValueType::Universe { .. }
                | ValueType::Element { .. }
                | ValueType::Row
                | ValueType::RowTail(_)
                | ValueType::Abstract(_)
                | ValueType::StaticPi { .. }
                | ValueType::Unknown),
            )
            | None => {},
        }
    }
    Layout::Lays
}

#[cfg(test)]
mod tests;
