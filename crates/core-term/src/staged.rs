//! The positions of a type a stage may refine, and the walk that erases the
//! stages standing there.
//!
//! A stage refines a data type reached through the formers a signature
//! builds: arrows and dependent arrows, returners, thunks, lazy products,
//! records, eager products and sums, dependent pairs, lists, and the types a
//! data type's arguments quote. [`placed`] names those children of a node in
//! order, [`rebuild`] reassembles a node over replacements for them, and
//! [`unstaged`] erases every stage the walk reaches: the plain reading of a
//! type a quantified signature writes, which is what a body's own types
//! carry.
//!
//! # Items
//!
//! - [`Part`]: a value or computation type node.
//! - [`placed`]: a node's placeable children, in order.
//! - [`rebuild`]: a node over replacements for its placeable children.
//! - [`unstaged`]: a type with every placed stage erased.
//! - [`Supply`]: a stage a call supplies its callee's binder at.

use alloc::vec::Vec;

use anodized::spec;

use crate::CompType;
use crate::CompTypeId;
use crate::CoreArena;
use crate::Value;
use crate::ValueId;
use crate::ValueType;
use crate::ValueTypeId;

#[cfg(test)]
mod tests;

/// One node of a type a staging walk reads.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the id names a node of the sort the variant says.
/// - executable: none — the arena it names a node in is not held.
///
/// # Adequacy
/// - hypothesis: L3 — the erasure witness walks both sorts.
/// - witness: `staged::tests::every_placed_stage_is_erased`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Part
{
    /// A value type.
    Value(ValueTypeId),
    /// A computation type.
    Computation(CompTypeId),
}

/// A stage a call supplies a binder of its callee at, written `f[i = s]`.
///
/// It names the value the call forces, the binder by its position in the
/// callee's signature, and the stage, one the caller's own signature mints.
/// The kernel never reads it: it re-derives the stage from the call's
/// arguments, so the checker holds a supply to the stage they show.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Supply
{
    /// The value the call forces: its callee's name.
    pub head: ValueId,
    /// The binder, by its position in the callee's signature.
    pub binder: gandr_kernel_term::StageBinder,
    /// The stage supplied.
    pub stage: gandr_kernel_term::Stage,
}

/// Hand each child of `part` a stage may be placed under to `each`, in order:
/// the former's own children where it is placeable, the types an argument of
/// a data type quotes, and none for any other former.
///
/// # Specification
/// trivial.
#[inline]
pub fn placed<Each>(
    arena: &CoreArena,
    part: Part,
    mut each: Each,
) where
    Each: FnMut(Part),
{
    match part {
        Part::Value(id) => match arena.value_type(id) {
            Some(&ValueType::Data { ref arguments, .. }) => {
                for &argument in arguments {
                    if let Some(&Value::Quote(quoted)) = arena.value(argument) {
                        each(Part::Value(quoted));
                    }
                }
            },
            Some(&ValueType::Thunk(body)) => each(Part::Computation(body)),
            Some(&ValueType::Record(ref fields)) => {
                for &field in fields.values() {
                    each(Part::Value(field));
                }
            },
            Some(&(ValueType::Product(ref parts) | ValueType::Sum(ref parts))) => {
                for &component in parts {
                    each(Part::Value(component));
                }
            },
            Some(&ValueType::Sigma { first, second }) => {
                each(Part::Value(first));
                each(Part::Value(second));
            },
            Some(&ValueType::List(element)) => each(Part::Value(element)),
            Some(_) | None => {},
        },
        Part::Computation(id) => match arena.comp_type(id) {
            Some(&(CompType::Arrow { domain, codomain } | CompType::Pi { domain, codomain })) => {
                each(Part::Value(domain));
                each(Part::Computation(codomain));
            },
            Some(&CompType::Returner { result, .. }) => each(Part::Value(result)),
            Some(&CompType::With(ref components)) => {
                for &component in components {
                    each(Part::Computation(component));
                }
            },
            Some(_) | None => {},
        },
    }
}

/// The value type a rebuilt child is.
///
/// # Specification
/// trivial.
const fn value_part(part: Option<&Part>) -> Option<ValueTypeId>
{
    match part {
        Some(&Part::Value(id)) => Some(id),
        Some(&Part::Computation(_)) | None => None,
    }
}

/// The computation type a rebuilt child is.
///
/// # Specification
/// trivial.
const fn computation_part(part: Option<&Part>) -> Option<CompTypeId>
{
    match part {
        Some(&Part::Computation(id)) => Some(id),
        Some(&Part::Value(_)) | None => None,
    }
}

/// `part` rebuilt over `children`, the replacements of its placed children
/// in order.
///
/// # Specification
/// - requires: `children` holds one replacement per child [`placed`] hands out
///   for `part`, of the same sort, in order.
/// - ensures: the same former over `children`, of `part`'s sort.
/// - fails: `None` for a child of the wrong sort or count, or a former with no
///   placeable child.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the erasure witness rebuilds an arrow, a returner, a
///   thunk and a list over erased children.
/// - witness: `staged::tests::every_placed_stage_is_erased`
#[spec(ensures: |ret| ret.is_none_or(|rebuilt| matches!((part, rebuilt),
    (Part::Value(_), Part::Value(_)) | (Part::Computation(_), Part::Computation(_)))))]
#[inline]
pub fn rebuild(
    arena: &mut CoreArena,
    part: Part,
    children: &[Part],
) -> Option<Part>
{
    let values = || {
        children
            .iter()
            .map(|child| value_part(Some(child)))
            .collect()
    };
    match part {
        Part::Value(id) => match arena.value_type(id).cloned() {
            Some(ValueType::Data {
                declaration,
                mut arguments,
            }) => {
                let mut next = children.iter();
                for argument in &mut arguments {
                    if let Some(&Value::Quote(_)) = arena.value(*argument) {
                        let quoted = value_part(next.next())?;
                        *argument = arena.value_quote(quoted);
                    }
                }
                Some(Part::Value(arena.value_type_data(declaration, arguments)))
            },
            Some(ValueType::Thunk(_)) => {
                let body = computation_part(children.first())?;
                Some(Part::Value(arena.value_type_thunk(body)))
            },
            Some(ValueType::Record(mut fields)) => {
                for (field, child) in fields.values_mut().zip(children) {
                    *field = value_part(Some(child))?;
                }
                (fields.len() == children.len())
                    .then(|| Part::Value(arena.value_type_record(fields)))
            },
            Some(ValueType::Product(_)) => {
                let parts: Option<Vec<ValueTypeId>> = values();
                Some(Part::Value(arena.value_type_product(&parts?)))
            },
            Some(ValueType::Sum(_)) => {
                let parts: Option<Vec<ValueTypeId>> = values();
                Some(Part::Value(arena.value_type_sum(&parts?)))
            },
            Some(ValueType::Sigma { .. }) => {
                let first = value_part(children.first())?;
                let second = value_part(children.get(1))?;
                Some(Part::Value(arena.value_type_sigma(first, second)))
            },
            Some(ValueType::List(_)) => {
                let element = value_part(children.first())?;
                Some(Part::Value(arena.value_type_list(element)))
            },
            Some(_) | None => None,
        },
        Part::Computation(id) => match arena.comp_type(id).cloned() {
            Some(CompType::Arrow { .. }) => {
                let domain = value_part(children.first())?;
                let codomain = computation_part(children.get(1))?;
                Some(Part::Computation(arena.comp_type_arrow(domain, codomain)))
            },
            Some(CompType::Pi { .. }) => {
                let domain = value_part(children.first())?;
                let codomain = computation_part(children.get(1))?;
                Some(Part::Computation(arena.comp_type_pi(domain, codomain)))
            },
            Some(CompType::Returner { effects, .. }) => {
                let result = value_part(children.first())?;
                Some(Part::Computation(
                    arena.comp_type_returner_with_effects(result, effects),
                ))
            },
            Some(CompType::With(_)) => {
                let parts: Option<Vec<CompTypeId>> = children
                    .iter()
                    .map(|child| computation_part(Some(child)))
                    .collect();
                Some(Part::Computation(arena.comp_type_with(&parts?)))
            },
            Some(_) | None => None,
        },
    }
}

/// `part` with every stage a placed position holds erased to the type it
/// refines.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `part` itself when no placed position holds a stage; otherwise
///   the same type over the erased children, of `part`'s sort, every placed
///   staged node replaced by its base.
/// - fails: `None` for a malformed arena, a placed child [`rebuild`] cannot
///   reassemble.
/// - panics: none.
///
/// # Termination
/// - reason: the `while let` worklist, not recursion; each node is opened once
///   and closed once.
/// - measure: the unread nodes under `part`, finite because the arena is
///   acyclic.
///
/// # Adequacy
/// - hypothesis: L3 — a function type staged in its domain, its returner and a
///   list's element erases to the plain function type, and a plain type is
///   answered as it stands.
/// - witness: `staged::tests::every_placed_stage_is_erased`
/// - witness: `staged::tests::a_plain_type_is_its_own_erasure`
#[spec(ensures: |ret| ret.is_none_or(|erased| matches!((part, erased),
    (Part::Value(_), Part::Value(_)) | (Part::Computation(_), Part::Computation(_)))))]
#[inline]
pub fn unstaged(
    arena: &mut CoreArena,
    part: Part,
) -> Option<Part>
{
    /// One step of the walk.
    enum Walk
    {
        /// Read the node: erase its stage and queue its placed children.
        Open(Part),
        /// Rebuild the node over its `count` children's erasures.
        Close(Part, usize),
    }
    let mut erased: Vec<Part> = Vec::new();
    let mut work = alloc::vec![Walk::Open(part)];
    while let Some(step) = work.pop() {
        match step {
            Walk::Open(node) => {
                let node = match node {
                    Part::Value(id) => match arena.value_type(id) {
                        Some(&ValueType::Staged { base, .. }) => Part::Value(base),
                        Some(_) | None => node,
                    },
                    Part::Computation(_) => node,
                };
                let mut children = Vec::new();
                placed(arena, node, |child| children.push(child));
                work.push(Walk::Close(node, children.len()));
                work.extend(children.into_iter().rev().map(Walk::Open));
            },
            Walk::Close(node, count) => {
                let start = erased.len().checked_sub(count)?;
                let children = erased.split_off(start);
                let mut kept = children.len() == count;
                let mut position = 0_usize;
                placed(arena, node, |child| {
                    kept = kept && children.get(position) == Some(&child);
                    position = position.saturating_add(1);
                });
                erased.push(if kept {
                    node
                }
                else {
                    rebuild(arena, node, &children)?
                });
            },
        }
    }
    match (erased.pop(), erased.is_empty()) {
        (Some(erased), true) => Some(erased),
        (Some(_) | None, _) => None,
    }
}
