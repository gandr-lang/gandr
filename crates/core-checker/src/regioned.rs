//! A definition abstracted over its caller's regions, read at one call: `def
//! read @[r : Region] (k : (() => Integer) at r) -> -F Integer`, called with
//! a thunk kept in a capability scope's region.
//!
//! The declared type keeps each value whose region the definition abstracts
//! at [`Region::Bound`]; nothing else names the binder, since a region is
//! erased and never computed. A call reads each binder off its arguments: a
//! variable argument whose type keeps a value, or holds a capability, where
//! its parameter's type names the binder shows the region it stands at there.
//! The binder stands at the region every other region shown outlives, the
//! shortest-lived of them, so each argument stands where its parameter is
//! asked. Where the arguments show none, or no region every other outlives,
//! it stands at the call's innermost region: every region open at the call
//! outlives that one, so an argument the call writes in place checks there,
//! and an answer kept at it lives no longer than the call's own extent. The
//! declared type with its binders renamed so is the type the call reads.
//!
//! A definition read outside a call keeps its binders. Its reader reads each
//! as a region that outlives the reader's own scopes and that the held region
//! outlives: one instantiation of the binder, which the definition's
//! parametricity makes as good as any.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::CompType;
use gandr_core_term::CoreArena;
use gandr_core_term::Renaming;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::effect::capability::Region;
use gandr_core_term::effect::capability::RegionBinder;
use gandr_core_term::effect::capability::RegionOrder;
use gandr_core_term::rename_value_type_traced;
use gandr_kernel_term::DeBruijnIndex;
use quenchant_shape::shape::Maybe;

use crate::CheckRefusal;
use crate::refusal::CoreNode;
use crate::refusal::TypeNode;

#[cfg(test)]
mod tests;

/// Why a call reads a definition's declared type as it stands.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Unread
{
    /// The declared type names no region binder.
    Unabstracted,
}

/// The region a binder stands at, given the regions its arguments show it at
/// and the call's innermost region.
///
/// # Specification
/// - ensures: the region of `shown` that every region of `shown` outlives, the
///   first such; `innermost` where `shown` is empty or holds no such region.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — two scoped regions place the deeper, two bound regions
///   place the innermost, and none places the innermost.
/// - witness: `regioned::tests::a_call_places_each_binder_at_the_shortest_region_shown_1221`
#[spec(ensures: |ret| shown.contains(&ret) || ret == innermost)]
fn placed(
    shown: &[Region],
    innermost: Region,
) -> Region
{
    shown
        .iter()
        .copied()
        .find(|&candidate| {
            shown
                .iter()
                .all(|&other| other.outlives(candidate) == RegionOrder::Outlives)
        })
        .unwrap_or(innermost)
}

/// Add to `shown` the region each binder `parameter` names stands at in the
/// argument type `argument`, reading the two types side by side.
///
/// # Specification
/// - requires: nothing.
/// - ensures: for every position the two types share through kept types,
///   thunks, returners, arrows, lists, products and sums of one length, where
///   the parameter keeps a value or holds a capability at a [`Region::Bound`]
///   and the argument keeps one or holds one at a region, that region is added
///   under the binder; a position where the two part ways adds nothing.
/// - fails: [`CheckRefusal::DanglingNode`] for a type that does not resolve.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Termination
/// - reason: the `while let` worklist, not recursion; each pair is popped once
///   per path that reaches it, and the arena is acyclic.
/// - measure: the paired paths not yet popped.
///
/// # Adequacy
/// - hypothesis: L3 — a parameter kept at a binder read against an argument
///   kept at a scope shows that scope, a thunk's answer shows through it, and
///   an argument kept nowhere shows nothing.
/// - witness: `regioned::tests::a_call_places_each_binder_at_the_shortest_region_shown_1221`
#[spec(captures: before = shown.len(), ensures: |ret| ret.is_err() || shown.len() >= before)]
fn shown_by(
    arena: &CoreArena,
    (parameter, argument): (ValueTypeId, ValueTypeId),
    shown: &mut BTreeMap<RegionBinder, Vec<Region>>,
) -> Result<(), CheckRefusal>
{
    let mut pairs = alloc::vec![(TypeNode::Value(parameter), TypeNode::Value(argument))];
    while let Some((wanted, found)) = pairs.pop() {
        let dangling = |node| CheckRefusal::DanglingNode {
            node: CoreNode::Type(node),
        };
        match (wanted, found) {
            (TypeNode::Value(wanted_id), TypeNode::Value(found_id)) => {
                let wanted_type = arena
                    .value_type(wanted_id)
                    .ok_or_else(|| dangling(wanted))?;
                let found_type = arena.value_type(found_id).ok_or_else(|| dangling(found))?;
                match (wanted_type, found_type) {
                    (
                        &ValueType::Kept {
                            value: wanted_value,
                            region: wanted_region,
                        },
                        &ValueType::Kept {
                            value: found_value,
                            region: found_region,
                        },
                    ) => {
                        if let Region::Bound(binder) = wanted_region {
                            shown.entry(binder).or_default().push(found_region);
                        }
                        pairs.push((TypeNode::Value(wanted_value), TypeNode::Value(found_value)));
                    },
                    (
                        &ValueType::Capability {
                            region: Region::Bound(binder),
                            ..
                        },
                        &ValueType::Capability {
                            region: found_region,
                            ..
                        },
                    ) => shown.entry(binder).or_default().push(found_region),
                    (&ValueType::Thunk(wanted_body), &ValueType::Thunk(found_body)) => {
                        pairs.push((
                            TypeNode::Computation(wanted_body),
                            TypeNode::Computation(found_body),
                        ));
                    },
                    (&ValueType::List(wanted_element), &ValueType::List(found_element)) => {
                        pairs.push((
                            TypeNode::Value(wanted_element),
                            TypeNode::Value(found_element),
                        ));
                    },
                    (
                        &ValueType::Product(ref wanted_parts),
                        &ValueType::Product(ref found_parts),
                    )
                    | (&ValueType::Sum(ref wanted_parts), &ValueType::Sum(ref found_parts))
                        if wanted_parts.len() == found_parts.len() =>
                    {
                        pairs.extend(wanted_parts.iter().zip(found_parts.iter()).map(
                            |(&left, &right)| (TypeNode::Value(left), TypeNode::Value(right)),
                        ));
                    },
                    _ => {},
                }
            },
            (TypeNode::Computation(wanted_id), TypeNode::Computation(found_id)) => {
                let wanted_type = arena.comp_type(wanted_id).ok_or_else(|| dangling(wanted))?;
                let found_type = arena.comp_type(found_id).ok_or_else(|| dangling(found))?;
                match (wanted_type, found_type) {
                    (
                        &CompType::Returner {
                            result: wanted_result,
                            ..
                        },
                        &CompType::Returner {
                            result: found_result,
                            ..
                        },
                    ) => {
                        pairs.push((
                            TypeNode::Value(wanted_result),
                            TypeNode::Value(found_result),
                        ));
                    },
                    (
                        &(CompType::Arrow {
                            domain: wanted_domain,
                            codomain: wanted_codomain,
                        }
                        | CompType::Pi {
                            domain: wanted_domain,
                            codomain: wanted_codomain,
                        }),
                        &(CompType::Arrow {
                            domain: found_domain,
                            codomain: found_codomain,
                        }
                        | CompType::Pi {
                            domain: found_domain,
                            codomain: found_codomain,
                        }),
                    ) => {
                        pairs.push((
                            TypeNode::Value(wanted_domain),
                            TypeNode::Value(found_domain),
                        ));
                        pairs.push((
                            TypeNode::Computation(wanted_codomain),
                            TypeNode::Computation(found_codomain),
                        ));
                    },
                    _ => {},
                }
            },
            (TypeNode::Value(_), TypeNode::Computation(_))
            | (TypeNode::Computation(_), TypeNode::Value(_)) => {},
        }
    }
    Ok(())
}

/// The renaming a call applying `spine` reads the definition declared at
/// `declared` by: each region binder the declared type names placed at the
/// region its arguments show it at, or at `innermost`.
///
/// # Specification
/// - requires: `spine` is the call's arguments, first applied first;
///   `innermost` is the innermost region open at the call, the caller's body at
///   depth zero when none is; `found` answers a variable argument's type.
/// - ensures: absent for a declared type that names no region binder; otherwise
///   a renaming of each binder it names to the region [`placed`] gives it from
///   the regions [`shown_by`] reads off each variable argument against its
///   parameter, the parameters read off the thunk's arrows and dependent arrows
///   in order.
/// - fails: `found`'s refusal; [`CheckRefusal::DanglingNode`] for a type that
///   does not resolve.
/// - panics: none.
/// - executable: none — the answer is the placement itself; a clause restating
///   it would read every argument's type against its parameter again.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — a function keeping two parameters at one binder and a
///   third at another, called with arguments kept at two scopes and one kept
///   nowhere, places the first binder at the deeper scope and the second at the
///   innermost region, in its parameters and its answer alike; a function
///   naming no binder reads as it stands.
/// - witness: `regioned::tests::a_call_places_each_binder_at_the_shortest_region_shown_1221`
/// - witness: `regioned::tests::a_definition_abstracting_no_region_reads_as_declared`
pub fn placement<Found>(
    arena: &CoreArena,
    declared: ValueTypeId,
    (spine, innermost): (&[ValueId], Region),
    mut found: Found,
) -> Result<Maybe<Renaming, Unread>, CheckRefusal>
where
    Found: FnMut(DeBruijnIndex) -> Result<ValueTypeId, CheckRefusal>,
{
    let named = crate::capability::binders(arena, TypeNode::Value(declared))?;
    if named.is_empty() {
        return Ok(Maybe::Absent(Unread::Unabstracted));
    }
    let mut shown: BTreeMap<RegionBinder, Vec<Region>> = BTreeMap::new();
    let mut body = match arena.value_type(declared) {
        Some(&ValueType::Thunk(body)) => Some(body),
        Some(_) | None => None,
    };
    for &argument in spine {
        let Some((parameter, codomain)) = body.and_then(|at| match arena.comp_type(at) {
            Some(&(CompType::Arrow { domain, codomain } | CompType::Pi { domain, codomain })) => {
                Some((domain, codomain))
            },
            Some(_) | None => None,
        })
        else {
            break;
        };
        body = Some(codomain);
        if let Some(&Value::Variable {
            zone: Zone::Intuitionistic,
            index,
        }) = arena.value(argument)
        {
            shown_by(arena, (parameter, found(index)?), &mut shown)?;
        }
    }
    let mut renaming = Renaming::new();
    for binder in named {
        let regions = shown.get(&binder).map_or(&[][..], Vec::as_slice);
        renaming.region(binder, placed(regions, innermost));
    }
    Ok(Maybe::Present(renaming))
}

/// The declared type `declared` read by `renaming`, the type a call reads.
///
/// # Specification
/// - requires: `declared` resolves in `arena`.
/// - ensures: as [`rename_value_type_traced`].
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`placement`].
/// - witness: `regioned::tests::a_call_places_each_binder_at_the_shortest_region_shown_1221`
#[spec(requires: arena.value_type(declared).is_some(), ensures: |ret| arena.value_type(ret).is_some())]
#[must_use]
pub fn instantiated(
    arena: &mut CoreArena,
    declared: ValueTypeId,
    renaming: &Renaming,
) -> ValueTypeId
{
    let mut carried = Vec::new();
    rename_value_type_traced(arena, declared, renaming, &mut carried)
}
