//! Element identity in the evaluator: the recursion that says, carrier by
//! carrier, what the paths of `Path(A, a, b)` are, and the comparison of two
//! transport motives.
//!
//! # The recursion
//!
//! [`clause`] reads a carrier's head and [`fibre`] reads it against two
//! evaluated endpoints, clause for clause with the kernel's identity
//! recursion:
//!
//! | carrier | endpoints | the paths |
//! |---|---|---|
//! | unit | any | [`Fibre::Unit`]: reflexivity alone |
//! | base | equal literals | [`Fibre::Unit`] |
//! | base | different literals | [`Fibre::Empty`] |
//! | base | a stuck endpoint | [`Fibre::Discrete`]: residual discrete equality |
//! | sum | one summand | [`Fibre::Payload`]: the payloads' paths |
//! | sum | two summands | [`Fibre::Empty`]: the cross-injection case |
//! | product | two tuples | [`Fibre::Components`]: each coordinate's paths |
//! | list | two empties / two cells / one of each | unit / head and tail / empty |
//! | `U(A → C)` | any | [`Fibre::Related`]: related inputs to related results |
//! | value universe | any | [`Fibre::Universe`]: the certified equivalences |
//! | abstract, decode of an open code, unknown | any | [`Fibre::Open`] |
//!
//! A stuck endpoint at a sum, a product or a list leaves the path type the
//! relation it names, [`Fibre::Suspended`]; every other former is
//! [`Fibre::Unclassified`].
//!
//! # Identity at an open type
//!
//! A sealed atom, a decode of a code no quote reaches and the unknown type
//! expose no structure, so the recursion has nothing to unfold: [`Fibre::Open`]
//! says the path type is its own neutral fibre there. The checker forms it,
//! reflexivity checks at it by endpoint conversion, and transport along it is
//! stuck except on reflexivity, where it reduces whatever the carrier.
//!
//! # Flows
//!
//! A flow evaluates to its former over its evaluated parts and reads back as
//! itself, and two flows convert when their formers agree and their parts
//! convert in order. A ride along one computes by the kernel's directed table
//! row for row, so a ride the checker admits computes the same here, in the
//! kernel and at runtime; along a stuck flow it stacks on the flow's spine.
//!
//! # Decisions
//!
//! - **The recursion classifies; it does not rewrite.** `Path(A, a, b)` stays a
//!   type of its own in conversion and in checking, and the recursion is read
//!   where a rule needs it. The alternative, unfolding the path type into the
//!   type it names during conversion, needs reflexivity to compute into each
//!   fibre's canonical inhabitant and transport to compute by the motive's
//!   structure at every former, the whole of a higher observational theory at
//!   once. Reversal: when transport computes at every former, the
//!   classification becomes the unfolding.
//! - **Funext covers first-order arguments.** The thunk clause relates inputs
//!   of a function's domain; a domain that is itself a function is the same
//!   clause one level up, and the clause does not yet descend into it.
//! - **Two motives compare by capture.** A stuck transport's motive is a type
//!   under a binder — a value type under one, or a telescope transport's
//!   computation type under the two its arrows bind — so two of them agree when
//!   they are one type over captures whose bindings agree, and wait for a
//!   binder otherwise.

use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::CompType;
use gandr_core_term::CompTypeId;
use gandr_core_term::CoreArena;
use gandr_core_term::Sort;
use gandr_core_term::Value;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::GroundSort;

use crate::arena::DomainArena;
use crate::arena::DomainFault;
use crate::arena::DomainValueId;
use crate::arena::ValueClosureId;
use crate::domain::DomainValue;
use crate::free::CoreTerm;
use crate::free::FreeFault;
use crate::free::FreeIndices;
use crate::free::Membership;

/// Why the recursion could not read its operands.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum IdentityFault
{
    /// A core id named no node of the arena read.
    DanglingTerm,
    /// The domain arena refused, in its own vocabulary.
    Domain(DomainFault),
}

/// Which clause of the recursion a carrier's head selects.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Clause
{
    /// The unit type.
    Unit,
    /// A base type: discrete equality of literals.
    Discrete,
    /// A sum: matching injections recurse, different ones are apart.
    Sum,
    /// A product: coordinates independently.
    Product,
    /// A native list: constructor by constructor.
    List,
    /// A thunk of a function: related inputs give related results.
    Function,
    /// The value universe: certified equivalences.
    Universe,
    /// An open carrier: the path type is its own neutral fibre.
    Open,
    /// A former the recursion has no clause for.
    Unclassified,
}

/// One coordinate the recursion reached: a carrier and the two endpoints it
/// relates there.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Coordinate
{
    /// The coordinate's carrier.
    carrier: ValueTypeId,
    /// The left endpoint's coordinate.
    left: DomainValueId,
    /// The right endpoint's coordinate.
    right: DomainValueId,
}

impl Coordinate
{
    /// The coordinate's carrier.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn carrier(&self) -> ValueTypeId
    {
        self.carrier
    }

    /// The left endpoint's coordinate.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn left(&self) -> DomainValueId
    {
        self.left
    }

    /// The right endpoint's coordinate.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn right(&self) -> DomainValueId
    {
        self.right
    }
}

/// What the paths of one path type are, by the recursion over its carrier.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Fibre
{
    /// Exactly one path, reflexivity.
    Unit,
    /// No path at all.
    Empty,
    /// Discrete equality of a base type with a stuck endpoint.
    Discrete,
    /// The paths of the one coordinate two matching injections carry.
    Payload(Coordinate),
    /// The paths of each coordinate, independently.
    Components(Vec<Coordinate>),
    /// Paths between related inputs taken to paths between the results.
    Related
    {
        /// The function's domain, where the inputs are related.
        domain: ValueTypeId,
        /// The function's codomain, where the results are related.
        codomain: CompTypeId,
    },
    /// The universe's certified equivalences.
    Universe,
    /// A stuck endpoint: the path type stays the relation it names.
    Suspended,
    /// An open carrier: the path type is its own neutral fibre.
    Open,
    /// A former the recursion has no clause for.
    Unclassified,
}

/// The clause a carrier's head selects.
///
/// # Specification
/// - requires: `carrier` is in weak head form: a decode of a quote has been
///   read through, so a remaining decode reads an open code.
/// - ensures: [`Clause::Unit`] for the empty product, [`Clause::Product`] for
///   any other product, [`Clause::Discrete`] for a base type, [`Clause::Sum`],
///   [`Clause::List`], [`Clause::Function`] for a thunk of an arrow,
///   [`Clause::Universe`] for the value universe, [`Clause::Open`] for an
///   abstract type, a decode and the unknown type, and [`Clause::Unclassified`]
///   for every other former.
/// - provides: the head reading [`fibre`] selects its row by.
/// - fails: [`IdentityFault::DanglingTerm`] for a carrier, or a thunk's body,
///   the arena does not hold.
/// - panics: none.
///
/// # Errors
/// - [`IdentityFault::DanglingTerm`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — one carrier per clause, an abstract atom and a decode of
///   a variable both open, a record unclassified; moving a former to another
///   clause changes its answer.
/// - witness: `identity::tests::every_carrier_selects_its_clause`
#[spec(ensures: |ret| core.value_type(carrier).is_some() || ret == Err(IdentityFault::DanglingTerm))]
#[inline]
pub fn clause(
    core: &CoreArena,
    carrier: ValueTypeId,
) -> Result<Clause, IdentityFault>
{
    Ok(
        match *core
            .value_type(carrier)
            .ok_or(IdentityFault::DanglingTerm)?
        {
            ValueType::Product(ref components) if components.is_empty() => Clause::Unit,
            ValueType::Product(_) => Clause::Product,
            ValueType::Base(_) => Clause::Discrete,
            ValueType::Sum(_) => Clause::Sum,
            ValueType::List(_) => Clause::List,
            ValueType::Thunk(body) => {
                match *core.comp_type(body).ok_or(IdentityFault::DanglingTerm)? {
                    CompType::Arrow { .. } => Clause::Function,
                    CompType::Returner { .. }
                    | CompType::Pi { .. }
                    | CompType::With(..)
                    | CompType::Element { .. }
                    | CompType::Unknown => Clause::Unclassified,
                }
            },
            ValueType::Universe {
                sort: Sort::Ground(GroundSort::Value),
                ..
            } => Clause::Universe,
            ValueType::Abstract(_) | ValueType::Element { .. } | ValueType::Unknown => Clause::Open,
            ValueType::Universe { .. }
            | ValueType::Data { .. }
            | ValueType::Record(_)
            | ValueType::PathUniverse(..)
            | ValueType::Path { .. }
            | ValueType::Stack { .. }
            | ValueType::Capability { .. }
            | ValueType::Lift { .. }
            | ValueType::StaticPi { .. }
            | ValueType::Sigma { .. }
            | ValueType::Session(_)
            | ValueType::Flow { .. }
            | ValueType::Run(_)
            | ValueType::Staged { .. } => Clause::Unclassified,
        },
    )
}

/// What the paths of `Path(carrier, left, right)` are.
///
/// # Specification
/// - requires: `carrier` is in weak head form, and `left` and `right` are
///   evaluated inhabitants of it.
/// - ensures: the row of the recursion's table the carrier and the two
///   endpoints select, as this module's table states it.
/// - provides: the identity recursion over evaluated endpoints.
/// - fails: [`IdentityFault::DanglingTerm`] for a carrier the arena does not
///   hold; [`IdentityFault::Domain`] for an endpoint or a field the domain does
///   not hold.
/// - panics: none.
///
/// # Errors
/// - [`IdentityFault::DanglingTerm`], [`IdentityFault::Domain`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — each clause is witnessed at its own carrier, the
///   cross-injection emptiness and the distinct literals separately from the
///   matching cases, and a stuck endpoint separately from a canonical one;
///   pairing the wrong coordinates, conflating the two emptiness cases with the
///   matching ones, or classifying an open carrier changes an answer.
/// - witness: `identity::tests::unit_and_discrete_carriers_unfold_by_their_endpoints`
/// - witness: `identity::tests::different_injections_have_no_path`
/// - witness: `identity::tests::matching_injections_recurse_into_the_payload`
/// - witness: `identity::tests::product_paths_are_componentwise`
/// - witness: `identity::tests::list_paths_follow_the_constructors`
/// - witness: `identity::tests::function_paths_relate_inputs_to_results`
/// - witness: `identity::tests::open_carriers_unfold_to_nothing`
/// - witness: `identity::tests::a_product_endpoint_of_another_width_is_refused_on_either_side`
#[spec(ensures: |ret| core.value_type(carrier).is_some() || ret == Err(IdentityFault::DanglingTerm))]
#[inline]
pub fn fibre(
    core: &CoreArena,
    domain: &DomainArena,
    carrier: ValueTypeId,
    left: DomainValueId,
    right: DomainValueId,
) -> Result<Fibre, IdentityFault>
{
    let selected = clause(core, carrier)?;
    let dangling = IdentityFault::Domain(DomainFault::Dangling);
    let ends = (
        *domain.value(left).ok_or(dangling)?,
        *domain.value(right).ok_or(dangling)?,
    );
    let node = core
        .value_type(carrier)
        .ok_or(IdentityFault::DanglingTerm)?;
    Ok(match (selected, node) {
        (Clause::Unit, _) => Fibre::Unit,
        (Clause::Discrete, _) => match ends {
            (
                DomainValue::Literal { literal: one, .. },
                DomainValue::Literal { literal: other, .. },
            ) => match (core.value(one), core.value(other)) {
                (Some(&Value::Literal(ref one)), Some(&Value::Literal(ref other))) => {
                    if one == other {
                        Fibre::Unit
                    }
                    else {
                        Fibre::Empty
                    }
                },
                _ => return Err(IdentityFault::DanglingTerm),
            },
            _ => Fibre::Discrete,
        },
        (Clause::Sum, &ValueType::Sum(ref summands)) => match ends {
            (
                DomainValue::Injection {
                    summand: one,
                    body: first,
                    ..
                },
                DomainValue::Injection {
                    summand: other,
                    body: second,
                    ..
                },
            ) => {
                if one == other {
                    let carrier = *summands
                        .get(usize::from(one))
                        .ok_or(IdentityFault::DanglingTerm)?;
                    Fibre::Payload(Coordinate {
                        carrier,
                        left: first,
                        right: second,
                    })
                }
                else {
                    Fibre::Empty
                }
            },
            _ => Fibre::Suspended,
        },
        (Clause::Product, &ValueType::Product(ref components)) => match ends {
            (DomainValue::Tuple { fields: one, .. }, DomainValue::Tuple { fields: other, .. }) => {
                let one = domain.fields(one).map_err(IdentityFault::Domain)?;
                let other = domain.fields(other).map_err(IdentityFault::Domain)?;
                if one.len() != components.len() || other.len() != components.len() {
                    return Err(IdentityFault::Domain(DomainFault::Dangling));
                }
                Fibre::Components(
                    components
                        .iter()
                        .zip(one.iter().zip(other))
                        .map(|(&carrier, (&left, &right))| Coordinate {
                            carrier,
                            left,
                            right,
                        })
                        .collect(),
                )
            },
            _ => Fibre::Suspended,
        },
        (Clause::List, &ValueType::List(element)) => match ends {
            (DomainValue::ListNil { .. }, DomainValue::ListNil { .. }) => Fibre::Unit,
            (
                DomainValue::ListCons {
                    first: head,
                    second: tail,
                    ..
                },
                DomainValue::ListCons {
                    first: other_head,
                    second: other_tail,
                    ..
                },
            ) => Fibre::Components(Vec::from([
                Coordinate {
                    carrier: element,
                    left: head,
                    right: other_head,
                },
                Coordinate {
                    carrier,
                    left: tail,
                    right: other_tail,
                },
            ])),
            (DomainValue::ListNil { .. }, DomainValue::ListCons { .. })
            | (DomainValue::ListCons { .. }, DomainValue::ListNil { .. }) => Fibre::Empty,
            _ => Fibre::Suspended,
        },
        (Clause::Function, &ValueType::Thunk(body)) => {
            match *core.comp_type(body).ok_or(IdentityFault::DanglingTerm)? {
                CompType::Arrow {
                    domain: input,
                    codomain,
                } => Fibre::Related {
                    domain: input,
                    codomain,
                },
                CompType::Returner { .. }
                | CompType::Pi { .. }
                | CompType::Element { .. }
                | CompType::Unknown
                | CompType::With(..) => return Err(IdentityFault::DanglingTerm),
            }
        },
        (Clause::Universe, _) => Fibre::Universe,
        (Clause::Open, _) => Fibre::Open,
        (Clause::Unclassified, _) => Fibre::Unclassified,
        (Clause::Sum | Clause::Product | Clause::List | Clause::Function, _) => {
            return Err(IdentityFault::DanglingTerm);
        },
    })
}

/// How two stuck transports' motives compare without opening their binder.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Motives
{
    /// One motive type over captures of one shape: the bindings to compare,
    /// pairwise, intuitionistic zone first.
    Alike(Vec<(DomainValueId, DomainValueId)>),
    /// Different motive types, or captures of different shapes: a binder must
    /// be opened to tell.
    Unlike,
}

/// Compare two transport motives by their body and their captures.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`Motives::Alike`] with every binding pair when both closures
///   hold one body, a one-binder transport's value type or a telescope
///   transport's computation type, over environments of one depth per zone;
///   [`Motives::Unlike`] otherwise.
/// - provides: the congruence two stuck transports' motives settle by in the
///   structural walk, which never opens a binder.
/// - fails: [`DomainFault::Dangling`] for a closure the arena does not hold.
/// - panics: none.
///
/// # Errors
/// - [`DomainFault::Dangling`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — two evaluations of one transport give alike motives whose
///   bindings pair up, and transports at two different motives give unlike
///   ones; comparing ids instead of bodies, or dropping the bindings, changes
///   the answer.
/// - witness: `identity::tests::stuck_transports_compare_by_motive_and_operand`
#[spec(ensures: |ret| match (domain.value_closure(left), domain.value_closure(right)) {
    | (Some(one), Some(other)) => ret.as_ref().is_ok_and(|motives| matches!(motives, Motives::Alike(_)) == (one.body() == other.body()
        && [Zone::Intuitionistic, Zone::Linear].iter().all(|&zone| one.environment().depth(zone) == other.environment().depth(zone)))),
    | _ => ret == Err(DomainFault::Dangling),
})]
#[inline]
pub fn motives(
    domain: &DomainArena,
    left: ValueClosureId,
    right: ValueClosureId,
) -> Result<Motives, DomainFault>
{
    let (Some(one), Some(other)) = (domain.value_closure(left), domain.value_closure(right))
    else {
        return Err(DomainFault::Dangling);
    };
    let zones = [Zone::Intuitionistic, Zone::Linear];
    let shaped = zones
        .iter()
        .all(|&zone| one.environment().depth(zone) == other.environment().depth(zone));
    if one.body() != other.body() || !shaped {
        return Ok(Motives::Unlike);
    }
    let mut bindings = Vec::new();
    for zone in zones {
        bindings.extend(
            one.environment()
                .bindings(zone)
                .iter()
                .copied()
                .zip(other.environment().bindings(zone).iter().copied()),
        );
    }
    Ok(Motives::Alike(bindings))
}

/// How a one-binder transport's or ride's family reads at its operand.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum TransportFamily
{
    /// The singleton `y. Path(D, l, y)` or `y. Flow(D, l, y)`: its right
    /// endpoint is the binder, and its carrier and left endpoint never read
    /// it.
    Singleton,
    /// Any other family.
    Other,
}

/// Read a one-binder transport's or ride's family as the singleton or not.
///
/// # Specification
/// - requires: `family` is a transport or ride motive's value type, read under
///   its one binder.
/// - ensures: [`TransportFamily::Singleton`] exactly when `family` is a path or
///   flow type whose right endpoint is the binder and whose carrier and left
///   endpoint read no index the binder binds; [`TransportFamily::Other`]
///   otherwise.
/// - provides: the guard of the singleton row, the kernel's own clause:
///   transport in `y. Path(D, l, y)` carries `here(l)` to the path itself,
///   which is what lets `J` check its identity over the path, and a ride in `y.
///   Flow(D, l, y)` composes the ridden flow with the flow it rides along.
/// - fails: the free-index walk's fault for a dangling node.
/// - panics: none.
///
/// # Errors
/// A [`FreeFault`], as above.
///
/// # Adequacy
/// - hypothesis: L3 — the singleton returns the path, a ride in the flow
///   singleton composes, and a family whose left endpoint is the binder keeps
///   the transport stuck.
/// - witness: `identity::tests::transport_in_the_singleton_returns_the_path`
/// - witness: `identity::tests::rides_compute_by_the_kernels_rows`
#[spec(ensures: |ret| !matches!(ret, Ok(TransportFamily::Singleton)) || matches!(
    core.value_type(family),
    Some(&(ValueType::Path { right, .. } | ValueType::Flow { target: right, .. }))
        if matches!(core.value(right), Some(&Value::Variable { zone: Zone::Intuitionistic, index }) if u32::from(index) == 0_u32)
))]
pub(crate) fn transport_family(
    core: &CoreArena,
    family: ValueTypeId,
) -> Result<TransportFamily, FreeFault>
{
    let Some(
        &(ValueType::Path {
            carrier,
            left,
            right,
        }
        | ValueType::Flow {
            carrier,
            source: left,
            target: right,
        }),
    ) = core.value_type(family)
    else {
        return Ok(TransportFamily::Other);
    };
    let bound = DeBruijnIndex::from(0_u32);
    let endpoint = matches!(
        core.value(right),
        Some(&Value::Variable {
            zone: Zone::Intuitionistic,
            index,
        }) if index == bound
    );
    if !endpoint {
        return Ok(TransportFamily::Other);
    }
    let mut free = FreeIndices::default();
    if free.of_type(core, carrier)?.intuitionistic().holds(bound) == Membership::Held {
        return Ok(TransportFamily::Other);
    }
    Ok(
        match free
            .of(core, CoreTerm::Value(left))?
            .intuitionistic()
            .holds(bound)
        {
            Membership::Held => TransportFamily::Other,
            Membership::Absent => TransportFamily::Singleton,
        },
    )
}

/// Whether a one-binder motive never reads its binder: the constant motive,
/// along which every ride returns its value unchanged.
///
/// # Specification
/// - requires: `family` is a ride motive's value type, read under its one
///   binder.
/// - ensures: [`Membership::Absent`] exactly when no node of `family` reads the
///   index its binder binds.
/// - provides: the guard of the kernel's constant-motive row.
/// - fails: the free-index walk's fault for a dangling node.
/// - panics: none.
/// - executable: none — the free-index walk is the only reading of the clause,
///   so a predicate would restate the body.
///
/// # Errors
/// A [`FreeFault`], as above.
///
/// # Adequacy
/// - hypothesis: L3 — a ride along a stuck flow in a constant motive returns
///   its value, and in the identity motive stays stuck.
/// - witness: `identity::tests::rides_compute_by_the_kernels_rows`
pub(crate) fn binder_read(
    core: &CoreArena,
    family: ValueTypeId,
) -> Result<Membership, FreeFault>
{
    let mut free = FreeIndices::default();
    Ok(free
        .of_type(core, family)?
        .intuitionistic()
        .holds(DeBruijnIndex::from(0_u32)))
}

#[cfg(test)]
mod tests;
