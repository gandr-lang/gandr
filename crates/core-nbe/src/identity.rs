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
            | ValueType::Product(ref components) if components.is_empty() => Clause::Unit,
            | ValueType::Product(_) => Clause::Product,
            | ValueType::Base(_) => Clause::Discrete,
            | ValueType::Sum(_) => Clause::Sum,
            | ValueType::List(_) => Clause::List,
            | ValueType::Thunk(body) => {
                match *core.comp_type(body).ok_or(IdentityFault::DanglingTerm)? {
                    | CompType::Arrow { .. } => Clause::Function,
                    | CompType::Returner { .. }
                    | CompType::Pi { .. }
                    | CompType::With(..)
                    | CompType::Element { .. }
                    | CompType::Unknown => Clause::Unclassified,
                }
            },
            | ValueType::Universe {
                sort: Sort::Ground(GroundSort::Value),
                ..
            } => Clause::Universe,
            | ValueType::Abstract(_) | ValueType::Element { .. } | ValueType::Unknown => {
                Clause::Open
            },
            | ValueType::Universe { .. }
            | ValueType::Data { .. }
            | ValueType::Record(_)
            | ValueType::PathUniverse(..)
            | ValueType::Path { .. }
            | ValueType::Stack { .. }
            | ValueType::Capability { .. }
            | ValueType::Lift { .. }
            | ValueType::StaticPi { .. }
            | ValueType::Session(_)
            | ValueType::Flow { .. }
            | ValueType::Run(_) => Clause::Unclassified,
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
        | (Clause::Unit, _) => Fibre::Unit,
        | (Clause::Discrete, _) => match ends {
            | (
                DomainValue::Literal { literal: one, .. },
                DomainValue::Literal { literal: other, .. },
            ) => match (core.value(one), core.value(other)) {
                | (Some(&Value::Literal(ref one)), Some(&Value::Literal(ref other))) => {
                    if one == other {
                        Fibre::Unit
                    }
                    else {
                        Fibre::Empty
                    }
                },
                | _ => return Err(IdentityFault::DanglingTerm),
            },
            | _ => Fibre::Discrete,
        },
        | (Clause::Sum, &ValueType::Sum(ref summands)) => match ends {
            | (
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
            | _ => Fibre::Suspended,
        },
        | (Clause::Product, &ValueType::Product(ref components)) => match ends {
            | (
                DomainValue::Tuple { fields: one, .. },
                DomainValue::Tuple { fields: other, .. },
            ) => {
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
            | _ => Fibre::Suspended,
        },
        | (Clause::List, &ValueType::List(element)) => match ends {
            | (DomainValue::ListNil { .. }, DomainValue::ListNil { .. }) => Fibre::Unit,
            | (
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
            | (DomainValue::ListNil { .. }, DomainValue::ListCons { .. })
            | (DomainValue::ListCons { .. }, DomainValue::ListNil { .. }) => Fibre::Empty,
            | _ => Fibre::Suspended,
        },
        | (Clause::Function, &ValueType::Thunk(body)) => {
            match *core.comp_type(body).ok_or(IdentityFault::DanglingTerm)? {
                | CompType::Arrow {
                    domain: input,
                    codomain,
                } => Fibre::Related {
                    domain: input,
                    codomain,
                },
                | _ => return Err(IdentityFault::DanglingTerm),
            }
        },
        | (Clause::Universe, _) => Fibre::Universe,
        | (Clause::Open, _) => Fibre::Open,
        | (Clause::Unclassified, _) => Fibre::Unclassified,
        | (Clause::Sum | Clause::Product | Clause::List | Clause::Function, _) => {
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
            | Membership::Held => TransportFamily::Other,
            | Membership::Absent => TransportFamily::Singleton,
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
mod tests
{
    use alloc::string::String;
    use alloc::vec::Vec;

    use gandr_core_term::CertificateEquality;
    use gandr_core_term::ComputationId;
    use gandr_core_term::CoreArena;
    use gandr_core_term::DefinitionalEnvironment;
    use gandr_core_term::ValueId;
    use gandr_core_term::ValueTypeId;
    use gandr_core_term::equal_certificate_syntax;
    use gandr_core_term::identity::back;
    use gandr_core_term::identity::cong;
    use gandr_core_term::identity::then;
    use gandr_kernel_check_memo::NullMemo;
    use gandr_kernel_conversion_trace::NullSink;
    use gandr_kernel_strata::Level;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::Literal;
    use gandr_kernel_term::Side;
    use gandr_kernel_term::StringLiteral;

    use super::Clause;
    use super::Coordinate;
    use super::Fibre;
    use super::clause;
    use super::fibre;
    use crate::arena::DomainArena;
    use crate::arena::DomainValueId;
    use crate::eval::Definitions;
    use crate::eval::Fuel;
    use crate::eval::LoweredChain;
    use crate::eval::eval_computation;
    use crate::eval::eval_value;
    use crate::machine::MachineSettings;
    use crate::machine::MachineVerdict;
    use crate::machine::Problem;
    use crate::machine::decide;
    use crate::readback::ReadbackMode;
    use crate::readback::readback_computation;

    /// A budget far above any fixture below.
    ///
    /// # Specification
    /// trivial.
    fn ample() -> Fuel
    {
        Fuel::from(4_096_u32)
    }

    /// The text literals the fixtures below compare.
    #[derive(Clone, Copy)]
    enum Word
    {
        /// `"five"`.
        Five,
        /// `"six"`.
        Six,
        /// `"seven"`.
        Seven,
    }

    /// A text literal.
    ///
    /// # Specification
    /// trivial.
    fn literal(
        core: &mut CoreArena,
        word: Word,
    ) -> ValueId
    {
        let content = match word {
            | Word::Five => "five",
            | Word::Six => "six",
            | Word::Seven => "seven",
        };
        core.value_literal(Literal::Text(StringLiteral::new(String::from(content))))
    }

    /// A rigid stand-in for a path no rule reduces: a constant with no body.
    ///
    /// # Specification
    /// trivial.
    fn stuck(
        core: &mut CoreArena,
        position: ConstantIndex,
    ) -> ValueId
    {
        core.value_constant(position)
    }

    /// The normal form of a computation, wrapped as a thunk for comparison.
    ///
    /// # Specification
    /// trivial.
    fn normal(
        core: &mut CoreArena,
        computation: ComputationId,
    ) -> ValueId
    {
        let chain = LoweredChain::new();
        let environment = DefinitionalEnvironment::new();
        let definitions = Definitions::new(&chain, &environment, environment.root());
        let mut domain = DomainArena::new();
        let evaluated = eval_computation(core, &mut domain, definitions, ample(), computation)
            .expect("closed identity terms evaluate");
        let read = readback_computation(
            core,
            &mut domain,
            definitions,
            ReadbackMode::Unfolding,
            ample(),
            evaluated,
        )
        .expect("closed identity terms read back");
        core.value_thunk(read)
    }

    /// How the normal form of `computation` compares with `expected` as
    /// written.
    ///
    /// # Specification
    /// trivial.
    fn normalises_to(
        core: &mut CoreArena,
        computation: ComputationId,
        expected: ComputationId,
    ) -> CertificateEquality
    {
        let read = normal(core, computation);
        let expected = core.value_thunk(expected);
        equal_certificate_syntax(core, read, expected)
    }

    /// The evaluated values `values` stand for, in a fresh domain.
    ///
    /// # Specification
    /// trivial.
    fn evaluated<const N: usize>(
        core: &CoreArena,
        domain: &mut DomainArena,
        values: [ValueId; N],
    ) -> [DomainValueId; N]
    {
        let chain = LoweredChain::new();
        let environment = DefinitionalEnvironment::new();
        let definitions = Definitions::new(&chain, &environment, environment.root());
        values.map(|value| {
            eval_value(core, domain, definitions, ample(), value).expect("closed values evaluate")
        })
    }

    /// The string base type.
    ///
    /// # Specification
    /// trivial.
    fn text_type(core: &mut CoreArena) -> ValueTypeId
    {
        core.value_type_base(BaseType::String)
    }

    #[test]
    fn transport_along_here_is_the_identity()
    {
        let mut core = CoreArena::new();
        let five = literal(&mut core, Word::Five);
        let seven = literal(&mut core, Word::Seven);
        let carrier = text_type(&mut core);
        let moving = core.value_variable(gandr_core_term::Zone::Intuitionistic, 0_u32.into());
        let motive = core.value_type_path(carrier, moving, moving);
        let path = core.value_here(five);
        let operand = core.value_here(seven);
        let transported = core.computation_path_transport(motive, path, operand);
        let expected = core.computation_return(operand);
        assert_eq!(
            normalises_to(&mut core, transported, expected),
            CertificateEquality::Equal,
            "transport along reflexivity returns its operand untouched"
        );
    }

    #[test]
    fn transport_in_the_singleton_returns_the_path()
    {
        let mut core = CoreArena::new();
        let five = literal(&mut core, Word::Five);
        let carrier = text_type(&mut core);
        let endpoint = core.value_variable(gandr_core_term::Zone::Intuitionistic, 0_u32.into());
        let singleton = core.value_type_path(carrier, five, endpoint);
        let path = stuck(&mut core, ConstantIndex::from(0_usize));
        let start = core.value_here(five);
        let transported = core.computation_path_transport(singleton, path, start);
        let expected = core.computation_return(path);
        assert_eq!(
            normalises_to(&mut core, transported, expected),
            CertificateEquality::Equal,
            "reflexivity transported in the singleton is the path itself"
        );
        let diagonal = core.value_type_path(carrier, endpoint, endpoint);
        let moved = core.computation_path_transport(diagonal, path, start);
        assert_eq!(
            normalises_to(&mut core, moved, moved),
            CertificateEquality::Equal,
            "a family whose left endpoint is the binder is no singleton and stays stuck"
        );
    }

    #[test]
    fn transport_along_a_stuck_path_is_stuck()
    {
        let mut core = CoreArena::new();
        let five = literal(&mut core, Word::Five);
        let carrier = text_type(&mut core);
        let path = stuck(&mut core, ConstantIndex::from(0_usize));
        let transported = core.computation_path_transport(carrier, path, five);
        assert_eq!(
            normalises_to(&mut core, transported, transported),
            CertificateEquality::Equal,
            "a transport along a path no rule reduces reads back as itself"
        );
    }

    /// The telescope motive `Π (y : Text). Π (z : Text). F Path(Text, z, y)`,
    /// whose fibre at a point is no singleton, so its transport keeps the
    /// operand's own form.
    ///
    /// # Specification
    /// trivial.
    fn telescope_motive(core: &mut CoreArena) -> gandr_core_term::CompTypeId
    {
        let carrier = text_type(core);
        let outer = core.value_variable(gandr_core_term::Zone::Intuitionistic, 1_u32.into());
        let inner = core.value_variable(gandr_core_term::Zone::Intuitionistic, 0_u32.into());
        let body = core.value_type_path(carrier, inner, outer);
        let returned = core.comp_type_returner(body);
        let entry = core.comp_type_pi(carrier, returned);
        core.comp_type_pi(carrier, entry)
    }

    #[test]
    fn telescope_transport_along_here_is_the_identity()
    {
        let mut core = CoreArena::new();
        let five = literal(&mut core, Word::Five);
        let six = literal(&mut core, Word::Six);
        let seven = literal(&mut core, Word::Seven);
        let motive = telescope_motive(&mut core);
        let path = core.value_here(five);
        let over = core.value_here(six);
        let operand = core.value_here(seven);
        let transported = core.computation_telescope_transport(motive, path, six, over, operand);
        let expected = core.computation_return(operand);
        assert_eq!(
            normalises_to(&mut core, transported, expected),
            CertificateEquality::Equal,
            "transport along reflexivity over reflexivity returns its operand untouched"
        );
    }

    #[test]
    fn telescope_transport_along_here_replays_the_fibre()
    {
        let mut core = CoreArena::new();
        let five = literal(&mut core, Word::Five);
        let six = literal(&mut core, Word::Six);
        let seven = literal(&mut core, Word::Seven);
        let motive = telescope_motive(&mut core);
        let path = core.value_here(five);
        let over = stuck(&mut core, ConstantIndex::from(0_usize));
        let operand = core.value_here(seven);
        let transported = core.computation_telescope_transport(motive, path, six, over, operand);
        let carrier = text_type(&mut core);
        let inner = core.value_variable(gandr_core_term::Zone::Intuitionistic, 0_u32.into());
        let fibre = core.value_type_path(carrier, inner, five);
        let expected = core.computation_path_transport(fibre, over, operand);
        assert_eq!(
            normalises_to(&mut core, transported, expected),
            CertificateEquality::Equal,
            "along reflexivity the operand transports along the identity over it in the fibre \
             at the path's point"
        );
    }

    #[test]
    fn telescope_transport_along_a_stuck_path_is_stuck()
    {
        let mut core = CoreArena::new();
        let six = literal(&mut core, Word::Six);
        let seven = literal(&mut core, Word::Seven);
        let motive = telescope_motive(&mut core);
        let path = stuck(&mut core, ConstantIndex::from(0_usize));
        let over = stuck(&mut core, ConstantIndex::from(1_usize));
        let transported = core.computation_telescope_transport(motive, path, six, over, seven);
        assert_eq!(
            normalises_to(&mut core, transported, transported),
            CertificateEquality::Equal,
            "a telescope transport along a path no rule reduces reads back as itself"
        );
        let other = core.computation_telescope_transport(motive, path, seven, over, seven);
        assert_eq!(
            normalises_to(&mut core, transported, other),
            CertificateEquality::Different,
            "the stuck form keeps its start"
        );
    }

    #[test]
    fn transport_through_a_product_is_componentwise()
    {
        let mut core = CoreArena::new();
        let five = literal(&mut core, Word::Five);
        let seven = literal(&mut core, Word::Seven);
        let carrier = text_type(&mut core);
        let unit = core.value_type_unit();
        let motive = core.value_type_product(&[carrier, unit]);
        let path = stuck(&mut core, ConstantIndex::from(0_usize));
        let empty = core.value_unit();
        let operand = core.value_tuple(&[five, empty]);
        let transported = core.computation_path_transport(motive, path, operand);

        let first = core.computation_path_transport(carrier, path, five);
        let first = core.value_returned(first);
        // The unit coordinate is itself a product of no components, so its
        // transport computes to the empty tuple.
        let pair = core.value_tuple(&[first, empty]);
        let expected = core.computation_return(pair);
        assert_eq!(
            normalises_to(&mut core, transported, expected),
            CertificateEquality::Equal,
            "each coordinate is transported in its own motive, in order"
        );
        let second = core.computation_path_transport(unit, path, empty);
        let second = core.value_returned(second);

        let swapped = core.value_tuple(&[second, first]);
        let swapped = core.computation_return(swapped);
        assert_eq!(
            normalises_to(&mut core, transported, swapped),
            CertificateEquality::Different
        );
        let other = core.computation_path_transport(carrier, path, seven);
        let other = core.value_returned(other);
        let other = core.value_tuple(&[other, second]);
        let other = core.computation_return(other);
        assert_eq!(
            normalises_to(&mut core, transported, other),
            CertificateEquality::Different
        );
    }

    #[test]
    fn transport_through_a_sum_keeps_the_summand()
    {
        let mut core = CoreArena::new();
        let five = literal(&mut core, Word::Five);
        let carrier = text_type(&mut core);
        let unit = core.value_type_unit();
        let motive = core.value_type_sum(&[unit, carrier]);
        let path = stuck(&mut core, ConstantIndex::from(0_usize));
        let operand = core.value_injection(Side::Right.into(), five);
        let transported = core.computation_path_transport(motive, path, operand);

        let payload = core.computation_path_transport(carrier, path, five);
        let payload = core.value_returned(payload);
        let injected = core.value_injection(Side::Right.into(), payload);
        let expected = core.computation_return(injected);
        assert_eq!(
            normalises_to(&mut core, transported, expected),
            CertificateEquality::Equal,
            "the payload is transported in its summand's motive and injected again"
        );
        let wrong = core.value_injection(Side::Left.into(), payload);
        let wrong = core.computation_return(wrong);
        assert_eq!(
            normalises_to(&mut core, transported, wrong),
            CertificateEquality::Different
        );
    }

    #[test]
    fn transport_moves_a_list_through_a_universe_path()
    {
        // Negation as a universe equivalence of Bool with itself, in the
        // motive `y. List(El y)`: each head is carried along it, in order.
        let mut core = CoreArena::new();
        let unit = core.value_unit();
        let [truth, falsity] =
            [Side::Left, Side::Right].map(|side| core.value_injection(side.into(), unit));
        let negated = [falsity, truth].map(|value| core.computation_return(value));
        let bound = core.value_variable(gandr_core_term::Zone::Intuitionistic, 0_u32.into());
        let body = core.computation_case(bound, &negated);
        let lambda = core.computation_lambda(body);
        let not = core.value_thunk(lambda);
        let path = core.value_equiv(not, not);
        let element = core.value_type_element(bound, gandr_kernel_strata::Level::zero());
        let motive = core.value_type_list(element);
        let list = |core: &mut CoreArena, heads: [ValueId; 2]| {
            let nil = core.value_list_nil();
            heads
                .iter()
                .rev()
                .fold(nil, |tail, &head| core.value_list_cons(head, tail))
        };
        let operand = list(&mut core, [truth, falsity]);
        let transported = core.computation_path_transport(motive, path, operand);
        let moved = list(&mut core, [falsity, truth]);
        let expected = core.computation_return(moved);
        assert_eq!(
            normalises_to(&mut core, transported, expected),
            CertificateEquality::Equal,
            "each head is negated and the spine kept"
        );
        let kept = core.computation_return(operand);
        assert_eq!(
            normalises_to(&mut core, transported, kept),
            CertificateEquality::Different
        );
        let nil = core.value_list_nil();
        let empty = core.computation_path_transport(motive, path, nil);
        let returned = core.computation_return(nil);
        assert_eq!(
            normalises_to(&mut core, empty, returned),
            CertificateEquality::Equal,
            "the empty list is carried unchanged"
        );
    }

    #[test]
    fn a_compound_endpoint_stands_for_what_it_returns()
    {
        let mut core = CoreArena::new();
        let five = literal(&mut core, Word::Five);
        let returned = core.computation_return(five);
        let compound = core.value_returned(returned);
        let reflexive = core.value_here(compound);
        let read = core.computation_return(reflexive);
        let at_five = core.value_here(five);
        let expected = core.computation_return(at_five);
        assert_eq!(
            normalises_to(&mut core, read, expected),
            CertificateEquality::Equal,
            "a compound endpoint that returns is the value it returns"
        );

        let head = stuck(&mut core, ConstantIndex::from(0_usize));
        let forced = core.computation_force(head);
        let blocked = core.value_returned(forced);
        let blocked = core.computation_return(blocked);
        assert_eq!(
            normalises_to(&mut core, blocked, blocked),
            CertificateEquality::Equal,
            "a compound endpoint that does not return is kept, not erased"
        );
    }

    #[test]
    fn a_compound_endpoint_runs_through_a_definition()
    {
        // def id = thunk { \x. return x } ; the endpoint `id("five")`.
        let mut core = CoreArena::new();
        let five = literal(&mut core, Word::Five);
        let bound = core.value_variable(gandr_core_term::Zone::Intuitionistic, 0_u32.into());
        let returned = core.computation_return(bound);
        let lambda = core.computation_lambda(returned);
        let body = core.value_thunk(lambda);
        let identity = core.value_constant(ConstantIndex::from(0_usize));
        let forced = core.computation_force(identity);
        let applied = core.computation_application(forced, five);
        let compound = core.value_returned(applied);
        let mut chain = gandr_core_term::DefinitionChain::new();
        chain
            .define(
                ConstantIndex::from(0_usize),
                gandr_kernel_term::GlobalIndex::from(0_u32),
                gandr_core_term::Transparency::Manifest,
                &[],
            )
            .expect("one definition enters an empty chain");
        let Ok(chain) =
            LoweredChain::lower(chain, |_entry| Ok::<_, core::convert::Infallible>(body));
        let environment = DefinitionalEnvironment::new();
        let definitions = Definitions::new(&chain, &environment, environment.root());
        let mut domain = DomainArena::new();
        let [endpoint, point] = [compound, five].map(|value| {
            eval_value(&core, &mut domain, definitions, ample(), value)
                .expect("closed values evaluate")
        });
        let verdict = decide::<NullSink, NullMemo>(
            &core,
            &mut domain,
            definitions,
            MachineSettings::default(),
            Problem::values(endpoint, point),
            &mut NullSink,
        )
        .expect("the machine answers")
        .verdict();
        assert_eq!(
            verdict,
            MachineVerdict::Convertible,
            "the endpoint runs through the definition to the value it returns"
        );
        let empty = LoweredChain::new();
        let rigid = Definitions::new(&empty, &environment, environment.root());
        let mut domain = DomainArena::new();
        let [endpoint, point] = [compound, five].map(|value| {
            eval_value(&core, &mut domain, rigid, ample(), value).expect("closed values evaluate")
        });
        let verdict = decide::<NullSink, NullMemo>(
            &core,
            &mut domain,
            rigid,
            MachineSettings::default(),
            Problem::values(endpoint, point),
            &mut NullSink,
        )
        .expect("the machine answers")
        .verdict();
        assert_ne!(
            verdict,
            MachineVerdict::Convertible,
            "with the definition rigid the endpoint is stuck, not the value"
        );
    }

    #[test]
    fn reflexivities_convert_by_their_points()
    {
        let mut core = CoreArena::new();
        let five = literal(&mut core, Word::Five);
        let again = literal(&mut core, Word::Five);
        let six = literal(&mut core, Word::Six);
        let one = core.value_here(five);
        let other = core.value_here(again);
        let apart = core.value_here(six);
        let mut domain = DomainArena::new();
        let [one, other, apart] = evaluated(&core, &mut domain, [one, other, apart]);
        let chain = LoweredChain::new();
        let environment = DefinitionalEnvironment::new();
        let definitions = Definitions::new(&chain, &environment, environment.root());
        let mut decided = |left, right| {
            decide::<NullSink, NullMemo>(
                &core,
                &mut domain,
                definitions,
                MachineSettings::default(),
                Problem::values(left, right),
                &mut NullSink,
            )
            .expect("the machine answers")
            .verdict()
        };
        assert_eq!(decided(one, other), MachineVerdict::Convertible);
        assert_eq!(decided(one, apart), MachineVerdict::NotConvertible);
    }

    #[test]
    fn stuck_transports_compare_by_motive_and_operand()
    {
        let mut core = CoreArena::new();
        let five = literal(&mut core, Word::Five);
        let six = literal(&mut core, Word::Six);
        let carrier = text_type(&mut core);
        let path = stuck(&mut core, ConstantIndex::from(0_usize));
        let transported = core.computation_path_transport(carrier, path, five);
        let elsewhere = core.computation_path_transport(carrier, path, six);
        let unit = core.value_type_unit();
        let remotivated = core.computation_path_transport(unit, path, five);
        let chain = LoweredChain::new();
        let environment = DefinitionalEnvironment::new();
        let definitions = Definitions::new(&chain, &environment, environment.root());
        let mut domain = DomainArena::new();
        let mut run = |term| {
            eval_computation(&core, &mut domain, definitions, ample(), term)
                .expect("closed transports evaluate")
        };
        let (one, other, apart, remotivated) = (
            run(transported),
            run(transported),
            run(elsewhere),
            run(remotivated),
        );
        let mut decided = |left, right| {
            decide::<NullSink, NullMemo>(
                &core,
                &mut domain,
                definitions,
                MachineSettings::default(),
                Problem::computations(left, right),
                &mut NullSink,
            )
            .expect("the machine answers")
            .verdict()
        };
        assert_eq!(decided(one, other), MachineVerdict::Convertible);
        assert_eq!(decided(one, apart), MachineVerdict::NotConvertible);
        assert_eq!(decided(one, remotivated), MachineVerdict::NotConvertible);
    }

    #[test]
    fn then_associates_at_reflexivity()
    {
        let mut core = CoreArena::new();
        let carrier = text_type(&mut core);
        let five = literal(&mut core, Word::Five);
        let here = core.value_here(five);
        let bound = core.value_variable(gandr_core_term::Zone::Intuitionistic, 0_u32.into());
        // Every operand is closed, so the bound composite needs no shift.
        // (here · here) · here
        let inner = then(&mut core, carrier, five, here, here);
        let outer = then(&mut core, carrier, five, bound, here);
        let left = core.computation_bind(inner, outer);
        // here · (here · here)
        let inner = then(&mut core, carrier, five, here, here);
        let outer = then(&mut core, carrier, five, here, bound);
        let right = core.computation_bind(inner, outer);
        let expected = core.computation_return(here);
        assert_eq!(
            normalises_to(&mut core, left, expected),
            CertificateEquality::Equal
        );
        assert_eq!(
            normalises_to(&mut core, right, expected),
            CertificateEquality::Equal
        );
    }

    #[test]
    fn then_is_unital_at_a_stuck_path()
    {
        let mut core = CoreArena::new();
        let carrier = text_type(&mut core);
        let five = literal(&mut core, Word::Five);
        let path = stuck(&mut core, ConstantIndex::from(0_usize));
        let here = core.value_here(five);
        let composed = then(&mut core, carrier, five, path, here);
        let expected = core.computation_return(path);
        assert_eq!(
            normalises_to(&mut core, composed, expected),
            CertificateEquality::Equal,
            "composing with reflexivity on the right is the path itself"
        );
        let reversed = then(&mut core, carrier, five, here, path);
        assert_eq!(
            normalises_to(&mut core, reversed, expected),
            CertificateEquality::Equal,
            "composing with reflexivity on the left is the singleton's transport, the path itself"
        );
    }

    #[test]
    fn back_inverts_at_reflexivity()
    {
        let mut core = CoreArena::new();
        let carrier = text_type(&mut core);
        let five = literal(&mut core, Word::Five);
        let here = core.value_here(five);
        let inverted = back(&mut core, carrier, five, here);
        let expected = core.computation_return(here);
        assert_eq!(
            normalises_to(&mut core, inverted, expected),
            CertificateEquality::Equal
        );

        // back(back(here)) and here · back(here) are reflexivity again; every
        // operand is closed, so the bound composite needs no shift.
        let bound = core.value_variable(gandr_core_term::Zone::Intuitionistic, 0_u32.into());
        let first = back(&mut core, carrier, five, here);
        let twice = back(&mut core, carrier, five, bound);
        let twice = core.computation_bind(first, twice);
        assert_eq!(
            normalises_to(&mut core, twice, expected),
            CertificateEquality::Equal
        );
        let first = back(&mut core, carrier, five, here);
        let cancelled = then(&mut core, carrier, five, here, bound);
        let cancelled = core.computation_bind(first, cancelled);
        assert_eq!(
            normalises_to(&mut core, cancelled, expected),
            CertificateEquality::Equal
        );
    }

    #[test]
    fn cong_respects_composition_at_reflexivity()
    {
        let mut core = CoreArena::new();
        let carrier = text_type(&mut core);
        let pair = core.value_type_product(&[carrier, carrier]);
        let five = literal(&mut core, Word::Five);
        // f = thunk (λx. return (x, x))
        let bound = core.value_variable(gandr_core_term::Zone::Intuitionistic, 0_u32.into());
        let doubled = core.value_tuple(&[bound, bound]);
        let body = core.computation_return(doubled);
        let lambda = core.computation_lambda(body);
        let function = core.value_thunk(lambda);
        let forced = core.computation_force(function);
        let applied = core.computation_application(forced, five);
        let image = core.value_returned(applied);
        let here = core.value_here(five);

        // Every operand is closed, so the bound composites need no shift.
        // cong(f, here · here)
        let composed = then(&mut core, carrier, five, here, here);
        let mapped = cong(&mut core, pair, function, image, bound);
        let left = core.computation_bind(composed, mapped);
        // cong(f, here) · cong(f, here)
        let first = cong(&mut core, pair, function, image, here);
        let second = cong(&mut core, pair, function, image, here);
        let outer = core.value_variable(gandr_core_term::Zone::Intuitionistic, 1_u32.into());
        let joined = then(&mut core, pair, image, outer, bound);
        let joined = core.computation_bind(second, joined);
        let right = core.computation_bind(first, joined);
        let both = core.value_tuple(&[five, five]);
        let at_image = core.value_here(both);
        let expected = core.computation_return(at_image);
        assert_eq!(
            normalises_to(&mut core, left, expected),
            CertificateEquality::Equal
        );
        assert_eq!(
            normalises_to(&mut core, right, expected),
            CertificateEquality::Equal
        );
    }

    #[test]
    fn every_carrier_selects_its_clause()
    {
        let mut core = CoreArena::new();
        let unit = core.value_type_unit();
        let text = text_type(&mut core);
        let pair = core.value_type_product(&[text, text]);
        let sum = core.value_type_sum(&[unit, text]);
        let list = core.value_type_list(text);
        let returner = core.comp_type_returner(text);
        let arrow = core.comp_type_arrow(text, returner);
        let function = core.value_type_thunk(arrow);
        let suspended = core.value_type_thunk(returner);
        let universe = core.value_type_universe(
            gandr_core_term::Sort::Ground(gandr_kernel_term::GroundSort::Value),
            Level::zero(),
        );
        let atom = core.value_type_abstract(ConstantIndex::from(0_usize));
        let code = core.value_variable(gandr_core_term::Zone::Intuitionistic, 0_u32.into());
        let decoded = core.value_type_element(code, Level::zero());
        let record = core.value_type_record(alloc::collections::BTreeMap::new());
        for (carrier, expected) in [
            (unit, Clause::Unit),
            (text, Clause::Discrete),
            (pair, Clause::Product),
            (sum, Clause::Sum),
            (list, Clause::List),
            (function, Clause::Function),
            (suspended, Clause::Unclassified),
            (universe, Clause::Universe),
            (atom, Clause::Open),
            (decoded, Clause::Open),
            (record, Clause::Unclassified),
        ] {
            assert_eq!(clause(&core, carrier), Ok(expected), "{carrier:?}");
        }
    }

    #[test]
    fn unit_and_discrete_carriers_unfold_by_their_endpoints()
    {
        let mut core = CoreArena::new();
        let unit = core.value_type_unit();
        let text = text_type(&mut core);
        let empty = core.value_unit();
        let five = literal(&mut core, Word::Five);
        let again = literal(&mut core, Word::Five);
        let six = literal(&mut core, Word::Six);
        let head = stuck(&mut core, ConstantIndex::from(0_usize));
        let mut domain = DomainArena::new();
        let [empty, five, again, six, head] =
            evaluated(&core, &mut domain, [empty, five, again, six, head]);
        assert_eq!(fibre(&core, &domain, unit, empty, empty), Ok(Fibre::Unit));
        assert_eq!(fibre(&core, &domain, text, five, again), Ok(Fibre::Unit));
        assert_eq!(fibre(&core, &domain, text, five, six), Ok(Fibre::Empty));
        assert_eq!(fibre(&core, &domain, text, five, head), Ok(Fibre::Discrete));
    }

    #[test]
    fn different_injections_have_no_path()
    {
        let mut core = CoreArena::new();
        let unit = core.value_type_unit();
        let text = text_type(&mut core);
        let sum = core.value_type_sum(&[unit, text]);
        let empty = core.value_unit();
        let five = literal(&mut core, Word::Five);
        let left = core.value_injection(Side::Left.into(), empty);
        let right = core.value_injection(Side::Right.into(), five);
        let mut domain = DomainArena::new();
        let [left, right] = evaluated(&core, &mut domain, [left, right]);
        assert_eq!(fibre(&core, &domain, sum, left, right), Ok(Fibre::Empty));
        assert_eq!(fibre(&core, &domain, sum, right, left), Ok(Fibre::Empty));
    }

    #[test]
    fn matching_injections_recurse_into_the_payload()
    {
        let mut core = CoreArena::new();
        let unit = core.value_type_unit();
        let text = text_type(&mut core);
        let sum = core.value_type_sum(&[unit, text]);
        let five = literal(&mut core, Word::Five);
        let six = literal(&mut core, Word::Six);
        let one = core.value_injection(Side::Right.into(), five);
        let other = core.value_injection(Side::Right.into(), six);
        let head = stuck(&mut core, ConstantIndex::from(0_usize));
        let mut domain = DomainArena::new();
        let [one, other, five, six, head] =
            evaluated(&core, &mut domain, [one, other, five, six, head]);
        let Ok(Fibre::Payload(coordinate)) = fibre(&core, &domain, sum, one, other)
        else {
            panic!("matching injections recurse");
        };
        assert_eq!(coordinate.carrier(), text);
        assert_eq!(
            [coordinate.left(), coordinate.right()].map(|id| domain.value(id).copied()),
            [five, six].map(|id| domain.value(id).copied())
        );
        assert_eq!(fibre(&core, &domain, sum, one, head), Ok(Fibre::Suspended));
    }

    #[test]
    fn product_paths_are_componentwise()
    {
        let mut core = CoreArena::new();
        let unit = core.value_type_unit();
        let text = text_type(&mut core);
        let pair = core.value_type_product(&[text, unit]);
        let five = literal(&mut core, Word::Five);
        let six = literal(&mut core, Word::Six);
        let empty = core.value_unit();
        let one = core.value_tuple(&[five, empty]);
        let other = core.value_tuple(&[six, empty]);
        let mut domain = DomainArena::new();
        let [one, other] = evaluated(&core, &mut domain, [one, other]);
        let Ok(Fibre::Components(coordinates)) = fibre(&core, &domain, pair, one, other)
        else {
            panic!("tuples are componentwise");
        };
        let carriers: Vec<ValueTypeId> = coordinates.iter().map(Coordinate::carrier).collect();
        assert_eq!(carriers, [text, unit]);
        let first = coordinates.first().expect("two coordinates");
        let Some(&crate::domain::DomainValue::Literal { literal, .. }) =
            domain.value(first.right())
        else {
            panic!("the first coordinate relates the texts");
        };
        assert_eq!(core.value(literal), core.value(six));
    }

    #[test]
    fn list_paths_follow_the_constructors()
    {
        let mut core = CoreArena::new();
        let text = text_type(&mut core);
        let list = core.value_type_list(text);
        let five = literal(&mut core, Word::Five);
        let nil = core.value_list_nil();
        let cell = core.value_list_cons(five, nil);
        let mut domain = DomainArena::new();
        let [nil, cell] = evaluated(&core, &mut domain, [nil, cell]);
        assert_eq!(fibre(&core, &domain, list, nil, nil), Ok(Fibre::Unit));
        assert_eq!(fibre(&core, &domain, list, nil, cell), Ok(Fibre::Empty));
        let Ok(Fibre::Components(coordinates)) = fibre(&core, &domain, list, cell, cell)
        else {
            panic!("two cells relate head and tail");
        };
        let carriers: Vec<ValueTypeId> = coordinates.iter().map(Coordinate::carrier).collect();
        assert_eq!(carriers, [text, list]);
    }

    #[test]
    fn function_paths_relate_inputs_to_results()
    {
        let mut core = CoreArena::new();
        let text = text_type(&mut core);
        let unit = core.value_type_unit();
        let returner = core.comp_type_returner(unit);
        let arrow = core.comp_type_arrow(text, returner);
        let function = core.value_type_thunk(arrow);
        let head = stuck(&mut core, ConstantIndex::from(0_usize));
        let mut domain = DomainArena::new();
        let [head] = evaluated(&core, &mut domain, [head]);
        assert_eq!(
            fibre(&core, &domain, function, head, head),
            Ok(Fibre::Related {
                domain: text,
                codomain: returner,
            })
        );
    }

    #[test]
    fn open_carriers_unfold_to_nothing()
    {
        let mut core = CoreArena::new();
        let atom = core.value_type_abstract(ConstantIndex::from(0_usize));
        let head = stuck(&mut core, ConstantIndex::from(1_usize));
        let mut domain = DomainArena::new();
        let [head] = evaluated(&core, &mut domain, [head]);
        assert_eq!(fibre(&core, &domain, atom, head, head), Ok(Fibre::Open));
    }

    /// `thunk (λx. return o)`, `o` built over the bound variable by `body`.
    ///
    /// # Specification
    /// trivial.
    fn translator(
        core: &mut CoreArena,
        body: fn(&mut CoreArena, ValueId) -> ValueId,
    ) -> ValueId
    {
        let bound = core.value_variable(gandr_core_term::Zone::Intuitionistic, 0_u32.into());
        let built = body(core, bound);
        let returned = core.computation_return(built);
        let lambda = core.computation_lambda(returned);
        core.value_thunk(lambda)
    }

    /// `x ↦ (x, unit)`.
    ///
    /// # Specification
    /// trivial.
    fn paired(
        core: &mut CoreArena,
        bound: ValueId,
    ) -> ValueId
    {
        let unit = core.value_unit();
        core.value_tuple(&[bound, unit])
    }

    /// `x ↦ inl(x)`.
    ///
    /// # Specification
    /// trivial.
    fn injected_left(
        core: &mut CoreArena,
        bound: ValueId,
    ) -> ValueId
    {
        core.value_injection(Side::Left.into(), bound)
    }

    /// `x ↦ inr(x)`.
    ///
    /// # Specification
    /// trivial.
    fn injected_right(
        core: &mut CoreArena,
        bound: ValueId,
    ) -> ValueId
    {
        core.value_injection(Side::Right.into(), bound)
    }

    /// The motive `y. El y`: the decode of the moving code.
    ///
    /// # Specification
    /// trivial.
    fn decoded(core: &mut CoreArena) -> ValueTypeId
    {
        let code = core.value_variable(gandr_core_term::Zone::Intuitionistic, 0_u32.into());
        core.value_type_element(code, Level::zero())
    }

    #[test]
    fn flows_read_back_and_compare_by_their_parts()
    {
        let mut core = CoreArena::new();
        let five = literal(&mut core, Word::Five);
        let again = literal(&mut core, Word::Five);
        let six = literal(&mut core, Word::Six);
        let pairing = translator(&mut core, paired);
        let injecting = translator(&mut core, injected_left);
        let kept = core.value_stay(five);
        let kept_again = core.value_stay(again);
        let kept_apart = core.value_stay(six);
        let forward = core.value_forward(pairing);
        let other = core.value_forward(injecting);
        let composite = core.value_then(forward, other);
        let composite_again = core.value_then(forward, other);
        let reversed = core.value_then(other, forward);
        let function = core.value_function_flow(forward, other);
        let swapped = core.value_function_flow(other, forward);
        for flow in [kept, forward, composite, function] {
            let returned = core.computation_return(flow);
            assert_eq!(
                normalises_to(&mut core, returned, returned),
                CertificateEquality::Equal,
                "a flow reads back as its former over its parts"
            );
        }
        let mut domain = DomainArena::new();
        let [
            kept,
            kept_again,
            kept_apart,
            forward,
            other,
            composite,
            composite_again,
            reversed,
            function,
            swapped,
        ] = evaluated(&core, &mut domain, [
            kept,
            kept_again,
            kept_apart,
            forward,
            other,
            composite,
            composite_again,
            reversed,
            function,
            swapped,
        ]);
        let chain = LoweredChain::new();
        let environment = DefinitionalEnvironment::new();
        let definitions = Definitions::new(&chain, &environment, environment.root());
        let mut decided = |left, right| {
            decide::<NullSink, NullMemo>(
                &core,
                &mut domain,
                definitions,
                MachineSettings::default(),
                Problem::values(left, right),
                &mut NullSink,
            )
            .expect("the machine answers")
            .verdict()
        };
        assert_eq!(decided(kept, kept_again), MachineVerdict::Convertible);
        assert_eq!(decided(kept, kept_apart), MachineVerdict::NotConvertible);
        assert_eq!(decided(forward, other), MachineVerdict::NotConvertible);
        assert_eq!(decided(forward, kept), MachineVerdict::NotConvertible);
        assert_eq!(
            decided(composite, composite_again),
            MachineVerdict::Convertible
        );
        assert_eq!(decided(composite, reversed), MachineVerdict::NotConvertible);
        assert_eq!(decided(function, swapped), MachineVerdict::NotConvertible);
    }

    #[test]
    fn rides_compute_by_the_kernels_rows()
    {
        let mut core = CoreArena::new();
        let five = literal(&mut core, Word::Five);
        let six = literal(&mut core, Word::Six);
        let unit = core.value_unit();
        let text = text_type(&mut core);
        let unit_type = core.value_type_unit();
        let identity = decoded(&mut core);
        let pairing = translator(&mut core, paired);
        let injecting = translator(&mut core, injected_left);
        let forward = core.value_forward(pairing);
        let other = core.value_forward(injecting);
        let flow = stuck(&mut core, ConstantIndex::from(0_usize));
        let code = core.value_quote(text);
        let kept = core.value_stay(code);

        let rode = core.computation_ride(identity, kept, five);
        let expected = core.computation_return(five);
        assert_eq!(
            normalises_to(&mut core, rode, expected),
            CertificateEquality::Equal,
            "stay returns the value"
        );

        let rode = core.computation_ride(text, flow, five);
        assert_eq!(
            normalises_to(&mut core, rode, expected),
            CertificateEquality::Equal,
            "a motive that ignores its binder returns the value, even along a stuck flow"
        );

        let rode = core.computation_ride(identity, forward, five);
        let image = core.value_tuple(&[five, unit]);
        let expected = core.computation_return(image);
        assert_eq!(
            normalises_to(&mut core, rode, expected),
            CertificateEquality::Equal,
            "a forward flow at the decode applies its translator"
        );

        let composite = core.value_then(forward, other);
        let rode = core.computation_ride(identity, composite, five);
        let image = core.value_tuple(&[five, unit]);
        let image = core.value_injection(Side::Left.into(), image);
        let expected = core.computation_return(image);
        assert_eq!(
            normalises_to(&mut core, rode, expected),
            CertificateEquality::Equal,
            "a composite rides its first leg, then its second"
        );

        let product = core.value_type_product(&[identity, text]);
        let pair = core.value_tuple(&[five, six]);
        let rode = core.computation_ride(product, other, pair);
        let moved = core.value_injection(Side::Left.into(), five);
        let image = core.value_tuple(&[moved, six]);
        let expected = core.computation_return(image);
        assert_eq!(
            normalises_to(&mut core, rode, expected),
            CertificateEquality::Equal,
            "a product motive rides componentwise"
        );

        let sum = core.value_type_sum(&[identity, unit_type]);
        let injected = core.value_injection(Side::Left.into(), five);
        let rode = core.computation_ride(sum, other, injected);
        let inner = core.value_injection(Side::Left.into(), five);
        let image = core.value_injection(Side::Left.into(), inner);
        let expected = core.computation_return(image);
        assert_eq!(
            normalises_to(&mut core, rode, expected),
            CertificateEquality::Equal,
            "a sum motive rides the injected payload"
        );

        let list = core.value_type_list(identity);
        let nil = core.value_list_nil();
        let cell = core.value_list_cons(five, nil);
        let rode = core.computation_ride(list, other, cell);
        let moved = core.value_injection(Side::Left.into(), five);
        let image = core.value_list_cons(moved, nil);
        let expected = core.computation_return(image);
        assert_eq!(
            normalises_to(&mut core, rode, expected),
            CertificateEquality::Equal,
            "a list motive rides every cell"
        );

        let moving = core.value_variable(gandr_core_term::Zone::Intuitionistic, 0_u32.into());
        let singleton = core.value_type_flow(text, five, moving);
        let start = core.value_stay(five);
        let rode = core.computation_ride(singleton, flow, start);
        let expected = core.computation_return(flow);
        assert_eq!(
            normalises_to(&mut core, rode, expected),
            CertificateEquality::Equal,
            "stay ridden in the singleton is the flow itself"
        );
        let rode = core.computation_ride(singleton, flow, forward);
        let joined = core.value_then(forward, flow);
        let expected = core.computation_return(joined);
        assert_eq!(
            normalises_to(&mut core, rode, expected),
            CertificateEquality::Equal,
            "any other value ridden in the singleton composes with the flow"
        );

        let rode = core.computation_ride(identity, flow, five);
        assert_eq!(
            normalises_to(&mut core, rode, rode),
            CertificateEquality::Equal,
            "a ride along a stuck flow at the decode reads back as itself"
        );
    }

    #[test]
    fn a_function_flow_rides_in_variance_order()
    {
        let mut core = CoreArena::new();
        let five = literal(&mut core, Word::Five);
        let unit = core.value_unit();
        let identity = decoded(&mut core);
        let pairing = translator(&mut core, paired);
        let lefting = translator(&mut core, injected_left);
        let righting = translator(&mut core, injected_right);
        let domain_flow = core.value_forward(pairing);
        let codomain_flow = core.value_forward(righting);
        let applied = |core: &mut CoreArena, flow: ValueId| {
            let rode = core.computation_ride(identity, flow, lefting);
            let bound = core.value_variable(gandr_core_term::Zone::Intuitionistic, 0_u32.into());
            let forced = core.computation_force(bound);
            let applied = core.computation_application(forced, five);
            core.computation_bind(rode, applied)
        };
        let function = core.value_function_flow(domain_flow, codomain_flow);
        let ran = applied(&mut core, function);
        let argument = core.value_tuple(&[five, unit]);
        let result = core.value_injection(Side::Left.into(), argument);
        let image = core.value_injection(Side::Right.into(), result);
        let expected = core.computation_return(image);
        assert_eq!(
            normalises_to(&mut core, ran, expected),
            CertificateEquality::Equal,
            "the argument rides the domain flow, the function runs, the result rides the codomain flow"
        );
        let swapped = core.value_function_flow(codomain_flow, domain_flow);
        let ran = applied(&mut core, swapped);
        assert_eq!(
            normalises_to(&mut core, ran, expected),
            CertificateEquality::Different,
            "swapping the boundaries is another function"
        );
    }

    #[test]
    fn a_flow_product_rides_a_pair_componentwise()
    {
        let mut core = CoreArena::new();
        let five = literal(&mut core, Word::Five);
        let six = literal(&mut core, Word::Six);
        let unit = core.value_unit();
        let identity = decoded(&mut core);
        let pairing = translator(&mut core, paired);
        let lefting = translator(&mut core, injected_left);
        let first = core.value_forward(pairing);
        let second = core.value_forward(lefting);
        let pair = core.value_tuple(&[five, six]);
        let product = core.value_flow_product(first, second);
        let rode = core.computation_ride(identity, product, pair);
        let left = core.value_tuple(&[five, unit]);
        let right = core.value_injection(Side::Left.into(), six);
        let image = core.value_tuple(&[left, right]);
        let expected = core.computation_return(image);
        assert_eq!(
            normalises_to(&mut core, rode, expected),
            CertificateEquality::Equal,
            "each component rides its own flow at the decode"
        );
        let swapped = core.value_flow_product(second, first);
        let rode = core.computation_ride(identity, swapped, pair);
        assert_eq!(
            normalises_to(&mut core, rode, expected),
            CertificateEquality::Different,
            "the first flow moves the left component"
        );
        let flow = stuck(&mut core, ConstantIndex::from(0_usize));
        let open = core.value_flow_product(flow, second);
        let rode = core.computation_ride(identity, open, pair);
        let moved = core.value_injection(Side::Left.into(), six);
        let held = core.computation_ride(identity, flow, five);
        let held = core.value_returned(held);
        let both = core.value_tuple(&[held, moved]);
        let expected = core.computation_return(both);
        assert_eq!(
            normalises_to(&mut core, rode, expected),
            CertificateEquality::Equal,
            "a component stuck on its flow stands for what it returns while the other rides"
        );
    }
}
