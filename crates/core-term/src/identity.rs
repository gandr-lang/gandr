//! The derived operations on element identity: `back`, `then` and `cong`,
//! each a transport in a family of paths, never a node of its own.
//!
//! # One eliminator, three derivations
//!
//! The vocabulary has one way to use a path, [`Computation::PathTransport`]:
//! `tr(P, p, x)` carries `x : P[a]` along `p : Path(A, a, b)` to `P[b]`. The
//! three operations a program reaches for are transports whose motive is
//! itself a path type, the based family `y. Path(A, a, y)` being the second
//! component of the singleton `Σ y. Path(A, a, y)`:
//!
//! | operation | motive | from |
//! |---|---|---|
//! | `back(p) : Path(A, b, a)` | `y. Path(A, y, a)` | `here(a)` |
//! | `then(p, q) : Path(A, a, c)` | `y. Path(A, a, y)`, along `q` | `p` |
//! | `cong(f, p) : Path(B, f a, f b)` | `y. Path(B, f a, f y)` | `here(f a)` |
//!
//! Each builds its transport over the arena and returns it, so the evaluator,
//! the checker and the kernel boundary meet only `tr`, `here` and `Path`.
//! Transport computes on `here`, so every law the three obey at reflexivity —
//! `then` associates and is unital, `back` inverts, `cong` respects `then` —
//! holds by normalisation. At a path that is not reflexivity both units of
//! `then` hold definitionally, the left one because transport in the singleton
//! family carries `here(a)` to the path itself; the rest are paths between
//! paths, the business of identity between identities.
//!
//! # Decisions
//!
//! - **Derived, not primitive.** The choice is three arena functions over `tr`.
//!   The alternatives were a node per operation, which would give each its own
//!   evaluation rule, typing rule and kernel tag, three places for the laws to
//!   drift apart, and a primitive `J`, whose motive ranges over the path as
//!   well as its endpoint: `J` is the telescope transport of
//!   [`Computation::TelescopeTransport`] in the singleton `(y : A, q : Path(A,
//!   a, y))`, starting at `here(a)` and moving along `here(p)`. Reversal: an
//!   operation whose derived form costs too much to normalise earns a node,
//!   with its law as the node's evaluation rule.
//! - **A motive that depends on the path is a telescope.**
//!   [`Computation::PathTransport`]'s motive is one value type under one
//!   binder, the moving endpoint. A motive that also reads an element of a
//!   family over the endpoint is the dependent arrow `Π (y : A). Π (z : B). F
//!   C` of [`Computation::TelescopeTransport`], moved by the path and by an
//!   identity over it. The alternative, one former whose motive ranges over any
//!   number of entries, would make every transport pay for a telescope its
//!   first-order motive does not have. Reversal: a third entry earns the
//!   general former.
//! - **The motive is written by the caller, read at the words.** A caller names
//!   the carrier and the fixed endpoint: a checking position reads them off its
//!   expected path type, and anywhere else the lowering reads them off the
//!   operands, a word standing at the path at its words' point and a derived
//!   path at the path type its own motive gave. No node is added for the
//!   synthesis; the transports are the ones a written answer would mint. The
//!   alternative, an annotated spelling only, repeats the type the words
//!   already state. Reversal: a word whose endpoints are not spelled, a cell
//!   between distinct points, leaves no point to read, and its operations need
//!   the written answer.
//! - **`cong` applies through a compound endpoint.** `f y` inside the motive is
//!   [`Value::Returned`] over `force f y`, so the image of the moving endpoint
//!   is compared by what `f` computes. A first-order map is all it needs; a
//!   function of a function is the same construction one level up.
//! - **`back` along a flow is the symmetry ride.** [`back_flow`] is `back`'s
//!   derivation in the flow family: [`Computation::Ride`] of `stay(a)` along `f
//!   : Flow(A, a, b)` in `y. Flow(A, y, a)`. Its motive reads the moving
//!   endpoint as a source, contravariantly, and the checker refuses every such
//!   ride, so a flow has no inverse by the rule that lets it ride at all. The
//!   alternative, refusing `back` in the lowering when its answer is a flow,
//!   names no rule. Reversal: none while a flow runs one way.

use anodized::spec;
use gandr_kernel_term::DeBruijnIndex;

use crate::CoreArena;
use crate::arena::CompTypeId;
use crate::arena::ComputationId;
use crate::arena::ValueId;
use crate::arena::ValueTypeId;
use crate::rewrite::Binders;
use crate::rewrite::shift_value;
use crate::rewrite::shift_value_type;
#[cfg(doc)]
use crate::syntax::Computation;
#[cfg(doc)]
use crate::syntax::Value;
use crate::syntax::Zone;

/// A relation between two types the surface writes infix.
///
/// The core states it as the record or the flow it abbreviates: the lowering
/// records it against the type, and the printer reads it back to spell the
/// relation as written.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Relation
{
    /// The quasi-inverse `A ≅ B`, or `Iso(A, B)`: the record of a map, a map
    /// back and the two round trips.
    Isomorphism,
    /// The equivalence `A ≃ B`: the record of a map with a left and a right
    /// inverse.
    Equivalence,
    /// The flow `A ⇝ B` between two types, `Flow(Type, A, B)`.
    Flow,
}

/// Where a round trip of a relation's record reads the forward map: past the
/// other map and the trip's own point.
const FORWARD_PAST_TWO: u32 = 2_u32;

/// Where a round trip of a relation's record reads the map back: past the
/// trip's own point.
const OTHER_PAST_ONE: u32 = 1_u32;

/// The type of a map from `from` to `to`, `+U (from -> -F to)`, both read
/// where the map stands.
///
/// # Specification
/// - requires: `from` and `to` are value types of `arena` in one context.
/// - ensures: the thunk of the arrow from `from` to the returner of `to`.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`quasi_inverse`].
/// - witness: `identity::tests::the_relation_records_state_their_maps_and_trips`
#[spec(ensures: |ret| matches!(arena.value_type(ret), Some(&crate::syntax::ValueType::Thunk(_))))]
#[inline]
#[must_use]
pub fn map_type(
    arena: &mut CoreArena,
    from: ValueTypeId,
    to: ValueTypeId,
) -> ValueTypeId
{
    let returned = arena.comp_type_returner(to);
    let arrow = arena.comp_type_arrow(from, returned);
    arena.value_type_thunk(arrow)
}

/// Which round trip of a relation's record a type states, past the forward
/// map and then the other.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Trip
{
    /// `other(to(x))`.
    Section,
    /// `to(other(x))`.
    Retraction,
}

/// The type of a round trip over `carrier`, `(x : C) => Path(C,
/// outer(inner(x)), x)`, its two maps the innermost two binders.
///
/// # Specification
/// - requires: `carrier` is a value type of `arena` in a context `Γ`; the round
///   trip stands in `Γ` extended by the forward map and then the other.
/// - ensures: the thunk of the dependent arrow over `carrier` shifted past the
///   two maps, returning the path over `carrier` shifted past the binder too,
///   from the outer map of `trip` applied to the inner one applied to the bound
///   point, each application the value its computation returns, to the bound
///   point: the core the written `(x : C) => Path(C, outer(inner(x)), x)`
///   lowers to.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`quasi_inverse`].
/// - witness: `identity::tests::the_relation_records_state_their_maps_and_trips`
#[spec(ensures: |ret| matches!(arena.value_type(ret), Some(&crate::syntax::ValueType::Thunk(_))))]
fn round_trip(
    arena: &mut CoreArena,
    carrier: ValueTypeId,
    trip: Trip,
) -> ValueTypeId
{
    let (inner, outer) = match trip {
        Trip::Section => (FORWARD_PAST_TWO, OTHER_PAST_ONE),
        Trip::Retraction => (OTHER_PAST_ONE, FORWARD_PAST_TWO),
    };
    let past_maps = Binders::ONE.deeper();
    let domain = shift_value_type(arena, carrier, past_maps);
    let over = shift_value_type(arena, carrier, past_maps.deeper());
    let point = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let first = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(inner));
    let forced = arena.computation_force(first);
    let applied = arena.computation_application(forced, point);
    let midway = arena.value_returned(applied);
    let second = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(outer));
    let forced = arena.computation_force(second);
    let applied = arena.computation_application(forced, midway);
    let there = arena.value_returned(applied);
    let back_at = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let path = arena.value_type_path(over, there, back_at);
    let returned = arena.comp_type_returner(path);
    let dependent = arena.comp_type_pi(domain, returned);
    arena.value_type_thunk(dependent)
}

/// The record type `A ≅ B` abbreviates: a map, a map back, and the two round
/// trips.
///
/// # Specification
/// - requires: `from` and `to` are value types of `arena` in one context.
/// - ensures: the core the written `#{to : +U (A -> -F B), back : +U (B -> -F
///   A), sect : (a : A) => Path(A, back(to(a)), a), retr : (b : B) => Path(B,
///   to(back(b)), b)}` lowers to: `Σ to. Σ back. sect × retr`, each occurrence
///   of `A` and `B` shifted past the binders it stands under.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the relation and the written record over two base types
///   and over two bound type codes are one type.
/// - witness: `identity::tests::the_relation_records_state_their_maps_and_trips`
#[spec(ensures: |ret| matches!(arena.value_type(ret), Some(&crate::syntax::ValueType::Sigma { .. })))]
#[inline]
#[must_use]
pub fn quasi_inverse(
    arena: &mut CoreArena,
    from: ValueTypeId,
    to: ValueTypeId,
) -> ValueTypeId
{
    let forward = map_type(arena, from, to);
    let from_past = shift_value_type(arena, from, Binders::ONE);
    let to_past = shift_value_type(arena, to, Binders::ONE);
    let backward = map_type(arena, to_past, from_past);
    let section = round_trip(arena, from, Trip::Section);
    let retraction = round_trip(arena, to, Trip::Retraction);
    let laws = arena.value_type_product(&[section, retraction]);
    let rest = arena.value_type_sigma(backward, laws);
    arena.value_type_sigma(forward, rest)
}

/// The record type `A ≃ B` abbreviates: a map with a left inverse and a right
/// inverse, the bi-invertible map.
///
/// # Specification
/// - requires: `from` and `to` are value types of `arena` in one context.
/// - ensures: the core the written `#{to : +U (A -> -F B), linv : #{g : +U (B
///   -> -F A), sect : (a : A) => Path(A, g(to(a)), a)}, rinv : #{h : +U (B ->
///   -F A), retr : (b : B) => Path(B, to(h(b)), b)}}` lowers to: `Σ to. (Σ g.
///   sect) × (Σ h. retr)`, each occurrence of `A` and `B` shifted past the
///   binders it stands under.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`quasi_inverse`].
/// - witness: `identity::tests::the_relation_records_state_their_maps_and_trips`
#[spec(ensures: |ret| matches!(arena.value_type(ret), Some(&crate::syntax::ValueType::Sigma { .. })))]
#[inline]
#[must_use]
pub fn bi_invertible(
    arena: &mut CoreArena,
    from: ValueTypeId,
    to: ValueTypeId,
) -> ValueTypeId
{
    let forward = map_type(arena, from, to);
    let from_past = shift_value_type(arena, from, Binders::ONE);
    let to_past = shift_value_type(arena, to, Binders::ONE);
    let left_map = map_type(arena, to_past, from_past);
    let section = round_trip(arena, from, Trip::Section);
    let left = arena.value_type_sigma(left_map, section);
    let right_map = map_type(arena, to_past, from_past);
    let retraction = round_trip(arena, to, Trip::Retraction);
    let right = arena.value_type_sigma(right_map, retraction);
    let inverses = arena.value_type_product(&[left, right]);
    arena.value_type_sigma(forward, inverses)
}

/// The forward map of a bi-invertible record, `thunk (λx. f ← e.0; force f
/// x)`, which univalence `ua(e)` carries so that transport along it applies
/// the map.
///
/// # Specification
/// - requires: `record` is read where the map stands.
/// - ensures: the thunk of the abstraction binding the bound point, which
///   projects the first component of `record` shifted past that binder and
///   applies the forced projection to the point, read past the projection's own
///   binder.
/// - provides: the one spelling of the map the lowering writes and the checker
///   compares a written `ua` against, so transport along `ua(e)` reduces to
///   what the kernel derives from the record.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — over a record that reads an outer variable the map reads
///   it one binder further out and applies the projection to the bound point;
///   dropping the shift, projecting another component or applying the record
///   itself changes the built term.
/// - witness: `identity::tests::univalence_carries_the_record_s_forward_map`
#[spec(ensures: |ret| matches!(arena.value(ret), Some(&crate::syntax::Value::Thunk(_))))]
#[inline]
#[must_use]
pub fn univalence_forward(
    arena: &mut CoreArena,
    record: ValueId,
) -> ValueId
{
    let lifted = shift_value(arena, record, Binders::ONE);
    let projected = arena.computation_tuple_projection(lifted, crate::Component::from(0_usize));
    let map = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let forced = arena.computation_force(map);
    let point = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let applied = arena.computation_application(forced, point);
    let bound = arena.computation_bind(projected, applied);
    let abstraction = arena.computation_lambda(bound);
    arena.value_thunk(abstraction)
}

/// The moving endpoint of a motive: the innermost intuitionistic binder.
///
/// # Specification
/// trivial.
fn moving(arena: &mut CoreArena) -> ValueId
{
    arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32))
}

/// `back(p) : Path(A, b, a)` for `p : Path(A, a, b)`: transport of `here(a)`
/// along `p` in the family `y. Path(A, y, a)`.
///
/// # Specification
/// - requires: `carrier` and `fixed` are read in the context the result stands
///   in, `fixed` being the path's left endpoint, which is the derived path's
///   right one.
/// - ensures: the transport `tr(y. Path(A↑, y, a↑), path, here(a))`, the
///   carrier and the endpoint shifted past the motive's binder.
/// - provides: the inverse of a path, derived.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — over a carrier and an endpoint that read an outer
///   variable, the motive reads them one binder further out and its own binder
///   as the left endpoint, and the base is reflexivity at the unshifted
///   endpoint; dropping a shift, swapping the endpoints or starting from the
///   path changes the built term.
/// - witness: `identity::tests::back_transports_reflexivity_into_the_reversed_family`
#[spec(ensures: |ret| matches!(arena.computation(ret), Some(&crate::syntax::Computation::PathTransport { motive, path: along, value })
    if along == path
        && arena.value(value) == Some(&crate::syntax::Value::Here(fixed))
        && matches!(arena.value_type(motive), Some(&crate::syntax::ValueType::Path { left, .. })
            if arena.value(left) == Some(&crate::syntax::Value::Variable { zone: Zone::Intuitionistic, index: DeBruijnIndex::from(0_u32) }))))]
#[inline]
#[must_use]
pub fn back(
    arena: &mut CoreArena,
    carrier: ValueTypeId,
    fixed: ValueId,
    path: ValueId,
) -> ComputationId
{
    let lifted_carrier = shift_value_type(arena, carrier, Binders::ONE);
    let lifted_fixed = shift_value(arena, fixed, Binders::ONE);
    let endpoint = moving(arena);
    let motive = arena.value_type_path(lifted_carrier, endpoint, lifted_fixed);
    let base = arena.value_here(fixed);
    arena.computation_path_transport(motive, path, base)
}

/// `then(p, q) : Path(A, a, c)` for `p : Path(A, a, b)` and `q : Path(A, b,
/// c)`: transport of `p` along `q` in the family `y. Path(A, a, y)`.
///
/// # Specification
/// - requires: `carrier` and `start` are read in the context the result stands
///   in, `start` being the first path's left endpoint.
/// - ensures: the transport `tr(y. Path(A↑, a↑, y), second, first)`.
/// - provides: the composite of two paths, derived.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — over a carrier and a start that read an outer variable,
///   the motive fixes the shifted start and moves its right endpoint, and the
///   transport runs along the second path from the first; transporting along
///   the first path or fixing the wrong endpoint changes the built term.
/// - witness: `identity::tests::then_transports_the_first_path_along_the_second`
#[spec(ensures: |ret| matches!(arena.computation(ret), Some(&crate::syntax::Computation::PathTransport { motive, path, value })
    if path == second && value == first
        && matches!(arena.value_type(motive), Some(&crate::syntax::ValueType::Path { right, .. })
            if arena.value(right) == Some(&crate::syntax::Value::Variable { zone: Zone::Intuitionistic, index: DeBruijnIndex::from(0_u32) }))))]
#[inline]
#[must_use]
pub fn then(
    arena: &mut CoreArena,
    carrier: ValueTypeId,
    start: ValueId,
    first: ValueId,
    second: ValueId,
) -> ComputationId
{
    let lifted_carrier = shift_value_type(arena, carrier, Binders::ONE);
    let lifted_start = shift_value(arena, start, Binders::ONE);
    let endpoint = moving(arena);
    let motive = arena.value_type_path(lifted_carrier, lifted_start, endpoint);
    arena.computation_path_transport(motive, second, first)
}

/// `back(f)` for `f : Flow(A, a, b)`: the ride of `stay(a)` along `f` in the
/// family `y. Flow(A, y, a)`, the symmetry a flow does not have.
///
/// # Specification
/// - requires: `carrier` and `fixed` are read in the context the result stands
///   in, `fixed` being the flow's source, which is the reversed flow's target.
/// - ensures: the ride `ride(y. Flow(A↑, y, a↑), flow, stay(a))`, the carrier
///   and the endpoint shifted past the motive's binder.
/// - provides: `back` spelled along a flow, which the checker refuses: the
///   motive reads its moving endpoint as a source, contravariantly.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — over a carrier and an endpoint that read an outer
///   variable, the motive reads them one binder further out and its own binder
///   as the source; moving the target instead changes the built term.
/// - witness: `identity::tests::back_along_a_flow_rides_stay_into_the_reversed_family`
#[spec(ensures: |ret| matches!(arena.computation(ret), Some(&crate::syntax::Computation::Ride { motive, flow: along, value })
    if along == flow
        && arena.value(value) == Some(&crate::syntax::Value::Stay(fixed))
        && matches!(arena.value_type(motive), Some(&crate::syntax::ValueType::Flow { source, .. })
            if arena.value(source) == Some(&crate::syntax::Value::Variable { zone: Zone::Intuitionistic, index: DeBruijnIndex::from(0_u32) }))))]
#[inline]
#[must_use]
pub fn back_flow(
    arena: &mut CoreArena,
    carrier: ValueTypeId,
    fixed: ValueId,
    flow: ValueId,
) -> ComputationId
{
    let lifted_carrier = shift_value_type(arena, carrier, Binders::ONE);
    let lifted_fixed = shift_value(arena, fixed, Binders::ONE);
    let endpoint = moving(arena);
    let motive = arena.value_type_flow(lifted_carrier, endpoint, lifted_fixed);
    let base = arena.value_stay(fixed);
    arena.computation_ride(motive, flow, base)
}

/// `cong(f, p) : Path(B, f a, f b)` for `f : U(A → F B)` and `p : Path(A, a,
/// b)`: transport of `here(f a)` along `p` in the family `y. Path(B, f a, f
/// y)`.
///
/// # Specification
/// - requires: `codomain`, `function` and `start` are read in the context the
///   result stands in; `start` is the image of the path's left endpoint, the
///   derived path's left endpoint, and the transport's typing checks that it
///   converts to `f a`.
/// - ensures: the transport `tr(y. Path(B↑, start↑, ⟨force f↑ y⟩), path,
///   here(start))`, the moving image a compound endpoint.
/// - provides: the action of a function on a path, derived.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — over a map and a start that read an outer variable, the
///   motive's right endpoint is the shifted map applied to its own binder, and
///   the base is reflexivity at the unshifted start; applying the unshifted map
///   or binding the wrong index changes the built term.
/// - witness: `identity::tests::cong_applies_the_map_to_the_moving_endpoint`
#[spec(ensures: |ret| matches!(arena.computation(ret), Some(&crate::syntax::Computation::PathTransport { motive, path: along, value })
    if along == path
        && arena.value(value) == Some(&crate::syntax::Value::Here(start))
        && matches!(arena.value_type(motive), Some(&crate::syntax::ValueType::Path { right, .. })
            if matches!(arena.value(right), Some(&crate::syntax::Value::Returned(_))))))]
#[inline]
#[must_use]
pub fn cong(
    arena: &mut CoreArena,
    codomain: ValueTypeId,
    function: ValueId,
    start: ValueId,
    path: ValueId,
) -> ComputationId
{
    let lifted_function = shift_value(arena, function, Binders::ONE);
    cong_lifted(arena, codomain, lifted_function, start, path)
}

/// [`cong`] over a map its caller already lifted under the motive's binder,
/// so a caller that records where each node came from holds the one copy of
/// the map the transport reads.
///
/// # Specification
/// - requires: `codomain`, `start` and `path` are read in the context the
///   result stands in, and `lifted` is the map read one binder deeper, as
///   [`shift_value`] by one lifts it.
/// - ensures: the transport `tr(y. Path(B↑, start↑, ⟨force lifted y⟩), path,
///   here(start))`, whose motive forces `lifted` itself.
/// - provides: the action of a function on a path, its map's lift chosen by the
///   caller.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`cong`], which lifts its map and calls this.
/// - witness: `identity::tests::cong_applies_the_map_to_the_moving_endpoint`
#[spec(ensures: |ret| matches!(arena.computation(ret), Some(&crate::syntax::Computation::PathTransport { motive, path: along, value })
    if along == path
        && arena.value(value) == Some(&crate::syntax::Value::Here(start))
        && matches!(arena.value_type(motive), Some(&crate::syntax::ValueType::Path { right, .. })
            if matches!(arena.value(right), Some(&crate::syntax::Value::Returned(applied))
                if matches!(arena.computation(applied), Some(&crate::syntax::Computation::Application(forced, _))
                    if arena.computation(forced) == Some(&crate::syntax::Computation::Force(lifted)))))))]
#[inline]
#[must_use]
pub fn cong_lifted(
    arena: &mut CoreArena,
    codomain: ValueTypeId,
    lifted: ValueId,
    start: ValueId,
    path: ValueId,
) -> ComputationId
{
    let lifted_codomain = shift_value_type(arena, codomain, Binders::ONE);
    let lifted_start = shift_value(arena, start, Binders::ONE);
    let forced = arena.computation_force(lifted);
    let endpoint = moving(arena);
    let applied = arena.computation_application(forced, endpoint);
    let image = arena.value_returned(applied);
    let motive = arena.value_type_path(lifted_codomain, lifted_start, image);
    let base = arena.value_here(start);
    arena.computation_path_transport(motive, path, base)
}

/// The answer of a case over `branches` at `point`, `b`: the value the
/// point's branch returns when the point is a constructor without fields, the
/// case at the point otherwise.
///
/// A loop's path is built over `b`: the checker owes the loop at it and reads
/// a loop arm's type off it, and the lowering substitutes it for the binder a
/// loop arm reads the answer through, so both read it here.
///
/// # Specification
/// - requires: `point` is a closed constructor term of the case's sort, and
///   `branches` the case's branches at `motive`.
/// - ensures: `v` exactly when `point` has no fields and the branch its tag
///   selects is `return v`, which stands in the case's own context; `⟨case
///   point { branches }⟩` otherwise. The two convert, since a case at a
///   constructor runs the branch it selects. Reading the branch's value leaves
///   a path type over `b` at the point its value spells, where the words a word
///   answers at read it.
/// - provides: the case's answer at a loop's point.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a case that returns a value at a point without fields
///   answers that value; a branch that computes, or a point with fields,
///   answers the case at the point. Answering the case where a value is
///   returned, or the value of the wrong branch, changes the built term.
/// - witness: `identity::tests::a_case_answers_at_a_point_by_the_value_its_branch_returns`
#[spec(ensures: |ret| branches.iter().any(|&branch| matches!(arena.computation(branch), Some(&crate::syntax::Computation::Return(value)) if value == ret))
    || matches!(arena.value(ret), Some(&crate::syntax::Value::Returned(case))
        if matches!(arena.computation(case), Some(&crate::syntax::Computation::DataCase { scrutinee, .. }) if scrutinee == point)))]
#[inline]
#[must_use]
pub fn answer_at(
    arena: &mut CoreArena,
    point: ValueId,
    motive: CompTypeId,
    branches: &[ComputationId],
) -> ValueId
{
    if let Some(&crate::syntax::Value::Constructor {
        tag, ref fields, ..
    }) = arena.value(point)
        && fields.is_empty()
        && let Some(&branch) = branches.get(usize::from(tag))
        && let Some(&crate::syntax::Computation::Return(value)) = arena.computation(branch)
    {
        return value;
    }
    let answered = arena.computation_data_case(point, motive, branches.to_vec());
    arena.value_returned(answered)
}

#[cfg(test)]
mod tests;
