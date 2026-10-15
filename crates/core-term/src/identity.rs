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
mod tests
{
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::DeBruijnIndex;

    use crate::CertificateEquality;
    use crate::CoreArena;
    use crate::arena::ValueId;
    use crate::arena::ValueTypeId;
    use crate::syntax::Zone;
    use crate::syntax::equal_certificate_syntax;

    /// The intuitionistic variable at `index`.
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

    /// A carrier that reads the variable at `index`: `El(#index)`.
    ///
    /// # Specification
    /// trivial.
    fn open_carrier(
        arena: &mut CoreArena,
        index: DeBruijnIndex,
    ) -> ValueTypeId
    {
        let code = variable(arena, index);
        arena.value_type_element(code, gandr_kernel_strata::Level::zero())
    }

    /// How two built terms compare as syntax.
    ///
    /// # Specification
    /// trivial.
    fn compared(
        arena: &CoreArena,
        left: crate::arena::ComputationId,
        right: crate::arena::ComputationId,
    ) -> CertificateEquality
    {
        let mut probe = arena.clone();
        let left = probe.value_thunk(left);
        let right = probe.value_thunk(right);
        equal_certificate_syntax(&probe, left, right)
    }

    #[test]
    fn back_transports_reflexivity_into_the_reversed_family()
    {
        let mut arena = CoreArena::new();
        let carrier = open_carrier(&mut arena, 1_u32.into());
        let fixed = variable(&mut arena, 0_u32.into());
        let path = variable(&mut arena, 2_u32.into());
        let built = super::back(&mut arena, carrier, fixed, path);

        let lifted_carrier = open_carrier(&mut arena, 2_u32.into());
        let moving = variable(&mut arena, 0_u32.into());
        let lifted_fixed = variable(&mut arena, 1_u32.into());
        let motive = arena.value_type_path(lifted_carrier, moving, lifted_fixed);
        let base = arena.value_here(fixed);
        let expected = arena.computation_path_transport(motive, path, base);
        assert_eq!(
            compared(&arena, built, expected),
            CertificateEquality::Equal,
            "back reverses the family past one binder"
        );

        let unshifted = arena.value_type_path(carrier, moving, fixed);
        let capturing = arena.computation_path_transport(unshifted, path, base);
        assert_eq!(
            compared(&arena, built, capturing),
            CertificateEquality::Different,
            "an unshifted motive captures the outer variables"
        );
    }

    #[test]
    fn back_along_a_flow_rides_stay_into_the_reversed_family()
    {
        let mut arena = CoreArena::new();
        let carrier = open_carrier(&mut arena, 1_u32.into());
        let fixed = variable(&mut arena, 0_u32.into());
        let flow = variable(&mut arena, 2_u32.into());
        let built = super::back_flow(&mut arena, carrier, fixed, flow);

        let lifted_carrier = open_carrier(&mut arena, 2_u32.into());
        let moving = variable(&mut arena, 0_u32.into());
        let lifted_fixed = variable(&mut arena, 1_u32.into());
        let motive = arena.value_type_flow(lifted_carrier, moving, lifted_fixed);
        let base = arena.value_stay(fixed);
        let expected = arena.computation_ride(motive, flow, base);
        assert_eq!(
            compared(&arena, built, expected),
            CertificateEquality::Equal,
            "back along a flow moves the source past one binder"
        );

        let covariant = arena.value_type_flow(lifted_carrier, lifted_fixed, moving);
        let covariant = arena.computation_ride(covariant, flow, base);
        assert_eq!(
            compared(&arena, built, covariant),
            CertificateEquality::Different,
            "the reversed family moves the source, not the target"
        );
    }

    #[test]
    fn then_transports_the_first_path_along_the_second()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let start = variable(&mut arena, 0_u32.into());
        let first = variable(&mut arena, 1_u32.into());
        let second = variable(&mut arena, 2_u32.into());
        let built = super::then(&mut arena, integer, start, first, second);

        let lifted_start = variable(&mut arena, 1_u32.into());
        let moving = variable(&mut arena, 0_u32.into());
        let motive = arena.value_type_path(integer, lifted_start, moving);
        let expected = arena.computation_path_transport(motive, second, first);
        assert_eq!(
            compared(&arena, built, expected),
            CertificateEquality::Equal,
            "then moves the right endpoint along the second path"
        );

        let swapped = arena.computation_path_transport(motive, first, second);
        assert_eq!(
            compared(&arena, built, swapped),
            CertificateEquality::Different,
            "transporting along the first path is another term"
        );
    }

    #[test]
    fn cong_applies_the_map_to_the_moving_endpoint()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let function = variable(&mut arena, 0_u32.into());
        let start = variable(&mut arena, 1_u32.into());
        let path = variable(&mut arena, 2_u32.into());
        let built = super::cong(&mut arena, integer, function, start, path);

        let lifted_start = variable(&mut arena, 2_u32.into());
        let lifted_function = variable(&mut arena, 1_u32.into());
        let forced = arena.computation_force(lifted_function);
        let moving = variable(&mut arena, 0_u32.into());
        let applied = arena.computation_application(forced, moving);
        let image = arena.value_returned(applied);
        let motive = arena.value_type_path(integer, lifted_start, image);
        let base = arena.value_here(start);
        let expected = arena.computation_path_transport(motive, path, base);
        assert_eq!(
            compared(&arena, built, expected),
            CertificateEquality::Equal,
            "cong maps the moving endpoint through the function"
        );

        let unshifted = arena.computation_force(function);
        let captured = arena.computation_application(unshifted, moving);
        let captured = arena.value_returned(captured);
        let capturing = arena.value_type_path(integer, lifted_start, captured);
        let capturing = arena.computation_path_transport(capturing, path, base);
        assert_eq!(
            compared(&arena, built, capturing),
            CertificateEquality::Different,
            "an unshifted map reads the motive's own binder"
        );
    }

    #[test]
    fn a_case_answers_at_a_point_by_the_value_its_branch_returns()
    {
        let mut arena = CoreArena::new();
        let sort = arena.value_type_data(
            gandr_kernel_term::ConstantIndex::from(0_usize),
            alloc::vec::Vec::new(),
        );
        let point = arena.value_constructor(
            sort,
            gandr_kernel_term::ConstructorTag::from(0_usize),
            alloc::vec::Vec::new(),
        );
        let field = arena.value_unit();
        let fielded = arena.value_constructor(
            sort,
            gandr_kernel_term::ConstructorTag::from(1_usize),
            alloc::vec![field],
        );
        let motive = arena.comp_type_returner(sort);
        let held = variable(&mut arena, 0_u32.into());
        let (at_point, at_fielded) = (
            arena.computation_return(point),
            arena.computation_return(held),
        );
        let branches = [at_point, at_fielded];
        assert_eq!(
            super::answer_at(&mut arena, point, motive, &branches),
            point,
            "a point without fields answers the value its branch returns"
        );

        let case_at = |arena: &CoreArena, answered| {
            matches!(arena.value(answered), Some(&crate::syntax::Value::Returned(case))
                if matches!(arena.computation(case), Some(&crate::syntax::Computation::DataCase { scrutinee, .. }) if scrutinee == point || scrutinee == fielded))
        };
        let answered = super::answer_at(&mut arena, fielded, motive, &branches);
        assert!(
            case_at(&arena, answered),
            "a point with fields answers the case at it"
        );
        let forced = arena.computation_force(held);
        let computing = [forced, at_fielded];
        let answered = super::answer_at(&mut arena, point, motive, &computing);
        assert!(
            case_at(&arena, answered),
            "a branch that computes answers the case at the point"
        );
    }
}
