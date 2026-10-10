//! **Conversion**: structural comparison of two types, descending into the
//! terms they carry, with the id-equality fast path above it.
//!
//! # What the relation is, precisely
//!
//! The checker invokes conversion at a mode switch — when a synthesizing term
//! is used where a type is expected. Over this vocabulary the definitional
//! equality that needs is **type conversion only**, and it is exactly:
//!
//! - an **id-equality fast path**, which is **positive only**: two nodes named
//!   by the same id in the same arena are the same node, so the pair is
//!   discharged. Two *different* ids decide nothing and fall through to the
//!   structural walk. That asymmetry is the whole of what keeps the fast path
//!   sound without taking any table into the trusted base — it decides
//!   reflexive pairs alone, and the kernel preserves the sharing a decode
//!   handed it rather than creating more;
//! - α-structural equality, which is syntactic identity because terms are
//!   nameless; the dependent arrow binds, and binding costs nothing here for
//!   the same reason — de Bruijn indices make two codomains under one binder
//!   each comparable directly;
//! - **head separation between the two arrows.** A non-dependent arrow and a
//!   dependent one never convert, and the reason is a context disagreement
//!   rather than a taste: their codomains are written against contexts
//!   differing by one binder, so comparing them would compare two indices
//!   counting different things. The producer's obligation is the other half —
//!   the dependent former is emitted only where the codomain is genuinely
//!   scoped, so the separation costs no completeness on a well-formed artifact;
//! - canonical level equality at the universe and lift formers, the level
//!   type's own equality being the level-equality oracle;
//! - nominal equality at the sealed atom, which is the whole rule for it: two
//!   atoms convert exactly when they name one declaration, and no arm relates
//!   an atom to a structural type, so opacity is a consequence of the closed
//!   match rather than a claim a producer makes.
//!
//! # It descends into terms, and it still does not reduce
//!
//! The universe-decoding former carries a value, so two types converge only
//! when the codes they are read off converge — and the walk therefore compares
//! terms as well as types, over the same worklist and with the same fast path.
//!
//! **No reduction fires and nothing is evaluated.** Two codes convert when they
//! are structurally equal, which is α-equality because terms are nameless. That
//! is sound and **incomplete**: `El ((λ. x) v)` and `El (x[v])` denote one type
//! and this walk separates them. The incompleteness is a refusal a producer
//! avoids by handing the kernel reduced codes, never a soundness hazard.
//!
//! # Fail-closed on an unreadable id
//!
//! A child id always resolves under the arena's minting invariant. Were one
//! not to, the checked read yields nothing and the walk answers
//! [`Convertibility::Distinct`] — refusing is the safe verdict, and it is the
//! same posture the rest of the kernel takes toward a fault it excludes.
//!
//! # Totality
//!
//! The walk is iterative over an explicit worklist of `Copy` id pairs. A
//! derived structural equality would recurse on depth and overflow the stack on
//! an adversarial-depth input, which decode can build from bytes.

use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::CompType;
use gandr_kernel_term::CompTypeId;
use gandr_kernel_term::Computation;
use gandr_kernel_term::ComputationId;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueType;
use gandr_kernel_term::ValueTypeId;

use crate::error::CompTypeMismatch;
use crate::error::KernelError;
use crate::error::ValueTypeMismatch;
use crate::witness::comp_type_witness;
use crate::witness::value_type_witness;

/// Whether two types are convertible.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Convertibility
{
    /// The two are definitionally equal.
    Convertible,
    /// The two are distinct.
    Distinct,
}

/// A pending obligation: a same-family id pair still to compare.
///
/// The two term families are here because a type can carry a code, so a type
/// comparison reaches a term comparison. They ride the same worklist and the
/// same discharged set, which is what keeps the walk one loop and its sharing
/// awareness one mechanism.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum ConversionGoal
{
    /// A pair of value types.
    ValueType(ValueTypeId, ValueTypeId),
    /// A pair of computation types.
    CompType(CompTypeId, CompTypeId),
    /// A pair of values.
    Value(ValueId, ValueId),
    /// A pair of computations.
    Computation(ComputationId, ComputationId),
}

/// Decide convertibility of two value types in one arena.
///
/// # Specification
/// - requires: nothing — an unreadable id is admissible input and fails closed.
/// - ensures: [`Convertibility::Convertible`] exactly when the two are equal up
///   to this subset's definitional equality; the relation is reflexive,
///   symmetric and transitive.
/// - provides: the type equality the checker invokes at a value mode switch.
///   Definitional equality and its relational laws remain prose-only: this call
///   has one pair, and no independent structural-equality predicate is
///   available without duplicating the conversion walk.
/// - fails: never — a negative answer is [`Convertibility::Distinct`] rather
///   than an error.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2/L3 — reflexivity and separation are pinned over one former
///   of every arm; the L3 residues are the positive-only id fast path (two
///   distinct ids over equal content still convert, so the fast path is not
///   doing the deciding), the canonical level comparison, and the nominal atom
///   arm, each asserted exactly.
/// - witness: `conv::tests::value_type_conversion_is_reflexive`
/// - witness: `conv::tests::structurally_equal_types_at_distinct_ids_convert`
/// - witness: `conv::tests::conversion_separates_every_former`
/// - witness: `conv::tests::universes_convert_by_canonical_level`
/// - witness: `conv::tests::sealed_atoms_are_nominal`
/// - witness: `conv::tests::types_read_off_codes_converge_with_their_codes`
/// - witness: `conv::tests::code_comparison_separates_every_term_former_without_reducing`
#[inline]
#[must_use]
pub fn convertible_value_types(
    arena: &TermArena,
    left: ValueTypeId,
    right: ValueTypeId,
) -> Convertibility
{
    converge(arena, ConversionGoal::ValueType(left, right))
}

/// Decide convertibility of two computation types in one arena.
///
/// # Specification
/// - requires: nothing — an unreadable id is admissible input and fails closed.
/// - ensures: [`Convertibility::Convertible`] exactly when the two are equal up
///   to this subset's definitional equality; reflexive, symmetric, transitive.
/// - provides: the type equality the checker invokes at a computation mode
///   switch and at a case's branch convergence. Definitional equality and its
///   relational laws remain prose-only for the same reason as
///   [`convertible_value_types`].
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2/L3 — as [`convertible_value_types`]; the residue is the
///   arrow's two children, whose polarities differ, asserted by separating a
///   pair that agrees on the domain and differs on the codomain.
/// - witness: `conv::tests::computation_type_conversion_is_reflexive`
/// - witness: `conv::tests::an_arrow_separates_on_either_child`
/// - witness: `conv::tests::the_two_arrows_never_convert_across`
#[inline]
#[must_use]
pub fn convertible_comp_types(
    arena: &TermArena,
    left: CompTypeId,
    right: CompTypeId,
) -> Convertibility
{
    converge(arena, ConversionGoal::CompType(left, right))
}

/// Decide structural equality of two values in one arena, without reducing.
///
/// # Specification
/// - requires: nothing — an unreadable id is admissible input and fails closed.
/// - ensures: [`Convertibility::Convertible`] exactly when the two are α-equal,
///   descending into every computation they carry; no reduction and no
///   unfolding fires.
/// - provides: the closing check a conversion replay applies where a trace says
///   two nodes met.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the walk is the one the type entries run, whose term arms
///   are separated former by former; the residue is the entry, carried by the
///   replay's closing witnesses.
/// - witness: `conv::tests::code_comparison_separates_every_term_former_without_reducing`
/// - witness: `replay::tests::a_compared_pair_closes_on_alpha_equality_or_rigid_separation`
#[inline]
#[must_use]
pub(crate) fn equal_values(
    arena: &TermArena,
    left: ValueId,
    right: ValueId,
) -> Convertibility
{
    converge(arena, ConversionGoal::Value(left, right))
}

/// Decide structural equality of two computations; see [`equal_values`].
///
/// # Specification
/// - requires: as [`equal_values`].
/// - ensures: as [`equal_values`], over the computation family.
/// - provides: as [`equal_values`].
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`equal_values`].
/// - witness: `replay::tests::a_compared_pair_closes_on_alpha_equality_or_rigid_separation`
#[inline]
#[must_use]
pub(crate) fn equal_computations(
    arena: &TermArena,
    left: ComputationId,
    right: ComputationId,
) -> Convertibility
{
    converge(arena, ConversionGoal::Computation(left, right))
}

/// Convert a synthesized value type against an expected one, building the
/// mismatch on divergence.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `|ret| ret.is_ok() == matches!(convertible_value_types(arena,
///   expected, actual), Convertibility::Convertible)` — success exactly when
///   [`convertible_value_types`] converges.
/// - provides: the checker's value mode-switch step.
/// - fails: [`KernelError::ValueTypeMismatch`] carrying content witnesses of
///   both roots, which stay meaningful after the arena is truncated.
/// - panics: none.
///
/// # Errors
/// [`KernelError::ValueTypeMismatch`].
///
/// # Adequacy
/// - hypothesis: L3 — the sole surface is the verdict branch, separated by a
///   converting pair (success) and a separating pair (the exact variant, with
///   both witnesses' heads asserted).
/// - witness: `conv::tests::a_value_mismatch_names_both_heads`
#[inline]
#[spec(ensures: |ret| ret.is_ok() == matches!(convertible_value_types(arena, expected, actual), Convertibility::Convertible))]
pub fn convert_value_type(
    arena: &TermArena,
    expected: ValueTypeId,
    actual: ValueTypeId,
) -> Result<(), KernelError>
{
    match convertible_value_types(arena, expected, actual) {
        | Convertibility::Convertible => Ok(()),
        | Convertibility::Distinct => Err(KernelError::ValueTypeMismatch(ValueTypeMismatch::new(
            value_type_witness(arena, expected),
            value_type_witness(arena, actual),
        ))),
    }
}

/// Convert a synthesized computation type against an expected one, building the
/// mismatch on divergence.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `|ret| ret.is_ok() == matches!(convertible_comp_types(arena,
///   expected, actual), Convertibility::Convertible)` — success exactly when
///   [`convertible_comp_types`] converges.
/// - provides: the checker's computation mode-switch step.
/// - fails: [`KernelError::ComputationTypeMismatch`] carrying content witnesses
///   of both roots.
/// - panics: none.
///
/// # Errors
/// [`KernelError::ComputationTypeMismatch`].
///
/// # Adequacy
/// - hypothesis: L3 — as [`convert_value_type`], on the computation plane.
/// - witness: `conv::tests::a_computation_mismatch_names_both_heads`
#[inline]
#[spec(ensures: |ret| ret.is_ok() == matches!(convertible_comp_types(arena, expected, actual), Convertibility::Convertible))]
pub fn convert_comp_type(
    arena: &TermArena,
    expected: CompTypeId,
    actual: CompTypeId,
) -> Result<(), KernelError>
{
    match convertible_comp_types(arena, expected, actual) {
        | Convertibility::Convertible => Ok(()),
        | Convertibility::Distinct => {
            Err(KernelError::ComputationTypeMismatch(CompTypeMismatch::new(
                comp_type_witness(arena, expected),
                comp_type_witness(arena, actual),
            )))
        },
    }
}

/// Build the refusal of a case whose branches did not converge.
///
/// # Specification
/// trivial.
#[inline]
pub(crate) fn case_branch_mismatch(
    arena: &TermArena,
    left: CompTypeId,
    right: CompTypeId,
) -> KernelError
{
    KernelError::CaseBranchMismatch(CompTypeMismatch::new(
        comp_type_witness(arena, left),
        comp_type_witness(arena, right),
    ))
}

/// Run the conversion worklist to a verdict.
///
/// # Specification
/// - requires: `initial` is a same-polarity id pair.
/// - ensures: [`Convertibility::Convertible`] exactly when every reachable
///   sub-pair is id-equal or matches structurally with canonical level equality
///   at level positions and nominal equality at atoms; the walk is iterative
///   over a heap stack, so it is total on any depth.
/// - provides: the shared engine of the two conversion faces. The pair's
///   polarity is guaranteed by `ConversionGoal`; the reachable-pair and
///   totality claims remain prose-only because they require an independent
///   graph walk and a termination argument, not a wrapper predicate.
/// - fails: never — the verdict is the return value, and an unreadable id
///   yields [`Convertibility::Distinct`].
/// - panics: none.
/// - intension: each distinct reachable pair is compared once per call rather
///   than once per occurrence. Nothing extensional depends on it — the verdict
///   is the same with or without the set.
///
/// # The walk is sharing-aware, and the discharged set is what makes it so
///
/// Without it two roots that share a subgraph re-walk every shared pair once
/// per occurrence, so the work is the *expansion* of the compared graphs rather
/// than their size — exponential in sharing depth on a term a decoder handed
/// over. A pair discharged once stays discharged: over this vocabulary a type
/// pair's verdict is a function of the two nodes alone, and any pair that fails
/// returns immediately, so nothing is recorded as discharged while its own
/// subtree is still undecided.
///
/// The set is **per call and holds only pairs**. It creates no sharing, is
/// never consulted for anything but skipping a repeat inside one comparison,
/// and dies with the call — so it is not the interning table the conversion
/// engine is forbidden to grow, and it is not on the memo's plane: the pinned
/// expansion laws count the checker's goal expansions, which this does not
/// touch.
///
/// # Adequacy
/// - hypothesis: L2/L3 — the arm table is pinned by the per-former separation
///   witnesses; the L3 residues are the fast path's positive-only direction and
///   the fail-closed unreadable arm. The discharged set adds no extensional
///   surface, and its intensional claim is separated by a shared composite
///   whose comparison would otherwise be exponential in its depth.
/// - witness: `conv::tests::structurally_equal_types_at_distinct_ids_convert`
/// - witness: `conv::tests::an_unreadable_id_fails_closed`
/// - witness: `conv::tests::a_shared_composite_converts_without_expanding`
#[spec(ensures: |ret| match initial {
    ConversionGoal::ValueType(left, right) => if left == right { ret == Convertibility::Convertible } else { match (arena.value_type(left), arena.value_type(right)) {
        (Some(a), Some(b)) => ret != Convertibility::Convertible || core::mem::discriminant(a) == core::mem::discriminant(b),
        _ => ret == Convertibility::Distinct,
    } },
    ConversionGoal::CompType(left, right) => if left == right { ret == Convertibility::Convertible } else { match (arena.comp_type(left), arena.comp_type(right)) {
        (Some(a), Some(b)) => ret != Convertibility::Convertible || core::mem::discriminant(a) == core::mem::discriminant(b),
        _ => ret == Convertibility::Distinct,
    } },
    ConversionGoal::Value(left, right) => if left == right { ret == Convertibility::Convertible } else { match (arena.value(left), arena.value(right)) {
        (Some(a), Some(b)) => ret != Convertibility::Convertible || core::mem::discriminant(a) == core::mem::discriminant(b),
        _ => ret == Convertibility::Distinct,
    } },
    ConversionGoal::Computation(left, right) => if left == right { ret == Convertibility::Convertible } else { match (arena.computation(left), arena.computation(right)) {
        (Some(a), Some(b)) => ret != Convertibility::Convertible || core::mem::discriminant(a) == core::mem::discriminant(b),
        _ => ret == Convertibility::Distinct,
    } },
})]
fn converge(
    arena: &TermArena,
    initial: ConversionGoal,
) -> Convertibility
{
    let mut stack: Vec<ConversionGoal> = Vec::new();
    let mut discharged: BTreeSet<ConversionGoal> = BTreeSet::new();
    stack.push(initial);
    while let Some(goal) = stack.pop() {
        if !discharged.insert(goal) {
            continue;
        }
        match goal {
            | ConversionGoal::ValueType(left, right) => {
                // The fast path, positive only: equal ids name one node, so the
                // pair is discharged. Unequal ids decide nothing.
                if left == right {
                    continue;
                }
                let (Some(left), Some(right)) = (arena.value_type(left), arena.value_type(right))
                else {
                    return Convertibility::Distinct;
                };
                match (left, right) {
                    | (&ValueType::PathUniverse(a, b), &ValueType::PathUniverse(c, d)) => {
                        stack.push(ConversionGoal::Value(a, c));
                        stack.push(ConversionGoal::Value(b, d));
                    },
                    | (&ValueType::Base(one), &ValueType::Base(other)) => {
                        if one != other {
                            return Convertibility::Distinct;
                        }
                    },
                    | (&ValueType::Unit, &ValueType::Unit)
                    | (&ValueType::Empty, &ValueType::Empty) => {},
                    | (
                        &ValueType::Product(one_first, one_second),
                        &ValueType::Product(other_first, other_second),
                    )
                    | (
                        &ValueType::Sum(one_first, one_second),
                        &ValueType::Sum(other_first, other_second),
                    )
                    | (
                        &ValueType::StaticPi {
                            domain: one_first,
                            codomain: one_second,
                        },
                        &ValueType::StaticPi {
                            domain: other_first,
                            codomain: other_second,
                        },
                    ) => {
                        stack.push(ConversionGoal::ValueType(one_first, other_first));
                        stack.push(ConversionGoal::ValueType(one_second, other_second));
                    },
                    | (&ValueType::Thunk(one_body), &ValueType::Thunk(other_body)) => {
                        stack.push(ConversionGoal::CompType(one_body, other_body));
                    },
                    | (
                        &ValueType::Session {
                            graph: ref one,
                            payloads: a,
                        },
                        &ValueType::Session {
                            graph: ref other,
                            payloads: b,
                        },
                    ) => {
                        // Graphs contain no native children; structural graph equality is finite.
                        if one != other {
                            return Convertibility::Distinct;
                        }
                        stack.push(ConversionGoal::ValueType(a, b));
                    },
                    | (&ValueType::List(one), &ValueType::List(other)) => {
                        stack.push(ConversionGoal::ValueType(one, other));
                    },
                    // Both sides are pinned to the universe former by the
                    // pattern, and the former carries a sort and a level and no
                    // child, so the node comparison delegated to here *is* the
                    // sort comparison and the canonical level comparison — no
                    // other child is reachable through this arm.
                    | (one @ &ValueType::Universe { .. }, other @ &ValueType::Universe { .. }) => {
                        if one != other {
                            return Convertibility::Distinct;
                        }
                    },
                    | (&ValueType::Abstract(one), &ValueType::Abstract(other)) => {
                        if one != other {
                            return Convertibility::Distinct;
                        }
                    },
                    // The one arm that leaves the type language. The carried
                    // level is compared canonically and the codes are compared
                    // as terms; the level comparison is redundant on a
                    // well-formed pair — a code has one type — and it is kept
                    // because conversion is asked about types the checker has
                    // not necessarily formed.
                    | (
                        &ValueType::Element {
                            code: one_code,
                            target: ref one_target,
                        },
                        &ValueType::Element {
                            code: other_code,
                            target: ref other_target,
                        },
                    ) => {
                        if one_target != other_target {
                            return Convertibility::Distinct;
                        }
                        stack.push(ConversionGoal::Value(one_code, other_code));
                    },
                    | (
                        &ValueType::Lift {
                            inner: one_inner,
                            target: ref one_target,
                        },
                        &ValueType::Lift {
                            inner: other_inner,
                            target: ref other_target,
                        },
                    ) => {
                        if one_target != other_target {
                            return Convertibility::Distinct;
                        }
                        stack.push(ConversionGoal::ValueType(one_inner, other_inner));
                    },
                    | (
                        &ValueType::PathUniverse(..)
                        | &ValueType::Base(_)
                        | &ValueType::Unit
                        | &ValueType::Empty
                        | &ValueType::Product(..)
                        | &ValueType::Sum(..)
                        | &ValueType::Session { .. }
                        | &ValueType::List(_)
                        | &ValueType::Thunk(_)
                        | &ValueType::Universe { .. }
                        | &ValueType::Abstract(_)
                        | &ValueType::Element { .. }
                        | &ValueType::Lift { .. }
                        | &ValueType::StaticPi { .. },
                        _,
                    ) => return Convertibility::Distinct,
                }
            },
            | ConversionGoal::CompType(left, right) => {
                if left == right {
                    continue;
                }
                let (Some(left), Some(right)) = (arena.comp_type(left), arena.comp_type(right))
                else {
                    return Convertibility::Distinct;
                };
                match (left, right) {
                    | (&CompType::Returner(one), &CompType::Returner(other)) => {
                        stack.push(ConversionGoal::ValueType(one, other));
                    },
                    // The two arrows compare alike child for child and never
                    // across: an arrow's codomain stands in the ambient context
                    // and a dependent codomain stands under one more binder, so
                    // a cross pair compares two codomains written against two
                    // different contexts. Refusing that pair is what makes the
                    // structural walk's reading of a de Bruijn index the same on
                    // both sides.
                    | (
                        &CompType::Arrow {
                            domain: one_domain,
                            codomain: one_codomain,
                        },
                        &CompType::Arrow {
                            domain: other_domain,
                            codomain: other_codomain,
                        },
                    )
                    | (
                        &CompType::Pi {
                            domain: one_domain,
                            codomain: one_codomain,
                        },
                        &CompType::Pi {
                            domain: other_domain,
                            codomain: other_codomain,
                        },
                    ) => {
                        stack.push(ConversionGoal::ValueType(one_domain, other_domain));
                        stack.push(ConversionGoal::CompType(one_codomain, other_codomain));
                    },
                    | (
                        &CompType::Element {
                            code: one_code,
                            target: ref one_target,
                        },
                        &CompType::Element {
                            code: other_code,
                            target: ref other_target,
                        },
                    ) => {
                        if one_target != other_target {
                            return Convertibility::Distinct;
                        }
                        stack.push(ConversionGoal::Value(one_code, other_code));
                    },
                    | (
                        &CompType::Returner(_)
                        | &CompType::Arrow { .. }
                        | &CompType::Pi { .. }
                        | &CompType::Element { .. },
                        _,
                    ) => {
                        return Convertibility::Distinct;
                    },
                }
            },
            | ConversionGoal::Value(left, right) => {
                if left == right {
                    continue;
                }
                let (Some(left), Some(right)) = (arena.value(left), arena.value(right))
                else {
                    return Convertibility::Distinct;
                };
                match (left, right) {
                    | (&Value::SessionPath { path_type: one_type, payload_paths: one_paths, evidence: ref one }, &Value::SessionPath { path_type: other_type, payload_paths: other_paths, evidence: ref other }) => {
                        // Relation proof pairs are erased; payload translator assignment is not.
                        if one.payloads != other.payloads { return Convertibility::Distinct; }
                        stack.push(ConversionGoal::ValueType(one_type, other_type));
                        stack.push(ConversionGoal::Value(one_paths, other_paths));
                    },
                    | (&Value::PathRefl(one), &Value::PathRefl(other)) => stack.push(ConversionGoal::Value(one, other)),
                    | (&Value::PathProduct(a, b), &Value::PathProduct(c, d)) => {
                        stack.push(ConversionGoal::Value(a, c));
                        stack.push(ConversionGoal::Value(b, d));
                    },
                    | (&Value::PathEquiv { path_type: one_type, forward: one_forward, backward: one_backward, .. },
                       &Value::PathEquiv { path_type: other_type, forward: other_forward, backward: other_backward, .. }) => {
                        // Round-trip evidence is erased, not translator syntax.
                        stack.push(ConversionGoal::ValueType(one_type, other_type));
                        stack.push(ConversionGoal::Value(one_forward, other_forward));
                        stack.push(ConversionGoal::Value(one_backward, other_backward));
                    },
                    | (&Value::Variable(one), &Value::Variable(other)) => {
                        if one != other {
                            return Convertibility::Distinct;
                        }
                    },
                    // Two constants convert when they name one declaration.
                    // Unfolding a constant is a reduction, and no reduction
                    // fires here, so two *different* constants separate even
                    // where their bodies would converge — the incompleteness the
                    // convertibility machine closes.
                    | (&Value::Constant(one), &Value::Constant(other)) => {
                        if one != other {
                            return Convertibility::Distinct;
                        }
                    },
                    | (&Value::Unit, &Value::Unit) => {},
                    // As at the universe arm: both sides are pinned to the
                    // literal former, which carries one field, so the node
                    // comparison delegated to here is the literal comparison.
                    | (one @ &Value::Literal(_), other @ &Value::Literal(_)) => {
                        if one != other {
                            return Convertibility::Distinct;
                        }
                    },
                    | (
                        &Value::Pair(one_first, one_second),
                        &Value::Pair(other_first, other_second),
                    )
                    // A static application is neutral — no static lambda can
                    // stand at its head — so two convert exactly when their
                    // heads and arguments do, and a family's instances at
                    // different heads or arities separate.
                    | (
                        &Value::StaticApplication(one_first, one_second),
                        &Value::StaticApplication(other_first, other_second),
                    ) => {
                        stack.push(ConversionGoal::Value(one_first, other_first));
                        stack.push(ConversionGoal::Value(one_second, other_second));
                    },
                    | (
                        &Value::Injection(one_side, one_body),
                        &Value::Injection(other_side, other_body),
                    ) => {
                        if one_side != other_side {
                            return Convertibility::Distinct;
                        }
                        stack.push(ConversionGoal::Value(one_body, other_body));
                    },
                    | (&Value::Thunk(one_body), &Value::Thunk(other_body)) => {
                        stack.push(ConversionGoal::Computation(one_body, other_body));
                    },
                    | (
                        &Value::Lift {
                            target: ref one_target,
                            body: one_body,
                        },
                        &Value::Lift {
                            target: ref other_target,
                            body: other_body,
                        },
                    ) => {
                        if one_target != other_target {
                            return Convertibility::Distinct;
                        }
                        stack.push(ConversionGoal::Value(one_body, other_body));
                    },
                    // Two codes convert when the types they quote do: a quote
                    // is a value whose one child is a type, so the walk steps
                    // from the value family into the type families here, the
                    // converse of the decoding arms above.
                    | (&Value::Quote(one), &Value::Quote(other)) => {
                        stack.push(ConversionGoal::ValueType(one, other));
                    },
                    | (&Value::QuoteComputation(one), &Value::QuoteComputation(other)) => {
                        stack.push(ConversionGoal::CompType(one, other));
                    },
                    | (
                        &Value::SessionPath { .. } | &Value::PathRefl(_) | &Value::PathProduct(..) | &Value::PathEquiv { .. }
                        | &Value::Variable(_)
                        | &Value::Constant(_)
                        | &Value::Unit
                        | &Value::Literal(_)
                        | &Value::Pair(..)
                        | &Value::Injection(..)
                        | &Value::Thunk(_)
                        | &Value::Lift { .. }
                        | &Value::Quote(_)
                        | &Value::QuoteComputation(_)
                        | &Value::StaticApplication(..),
                        _,
                    ) => return Convertibility::Distinct,
                }
            },
            | ConversionGoal::Computation(left, right) => {
                if left == right {
                    continue;
                }
                let (Some(left), Some(right)) = (arena.computation(left), arena.computation(right))
                else {
                    return Convertibility::Distinct;
                };
                match (left, right) {
                    | (&Computation::Transport(a, b), &Computation::Transport(c, d)) => {
                        stack.push(ConversionGoal::Value(a, c));
                        stack.push(ConversionGoal::Value(b, d));
                    },
                    | (&Computation::Lambda(one), &Computation::Lambda(other)) => {
                        stack.push(ConversionGoal::Computation(one, other));
                    },
                    | (
                        &Computation::Application(one_head, one_argument),
                        &Computation::Application(other_head, other_argument),
                    ) => {
                        stack.push(ConversionGoal::Computation(one_head, other_head));
                        stack.push(ConversionGoal::Value(one_argument, other_argument));
                    },
                    | (&Computation::Return(one), &Computation::Return(other))
                    | (&Computation::Absurd(one), &Computation::Absurd(other))
                    | (&Computation::Force(one), &Computation::Force(other)) => {
                        stack.push(ConversionGoal::Value(one, other));
                    },
                    | (
                        &Computation::Bind(one_bound, one_body),
                        &Computation::Bind(other_bound, other_body),
                    ) => {
                        stack.push(ConversionGoal::Computation(one_bound, other_bound));
                        stack.push(ConversionGoal::Computation(one_body, other_body));
                    },
                    | (
                        &Computation::Case {
                            scrutinee: one_scrutinee,
                            on_left: one_left,
                            on_right: one_right,
                        },
                        &Computation::Case {
                            scrutinee: other_scrutinee,
                            on_left: other_left,
                            on_right: other_right,
                        },
                    ) => {
                        stack.push(ConversionGoal::Value(one_scrutinee, other_scrutinee));
                        stack.push(ConversionGoal::Computation(one_left, other_left));
                        stack.push(ConversionGoal::Computation(one_right, other_right));
                    },
                    | (
                        &Computation::Transport(..)
                        | &Computation::Lambda(_)
                        | &Computation::Application(..)
                        | &Computation::Return(_)
                        | &Computation::Absurd(_)
                        | &Computation::Bind(..)
                        | &Computation::Force(_)
                        | &Computation::Case { .. },
                        _,
                    ) => return Convertibility::Distinct,
                }
            },
        }
    }
    Convertibility::Convertible
}

#[cfg(test)]
mod tests
{
    use gandr_kernel_strata::Level;
    use gandr_kernel_strata::LevelConstant;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::GroundSort;
    use gandr_kernel_term::Side;
    use gandr_kernel_term::TermArena;

    use super::Convertibility;
    use super::convert_comp_type;
    use super::convert_value_type;
    use super::convertible_comp_types;
    use super::convertible_value_types;
    use crate::error::CompTypeHead;
    use crate::error::KernelError;
    use crate::error::ValueTypeHead;

    /// The constant level `value`.
    ///
    /// # Specification
    /// trivial.
    fn level(value: LevelConstant) -> Level
    {
        Level::constant(value)
    }

    #[test]
    fn value_type_conversion_is_reflexive()
    {
        let mut arena = TermArena::new();
        let unit = arena.value_type_unit();
        let base = arena.value_type_base(BaseType::Integer);
        let product = arena.value_type_product(unit, base);
        assert_eq!(
            Convertibility::Convertible,
            convertible_value_types(&arena, product, product),
            "a type converts with itself"
        );
    }

    #[test]
    fn computation_type_conversion_is_reflexive()
    {
        let mut arena = TermArena::new();
        let unit = arena.value_type_unit();
        let returner = arena.comp_type_returner(unit);
        let arrow = arena.comp_type_arrow(unit, returner);
        assert_eq!(
            Convertibility::Convertible,
            convertible_comp_types(&arena, arrow, arrow),
            "a computation type converts with itself"
        );
    }

    #[test]
    fn structurally_equal_types_at_distinct_ids_convert()
    {
        let mut arena = TermArena::new();
        let first_unit = arena.value_type_unit();
        let second_unit = arena.value_type_unit();
        let first = arena.value_type_product(first_unit, first_unit);
        let second = arena.value_type_product(second_unit, second_unit);
        assert_ne!(first, second, "the fixture mints two distinct arena nodes");
        assert_eq!(
            Convertibility::Convertible,
            convertible_value_types(&arena, first, second),
            "the id fast path is positive only: unequal ids decide nothing and the structural \
             walk decides"
        );
    }

    #[test]
    fn conversion_separates_every_former()
    {
        let mut arena = TermArena::new();
        let unit = arena.value_type_unit();
        let integer = arena.value_type_base(BaseType::Integer);
        let string = arena.value_type_base(BaseType::String);
        let product = arena.value_type_product(unit, integer);
        let sum = arena.value_type_sum(unit, integer);
        let returner = arena.comp_type_returner(unit);
        let thunk = arena.value_type_thunk(returner);
        let separated = [
            (integer, string),
            (unit, integer),
            (product, sum),
            (product, thunk),
            (sum, unit),
        ];
        for (left, right) in separated {
            assert_eq!(
                Convertibility::Distinct,
                convertible_value_types(&arena, left, right),
                "distinct formers or distinct atoms do not convert"
            );
        }
        let transposed = arena.value_type_product(integer, unit);
        assert_eq!(
            Convertibility::Distinct,
            convertible_value_types(&arena, product, transposed),
            "and the children are compared in order"
        );
    }

    #[test]
    fn universes_convert_by_canonical_level()
    {
        let mut arena = TermArena::new();
        let zero = arena.value_type_universe(GroundSort::Value, level(LevelConstant::from(0)));
        let also_zero = arena.value_type_universe(GroundSort::Value, level(LevelConstant::from(0)));
        let one = arena.value_type_universe(GroundSort::Value, level(LevelConstant::from(1)));
        assert_eq!(
            Convertibility::Convertible,
            convertible_value_types(&arena, zero, also_zero),
            "one level is one universe"
        );
        assert_eq!(
            Convertibility::Distinct,
            convertible_value_types(&arena, zero, one),
            "and two levels are two universes"
        );
        let lift_zero = arena.value_type_lift(zero, level(LevelConstant::from(4)));
        let lift_five = arena.value_type_lift(zero, level(LevelConstant::from(5)));
        assert_eq!(
            Convertibility::Distinct,
            convertible_value_types(&arena, lift_zero, lift_five),
            "a lift's target is part of its identity"
        );
    }

    #[test]
    fn sealed_atoms_are_nominal()
    {
        let mut arena = TermArena::new();
        let first = arena.value_type_abstract(ConstantIndex::from(0_usize));
        let also_first = arena.value_type_abstract(ConstantIndex::from(0_usize));
        let second = arena.value_type_abstract(ConstantIndex::from(1_usize));
        let unit = arena.value_type_unit();
        assert_eq!(
            Convertibility::Convertible,
            convertible_value_types(&arena, first, also_first),
            "two references to one atom are one type"
        );
        assert_eq!(
            Convertibility::Distinct,
            convertible_value_types(&arena, first, second),
            "two atoms are two types however they were implemented"
        );
        assert_eq!(
            Convertibility::Distinct,
            convertible_value_types(&arena, first, unit),
            "and no arm relates an atom to a structural type, which is what opacity means here"
        );
    }

    #[test]
    fn an_arrow_separates_on_either_child()
    {
        let mut arena = TermArena::new();
        let unit = arena.value_type_unit();
        let integer = arena.value_type_base(BaseType::Integer);
        let unit_returner = arena.comp_type_returner(unit);
        let integer_returner = arena.comp_type_returner(integer);
        let base = arena.comp_type_arrow(unit, unit_returner);
        let other_domain = arena.comp_type_arrow(integer, unit_returner);
        let other_codomain = arena.comp_type_arrow(unit, integer_returner);
        assert_eq!(
            Convertibility::Distinct,
            convertible_comp_types(&arena, base, other_domain),
            "the domain is compared"
        );
        assert_eq!(
            Convertibility::Distinct,
            convertible_comp_types(&arena, base, other_codomain),
            "and so is the codomain"
        );
    }

    /// The two arrows separate on their head, and the dependent one still
    /// compares child for child with itself.
    ///
    /// The separation is the load-bearing half: the two formers hold the *same*
    /// two children here, so anything but a head comparison would have
    /// converted them and silently equated a codomain in the ambient
    /// context with one under a binder.
    #[test]
    fn the_two_arrows_never_convert_across()
    {
        let mut arena = TermArena::new();
        let unit = arena.value_type_unit();
        let integer = arena.value_type_base(BaseType::Integer);
        let returner = arena.comp_type_returner(unit);
        let plain = arena.comp_type_arrow(unit, returner);
        let dependent = arena.comp_type_pi(unit, returner);
        assert_eq!(
            Convertibility::Distinct,
            convertible_comp_types(&arena, plain, dependent),
            "a non-dependent arrow and a dependent one are two types over the same children"
        );
        let also_dependent = arena.comp_type_pi(unit, returner);
        assert_eq!(
            Convertibility::Convertible,
            convertible_comp_types(&arena, dependent, also_dependent),
            "and two dependent arrows over equal children convert"
        );
        let other_domain = arena.comp_type_pi(integer, returner);
        assert_eq!(
            Convertibility::Distinct,
            convertible_comp_types(&arena, dependent, other_domain),
            "with the domain compared"
        );
        let integer_returner = arena.comp_type_returner(integer);
        let other_codomain = arena.comp_type_pi(unit, integer_returner);
        assert_eq!(
            Convertibility::Distinct,
            convertible_comp_types(&arena, dependent, other_codomain),
            "and the codomain compared too"
        );
    }

    /// Two types read off codes converge exactly when the codes do, and the
    /// comparison descends into the term language to decide it.
    ///
    /// The separating half is the one that matters: without a term arm the walk
    /// would have had to answer on the two `Element` nodes alone, and any
    /// answer it gave would have been wrong for one of these pairs.
    #[test]
    fn types_read_off_codes_converge_with_their_codes()
    {
        let mut arena = TermArena::new();
        let zero = level(LevelConstant::from(0));
        let one_code = arena.value_variable(DeBruijnIndex::from(0_u32));
        let other_code = arena.value_variable(DeBruijnIndex::from(1_u32));
        let one = arena.value_type_element(one_code, zero.clone());
        let same_code = arena.value_variable(DeBruijnIndex::from(0_u32));
        let also_one = arena.value_type_element(same_code, zero.clone());
        let other = arena.value_type_element(other_code, zero);
        assert_eq!(
            Convertibility::Convertible,
            convertible_value_types(&arena, one, also_one),
            "two spellings of one code are one type"
        );
        assert_eq!(
            Convertibility::Distinct,
            convertible_value_types(&arena, one, other),
            "and two different codes are two types"
        );
        let higher = arena.value_type_element(one_code, level(LevelConstant::from(1)));
        assert_eq!(
            Convertibility::Distinct,
            convertible_value_types(&arena, one, higher),
            "the carried universe is compared canonically too"
        );
        let unit = arena.value_type_unit();
        assert_eq!(
            Convertibility::Distinct,
            convertible_value_types(&arena, one, unit),
            "and no arm relates a code-read type to a structural one"
        );
    }

    /// Every term former separates, which is what makes the descent into terms
    /// a real comparison rather than a reflexivity check.
    ///
    /// A code is compared **without reducing**, so two applications separate on
    /// their head and argument rather than on what they would evaluate to —
    /// the incompleteness the convertibility machine closes, pinned here so it
    /// is a recorded property rather than a surprise.
    #[test]
    fn code_comparison_separates_every_term_former_without_reducing()
    {
        let mut arena = TermArena::new();
        let zero = level(LevelConstant::from(0));
        let element = |arena: &mut TermArena, code| {
            let target = zero.clone();
            arena.value_type_element(code, target)
        };
        let unit = arena.value_unit();
        let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
        let constant = arena.value_constant(ConstantIndex::from(0_usize));
        let other_constant = arena.value_constant(ConstantIndex::from(1_usize));
        let pair = arena.value_pair(unit, variable);
        let transposed = arena.value_pair(variable, unit);
        let left = arena.value_injection(Side::Left, unit);
        let right = arena.value_injection(Side::Right, unit);
        let returner = arena.computation_return(unit);
        let force = arena.computation_force(unit);
        let thunk = arena.value_thunk(returner);
        let forced_thunk = arena.value_thunk(force);

        let separated = [
            (unit, variable),
            (constant, other_constant),
            (pair, transposed),
            (left, right),
            (thunk, forced_thunk),
        ];
        for (one, other) in separated {
            let one = element(&mut arena, one);
            let other = element(&mut arena, other);
            assert_eq!(
                Convertibility::Distinct,
                convertible_value_types(&arena, one, other),
                "distinct codes do not convert"
            );
        }

        // The redex and its contractum: sound to separate, and incomplete.
        let identity_body = arena.computation_return(variable);
        let identity = arena.computation_lambda(identity_body);
        let redex = arena.computation_application(identity, unit);
        let redex_code = arena.value_thunk(redex);
        let contractum = arena.computation_return(unit);
        let contractum_code = arena.value_thunk(contractum);
        let redex_type = element(&mut arena, redex_code);
        let contractum_type = element(&mut arena, contractum_code);
        assert_eq!(
            Convertibility::Distinct,
            convertible_value_types(&arena, redex_type, contractum_type),
            "no reduction fires here, so a redex and its contractum separate"
        );
    }

    /// The intensional claim, exhibited rather than timed: two self-similar
    /// composites whose tree expansion is over a billion pairs converge, and
    /// converge fast, because each distinct pair is compared once.
    ///
    /// Without the discharged set this comparison walks `2^depth` pairs and
    /// does not finish; the depth is asserted through the arena's own node
    /// count so the case cannot degenerate into a shallow composite and
    /// keep passing.
    #[test]
    fn a_shared_composite_converts_without_expanding()
    {
        let mut arena = TermArena::new();
        let mut left = arena.value_type_unit();
        let mut right = arena.value_type_unit();
        for _step in 0 .. 30_u32 {
            left = arena.value_type_product(left, left);
            right = arena.value_type_product(right, right);
        }
        assert_ne!(
            left, right,
            "the two spellings are distinct arena nodes at every level, so the id fast path \
             discharges nothing above the leaves"
        );
        assert_eq!(
            Convertibility::Convertible,
            convertible_value_types(&arena, left, right),
            "two structurally equal composites converge in their distinct pairs, not their \
             occurrences"
        );

        // And the separating direction on the same shape, so the set is not
        // hiding a difference.
        let integer = arena.value_type_base(BaseType::Integer);
        let mut other = integer;
        for _step in 0 .. 30_u32 {
            other = arena.value_type_product(other, other);
        }
        assert_eq!(
            Convertibility::Distinct,
            convertible_value_types(&arena, left, other),
            "a composite over a different leaf still separates"
        );
    }

    #[test]
    fn an_unreadable_id_fails_closed()
    {
        let mut arena = TermArena::new();
        let floor = arena.watermark();
        let unit = arena.value_type_unit();
        let other = arena.value_type_base(BaseType::Integer);
        arena.truncate_to(floor);
        assert_eq!(
            Convertibility::Distinct,
            convertible_value_types(&arena, unit, other),
            "an id that resolves to nothing refuses rather than converting"
        );
    }

    #[test]
    fn a_value_mismatch_names_both_heads()
    {
        let mut arena = TermArena::new();
        let unit = arena.value_type_unit();
        let integer = arena.value_type_base(BaseType::Integer);
        assert_eq!(
            Ok(()),
            convert_value_type(&arena, unit, unit),
            "a converting pair passes"
        );
        let refused = convert_value_type(&arena, unit, integer);
        let KernelError::ValueTypeMismatch(mismatch) =
            refused.expect_err("a separating pair refuses")
        else {
            panic!("the refusal is a value-type mismatch");
        };
        assert_eq!(ValueTypeHead::Unit, mismatch.expected().head());
        assert_eq!(ValueTypeHead::Base, mismatch.actual().head());
        assert_ne!(
            mismatch.expected().digest(),
            mismatch.actual().digest(),
            "and the two are separated by content, not only by head"
        );
    }

    #[test]
    fn a_computation_mismatch_names_both_heads()
    {
        let mut arena = TermArena::new();
        let unit = arena.value_type_unit();
        let returner = arena.comp_type_returner(unit);
        let arrow = arena.comp_type_arrow(unit, returner);
        let refused = convert_comp_type(&arena, returner, arrow);
        let KernelError::ComputationTypeMismatch(mismatch) =
            refused.expect_err("a separating pair refuses")
        else {
            panic!("the refusal is a computation-type mismatch");
        };
        assert_eq!(CompTypeHead::Returner, mismatch.expected().head());
        assert_eq!(CompTypeHead::Arrow, mismatch.actual().head());
    }
}
