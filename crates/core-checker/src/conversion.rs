//! The conversion module boundary: the two places a synthesised type meets the
//! type it is checked against, and the decision behind them.
//!
//! # Two bridges, one decision, nothing else calls it
//!
//! The judgement compares types in exactly two rules: a synthesising value in
//! checking position crosses [`value_bridge`], a synthesising computation in
//! checking position crosses [`comp_bridge`]. Both lower to the one private
//! decision [`convert`]; no rule compares ids or nodes itself, so swapping the
//! decision — for the core normaliser's conversion, when a type former embeds
//! terms — is a change of this module alone.
//!
//! # Structural agreement is the whole conversion of the fragment's types
//!
//! The fragment's types embed no term, so no type reduces: two formed types
//! convert exactly when they are the same tree. The decision walks both trees
//! together, with two economies. Two equal ids are one node, so the pair is
//! accepted without reading it; and a pair met once is not compared again, so
//! shared subtrees cost their distinct pairs, not their expansion.
//!
//! # The declared projection
//!
//! Each crossing of a bridge adds one to the run's [`ConversionCount`], which
//! the faces return beside their result. The count is how a test observes that
//! a check converted where it should and nowhere else, without reaching into
//! the walk.

use alloc::collections::BTreeSet;
use alloc::vec::Vec;
use core::fmt;

use gandr_core_term::CompTypeId;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;

use crate::refusal::CheckRefusal;
use crate::refusal::Mismatch;
use crate::view::CompTypeView;
use crate::view::ValueTypeView;
use crate::view::comp_type_view;
use crate::view::value_type_view;

/// How many times a judgement crossed the conversion boundary.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ConversionCount(usize);

impl ConversionCount
{
    /// The count after one more crossing, saturating at the ceiling.
    ///
    /// # Specification
    /// trivial.
    const fn crossed(self) -> Self
    {
        Self(self.0.saturating_add(1_usize))
    }
}

impl From<usize> for ConversionCount
{
    /// The count of `crossings` crossings.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(crossings: usize) -> Self
    {
        Self(crossings)
    }
}

impl From<ConversionCount> for usize
{
    /// The number of crossings `count` records.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: ConversionCount) -> Self
    {
        count.0
    }
}

impl fmt::Display for ConversionCount
{
    /// Writes the number of crossings.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        fmt::Display::fmt(&self.0, f)
    }
}

/// A pair of type nodes of one sort, to be compared.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Pairing
{
    /// Two value types.
    Values(ValueTypeId, ValueTypeId),
    /// Two computation types.
    Comps(CompTypeId, CompTypeId),
}

/// The decision's verdict on a pair.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Agreement
{
    /// The two types are the same tree.
    Convertible,
    /// The two types differ at some node.
    Apart,
}

/// Cross the value bridge: the type `at` synthesised against the type it is
/// checked against.
///
/// # Specification
/// - requires: both types are formed, in `arena`.
/// - ensures: success exactly when `synthesised` and `expected` are the same
///   tree; `tally` is one higher on every outcome.
/// - provides: the only comparison of value types the judgement makes.
/// - fails: [`CheckRefusal::TypeMismatch`] with [`Mismatch::Value`] naming `at`
///   and both types when they differ.
/// - panics: none.
/// - intension: one crossing per call, counted in `tally`.
///
/// # Errors
/// - [`CheckRefusal::TypeMismatch`] — the two types differ.
///
/// # Judgement
/// - expected: `expected`
///
/// # Adequacy
/// - hypothesis: L3 — the decision is [`convert`]'s; this bridge's own surface
///   is the refusal it builds and the count, separated by an agreeing and a
///   differing pair, each count asserted.
/// - witness: `judgement::tests::a_mismatched_literal_is_refused_with_both_types`
/// - witness: `judgement::tests::a_two_bridge_check_crosses_the_boundary_twice`
pub fn value_bridge(
    arena: &CoreArena,
    at: ValueId,
    synthesised: ValueTypeId,
    expected: ValueTypeId,
    tally: &mut ConversionCount,
) -> Result<(), CheckRefusal>
{
    *tally = tally.crossed();
    match convert(arena, Pairing::Values(synthesised, expected))? {
        | Agreement::Convertible => Ok(()),
        | Agreement::Apart => Err(CheckRefusal::TypeMismatch(Mismatch::Value {
            at,
            synthesised,
            expected,
        })),
    }
}

/// Cross the computation bridge: the type `at` synthesised against the type it
/// is checked against.
///
/// # Specification
/// - requires: both types are formed, in `arena`.
/// - ensures: success exactly when `synthesised` and `expected` are the same
///   tree; `tally` is one higher on every outcome.
/// - provides: the only comparison of computation types the judgement makes.
/// - fails: [`CheckRefusal::TypeMismatch`] with [`Mismatch::Computation`]
///   naming `at` and both types when they differ.
/// - panics: none.
/// - intension: one crossing per call, counted in `tally`.
///
/// # Errors
/// - [`CheckRefusal::TypeMismatch`] — the two types differ.
///
/// # Judgement
/// - expected: `expected`
///
/// # Adequacy
/// - hypothesis: L3 — as for [`value_bridge`], over computation types.
/// - witness: `judgement::tests::a_mismatched_application_is_refused_at_the_computation_bridge`
/// - witness: `judgement::tests::a_two_bridge_check_crosses_the_boundary_twice`
pub fn comp_bridge(
    arena: &CoreArena,
    at: ComputationId,
    synthesised: CompTypeId,
    expected: CompTypeId,
    tally: &mut ConversionCount,
) -> Result<(), CheckRefusal>
{
    *tally = tally.crossed();
    match convert(arena, Pairing::Comps(synthesised, expected))? {
        | Agreement::Convertible => Ok(()),
        | Agreement::Apart => Err(CheckRefusal::TypeMismatch(Mismatch::Computation {
            at,
            synthesised,
            expected,
        })),
    }
}

/// Decide whether the two types of `root` are the same tree.
///
/// # Specification
/// - requires: nothing — the bridges pass formed types, and anything else is
///   refused where the walk meets it.
/// - ensures: [`Agreement::Convertible`] exactly when both sides have the same
///   former at every position the walk reaches; [`Agreement::Apart`] at the
///   first position they differ.
/// - fails: the refusal a view gives for a node outside the fragment or a
///   dangling id.
/// - panics: none.
/// - intension: a pair of equal ids is accepted without reading the node, and a
///   pair already met is not compared again; a worklist, so no depth overflows
///   a stack.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surfaces are the id fast path, the
///   per-former comparison and the child pairing, separated by one id against
///   itself, two structurally equal trees at distinct ids, trees differing at
///   the root and beneath a thunk in either order, and a dangling id; the fast
///   path is pinned against the structural decision by property.
/// - witness: `conversion::tests::one_id_converts_without_being_read`
/// - witness: `conversion::tests::equal_trees_at_distinct_ids_convert`
/// - witness: `conversion::tests::differing_trees_are_apart_in_either_order`
/// - witness: `conversion::tests::a_dangling_type_is_refused`
/// - witness: `conversion::tests::the_id_fast_path_agrees_with_the_structural_decision`
fn convert(
    arena: &CoreArena,
    root: Pairing,
) -> Result<Agreement, CheckRefusal>
{
    let mut pending = Vec::from([root]);
    let mut met = BTreeSet::new();
    while let Some(pairing) = pending.pop() {
        let reflexive = match pairing {
            | Pairing::Values(left, right) => left == right,
            | Pairing::Comps(left, right) => left == right,
        };
        if reflexive || !met.insert(pairing) {
            continue;
        }
        match pairing {
            | Pairing::Values(left, right) => {
                match (
                    value_type_view(arena, left)?,
                    value_type_view(arena, right)?,
                ) {
                    | (ValueTypeView::Integer, ValueTypeView::Integer)
                    | (ValueTypeView::String, ValueTypeView::String)
                    | (ValueTypeView::Unit, ValueTypeView::Unit) => {},
                    | (ValueTypeView::Thunk(left), ValueTypeView::Thunk(right)) => {
                        pending.push(Pairing::Comps(left, right));
                    },
                    | (
                        ValueTypeView::Integer
                        | ValueTypeView::String
                        | ValueTypeView::Unit
                        | ValueTypeView::Thunk(_),
                        _,
                    ) => return Ok(Agreement::Apart),
                }
            },
            | Pairing::Comps(left, right) => {
                match (comp_type_view(arena, left)?, comp_type_view(arena, right)?) {
                    | (CompTypeView::Returner(left), CompTypeView::Returner(right)) => {
                        pending.push(Pairing::Values(left, right));
                    },
                    | (
                        CompTypeView::Arrow {
                            domain: left_domain,
                            codomain: left_codomain,
                        },
                        CompTypeView::Arrow {
                            domain: right_domain,
                            codomain: right_codomain,
                        },
                    ) => {
                        pending.push(Pairing::Comps(left_codomain, right_codomain));
                        pending.push(Pairing::Values(left_domain, right_domain));
                    },
                    | (CompTypeView::Returner(_) | CompTypeView::Arrow { .. }, _) => {
                        return Ok(Agreement::Apart);
                    },
                }
            },
        }
    }
    Ok(Agreement::Convertible)
}

#[cfg(test)]
mod tests
{
    use gandr_core_term::CoreArena;
    use gandr_kernel_term::BaseType;
    use proptest::prelude::ProptestConfig;
    use proptest::prelude::prop_assert_eq;
    use proptest::prelude::proptest;

    use super::Agreement;
    use super::Pairing;
    use super::convert;
    use crate::fixture::TypeRecipe;
    use crate::fixture::dangling_value_type;
    use crate::fixture::type_recipe;
    use crate::refusal::CheckRefusal;
    use crate::refusal::CoreNode;
    use crate::refusal::TypeNode;
    use crate::refusal::UnadmittedFormer;

    #[test]
    fn one_id_converts_without_being_read()
    {
        let mut arena = CoreArena::new();
        let unit = arena.value_type_unit();
        let result = arena.comp_type_returner(unit);
        let pi = arena.comp_type_pi(unit, result);
        let copy = arena.comp_type_pi(unit, result);
        assert_eq!(
            convert(&arena, Pairing::Comps(pi, pi)),
            Ok(Agreement::Convertible),
            "one id is one node, so the pair is accepted without its former being read"
        );
        assert_eq!(
            convert(&arena, Pairing::Comps(pi, copy)),
            Err(CheckRefusal::OutOfFragment {
                at: CoreNode::Type(TypeNode::Computation(pi)),
                former: UnadmittedFormer::Pi,
            }),
            "two ids are read, so the same former at a distinct id is met and refused"
        );
    }

    #[test]
    fn equal_trees_at_distinct_ids_convert()
    {
        let mut arena = CoreArena::new();
        let build = |arena: &mut CoreArena| {
            let integer = arena.value_type_base(BaseType::Integer);
            let result = arena.comp_type_returner(integer);
            let arrow = arena.comp_type_arrow(integer, result);
            arena.value_type_thunk(arrow)
        };
        let left = build(&mut arena);
        let right = build(&mut arena);
        assert_ne!(left, right, "the two trees sit at distinct ids");
        assert_eq!(
            convert(&arena, Pairing::Values(left, right)),
            Ok(Agreement::Convertible),
            "conversion compares trees, not ids"
        );
    }

    #[test]
    fn differing_trees_are_apart_in_either_order()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let string = arena.value_type_base(BaseType::String);
        let unit = arena.value_type_unit();
        let returns_integer = arena.comp_type_returner(integer);
        let returns_string = arena.comp_type_returner(string);
        let thunk_integer = arena.value_type_thunk(returns_integer);
        let thunk_string = arena.value_type_thunk(returns_string);
        let arrow = arena.comp_type_arrow(unit, returns_integer);
        let pairs = [
            Pairing::Values(integer, string),
            Pairing::Values(unit, thunk_integer),
            Pairing::Values(thunk_integer, thunk_string),
            Pairing::Comps(returns_integer, arrow),
        ];
        for pairing in pairs {
            let swapped = match pairing {
                | Pairing::Values(left, right) => Pairing::Values(right, left),
                | Pairing::Comps(left, right) => Pairing::Comps(right, left),
            };
            assert_eq!(
                convert(&arena, pairing),
                Ok(Agreement::Apart),
                "{pairing:?} differ"
            );
            assert_eq!(
                convert(&arena, swapped),
                Ok(Agreement::Apart),
                "{swapped:?} differ in the other order too"
            );
        }
    }

    #[test]
    fn a_dangling_type_is_refused()
    {
        let mut arena = CoreArena::new();
        let unit = arena.value_type_unit();
        let dangling = dangling_value_type();
        assert_eq!(
            convert(&arena, Pairing::Values(unit, dangling)),
            Err(CheckRefusal::DanglingNode {
                node: CoreNode::Type(TypeNode::Value(dangling)),
            }),
            "an id from another arena is refused rather than read"
        );
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(256))]

        #[test]
        fn the_id_fast_path_agrees_with_the_structural_decision(
            first in type_recipe(),
            second in type_recipe(),
        )
        {
            let mut arena = CoreArena::new();
            let first_tree = TypeRecipe::build(&first, &mut arena);
            let first_copy = TypeRecipe::build(&first, &mut arena);
            let second_tree = TypeRecipe::build(&second, &mut arena);
            let second_copy = TypeRecipe::build(&second, &mut arena);
            prop_assert_eq!(
                convert(&arena, Pairing::Values(first_tree, first_copy)),
                Ok(Agreement::Convertible),
                "a tree converts with its copy at fresh ids"
            );
            let verdict = convert(&arena, Pairing::Values(first_tree, second_tree));
            prop_assert_eq!(
                convert(&arena, Pairing::Values(second_tree, first_tree)),
                verdict,
                "the decision is symmetric"
            );
            prop_assert_eq!(
                convert(&arena, Pairing::Values(first_copy, second_copy)),
                verdict,
                "replacing either side by a copy at fresh ids keeps the verdict"
            );
            prop_assert_eq!(
                verdict == Ok(Agreement::Convertible),
                first.shape() == second.shape(),
                "the trees convert exactly when their shapes agree"
            );
        }
    }
}
