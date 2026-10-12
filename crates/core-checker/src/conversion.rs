//! The conversion module boundary: the three places a synthesised type meets
//! the type it is checked against, and the decision behind them.
//!
//! # Three bridges, one decision, nothing else calls it
//!
//! The judgement compares types in exactly three rules: a synthesising value in
//! checking position crosses [`value_bridge`], a synthesising computation in
//! checking position crosses [`comp_bridge`], and the code of a decode crosses
//! [`decode_bridge`] when formation checks it. The first two lower to the one
//! private decision [`convert`]; no rule compares ids or nodes itself.
//!
//! # Structural agreement, read at the weak head
//!
//! Two formed types convert when they are the same tree once every decode of a
//! code constant with a body is read as the type its body denotes. The walk
//! reads each side at its weak head — [`CheckingContext`] unfolds such a
//! decode through the normaliser's conversion machine, which certifies each
//! unfolding — and then compares former by former: a universe and a lift by
//! their sort and level exactly, a decode left rigid by its code, a variable
//! or a constant without a body, compared as a leaf. Two equal ids are one
//! node, so the pair is accepted without reading it; and a pair met once is
//! not compared again, so shared subtrees cost their distinct pairs, not their
//! expansion.
//!
//! # The unknown type is consistent with every type
//!
//! Where either side is the unknown type — a hole's, a mark's, or the decode
//! of a code that is a hole or a mark — the walk accepts the pair and goes no
//! deeper: the relation is consistency in the sense of Hazelnut (Omar et al.,
//! POPL 2017, doi:10.1145/3009837.3009900), which is conversion with the
//! unknown as a wildcard, and it coincides with conversion on types that hold
//! no unknown. Codes read the same way: a hole or a mark at a code's head
//! agrees with any code, and a data index whose root is a hole or a mark
//! agrees with any index. A hole nested beneath an index's root is compared
//! as syntax with the rest of the index, so such an index can be refused
//! where a finer walk would accept it; the kernel admits no index that holds
//! a hole either way.
//!
//! # Smallness lives at the value bridge alone
//!
//! A code that synthesised the value universe at level `k` checks at the
//! value universe at any level `l` at or above `k`: the bridge records a
//! [`Lift`] at the code, which the kernel bridge writes as the kernel's
//! explicit lift. A computation universe admits no such crossing — the core
//! has no lift of a computation type — and no universe crosses to another
//! sort. The rule fires only at the head of the two types; beneath a former,
//! universes compare exactly, so cumulativity never hides inside a thunk type
//! or an arrow. Formation never asks it: a decode's code synthesises exactly
//! the universe the decode names.
//!
//! # The declared projection
//!
//! Each crossing of a bridge adds one to the run's [`ConversionCount`], which
//! the faces return beside their result. The count is how a test observes that
//! a check converted where it should and nowhere else, without reaching into
//! the walk.
//!
//! # Why three bridges
//!
//! Nothing else in the crate can reach [`convert`], so the three sites are a
//! visibility fact rather than a count someone asserts. The count saturates at
//! its maximum. The fixture `def f : U (Integer → F Integer) = thunk { λx.
//! (force g) x }`, with `g` of the same type, crosses the value and computation
//! bridges once each and reports two.
//!
//! The alternatives were rebuilding and comparing a synthesised type at every
//! rule, which spreads type comparison over dozens of sites, and a counting
//! lint, which needs a whole-crate pass and a declared expected number where a
//! visibility rule needs neither. The decode bridge is the third site because a
//! decode's code is a term whose type is a universe, and formation, which runs
//! in the judgement's machine, is where that term is checked. The choice
//! reverses when a former brings a cover merge — a sum elimination whose
//! branches synthesise — at which point the merge joins the module and the
//! projection's expected values change with it.
//!
//! # Why smallness is a lift
//!
//! A computation code checked one level up is `LevelMismatch`, and a universe
//! offered at the other sort is `SortMismatch`. A lift the author writes is
//! accepted only when it raises; one that does not is the unadmitted
//! `TypeLift`. The alternatives were full cumulativity as subtyping, which the
//! kernel would have to rediscover at every comparison instead of checking one
//! lift at a recorded site, and no cumulativity, which makes every small type
//! unusable at a larger universe without an annotation the author cannot write
//! in the surface. The choice reverses if the kernel gains cumulativity of its
//! own, at which point the recorded lift is redundant and the bridge stops
//! writing it.
//!
//! # Variance
//!
//! A returner's row is covariant: `F A` stands where `F^ε A` is expected, never
//! the reverse. Operation payload and reply types are invariant. A stack
//! `Stack(B, C)` is contravariant in what it consumes and covariant in what it
//! delivers: it stands where `Stack(B′, C′)` is expected when `B′ ⊑ B` and `C ⊑
//! C′`. Witnesses:
//! `conversion::tests::returner_rows_are_covariant_but_signature_types_are_invariant`,
//! `conversion::tests::stack_is_contravariant_in_b_covariant_in_c_positive` and
//! `conversion::tests::stack_variance_negative`.

use alloc::collections::BTreeSet;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_core_term::CompTypeId;
use gandr_core_term::ComputationId;
use gandr_core_term::Sort;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::hole::Knowledge;
use gandr_kernel_strata::Level;
use gandr_kernel_term::GroundSort;

use crate::code::Lift;
use crate::context::CheckingContext;
use crate::refusal::CheckRefusal;
use crate::refusal::CoreNode;
use crate::refusal::Mismatch;
use crate::refusal::TermNode;
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
    /// - requires: nothing.
    /// - ensures: one more crossing below the ceiling; the ceiling otherwise.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — ordinary two-bridge checking and a tally one below
    ///   the ceiling followed by success and refusal separate lost increments,
    ///   wrapping and refusal paths that stop counting.
    /// - witness: `judgement::tests::a_two_bridge_check_crosses_the_boundary_twice`
    /// - witness: `conversion::tests::crossing_counts_saturate_on_success_and_refusal`
    #[spec(ensures: |ret| ret.0 == self.0.saturating_add(1))]
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

/// A pair of nodes of one family, to be compared.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Pairing
{
    /// Two value types.
    Values(ValueTypeId, ValueTypeId),
    /// Directional structural record inclusion; other types remain invariant.
    Assignable(ValueTypeId, ValueTypeId),
    /// Two computation types.
    Comps(CompTypeId, CompTypeId),
    /// Two codes, each read at its head.
    Codes(ValueId, ValueId),
    /// Invariant term-valued indices, with the kernel's structural equality.
    Terms(ValueId, ValueId),
    /// A value type used where the second type is permitted.
    SubValues(ValueTypeId, ValueTypeId),
    /// A computation type used where the second row is permitted.
    SubComps(CompTypeId, CompTypeId),
}

/// The decision's verdict on a pair.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Agreement
{
    /// The two types are the same tree at their weak heads.
    Convertible,
    /// The two types differ at some node.
    Apart,
}

/// Cross the value bridge: the type `at` synthesised against the type it is
/// checked against.
///
/// # Specification
/// - requires: both types are formed, in the context's arena.
/// - ensures: when both types are universes at their weak heads, success
///   exactly when they share a sort and the synthesised level lies at or below
///   the expected one, below only in the value sort, which records a [`Lift`]
///   at `at` from the synthesised level to the expected one; otherwise success
///   exactly when [`convert`] answers convertible. `tally` advances once on
///   every outcome, saturating at its ceiling.
/// - provides: the only comparison of value types the judgement makes, and the
///   only place a code moves up a universe.
/// - fails: [`CheckRefusal::SortMismatch`] for two universes of different
///   sorts; [`CheckRefusal::LevelMismatch`] for a level above the expected one,
///   or below it in the computation sort; [`CheckRefusal::TypeMismatch`] with
///   [`Mismatch::Value`] naming `at` and both types when they differ otherwise;
///   the unfolding's refusal when a decode does not unfold.
/// - panics: none.
/// - intension: one crossing per call, counted in `tally`.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Judgement
/// - expected: `expected`
///
/// # Adequacy
/// - hypothesis: L3 — the decision is [`convert`]'s; this bridge's own surface
///   is the smallness rule, the refusal it builds and the count, separated by
///   an agreeing and a differing pair, a value code checked at its own level,
///   one level up and one level down, a computation code one level up, and a
///   code of the other sort, each answer and count asserted.
/// - witness: `conversion::tests::the_value_bridge_lifts_a_small_value_code_and_nothing_else`
/// - witness: `judgement::tests::a_mismatched_literal_is_refused_with_both_types`
/// - witness: `judgement::tests::a_two_bridge_check_crosses_the_boundary_twice`
/// - witness: `judgement::tests::a_value_type_in_a_computation_universe_is_a_sort_mismatch`
#[spec(
    captures: before = tally.0,
    ensures: |ret| tally.0 == before.saturating_add(1)
        && match ret {
            | Err(CheckRefusal::TypeMismatch(Mismatch::Value { at: named, synthesised: found, expected: wanted })) => named == at && found == synthesised && wanted == expected,
            | Err(CheckRefusal::SortMismatch { at: named, .. } | CheckRefusal::LevelMismatch { at: named, .. }) => named == at,
            | _ => true,
        }
        && if let (Ok(ValueTypeView::Universe { sort: found_sort, level: found }), Ok(ValueTypeView::Universe { sort: wanted_sort, level: wanted })) =
            (value_type_view(context.arena(), synthesised), value_type_view(context.arena(), expected)) {
            let lifts = found_sort == GroundSort::Value && bool::from(found.lt(wanted));
            ret.is_ok() == (found_sort == wanted_sort && (found == wanted || lifts))
                && (ret.is_err() || !lifts || context.lifts().get(&at).is_some_and(|lift| lift.natural() == found && lift.target() == wanted))
        } else {
            true
        },
)]
pub fn value_bridge(
    context: &mut CheckingContext<'_>,
    at: ValueId,
    synthesised: ValueTypeId,
    expected: ValueTypeId,
    tally: &mut ConversionCount,
) -> Result<(), CheckRefusal>
{
    *tally = tally.crossed();
    let found = context.whnf_value_type(synthesised)?;
    let wanted = context.whnf_value_type(expected)?;
    if let (
        ValueTypeView::Universe {
            sort: found_sort,
            level: found_level,
        },
        ValueTypeView::Universe {
            sort: wanted_sort,
            level: wanted_level,
        },
    ) = (
        value_type_view(context.arena(), found)?,
        value_type_view(context.arena(), wanted)?,
    ) {
        let (found_level, wanted_level) = (found_level.clone(), wanted_level.clone());
        if found_sort != wanted_sort {
            return Err(CheckRefusal::SortMismatch {
                at,
                synthesised: found,
                expected: wanted,
            });
        }
        if found_level == wanted_level {
            return Ok(());
        }
        if found_sort == GroundSort::Value && bool::from(found_level.lt(&wanted_level)) {
            context.record_lift(at, Lift::new(found_level, wanted_level));
            return Ok(());
        }
        return Err(CheckRefusal::LevelMismatch {
            at,
            synthesised: found,
            expected: wanted,
        });
    }
    match convert(context, Pairing::Assignable(found, wanted))? {
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
/// - requires: both types are formed, in the context's arena.
/// - ensures: success exactly when [`convert`] answers convertible; `tally`
///   advances once on every outcome, saturating at its ceiling.
/// - provides: the only comparison of computation types the judgement makes.
/// - fails: [`CheckRefusal::TypeMismatch`] with [`Mismatch::Computation`]
///   naming `at` and both types when they differ; the unfolding's refusal when
///   a decode does not unfold.
/// - panics: none.
/// - intension: one crossing per call, counted in `tally`.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Judgement
/// - expected: `expected`
///
/// # Adequacy
/// - hypothesis: L3 — as for [`value_bridge`], over computation types, which
///   have no smallness rule.
/// - witness: `judgement::tests::a_mismatched_application_is_refused_at_the_computation_bridge`
/// - witness: `judgement::tests::a_two_bridge_check_crosses_the_boundary_twice`
#[spec(
    captures: before = tally.0,
    ensures: |ret| tally.0 == before.saturating_add(1)
        && (synthesised != expected || ret == Ok(()))
        && match ret {
            | Err(CheckRefusal::TypeMismatch(Mismatch::Computation { at: named, synthesised: found, expected: wanted })) => named == at && found == synthesised && wanted == expected,
            | _ => true,
        },
)]
pub fn comp_bridge(
    context: &mut CheckingContext<'_>,
    at: ComputationId,
    synthesised: CompTypeId,
    expected: CompTypeId,
    tally: &mut ConversionCount,
) -> Result<(), CheckRefusal>
{
    *tally = tally.crossed();
    match convert(context, Pairing::SubComps(synthesised, expected))? {
        | Agreement::Convertible => Ok(()),
        | Agreement::Apart => Err(CheckRefusal::TypeMismatch(Mismatch::Computation {
            at,
            synthesised,
            expected,
        })),
    }
}

/// Cross the decode bridge: the type the code of a decode synthesised against
/// the universe of `sort` at `target` the decode names.
///
/// # Specification
/// - requires: `synthesised` is formed, in the context's arena.
/// - ensures: success exactly when `synthesised` is, at its weak head, the
///   universe of `sort` at exactly `target`, or the unknown type, which is
///   consistent with every universe; `tally` advances once on every outcome,
///   saturating at its ceiling.
/// - provides: formation's one comparison: a decode is formed at its own level,
///   with no smallness, so a classifier is read off its type.
/// - fails: [`CheckRefusal::SortMismatch`] for a universe of the other sort;
///   [`CheckRefusal::LevelMismatch`] for one at another level;
///   [`CheckRefusal::TypeMismatch`] with [`Mismatch::Value`] when `code`
///   synthesised no universe; each names the universe the decode expected,
///   minted.
/// - panics: none.
/// - intension: one crossing per call, counted in `tally`.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — separated by a code of the decode's universe, one of the
///   other sort, one a level up, and a value that is no code.
/// - witness: `judgement::tests::a_value_type_in_a_computation_universe_is_a_sort_mismatch`
/// - witness: `formation::tests::every_value_type_constructor_has_a_formation_rule`
/// - witness: `formation::tests::every_comp_type_constructor_has_a_formation_rule`
/// - witness: `context::tests::a_value_typed_hypothesis_does_not_become_a_type_variable`
#[spec(
    captures: before = tally.0,
    ensures: |ret| tally.0 == before.saturating_add(1)
        && match value_type_view(context.arena(), synthesised) {
            | Ok(ValueTypeView::Universe { sort: found, level }) => ret.is_ok() == (found == sort && level == target),
            | _ => true,
        }
        && match ret {
            | Err(CheckRefusal::TypeMismatch(Mismatch::Value { at, expected, .. })
                | CheckRefusal::SortMismatch { at, expected, .. }
                | CheckRefusal::LevelMismatch { at, expected, .. }) => at == code
                    && matches!(value_type_view(context.arena(), expected), Ok(ValueTypeView::Universe { sort: found, level }) if found == sort && level == target),
            | _ => true,
        },
)]
pub fn decode_bridge(
    context: &mut CheckingContext<'_>,
    code: ValueId,
    synthesised: ValueTypeId,
    sort: GroundSort,
    target: &Level,
    tally: &mut ConversionCount,
) -> Result<(), CheckRefusal>
{
    *tally = tally.crossed();
    let found = context.whnf_value_type(synthesised)?;
    let expected = context
        .arena_mut()
        .value_type_universe(Sort::Ground(sort), target.clone());
    match value_type_view(context.arena(), found)? {
        | ValueTypeView::Universe {
            sort: found_sort,
            level,
        } => {
            if found_sort != sort {
                Err(CheckRefusal::SortMismatch {
                    at: code,
                    synthesised: found,
                    expected,
                })
            }
            else if level != target {
                Err(CheckRefusal::LevelMismatch {
                    at: code,
                    synthesised: found,
                    expected,
                })
            }
            else {
                Ok(())
            }
        },
        | ValueTypeView::Unknown => Ok(()),
        | ValueTypeView::PathUniverse(..)
        | ValueTypeView::Data { .. }
        | ValueTypeView::Record(_)
        | ValueTypeView::Sum(..)
        | ValueTypeView::List(_)
        | ValueTypeView::Stack { .. }
        | ValueTypeView::Integer
        | ValueTypeView::String
        | ValueTypeView::Unit
        | ValueTypeView::Thunk(_)
        | ValueTypeView::Lift { .. }
        | ValueTypeView::Element { .. }
        | ValueTypeView::Product(..)
        | ValueTypeView::StaticPi { .. } => Err(CheckRefusal::TypeMismatch(Mismatch::Value {
            at: code,
            synthesised: found,
            expected,
        })),
    }
}

/// Decide whether the two types of `root` are the same tree at their weak
/// heads.
///
/// # Specification
/// - requires: nothing — the bridges pass formed types, and anything else is
///   refused where the walk meets it.
/// - ensures: [`Agreement::Convertible`] exactly when, reading each side at its
///   weak head at every position the walk reaches, either side is the unknown
///   type, or both sides have the same former, universes and lifts the same
///   sort and level, and rigid decodes the same level and the same code: two
///   codes agree when, each reduced at its head, either is a hole or a mark, or
///   they are the same variable or constant, quotes of agreeing types, static
///   applications of agreeing heads to agreeing arguments, or static lambdas
///   over agreeing bodies; two data indices agree when either root is a hole or
///   a mark or they are equal as syntax; [`Agreement::Apart`] at the first
///   position they differ.
/// - fails: the refusal a view gives for a node outside the fragment or a
///   dangling id, and the unfolding's refusal when a decode or a code does not
///   reduce.
/// - panics: none.
/// - intension: a pair of equal ids is accepted without reading the node, and a
///   pair already met is not compared again; a worklist, so no depth overflows
///   a stack.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surfaces are the id fast path, the weak
///   head, the per-former comparison and the child pairing, separated by one id
///   against itself, two structurally equal trees at distinct ids, trees
///   differing at the root and beneath a thunk in either order, universes and
///   lifts differing only in level, two rigid decodes of different variables, a
///   decode of a defined code against its body beneath a former, static
///   instances rigid and defined, static lambdas alike and unlike, and a
///   dangling id; the fast path is pinned against the structural decision by
///   property.
/// - witness: `conversion::tests::one_id_converts_without_being_read`
/// - witness: `conversion::tests::equal_trees_at_distinct_ids_convert`
/// - witness: `conversion::tests::differing_trees_are_apart_in_either_order`
/// - witness: `conversion::tests::a_decode_of_a_defined_code_converts_with_its_body`
/// - witness: `conversion::tests::static_codes_compare_by_head_argument_and_body`
/// - witness: `conversion::tests::a_dangling_type_is_refused`
/// - witness: `conversion::tests::the_id_fast_path_agrees_with_the_structural_decision`
/// - witness: `conversion::tests::the_unknown_type_is_consistent_beside_a_differing_former`
#[spec(ensures: |ret| match root {
    | Pairing::Values(left, right) | Pairing::Assignable(left, right) | Pairing::SubValues(left, right) if left == right => ret == Ok(Agreement::Convertible),
    | Pairing::Comps(left, right) | Pairing::SubComps(left, right) if left == right => ret == Ok(Agreement::Convertible),
    | Pairing::Codes(left, right) | Pairing::Terms(left,right) if left == right => ret == Ok(Agreement::Convertible),
    | Pairing::Values(..) | Pairing::Assignable(..) | Pairing::SubValues(..) | Pairing::Comps(..) | Pairing::SubComps(..) | Pairing::Codes(..) | Pairing::Terms(..) => true,
})]
fn convert(
    context: &mut CheckingContext<'_>,
    root: Pairing,
) -> Result<Agreement, CheckRefusal>
{
    let mut pending = Vec::from([root]);
    let mut met = BTreeSet::new();
    while let Some(pairing) = pending.pop() {
        let reflexive = match pairing {
            | Pairing::Values(left, right)
            | Pairing::Assignable(left, right)
            | Pairing::SubValues(left, right) => left == right,
            | Pairing::Comps(left, right) | Pairing::SubComps(left, right) => left == right,
            | Pairing::Codes(left, right) | Pairing::Terms(left, right) => left == right,
        };
        if reflexive || !met.insert(pairing) {
            continue;
        }
        let subtyping = matches!(pairing, Pairing::SubValues(..) | Pairing::SubComps(..));
        let values = |a, b| {
            if subtyping {
                Pairing::SubValues(a, b)
            }
            else {
                Pairing::Values(a, b)
            }
        };
        let comps = |a, b| {
            if subtyping {
                Pairing::SubComps(a, b)
            }
            else {
                Pairing::Comps(a, b)
            }
        };
        let agrees = match pairing {
            | Pairing::Terms(left, right) => {
                root_knowledge(context, left)? == Knowledge::Unknown
                    || root_knowledge(context, right)? == Knowledge::Unknown
                    || gandr_core_term::equal_certificate_syntax(context.arena(), left, right)
                        == gandr_core_term::CertificateEquality::Equal
            },
            | Pairing::Assignable(left, right) => {
                let left = context.whnf_value_type(left)?;
                let right = context.whnf_value_type(right)?;
                match (
                    value_type_view(context.arena(), left)?,
                    value_type_view(context.arena(), right)?,
                ) {
                    | (ValueTypeView::Record(found), ValueTypeView::Record(wanted)) => {
                        for (label, &expected) in wanted {
                            let Some(&synthesised) = found.get(label)
                            else {
                                return Ok(Agreement::Apart);
                            };
                            pending.push(Pairing::Assignable(synthesised, expected));
                        }
                    },
                    | _ => pending.push(Pairing::SubValues(left, right)),
                }
                true
            },
            | Pairing::Values(left, right) | Pairing::SubValues(left, right) => {
                let left = context.whnf_value_type(left)?;
                let right = context.whnf_value_type(right)?;
                match (
                    value_type_view(context.arena(), left)?,
                    value_type_view(context.arena(), right)?,
                ) {
                    | (
                        ValueTypeView::Data {
                            declaration: a,
                            arguments: aa,
                        },
                        ValueTypeView::Data {
                            declaration: b,
                            arguments: right_arguments,
                        },
                    ) => {
                        if a != b || aa.len() != right_arguments.len() {
                            return Ok(Agreement::Apart);
                        }
                        pending.extend(
                            aa.iter()
                                .zip(right_arguments)
                                .map(|(&a, &b)| Pairing::Terms(a, b)),
                        );
                        true
                    },
                    | (ValueTypeView::Record(a), ValueTypeView::Record(b)) => {
                        if a.len() != b.len() || !a.keys().eq(b.keys()) {
                            return Ok(Agreement::Apart);
                        }
                        pending.extend(a.values().zip(b.values()).map(|(&a, &b)| values(a, b)));
                        true
                    },
                    | (
                        ValueTypeView::Stack {
                            input: a,
                            output: b,
                        },
                        ValueTypeView::Stack {
                            input: c,
                            output: d,
                        },
                    ) => {
                        pending.extend([comps(c, a), comps(b, d)]);
                        true
                    },
                    | (ValueTypeView::PathUniverse(a, b), ValueTypeView::PathUniverse(c, d)) => {
                        pending.push(Pairing::Codes(a, c));
                        pending.push(Pairing::Codes(b, d));
                        true
                    },
                    | (ValueTypeView::List(left), ValueTypeView::List(right)) => {
                        pending.push(values(left, right));
                        true
                    },
                    | (ValueTypeView::Unknown, _)
                    | (_, ValueTypeView::Unknown)
                    | (ValueTypeView::Integer, ValueTypeView::Integer)
                    | (ValueTypeView::String, ValueTypeView::String)
                    | (ValueTypeView::Unit, ValueTypeView::Unit) => true,
                    | (ValueTypeView::Thunk(left), ValueTypeView::Thunk(right)) => {
                        pending.push(comps(left, right));
                        true
                    },
                    | (
                        ValueTypeView::Universe {
                            sort: left_sort,
                            level: left_level,
                        },
                        ValueTypeView::Universe {
                            sort: right_sort,
                            level: right_level,
                        },
                    ) => left_sort == right_sort && left_level == right_level,
                    | (
                        ValueTypeView::Lift {
                            inner: left_inner,
                            target: left_target,
                        },
                        ValueTypeView::Lift {
                            inner: right_inner,
                            target: right_target,
                        },
                    ) => {
                        pending.push(values(left_inner, right_inner));
                        left_target == right_target
                    },
                    | (
                        ValueTypeView::Element {
                            code: left_code,
                            target: left_target,
                        },
                        ValueTypeView::Element {
                            code: right_code,
                            target: right_target,
                        },
                    ) => {
                        pending.push(Pairing::Codes(left_code, right_code));
                        left_target == right_target
                    },
                    | (ValueTypeView::Sum(left), ValueTypeView::Sum(right))
                    | (ValueTypeView::Product(left), ValueTypeView::Product(right)) => {
                        let same = left.len() == right.len();
                        if same {
                            pending.extend(
                                left.iter()
                                    .zip(right)
                                    .rev()
                                    .map(|(&left, &right)| values(left, right)),
                            );
                        }
                        same
                    },
                    | (
                        ValueTypeView::StaticPi {
                            domain: left_first,
                            codomain: left_second,
                        },
                        ValueTypeView::StaticPi {
                            domain: right_first,
                            codomain: right_second,
                        },
                    ) => {
                        pending.push(values(left_second, right_second));
                        pending.push(values(right_first, left_first));
                        true
                    },
                    | (
                        ValueTypeView::PathUniverse(..)
                        | ValueTypeView::Data { .. }
                        | ValueTypeView::Record(_)
                        | ValueTypeView::Sum(..)
                        | ValueTypeView::List(_)
                        | ValueTypeView::Stack { .. }
                        | ValueTypeView::Integer
                        | ValueTypeView::String
                        | ValueTypeView::Unit
                        | ValueTypeView::Thunk(_)
                        | ValueTypeView::Universe { .. }
                        | ValueTypeView::Lift { .. }
                        | ValueTypeView::Element { .. }
                        | ValueTypeView::Product(..)
                        | ValueTypeView::StaticPi { .. },
                        _,
                    ) => false,
                }
            },
            | Pairing::Comps(left, right) | Pairing::SubComps(left, right) => {
                let left = context.whnf_comp_type(left)?;
                let right = context.whnf_comp_type(right)?;
                match (
                    comp_type_view(context.arena(), left)?,
                    comp_type_view(context.arena(), right)?,
                ) {
                    | (CompTypeView::Unknown, _) | (_, CompTypeView::Unknown) => true,
                    | (CompTypeView::With(a, b), CompTypeView::With(c, d)) => {
                        pending.extend([comps(a, c), comps(b, d)]);
                        true
                    },
                    | (
                        CompTypeView::Returner {
                            result: left,
                            effects: first,
                        },
                        CompTypeView::Returner {
                            result: right,
                            effects: second,
                        },
                    ) => {
                        let mut same_shape =
                            subtyping || first.signatures().len() == second.signatures().len();
                        let mut candidates = second.signatures().peekable();
                        for signature in first.signatures() {
                            while candidates
                                .peek()
                                .is_some_and(|candidate| candidate.name() < signature.name())
                            {
                                candidates.next();
                            }
                            let Some(candidate) = candidates
                                .next()
                                .filter(|candidate| candidate.name() == signature.name())
                            else {
                                same_shape = false;
                                break;
                            };
                            if signature.operations().len() != candidate.operations().len() {
                                same_shape = false;
                                break;
                            }
                            for (a, b) in signature.operations().zip(candidate.operations()) {
                                if a.name != b.name {
                                    same_shape = false;
                                    break;
                                }
                                pending.push(Pairing::Values(a.payload, b.payload));
                                pending.push(Pairing::Values(a.reply, b.reply));
                            }
                            if !same_shape {
                                break;
                            }
                        }
                        if same_shape {
                            pending.push(values(left, right));
                        }
                        same_shape
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
                    )
                    | (
                        CompTypeView::Pi {
                            domain: left_domain,
                            codomain: left_codomain,
                        },
                        CompTypeView::Pi {
                            domain: right_domain,
                            codomain: right_codomain,
                        },
                    ) => {
                        pending.push(comps(left_codomain, right_codomain));
                        pending.push(values(right_domain, left_domain));
                        true
                    },
                    | (
                        CompTypeView::Element {
                            code: left_code,
                            target: left_target,
                        },
                        CompTypeView::Element {
                            code: right_code,
                            target: right_target,
                        },
                    ) => {
                        pending.push(Pairing::Codes(left_code, right_code));
                        left_target == right_target
                    },
                    | (
                        CompTypeView::Returner { .. }
                        | CompTypeView::With(..)
                        | CompTypeView::Arrow { .. }
                        | CompTypeView::Pi { .. }
                        | CompTypeView::Element { .. },
                        _,
                    ) => false,
                }
            },
            | Pairing::Codes(left, right) => {
                let left = context.whnf_code(left)?;
                let right = context.whnf_code(right)?;
                left == right
                    || root_knowledge(context, left)? == Knowledge::Unknown
                    || root_knowledge(context, right)? == Knowledge::Unknown
                    || {
                        let read = |code: ValueId| {
                            context
                                .arena()
                                .value(code)
                                .ok_or(CheckRefusal::DanglingNode {
                                    node: CoreNode::Term(TermNode::Value(code)),
                                })
                        };
                        {
                            let (matched_left_value, matched_right_value) =
                                (read(left)?, read(right)?);
                            if let Value::Literal(ref a) = *matched_left_value
                                && let Value::Literal(ref b) = *matched_right_value
                            {
                                a == b
                            }
                            else if let Value::Tuple(ref a) = *matched_left_value
                                && let Value::Tuple(ref b) = *matched_right_value
                            {
                                a.len() == b.len() && {
                                    pending.extend(
                                        a.iter()
                                            .zip(b.iter())
                                            .map(|(&left, &right)| Pairing::Codes(left, right)),
                                    );
                                    true
                                }
                            }
                            else if let Value::Injection(ref a, ref av) = *matched_left_value
                                && let Value::Injection(ref b, ref bv) = *matched_right_value
                            {
                                {
                                    pending.push(Pairing::Codes(*av, *bv));
                                    a == b
                                }
                            }
                            else if let Value::Constructor {
                                datatype: ref a,
                                tag: ref at,
                                fields: ref af,
                            } = *matched_left_value
                                && let Value::Constructor {
                                    datatype: ref b,
                                    tag: ref bt,
                                    fields: ref bf,
                                } = *matched_right_value
                            {
                                {
                                    if at != bt || af.len() != bf.len() {
                                        return Ok(Agreement::Apart);
                                    }
                                    pending.push(Pairing::Values(*a, *b));
                                    pending.extend(
                                        af.iter().zip(bf).map(|(&a, &b)| Pairing::Codes(a, b)),
                                    );
                                    true
                                }
                            }
                            else if let Value::Record(ref a) = *matched_left_value
                                && let Value::Record(ref b) = *matched_right_value
                            {
                                {
                                    if a.len() != b.len() || !a.keys().eq(b.keys()) {
                                        return Ok(Agreement::Apart);
                                    }
                                    pending.extend(
                                        a.values()
                                            .zip(b.values())
                                            .map(|(&a, &b)| Pairing::Codes(a, b)),
                                    );
                                    true
                                }
                            }
                            else if let Value::Variable {
                                zone: ref left_zone,
                                index: ref left_index,
                            } = *matched_left_value
                                && let Value::Variable {
                                    zone: ref right_zone,
                                    index: ref right_index,
                                } = *matched_right_value
                            {
                                left_zone == right_zone && left_index == right_index
                            }
                            else if let Value::Constant(ref left_constant) = *matched_left_value
                                && let Value::Constant(ref right_constant) = *matched_right_value
                            {
                                left_constant == right_constant
                            }
                            else if let Value::Quote(ref left_quoted) = *matched_left_value
                                && let Value::Quote(ref right_quoted) = *matched_right_value
                            {
                                {
                                    pending.push(Pairing::Values(*left_quoted, *right_quoted));
                                    true
                                }
                            }
                            else if let Value::QuoteComputation(ref left_quoted) =
                                *matched_left_value
                                && let Value::QuoteComputation(ref right_quoted) =
                                    *matched_right_value
                            {
                                {
                                    pending.push(Pairing::Comps(*left_quoted, *right_quoted));
                                    true
                                }
                            }
                            else if let Value::StaticApplication(ref left_head, ref left_argument) =
                                *matched_left_value
                                && let Value::StaticApplication(ref right_head, ref right_argument) =
                                    *matched_right_value
                            {
                                {
                                    pending.push(Pairing::Codes(*left_argument, *right_argument));
                                    pending.push(Pairing::Codes(*left_head, *right_head));
                                    true
                                }
                            }
                            else if let Value::StaticLambda(ref left_body) = *matched_left_value
                                && let Value::StaticLambda(ref right_body) = *matched_right_value
                            {
                                {
                                    pending.push(Pairing::Codes(*left_body, *right_body));
                                    true
                                }
                            }
                            else {
                                {
                                    match *matched_left_value {
                                        | Value::PathRefl(_)
                                        | Value::Constructor { .. }
                                        | Value::Record(_)
                                        | Value::Primitive { .. }
                                        | Value::PathProduct(..)
                                        | Value::PathEquiv { .. }
                                        | Value::Variable { .. }
                                        | Value::Constant(_)
                                        | Value::Tuple(_)
                                        | Value::Literal(_)
                                        | Value::Injection(..)
                                        | Value::Thunk(_)
                                        | Value::Lift { .. }
                                        | Value::Quote(_)
                                        | Value::QuoteComputation(_)
                                        | Value::StaticApplication(..)
                                        | Value::StaticLambda(_)
                                        | Value::Reify(_)
                                        | Value::ListNil
                                        | Value::ListCons(..)
                                        | Value::Hole(_)
                                        | Value::Mark { .. } => false,
                                    }
                                }
                            }
                        }
                    }
            },
        };
        if !agrees {
            return Ok(Agreement::Apart);
        }
    }
    Ok(Agreement::Convertible)
}

/// What the code or index `node` reads as at its root: unknown when it is a
/// hole or a mark.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`Knowledge::Unknown`] exactly when `node` is a hole or a mark,
///   [`Knowledge::Known`] for every other node.
/// - fails: [`CheckRefusal::DanglingNode`] for an id the arena does not hold.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — separated by a hole, a mark and a variable as a code.
/// - witness: `conversion::tests::the_unknown_type_is_consistent_beside_a_differing_former`
#[spec(ensures: |ret| match ret {
    | Ok(found) => (found == Knowledge::Unknown) == matches!(context.arena().value(node), Some(Value::Hole(_) | Value::Mark { .. })),
    | Err(_) => context.arena().value(node).is_none(),
})]
fn root_knowledge(
    context: &CheckingContext<'_>,
    node: ValueId,
) -> Result<Knowledge, CheckRefusal>
{
    let held = context
        .arena()
        .value(node)
        .ok_or(CheckRefusal::DanglingNode {
            node: CoreNode::Term(TermNode::Value(node)),
        })?;
    if matches!(*held, Value::Hole(_) | Value::Mark { .. }) {
        Ok(Knowledge::Unknown)
    }
    else {
        Ok(Knowledge::Known)
    }
}

#[cfg(test)]
mod tests
{
    use gandr_core_term::CompTypeId;
    use gandr_core_term::CoreArena;
    use gandr_core_term::Sort;
    use gandr_core_term::Zone;
    use gandr_kernel_strata::Level;
    use gandr_kernel_strata::LevelConstant;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::GroundSort;
    use proptest::prelude::ProptestConfig;
    use proptest::prelude::prop_assert_eq;
    use proptest::prelude::proptest;

    use super::Agreement;
    use super::ConversionCount;
    use super::Pairing;
    use super::convert;
    use super::value_bridge;
    use crate::code::Lift;
    use crate::context::CheckBudget;
    use crate::context::CheckingContext;
    use crate::fixture::TypeRecipe;
    use crate::fixture::dangling_value_type;
    use crate::fixture::seed;
    use crate::fixture::type_recipe;
    use crate::refusal::CheckRefusal;
    use crate::refusal::CoreNode;
    use crate::refusal::TypeNode;

    #[test]
    fn one_id_converts_without_being_read()
    {
        let mut arena = CoreArena::new();
        let unit = arena.value_type_unit();
        let dangling = dangling_value_type();
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        assert_eq!(
            convert(&mut context, Pairing::Values(dangling, dangling)),
            Ok(Agreement::Convertible),
            "one id is one node, so the pair is accepted without its node being read"
        );
        assert_eq!(
            convert(&mut context, Pairing::Values(unit, dangling)),
            Err(CheckRefusal::DanglingNode {
                node: CoreNode::Type(TypeNode::Value(dangling)),
            }),
            "two ids are read, so the id the arena does not hold is met and refused"
        );
    }

    #[test]
    fn equal_trees_at_distinct_ids_convert()
    {
        let mut arena = CoreArena::new();
        let build = |arena: &mut CoreArena| {
            let integer = arena.value_type_base(BaseType::Integer);
            let universe =
                arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
            let result = arena.comp_type_returner(integer);
            let pi = arena.comp_type_pi(universe, result);
            arena.value_type_thunk(pi)
        };
        let left = build(&mut arena);
        let right = build(&mut arena);
        assert_ne!(left, right, "the two trees sit at distinct ids");
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        assert_eq!(
            convert(&mut context, Pairing::Values(left, right)),
            Ok(Agreement::Convertible),
            "conversion compares trees, not ids"
        );
    }

    #[test]
    fn returner_rows_are_covariant_but_signature_types_are_invariant()
    {
        use gandr_core_term::effect::EffectName;
        use gandr_core_term::effect::EffectOp;
        use gandr_core_term::effect::EffectRow;
        use gandr_core_term::effect::EffectSig;
        use gandr_core_term::effect::OperationName;
        let mut arena = CoreArena::new();
        let unit = arena.value_type_unit();
        let pure = arena.comp_type_returner(unit);
        let signature = |name: &str, reply| {
            EffectRow::singleton(
                EffectSig::new(EffectName::from(name), alloc::vec![EffectOp {
                    name: OperationName::from("get"),
                    payload: unit,
                    reply
                }])
                .unwrap(),
            )
        };
        let effectful = arena.comp_type_returner_with_effects(unit, signature("IO", unit));
        let pure_thunk = arena.value_type_thunk(pure);
        let effectful_thunk = arena.value_type_thunk(effectful);
        let first = arena.comp_type_returner_with_effects(unit, signature("State", pure_thunk));
        let second =
            arena.comp_type_returner_with_effects(unit, signature("State", effectful_thunk));
        let accepts_effectful = arena.comp_type_arrow(effectful_thunk, pure);
        let accepts_pure = arena.comp_type_arrow(pure_thunk, pure);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        assert_eq!(
            convert(&mut context, Pairing::SubComps(pure, effectful)),
            Ok(Agreement::Convertible)
        );
        assert_eq!(
            convert(&mut context, Pairing::SubComps(effectful, pure)),
            Ok(Agreement::Apart)
        );
        assert_eq!(
            convert(&mut context, Pairing::Comps(pure, effectful)),
            Ok(Agreement::Apart)
        );
        assert_eq!(
            convert(
                &mut context,
                Pairing::SubValues(pure_thunk, effectful_thunk)
            ),
            Ok(Agreement::Convertible)
        );
        assert_eq!(
            convert(
                &mut context,
                Pairing::SubComps(accepts_effectful, accepts_pure)
            ),
            Ok(Agreement::Convertible)
        );
        assert_eq!(
            convert(
                &mut context,
                Pairing::SubComps(accepts_pure, accepts_effectful)
            ),
            Ok(Agreement::Apart)
        );
        assert_eq!(
            convert(&mut context, Pairing::SubComps(first, second)),
            Ok(Agreement::Apart)
        );
        assert_eq!(
            convert(&mut context, Pairing::SubComps(second, first)),
            Ok(Agreement::Apart)
        );
    }

    /// A pure returner and an effectful one over the same result, the pure one
    /// below the effectful one.
    ///
    /// # Specification
    /// trivial.
    fn pure_below_effectful() -> (CoreArena, CompTypeId, CompTypeId)
    {
        use gandr_core_term::effect::EffectName;
        use gandr_core_term::effect::EffectOp;
        use gandr_core_term::effect::EffectRow;
        use gandr_core_term::effect::EffectSig;
        use gandr_core_term::effect::OperationName;
        let mut arena = CoreArena::new();
        let unit = arena.value_type_unit();
        let pure = arena.comp_type_returner(unit);
        let row = EffectRow::singleton(
            EffectSig::new(EffectName::from("IO"), alloc::vec![EffectOp {
                name: OperationName::from("get"),
                payload: unit,
                reply: unit
            }])
            .unwrap(),
        );
        let effectful = arena.comp_type_returner_with_effects(unit, row);
        (arena, pure, effectful)
    }

    /// `Stack(B, C) ⊑ Stack(B′, C′)` when `B′ ⊑ B` and `C ⊑ C′`: a stack that
    /// accepts the effectful input and delivers the pure output stands where
    /// one accepting the pure input and delivering the effectful output is
    /// expected.
    #[test]
    fn stack_is_contravariant_in_b_covariant_in_c_positive()
    {
        let (mut arena, pure, effectful) = pure_below_effectful();
        let narrow = arena.value_type_stack(effectful, pure);
        let wide = arena.value_type_stack(pure, effectful);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        assert_eq!(
            convert(&mut context, Pairing::SubValues(narrow, wide)),
            Ok(Agreement::Convertible)
        );
    }

    /// Widening a stack's input or narrowing its output breaks the subsumption,
    /// and so does the converse of a valid widening.
    #[test]
    fn stack_variance_negative()
    {
        let (mut arena, pure, effectful) = pure_below_effectful();
        let narrow = arena.value_type_stack(effectful, pure);
        let wide = arena.value_type_stack(pure, effectful);
        let pure_to_pure = arena.value_type_stack(pure, pure);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        for (sub, sup) in [(wide, narrow), (pure_to_pure, narrow), (wide, pure_to_pure)] {
            assert_eq!(
                convert(&mut context, Pairing::SubValues(sub, sup)),
                Ok(Agreement::Apart)
            );
        }
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
        let pi = arena.comp_type_pi(unit, returns_integer);
        let one = Level::constant(LevelConstant::from(1_u64));
        let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
        let large = arena.value_type_universe(Sort::Ground(GroundSort::Value), one.clone());
        let negative =
            arena.value_type_universe(Sort::Ground(GroundSort::Computation), Level::zero());
        let lifted_once = arena.value_type_lift(integer, one);
        let lifted_twice =
            arena.value_type_lift(integer, Level::constant(LevelConstant::from(2_u64)));
        let inner = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let outer = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
        let decode_inner = arena.value_type_element(inner, Level::zero());
        let decode_outer = arena.value_type_element(outer, Level::zero());
        let pairs = [
            Pairing::Values(integer, string),
            Pairing::Values(unit, thunk_integer),
            Pairing::Values(thunk_integer, thunk_string),
            Pairing::Comps(returns_integer, arrow),
            Pairing::Comps(arrow, pi),
            Pairing::Values(small, large),
            Pairing::Values(small, negative),
            Pairing::Values(lifted_once, lifted_twice),
            Pairing::Values(lifted_once, integer),
            Pairing::Values(decode_inner, decode_outer),
        ];
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        for pairing in pairs {
            let swapped = match pairing {
                | Pairing::Assignable(left, right) => Pairing::Assignable(right, left),
                | Pairing::Values(left, right) => Pairing::Values(right, left),
                | Pairing::Comps(left, right) => Pairing::Comps(right, left),
                | Pairing::Codes(left, right) => Pairing::Codes(right, left),
                | Pairing::Terms(left, right) => Pairing::Terms(right, left),
                | Pairing::SubValues(left, right) => Pairing::SubValues(right, left),
                | Pairing::SubComps(left, right) => Pairing::SubComps(right, left),
            };
            assert_eq!(
                convert(&mut context, pairing),
                Ok(Agreement::Apart),
                "{pairing:?} differ"
            );
            assert_eq!(
                convert(&mut context, swapped),
                Ok(Agreement::Apart),
                "{swapped:?} differ in the other order too"
            );
        }
    }

    #[test]
    fn the_unknown_type_is_consistent_beside_a_differing_former()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let string = arena.value_type_base(BaseType::String);
        let unknown = arena.value_type_unknown();
        let unknown_computation = arena.comp_type_unknown();
        let returns_integer = arena.comp_type_returner(integer);
        let hole = arena.value_hole(gandr_core_term::hole::HoleId::from(0_u32));
        let variable = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let marked = arena.value_mark(gandr_core_term::hole::MarkIndex::from(0_u32), variable);
        let decode_hole = arena.value_type_element(hole, Level::zero());
        let decode_variable = arena.value_type_element(variable, Level::zero());
        let decode_marked = arena.value_type_element(marked, Level::zero());
        let known_left = arena.value_type_product(&[integer, integer]);
        let unknown_left = arena.value_type_product(&[unknown, integer]);
        let unknown_left_string = arena.value_type_product(&[unknown, string]);
        let unit_code = arena.value_unit();
        let consistent = [
            Pairing::Values(unknown, integer),
            Pairing::Values(decode_hole, integer),
            Pairing::Values(decode_marked, decode_variable),
            Pairing::Values(known_left, unknown_left),
            Pairing::Comps(unknown_computation, returns_integer),
            Pairing::Codes(hole, variable),
            Pairing::Terms(hole, variable),
        ];
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        for pairing in consistent {
            let swapped = match pairing {
                | Pairing::Assignable(left, right) => Pairing::Assignable(right, left),
                | Pairing::Values(left, right) => Pairing::Values(right, left),
                | Pairing::SubValues(left, right) => Pairing::SubValues(right, left),
                | Pairing::Comps(left, right) => Pairing::Comps(right, left),
                | Pairing::SubComps(left, right) => Pairing::SubComps(right, left),
                | Pairing::Codes(left, right) => Pairing::Codes(right, left),
                | Pairing::Terms(left, right) => Pairing::Terms(right, left),
            };
            assert_eq!(
                convert(&mut context, pairing),
                Ok(Agreement::Convertible),
                "{pairing:?}"
            );
            assert_eq!(
                convert(&mut context, swapped),
                Ok(Agreement::Convertible),
                "{swapped:?}"
            );
        }
        assert_eq!(
            convert(
                &mut context,
                Pairing::Values(known_left, unknown_left_string)
            ),
            Ok(Agreement::Apart),
            "the unknown factor agrees, the differing one does not"
        );
        assert_eq!(
            convert(&mut context, Pairing::Terms(variable, unit_code)),
            Ok(Agreement::Apart),
            "an index without a hole is compared as syntax"
        );
    }

    /// `def Num : Type = Integer`: a decode of `Num` is the integer atom
    /// wherever it stands, and a decode of an undefined code is not.
    #[test]
    fn a_decode_of_a_defined_code_converts_with_its_body()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let string = arena.value_type_base(BaseType::String);
        let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
        let body = arena.value_quote(integer);
        let num = arena.value_constant(ConstantIndex::from(0_usize));
        let opaque = arena.value_constant(ConstantIndex::from(1_usize));
        let decoded = arena.value_type_element(num, Level::zero());
        let rigid = arena.value_type_element(opaque, Level::zero());
        let returns_decoded = arena.comp_type_returner(decoded);
        let returns_integer = arena.comp_type_returner(integer);
        let under_arrow = arena.comp_type_arrow(decoded, returns_decoded);
        let plain_arrow = arena.comp_type_arrow(integer, returns_integer);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        seed(&mut context, &[small, small]);
        context.define(
            ConstantIndex::from(0_usize),
            crate::formation::FormedValueType::derived(small),
            body,
        );
        assert_eq!(
            convert(&mut context, Pairing::Values(decoded, integer)),
            Ok(Agreement::Convertible),
            "the decode unfolds to the type its body quotes"
        );
        assert_eq!(
            convert(&mut context, Pairing::Comps(under_arrow, plain_arrow)),
            Ok(Agreement::Convertible),
            "and does so beneath every former the walk descends"
        );
        assert_eq!(
            convert(&mut context, Pairing::Values(decoded, string)),
            Ok(Agreement::Apart),
            "the unfolded type is compared, not assumed"
        );
        assert_eq!(
            convert(&mut context, Pairing::Values(rigid, integer)),
            Ok(Agreement::Apart),
            "a code with no body stays rigid"
        );
    }

    /// Codes compare at their reduced heads: a static instance of a defined
    /// operator by its reduct, a rigid one by head and argument, a static
    /// lambda by its body.
    #[test]
    fn static_codes_compare_by_head_argument_and_body()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let string = arena.value_type_base(BaseType::String);
        let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
        let operator_type = arena.value_type_static_pi(small, small);
        let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let decoded_bound = arena.value_type_element(bound, Level::zero());
        let squared = arena.value_type_product(&[decoded_bound, decoded_bound]);
        let squared_code = arena.value_quote(squared);
        let pair_body = arena.value_static_lambda(squared_code);
        let pair = arena.value_constant(ConstantIndex::from(0_usize));
        let integer_code = arena.value_quote(integer);
        let string_code = arena.value_quote(string);
        let instance = arena.value_static_application(pair, integer_code);
        let decoded_instance = arena.value_type_element(instance, Level::zero());
        let written = arena.value_type_product(&[integer, integer]);
        let rigid = |arena: &mut CoreArena, head: u32, argument| {
            let head = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(head));
            let applied = arena.value_static_application(head, argument);
            arena.value_type_element(applied, Level::zero())
        };
        let at_integer = rigid(&mut arena, 0, integer_code);
        let again = rigid(&mut arena, 0, integer_code);
        let at_string = rigid(&mut arena, 0, string_code);
        let other_head = rigid(&mut arena, 1, integer_code);
        let identity = arena.value_static_lambda(bound);
        let other_identity = arena.value_static_lambda(bound);
        let constant_body = arena.value_static_lambda(integer_code);
        let at_identity = rigid(&mut arena, 0, identity);
        let at_other_identity = rigid(&mut arena, 0, other_identity);
        let at_constant = rigid(&mut arena, 0, constant_body);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        seed(&mut context, &[operator_type]);
        context.define(
            ConstantIndex::from(0_usize),
            crate::formation::FormedValueType::derived(operator_type),
            pair_body,
        );
        for (pairing, agreement, message) in [
            (
                Pairing::Values(decoded_instance, written),
                Agreement::Convertible,
                "an instance of a defined operator converts with its reduct",
            ),
            (
                Pairing::Values(at_integer, again),
                Agreement::Convertible,
                "two rigid instances agree by head and argument",
            ),
            (
                Pairing::Values(at_integer, at_string),
                Agreement::Apart,
                "a different argument is apart",
            ),
            (
                Pairing::Values(at_integer, other_head),
                Agreement::Apart,
                "a different head is apart",
            ),
            (
                Pairing::Values(at_identity, at_other_identity),
                Agreement::Convertible,
                "two static lambdas over one body agree",
            ),
            (
                Pairing::Values(at_identity, at_constant),
                Agreement::Apart,
                "static lambdas over different bodies are apart",
            ),
        ] {
            assert_eq!(convert(&mut context, pairing), Ok(agreement), "{message}");
        }
    }

    #[test]
    fn the_value_bridge_lifts_a_small_value_code_and_nothing_else()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let returns_integer = arena.comp_type_returner(integer);
        let one = Level::constant(LevelConstant::from(1_u64));
        let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
        let large = arena.value_type_universe(Sort::Ground(GroundSort::Value), one.clone());
        let small_negative =
            arena.value_type_universe(Sort::Ground(GroundSort::Computation), Level::zero());
        let large_negative =
            arena.value_type_universe(Sort::Ground(GroundSort::Computation), one.clone());
        let code = arena.value_quote(integer);
        let negative_code = arena.value_quote_computation(returns_integer);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let mut tally = ConversionCount::default();
        assert_eq!(
            value_bridge(&mut context, code, small, small, &mut tally),
            Ok(()),
            "a code checks at its own universe"
        );
        assert!(context.lifts().is_empty(), "and records no lift there");
        assert_eq!(
            value_bridge(&mut context, code, small, large, &mut tally),
            Ok(()),
            "a value code checks one universe up"
        );
        assert_eq!(
            context.lifts().get(&code),
            Some(&Lift::new(Level::zero(), one)),
            "and the crossing records the lift the kernel bridge writes"
        );
        assert_eq!(
            value_bridge(&mut context, code, large, small, &mut tally),
            Err(CheckRefusal::LevelMismatch {
                at: code,
                synthesised: large,
                expected: small,
            }),
            "no code moves down a universe"
        );
        assert_eq!(
            value_bridge(
                &mut context,
                negative_code,
                small_negative,
                large_negative,
                &mut tally
            ),
            Err(CheckRefusal::LevelMismatch {
                at: negative_code,
                synthesised: small_negative,
                expected: large_negative,
            }),
            "the core has no lift of a computation type, so a computation code stays at its level"
        );
        assert_eq!(
            value_bridge(&mut context, code, small, small_negative, &mut tally),
            Err(CheckRefusal::SortMismatch {
                at: code,
                synthesised: small,
                expected: small_negative,
            }),
            "no code crosses to the other sort"
        );
        assert_eq!(
            tally,
            ConversionCount::from(5_usize),
            "every call crossed once"
        );
    }

    #[test]
    fn a_dangling_type_is_refused()
    {
        let mut arena = CoreArena::new();
        let unit = arena.value_type_unit();
        let dangling = dangling_value_type();
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        assert_eq!(
            convert(&mut context, Pairing::Values(unit, dangling)),
            Err(CheckRefusal::DanglingNode {
                node: CoreNode::Type(TypeNode::Value(dangling)),
            }),
            "an id from another arena is refused rather than read"
        );
    }

    #[test]
    fn crossing_counts_saturate_on_success_and_refusal()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let string = arena.value_type_base(BaseType::String);
        let literal = arena.value_literal(crate::fixture::integer_literal());
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let mut tally = ConversionCount::from(usize::MAX - 1);
        assert_eq!(
            value_bridge(&mut context, literal, integer, integer, &mut tally),
            Ok(())
        );
        assert_eq!(usize::from(tally), usize::MAX);
        assert_eq!(
            value_bridge(&mut context, literal, integer, string, &mut tally),
            Err(CheckRefusal::TypeMismatch(
                crate::refusal::Mismatch::Value {
                    at: literal,
                    synthesised: integer,
                    expected: string,
                }
            ))
        );
        assert_eq!(usize::from(tally), usize::MAX);
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
            let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
            prop_assert_eq!(
                convert(&mut context, Pairing::Values(first_tree, first_copy)),
                Ok(Agreement::Convertible),
                "a tree converts with its copy at fresh ids"
            );
            let verdict = convert(&mut context, Pairing::Values(first_tree, second_tree));
            prop_assert_eq!(
                convert(&mut context, Pairing::Values(second_tree, first_tree)),
                verdict,
                "the decision is symmetric"
            );
            prop_assert_eq!(
                convert(&mut context, Pairing::Values(first_copy, second_copy)),
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
