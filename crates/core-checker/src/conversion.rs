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
//! unfolding, and reads a sealed atom as its representation inside its seal —
//! and then compares former by former: a universe and a lift by their sort and
//! level exactly, a decode left rigid by its code, a variable or a constant
//! without a body, compared as a leaf, and a sealed atom outside its seal by
//! its admission position alone, so it relates to no representation and to no
//! other atom however it was implemented. Two equal ids are one node, so the
//! pair is accepted without reading it; and a pair met once is not compared
//! again, so shared subtrees cost their distinct pairs, not their expansion.
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
//! # A stage is decided by the order
//!
//! A type refined at a stage of a structural fixpoint (`A^s`) is subsumed,
//! not converted: where a found type meets a wanted one, `A^r` stands for
//! `A^s` when the stage order puts `r` at or below `s` and the two bases
//! relate, and for `A` itself, its stage forgotten; `A` never stands for
//! `A^s`, since a value at no stage may be any size. Invariantly — a code, a
//! data index, an equivalence — a stage equals only itself. The walk answers
//! [`Agreement::NotBelow`] at the first pair the order refuses, which the
//! value bridge names [`CheckRefusal::StageNotBelow`].
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
//! C′`. A capability is contravariant in its authority and covariant in its
//! region: `Cap E` stands where `Cap E′` is expected when every grant atom of
//! `E′` is one of `E` (Attenuate) and its region lives wherever the expected
//! one does; its grade is invariant. The first failure is
//! [`CheckRefusal::CapabilityAmplified`], the second
//! [`CheckRefusal::CapabilityEscaped`], and a type of another former where a
//! capability is expected is [`CheckRefusal::CapabilityForged`]: no term but a
//! capability hypothesis stands at a capability type. Witnesses:
//! `conversion::tests::returner_rows_are_covariant_but_signature_types_are_invariant`,
//! `conversion::tests::stack_is_contravariant_in_b_covariant_in_c_positive`,
//! `conversion::tests::stack_variance_negative` and
//! `capability::tests::attenuation_narrows_and_never_widens`.

use alloc::collections::BTreeSet;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_core_term::CertificateEquality;
use gandr_core_term::CompTypeId;
use gandr_core_term::ComputationId;
use gandr_core_term::Sort;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::effect::RowInclusion;
use gandr_core_term::effect::capability::RegionOrder;
use gandr_core_term::equal_certificate_syntax;
use gandr_core_term::hole::Knowledge;
use gandr_kernel_core::stage_order::Fit;
use gandr_kernel_strata::Level;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::Standing;
use quenchant_shape::shape::Maybe;

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
    /// Two path endpoints: the same term up to the normaliser's conversion,
    /// every admitted definition unfolding.
    Endpoints(ValueId, ValueId),
    /// A value type used where the second type is permitted.
    SubValues(ValueTypeId, ValueTypeId),
    /// A computation type used where the second row is permitted.
    SubComps(CompTypeId, CompTypeId),
}

/// The decision's verdict on a pair.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Agreement
{
    /// The two types are the same tree at their weak heads.
    Convertible,
    /// The two types differ at some node.
    Apart,
    /// Two capabilities whose expected authority grants an atom the found
    /// one does not.
    Amplified,
    /// Two capabilities whose found region ends before the expected one.
    Escaped,
    /// A value type at a stage, or at none, where a stage it does not stand
    /// at or below is wanted.
    NotBelow
    {
        /// Where the found type stands.
        found: gandr_kernel_term::Standing,
        /// The stage wanted.
        bound: gandr_kernel_term::Stage,
    },
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
///   [`CheckRefusal::CapabilityForged`] when a capability is expected and the
///   synthesised type is of another known former;
///   [`CheckRefusal::StageNotBelow`] naming `at` when a stage the order refuses
///   is wanted; [`CheckRefusal::CapabilityAmplified`] and
///   [`CheckRefusal::CapabilityEscaped`] when [`convert`] finds a capability
///   granting less or living shorter than the one expected; the unfolding's
///   refusal when a decode does not unfold.
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
    let mismatch = Mismatch::Value {
        at,
        synthesised,
        expected,
    };
    match convert(context, Pairing::Assignable(found, wanted))? {
        Agreement::Convertible => Ok(()),
        Agreement::Apart
            if matches!(
                value_type_view(context.arena(), wanted)?,
                ValueTypeView::Capability { .. }
            ) && !matches!(
                value_type_view(context.arena(), found)?,
                ValueTypeView::Capability { .. }
            ) =>
        {
            Err(CheckRefusal::CapabilityForged { at, expected })
        },
        Agreement::Apart => Err(CheckRefusal::TypeMismatch(mismatch)),
        Agreement::Amplified => Err(CheckRefusal::CapabilityAmplified(mismatch)),
        Agreement::Escaped => Err(CheckRefusal::CapabilityEscaped {
            at: TermNode::Value(at),
            found: crate::refusal::TypeNode::Value(synthesised),
        }),
        Agreement::NotBelow { found, bound } => {
            Err(CheckRefusal::StageNotBelow { at, found, bound })
        },
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
///   naming `at` and both types when they differ;
///   [`CheckRefusal::CapabilityAmplified`] and
///   [`CheckRefusal::CapabilityEscaped`] when a capability inside grants less
///   or lives shorter than the one expected; the unfolding's refusal when a
///   decode does not unfold.
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
    let mismatch = Mismatch::Computation {
        at,
        synthesised,
        expected,
    };
    match convert(context, Pairing::SubComps(synthesised, expected))? {
        Agreement::Convertible => Ok(()),
        Agreement::Apart | Agreement::NotBelow { .. } => Err(CheckRefusal::TypeMismatch(mismatch)),
        Agreement::Amplified => Err(CheckRefusal::CapabilityAmplified(mismatch)),
        Agreement::Escaped => Err(CheckRefusal::CapabilityEscaped {
            at: TermNode::Computation(at),
            found: crate::refusal::TypeNode::Computation(synthesised),
        }),
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
        ValueTypeView::Universe {
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
        ValueTypeView::Unknown => Ok(()),
        ValueTypeView::PathUniverse(..)
        | ValueTypeView::Path { .. }
        | ValueTypeView::Flow { .. }
        | ValueTypeView::Run(_)
        | ValueTypeView::Data { .. }
        | ValueTypeView::Record(_)
        | ValueTypeView::Sum(..)
        | ValueTypeView::List(_)
        | ValueTypeView::Stack { .. }
        | ValueTypeView::Capability { .. }
        | ValueTypeView::Integer
        | ValueTypeView::String
        | ValueTypeView::Unit
        | ValueTypeView::Thunk(_)
        | ValueTypeView::Lift { .. }
        | ValueTypeView::Element { .. }
        | ValueTypeView::Product(..)
        | ValueTypeView::Sigma { .. }
        | ValueTypeView::Abstract(_)
        | ValueTypeView::Session(_)
        | ValueTypeView::Staged { .. }
        | ValueTypeView::StaticPi { .. } => Err(CheckRefusal::TypeMismatch(Mismatch::Value {
            at: code,
            synthesised: found,
            expected,
        })),
    }
}

/// Whether the formed value types `left` and `right` are equivalent: the
/// decision [`convert`] makes, invariantly.
///
/// # Specification
/// - requires: both types are formed, in the context's arena.
/// - ensures: [`Agreement::Convertible`] exactly when [`convert`] answers it
///   for the pair compared invariantly; one id against itself is convertible.
/// - provides: the comparison an offer's arms agree on an endpoint's state by.
/// - fails: as [`convert`].
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — two arms leaving one endpoint at the same state minted
///   twice agree, and an arm leaving it at another state is refused.
/// - witness: `judgement::session::tests::offer_arms_leaving_different_endpoints_are_refused`
#[spec(ensures: |ret| left != right || ret == Ok(Agreement::Convertible))]
pub fn equivalent(
    context: &mut CheckingContext<'_>,
    left: ValueTypeId,
    right: ValueTypeId,
) -> Result<Agreement, CheckRefusal>
{
    convert(context, Pairing::Values(left, right))
}

/// Whether two path endpoints a type conversion met are the same term, keeping
/// the derivation where the machine's traced reading relates them.
///
/// # Specification
/// - requires: both endpoints stand under the binders the conversion is under.
/// - ensures: [`Agreement::Convertible`] with the trace recorded for the pair
///   on `context` when the machine relates `left` to `right` with returned
///   endpoints held at the definitions they call; otherwise
///   [`Agreement::Convertible`] exactly when its untraced conversion relates
///   them, and [`Agreement::Apart`] when it does not.
/// - provides: the dialogue a definition carries for the kernel, whose forced
///   reading does not unfold a definition under a binder. The traced reading is
///   tried first and only ever adds a derivation: where it does not relate, the
///   verdict and every refusal are the untraced conversion's, so nothing the
///   conversion accepted is refused.
/// - fails: the untraced conversion's refusal, where the traced reading does
///   not relate.
/// - panics: none.
/// - executable: none — both verdicts are the machine's own readings; a
///   predicate restating them would run the two readings again.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — an ascription relating compound endpoints through a
///   definition's body keeps the pair and its derivation, which the kernel
///   replays; an ascription whose endpoints are the same syntax keeps none.
/// - witness: `module::tests::an_ascription_keeps_the_endpoints_it_related`
/// - witness: `bridge::tests::an_ascription_crosses_with_the_endpoints_it_related`
fn endpoints_agree(
    context: &mut CheckingContext<'_>,
    left: ValueId,
    right: ValueId,
) -> Result<Agreement, CheckRefusal>
{
    if let Ok(Maybe::Present(decisions)) =
        context
            .definitions()
            .relate_terms(context.arena(), left, right)
    {
        context.record_relation(left, right, decisions);
        return Ok(Agreement::Convertible);
    }
    let verdict = context
        .definitions()
        .convert_terms(context.arena(), left, right)?;
    if verdict == gandr_core_nbe::MachineVerdict::Convertible {
        Ok(Agreement::Convertible)
    }
    else {
        Ok(Agreement::Apart)
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
///   position they differ. Two staged types agree invariantly at one stage and
///   agreeing bases; under subtyping a found staged type agrees with a wanted
///   one whose stage its own fits within, and with an unstaged type as its
///   base, while an unstaged type against a staged one, or a stage the order
///   refuses, is [`Agreement::NotBelow`].
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
///   instances rigid and defined, static lambdas alike and unlike, two rigid
///   returned codes of one call at distinct ids, and a dangling id; the fast
///   path is pinned against the structural decision by property.
/// - witness: `conversion::tests::one_id_converts_without_being_read`
/// - witness: `conversion::tests::equal_trees_at_distinct_ids_convert`
/// - witness: `conversion::tests::differing_trees_are_apart_in_either_order`
/// - witness: `conversion::tests::a_decode_of_a_defined_code_converts_with_its_body`
/// - witness: `conversion::tests::static_codes_compare_by_head_argument_and_body`
/// - witness: `conversion::tests::a_dangling_type_is_refused`
/// - witness: `conversion::tests::the_id_fast_path_agrees_with_the_structural_decision`
/// - witness: `conversion::tests::the_unknown_type_is_consistent_beside_a_differing_former`
/// - witness: `bridge::tests::an_unquoted_function_call_crosses_with_its_run_certified`
#[spec(ensures: |ret| match root {
    | Pairing::Values(left, right) | Pairing::Assignable(left, right) | Pairing::SubValues(left, right) if left == right => ret == Ok(Agreement::Convertible),
    | Pairing::Comps(left, right) | Pairing::SubComps(left, right) if left == right => ret == Ok(Agreement::Convertible),
    | Pairing::Codes(left, right) | Pairing::Terms(left,right) | Pairing::Endpoints(left, right) if left == right => ret == Ok(Agreement::Convertible),
    | Pairing::Values(..) | Pairing::Assignable(..) | Pairing::SubValues(..) | Pairing::Comps(..) | Pairing::SubComps(..) | Pairing::Codes(..) | Pairing::Terms(..) | Pairing::Endpoints(..) => true,
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
            Pairing::Values(left, right)
            | Pairing::Assignable(left, right)
            | Pairing::SubValues(left, right) => left == right,
            Pairing::Comps(left, right) | Pairing::SubComps(left, right) => left == right,
            Pairing::Codes(left, right)
            | Pairing::Terms(left, right)
            | Pairing::Endpoints(left, right) => left == right,
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
            Pairing::Terms(left, right) => {
                root_knowledge(context, left)? == Knowledge::Unknown
                    || root_knowledge(context, right)? == Knowledge::Unknown
                    || gandr_core_term::equal_certificate_syntax(context.arena(), left, right)
                        == gandr_core_term::CertificateEquality::Equal
            },
            Pairing::Endpoints(left, right) => {
                root_knowledge(context, left)? == Knowledge::Unknown
                    || root_knowledge(context, right)? == Knowledge::Unknown
                    || gandr_core_term::equal_certificate_syntax(context.arena(), left, right)
                        == gandr_core_term::CertificateEquality::Equal
                    || endpoints_agree(context, left, right)? == Agreement::Convertible
            },
            Pairing::Assignable(left, right) => {
                let left = context.whnf_value_type(left)?;
                let right = context.whnf_value_type(right)?;
                match (
                    value_type_view(context.arena(), left)?,
                    value_type_view(context.arena(), right)?,
                ) {
                    (ValueTypeView::Record(found), ValueTypeView::Record(wanted)) => {
                        for (label, &expected) in wanted {
                            let Some(&synthesised) = found.get(label)
                            else {
                                return Ok(Agreement::Apart);
                            };
                            pending.push(Pairing::Assignable(synthesised, expected));
                        }
                    },
                    _ => pending.push(Pairing::SubValues(left, right)),
                }
                true
            },
            Pairing::Values(left, right) | Pairing::SubValues(left, right) => {
                let left = context.whnf_value_type(left)?;
                let right = context.whnf_value_type(right)?;
                match (
                    value_type_view(context.arena(), left)?,
                    value_type_view(context.arena(), right)?,
                ) {
                    (
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
                    // A path at the point a type of words' cells loop at is
                    // those words, as the kernel reads them: both endpoints
                    // spell the point, or one does and the other converts
                    // with it, or each computes it (`mul(Base, Base)` at
                    // the circle's `Base`) and converts with it (#485).
                    (
                        ValueTypeView::Data {
                            declaration,
                            arguments,
                        },
                        ValueTypeView::Path {
                            carrier,
                            left: from,
                            right: to,
                        },
                    )
                    | (
                        ValueTypeView::Path {
                            carrier,
                            left: from,
                            right: to,
                        },
                        ValueTypeView::Data {
                            declaration,
                            arguments,
                        },
                    ) => {
                        if !arguments.is_empty() {
                            false
                        }
                        else if context.words(carrier, (from, to))? == Some(declaration) {
                            true
                        }
                        else if context.words(carrier, (to, to))? == Some(declaration) {
                            pending.push(Pairing::Endpoints(from, to));
                            true
                        }
                        else if context.words(carrier, (from, from))? == Some(declaration) {
                            pending.push(Pairing::Endpoints(to, from));
                            true
                        }
                        else if let Some(point) =
                            crate::loops::point_of(context, carrier, declaration)?
                        {
                            pending.push(Pairing::Endpoints(from, point));
                            pending.push(Pairing::Endpoints(to, point));
                            true
                        }
                        else {
                            false
                        }
                    },
                    (ValueTypeView::Record(a), ValueTypeView::Record(b)) => {
                        if a.len() != b.len() || !a.keys().eq(b.keys()) {
                            return Ok(Agreement::Apart);
                        }
                        pending.extend(a.values().zip(b.values()).map(|(&a, &b)| values(a, b)));
                        true
                    },
                    (
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
                    (ValueTypeView::PathUniverse(a, b), ValueTypeView::PathUniverse(c, d)) => {
                        pending.push(Pairing::Codes(a, c));
                        pending.push(Pairing::Codes(b, d));
                        true
                    },
                    (
                        ValueTypeView::Path {
                            carrier: a,
                            left: first,
                            right: second,
                        },
                        ValueTypeView::Path {
                            carrier: b,
                            left: third,
                            right: fourth,
                        },
                    )
                    | (
                        ValueTypeView::Flow {
                            carrier: a,
                            source: first,
                            target: second,
                        },
                        ValueTypeView::Flow {
                            carrier: b,
                            source: third,
                            target: fourth,
                        },
                    ) => {
                        pending.push(Pairing::Endpoints(second, fourth));
                        pending.push(Pairing::Endpoints(first, third));
                        pending.push(values(a, b));
                        true
                    },
                    // A run type is invariant in its protocol: a subtype's run
                    // may take an offer its supertype lacks, so moving a run
                    // along a subtyping is the checked `ride`, never a
                    // silent subsumption.
                    (ValueTypeView::Run(left), ValueTypeView::Run(right)) => {
                        pending.push(Pairing::Codes(left, right));
                        true
                    },
                    (ValueTypeView::List(left), ValueTypeView::List(right)) => {
                        pending.push(values(left, right));
                        true
                    },
                    (ValueTypeView::Unknown, _)
                    | (_, ValueTypeView::Unknown)
                    | (ValueTypeView::Integer, ValueTypeView::Integer)
                    | (ValueTypeView::String, ValueTypeView::String)
                    | (ValueTypeView::Unit, ValueTypeView::Unit) => true,
                    // Where a found type meets a wanted one a stage is
                    // subsumed by the order; invariantly it equals only
                    // itself.
                    (
                        ValueTypeView::Staged {
                            base: found_base,
                            stage: found,
                        },
                        ValueTypeView::Staged {
                            base: wanted_base,
                            stage: wanted,
                        },
                    ) => {
                        if subtyping {
                            if context.stages().fit(found, wanted) == Fit::NotBelow {
                                return Ok(Agreement::NotBelow {
                                    found: Standing::Staged(found),
                                    bound: wanted,
                                });
                            }
                            pending.push(values(found_base, wanted_base));
                            true
                        }
                        else {
                            pending.push(values(found_base, wanted_base));
                            found == wanted
                        }
                    },
                    (ValueTypeView::Staged { base, .. }, _) if subtyping => {
                        pending.push(values(base, right));
                        true
                    },
                    (_, ValueTypeView::Staged { stage, .. }) if subtyping => {
                        return Ok(Agreement::NotBelow {
                            found: Standing::Top,
                            bound: stage,
                        });
                    },
                    (ValueTypeView::Abstract(left), ValueTypeView::Abstract(right)) => {
                        left == right
                    },
                    (
                        ValueTypeView::Capability {
                            authority: found,
                            grade: found_grade,
                            region: found_region,
                        },
                        ValueTypeView::Capability {
                            authority: wanted,
                            grade: wanted_grade,
                            region: wanted_region,
                        },
                    ) => {
                        let arena = context.arena();
                        let narrows = wanted.grants_within(found, arena) == RowInclusion::Included;
                        if subtyping {
                            if !narrows {
                                return Ok(Agreement::Amplified);
                            }
                            if found_region.outlives(wanted_region) == RegionOrder::EndsFirst {
                                return Ok(Agreement::Escaped);
                            }
                            found_grade == wanted_grade
                        }
                        else {
                            narrows
                                && found.grants_within(wanted, arena) == RowInclusion::Included
                                && (found_grade, found_region) == (wanted_grade, wanted_region)
                        }
                    },
                    (ValueTypeView::Thunk(left), ValueTypeView::Thunk(right)) => {
                        pending.push(comps(left, right));
                        true
                    },
                    (
                        ValueTypeView::Universe {
                            sort: left_sort,
                            level: left_level,
                        },
                        ValueTypeView::Universe {
                            sort: right_sort,
                            level: right_level,
                        },
                    ) => left_sort == right_sort && left_level == right_level,
                    (
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
                    (
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
                    (ValueTypeView::Sum(left), ValueTypeView::Sum(right))
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
                    (ValueTypeView::Session(_), ValueTypeView::Session(_)) => {
                        let relation = if subtyping {
                            gandr_core_session::Relation::Subtype
                        }
                        else {
                            gandr_core_session::Relation::Equivalent
                        };
                        match crate::session::relate(context, left, right, relation)? {
                            Maybe::Present(payloads) => {
                                pending.extend(
                                    payloads
                                        .into_iter()
                                        .map(|(left, right)| Pairing::Values(left, right)),
                                );
                                true
                            },
                            Maybe::Absent(_) => false,
                        }
                    },
                    (
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
                    // The second factors stand under one binder each, at the
                    // same index, so they compare as they stand.
                    (
                        ValueTypeView::Sigma {
                            first: left_first,
                            second: left_second,
                        },
                        ValueTypeView::Sigma {
                            first: right_first,
                            second: right_second,
                        },
                    ) => {
                        pending.push(values(left_second, right_second));
                        pending.push(values(left_first, right_first));
                        true
                    },
                    (
                        ValueTypeView::PathUniverse(..)
                        | ValueTypeView::Path { .. }
                        | ValueTypeView::Flow { .. }
                        | ValueTypeView::Run(_)
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
                        | ValueTypeView::Sigma { .. }
                        | ValueTypeView::Abstract(_)
                        | ValueTypeView::Session(_)
                        | ValueTypeView::StaticPi { .. }
                        | ValueTypeView::Capability { .. }
                        | ValueTypeView::Staged { .. },
                        _,
                    ) => false,
                }
            },
            Pairing::Comps(left, right) | Pairing::SubComps(left, right) => {
                let left = context.whnf_comp_type(left)?;
                let right = context.whnf_comp_type(right)?;
                match (
                    comp_type_view(context.arena(), left)?,
                    comp_type_view(context.arena(), right)?,
                ) {
                    (CompTypeView::Unknown, _) | (_, CompTypeView::Unknown) => true,
                    (CompTypeView::With(a, b), CompTypeView::With(c, d)) => {
                        pending.extend([comps(a, c), comps(b, d)]);
                        true
                    },
                    (
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
                    (
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
                    (
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
                    (
                        CompTypeView::Returner { .. }
                        | CompTypeView::With(..)
                        | CompTypeView::Arrow { .. }
                        | CompTypeView::Pi { .. }
                        | CompTypeView::Element { .. },
                        _,
                    ) => false,
                }
            },
            Pairing::Codes(left, right) => {
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
                            else if let Value::Returned(_) = *matched_left_value
                                && let Value::Returned(_) = *matched_right_value
                            {
                                equal_certificate_syntax(context.arena(), left, right)
                                    == CertificateEquality::Equal
                            }
                            else if let Value::Recorded(ref left_moves) = *matched_left_value
                                && let Value::Recorded(ref right_moves) = *matched_right_value
                            {
                                let same = left_moves.len() == right_moves.len()
                                    && left_moves.iter().zip(right_moves.iter()).all(
                                        |(left, right)| left.carrying(()) == right.carrying(()),
                                    );
                                if same {
                                    pending.extend(
                                        left_moves.iter().zip(right_moves.iter()).rev().filter_map(
                                            |(left, right)| match (left.payload(), right.payload())
                                            {
                                                (Maybe::Present(left), Maybe::Present(right)) => {
                                                    Some(Pairing::Codes(left, right))
                                                },
                                                _ => None,
                                            },
                                        ),
                                    );
                                }
                                same
                            }
                            else {
                                {
                                    match *matched_left_value {
                                        Value::PathRefl(_)
                                        | Value::Here(_)
                                        | Value::Stay(_)
                                        | Value::Then(..)
                                        | Value::FlowProduct(..)
                                        | Value::Forward(_)
                                        | Value::FunctionFlow(..)
                                        | Value::SessionRelated { .. }
                                        | Value::Recorded(_)
                                        | Value::Funext(..)
                                        | Value::Equiv(..)
                                        | Value::Ua { .. }
                                        | Value::Returned(_)
                                        | Value::Nested(_)
                                        | Value::Run(_)
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
mod tests;
