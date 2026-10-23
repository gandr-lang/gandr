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
//! # A dependent arrow whose codomain ignores its binder is the plain arrow
//!
//! `(x : A) -> B` with `x` absent from `B` is `A -> B` (#577). The walk kept
//! the two arrows apart by head, on the producer's promise to emit the
//! dependent former only where the codomain names its binder; a family applied
//! at its binder (`always(x)`) breaks that promise, since only reading the
//! family's code shows that the codomain ignores `x`. A dependent arrow against
//! a plain one now compares their domains, contravariantly as two arrows do,
//! and the dependent codomain against the plain one weakened past the binder:
//! the weakened codomain cannot name the binder, so the pair agrees exactly
//! when the dependent codomain does not use it. The kernel and the
//! normaliser's comparison of codes read the same rule. Alternatives:
//! strengthening the dependent codomain, which needs an occurrence test the
//! weakening does without, and rewriting a vacuous dependent arrow to the
//! plain one where it is minted, which no producer can do before the family
//! is read. Reversal: a core with one arrow former.
//!
//! # A relocated side is read through its relocation
//!
//! A variable's slot type reaches the value bridge moved to the depth it is
//! read at as a root update, a [`Relocated`] id, and the walk reads it
//! without minting the moved tree. Where both sides stand at a former whose
//! comparison is types beneath and a leaf — a product, a sum, a record, a
//! list, a thunk, a stack, a static or dependent pair, a lift, a universe, a
//! base type, a lazy product, a returner over the empty row, an arrow of either
//! kind — each child pair is pushed carrying its parent's relocation, under
//! one more binder at a dependent pair's second factor and a dependent
//! arrow's codomain; the plain codomain an arrow meets a dependent one with
//! is weakened by a root update too. Everything else is settled first and
//! compared as before: a decode or a sealed atom, whose unfolding is
//! certified beneath the context's binders; a data type, a path, a flow, a
//! run, a session, a capability, a staged type and a world, whose comparisons
//! read terms, protocols, grants or the stage order; a returner over a row.
//! An owed flex–rigid equation always has a decode on one side, so deferral
//! sees only settled pairs, and a refusal names the synthesised type settled.
//! The alternatives were settling at the variable rule, which mints the moved
//! tree on every read, and composing the relocation into every reader, which
//! the views, goals and refusals would all carry. Reversal: when the
//! judgement's goals read relocated types themselves, the settled formers
//! here move to reading through one by one.
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
use gandr_core_term::Binders;
use gandr_core_term::CertificateEquality;
use gandr_core_term::CompTypeId;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::Relocated;
use gandr_core_term::Relocation;
use gandr_core_term::Sort;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::effect::RowInclusion;
use gandr_core_term::effect::capability::RegionOrder;
use gandr_core_term::equal_certificate_syntax;
use gandr_core_term::hole::Knowledge;
use gandr_core_term::shift_comp_type;
use gandr_core_term::world::WorldType;
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
use crate::refusal::TypeNode;
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

/// A pair of nodes of one family, to be compared. A type is read through the
/// relocation it carries, a code or a term as it stands.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Pairing
{
    /// Two value types.
    Values(Relocated<ValueTypeId>, Relocated<ValueTypeId>),
    /// Directional structural record inclusion; other types remain invariant.
    Assignable(Relocated<ValueTypeId>, Relocated<ValueTypeId>),
    /// Two computation types.
    Comps(Relocated<CompTypeId>, Relocated<CompTypeId>),
    /// Two codes, each read at its head.
    Codes(ValueId, ValueId),
    /// Invariant term-valued indices, with the kernel's structural equality.
    Terms(ValueId, ValueId),
    /// Two path endpoints: the same term up to the normaliser's conversion,
    /// every admitted definition unfolding.
    Endpoints(ValueId, ValueId),
    /// A value type used where the second type is permitted.
    SubValues(Relocated<ValueTypeId>, Relocated<ValueTypeId>),
    /// A computation type used where the second row is permitted.
    SubComps(Relocated<CompTypeId>, Relocated<CompTypeId>),
}

/// How a walk relates the type pairs beneath the pair it is at.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Variance
{
    /// Each pair is the same type on both sides.
    Invariant,
    /// Each pair is a found type against a wanted one.
    Subtyping,
}

impl Variance
{
    /// The pairing of two value types at this variance.
    ///
    /// # Specification
    /// trivial.
    const fn values(
        self,
        found: Relocated<ValueTypeId>,
        wanted: Relocated<ValueTypeId>,
    ) -> Pairing
    {
        match self {
            Self::Invariant => Pairing::Values(found, wanted),
            Self::Subtyping => Pairing::SubValues(found, wanted),
        }
    }

    /// The pairing of two computation types at this variance.
    ///
    /// # Specification
    /// trivial.
    const fn comps(
        self,
        found: Relocated<CompTypeId>,
        wanted: Relocated<CompTypeId>,
    ) -> Pairing
    {
        match self {
            Self::Invariant => Pairing::Comps(found, wanted),
            Self::Subtyping => Pairing::SubComps(found, wanted),
        }
    }
}

/// Why a pair of types was not read through their relocations.
mod through
{
    /// The reason the walk reads the pair as plain types.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub(super) enum Absent
    {
        /// Neither side carries a relocation.
        Plain,
        /// The formers met are not read through a relocation: a decode, whose
        /// code is compared as a term, or a former whose comparison reads
        /// terms, sessions, capabilities or stages.
        Unread,
    }
}

/// Why a pair poses no equation to the solver.
mod open
{
    /// The reason the pair is compared as written.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub(super) enum Absent
    {
        /// Neither side is a hole or a mark: the pair is compared as written.
        Closed,
    }
}

/// What reading a pair through its relocations found.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Read
{
    /// The pair agrees once the pairs pushed beneath it do.
    Pushed,
    /// The pair disagrees at its root.
    Apart,
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
/// - requires: both types are formed, in the context's arena; the synthesised
///   one plain or read through the relocation it carries, as a variable's slot
///   type arrives.
/// - ensures: when both types are universes at their weak heads, success
///   exactly when they share a sort and the synthesised level lies at or below
///   the expected one, below only in the value sort, which records a [`Lift`]
///   at `at` from the synthesised level to the expected one — in the side table
///   under ordinary checking, as one more occurrence of `at` under a
///   term-producing run, which records an equal level as an identity occurrence
///   too; otherwise success exactly when [`convert`] answers convertible, or
///   when it answers apart and a kept reduct carries the synthesised type to
///   the expected one, which records the crossing at `at` by the first such
///   reduct. `tally` advances once on every outcome, saturating at its ceiling.
/// - provides: the only comparison of value types the judgement makes, and the
///   only place a code moves up a universe.
/// - fails: [`CheckRefusal::SortMismatch`] for two universes of different
///   sorts; [`CheckRefusal::LevelMismatch`] for a level above the expected one,
///   or below it in the computation sort; [`CheckRefusal::TypeMismatch`] with
///   [`Mismatch::Value`] naming `at` and both types, the synthesised one
///   settled, when they differ otherwise; [`CheckRefusal::CapabilityForged`]
///   when a capability is expected and the synthesised type is of another known
///   former; [`CheckRefusal::StageNotBelow`] naming `at` when a stage the order
///   refuses is wanted; [`CheckRefusal::CapabilityAmplified`] and
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
///   code of the other sort, each answer and count asserted; a relocated
///   synthesised type answers as its settled reading does; a pair nesting more
///   components than the one asked crosses by the reduct kept, and is refused
///   with none kept.
/// - witness: `conversion::tests::the_value_bridge_lifts_a_small_value_code_and_nothing_else`
/// - witness: `conversion::tests::a_relocated_type_converts_as_its_settled_reading`
/// - witness: `judgement::tests::a_mismatched_literal_is_refused_with_both_types`
/// - witness: `judgement::tests::a_two_bridge_check_crosses_the_boundary_twice`
/// - witness: `judgement::tests::a_value_type_in_a_computation_universe_is_a_sort_mismatch`
/// - witness: `elaboration::tests::shared_code_occurrences_keep_distinct_transports`
/// - witness: `module::tests::a_model_crosses_to_an_included_theory_s_by_its_reduct`
#[spec(
    captures: before = tally.0,
    ensures: |ret| tally.0 == before.saturating_add(1)
        && match ret {
            | Err(CheckRefusal::TypeMismatch(Mismatch::Value { at: named, synthesised: found, expected: wanted })) => named == at && wanted == expected
                && (Relocated::from(found) == Into::<Relocated<ValueTypeId>>::into(synthesised)
                    || Into::<Relocated<ValueTypeId>>::into(synthesised).relocation() != Relocation::IDENTITY),
            | Err(CheckRefusal::SortMismatch { at: named, .. } | CheckRefusal::LevelMismatch { at: named, .. }) => named == at,
            | _ => true,
        }
        && if let (Ok(ValueTypeView::Universe { sort: found_sort, level: found }), Ok(ValueTypeView::Universe { sort: wanted_sort, level: wanted })) =
            (value_type_view(context.arena(), Into::<Relocated<ValueTypeId>>::into(synthesised).node()), value_type_view(context.arena(), expected)) {
            let lifts = found_sort == GroundSort::Value && bool::from(found.lt(wanted));
            ret.is_ok() == (found_sort == wanted_sort && (found == wanted || lifts))
                && (ret.is_err() || !lifts || !matches!(context.deferrals().emission, crate::elaboration::Emission::Off)
                    || context.lifts().get(&at).is_some_and(|lift| lift.natural() == found && lift.target() == wanted))
        } else {
            true
        },
)]
pub fn value_bridge<Synthesised>(
    context: &mut CheckingContext<'_>,
    at: ValueId,
    synthesised: Synthesised,
    expected: ValueTypeId,
    tally: &mut ConversionCount,
) -> Result<(), CheckRefusal>
where
    Synthesised: Into<Relocated<ValueTypeId>> + Copy,
{
    *tally = tally.crossed();
    let synthesised = synthesised.into();
    let found = value_head(context, synthesised)?;
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
        value_type_view(context.arena(), found.node())?,
        value_type_view(context.arena(), wanted)?,
    ) {
        let (found_level, wanted_level) = (found_level.clone(), wanted_level.clone());
        if found_sort != wanted_sort {
            return Err(CheckRefusal::SortMismatch {
                at,
                synthesised: found.settle(context.arena_mut()),
                expected: wanted,
            });
        }
        if found_level == wanted_level {
            context.record_unlifted(at);
            return Ok(());
        }
        if found_sort == GroundSort::Value && bool::from(found_level.lt(&wanted_level)) {
            context.record_lift(at, Lift::new(found_level, wanted_level));
            return Ok(());
        }
        return Err(CheckRefusal::LevelMismatch {
            at,
            synthesised: found.settle(context.arena_mut()),
            expected: wanted,
        });
    }
    let agreement = convert(context, Pairing::Assignable(found, Relocated::from(wanted)))?;
    if agreement == Agreement::Convertible {
        return Ok(());
    }
    // A model of a theory stands at a model of one it includes by the reduct
    // between them, and a model whose sorts are manifest at its theory's
    // models by the theory's forgetting map at the carriers its sorts are
    // fixed to; the elaboration applies the map where the bridge crossed.
    if agreement == Agreement::Apart
        && let Maybe::Present(crossing) = crossing(context, found, wanted)?
    {
        context.record_crossing(at, crossing);
        return Ok(());
    }
    let forged = agreement == Agreement::Apart
        && matches!(
            value_type_view(context.arena(), wanted)?,
            ValueTypeView::Capability { .. }
        )
        && !matches!(
            value_type_view(context.arena(), found.node())?,
            ValueTypeView::Capability { .. }
        );
    // A refusal names the types as they print: the synthesised one settled.
    let synthesised = synthesised.settle(context.arena_mut());
    let mismatch = Mismatch::Value {
        at,
        synthesised,
        expected,
    };
    match agreement {
        Agreement::Convertible => Ok(()),
        Agreement::Apart if forged => Err(CheckRefusal::CapabilityForged { at, expected }),
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

/// The first kept map between models whose signature carries the type `found`
/// to the type `wanted`, with the carriers it takes before the value.
///
/// # Specification
/// - requires: both types are formed, in the context's arena.
/// - ensures: the first map the context keeps whose signature is a thunk of
///   `Π(x₁ : U₁) … Π(xₙ : Uₙ). A → F B`, `n` possibly none, with carriers `c₁ …
///   cₙ` at which `found` converts to `A[c/x]` and `B[c/x]` to `wanted`; the
///   carriers are those [`carriers`] solves from `found` against `A`, none for
///   a map that quantifies over none; nothing when no kept map's does.
/// - fails: the refusals [`convert`] yields, and a view's of a signature.
/// - panics: none.
/// - executable: none — the kept maps and their signatures are the context's,
///   which a predicate would search and convert again.
///
/// # Errors
/// As the fails clause.
///
/// # Adequacy
/// - hypothesis: L3 — a monoid's model at a semigroup's crosses by the monoid's
///   reduct, and at an unrelated theory's by none; a counter whose carrier is
///   manifest crosses at the counters by the forgetting map at that carrier.
/// - witness: `module::tests::a_model_crosses_to_an_included_theory_s_by_its_reduct`
/// - witness: `module::tests::a_manifest_model_crosses_by_its_forgetting_map_at_its_carrier`
fn crossing(
    context: &mut CheckingContext<'_>,
    found: Relocated<ValueTypeId>,
    wanted: ValueTypeId,
) -> Result<Maybe<gandr_core_term::Crossing, ()>, CheckRefusal>
{
    let mut next = 0_usize;
    while let Some(&map) = context.reducts().get(next) {
        next = next.saturating_add(1);
        let Maybe::Present(signature) = context.signature(map)
        else {
            continue;
        };
        let ValueTypeView::Thunk(chain) = value_type_view(context.arena(), signature.id())?
        else {
            continue;
        };
        let carriers = match carriers(context, found, chain)? {
            Maybe::Present(carriers) => carriers,
            Maybe::Absent(()) => continue,
        };
        let mut arrow = chain;
        for &carrier in &carriers {
            let CompTypeView::Pi { codomain, .. } = comp_type_view(context.arena(), arrow)?
            else {
                break;
            };
            arrow = gandr_core_term::instantiate_comp_type(context.arena_mut(), codomain, carrier);
        }
        let CompTypeView::Arrow { domain, codomain } = comp_type_view(context.arena(), arrow)?
        else {
            continue;
        };
        let CompTypeView::Returner { result, .. } = comp_type_view(context.arena(), codomain)?
        else {
            continue;
        };
        if convert(context, Pairing::Assignable(found, Relocated::from(domain)))?
            == Agreement::Convertible
            && convert(
                context,
                Pairing::Assignable(Relocated::from(result), Relocated::from(wanted)),
            )? == Agreement::Convertible
        {
            return Ok(Maybe::Present(gandr_core_term::Crossing {
                by: map,
                carriers,
            }));
        }
    }

    Ok(Maybe::Absent(()))
}

/// The carriers a map's signature `chain` takes before the value it crosses
/// `found` by: one per leading `Π`, each the solution the solver binds a
/// metavariable standing for it to, from `found` against the arrow's domain.
///
/// # Specification
/// - requires: `chain` is the computation type a kept map's signature thunks,
///   closed; `found` is formed in the context's arena.
/// - ensures: no carriers when `chain` opens with no `Π`; otherwise one
///   metavariable per leading `Π`, declared over the context's intuitionistic
///   binders and named by [`gandr_core_term::hole::HoleId::crossing`] in order,
///   `chain` instantiated at them, and the domain of the arrow below posed
///   against `found` settled: the solutions, outermost first, when the solver
///   refutes nothing and binds every one, what it postpones left to the
///   conversion [`crossing`] confirms by; nothing otherwise. The metavariables
///   are the call's own and stand in no body.
/// - fails: a view's refusal of `chain`; the context's refusal of a depth no
///   binder count holds.
/// - panics: none.
/// - executable: none — the solutions are the solver's, which a predicate would
///   pose again; [`crossing`] confirms them by conversion.
///
/// # Errors
/// As the fails clause.
///
/// # Adequacy
/// - hypothesis: L3 — as [`crossing`].
/// - witness: `module::tests::a_manifest_model_crosses_by_its_forgetting_map_at_its_carrier`
fn carriers(
    context: &mut CheckingContext<'_>,
    found: Relocated<ValueTypeId>,
    chain: CompTypeId,
) -> Result<Maybe<Vec<ValueId>, ()>, CheckRefusal>
{
    if !matches!(
        comp_type_view(context.arena(), chain)?,
        CompTypeView::Pi { .. }
    ) {
        return Ok(Maybe::Present(Vec::new()));
    }
    let scope = context.intuitionistic_scope()?;
    let mut metas = gandr_core_unify::Metas::new();
    let mut declared = Vec::new();
    let mut arrow = chain;
    let mut place = 0_u32;
    while let CompTypeView::Pi { codomain, .. } = comp_type_view(context.arena(), arrow)? {
        let Some(hole) = gandr_core_term::hole::HoleId::crossing(
            gandr_core_term::hole::NominationIndex::from(place),
        )
        else {
            return Ok(Maybe::Absent(()));
        };
        let Maybe::Present(meta) = metas.declare(hole, scope)
        else {
            return Ok(Maybe::Absent(()));
        };
        declared.push(meta);
        let standing = context.arena_mut().value_hole(hole);
        arrow = gandr_core_term::instantiate_comp_type(context.arena_mut(), codomain, standing);
        place = place.saturating_add(1);
    }
    let CompTypeView::Arrow { domain, .. } = comp_type_view(context.arena(), arrow)?
    else {
        return Ok(Maybe::Absent(()));
    };
    let found = found.settle(context.arena_mut());
    let equation = gandr_core_unify::Equation::new(
        scope,
        gandr_core_unify::Side::ValueType(domain),
        gandr_core_unify::Side::ValueType(found),
    );
    // A former the fragment does not decompose, a law's `Path` among them,
    // waits rather than binds; what waits is the confirming conversion's to
    // decide, so only a refutation stops the carriers here.
    if matches!(
        gandr_core_unify::solve(context.arena_mut(), &mut metas, &[equation]),
        gandr_core_unify::Verdict::Refuted(_)
    ) {
        return Ok(Maybe::Absent(()));
    }
    let mut solved = Vec::with_capacity(declared.len());
    for meta in declared {
        let Maybe::Present(solution) = metas.solution(meta)
        else {
            return Ok(Maybe::Absent(()));
        };
        solved.push(solution);
    }

    Ok(Maybe::Present(solved))
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
    match convert(
        context,
        Pairing::SubComps(Relocated::from(synthesised), Relocated::from(expected)),
    )? {
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
        | ValueTypeView::Prefix(_)
        | ValueTypeView::Dialogue(_)
        | ValueTypeView::Web
        | ValueTypeView::Data { .. }
        | ValueTypeView::Record(_)
        | ValueTypeView::Sum(..)
        | ValueTypeView::List(_)
        | ValueTypeView::Stack { .. }
        | ValueTypeView::Capability { .. }
        | ValueTypeView::Buffer
        | ValueTypeView::Integer
        | ValueTypeView::String
        | ValueTypeView::Character
        | ValueTypeView::Float64
        | ValueTypeView::Fixed(_)
        | ValueTypeView::Unit
        | ValueTypeView::Thunk(_)
        | ValueTypeView::Lift { .. }
        | ValueTypeView::Element { .. }
        | ValueTypeView::Product(..)
        | ValueTypeView::Sigma { .. }
        | ValueTypeView::Abstract(_)
        | ValueTypeView::Session(_)
        | ValueTypeView::Staged { .. }
        | ValueTypeView::Kept { .. }
        | ValueTypeView::World(_)
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
    convert(
        context,
        Pairing::Values(Relocated::from(left), Relocated::from(right)),
    )
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
            .relate_terms(context.arena(), left, right, &[])
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
///   type, or both sides have the same former, or one is a dependent arrow and
///   the other a plain arrow whose codomain, weakened past the dependent
///   binder, agrees with the dependent codomain, universes and lifts the same
///   sort and level, and rigid decodes the same level and the same code: two
///   codes agree when, each reduced at its head, either is a hole or a mark, or
///   they are the same variable or constant, quotes of agreeing types, static
///   applications of agreeing heads to agreeing arguments, or static lambdas
///   over agreeing bodies; two data indices agree when either root is a hole or
///   a mark the solver does not refute against the other side, or they are
///   equal as syntax, and two endpoints by the same rule or when they convert
///   as endpoints; [`Agreement::Apart`] at the first rigid disagreement. Inside
///   the elaboration run a bare owed flex–rigid equation is accumulated
///   instead: agreement is then conditional on those residuals, and a later
///   rigid disagreement still answers `Apart`. A pair not deferred whose side
///   is the decode of a metavariable a call nominated is posed to the solver: a
///   solved or postponed equation agrees, and a refuted one answers `Apart`.
///   Two staged types agree invariantly at one stage and agreeing bases; under
///   subtyping a found staged type agrees with a wanted one whose stage its own
///   fits within, and with an unstaged type as its base, while an unstaged type
///   against a staged one, or a stage the order refuses, is
///   [`Agreement::NotBelow`].
/// - fails: the refusal a view gives for a node outside the fragment or a
///   dangling id, the unfolding's refusal when a decode or a code does not
///   reduce, and [`CheckRefusal::MachineInvariant`] when the binders open pass
///   any binder count a metavariable's equation can be posed under.
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
///   returned codes of one call at distinct ids, a dependent arrow against a
///   plain one whose codomain ignores the binder, names it, or reads the
///   ambient context past it, and a dangling id; the fast path is pinned
///   against the structural decision by property.
/// - witness: `conversion::tests::one_id_converts_without_being_read`
/// - witness: `conversion::tests::equal_trees_at_distinct_ids_convert`
/// - witness: `conversion::tests::differing_trees_are_apart_in_either_order`
/// - witness: `conversion::tests::a_decode_of_a_defined_code_converts_with_its_body`
/// - witness: `conversion::tests::static_codes_compare_by_head_argument_and_body`
/// - witness: `conversion::tests::a_dangling_type_is_refused`
/// - witness: `conversion::tests::the_id_fast_path_agrees_with_the_structural_decision`
/// - witness: `conversion::tests::the_unknown_type_is_consistent_beside_a_differing_former`
/// - witness: `bridge::tests::an_unquoted_function_call_crosses_with_its_run_certified`
/// - witness: `conversion::tests::codes_agree_exactly_where_their_parts_do`
/// - witness: `conversion::tests::invariant_types_agree_exactly_where_their_parts_do`
/// - witness: `conversion::tests::a_row_meets_its_signatures_in_a_wider_row_by_name`
/// - witness: `conversion::tests::invariant_capabilities_agree_on_authority_grade_and_region`
/// - witness: `conversion::tests::kept_and_located_types_agree_on_their_region_and_world`
/// - witness: `conversion::tests::a_path_type_is_apart_from_data_it_does_not_read_as`
/// - witness: `conversion::tests::a_vacuous_dependent_arrow_is_the_plain_arrow_577`
/// - witness: `elaboration::tests::owed_conversion_suspends`
/// - witness: `elaboration::tests::residual_conjunction_does_not_hide_refusal`
/// - witness: `bridge::tests::an_omitted_implicit_is_supplied_before_the_kernel_1216`
/// - witness: `bridge::tests::an_omitted_implicit_is_refused_unforced_or_apart_1216`
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
        let variance = if subtyping {
            Variance::Subtyping
        }
        else {
            Variance::Invariant
        };
        let values = |a: ValueTypeId, b: ValueTypeId| {
            variance.values(Relocated::from(a), Relocated::from(b))
        };
        let comps =
            |a: CompTypeId, b: CompTypeId| variance.comps(Relocated::from(a), Relocated::from(b));
        let agrees = match pairing {
            Pairing::Terms(left, right) => match pose_open(context, left, right)? {
                Maybe::Present(unified) => unified != crate::elaboration::Unified::Refuted,
                Maybe::Absent(open::Absent::Closed) => {
                    gandr_core_term::equal_certificate_syntax(context.arena(), left, right)
                        == gandr_core_term::CertificateEquality::Equal
                },
            },
            Pairing::Endpoints(left, right) => match pose_open(context, left, right)? {
                Maybe::Present(unified) => unified != crate::elaboration::Unified::Refuted,
                Maybe::Absent(open::Absent::Closed) => {
                    gandr_core_term::equal_certificate_syntax(context.arena(), left, right)
                        == gandr_core_term::CertificateEquality::Equal
                        || endpoints_agree(context, left, right)? == Agreement::Convertible
                },
            },
            Pairing::Assignable(left, right) => {
                let left = value_head(context, left)?;
                let right = value_head(context, right)?;
                let arena = context.arena();
                match (
                    value_type_view(arena, left.node())?,
                    value_type_view(arena, right.node())?,
                ) {
                    (ValueTypeView::Record(found), ValueTypeView::Record(wanted)) => {
                        for (label, &expected) in wanted {
                            let Some(&synthesised) = found.get(label)
                            else {
                                return Ok(Agreement::Apart);
                            };
                            pending.push(Pairing::Assignable(
                                arena.place_value_type(synthesised, left.relocation()),
                                arena.place_value_type(expected, right.relocation()),
                            ));
                        }
                    },
                    _ => pending.push(Pairing::SubValues(left, right)),
                }
                true
            },
            Pairing::Values(left, right) | Pairing::SubValues(left, right) => {
                let left = value_head(context, left)?;
                let right = value_head(context, right)?;
                match relocated_values(context.arena(), (left, right), variance, &mut pending)? {
                    Maybe::Present(Read::Pushed) => continue,
                    Maybe::Present(Read::Apart) => return Ok(Agreement::Apart),
                    Maybe::Absent(through::Absent::Plain | through::Absent::Unread) => {},
                }
                let left = left.settle(context.arena_mut());
                let right = right.settle(context.arena_mut());
                if context.defer(TypeNode::Value(left), TypeNode::Value(right))
                    == crate::elaboration::Deferred::Yes
                {
                    continue;
                }
                match context.unify(TypeNode::Value(left), TypeNode::Value(right))? {
                    crate::elaboration::Unified::Agreed => continue,
                    crate::elaboration::Unified::Refuted => return Ok(Agreement::Apart),
                    crate::elaboration::Unified::Rigid => {},
                }
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
                    // A run, prefix or dialogue type is invariant in its
                    // protocol: a subtype's run may take an offer its
                    // supertype lacks, so moving a run along a subtyping is
                    // the checked `ride`, never a silent subsumption. A run is
                    // no prefix: the formers do not convert.
                    (ValueTypeView::Run(left), ValueTypeView::Run(right))
                    | (ValueTypeView::Prefix(left), ValueTypeView::Prefix(right))
                    | (ValueTypeView::Dialogue(left), ValueTypeView::Dialogue(right)) => {
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
                    | (ValueTypeView::Character, ValueTypeView::Character)
                    | (ValueTypeView::Float64, ValueTypeView::Float64)
                    | (ValueTypeView::Unit, ValueTypeView::Unit)
                    | (ValueTypeView::Buffer, ValueTypeView::Buffer)
                    | (ValueTypeView::Web, ValueTypeView::Web) => true,
                    (ValueTypeView::Fixed(left_width), ValueTypeView::Fixed(right_width)) => {
                        left_width == right_width
                    },
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
                    // A value kept in a region that outlives the one wanted
                    // lives long enough; invariantly a region equals only
                    // itself. Any value enters a region, and none leaves one.
                    (
                        ValueTypeView::Kept {
                            value: found_value,
                            region: found,
                        },
                        ValueTypeView::Kept {
                            value: wanted_value,
                            region: wanted,
                        },
                    ) => {
                        pending.push(values(found_value, wanted_value));
                        if subtyping {
                            found.outlives(wanted) == RegionOrder::Outlives
                        }
                        else {
                            found == wanted
                        }
                    },
                    (_, ValueTypeView::Kept { value, .. }) if subtyping => {
                        pending.push(values(left, value));
                        true
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
                                pending.extend(payloads.into_iter().map(|pair| {
                                    let (left, right) = pair.types;
                                    Pairing::Values(Relocated::from(left), Relocated::from(right))
                                }));
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
                    // A handle is covariant in what it holds and names one
                    // world; a capability names one world.
                    (
                        ValueTypeView::World(WorldType::At {
                            inner: left_inner,
                            world: left_world,
                        }),
                        ValueTypeView::World(WorldType::At {
                            inner: right_inner,
                            world: right_world,
                        }),
                    ) => {
                        pending.push(values(left_inner, right_inner));
                        left_world == right_world
                    },
                    (
                        ValueTypeView::World(WorldType::Capability(left_world)),
                        ValueTypeView::World(WorldType::Capability(right_world)),
                    ) => left_world == right_world,
                    (
                        ValueTypeView::PathUniverse(..)
                        | ValueTypeView::Path { .. }
                        | ValueTypeView::Flow { .. }
                        | ValueTypeView::Run(_)
                        | ValueTypeView::Prefix(_)
                        | ValueTypeView::Dialogue(_)
                        | ValueTypeView::Web
                        | ValueTypeView::Data { .. }
                        | ValueTypeView::Record(_)
                        | ValueTypeView::Sum(..)
                        | ValueTypeView::List(_)
                        | ValueTypeView::Stack { .. }
                        | ValueTypeView::Integer
                        | ValueTypeView::String
                        | ValueTypeView::Character
                        | ValueTypeView::Float64
                        | ValueTypeView::Fixed(_)
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
                        | ValueTypeView::Buffer
                        | ValueTypeView::Staged { .. }
                        | ValueTypeView::Kept { .. }
                        | ValueTypeView::World(_),
                        _,
                    ) => false,
                }
            },
            Pairing::Comps(left, right) | Pairing::SubComps(left, right) => {
                let left = comp_head(context, left)?;
                let right = comp_head(context, right)?;
                match relocated_comps(context.arena_mut(), (left, right), variance, &mut pending)? {
                    Maybe::Present(Read::Pushed) => continue,
                    Maybe::Present(Read::Apart) => return Ok(Agreement::Apart),
                    Maybe::Absent(through::Absent::Plain | through::Absent::Unread) => {},
                }
                let left = left.settle(context.arena_mut());
                let right = right.settle(context.arena_mut());
                if context.defer(TypeNode::Computation(left), TypeNode::Computation(right))
                    == crate::elaboration::Deferred::Yes
                {
                    continue;
                }
                match context.unify(TypeNode::Computation(left), TypeNode::Computation(right))? {
                    crate::elaboration::Unified::Agreed => continue,
                    crate::elaboration::Unified::Refuted => return Ok(Agreement::Apart),
                    crate::elaboration::Unified::Rigid => {},
                }
                match (
                    comp_type_view(context.arena(), left)?,
                    comp_type_view(context.arena(), right)?,
                ) {
                    (CompTypeView::Unknown, _) | (_, CompTypeView::Unknown) => true,
                    (CompTypeView::With(a), CompTypeView::With(b)) => {
                        if a.len() == b.len() {
                            pending.extend(a.iter().zip(b).map(|(&a, &b)| comps(a, b)));
                            true
                        }
                        else {
                            false
                        }
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
                                pending.push(Pairing::Values(
                                    Relocated::from(a.payload),
                                    Relocated::from(b.payload),
                                ));
                                pending.push(Pairing::Values(
                                    Relocated::from(a.reply),
                                    Relocated::from(b.reply),
                                ));
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
                    // A dependent arrow whose codomain ignores its binder is
                    // the plain arrow over the same children (#577): the
                    // arrow's codomain, read under the dependent arrow's
                    // binder, cannot name it, so the two codomains agree
                    // exactly when the dependent one does not use its binder.
                    (
                        CompTypeView::Pi {
                            domain: left_domain,
                            codomain: left_codomain,
                        },
                        CompTypeView::Arrow {
                            domain: right_domain,
                            codomain: right_codomain,
                        },
                    ) => {
                        let weakened =
                            shift_comp_type(context.arena_mut(), right_codomain, Binders::ONE);
                        pending.push(variance.comps(Relocated::from(left_codomain), weakened));
                        pending.push(values(right_domain, left_domain));
                        true
                    },
                    (
                        CompTypeView::Arrow {
                            domain: left_domain,
                            codomain: left_codomain,
                        },
                        CompTypeView::Pi {
                            domain: right_domain,
                            codomain: right_codomain,
                        },
                    ) => {
                        let weakened =
                            shift_comp_type(context.arena_mut(), left_codomain, Binders::ONE);
                        pending.push(variance.comps(weakened, Relocated::from(right_codomain)));
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
                        CompTypeView::Codata {
                            declaration: a,
                            arguments: left_arguments,
                        },
                        CompTypeView::Codata {
                            declaration: b,
                            arguments: right_arguments,
                        },
                    ) => {
                        if a != b || left_arguments.len() != right_arguments.len() {
                            return Ok(Agreement::Apart);
                        }
                        pending.extend(
                            left_arguments
                                .iter()
                                .zip(right_arguments)
                                .map(|(&a, &b)| Pairing::Terms(a, b)),
                        );
                        true
                    },
                    (
                        CompTypeView::Returner { .. }
                        | CompTypeView::With(..)
                        | CompTypeView::Arrow { .. }
                        | CompTypeView::Pi { .. }
                        | CompTypeView::Element { .. }
                        | CompTypeView::Codata { .. },
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
                                    pending.push(Pairing::Values(
                                        Relocated::from(*a),
                                        Relocated::from(*b),
                                    ));
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
                                    pending.push(Pairing::Values(
                                        Relocated::from(*left_quoted),
                                        Relocated::from(*right_quoted),
                                    ));
                                    true
                                }
                            }
                            else if let Value::QuoteComputation(ref left_quoted) =
                                *matched_left_value
                                && let Value::QuoteComputation(ref right_quoted) =
                                    *matched_right_value
                            {
                                {
                                    pending.push(Pairing::Comps(
                                        Relocated::from(*left_quoted),
                                        Relocated::from(*right_quoted),
                                    ));
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
                            // A dialogue is its endpoints' moves: two logs that
                            // interleave the same moves differently convert.
                            else if let Value::Dialogue(ref left_moves) = *matched_left_value
                                && let Value::Dialogue(ref right_moves) = *matched_right_value
                            {
                                let mut pairs = Vec::new();
                                let same = gandr_core_term::session::pair_dialogues(
                                    left_moves,
                                    right_moves,
                                    |left, right| pairs.push(Pairing::Codes(left, right)),
                                ) == CertificateEquality::Equal;
                                if same {
                                    pending.extend(pairs.into_iter().rev());
                                }
                                same
                            }
                            else if let Value::Web(ref left_pieces) = *matched_left_value
                                && let Value::Web(ref right_pieces) = *matched_right_value
                            {
                                left_pieces == right_pieces
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
                                        | Value::Dialogue(_)
                                        | Value::Web(_)
                                        | Value::Funext(..)
                                        | Value::Equiv(..)
                                        | Value::Univalence(..)
                                        | Value::Ua { .. }
                                        | Value::Returned(_)
                                        | Value::Nested(_)
                                        | Value::Run(_)
                                        | Value::RecordUpdate { .. }
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
                                        | Value::Ascribe { .. }
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

/// `side` at its weak head, as [`CheckingContext::whnf_value_type`] reads a
/// plain type: a relocated side whose former is already a weak head stays
/// relocated, and one at a decode or a sealed atom is settled first, since an
/// unfolding is certified beneath the context's binders.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a plain side's weak head, plain; a relocated side itself when its
///   node is neither a decode nor an atom; otherwise the weak head of the side
///   settled.
/// - fails: as [`CheckingContext::whnf_value_type`], and the view's refusal for
///   a node outside the fragment.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — a relocated decode, a relocated former and a plain type
///   each converted against their settled readings.
/// - witness: `conversion::tests::a_relocated_type_converts_as_its_settled_reading`
#[spec(ensures: |ret| ret.is_err() || side.relocation() != Relocation::IDENTITY
    || ret.as_ref().is_ok_and(|head| head.relocation() == Relocation::IDENTITY))]
fn value_head(
    context: &mut CheckingContext<'_>,
    side: Relocated<ValueTypeId>,
) -> Result<Relocated<ValueTypeId>, CheckRefusal>
{
    if side.relocation() == Relocation::IDENTITY {
        return Ok(Relocated::from(context.whnf_value_type(side.node())?));
    }
    match value_type_view(context.arena(), side.node())? {
        ValueTypeView::Element { .. } | ValueTypeView::Abstract(_) => {
            let settled = side.settle(context.arena_mut());
            Ok(Relocated::from(context.whnf_value_type(settled)?))
        },
        ValueTypeView::Data { .. }
        | ValueTypeView::Record(_)
        | ValueTypeView::Stack { .. }
        | ValueTypeView::PathUniverse(..)
        | ValueTypeView::Path { .. }
        | ValueTypeView::Flow { .. }
        | ValueTypeView::Run(_)
        | ValueTypeView::Prefix(_)
        | ValueTypeView::Dialogue(_)
        | ValueTypeView::Web
        | ValueTypeView::Sum(_)
        | ValueTypeView::List(_)
        | ValueTypeView::Integer
        | ValueTypeView::String
        | ValueTypeView::Character
        | ValueTypeView::Float64
        | ValueTypeView::Fixed(_)
        | ValueTypeView::Unit
        | ValueTypeView::Thunk(_)
        | ValueTypeView::Universe { .. }
        | ValueTypeView::Lift { .. }
        | ValueTypeView::Product(_)
        | ValueTypeView::StaticPi { .. }
        | ValueTypeView::Sigma { .. }
        | ValueTypeView::Capability { .. }
        | ValueTypeView::Buffer
        | ValueTypeView::Session(_)
        | ValueTypeView::Staged { .. }
        | ValueTypeView::Kept { .. }
        | ValueTypeView::World(_)
        | ValueTypeView::Unknown => Ok(side),
    }
}

/// `side` at its weak head, as [`value_head`] reads a value type: a relocated
/// decode is settled before it unfolds.
///
/// # Specification
/// - requires: nothing.
/// - ensures: as [`value_head`], over computation types, a decode the one
///   former settled.
/// - fails: as [`CheckingContext::whnf_comp_type`], and the view's refusal for
///   a node outside the fragment.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — as [`value_head`].
/// - witness: `conversion::tests::a_relocated_type_converts_as_its_settled_reading`
#[spec(ensures: |ret| ret.is_err() || side.relocation() != Relocation::IDENTITY
    || ret.as_ref().is_ok_and(|head| head.relocation() == Relocation::IDENTITY))]
fn comp_head(
    context: &mut CheckingContext<'_>,
    side: Relocated<CompTypeId>,
) -> Result<Relocated<CompTypeId>, CheckRefusal>
{
    if side.relocation() == Relocation::IDENTITY {
        return Ok(Relocated::from(context.whnf_comp_type(side.node())?));
    }
    match comp_type_view(context.arena(), side.node())? {
        CompTypeView::Element { .. } => {
            let settled = side.settle(context.arena_mut());
            Ok(Relocated::from(context.whnf_comp_type(settled)?))
        },
        CompTypeView::With(..)
        | CompTypeView::Returner { .. }
        | CompTypeView::Arrow { .. }
        | CompTypeView::Pi { .. }
        | CompTypeView::Codata { .. }
        | CompTypeView::Unknown => Ok(side),
    }
}

/// Read two value types at their weak heads through the relocations they
/// carry, pushing the pairs beneath them each under its parent's relocation
/// and the binders its position crosses.
///
/// The formers read through are those whose comparison is a pair of types
/// beneath and a leaf: a decode is not, since its code is compared as a term,
/// nor a data type, a path, a session, a capability, a stage or a world, whose
/// comparisons read terms, protocols, grants or the stage order — the caller
/// settles those and compares them plain.
///
/// # Specification
/// - requires: both sides at their weak heads.
/// - ensures: [`through::Absent::Plain`] when neither side is relocated;
///   [`through::Absent::Unread`], pushing nothing, when a side is a decode or
///   the pair is not two of the formers read through; otherwise what the plain
///   walk answers for the settled pair, the pairs it would push carried
///   relocated in its order: the second factor of a dependent pair under one
///   more binder, every other child under its parent's relocation.
/// - fails: the view's refusal for a node outside the fragment.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — relocated products, records, sums, lists, thunks, stacks,
///   static and dependent pairs, universes and leaves, agreeing and differing,
///   each against its settled reading.
/// - witness: `conversion::tests::a_relocated_type_converts_as_its_settled_reading`
#[spec(ensures: |ret| !matches!(ret, Ok(Maybe::Absent(through::Absent::Plain)))
    || (left.relocation() == Relocation::IDENTITY && right.relocation() == Relocation::IDENTITY))]
fn relocated_values(
    arena: &CoreArena,
    (left, right): (Relocated<ValueTypeId>, Relocated<ValueTypeId>),
    variance: Variance,
    pending: &mut Vec<Pairing>,
) -> Result<Maybe<Read, through::Absent>, CheckRefusal>
{
    let (at_left, at_right) = (left.relocation(), right.relocation());
    if at_left == Relocation::IDENTITY && at_right == Relocation::IDENTITY {
        return Ok(Maybe::Absent(through::Absent::Plain));
    }
    let child = |id: ValueTypeId, at: Relocation| arena.place_value_type(id, at);
    let body = |id: CompTypeId, at: Relocation| arena.place_comp_type(id, at);
    let read = match (
        value_type_view(arena, left.node())?,
        value_type_view(arena, right.node())?,
    ) {
        (ValueTypeView::Element { .. }, _) | (_, ValueTypeView::Element { .. }) => {
            return Ok(Maybe::Absent(through::Absent::Unread));
        },
        (ValueTypeView::Unknown, _)
        | (_, ValueTypeView::Unknown)
        | (ValueTypeView::Integer, ValueTypeView::Integer)
        | (ValueTypeView::String, ValueTypeView::String)
        | (ValueTypeView::Character, ValueTypeView::Character)
        | (ValueTypeView::Float64, ValueTypeView::Float64)
        | (ValueTypeView::Unit, ValueTypeView::Unit) => Read::Pushed,
        (ValueTypeView::Fixed(left_width), ValueTypeView::Fixed(right_width))
            if left_width == right_width =>
        {
            Read::Pushed
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
        ) => {
            if left_sort == right_sort && left_level == right_level {
                Read::Pushed
            }
            else {
                Read::Apart
            }
        },
        (ValueTypeView::Thunk(left_body), ValueTypeView::Thunk(right_body)) => {
            pending.push(variance.comps(body(left_body, at_left), body(right_body, at_right)));
            Read::Pushed
        },
        (ValueTypeView::List(left_item), ValueTypeView::List(right_item)) => {
            pending.push(variance.values(child(left_item, at_left), child(right_item, at_right)));
            Read::Pushed
        },
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
            pending.push(variance.values(child(left_inner, at_left), child(right_inner, at_right)));
            if left_target == right_target {
                Read::Pushed
            }
            else {
                Read::Apart
            }
        },
        (ValueTypeView::Sum(left_parts), ValueTypeView::Sum(right_parts))
        | (ValueTypeView::Product(left_parts), ValueTypeView::Product(right_parts)) => {
            if left_parts.len() == right_parts.len() {
                pending.extend(left_parts.iter().zip(right_parts).rev().map(
                    |(&found, &wanted)| {
                        variance.values(child(found, at_left), child(wanted, at_right))
                    },
                ));
                Read::Pushed
            }
            else {
                Read::Apart
            }
        },
        (ValueTypeView::Record(left_fields), ValueTypeView::Record(right_fields)) => {
            if left_fields.len() == right_fields.len() && left_fields.keys().eq(right_fields.keys())
            {
                pending.extend(left_fields.values().zip(right_fields.values()).map(
                    |(&found, &wanted)| {
                        variance.values(child(found, at_left), child(wanted, at_right))
                    },
                ));
                Read::Pushed
            }
            else {
                Read::Apart
            }
        },
        (
            ValueTypeView::Stack {
                input: left_input,
                output: left_output,
            },
            ValueTypeView::Stack {
                input: right_input,
                output: right_output,
            },
        ) => {
            pending.extend([
                variance.comps(body(right_input, at_right), body(left_input, at_left)),
                variance.comps(body(left_output, at_left), body(right_output, at_right)),
            ]);
            Read::Pushed
        },
        (
            ValueTypeView::StaticPi {
                domain: left_domain,
                codomain: left_codomain,
            },
            ValueTypeView::StaticPi {
                domain: right_domain,
                codomain: right_codomain,
            },
        ) => {
            pending.push(variance.values(
                child(left_codomain, at_left),
                child(right_codomain, at_right),
            ));
            pending
                .push(variance.values(child(right_domain, at_right), child(left_domain, at_left)));
            Read::Pushed
        },
        // The second factors stand under one binder each, which a relocation
        // read beneath it passes over.
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
            pending.push(variance.values(
                child(left_second, at_left.under(Binders::ONE)),
                child(right_second, at_right.under(Binders::ONE)),
            ));
            pending.push(variance.values(child(left_first, at_left), child(right_first, at_right)));
            Read::Pushed
        },
        (
            ValueTypeView::Data { .. }
            | ValueTypeView::Record(_)
            | ValueTypeView::Stack { .. }
            | ValueTypeView::PathUniverse(..)
            | ValueTypeView::Path { .. }
            | ValueTypeView::Flow { .. }
            | ValueTypeView::Run(_)
            | ValueTypeView::Prefix(_)
            | ValueTypeView::Dialogue(_)
            | ValueTypeView::Web
            | ValueTypeView::Sum(_)
            | ValueTypeView::List(_)
            | ValueTypeView::Integer
            | ValueTypeView::String
            | ValueTypeView::Character
            | ValueTypeView::Float64
            | ValueTypeView::Fixed(_)
            | ValueTypeView::Unit
            | ValueTypeView::Thunk(_)
            | ValueTypeView::Universe { .. }
            | ValueTypeView::Lift { .. }
            | ValueTypeView::Product(_)
            | ValueTypeView::StaticPi { .. }
            | ValueTypeView::Sigma { .. }
            | ValueTypeView::Abstract(_)
            | ValueTypeView::Capability { .. }
            | ValueTypeView::Buffer
            | ValueTypeView::Session(_)
            | ValueTypeView::Staged { .. }
            | ValueTypeView::Kept { .. }
            | ValueTypeView::World(_),
            _,
        ) => return Ok(Maybe::Absent(through::Absent::Unread)),
    };
    Ok(Maybe::Present(read))
}

/// Read two computation types at their weak heads through the relocations
/// they carry, as [`relocated_values`] reads value types: the codomain of a
/// dependent arrow under one more binder, and a plain arrow's codomain against
/// a dependent one weakened past its binder by a root update.
///
/// # Specification
/// - requires: both sides at their weak heads.
/// - ensures: as [`relocated_values`], for lazy products, returners over the
///   empty row, and arrows of either kind; a returner over a row, a decode and
///   a codata type are [`through::Absent::Unread`].
/// - fails: the view's refusal for a node outside the fragment.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — relocated returners, arrows, dependent arrows and their
///   mixtures, agreeing and differing, each against its settled reading.
/// - witness: `conversion::tests::a_relocated_type_converts_as_its_settled_reading`
#[spec(ensures: |ret| !matches!(ret, Ok(Maybe::Absent(through::Absent::Plain)))
    || (left.relocation() == Relocation::IDENTITY && right.relocation() == Relocation::IDENTITY))]
fn relocated_comps(
    arena: &mut CoreArena,
    (left, right): (Relocated<CompTypeId>, Relocated<CompTypeId>),
    variance: Variance,
    pending: &mut Vec<Pairing>,
) -> Result<Maybe<Read, through::Absent>, CheckRefusal>
{
    let (at_left, at_right) = (left.relocation(), right.relocation());
    if at_left == Relocation::IDENTITY && at_right == Relocation::IDENTITY {
        return Ok(Maybe::Absent(through::Absent::Plain));
    }
    let read =
        match (
            comp_type_view(arena, left.node())?,
            comp_type_view(arena, right.node())?,
        ) {
            (CompTypeView::Element { .. } | CompTypeView::Codata { .. }, _)
            | (_, CompTypeView::Element { .. } | CompTypeView::Codata { .. }) => {
                return Ok(Maybe::Absent(through::Absent::Unread));
            },
            (CompTypeView::Unknown, _) | (_, CompTypeView::Unknown) => Read::Pushed,
            (CompTypeView::With(left_components), CompTypeView::With(right_components))
                if left_components.len() == right_components.len() =>
            {
                pending.extend(left_components.iter().zip(right_components).map(
                    |(&left, &right)| {
                        variance.comps(
                            arena.place_comp_type(left, at_left),
                            arena.place_comp_type(right, at_right),
                        )
                    },
                ));
                Read::Pushed
            },
            (
                CompTypeView::Returner {
                    result: left_result,
                    effects: left_effects,
                },
                CompTypeView::Returner {
                    result: right_result,
                    effects: right_effects,
                },
            ) if left_effects.signatures().len() == 0 => {
                if variance == Variance::Subtyping || right_effects.signatures().len() == 0 {
                    pending.push(variance.values(
                        arena.place_value_type(left_result, at_left),
                        arena.place_value_type(right_result, at_right),
                    ));
                    Read::Pushed
                }
                else {
                    Read::Apart
                }
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
            ) => {
                pending.push(variance.comps(
                    arena.place_comp_type(left_codomain, at_left),
                    arena.place_comp_type(right_codomain, at_right),
                ));
                pending.push(variance.values(
                    arena.place_value_type(right_domain, at_right),
                    arena.place_value_type(left_domain, at_left),
                ));
                Read::Pushed
            },
            (
                CompTypeView::Pi {
                    domain: left_domain,
                    codomain: left_codomain,
                },
                CompTypeView::Pi {
                    domain: right_domain,
                    codomain: right_codomain,
                },
            ) => {
                pending.push(variance.comps(
                    arena.place_comp_type(left_codomain, at_left.under(Binders::ONE)),
                    arena.place_comp_type(right_codomain, at_right.under(Binders::ONE)),
                ));
                pending.push(variance.values(
                    arena.place_value_type(right_domain, at_right),
                    arena.place_value_type(left_domain, at_left),
                ));
                Read::Pushed
            },
            (
                CompTypeView::Pi {
                    domain: left_domain,
                    codomain: left_codomain,
                },
                CompTypeView::Arrow {
                    domain: right_domain,
                    codomain: right_codomain,
                },
            ) => {
                let dependent = arena.place_comp_type(left_codomain, at_left.under(Binders::ONE));
                let plain = arena.place_comp_type(right_codomain, at_right);
                let weakened = shift_comp_type(arena, plain, Binders::ONE);
                pending.push(variance.comps(dependent, weakened));
                pending.push(variance.values(
                    arena.place_value_type(right_domain, at_right),
                    arena.place_value_type(left_domain, at_left),
                ));
                Read::Pushed
            },
            (
                CompTypeView::Arrow {
                    domain: left_domain,
                    codomain: left_codomain,
                },
                CompTypeView::Pi {
                    domain: right_domain,
                    codomain: right_codomain,
                },
            ) => {
                let plain = arena.place_comp_type(left_codomain, at_left);
                let weakened = shift_comp_type(arena, plain, Binders::ONE);
                let dependent = arena.place_comp_type(right_codomain, at_right.under(Binders::ONE));
                pending.push(variance.comps(weakened, dependent));
                pending.push(variance.values(
                    arena.place_value_type(right_domain, at_right),
                    arena.place_value_type(left_domain, at_left),
                ));
                Read::Pushed
            },
            (
                CompTypeView::Returner { .. }
                | CompTypeView::With(..)
                | CompTypeView::Arrow { .. }
                | CompTypeView::Pi { .. },
                _,
            ) => return Ok(Maybe::Absent(through::Absent::Unread)),
        };
    Ok(Maybe::Present(read))
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

/// The verdict on `left` and `right` when one of them is a hole or a mark: a
/// metavariable among them is posed to the solver against the other side.
///
/// # Specification
/// - requires: both values are read at one type in the context's open binders.
/// - ensures: [`open::Absent::Closed`] when neither side is a hole or a mark;
///   otherwise the solver's verdict on the equation, which is
///   [`crate::elaboration::Unified::Refuted`] only when a side is a
///   metavariable the other refutes, the solution or the postponed equation
///   left in the context's store.
/// - fails: [`CheckRefusal::DanglingNode`] for an id the arena does not hold; a
///   machine invariant as [`CheckingContext::unify_values`] raises it.
/// - panics: none.
/// - executable: none — the verdict is the solver's, which
///   [`crate::elaboration::Deferrals::unify_values`] specifies.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — a path type's open end met at the value bridge against a
///   known end is solved to it; a hole no judgement nominated stays unknown.
/// - witness: `bridge::tests::an_ascription_solves_the_wildcard_its_type_holds_1979`
/// - witness: `conversion::tests::the_unknown_type_is_consistent_beside_a_differing_former`
fn pose_open(
    context: &mut CheckingContext<'_>,
    left: ValueId,
    right: ValueId,
) -> Result<Maybe<crate::elaboration::Unified, open::Absent>, CheckRefusal>
{
    if root_knowledge(context, left)? == Knowledge::Known
        && root_knowledge(context, right)? == Knowledge::Known
    {
        return Ok(Maybe::Absent(open::Absent::Closed));
    }
    Ok(Maybe::Present(context.unify_values(left, right)?))
}

#[cfg(test)]
mod tests;
