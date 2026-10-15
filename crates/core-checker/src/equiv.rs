//! Universe equivalences in the core: `equiv(f, g)`, decided by computation
//! and admitted by the kernel as the native universe path it relates.
//!
//! # The rule
//!
//! `equiv(f, g)` synthesises `Path(Type, ⌜A⌝, ⌜B⌝)` when `f` synthesises the
//! thunk type `U (A → F B)` of a pure non-dependent arrow, `g` checks against
//! `U (B → F A)`, both translators are closed, `A` and `B` are codes of the
//! native universe-path vocabulary, and both round trips return their input.
//! The vocabulary is the unit type, the base atoms, sums of at least one
//! summand and products of any arity. A round trip is decided at every pattern
//! the code's coverage reaches: the unit value, a fresh variable at a base
//! atom, each summand's patterns injected, and each tuple of the components'
//! patterns, an earlier component read past a later one's binders. At a
//! pattern `p` standing under its binders, `x ← f p; g x` must convert to
//! `return p`, every admitted definition unfolding and every binder read as a
//! rigid variable.
//!
//! A round trip that does not convert is [`CheckRefusal::RoundTripDistinct`]:
//! the rule admits what it shows and refutes nothing it cannot. A List code
//! is [`CheckRefusal::UncertifiedStratum`]: its inhabitants are unbounded, so
//! no finite coverage certifies a round trip over it. Open translators, a
//! classifier that is no thunk of a pure non-dependent arrow, and a code
//! outside the vocabulary are [`CheckRefusal::EquivUnsupported`].
//!
//! The judgement records, for each `equiv` it accepts, the native classifier
//! `Path_U(⌜A⌝, ⌜B⌝)` and the machine's trace of every round trip, source
//! patterns then target ones. The kernel's identity at the value universe is
//! its native universe path, so the bridge erases the `equiv` to the kernel's
//! certificate over the two quotes with that trace as its evidence; admission
//! regenerates the coverage and replays each dialogue under the definitions
//! it admitted, and trusts nothing the core decided.
//!
//! # Decisions
//!
//! - **Decided by computation.** The choice is the kernel's own round-trip
//!   coverage, evaluated by the normaliser at check time. The alternatives were
//!   a postulated univalence, which no kernel rule replays, and equivalence up
//!   to a written inverse proof, which would ask the surface for homotopies the
//!   kernel cannot read. Reversal: none while the kernel's universe path
//!   certifies by replayed round trips.
//! - **The identity at the universe, not a second path type.** `equiv` inhabits
//!   `Path(Type, A, B)`, the element identity whose fibre the kernel computes
//!   as its universe path, so transport along it is element transport in any
//!   motive over the universe. The alternative was a written `Path_U` former
//!   beside it, which element transport would not read and the surface would
//!   spell twice. Reversal: a universe stratum whose fibre is not the native
//!   universe path.
//! - **Synthesised from its forward translator.** `f` names both codes, so the
//!   backward translator checks against the arrow they determine. Reversal: a
//!   checking rule against `Path(Type, A, B)` reads the codes from the expected
//!   type instead, and admits a λ as the forward translator.
//! - **Recursive codes refused by name.** The stratum of unbounded codes ends
//!   the vocabulary, as it ends the kernel's. Reversal: a guarded round-trip
//!   discipline that certifies an unobserved tail.

use alloc::sync::Arc;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Binders;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::effect::Purity;
use gandr_kernel_conversion_trace::ConversionDecision;
use gandr_kernel_core::ReplayBudget;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::PathEvidence;
use quenchant_shape::shape::Maybe;

use crate::code::OpenBinders;
use crate::code::loose_reach;
use crate::context::CheckingContext;
use crate::refusal::CheckRefusal;
use crate::refusal::CoreNode;
use crate::refusal::TermNode;
use crate::view::CompTypeView;
use crate::view::ValueTypeView;
use crate::view::comp_type_view;
use crate::view::value_type_view;

#[cfg(test)]
mod tests;

/// A universe equivalence the judgement decided: the native classifier the
/// bridge erases it at, and the evidence of its round trips.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Equivalence
{
    /// The quote of the source code.
    source: ValueId,
    /// The quote of the target code.
    target: ValueId,
    /// The native classifier `Path_U(⌜A⌝, ⌜B⌝)`.
    classifier: ValueTypeId,
    /// The machine's trace of every round trip, in coverage order.
    evidence: Arc<PathEvidence>,
}

impl Equivalence
{
    /// The native classifier `Path_U(⌜A⌝, ⌜B⌝)` the bridge erases the
    /// equivalence at.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn classifier(&self) -> ValueTypeId
    {
        self.classifier
    }

    /// The machine's trace of every round trip: backward after forward at
    /// each source pattern, forward after backward at each target one.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn evidence(&self) -> &Arc<PathEvidence>
    {
        &self.evidence
    }

    /// The identity the equivalence inhabits, `Path(Type, ⌜A⌝, ⌜B⌝)`.
    ///
    /// # Specification
    /// - ensures: a path type over the value universe at level zero whose
    ///   endpoints are the two quotes the classifier relates.
    /// - panics: none.
    /// - executable: none — the minted node is checked by the judgement that
    ///   compares it against the type it is checked at.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — negation's equivalence synthesises the identity at
    ///   the universe between the two quotes of Bool.
    /// - witness: `equiv::tests::an_involution_is_its_own_inverse_by_computation`
    #[inline]
    pub fn identity(
        &self,
        arena: &mut CoreArena,
    ) -> ValueTypeId
    {
        let universe = arena.value_type_universe(
            gandr_core_term::Sort::Ground(gandr_kernel_term::GroundSort::Value),
            gandr_kernel_strata::Level::zero(),
        );
        arena.value_type_path(universe, self.source, self.target)
    }
}

/// One pattern of a code's coverage, standing under its own binders.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Pattern
{
    /// How many pattern binders the pattern stands under.
    binders: u32,
    /// The pattern.
    value: ValueId,
}

impl Pattern
{
    /// How many pattern binders the pattern stands under.
    ///
    /// # Specification
    /// trivial.
    pub const fn binders(self) -> OpenBinders
    {
        OpenBinders(self.binders)
    }

    /// The pattern, standing under its binders.
    ///
    /// # Specification
    /// trivial.
    pub const fn value(self) -> ValueId
    {
        self.value
    }
}

/// A coverage task: a type to cover, or a former whose part coverages are
/// ready to join.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Task
{
    /// Cover the type.
    Cover(ValueTypeId),
    /// Inject the coverages of this many summands, the last on top.
    Sum(usize),
    /// Cross the coverages of this many components, the last on top.
    Product(usize),
}

/// The two codes the classifier of an equivalence's forward translator names:
/// `U (A → F B)` gives `(A, B)`.
///
/// # Specification
/// - requires: `classifier` is the type the forward translator synthesised.
/// - ensures: the domain and the result of the pure non-dependent arrow the
///   classifier is the thunk of, read at their weak heads.
/// - fails: [`CheckRefusal::EquivUnsupported`] at `at` for a classifier that is
///   no thunk of a pure non-dependent arrow; a weak-head or view refusal as
///   those raise it.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — negation names Bool twice, and a translator returning a
///   thunk names its result.
/// - witness: `equiv::tests::an_involution_is_its_own_inverse_by_computation`
/// - witness: `equiv::tests::what_the_rule_cannot_show_it_refuses_by_name`
#[spec(ensures: |ret| match ret {
    | Err(CheckRefusal::EquivUnsupported { at: site, classifier: found }) => site == at && found == classifier,
    | Ok(_) | Err(_) => true,
})]
pub fn codes(
    context: &mut CheckingContext<'_>,
    at: ValueId,
    classifier: ValueTypeId,
) -> Result<(ValueTypeId, ValueTypeId), CheckRefusal>
{
    let unsupported = CheckRefusal::EquivUnsupported { at, classifier };
    let head = context.whnf_value_type(classifier)?;
    let ValueTypeView::Thunk(computation) = value_type_view(context.arena(), head)?
    else {
        return Err(unsupported);
    };
    let computation = context.whnf_comp_type(computation)?;
    let CompTypeView::Arrow { domain, codomain } = comp_type_view(context.arena(), computation)?
    else {
        return Err(unsupported);
    };
    let codomain = context.whnf_comp_type(codomain)?;
    match comp_type_view(context.arena(), codomain)? {
        CompTypeView::Returner { result, effects } if effects.purity() == Purity::Pure => {
            Ok((domain, result))
        },
        CompTypeView::With(..)
        | CompTypeView::Returner { .. }
        | CompTypeView::Arrow { .. }
        | CompTypeView::Pi { .. }
        | CompTypeView::Element { .. }
        | CompTypeView::Unknown => Err(unsupported),
    }
}

/// The translator type `U (from → F to)`.
///
/// # Specification
/// trivial.
pub fn translator(
    context: &mut CheckingContext<'_>,
    (from, to): (ValueTypeId, ValueTypeId),
) -> ValueTypeId
{
    let arena = context.arena_mut();
    let returner = arena.comp_type_returner(to);
    let arrow = arena.comp_type_arrow(from, returner);
    arena.value_type_thunk(arrow)
}

/// Decide `equiv(f, g)` between the codes `(A, B)` the forward translator
/// named, `g` already checked against `U (B → F A)`.
///
/// # Specification
/// - requires: `forward` synthesised `U (A → F B)`; `backward` checked against
///   `U (B → F A)`; both stand under the judgement's binders.
/// - ensures: on success the classifier `Path_U(⌜A⌝, ⌜B⌝)` and one dialogue per
///   pattern of `A`'s coverage and then of `B`'s, in the kernel's order, each
///   the machine's trace that the round trip at that pattern converts to
///   returning it.
/// - provides: the decision the judgement's `equiv` rule makes and the record
///   the bridge erases.
/// - fails: [`CheckRefusal::EquivUnsupported`] at `at` for open translators, a
///   code outside the unit type, the base atoms, sums of at least one summand
///   and products, or a coverage past the kernel's allowance;
///   [`CheckRefusal::UncertifiedStratum`] at `at` naming the first List code
///   either code reaches; [`CheckRefusal::RoundTripDistinct`] at `at` when a
///   round trip does not convert to returning its input; a weak-head, view or
///   machine refusal as those raise it.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Termination
/// - reason: the coverage is a `while let` worklist over each code's finite
///   tree and the round trips `for` loops over its patterns, not recursion.
/// - measure: the tasks left, bounded by the kernel's coverage allowance; then
///   the patterns left.
///
/// # Adequacy
/// - hypothesis: L3 — negation is its own inverse at both injections; the
///   identity and negation are not inverse; a translator out of a list and an
///   open translator refuse by name.
/// - witness: `equiv::tests::an_involution_is_its_own_inverse_by_computation`
/// - witness: `equiv::tests::what_the_rule_cannot_show_it_refuses_by_name`
#[spec(ensures: |ret| match ret {
    | Err(CheckRefusal::EquivUnsupported { at: site, .. } | CheckRefusal::UncertifiedStratum { at: site, .. } | CheckRefusal::RoundTripDistinct { at: site }) => site == at,
    | Ok(ref decided) => decided.evidence.source.len().saturating_add(decided.evidence.target.len()) >= 2,
    | Err(_) => true,
})]
pub fn decide(
    context: &mut CheckingContext<'_>,
    at: ValueId,
    (forward, backward): (ValueId, ValueId),
    (source, target): (ValueTypeId, ValueTypeId),
) -> Result<Equivalence, CheckRefusal>
{
    for translator in [forward, backward] {
        let reach = loose_reach(context.arena(), CoreNode::Term(TermNode::Value(translator)))?;
        if usize::from(reach) != 0 {
            return Err(CheckRefusal::EquivUnsupported {
                at,
                classifier: source,
            });
        }
    }
    let evidence = PathEvidence {
        source: round_trips(context, at, source, (forward, backward))?,
        target: round_trips(context, at, target, (backward, forward))?,
    };
    let arena = context.arena_mut();
    let source = arena.value_quote(source);
    let target = arena.value_quote(target);
    let classifier = arena.value_type_path_universe(source, target);
    Ok(Equivalence {
        source,
        target,
        classifier,
        evidence: Arc::new(evidence),
    })
}

/// The round trips at every pattern of `code`'s coverage: `first`, then
/// `second`, each traced against returning the pattern.
///
/// # Specification
/// - requires: as [`decide`], `first` translating out of `code`.
/// - ensures: one dialogue per pattern, in coverage order, each the machine's
///   trace that `x ← first p; second x` converts to `return p`.
/// - fails: as [`decide`] for this one side.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Termination
/// - reason: a `for` loop over the finite coverage, not recursion.
/// - measure: the patterns left.
///
/// # Adequacy
/// - hypothesis: L3 — as [`decide`]; an equivalence of a code with itself
///   carries both sides' round trips.
/// - witness: `equiv::tests::an_involution_is_its_own_inverse_by_computation`
#[spec(ensures: |ret| match ret {
    | Err(CheckRefusal::EquivUnsupported { at: site, .. } | CheckRefusal::UncertifiedStratum { at: site, .. } | CheckRefusal::RoundTripDistinct { at: site }) => site == at,
    | Ok(ref dialogues) => !dialogues.is_empty(),
    | Err(_) => true,
})]
fn round_trips(
    context: &mut CheckingContext<'_>,
    at: ValueId,
    code: ValueTypeId,
    (first, second): (ValueId, ValueId),
) -> Result<Vec<Vec<ConversionDecision<()>>>, CheckRefusal>
{
    let Maybe::Present(patterns) = coverage(context, at, code)?
    else {
        return Err(CheckRefusal::EquivUnsupported {
            at,
            classifier: code,
        });
    };
    let mut dialogues = Vec::with_capacity(patterns.len());
    for pattern in patterns {
        let arena = context.arena_mut();
        let forced = arena.computation_force(first);
        let there = arena.computation_application(forced, pattern.value);
        let forced = arena.computation_force(second);
        let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let back = arena.computation_application(forced, bound);
        let round = arena.computation_bind(there, back);
        let returned = arena.computation_return(pattern.value);
        let traced =
            context.trace_conversion(at, (round, returned), OpenBinders(pattern.binders))?;
        let Maybe::Present(dialogue) = traced
        else {
            return Err(CheckRefusal::RoundTripDistinct { at });
        };
        dialogues.push(dialogue);
    }
    Ok(dialogues)
}

/// The coverage of `code`, as the kernel's universe-path patterns lay it out:
/// the unit value; one fresh variable at a base atom; each summand's patterns
/// injected, the first summand first; and each tuple crossing the components'
/// patterns lexicographically, an earlier component read past a later one's
/// binders.
///
/// # Specification
/// - requires: `code` is formed under the judgement's binders.
/// - ensures: the patterns in the kernel's order, or nothing when a type in the
///   tree is outside the unit type, the base atoms, sums of at least one
///   summand and products, or when the work passes the kernel's allowance.
/// - fails: [`CheckRefusal::UncertifiedStratum`] at `at` naming the first List
///   code the walk reaches; a weak-head or view refusal as those raise it.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Termination
/// - reason: a `while let` worklist over the finite type tree, not recursion.
/// - measure: the tasks left, each cover task replaced by strictly smaller
///   ones, every turn charged against the allowance.
///
/// # Adequacy
/// - hypothesis: L3 — a sum of two units covers as its two injections in order,
///   a list refuses by its stratum, and a thunk type covers as nothing.
/// - witness: `equiv::tests::an_involution_is_its_own_inverse_by_computation`
/// - witness: `equiv::tests::what_the_rule_cannot_show_it_refuses_by_name`
#[spec(ensures: |ret| match ret {
    | Ok(Maybe::Present(ref patterns)) => !patterns.is_empty()
        && patterns.iter().all(|pattern| context.arena().value(pattern.value).is_some()),
    | Err(CheckRefusal::UncertifiedStratum { at: site, .. }) => site == at,
    | Ok(Maybe::Absent(_)) | Err(_) => true,
})]
pub fn coverage(
    context: &mut CheckingContext<'_>,
    at: ValueId,
    code: ValueTypeId,
) -> Result<Maybe<Vec<Pattern>, uncovered::Absent>, CheckRefusal>
{
    let mut allowance = u64::from(ReplayBudget::DEFAULT);
    let mut tasks = Vec::from([Task::Cover(code)]);
    let mut built: Vec<Vec<Pattern>> = Vec::new();
    while let Some(task) = tasks.pop() {
        let Some(left) = allowance.checked_sub(1)
        else {
            return Ok(Maybe::Absent(uncovered::Absent::Allowance));
        };
        allowance = left;
        match task {
            Task::Cover(ty) => {
                let head = context.whnf_value_type(ty)?;
                match value_type_view(context.arena(), head)? {
                    ValueTypeView::Unit => {
                        let unit = context.arena_mut().value_tuple(&[]);
                        built.push(Vec::from([Pattern {
                            binders: 0,
                            value: unit,
                        }]));
                    },
                    ValueTypeView::Integer | ValueTypeView::String => {
                        let leaf = context
                            .arena_mut()
                            .value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
                        built.push(Vec::from([Pattern {
                            binders: 1,
                            value: leaf,
                        }]));
                    },
                    ValueTypeView::Sum(parts) if !parts.is_empty() => {
                        tasks.push(Task::Sum(parts.len()));
                        tasks.extend(parts.iter().rev().copied().map(Task::Cover));
                    },
                    ValueTypeView::Product(parts) => {
                        tasks.push(Task::Product(parts.len()));
                        tasks.extend(parts.iter().rev().copied().map(Task::Cover));
                    },
                    ValueTypeView::List(_) => {
                        return Err(CheckRefusal::UncertifiedStratum { at, code: head });
                    },
                    ValueTypeView::Data { .. }
                    | ValueTypeView::Record(_)
                    | ValueTypeView::Stack { .. }
                    | ValueTypeView::PathUniverse(..)
                    | ValueTypeView::Path { .. }
                    | ValueTypeView::Flow { .. }
                    | ValueTypeView::Run(_)
                    | ValueTypeView::Sum(_)
                    | ValueTypeView::Thunk(_)
                    | ValueTypeView::Universe { .. }
                    | ValueTypeView::Lift { .. }
                    | ValueTypeView::Element { .. }
                    | ValueTypeView::StaticPi { .. }
                    | ValueTypeView::Sigma { .. }
                    | ValueTypeView::Abstract(_)
                    | ValueTypeView::Capability { .. }
                    | ValueTypeView::Session(_)
                    | ValueTypeView::Unknown => {
                        return Ok(Maybe::Absent(uncovered::Absent::Former));
                    },
                }
            },
            Task::Sum(arity) => {
                let start = built
                    .len()
                    .checked_sub(arity)
                    .ok_or(CheckRefusal::MachineInvariant)?;
                let mut joined = Vec::new();
                for (summand, branch) in built.drain(start ..).enumerate() {
                    for pattern in branch {
                        let Some(left) = allowance.checked_sub(1)
                        else {
                            return Ok(Maybe::Absent(uncovered::Absent::Allowance));
                        };
                        allowance = left;
                        let value = context
                            .arena_mut()
                            .value_injection(summand.into(), pattern.value);
                        joined.push(Pattern { value, ..pattern });
                    }
                }
                built.push(joined);
            },
            // Each step crosses the tuples so far with the next component's
            // patterns; the earlier components' variables shift past the new
            // component's, so every variable stays distinct.
            Task::Product(arity) => {
                let start = built
                    .len()
                    .checked_sub(arity)
                    .ok_or(CheckRefusal::MachineInvariant)?;
                let components: Vec<Vec<Pattern>> = built.drain(start ..).collect();
                let mut tuples = Vec::from([(Vec::<ValueId>::new(), 0_u32)]);
                for component in components {
                    let mut crossed = Vec::new();
                    for &(ref prefix, binders) in &tuples {
                        for next in &component {
                            let Some(left) = allowance.checked_sub(1)
                            else {
                                return Ok(Maybe::Absent(uncovered::Absent::Allowance));
                            };
                            allowance = left;
                            let binders = binders
                                .checked_add(next.binders)
                                .ok_or(CheckRefusal::MachineInvariant)?;
                            let arena = context.arena_mut();
                            let mut values = Vec::with_capacity(prefix.len().saturating_add(1));
                            for &earlier in prefix {
                                values.push(gandr_core_term::shift_value(
                                    arena,
                                    earlier,
                                    Binders::from(next.binders),
                                ));
                            }
                            values.push(next.value);
                            crossed.push((values, binders));
                        }
                    }
                    tuples = crossed;
                }
                let arena = context.arena_mut();
                let joined = tuples
                    .into_iter()
                    .map(|(values, binders)| Pattern {
                        binders,
                        value: arena.value_tuple(&values),
                    })
                    .collect();
                built.push(joined);
            },
        }
    }
    match (built.pop(), built.is_empty()) {
        (Some(patterns), true) => Ok(Maybe::Present(patterns)),
        _ => Err(CheckRefusal::MachineInvariant),
    }
}

quenchant_shape::reason_enum! {
    /// Why a code has no coverage the rule decides over.
    pub mod uncovered {
        /// The reason the coverage stopped.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// A type in the tree is outside the unit type, the base atoms,
            /// sums of at least one summand and products.
            Former,
            /// The coverage outgrew the kernel's allowance.
            Allowance,
        }
    }
}
