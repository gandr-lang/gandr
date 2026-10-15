//! **Conversion**: structural comparison of two types, descending into the
//! terms they carry, with the id-equality fast path above it.
//!
//! # What the relation is, precisely
//!
//! The checker invokes conversion at a mode switch — when a synthesizing term
//! is used where a type is expected. Over this vocabulary the definitional
//! equality that needs is **type conversion only**, and it is exactly:
//!
//! - an **id-equality fast path**, which is **positive only**: a readable id
//!   names one node in its arena, so an equal pair is discharged. An unreadable
//!   equal pair refuses. Two *different* ids decide nothing and fall through to
//!   the structural walk. The fast path decides readable reflexive pairs alone;
//!   the kernel preserves the sharing a decode handed it rather than creating
//!   more.
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
//! # A returned endpoint compares by its computation, or waits to be read
//!
//! Two returned endpoints compare by their computations, structurally, as two
//! thunks do; a returned endpoint against any other former is apart here,
//! because what it returns is a reduction and none fires. The checker's mode
//! switches and reflexivity ask the walk to set such a pair aside instead,
//! through [`pending_endpoints`], and read each pair by the replay's own
//! reduction ([`crate::replay::read_endpoints`]). Where that reading leaves a
//! definition's types apart, [`related_pairs`] sets aside every path type's
//! endpoint pair as well, for the dialogues the definition carries
//! ([`crate::element_identity::related_endpoints`]). The walk itself still
//! reduces nothing: the pairs it sets aside are the only place a reading
//! enters, and every other pair is decided as before.
//!
//! # Fail-closed on an unreadable id
//!
//! A child id resolves under the arena's minting invariant. Every examined
//! pair, including an equal-id pair, must have readable roots. A failed checked
//! read answers [`Convertibility::Distinct`]. Identity does not recursively
//! validate descendants: the arena's child-before-parent invariant supplies
//! their validity.
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
pub(crate) enum ConversionGoal
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

/// A pair the walk set aside, unread, for its caller to read.
///
/// # Specification
/// - requires: nothing; the ids are the walk's own, read in its arena.
/// - ensures: the variant names how the caller reads the pair.
/// - provides: the one list a mode switch, reflexivity and a definition's
///   relations read.
/// - fails: none as a data value.
/// - panics: none as a data value.
///
/// # Adequacy
/// - hypothesis: L3 — a returned endpoint, a decode of a returned code against
///   another former and a path type's endpoint pair are each set aside as the
///   variant that reads them.
/// - witness: `conv::tests::related_pairs_set_aside_path_endpoints`
/// - witness: `conv::tests::a_decode_of_a_returned_code_is_set_aside_against_another_former`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum SetAside
{
    /// Two values, one of them a returned endpoint or a presented type's
    /// constructor, or a path type's endpoint pair the walk relates.
    Values(ValueId, ValueId),
    /// A value type decoded from a returned code, `El(⟨c⟩)`, against a value
    /// type of another former: what the code's computation returns is read,
    /// and the type a quote it returns quotes is compared with `other`.
    Decoded
    {
        /// The returned code the decode reads.
        code: ValueId,
        /// The value type on the other side.
        other: ValueTypeId,
    },
}

/// What the walk does with a value pair one of whose sides is a returned
/// endpoint or a presented type's constructor, and with a value type decoded
/// from a returned code against a value type of another former.
#[derive(Debug)]
enum Endpoints<'pending>
{
    /// Decide it as every other pair: two returned endpoints by their
    /// computations, a returned endpoint against any other former apart, two
    /// constructors by their tags and fields, a decode against another former
    /// apart.
    Structural,
    /// Set it aside, unread, for the caller to read; a presented type's
    /// constructor is read by the types `presentations` names.
    Deferred
    {
        /// The pairs set aside.
        pending: &'pending mut Vec<SetAside>,
        /// The presented types whose constructors are set aside.
        presentations: &'pending crate::presented::Presentations,
    },
    /// Set it aside as [`Endpoints::Deferred`] does, and set aside every
    /// pair of path endpoints too, for the caller to relate.
    Related
    {
        /// The pairs set aside.
        pending: &'pending mut Vec<SetAside>,
        /// The presented types whose constructors are set aside.
        presentations: &'pending crate::presented::Presentations,
    },
}

/// Decide convertibility of two value types in one arena.
///
/// # Specification
/// - requires: nothing — an unreadable id is admissible input and fails closed.
/// - ensures: [`Convertibility::Convertible`] exactly when readable roots are
///   equal up to this subset's definitional equality. On valid arena graphs the
///   relation is reflexive, symmetric and transitive.
/// - provides: the type equality the checker invokes at a value mode switch.
///   The predicate checks root readability, readable identity and head
///   separation; the structural walk and its relational laws have the witnesses
///   below rather than a second implementation in the predicate.
/// - fails: never — a negative answer is [`Convertibility::Distinct`] rather
///   than an error.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1/L2/L3 — root readability, readable reflexivity and head
///   separation are executable. The finite witnesses separate every value-type
///   former, all three base atoms, canonical levels, nominal atoms and selected
///   term forms; equal content at distinct ids still converts. They do not
///   enumerate all graphs or establish the relational laws by exhaustive
///   testing.
/// - witness: `conv::tests::value_type_conversion_is_reflexive`
/// - witness: `conv::tests::structurally_equal_types_at_distinct_ids_convert`
/// - witness: `conv::tests::conversion_separates_every_former`
/// - witness: `conv::tests::universes_convert_by_canonical_level`
/// - witness: `conv::tests::sealed_atoms_are_nominal`
/// - witness: `conv::tests::types_read_off_codes_converge_with_their_codes`
/// - witness: `conv::tests::code_comparison_separates_selected_term_forms_without_reducing`
/// - witness: `conv::tests::identity_requires_a_readable_root_in_every_family`
#[inline]
#[must_use]
#[spec(ensures: |ret| match (arena.value_type(left), arena.value_type(right)) {
    (Some(one), Some(other)) => if left == right {
        ret == Convertibility::Convertible
    } else {
        ret == Convertibility::Distinct
            || core::mem::discriminant(one) == core::mem::discriminant(other)
    },
    _ => ret == Convertibility::Distinct,
})]
pub fn convertible_value_types(
    arena: &TermArena,
    left: ValueTypeId,
    right: ValueTypeId,
) -> Convertibility
{
    converge(
        arena,
        ConversionGoal::ValueType(left, right),
        Endpoints::Structural,
    )
}

/// Decide convertibility of two computation types in one arena.
///
/// # Specification
/// - requires: nothing — an unreadable id is admissible input and fails closed.
/// - ensures: [`Convertibility::Convertible`] exactly when readable roots are
///   equal up to this subset's definitional equality; reflexive, symmetric and
///   transitive on valid arena graphs.
/// - provides: the type equality at a computation mode switch or a case's
///   branch convergence. Its predicate checks the same root-level projection as
///   [`convertible_value_types`]; child equality remains witnessed.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1/L2/L3 — unreadable identity and either unreadable side
///   refuse, while readable identity converts. Arrow and dependent-arrow
///   witnesses separate heads and each child position; these finite cases do
///   not exhaust computation graphs.
/// - witness: `conv::tests::computation_type_conversion_is_reflexive`
/// - witness: `conv::tests::an_arrow_separates_on_either_child`
/// - witness: `conv::tests::the_two_arrows_never_convert_across`
/// - witness: `conv::tests::identity_requires_a_readable_root_in_every_family`
#[inline]
#[must_use]
#[spec(ensures: |ret| match (arena.comp_type(left), arena.comp_type(right)) {
    (Some(one), Some(other)) => if left == right {
        ret == Convertibility::Convertible
    } else {
        ret == Convertibility::Distinct
            || core::mem::discriminant(one) == core::mem::discriminant(other)
    },
    _ => ret == Convertibility::Distinct,
})]
pub fn convertible_comp_types(
    arena: &TermArena,
    left: CompTypeId,
    right: CompTypeId,
) -> Convertibility
{
    converge(
        arena,
        ConversionGoal::CompType(left, right),
        Endpoints::Structural,
    )
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
/// - hypothesis: L1/L3 — the root predicate and four-family truncation witness
///   cover unreadable identity and either unreadable side. Selected term-form
///   counterexamples and replay closures exercise structural comparison; they
///   do not enumerate every value graph.
/// - witness: `conv::tests::code_comparison_separates_selected_term_forms_without_reducing`
/// - witness: `replay::tests::a_compared_pair_closes_on_alpha_equality_or_rigid_separation`
/// - witness: `conv::tests::identity_requires_a_readable_root_in_every_family`
#[inline]
#[must_use]
#[spec(ensures: |ret| match (arena.value(left), arena.value(right)) {
    (Some(one), Some(other)) => if left == right {
        ret == Convertibility::Convertible
    } else {
        ret == Convertibility::Distinct
            || core::mem::discriminant(one) == core::mem::discriminant(other)
    },
    _ => ret == Convertibility::Distinct,
})]
pub(crate) fn equal_values(
    arena: &TermArena,
    left: ValueId,
    right: ValueId,
) -> Convertibility
{
    converge(
        arena,
        ConversionGoal::Value(left, right),
        Endpoints::Structural,
    )
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
/// - hypothesis: L1/L3 — the four-family witness covers readable identity and
///   unreadability on either side; replay closures cover representative
///   alpha-equality and rigid separation, not every computation graph.
/// - witness: `replay::tests::a_compared_pair_closes_on_alpha_equality_or_rigid_separation`
/// - witness: `conv::tests::identity_requires_a_readable_root_in_every_family`
#[inline]
#[must_use]
#[spec(ensures: |ret| match (arena.computation(left), arena.computation(right)) {
    (Some(one), Some(other)) => if left == right {
        ret == Convertibility::Convertible
    } else {
        ret == Convertibility::Distinct
            || core::mem::discriminant(one) == core::mem::discriminant(other)
    },
    _ => ret == Convertibility::Distinct,
})]
pub(crate) fn equal_computations(
    arena: &TermArena,
    left: ComputationId,
    right: ComputationId,
) -> Convertibility
{
    converge(
        arena,
        ConversionGoal::Computation(left, right),
        Endpoints::Structural,
    )
}

/// The kernel's term equality on two values: α-equality first, then the
/// rules a conversion is forced to fire, a presented type's terms rewritten
/// by `presentations` among them.
///
/// # Specification
/// - requires: nothing — an unreadable id is admissible input and fails closed.
/// - ensures: [`Convertibility::Convertible`] when [`equal_values`] answers it,
///   or else when [`crate::replay::convert`] certifies the pair within
///   [`crate::replay::ReplayBudget::DEFAULT`]; [`Convertibility::Distinct`]
///   otherwise, which means not shown equal rather than shown apart. `arena`
///   holds what it held on entry.
/// - provides: the one equality a judgement the kernel decides without an
///   engine's trace reads, reflexivity's endpoints first.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an η-expanded pair and a reassociated pair convert, a
///   pair apart in one continuation does not, and an α-equal pair converts
///   without the replay; comparing syntax alone or relating every neutral pair
///   changes one of the three.
/// - witness: `element_identity::tests::reflexivity_converts_its_endpoints_by_the_laws_of_bind`
#[spec(
    captures: before = arena.watermark(),
    ensures: |ret| arena.watermark() == before
        && (ret == Convertibility::Distinct || arena.value(left).is_some() && arena.value(right).is_some()),
)]
pub(crate) fn convert_values(
    arena: &mut TermArena,
    presentations: &crate::presented::Presentations,
    left: ValueId,
    right: ValueId,
) -> Convertibility
{
    if equal_values(arena, left, right) == Convertibility::Convertible {
        return Convertibility::Convertible;
    }
    let unfoldings = crate::replay::Unfoldings::default().presenting(presentations.clone());
    match crate::replay::convert(
        arena,
        &unfoldings,
        crate::replay::ReplaySides::Values(left, right),
        crate::replay::ReplayBudget::DEFAULT,
    ) {
        crate::replay::KernelVerdict::Convertible => Convertibility::Convertible,
        crate::replay::KernelVerdict::NotConvertible
        | crate::replay::KernelVerdict::Declined(_) => Convertibility::Distinct,
    }
}

/// Compare `goal` structurally, setting aside into `pending` every value pair
/// one of whose sides is a returned endpoint or a constructor of a type
/// `presentations` presents, and every value type decoded from a returned
/// code against a value type of another former.
///
/// # Specification
/// - requires: nothing — an unreadable id fails closed.
/// - ensures: [`Convertibility::Convertible`] exactly when every pair the walk
///   examined, other than the pairs it appended to `pending`, converts as
///   [`convertible_value_types`] would; a set-aside pair is neither compared
///   nor descended into. On [`Convertibility::Distinct`] `pending` holds
///   whatever was set aside before the separating pair.
/// - provides: where the checker's endpoint reading looks: the type
///   conversion's own structural walk, finding the returned endpoints, the
///   decodes of returned codes and the presented terms it would otherwise
///   compare by syntax. Each is then read by [`crate::replay::read_endpoints`],
///   never compared here.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a returned endpoint inside a path type is set aside while
///   its domain still separates, so the reading is asked only the pairs
///   structure leaves open; a circle word is set aside for its normal form; a
///   decode of a returned code is set aside against a type of another former,
///   and against a decode compares its code.
/// - witness: `element_identity::tests::a_returned_endpoint_reads_at_a_mode_switch`
/// - witness: `element_identity::tests::a_stuck_returned_endpoint_compares_structurally`
/// - witness: `presented::tests::a_mode_switch_reads_circle_words_by_their_normal_forms`
/// - witness: `conv::tests::a_decode_of_a_returned_code_is_set_aside_against_another_former`
#[spec(captures: before = pending.len(), ensures: |ret| pending.len() >= before
    && (ret == Convertibility::Distinct || pending.get(before ..).is_some_and(|set_aside| set_aside.iter().all(|pair| match *pair {
        SetAside::Values(left, right) => [left, right].iter().any(|&side| matches!(arena.value(side), Some(&(Value::Returned(_) | Value::Constructor { .. })))),
        SetAside::Decoded { code, other } => matches!(arena.value(code), Some(&Value::Returned(_)))
            && !matches!(arena.value_type(other), Some(&ValueType::Element { .. }) | None),
    }))))]
pub(crate) fn pending_endpoints(
    arena: &TermArena,
    presentations: &crate::presented::Presentations,
    goal: ConversionGoal,
    pending: &mut Vec<SetAside>,
) -> Convertibility
{
    converge(arena, goal, Endpoints::Deferred {
        pending,
        presentations,
    })
}

/// Compare `goal` structurally, setting aside into `pending` every pair of
/// path endpoints and every value pair one of whose sides is a returned
/// endpoint or a constructor of a type `presentations` presents.
///
/// # Specification
/// - requires: nothing — an unreadable id fails closed.
/// - ensures: [`Convertibility::Convertible`] exactly when every pair the walk
///   examined, other than the pairs it appended to `pending`, converts as
///   [`convertible_value_types`] would; a set-aside pair is neither compared
///   nor descended into. On [`Convertibility::Distinct`] `pending` holds
///   whatever was set aside before the separating pair.
/// - provides: where a definition's relations are read: the same walk as
///   [`pending_endpoints`], leaving to the caller every endpoint pair a path
///   type carries, which is where the producer's conversion recorded its
///   dialogues.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — two path types whose compound endpoints differ set both
///   endpoint pairs aside and converge, so a relation reaches them, while a
///   differing domain still separates.
/// - witness: `element_identity::tests::a_definition_relating_compound_endpoints_admits`
/// - witness: `conv::tests::related_pairs_set_aside_path_endpoints`
#[spec(captures: before = pending.len(), ensures: |ret| pending.len() >= before)]
pub(crate) fn related_pairs(
    arena: &TermArena,
    presentations: &crate::presented::Presentations,
    goal: ConversionGoal,
    pending: &mut Vec<SetAside>,
) -> Convertibility
{
    converge(arena, goal, Endpoints::Related {
        pending,
        presentations,
    })
}

/// Convert a synthesized value type against an expected one, building the
/// mismatch on divergence.
///
/// # Specification
/// - requires: nothing.
/// - ensures: success exactly when [`convertible_value_types`] converges; an
///   unreadable root never converts, even to the same id.
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
#[spec(ensures: |ret| {
    let one = arena.value_type(expected);
    let other = arena.value_type(actual);
    match ret {
        Ok(()) => one.is_some() && other.is_some()
            && one.map(core::mem::discriminant) == other.map(core::mem::discriminant),
        Err(KernelError::ValueTypeMismatch(ref mismatch)) => (expected != actual || one.is_none())
            && mismatch.expected().head() == one.map_or(crate::error::ValueTypeHead::Unreadable, crate::error::ValueTypeHead::of)
            && mismatch.actual().head() == other.map_or(crate::error::ValueTypeHead::Unreadable, crate::error::ValueTypeHead::of),
        Err(_) => false,
    }
})]
pub fn convert_value_type(
    arena: &TermArena,
    expected: ValueTypeId,
    actual: ValueTypeId,
) -> Result<(), KernelError>
{
    match convertible_value_types(arena, expected, actual) {
        Convertibility::Convertible => Ok(()),
        Convertibility::Distinct => Err(KernelError::ValueTypeMismatch(ValueTypeMismatch::new(
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
/// - ensures: success exactly when [`convertible_comp_types`] converges; an
///   unreadable root never converts, even to the same id.
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
#[spec(ensures: |ret| {
    let one = arena.comp_type(expected);
    let other = arena.comp_type(actual);
    match ret {
        Ok(()) => one.is_some() && other.is_some()
            && one.map(core::mem::discriminant) == other.map(core::mem::discriminant),
        Err(KernelError::ComputationTypeMismatch(ref mismatch)) => (expected != actual || one.is_none())
            && mismatch.expected().head() == one.map_or(crate::error::CompTypeHead::Unreadable, crate::error::CompTypeHead::of)
            && mismatch.actual().head() == other.map_or(crate::error::CompTypeHead::Unreadable, crate::error::CompTypeHead::of),
        Err(_) => false,
    }
})]
pub fn convert_comp_type(
    arena: &TermArena,
    expected: CompTypeId,
    actual: CompTypeId,
) -> Result<(), KernelError>
{
    match convertible_comp_types(arena, expected, actual) {
        Convertibility::Convertible => Ok(()),
        Convertibility::Distinct => {
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
/// - requires: nothing; [`ConversionGoal`] fixes each pair's family.
/// - ensures: [`Convertibility::Convertible`] exactly when each examined pair
///   has readable roots and either equal ids or matching structure, with
///   canonical level equality and nominal atom equality. Under
///   [`Endpoints::Deferred`] a value pair with a returned endpoint, or with a
///   constructor of a presented type, on either side, and a value type decoded
///   from a returned code against a value type of another former, are appended
///   to the list unexamined and close, and a type of words converts with the
///   path type at the point its cells loop at
///   ([`crate::presented::Presentations::words`]); under [`Endpoints::Related`]
///   so does each, and every pair of path endpoints is appended too. The
///   iterative heap stack does not impose a host-stack depth limit.
/// - provides: the shared engine of the conversion and term-equality faces. The
///   predicate checks the initial roots' readability, identity and head
///   separation; the graph judgement and termination argument are not replayed
///   in the predicate.
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
/// over. The set records a pair before its children are compared. Its first
/// expansion leaves every required child on the worklist; a repeated pair can
/// therefore skip expansion without losing those obligations. Any failing
/// child refuses immediately, and only an empty worklist permits conversion.
///
/// The set is **per call and holds only pairs**. It creates no sharing, is
/// never consulted for anything but skipping a repeat inside one comparison,
/// and dies with the call — so it is not the interning table the conversion
/// engine is forbidden to grow, and it is not on the memo's plane: the pinned
/// expansion laws count the checker's goal expansions, which this does not
/// touch. It bounds the conversion path rather than decoding, so it sits
/// outside `gandr-kernel-term`'s amplification budgets: it guards a public
/// surface, since a direct arena caller is not behind the decoder's
/// expanded-work gate. Removing it leaves the suite unable to finish rather
/// than red: the claim is intensional and exponential, and a timeout is
/// indeterminate rather than a kill.
///
/// # Adequacy
/// - hypothesis: L1/L2/L3 — root readability, identity and head separation are
///   executable. Finite former and truncation witnesses separate the structural
///   arms and all four identity paths. A shared composite at depth 30 exercises
///   bounded expansion rather than proving the asymptotic claim by timing.
/// - witness: `conv::tests::structurally_equal_types_at_distinct_ids_convert`
/// - witness: `conv::tests::an_unreadable_id_fails_closed`
/// - witness: `conv::tests::a_shared_composite_converts_without_expanding`
/// - witness: `conv::tests::identity_requires_a_readable_root_in_every_family`
#[spec(captures: deferring = matches!(endpoints, Endpoints::Deferred { .. } | Endpoints::Related { .. }), ensures: |ret| match initial {
    ConversionGoal::ValueType(left, right) => match (arena.value_type(left), arena.value_type(right)) {
    (Some(one), Some(other)) => if left == right {
        ret == Convertibility::Convertible
    } else {
        ret == Convertibility::Distinct
            || core::mem::discriminant(one) == core::mem::discriminant(other)
            || deferring
    },
    _ => ret == Convertibility::Distinct,
},
    ConversionGoal::CompType(left, right) => match (arena.comp_type(left), arena.comp_type(right)) {
    (Some(one), Some(other)) => if left == right {
        ret == Convertibility::Convertible
    } else {
        ret == Convertibility::Distinct
            || core::mem::discriminant(one) == core::mem::discriminant(other)
    },
    _ => ret == Convertibility::Distinct,
},
    ConversionGoal::Value(left, right) => match (arena.value(left), arena.value(right)) {
    (Some(one), Some(other)) => if left == right {
        ret == Convertibility::Convertible
    } else {
        ret == Convertibility::Distinct
            || core::mem::discriminant(one) == core::mem::discriminant(other)
            || deferring
    },
    _ => ret == Convertibility::Distinct,
},
    ConversionGoal::Computation(left, right) => match (arena.computation(left), arena.computation(right)) {
    (Some(one), Some(other)) => if left == right {
        ret == Convertibility::Convertible
    } else {
        ret == Convertibility::Distinct
            || core::mem::discriminant(one) == core::mem::discriminant(other)
    },
    _ => ret == Convertibility::Distinct,
},
})]
fn converge(
    arena: &TermArena,
    initial: ConversionGoal,
    mut endpoints: Endpoints<'_>,
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
            ConversionGoal::ValueType(left, right) => {
                // Equal readable ids discharge one node. Unequal ids still
                // require structural comparison.
                if left == right {
                    if arena.value_type(left).is_none() {
                        return Convertibility::Distinct;
                    }
                    continue;
                }
                let pair = (left, right);
                let (Some(left), Some(right)) = (arena.value_type(left), arena.value_type(right))
                else {
                    return Convertibility::Distinct;
                };
                // A decode of a returned code against a type of another
                // former waits to be read: the type it denotes is what the
                // code's computation returns, a reduction, and none fires
                // here. Two decodes compare their codes below, and a pair
                // of returned codes is set aside there.
                let decoded = if let &ValueType::Element { code, .. } = left
                    && !matches!(*right, ValueType::Element { .. })
                {
                    Some((code, pair.1))
                }
                else if let &ValueType::Element { code, .. } = right
                    && !matches!(*left, ValueType::Element { .. })
                {
                    Some((code, pair.0))
                }
                else {
                    None
                };
                if let Some((code, other)) = decoded
                    && matches!(arena.value(code), Some(&Value::Returned(_)))
                    && let Endpoints::Deferred {
                        ref mut pending, ..
                    }
                    | Endpoints::Related {
                        ref mut pending, ..
                    } = endpoints
                {
                    pending.push(SetAside::Decoded { code, other });
                    continue;
                }
                match (left, right) {
                    (
                        &ValueType::Data {
                            declaration: one,
                            arguments: ref a,
                        },
                        &ValueType::Data {
                            declaration: other,
                            arguments: ref b,
                        },
                    ) => {
                        if one != other || a.len() != b.len() {
                            return Convertibility::Distinct;
                        }
                        stack.extend(a.iter().zip(b).map(|(a, b)| ConversionGoal::Value(*a, *b)));
                    },
                    // A path at the point a type of words' cells loop at is
                    // those words, once presented types are read: both
                    // endpoints spell the point, or one does and the other
                    // converts with it.
                    (
                        &ValueType::Data {
                            declaration,
                            ref arguments,
                        },
                        &ValueType::Path {
                            domain,
                            left: from,
                            right: to,
                        },
                    )
                    | (
                        &ValueType::Path {
                            domain,
                            left: from,
                            right: to,
                        },
                        &ValueType::Data {
                            declaration,
                            ref arguments,
                        },
                    ) => {
                        let presentations = match endpoints {
                            Endpoints::Deferred { presentations, .. }
                            | Endpoints::Related { presentations, .. } => presentations,
                            Endpoints::Structural => return Convertibility::Distinct,
                        };
                        let at =
                            |sides| presentations.words(arena, domain, sides) == Some(declaration);
                        if !arguments.is_empty() {
                            return Convertibility::Distinct;
                        }
                        if at((from, to)) {
                            continue;
                        }
                        if at((to, to)) {
                            stack.push(ConversionGoal::Value(from, to));
                        }
                        else if at((from, from)) {
                            stack.push(ConversionGoal::Value(to, from));
                        }
                        else {
                            return Convertibility::Distinct;
                        }
                    },
                    (&ValueType::Record(ref a), &ValueType::Record(ref b)) => {
                        if a.len() != b.len() || !a.keys().eq(b.keys()) {
                            return Convertibility::Distinct;
                        }
                        stack.extend(
                            a.values()
                                .zip(b.values())
                                .map(|(a, b)| ConversionGoal::ValueType(*a, *b)),
                        );
                    },
                    (&ValueType::PathUniverse(a, b), &ValueType::PathUniverse(c, d))
                    | (&ValueType::FlowUniverse(a, b), &ValueType::FlowUniverse(c, d)) => {
                        stack.push(ConversionGoal::Value(a, c));
                        stack.push(ConversionGoal::Value(b, d));
                    },
                    // Path and Flow never convert to each other: each pair
                    // below names one family on both sides.
                    (
                        &ValueType::Path {
                            domain: one_domain,
                            left: one_left,
                            right: one_right,
                        },
                        &ValueType::Path {
                            domain: other_domain,
                            left: other_left,
                            right: other_right,
                        },
                    )
                    | (
                        &ValueType::Flow {
                            domain: one_domain,
                            source: one_left,
                            target: one_right,
                        },
                        &ValueType::Flow {
                            domain: other_domain,
                            source: other_left,
                            target: other_right,
                        },
                    ) => {
                        stack.push(ConversionGoal::ValueType(one_domain, other_domain));
                        if let Endpoints::Related {
                            ref mut pending, ..
                        } = endpoints
                        {
                            pending.push(SetAside::Values(one_left, other_left));
                            pending.push(SetAside::Values(one_right, other_right));
                        }
                        else {
                            stack.push(ConversionGoal::Value(one_left, other_left));
                            stack.push(ConversionGoal::Value(one_right, other_right));
                        }
                    },
                    (&ValueType::Base(one), &ValueType::Base(other)) => {
                        if one != other {
                            return Convertibility::Distinct;
                        }
                    },
                    // Two products, or two sums, convert part by part; a
                    // different arity separates them.
                    (&ValueType::Product(ref one), &ValueType::Product(ref other))
                    | (&ValueType::Sum(ref one), &ValueType::Sum(ref other)) => {
                        if one.len() != other.len() {
                            return Convertibility::Distinct;
                        }
                        stack.extend(
                            one.iter()
                                .zip(other.iter())
                                .map(|(&one, &other)| ConversionGoal::ValueType(one, other)),
                        );
                    },
                    // Two static Pis, and two dependent pairs, convert factor
                    // by factor; a Σ's second factors stand under the same
                    // binder on both sides.
                    (
                        &ValueType::StaticPi {
                            domain: one_first,
                            codomain: one_second,
                        },
                        &ValueType::StaticPi {
                            domain: other_first,
                            codomain: other_second,
                        },
                    )
                    | (
                        &ValueType::Sigma {
                            first: one_first,
                            second: one_second,
                        },
                        &ValueType::Sigma {
                            first: other_first,
                            second: other_second,
                        },
                    ) => {
                        stack.push(ConversionGoal::ValueType(one_first, other_first));
                        stack.push(ConversionGoal::ValueType(one_second, other_second));
                    },
                    (&ValueType::Thunk(one_body), &ValueType::Thunk(other_body)) => {
                        stack.push(ConversionGoal::CompType(one_body, other_body));
                    },
                    (
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
                    (&ValueType::List(one), &ValueType::List(other)) => {
                        stack.push(ConversionGoal::ValueType(one, other));
                    },
                    // Both sides are pinned to the universe former by the
                    // pattern, and the former carries a sort and a level and no
                    // child, so the node comparison delegated to here *is* the
                    // sort comparison and the canonical level comparison — no
                    // other child is reachable through this arm.
                    (one @ &ValueType::Universe { .. }, other @ &ValueType::Universe { .. }) => {
                        if one != other {
                            return Convertibility::Distinct;
                        }
                    },
                    (&ValueType::Abstract(one), &ValueType::Abstract(other)) => {
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
                    (
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
                    (
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
                    (
                        &ValueType::Data { .. }
                        | &ValueType::Record(_)
                        | &ValueType::PathUniverse(..)
                        | &ValueType::FlowUniverse(..)
                        | &ValueType::Path { .. }
                        | &ValueType::Flow { .. }
                        | &ValueType::Base(_)
                        | &ValueType::Product(..)
                        | &ValueType::Sigma { .. }
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
            ConversionGoal::CompType(left, right) => {
                if left == right {
                    if arena.comp_type(left).is_none() {
                        return Convertibility::Distinct;
                    }
                    continue;
                }
                let (Some(left), Some(right)) = (arena.comp_type(left), arena.comp_type(right))
                else {
                    return Convertibility::Distinct;
                };
                match (left, right) {
                    (&CompType::Returner(one), &CompType::Returner(other)) => {
                        stack.push(ConversionGoal::ValueType(one, other));
                    },
                    // The two arrows compare alike child for child and never
                    // across: an arrow's codomain stands in the ambient context
                    // and a dependent codomain stands under one more binder, so
                    // a cross pair compares two codomains written against two
                    // different contexts. Refusing that pair is what makes the
                    // structural walk's reading of a de Bruijn index the same on
                    // both sides.
                    (
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
                    (
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
                    (
                        &CompType::With(one_left, one_right),
                        &CompType::With(other_left, other_right),
                    ) => {
                        stack.push(ConversionGoal::CompType(one_left, other_left));
                        stack.push(ConversionGoal::CompType(one_right, other_right));
                    },
                    (
                        &CompType::Returner(_)
                        | &CompType::Arrow { .. }
                        | &CompType::Pi { .. }
                        | &CompType::Element { .. }
                        | &CompType::With(..),
                        _,
                    ) => {
                        return Convertibility::Distinct;
                    },
                }
            },
            ConversionGoal::Value(left, right) => {
                if left == right {
                    if arena.value(left).is_none() {
                        return Convertibility::Distinct;
                    }
                    continue;
                }
                let pair = (left, right);
                let (Some(left), Some(right)) = (arena.value(left), arena.value(right))
                else {
                    return Convertibility::Distinct;
                };
                let presented = |value: &Value| match *value {
                    Value::Constructor { datatype, .. } => match endpoints {
                        Endpoints::Deferred { presentations, .. }
                        | Endpoints::Related { presentations, .. } => matches!(
                            arena.value_type(datatype),
                            Some(&ValueType::Data { declaration, .. })
                                if presentations.presented(declaration).is_some()
                        ),
                        Endpoints::Structural => false,
                    },
                    Value::Record(_)
                    | Value::SessionPath { .. }
                    | Value::SessionFlow { .. }
                    | Value::Stay { .. }
                    | Value::ForwardFlow { .. }
                    | Value::FunctionFlow { .. }
                    | Value::Then { .. }
                    | Value::FlowProduct(..)
                    | Value::PathRefl(_)
                    | Value::PathProduct(..)
                    | Value::PathEquiv { .. }
                    | Value::Here { .. }
                    | Value::Returned(_)
                    | Value::Higher { .. }
                    | Value::HigherEvaluation { .. }
                    | Value::QuantifiedEvaluation { .. }
                    | Value::Variable(_)
                    | Value::Constant(_)
                    | Value::Literal(_)
                    | Value::Tuple(_)
                    | Value::Injection(..)
                    | Value::ListNil
                    | Value::ListCons(..)
                    | Value::Thunk(_)
                    | Value::Lift { .. }
                    | Value::Quote(_)
                    | Value::QuoteComputation(_)
                    | Value::StaticApplication(..) => false,
                };
                let set_aside = matches!(*left, Value::Returned(_))
                    || matches!(*right, Value::Returned(_))
                    || presented(left)
                    || presented(right);
                if let Endpoints::Deferred {
                    ref mut pending, ..
                }
                | Endpoints::Related {
                    ref mut pending, ..
                } = endpoints
                    && set_aside
                {
                    pending.push(SetAside::Values(pair.0, pair.1));
                    continue;
                }
                match (left, right) {
                    | (&Value::Constructor { datatype: a, tag: one, fields: ref xs }, &Value::Constructor { datatype: b, tag: other, fields: ref ys }) => {
                        if one != other || xs.len() != ys.len() { return Convertibility::Distinct; }
                        stack.push(ConversionGoal::ValueType(a, b));
                        stack.extend(xs.iter().zip(ys).map(|(a, b)| ConversionGoal::Value(*a, *b)));
                    },
                    | (&Value::Record(ref a), &Value::Record(ref b)) => {
                        if a.len() != b.len() || !a.keys().eq(b.keys()) { return Convertibility::Distinct; }
                        stack.extend(a.values().zip(b.values()).map(|(a, b)| ConversionGoal::Value(*a, *b)));
                    },
                    | (&Value::SessionPath { path_type: one_type, payload_paths: one_paths, evidence: ref one }, &Value::SessionPath { path_type: other_type, payload_paths: other_paths, evidence: ref other })
                    | (&Value::SessionFlow { flow_type: one_type, payload_paths: one_paths, evidence: ref one }, &Value::SessionFlow { flow_type: other_type, payload_paths: other_paths, evidence: ref other }) => {
                        // Relation proof pairs are erased; payload translator assignment is not.
                        if one.payloads != other.payloads { return Convertibility::Distinct; }
                        stack.push(ConversionGoal::ValueType(one_type, other_type));
                        stack.push(ConversionGoal::Value(one_paths, other_paths));
                    },
                    // Two reflexivities compare by their points: the dialogues
                    // relating a point to its endpoints are evidence about the
                    // term, not part of what it means.
                    | (&Value::PathRefl(one), &Value::PathRefl(other))
                    | (&Value::Here { point: one, .. }, &Value::Here { point: other, .. })
                    | (&Value::Stay { point: one, .. }, &Value::Stay { point: other, .. }) => {
                        stack.push(ConversionGoal::Value(one, other));
                    },
                    // Two returned endpoints compare by their computations, as
                    // two thunks do; what either returns is a reduction.
                    | (&Value::Returned(one), &Value::Returned(other)) => {
                        stack.push(ConversionGoal::Computation(one, other));
                    },
                    // The guarded program is the field's structure and compares
                    // exactly; the layer evidence compares child for child.
                    | (&Value::Higher { program: ref one, evidence: ref xs }, &Value::Higher { program: ref other, evidence: ref ys }) => {
                        if one != other || xs.len() != ys.len() { return Convertibility::Distinct; }
                        stack.extend(xs.iter().zip(ys.iter()).map(|(&a, &b)| ConversionGoal::Value(a, b)));
                    },
                    // Replay dialogues are certificates and are erased, as the
                    // universe-path round-trip evidence is.
                    | (&Value::HigherEvaluation { components: ref xs, .. }, &Value::HigherEvaluation { components: ref ys, .. }) => {
                        if xs.len() != ys.len() { return Convertibility::Distinct; }
                        for (one, other) in xs.iter().zip(ys.iter()) {
                            stack.push(ConversionGoal::Value(one.left, other.left));
                            stack.push(ConversionGoal::Value(one.right, other.right));
                            stack.push(ConversionGoal::Value(one.evidence, other.evidence));
                        }
                    },
                    // The step kinds and fibres shape the tree, so they are
                    // compared; the dialogues are erased as above.
                    | (&Value::QuantifiedEvaluation { steps: ref one, children: ref xs }, &Value::QuantifiedEvaluation { steps: ref other, children: ref ys }) => {
                        let shape = |step: &gandr_kernel_term::QuantifiedStep| match *step {
                            | gandr_kernel_term::QuantifiedStep::Return(_) => None,
                            | gandr_kernel_term::QuantifiedStep::Apply { fibre, .. } => Some(fibre),
                        };
                        if !one.iter().map(shape).eq(other.iter().map(shape)) || xs.len() != ys.len() { return Convertibility::Distinct; }
                        stack.extend(xs.iter().zip(ys.iter()).map(|(&a, &b)| ConversionGoal::Value(a, b)));
                    },
                    | (&Value::PathProduct(a, b), &Value::PathProduct(c, d))
                    | (&Value::FlowProduct(a, b), &Value::FlowProduct(c, d)) => {
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
                    // A forward flow is its classifier and translator; the
                    // replayed images are certificate evidence the translator
                    // determines, and are erased as round-trip evidence is.
                    | (
                        &Value::ForwardFlow { flow_type: one_type, translator: one_map, .. },
                        &Value::ForwardFlow { flow_type: other_type, translator: other_map, .. },
                    ) => {
                        stack.push(ConversionGoal::ValueType(one_type, other_type));
                        stack.push(ConversionGoal::Value(one_map, other_map));
                    },
                    | (
                        &Value::FunctionFlow { flow_type: one_type, domain: one_domain, codomain: one_codomain },
                        &Value::FunctionFlow { flow_type: other_type, domain: other_domain, codomain: other_codomain },
                    ) => {
                        stack.push(ConversionGoal::ValueType(one_type, other_type));
                        stack.push(ConversionGoal::Value(one_domain, other_domain));
                        stack.push(ConversionGoal::Value(one_codomain, other_codomain));
                    },
                    | (
                        &Value::Then { first: one_first, second: one_second, seam: one_seam },
                        &Value::Then { first: other_first, second: other_second, seam: other_seam },
                    ) => {
                        if one_seam != other_seam { return Convertibility::Distinct; }
                        stack.push(ConversionGoal::Value(one_first, other_first));
                        stack.push(ConversionGoal::Value(one_second, other_second));
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
                    | (&Value::ListNil, &Value::ListNil) => {},
                    // Two tuples convert component by component; a different
                    // arity separates them.
                    | (&Value::Tuple(ref one), &Value::Tuple(ref other)) => {
                        if one.len() != other.len() {
                            return Convertibility::Distinct;
                        }
                        stack.extend(
                            one.iter()
                                .zip(other.iter())
                                .map(|(&one, &other)| ConversionGoal::Value(one, other)),
                        );
                    },
                    // As at the universe arm: both sides are pinned to the
                    // literal former, which carries one field, so the node
                    // comparison delegated to here is the literal comparison.
                    | (one @ &Value::Literal(_), other @ &Value::Literal(_)) => {
                        if one != other {
                            return Convertibility::Distinct;
                        }
                    },
                    | (&Value::ListCons(one_first, one_second), &Value::ListCons(other_first, other_second))
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
                        &Value::Constructor { .. } | &Value::Record(_) | &Value::SessionPath { .. } | &Value::SessionFlow { .. } | &Value::PathRefl(_) | &Value::PathProduct(..) | &Value::PathEquiv { .. }
                        | &Value::Here { .. } | &Value::Stay { .. } | &Value::ForwardFlow { .. } | &Value::FunctionFlow { .. } | &Value::Then { .. } | &Value::FlowProduct(..)
                        | &Value::Returned(_) | &Value::Higher { .. } | &Value::HigherEvaluation { .. } | &Value::QuantifiedEvaluation { .. }
                        | &Value::Variable(_)
                        | &Value::Constant(_)
                        | &Value::ListNil | &Value::ListCons(..)
                        | &Value::Literal(_)
                        | &Value::Tuple(..)
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
            ConversionGoal::Computation(left, right) => {
                if left == right {
                    if arena.computation(left).is_none() {
                        return Convertibility::Distinct;
                    }
                    continue;
                }
                let (Some(left), Some(right)) = (arena.computation(left), arena.computation(right))
                else {
                    return Convertibility::Distinct;
                };
                match (left, right) {
                    (
                        &Computation::DataCase {
                            scrutinee: a,
                            motive: c,
                            branches: ref xs,
                        },
                        &Computation::DataCase {
                            scrutinee: b,
                            motive: d,
                            branches: ref ys,
                        },
                    ) => {
                        if xs.len() != ys.len() {
                            return Convertibility::Distinct;
                        }
                        stack.push(ConversionGoal::Value(a, b));
                        stack.push(ConversionGoal::CompType(c, d));
                        stack.extend(
                            xs.iter()
                                .zip(ys)
                                .map(|(a, b)| ConversionGoal::Computation(*a, *b)),
                        );
                    },
                    (
                        &Computation::SigmaSplit {
                            scrutinee: one_scrutinee,
                            motive: one_motive,
                            body: one_body,
                        },
                        &Computation::SigmaSplit {
                            scrutinee: other_scrutinee,
                            motive: other_motive,
                            body: other_body,
                        },
                    ) => {
                        stack.push(ConversionGoal::Value(one_scrutinee, other_scrutinee));
                        stack.push(ConversionGoal::CompType(one_motive, other_motive));
                        stack.push(ConversionGoal::Computation(one_body, other_body));
                    },
                    (
                        &Computation::RecordProjection(a, ref one),
                        &Computation::RecordProjection(b, ref other),
                    ) => {
                        if one != other {
                            return Convertibility::Distinct;
                        }
                        stack.push(ConversionGoal::Value(a, b));
                    },
                    (
                        &Computation::TupleProjection(a, one),
                        &Computation::TupleProjection(b, other),
                    ) => {
                        if one != other {
                            return Convertibility::Distinct;
                        }
                        stack.push(ConversionGoal::Value(a, b));
                    },
                    (
                        &Computation::ListFold {
                            element: left_element,
                            result: left_result,
                            list: left_list,
                            on_nil: left_nil,
                            on_cons: left_cons,
                        },
                        &Computation::ListFold {
                            element: right_element,
                            result: right_result,
                            list: right_list,
                            on_nil: right_nil,
                            on_cons: right_cons,
                        },
                    ) => {
                        stack.extend([
                            ConversionGoal::ValueType(left_element, right_element),
                            ConversionGoal::ValueType(left_result, right_result),
                            ConversionGoal::Value(left_list, right_list),
                            ConversionGoal::Computation(left_nil, right_nil),
                            ConversionGoal::Computation(left_cons, right_cons),
                        ]);
                    },
                    (&Computation::Transport(a, b), &Computation::Transport(c, d)) => {
                        stack.push(ConversionGoal::Value(a, c));
                        stack.push(ConversionGoal::Value(b, d));
                    },
                    (
                        &Computation::PathTransport {
                            motive: one_motive,
                            path: one_path,
                            value: one_value,
                        },
                        &Computation::PathTransport {
                            motive: other_motive,
                            path: other_path,
                            value: other_value,
                        },
                    )
                    | (
                        &Computation::Ride {
                            motive: one_motive,
                            flow: one_path,
                            value: one_value,
                        },
                        &Computation::Ride {
                            motive: other_motive,
                            flow: other_path,
                            value: other_value,
                        },
                    ) => {
                        stack.push(ConversionGoal::ValueType(one_motive, other_motive));
                        stack.push(ConversionGoal::Value(one_path, other_path));
                        stack.push(ConversionGoal::Value(one_value, other_value));
                    },
                    (
                        &Computation::TelescopeTransport {
                            motive: one_motive,
                            path: one_path,
                            start: one_start,
                            over: one_over,
                            value: one_value,
                        },
                        &Computation::TelescopeTransport {
                            motive: other_motive,
                            path: other_path,
                            start: other_start,
                            over: other_over,
                            value: other_value,
                        },
                    )
                    | (
                        &Computation::TelescopeRide {
                            motive: one_motive,
                            flow: one_path,
                            start: one_start,
                            over: one_over,
                            value: one_value,
                        },
                        &Computation::TelescopeRide {
                            motive: other_motive,
                            flow: other_path,
                            start: other_start,
                            over: other_over,
                            value: other_value,
                        },
                    ) => {
                        stack.extend([
                            ConversionGoal::CompType(one_motive, other_motive),
                            ConversionGoal::Value(one_path, other_path),
                            ConversionGoal::Value(one_start, other_start),
                            ConversionGoal::Value(one_over, other_over),
                            ConversionGoal::Value(one_value, other_value),
                        ]);
                    },
                    (
                        &Computation::RelatedApplication {
                            path: one_path,
                            left: one_left,
                            right: one_right,
                            evidence: one_evidence,
                            body: one_body,
                        },
                        &Computation::RelatedApplication {
                            path: other_path,
                            left: other_left,
                            right: other_right,
                            evidence: other_evidence,
                            body: other_body,
                        },
                    ) => {
                        stack.extend([
                            ConversionGoal::Value(one_path, other_path),
                            ConversionGoal::Value(one_left, other_left),
                            ConversionGoal::Value(one_right, other_right),
                            ConversionGoal::Value(one_evidence, other_evidence),
                            ConversionGoal::Computation(one_body, other_body),
                        ]);
                    },
                    (&Computation::Lambda(one), &Computation::Lambda(other))
                    | (
                        &Computation::Fixpoint { body: one, .. },
                        &Computation::Fixpoint { body: other, .. },
                    ) => {
                        stack.push(ConversionGoal::Computation(one, other));
                    },
                    (
                        &Computation::Application(one_head, one_argument),
                        &Computation::Application(other_head, other_argument),
                    ) => {
                        stack.push(ConversionGoal::Computation(one_head, other_head));
                        stack.push(ConversionGoal::Value(one_argument, other_argument));
                    },
                    (&Computation::Return(one), &Computation::Return(other))
                    | (&Computation::Force(one), &Computation::Force(other)) => {
                        stack.push(ConversionGoal::Value(one, other));
                    },
                    (
                        &Computation::Bind(one_bound, one_body),
                        &Computation::Bind(other_bound, other_body),
                    )
                    | (
                        &Computation::With(one_bound, one_body),
                        &Computation::With(other_bound, other_body),
                    ) => {
                        stack.push(ConversionGoal::Computation(one_bound, other_bound));
                        stack.push(ConversionGoal::Computation(one_body, other_body));
                    },
                    (
                        &Computation::Project(one_side, one),
                        &Computation::Project(other_side, other),
                    ) => {
                        if one_side != other_side {
                            return Convertibility::Distinct;
                        }
                        stack.push(ConversionGoal::Computation(one, other));
                    },
                    (
                        &Computation::Case {
                            scrutinee: one_scrutinee,
                            branches: ref one_branches,
                        },
                        &Computation::Case {
                            scrutinee: other_scrutinee,
                            branches: ref other_branches,
                        },
                    ) => {
                        if one_branches.len() != other_branches.len() {
                            return Convertibility::Distinct;
                        }
                        stack.push(ConversionGoal::Value(one_scrutinee, other_scrutinee));
                        stack.extend(
                            one_branches
                                .iter()
                                .zip(other_branches.iter())
                                .map(|(&one, &other)| ConversionGoal::Computation(one, other)),
                        );
                    },
                    (
                        &Computation::DataCase { .. }
                        | &Computation::SigmaSplit { .. }
                        | &Computation::RecordProjection(..)
                        | &Computation::TupleProjection(..)
                        | &Computation::Transport(..)
                        | &Computation::PathTransport { .. }
                        | &Computation::TelescopeTransport { .. }
                        | &Computation::Ride { .. }
                        | &Computation::TelescopeRide { .. }
                        | &Computation::RelatedApplication { .. }
                        | &Computation::Lambda(_)
                        | &Computation::Fixpoint { .. }
                        | &Computation::ListFold { .. }
                        | &Computation::Application(..)
                        | &Computation::Return(_)
                        | &Computation::Bind(..)
                        | &Computation::With(..)
                        | &Computation::Project(..)
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
        let product = arena.value_type_product(&[unit, base]);
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
        let first = arena.value_type_product(&[first_unit, first_unit]);
        let second = arena.value_type_product(&[second_unit, second_unit]);
        assert_ne!(first, second, "the fixture mints two distinct arena nodes");
        assert_eq!(
            Convertibility::Convertible,
            convertible_value_types(&arena, first, second),
            "the id fast path is positive only: unequal ids decide nothing and the structural \
             walk decides"
        );
    }

    #[test]
    fn related_pairs_set_aside_path_endpoints()
    {
        let mut arena = TermArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let string = arena.value_type_base(BaseType::String);
        let first = arena.value_variable(DeBruijnIndex::from(0_u32));
        let second = arena.value_variable(DeBruijnIndex::from(1_u32));
        let one = arena.value_type_path(integer, first, second);
        let other = arena.value_type_path(integer, second, first);
        let mut pending = alloc::vec::Vec::new();
        assert_eq!(
            super::related_pairs(
                &arena,
                &crate::presented::FREE,
                super::ConversionGoal::ValueType(one, other),
                &mut pending
            ),
            Convertibility::Convertible,
            "differing endpoints are left to the caller"
        );
        assert_eq!(pending, [
            super::SetAside::Values(first, second),
            super::SetAside::Values(second, first)
        ]);
        assert_eq!(
            convertible_value_types(&arena, one, other),
            Convertibility::Distinct,
            "the structural walk compares the same endpoints"
        );
        let apart = arena.value_type_path(string, second, first);
        let mut pending = alloc::vec::Vec::new();
        assert_eq!(
            super::related_pairs(
                &arena,
                &crate::presented::FREE,
                super::ConversionGoal::ValueType(one, apart),
                &mut pending
            ),
            Convertibility::Distinct,
            "a differing domain still separates"
        );
    }

    #[test]
    fn a_decode_of_a_returned_code_is_set_aside_against_another_former()
    {
        // `El(⟨c⟩)` for a returned code against `Integer` is set aside, in
        // either order, for the caller to read; the plain walk, which reads
        // nothing, separates the two. A decode of a variable code is no
        // reduction and separates in place.
        let mut arena = TermArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
        let forced = arena.computation_force(variable);
        let code = arena.value_returned(forced);
        let decoded = arena.value_type_element(code, Level::zero());
        let rigid = arena.value_type_element(variable, Level::zero());
        for (one, other) in [(decoded, integer), (integer, decoded)] {
            let mut pending = alloc::vec::Vec::new();
            assert_eq!(
                super::pending_endpoints(
                    &arena,
                    &crate::presented::FREE,
                    super::ConversionGoal::ValueType(one, other),
                    &mut pending
                ),
                Convertibility::Convertible,
                "the decode waits to be read"
            );
            assert_eq!(pending, [super::SetAside::Decoded {
                code,
                other: integer
            }]);
            assert_eq!(
                convertible_value_types(&arena, one, other),
                Convertibility::Distinct
            );
        }
        let mut pending = alloc::vec::Vec::new();
        assert_eq!(
            super::pending_endpoints(
                &arena,
                &crate::presented::FREE,
                super::ConversionGoal::ValueType(rigid, integer),
                &mut pending
            ),
            Convertibility::Distinct
        );
        assert!(pending.is_empty());
    }

    #[test]
    fn conversion_separates_every_former()
    {
        let mut arena = TermArena::new();
        let unit = arena.value_type_unit();
        let integer = arena.value_type_base(BaseType::Integer);
        let string = arena.value_type_base(BaseType::String);
        let numeric = arena.value_type_base(BaseType::Numeric);
        let product = arena.value_type_product(&[unit, integer]);
        let sum = arena.value_type_sum(&[unit, integer]);
        let returner = arena.comp_type_returner(unit);
        let thunk = arena.value_type_thunk(returner);
        let universe = arena.value_type_universe(GroundSort::Value, Level::zero());
        let atom = arena.value_type_abstract(ConstantIndex::from(0_usize));
        let code = arena.value_variable(DeBruijnIndex::from(0_u32));
        let element = arena.value_type_element(code, Level::zero());
        let lift = arena.value_type_lift(unit, level(LevelConstant::from(1)));
        let static_pi = arena.value_type_static_pi(universe, universe);
        let formers = [
            unit, integer, string, numeric, product, sum, thunk, universe, atom, element, lift,
            static_pi,
        ];
        for (one, left) in formers.iter().copied().enumerate() {
            for (other, right) in formers.iter().copied().enumerate() {
                let expected = if one == other {
                    Convertibility::Convertible
                }
                else {
                    Convertibility::Distinct
                };
                assert_eq!(
                    expected,
                    convertible_value_types(&arena, left, right),
                    "formers {one}/{other}: distinct formers or base atoms separate in both directions"
                );
            }
        }
        let transposed = arena.value_type_product(&[integer, unit]);
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
        let integer = arena.value_type_base(BaseType::Integer);
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
        for structural in [unit, integer] {
            assert_eq!(
                (Convertibility::Distinct, Convertibility::Distinct),
                (
                    convertible_value_types(&arena, first, structural),
                    convertible_value_types(&arena, structural, first),
                ),
                "and no arm relates an atom to a structural type in either direction, which is \
                 what opacity means here"
            );
        }
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

    /// Selected term-form counterexamples make the descent into terms a real
    /// comparison rather than a reflexivity check.
    ///
    /// A code is compared **without reducing**, so two applications separate on
    /// their head and argument rather than on what they would evaluate to —
    /// the incompleteness the convertibility machine closes, pinned here so it
    /// is a recorded property rather than a surprise.
    #[test]
    fn code_comparison_separates_selected_term_forms_without_reducing()
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
        let pair = arena.value_tuple(&[unit, variable]);
        let transposed = arena.value_tuple(&[variable, unit]);
        let left = arena.value_injection(Side::Left.into(), unit);
        let right = arena.value_injection(Side::Right.into(), unit);
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
            left = arena.value_type_product(&[left, left]);
            right = arena.value_type_product(&[right, right]);
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
            other = arena.value_type_product(&[other, other]);
        }
        assert_eq!(
            Convertibility::Distinct,
            convertible_value_types(&arena, left, other),
            "a composite over a different leaf still separates"
        );
    }

    #[test]
    fn identity_requires_a_readable_root_in_every_family()
    {
        let mut arena = TermArena::new();
        let live_value_type = arena.value_type_unit();
        let live_comp_type = arena.comp_type_returner(live_value_type);
        let live_value = arena.value_unit();
        let live_computation = arena.computation_return(live_value);
        let floor = arena.watermark();
        let stale_value_type = arena.value_type_unit();
        let stale_comp_type = arena.comp_type_returner(live_value_type);
        let stale_value = arena.value_unit();
        let stale_computation = arena.computation_return(live_value);
        arena.truncate_to(floor);
        let cases = [
            ("value type", [
                convertible_value_types(&arena, live_value_type, live_value_type),
                convertible_value_types(&arena, stale_value_type, stale_value_type),
                convertible_value_types(&arena, live_value_type, stale_value_type),
                convertible_value_types(&arena, stale_value_type, live_value_type),
            ]),
            ("computation type", [
                convertible_comp_types(&arena, live_comp_type, live_comp_type),
                convertible_comp_types(&arena, stale_comp_type, stale_comp_type),
                convertible_comp_types(&arena, live_comp_type, stale_comp_type),
                convertible_comp_types(&arena, stale_comp_type, live_comp_type),
            ]),
            ("value", [
                super::equal_values(&arena, live_value, live_value),
                super::equal_values(&arena, stale_value, stale_value),
                super::equal_values(&arena, live_value, stale_value),
                super::equal_values(&arena, stale_value, live_value),
            ]),
            ("computation", [
                super::equal_computations(&arena, live_computation, live_computation),
                super::equal_computations(&arena, stale_computation, stale_computation),
                super::equal_computations(&arena, live_computation, stale_computation),
                super::equal_computations(&arena, stale_computation, live_computation),
            ]),
        ];
        for (family, observed) in cases {
            assert_eq!(
                observed,
                [
                    Convertibility::Convertible,
                    Convertibility::Distinct,
                    Convertibility::Distinct,
                    Convertibility::Distinct,
                ],
                "{family}: identity requires readability; either unreadable side refuses"
            );
        }
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
        assert_eq!(ValueTypeHead::Product, mismatch.expected().head());
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
        assert_eq!(Ok(()), convert_comp_type(&arena, returner, returner));
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
