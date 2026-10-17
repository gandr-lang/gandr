//! Univalence in the core: `ua(e)`, admitted on its record's laws at any two
//! codes of the value universe.
//!
//! # The rule
//!
//! Checked against `Path(Type, a, b)`, `ua(e)` checks `e` against the
//! bi-invertible record `A ≃ B` over the types the two codes denote: `T` for
//! a quote `⌜T⌝`, `El c` for any other code `c`. Anywhere else `ua(e)`
//! synthesises `Path(Type, a, b)` when `e` synthesises a dependent pair whose
//! first factor is the thunk type `U (A → F B)` of a pure non-dependent arrow,
//! `e` checks against `A ≃ B`, and `a` and `b`, the codes of `A` and `B`, check
//! against `Type`; a type `El c` has the code `c`, any other type its quote.
//! The record's fields are the evidence: a section or a retraction that does
//! not hold is a field that does not check, refused where the record is, and
//! a code above `Type` is refused where the code is. Nothing is decided by
//! computation, so the codes may be variables, path types or anything else the
//! universe holds.
//!
//! The core node carries, beside the record, the forward map `thunk (λx. f ←
//! e.0; force f x)` the lowering derives from it
//! ([`gandr_core_term::identity::univalence_forward`]), so the normaliser
//! transports along the path by applying it. The judgement compares the
//! carried map with the one it derives and refuses another as malformed. The
//! bridge erases the record alone, and the kernel reads the identity off the
//! record's type, or rebuilds the record type from the identity it is checked
//! against, checks the record and derives the forward map itself.
//!
//! # Decisions
//!
//! - **Evidence, not computation.** The choice is the record's laws checked as
//!   its fields. The alternative, extending the round-trip coverage of
//!   `equiv(f, g)` to every code, was declined: coverage is finite only over
//!   the first-order stratum, and a code like `Path(Circle, base, base)` has no
//!   finite coverage. Reversal: univalence proved as a theorem of the kernel,
//!   after which `ua` is a definition and this rule a derived one.
//! - **Checked against its path type, synthesised from its record elsewhere.**
//!   The expected type names both codes, so a record literal checks; away from
//!   one, the record names both types through its forward map's type, as
//!   `equiv`'s forward translator does. Reversal: none while both readings
//!   agree on the record type.

use anodized::spec;
use gandr_core_term::CertificateEquality;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::equal_type_syntax;
use gandr_kernel_strata::Level;
use gandr_kernel_term::GroundSort;

use crate::context::CheckingContext;
use crate::refusal::CheckRefusal;
use crate::refusal::ExpectedShape;
use crate::refusal::TermNode;
use crate::refusal::TypeNode;
use crate::view::ValueTypeView;
use crate::view::value_type_view;

/// What the judgement checks of a synthesised univalence before it admits it:
/// its record against the bi-invertible record type, then each code against
/// `Type`.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Premises
{
    /// The path type the univalence synthesises once its premises check.
    pub path: ValueTypeId,
    /// Each term the judgement checks and the type it checks against, in
    /// order.
    pub checks: [(ValueId, ValueTypeId); 3],
}

/// How the judgement reads a univalence checked against a type.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Reading
{
    /// The type is an identity at `Type`: the record checks against `record`,
    /// the bi-invertible record type, and the univalence has the identity
    /// `path` written afresh from the type's codes.
    Record
    {
        /// The record type.
        record: ValueTypeId,
        /// The identity at `Type` between the two codes.
        path: ValueTypeId,
    },
    /// Any other type: the univalence is synthesised and compared with it.
    Synthesised,
}

/// The code of the value type `carrier`: the code `c` of `El c`, the quote of
/// any other type.
///
/// # Specification
/// - requires: `carrier` is a value type of the context's arena.
/// - ensures: the code an element type decodes at its weak head, or a fresh
///   quote of `carrier`.
/// - fails: a weak-head or view refusal as those raise it.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — a decoded variable code crosses as the variable and a
///   list type as its quote, each converting with the written identity; quoting
///   a decoded code, or decoding a quote, changes the path type.
/// - witness: `univalence::tests::ua_is_admitted_on_the_record_s_laws_beyond_the_first_order_stratum`
#[spec(ensures: |ret| ret.is_err() || ret.as_ref().is_ok_and(|&code| context.arena().value(code).is_some()))]
fn code_of(
    context: &mut CheckingContext<'_>,
    carrier: ValueTypeId,
) -> Result<ValueId, CheckRefusal>
{
    let head = context.whnf_value_type(carrier)?;
    if let ValueTypeView::Element { code, .. } = value_type_view(context.arena(), head)? {
        return Ok(code);
    }
    Ok(context.arena_mut().value_quote(carrier))
}

/// The type the code `code` of the level-zero value universe denotes: `T` for
/// a quote `⌜T⌝`, `El c` for any other code `c`.
///
/// # Specification
/// - requires: `code` is a value of the context's arena.
/// - ensures: the quoted type at the code's weak head, or a fresh decode of
///   `code` at level zero.
/// - fails: a weak-head refusal as it raises it.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — a record literal checked against `Path(Type, a, b)` reads
///   `⌜Bool⌝` as the booleans and two variables as their decodes, which the
///   identity map does not relate; quoting a variable, or decoding a quote,
///   changes the record type the literal checks against.
/// - witness: `univalence::tests::a_record_whose_law_fails_does_not_build_a_path`
#[spec(ensures: |ret| ret.is_err() || ret.as_ref().is_ok_and(|&denoted| context.arena().value_type(denoted).is_some()))]
fn denoted(
    context: &mut CheckingContext<'_>,
    code: ValueId,
) -> Result<ValueTypeId, CheckRefusal>
{
    let head = context.whnf_code(code)?;
    if let Some(&gandr_core_term::Value::Quote(quoted)) = context.arena().value(head) {
        return Ok(quoted);
    }
    Ok(context.arena_mut().value_type_element(code, Level::zero()))
}

/// Refuse a carried forward map other than the one `record` derives.
///
/// # Specification
/// - requires: both terms stand under the judgement's binders.
/// - ensures: success exactly when `forward` is, syntactically, the map
///   [`gandr_core_term::identity::univalence_forward`] derives from `record`.
/// - fails: [`CheckRefusal::MachineInvariant`] otherwise.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — the derived map passes and a forged one is refused as
///   malformed core.
/// - witness: `univalence::tests::ua_is_admitted_on_the_record_s_laws_beyond_the_first_order_stratum`
#[spec(ensures: |ret| match ret {
    Ok(()) | Err(CheckRefusal::MachineInvariant) => true,
    Err(_) => false,
})]
fn derived(
    context: &mut CheckingContext<'_>,
    (record, forward): (ValueId, ValueId),
) -> Result<(), CheckRefusal>
{
    let arena = context.arena_mut();
    let derived = gandr_core_term::identity::univalence_forward(arena, record);
    if gandr_core_term::equal_certificate_syntax(arena, derived, forward)
        != CertificateEquality::Equal
    {
        return Err(CheckRefusal::MachineInvariant);
    }
    Ok(())
}

/// How `ua(e)` checks against `expected`: its record against the
/// bi-invertible record type when `expected` is an identity at `Type`, by
/// synthesis otherwise.
///
/// # Specification
/// - requires: `forward` is the map the node carries for `record`; both and
///   `expected` stand under the judgement's binders.
/// - ensures: for `expected` an identity `Path(Type, a, b)` at the level-zero
///   value universe, [`Reading::Record`] at the bi-invertible record type over
///   the types `a` and `b` denote and at `Path(Type, a, b)` written afresh;
///   [`Reading::Synthesised`] for any other type.
/// - provides: the checking reading of the `ua` rule, which admits a record
///   literal.
/// - fails: [`CheckRefusal::MachineInvariant`] for a carried map other than the
///   one the record derives; a weak-head or view refusal as those raise it.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — a record literal whose section fails is refused against
///   `Path(Type, ⌜Bool⌝, ⌜Bool⌝)` and one whose laws hold checks; reading the
///   record type off the wrong endpoint admits it or refuses it elsewhere.
/// - witness: `univalence::tests::a_record_whose_law_fails_does_not_build_a_path`
#[spec(ensures: |ret| match ret {
    | Ok(Reading::Record { record, path }) => context.arena().value_type(record).is_some() && context.arena().value_type(path).is_some(),
    | Ok(Reading::Synthesised) | Err(_) => true,
})]
pub fn checked(
    context: &mut CheckingContext<'_>,
    (record, forward): (ValueId, ValueId),
    expected: ValueTypeId,
) -> Result<Reading, CheckRefusal>
{
    let head = context.whnf_value_type(expected)?;
    let ValueTypeView::Path {
        carrier,
        left,
        right,
    } = value_type_view(context.arena(), head)?
    else {
        return Ok(Reading::Synthesised);
    };
    let carrier = context.whnf_value_type(carrier)?;
    let at_type = matches!(
        value_type_view(context.arena(), carrier)?,
        ValueTypeView::Universe { sort: GroundSort::Value, level } if *level == Level::zero()
    );
    if !at_type {
        return Ok(Reading::Synthesised);
    }
    derived(context, (record, forward))?;
    let from = denoted(context, left)?;
    let to = denoted(context, right)?;
    let arena = context.arena_mut();
    let record = gandr_core_term::identity::bi_invertible(arena, from, to);
    let universe = arena.value_type_universe(
        gandr_core_term::Sort::Ground(GroundSort::Value),
        Level::zero(),
    );
    let path = arena.value_type_path(universe, left, right);
    Ok(Reading::Record { record, path })
}

/// The premises of `ua(e)` at `at`, read off the type `classifier` its record
/// `e` synthesised.
///
/// # Specification
/// - requires: `classifier` is the type `record` synthesised; `forward` is the
///   map the node carries; all stand under the judgement's binders.
/// - ensures: the path type `Path(Type, a, b)` over the codes of the two types
///   the classifier's first factor relates, and the checks of the record
///   against `A ≃ B` — the classifier itself when it is that type to the syntax
///   — and of `a` and `b` against `Type`, in that order.
/// - provides: what the judgement's `ua` rule checks before it synthesises the
///   path type.
/// - fails: [`CheckRefusal::ShapeMismatch`] at `at` wanting a dependent pair
///   for a classifier that is none, and wanting a thunk for one whose first
///   factor is no thunk of a pure non-dependent arrow, naming that factor;
///   [`CheckRefusal::MachineInvariant`] for a carried map other than the one
///   the record derives; a weak-head or view refusal as those raise it.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — a record of `List Bool ≃ List Bool` names both codes as
///   quotes, one of `El a ≃ El b` as the variables, and a unit is refused
///   wanting a dependent pair; reading the codes off the wrong factor, or
///   skipping a check, admits a record the rule does not.
/// - witness: `univalence::tests::ua_is_admitted_on_the_record_s_laws_beyond_the_first_order_stratum`
#[spec(ensures: |ret| match ret {
    | Err(CheckRefusal::ShapeMismatch { at: site, wanted, .. }) => site == TermNode::Value(at) && matches!(wanted, ExpectedShape::Sigma | ExpectedShape::Thunk),
    | Ok(premises) => premises.checks[0].0 == record,
    | Err(_) => true,
})]
pub fn premises(
    context: &mut CheckingContext<'_>,
    at: ValueId,
    (record, forward): (ValueId, ValueId),
    classifier: ValueTypeId,
) -> Result<Premises, CheckRefusal>
{
    let head = context.whnf_value_type(classifier)?;
    let ValueTypeView::Sigma { first, .. } = value_type_view(context.arena(), head)?
    else {
        return Err(CheckRefusal::ShapeMismatch {
            at: TermNode::Value(at),
            wanted: ExpectedShape::Sigma,
            found: TypeNode::Value(classifier),
        });
    };
    let (from, to) = crate::equiv::codes(context, at, first).map_err(|refusal| {
        if matches!(refusal, CheckRefusal::EquivUnsupported { .. }) {
            CheckRefusal::ShapeMismatch {
                at: TermNode::Value(at),
                wanted: ExpectedShape::Thunk,
                found: TypeNode::Value(first),
            }
        }
        else {
            refusal
        }
    })?;
    derived(context, (record, forward))?;
    // The record checks against the type it synthesised when that is the record
    // type already, as a declared `A ≃ B` is, so its typed entry keeps the type
    // its source wrote; against the record type rebuilt from the two types
    // otherwise.
    let rebuilt = gandr_core_term::identity::bi_invertible(context.arena_mut(), from, to);
    let expected =
        if equal_type_syntax(context.arena(), classifier, rebuilt) == CertificateEquality::Equal {
            classifier
        }
        else {
            rebuilt
        };
    let source = code_of(context, from)?;
    let target = code_of(context, to)?;
    let arena = context.arena_mut();
    let universe = arena.value_type_universe(
        gandr_core_term::Sort::Ground(GroundSort::Value),
        Level::zero(),
    );
    let path = arena.value_type_path(universe, source, target);
    Ok(Premises {
        path,
        checks: [(record, expected), (source, universe), (target, universe)],
    })
}

#[cfg(test)]
mod tests;
