//! Typed holes and marks, the elaboration-only formers.
//!
//! They let an unfinished or ill-typed program still have a type, and the
//! matched-type operations here are what a judgement reads an expected or
//! synthesised type through when that type may be unknown.
//!
//! # A hole is a term, and its type is unknown
//!
//! [`Value::Hole`] and [`Computation::Hole`](crate::Computation::Hole) stand
//! for a term the author has not written. Each carries a [`HoleId`], the name a
//! fill finds it by. A hole synthesises the unknown type —
//! [`ValueType::Unknown`] or [`CompType::Unknown`] — and checks against any
//! type, so a judgement that meets one keeps going rather than stopping at the
//! first gap (Omar et al., *Hazelnut: A Bidirectionally Typed Structure Editor
//! Calculus*, POPL 2017, doi:10.1145/3009837.3009900).
//!
//! # A mark is an error kept in place
//!
//! [`Value::Mark`] and [`Computation::Mark`](crate::Computation::Mark) wrap a
//! subterm the elaborator could not type and name the entry of the
//! elaboration's mark table that says why. A marked term types as a hole does
//! and its body is not judged, so a marked elaboration is well formed however
//! many errors it carries: the error is a mark on a well-formed term rather
//! than the end of the judgement (Zhao et al., *Total Type Error Localization
//! and Recovery with Holes*, POPL 2024, doi:10.1145/3632910).
//!
//! # The decode of a hole is an unknown type
//!
//! A type holds a hole through a code: `El ?h` is the type the hole will
//! denote once filled. Until then it is unknown, and [`value_type_knowledge`]
//! and [`comp_type_knowledge`] read both spellings — the unknown former and the
//! decode of a hole or a mark — as one. The decode keeps the hole's name, so a
//! fill reaches the type too; the unknown former is what a hole synthesises,
//! which has no name to keep.
//!
//! # Matching a type against a former
//!
//! An introduction checks against an expected former, and an elimination reads
//! the former its head synthesised. The unknown type matches every former, with
//! unknown components: [`matched_thunk`] and its siblings answer a former's
//! components, minting the unknown where the type is unknown, and a named
//! absence where the type is another former. They read the node as it stands:
//! unfolding a definition to reach the weak head is the judgement's, which
//! holds the definitions.

use anodized::spec;
use quenchant_shape::shape::Maybe;

use crate::arena::CompTypeId;
use crate::arena::ComputationId;
use crate::arena::CoreArena;
use crate::arena::ValueId;
use crate::arena::ValueTypeId;
use crate::syntax::CompType;
use crate::syntax::Value;
use crate::syntax::ValueType;

/// The name of a typed hole: what a fill finds it by.
///
/// The elaborator issues hole names; this crate compares them and nothing
/// else, so two holes with one name are one hole filled at once.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct HoleId(u32);

impl From<u32> for HoleId
{
    /// Read a `u32` as a hole name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(name: u32) -> Self
    {
        Self(name)
    }
}

impl From<HoleId> for u32
{
    /// The name a hole carries.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(hole: HoleId) -> Self
    {
        hole.0
    }
}

/// The index of one entry of an elaboration's mark table.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct MarkIndex(u32);

impl From<u32> for MarkIndex
{
    /// Read a `u32` as a mark-table index.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: u32) -> Self
    {
        Self(index)
    }
}

impl From<MarkIndex> for u32
{
    /// The table index a mark names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(mark: MarkIndex) -> Self
    {
        mark.0
    }
}

/// A term of either family: what a fill places and what a mark wraps.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum TermId
{
    /// A value.
    Value(ValueId),
    /// A computation.
    Computation(ComputationId),
}

/// Whether a type is known: a former the judgement can read, or the unknown
/// type a hole or a mark stands behind.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Knowledge
{
    /// The type is a former other than the unknown one.
    Known,
    /// The type is the unknown former, or the decode of a hole or a mark.
    Unknown,
}

quenchant_shape::reason_enum! {
    /// Why a type matched no former.
    pub mod matching {
        /// The reason a matched-type operation answered no components.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The type is known, and is a former other than the one asked for.
            Mismatched,
            /// The id named no node of the arena.
            Dangling,
        }
    }
}

/// Where a matched function type's codomain stands.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum CodomainScope
{
    /// In the ambient context, as an arrow's does: it binds nothing.
    Ambient,
    /// Under the domain's binder, as a dependent arrow's does.
    UnderBinder,
}

/// A function type's components, as a lambda or an application reads them.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct MatchedFunction
{
    /// The value-type domain.
    domain: ValueTypeId,
    /// The computation-type codomain.
    codomain: CompTypeId,
    /// Where the codomain stands.
    scope: CodomainScope,
}

impl MatchedFunction
{
    /// The value-type domain.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn domain(&self) -> ValueTypeId
    {
        self.domain
    }

    /// The computation-type codomain, standing where [`Self::scope`] says.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn codomain(&self) -> CompTypeId
    {
        self.codomain
    }

    /// Where the codomain stands.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn scope(&self) -> CodomainScope
    {
        self.scope
    }
}

/// Whether `code` is a hole or a mark: a code whose decode is unknown.
///
/// # Specification
/// trivial.
fn unknown_code(
    arena: &CoreArena,
    code: ValueId,
) -> Knowledge
{
    match arena.value(code) {
        | Some(&(Value::Hole(_) | Value::Mark { .. })) => Knowledge::Unknown,
        | Some(_) | None => Knowledge::Known,
    }
}

/// Whether the value type `subject` is unknown, read as it stands.
///
/// # Specification
/// - requires: nothing; a dangling id is admitted.
/// - ensures: [`Knowledge::Unknown`] exactly when `subject` is
///   [`ValueType::Unknown`] or a decode whose code is a hole or a mark.
/// - provides: the one reading of "unknown" every consumer of a value type
///   shares, so a named type hole and the anonymous unknown agree.
/// - fails: never; a dangling id reads as known, so a caller that needs it
///   resolved meets it at its own read.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the unknown former, the decode of a hole, the decode of a
///   mark, the decode of a variable and an atom separate the two answers.
/// - witness: `hole::tests::the_decode_of_a_hole_is_unknown_and_of_a_variable_is_not`
#[spec(ensures: |ret| (ret == Knowledge::Unknown) == match arena.value_type(subject) {
    | Some(&ValueType::Unknown) => true,
    | Some(&ValueType::Element { code, .. }) => matches!(arena.value(code), Some(&(Value::Hole(_) | Value::Mark { .. }))),
    | Some(_) | None => false,
})]
#[inline]
#[must_use]
pub fn value_type_knowledge(
    arena: &CoreArena,
    subject: ValueTypeId,
) -> Knowledge
{
    match arena.value_type(subject) {
        | Some(&ValueType::Unknown) => Knowledge::Unknown,
        | Some(&ValueType::Element { code, .. }) => unknown_code(arena, code),
        | Some(_) | None => Knowledge::Known,
    }
}

/// Whether the computation type `subject` is unknown, read as it stands.
///
/// # Specification
/// - requires: nothing; a dangling id is admitted.
/// - ensures: [`Knowledge::Unknown`] exactly when `subject` is
///   [`CompType::Unknown`] or a decode whose code is a hole or a mark.
/// - provides: the computation half of [`value_type_knowledge`].
/// - fails: never; a dangling id reads as known.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the same decision surface as the value reading, over the
///   computation formers.
/// - witness: `hole::tests::the_decode_of_a_hole_is_unknown_and_of_a_variable_is_not`
#[spec(ensures: |ret| (ret == Knowledge::Unknown) == match arena.comp_type(subject) {
    | Some(&CompType::Unknown) => true,
    | Some(&CompType::Element { code, .. }) => matches!(arena.value(code), Some(&(Value::Hole(_) | Value::Mark { .. }))),
    | Some(_) | None => false,
})]
#[inline]
#[must_use]
pub fn comp_type_knowledge(
    arena: &CoreArena,
    subject: CompTypeId,
) -> Knowledge
{
    match arena.comp_type(subject) {
        | Some(&CompType::Unknown) => Knowledge::Unknown,
        | Some(&CompType::Element { code, .. }) => unknown_code(arena, code),
        | Some(_) | None => Knowledge::Known,
    }
}

/// The absence a known type that is not the asked-for former answers.
///
/// # Specification
/// trivial.
const fn mismatched<Matched>() -> Maybe<Matched, matching::Absent>
{
    Maybe::Absent(matching::Absent::Mismatched)
}

/// The absence a dangling id answers.
///
/// # Specification
/// trivial.
const fn dangling<Matched>() -> Maybe<Matched, matching::Absent>
{
    Maybe::Absent(matching::Absent::Dangling)
}

/// Match a value type against the thunk former: `A ▸ U C`.
///
/// # Specification
/// - requires: `subject` is read at its weak head; unfolding is the caller's.
/// - ensures: the body of a thunk type; a freshly minted unknown computation
///   type when `subject` is unknown.
/// - provides: what a thunk checks its body against and what a force runs.
/// - fails: [`matching::Absent::Mismatched`] for another known former,
///   [`matching::Absent::Dangling`] for an id naming no node.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a thunk type, the unknown type, another former and a
///   dangling id separate the four answers.
/// - witness: `hole::tests::the_unknown_type_matches_every_former_with_unknown_components`
/// - witness: `hole::tests::a_known_type_matches_only_its_own_former`
#[spec(ensures: |ret| match ret {
    | Maybe::Present(body) => arena.comp_type(body).is_some(),
    | Maybe::Absent(_) => true,
})]
#[inline]
pub fn matched_thunk(
    arena: &mut CoreArena,
    subject: ValueTypeId,
) -> Maybe<CompTypeId, matching::Absent>
{
    if value_type_knowledge(arena, subject) == Knowledge::Unknown {
        return Maybe::Present(arena.comp_type_unknown());
    }
    match arena.value_type(subject) {
        | Some(&ValueType::Thunk(body)) => Maybe::Present(body),
        | Some(_) => mismatched(),
        | None => dangling(),
    }
}

/// Match a value type against the eager product: `A ▸ A₁ × A₂`.
///
/// # Specification
/// - requires: `subject` is read at its weak head.
/// - ensures: both factors of a product of two components; two freshly minted
///   unknown value types when `subject` is unknown.
/// - provides: what a pair checks its components against.
/// - fails: [`matching::Absent::Mismatched`] for another known former or a
///   product of another arity, [`matching::Absent::Dangling`] for an id naming
///   no node.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`matched_thunk`], over the product former.
/// - witness: `hole::tests::the_unknown_type_matches_every_former_with_unknown_components`
/// - witness: `hole::tests::a_known_type_matches_only_its_own_former`
#[spec(ensures: |ret| match ret {
    | Maybe::Present((first, second)) => arena.value_type(first).is_some() && arena.value_type(second).is_some(),
    | Maybe::Absent(_) => true,
})]
#[inline]
pub fn matched_product(
    arena: &mut CoreArena,
    subject: ValueTypeId,
) -> Maybe<(ValueTypeId, ValueTypeId), matching::Absent>
{
    if value_type_knowledge(arena, subject) == Knowledge::Unknown {
        let unknown = arena.value_type_unknown();
        return Maybe::Present((unknown, unknown));
    }
    match arena.value_type(subject) {
        | Some(&ValueType::Product(ref components)) => match **components {
            | [first, second] => Maybe::Present((first, second)),
            | _ => mismatched(),
        },
        | Some(_) => mismatched(),
        | None => dangling(),
    }
}

/// Match a value type against the sum: `A ▸ A₁ + A₂`.
///
/// # Specification
/// - requires: `subject` is read at its weak head.
/// - ensures: both summands of a sum of two summands; two freshly minted
///   unknown value types when `subject` is unknown.
/// - provides: what an injection checks its payload against and what a case
///   binds in each branch.
/// - fails: [`matching::Absent::Mismatched`] for another known former or a sum
///   of another arity, [`matching::Absent::Dangling`] for an id naming no node.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`matched_thunk`], over the sum former.
/// - witness: `hole::tests::the_unknown_type_matches_every_former_with_unknown_components`
/// - witness: `hole::tests::a_known_type_matches_only_its_own_former`
#[spec(ensures: |ret| match ret {
    | Maybe::Present((left, right)) => arena.value_type(left).is_some() && arena.value_type(right).is_some(),
    | Maybe::Absent(_) => true,
})]
#[inline]
pub fn matched_sum(
    arena: &mut CoreArena,
    subject: ValueTypeId,
) -> Maybe<(ValueTypeId, ValueTypeId), matching::Absent>
{
    if value_type_knowledge(arena, subject) == Knowledge::Unknown {
        let unknown = arena.value_type_unknown();
        return Maybe::Present((unknown, unknown));
    }
    match arena.value_type(subject) {
        | Some(&ValueType::Sum(ref summands)) => match **summands {
            | [left, right] => Maybe::Present((left, right)),
            | _ => mismatched(),
        },
        | Some(_) => mismatched(),
        | None => dangling(),
    }
}

/// Match a value type against the static Pi.
///
/// # Specification
/// - requires: `subject` is read at its weak head.
/// - ensures: the domain and codomain of a static Pi, both in the ambient
///   context; two freshly minted unknown value types when `subject` is unknown.
/// - provides: what a static lambda checks its body against and what a static
///   application reads.
/// - fails: [`matching::Absent::Mismatched`] for another known former,
///   [`matching::Absent::Dangling`] for an id naming no node.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`matched_thunk`], over the static Pi.
/// - witness: `hole::tests::the_unknown_type_matches_every_former_with_unknown_components`
/// - witness: `hole::tests::a_known_type_matches_only_its_own_former`
#[spec(ensures: |ret| match ret {
    | Maybe::Present((domain, codomain)) => arena.value_type(domain).is_some() && arena.value_type(codomain).is_some(),
    | Maybe::Absent(_) => true,
})]
#[inline]
pub fn matched_static_pi(
    arena: &mut CoreArena,
    subject: ValueTypeId,
) -> Maybe<(ValueTypeId, ValueTypeId), matching::Absent>
{
    if value_type_knowledge(arena, subject) == Knowledge::Unknown {
        let unknown = arena.value_type_unknown();
        return Maybe::Present((unknown, unknown));
    }
    match arena.value_type(subject) {
        | Some(&ValueType::StaticPi { domain, codomain }) => Maybe::Present((domain, codomain)),
        | Some(_) => mismatched(),
        | None => dangling(),
    }
}

/// Match a computation type against the returner: `C ▸ F A`.
///
/// # Specification
/// - requires: `subject` is read at its weak head.
/// - ensures: the result of a returner; a freshly minted unknown value type
///   when `subject` is unknown.
/// - provides: what a return checks its value against and what a bind binds.
/// - fails: [`matching::Absent::Mismatched`] for another known former,
///   [`matching::Absent::Dangling`] for an id naming no node.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`matched_thunk`], over the returner.
/// - witness: `hole::tests::the_unknown_type_matches_every_former_with_unknown_components`
/// - witness: `hole::tests::a_known_type_matches_only_its_own_former`
#[spec(ensures: |ret| match ret {
    | Maybe::Present(result) => arena.value_type(result).is_some(),
    | Maybe::Absent(_) => true,
})]
#[inline]
pub fn matched_returner(
    arena: &mut CoreArena,
    subject: CompTypeId,
) -> Maybe<ValueTypeId, matching::Absent>
{
    if comp_type_knowledge(arena, subject) == Knowledge::Unknown {
        return Maybe::Present(arena.value_type_unknown());
    }
    match arena.comp_type(subject) {
        | Some(&CompType::Returner { result, .. }) => Maybe::Present(result),
        | Some(_) => mismatched(),
        | None => dangling(),
    }
}

/// Match a computation type against the function formers: `C ▸ A → C'`.
///
/// # Specification
/// - requires: `subject` is read at its weak head.
/// - ensures: an arrow's domain and codomain in the ambient scope; a dependent
///   arrow's under the binder; for an unknown `subject`, a freshly minted
///   unknown domain and codomain in the ambient scope, since the unknown
///   mentions no binder.
/// - provides: what a lambda checks its body against and what an application
///   checks its argument against.
/// - fails: [`matching::Absent::Mismatched`] for another known former,
///   [`matching::Absent::Dangling`] for an id naming no node.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an arrow, a dependent arrow, the unknown type, another
///   former and a dangling id separate the scopes and the absences.
/// - witness: `hole::tests::the_unknown_type_matches_every_former_with_unknown_components`
/// - witness: `hole::tests::a_known_type_matches_only_its_own_former`
#[spec(ensures: |ret| match ret {
    | Maybe::Present(function) => arena.value_type(function.domain).is_some()
        && arena.comp_type(function.codomain).is_some()
        && (function.scope == CodomainScope::UnderBinder) == matches!(arena.comp_type(subject), Some(&CompType::Pi { .. })),
    | Maybe::Absent(_) => true,
})]
#[inline]
pub fn matched_function(
    arena: &mut CoreArena,
    subject: CompTypeId,
) -> Maybe<MatchedFunction, matching::Absent>
{
    if comp_type_knowledge(arena, subject) == Knowledge::Unknown {
        let domain = arena.value_type_unknown();
        let codomain = arena.comp_type_unknown();
        return Maybe::Present(MatchedFunction {
            domain,
            codomain,
            scope: CodomainScope::Ambient,
        });
    }
    match arena.comp_type(subject) {
        | Some(&CompType::Arrow { domain, codomain }) => Maybe::Present(MatchedFunction {
            domain,
            codomain,
            scope: CodomainScope::Ambient,
        }),
        | Some(&CompType::Pi { domain, codomain }) => Maybe::Present(MatchedFunction {
            domain,
            codomain,
            scope: CodomainScope::UnderBinder,
        }),
        | Some(_) => mismatched(),
        | None => dangling(),
    }
}

/// Match a value type against the native List former: `A ▸ List A₁`.
///
/// # Specification
/// - requires: `subject` is read at its weak head.
/// - ensures: the element type of a List; a freshly minted unknown value type
///   when `subject` is unknown.
/// - provides: what a nil and a cons check against.
/// - fails: [`matching::Absent::Mismatched`] for another known former,
///   [`matching::Absent::Dangling`] for an id naming no node.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`matched_thunk`], over the List former.
/// - witness: `hole::tests::the_unknown_type_matches_every_former_with_unknown_components`
/// - witness: `hole::tests::a_known_type_matches_only_its_own_former`
#[spec(ensures: |ret| match ret {
    | Maybe::Present(element) => arena.value_type(element).is_some(),
    | Maybe::Absent(_) => true,
})]
#[inline]
pub fn matched_list(
    arena: &mut CoreArena,
    subject: ValueTypeId,
) -> Maybe<ValueTypeId, matching::Absent>
{
    if value_type_knowledge(arena, subject) == Knowledge::Unknown {
        return Maybe::Present(arena.value_type_unknown());
    }
    match arena.value_type(subject) {
        | Some(&ValueType::List(element)) => Maybe::Present(element),
        | Some(_) => mismatched(),
        | None => dangling(),
    }
}

/// Match a value type against the first-class stack: `A ▸ Stack C₁ C₂`.
///
/// # Specification
/// - requires: `subject` is read at its weak head.
/// - ensures: the input and output computation types of a stack; two freshly
///   minted unknown computation types when `subject` is unknown.
/// - provides: what a stack literal checks its frames against and what a
///   resumption feeds.
/// - fails: [`matching::Absent::Mismatched`] for another known former,
///   [`matching::Absent::Dangling`] for an id naming no node.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`matched_thunk`], over the stack former.
/// - witness: `hole::tests::the_unknown_type_matches_every_former_with_unknown_components`
/// - witness: `hole::tests::a_known_type_matches_only_its_own_former`
#[spec(ensures: |ret| match ret {
    | Maybe::Present((input, output)) => arena.comp_type(input).is_some() && arena.comp_type(output).is_some(),
    | Maybe::Absent(_) => true,
})]
#[inline]
pub fn matched_stack(
    arena: &mut CoreArena,
    subject: ValueTypeId,
) -> Maybe<(CompTypeId, CompTypeId), matching::Absent>
{
    if value_type_knowledge(arena, subject) == Knowledge::Unknown {
        let unknown = arena.comp_type_unknown();
        return Maybe::Present((unknown, unknown));
    }
    match arena.value_type(subject) {
        | Some(&ValueType::Stack { input, output }) => Maybe::Present((input, output)),
        | Some(_) => mismatched(),
        | None => dangling(),
    }
}

/// Match a computation type against the lazy pair: `C ▸ C₁ & C₂`.
///
/// # Specification
/// - requires: `subject` is read at its weak head.
/// - ensures: both components of a lazy pair, left first; two freshly minted
///   unknown computation types when `subject` is unknown.
/// - provides: what a projection selects.
/// - fails: [`matching::Absent::Mismatched`] for another known former,
///   [`matching::Absent::Dangling`] for an id naming no node.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`matched_thunk`], over the lazy pair.
/// - witness: `hole::tests::the_unknown_type_matches_every_former_with_unknown_components`
/// - witness: `hole::tests::a_known_type_matches_only_its_own_former`
#[spec(ensures: |ret| match ret {
    | Maybe::Present((first, second)) => arena.comp_type(first).is_some() && arena.comp_type(second).is_some(),
    | Maybe::Absent(_) => true,
})]
#[inline]
pub fn matched_with(
    arena: &mut CoreArena,
    subject: CompTypeId,
) -> Maybe<(CompTypeId, CompTypeId), matching::Absent>
{
    if comp_type_knowledge(arena, subject) == Knowledge::Unknown {
        let unknown = arena.comp_type_unknown();
        return Maybe::Present((unknown, unknown));
    }
    match arena.comp_type(subject) {
        | Some(&CompType::With(first, second)) => Maybe::Present((first, second)),
        | Some(_) => mismatched(),
        | None => dangling(),
    }
}

#[cfg(test)]
mod tests
{
    use gandr_kernel_strata::Level;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::GroundSort;
    use quenchant_shape::shape::Maybe;

    use super::CodomainScope;
    use super::HoleId;
    use super::Knowledge;
    use super::MarkIndex;
    use super::comp_type_knowledge;
    use super::matched_function;
    use super::matched_list;
    use super::matched_product;
    use super::matched_returner;
    use super::matched_stack;
    use super::matched_static_pi;
    use super::matched_sum;
    use super::matched_thunk;
    use super::matched_with;
    use super::matching;
    use super::value_type_knowledge;
    use crate::arena::CoreArena;
    use crate::classifier::Sort;
    use crate::syntax::CompType;
    use crate::syntax::ValueType;
    use crate::syntax::Zone;

    #[test]
    fn the_decode_of_a_hole_is_unknown_and_of_a_variable_is_not()
    {
        let mut arena = CoreArena::new();
        let unknown = arena.value_type_unknown();
        let hole = arena.value_hole(HoleId::from(3_u32));
        let named = arena.value_type_element(hole, Level::zero());
        let marked = arena.value_mark(MarkIndex::from(0_u32), hole);
        let marked = arena.value_type_element(marked, Level::zero());
        let variable = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let decoded = arena.value_type_element(variable, Level::zero());
        let atom = arena.value_type_base(BaseType::Integer);
        for (subject, knowledge) in [
            (unknown, Knowledge::Unknown),
            (named, Knowledge::Unknown),
            (marked, Knowledge::Unknown),
            (decoded, Knowledge::Known),
            (atom, Knowledge::Known),
        ] {
            assert_eq!(value_type_knowledge(&arena, subject), knowledge);
        }
        assert_eq!(
            value_type_knowledge(&CoreArena::new(), unknown),
            Knowledge::Known,
            "a dangling id reads as known"
        );
        let unknown = arena.comp_type_unknown();
        let named = arena.comp_type_element(hole, Level::zero());
        let decoded = arena.comp_type_element(variable, Level::zero());
        let returner = arena.comp_type_returner(atom);
        for (subject, knowledge) in [
            (unknown, Knowledge::Unknown),
            (named, Knowledge::Unknown),
            (decoded, Knowledge::Known),
            (returner, Knowledge::Known),
        ] {
            assert_eq!(comp_type_knowledge(&arena, subject), knowledge);
        }
    }

    #[test]
    fn the_unknown_type_matches_every_former_with_unknown_components()
    {
        let mut arena = CoreArena::new();
        let unknown = arena.value_type_unknown();
        let hole = arena.value_hole(HoleId::from(1_u32));
        let named = arena.value_type_element(hole, Level::zero());
        for subject in [unknown, named] {
            let Maybe::Present(body) = matched_thunk(&mut arena, subject)
            else {
                panic!("the unknown type matches a thunk");
            };
            assert_eq!(arena.comp_type(body), Some(&CompType::Unknown));
            for matched in [
                matched_product(&mut arena, subject),
                matched_sum(&mut arena, subject),
                matched_static_pi(&mut arena, subject),
            ] {
                let Maybe::Present((first, second)) = matched
                else {
                    panic!("the unknown type matches every binary former");
                };
                assert_eq!(arena.value_type(first), Some(&ValueType::Unknown));
                assert_eq!(arena.value_type(second), Some(&ValueType::Unknown));
            }
            let Maybe::Present(element) = matched_list(&mut arena, subject)
            else {
                panic!("the unknown type matches a List");
            };
            assert_eq!(arena.value_type(element), Some(&ValueType::Unknown));
            let Maybe::Present((input, output)) = matched_stack(&mut arena, subject)
            else {
                panic!("the unknown type matches a stack");
            };
            assert_eq!(arena.comp_type(input), Some(&CompType::Unknown));
            assert_eq!(arena.comp_type(output), Some(&CompType::Unknown));
        }
        let unknown = arena.comp_type_unknown();
        let Maybe::Present(result) = matched_returner(&mut arena, unknown)
        else {
            panic!("the unknown type matches a returner");
        };
        assert_eq!(arena.value_type(result), Some(&ValueType::Unknown));
        let Maybe::Present(function) = matched_function(&mut arena, unknown)
        else {
            panic!("the unknown type matches a function");
        };
        assert_eq!(
            arena.value_type(function.domain()),
            Some(&ValueType::Unknown)
        );
        assert_eq!(
            arena.comp_type(function.codomain()),
            Some(&CompType::Unknown)
        );
        assert_eq!(function.scope(), CodomainScope::Ambient);
        let Maybe::Present((first, second)) = matched_with(&mut arena, unknown)
        else {
            panic!("the unknown type matches a lazy pair");
        };
        assert_eq!(arena.comp_type(first), Some(&CompType::Unknown));
        assert_eq!(arena.comp_type(second), Some(&CompType::Unknown));
    }

    #[test]
    fn a_known_type_matches_only_its_own_former()
    {
        let mut arena = CoreArena::new();
        let atom = arena.value_type_base(BaseType::Integer);
        let text = arena.value_type_base(BaseType::String);
        let product = arena.value_type_product(&[atom, text]);
        let sum = arena.value_type_sum(&[text, atom]);
        let returner = arena.comp_type_returner(atom);
        let thunk = arena.value_type_thunk(returner);
        let universe = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
        let static_pi = arena.value_type_static_pi(universe, universe);
        let arrow = arena.comp_type_arrow(atom, returner);
        let pi = arena.comp_type_pi(text, returner);
        let list = arena.value_type_list(atom);
        let stack = arena.value_type_stack(returner, arrow);
        let with = arena.comp_type_with(returner, arrow);
        assert_eq!(matched_thunk(&mut arena, thunk), Maybe::Present(returner));
        assert_eq!(
            matched_product(&mut arena, product),
            Maybe::Present((atom, text))
        );
        assert_eq!(matched_sum(&mut arena, sum), Maybe::Present((text, atom)));
        assert_eq!(
            matched_static_pi(&mut arena, static_pi),
            Maybe::Present((universe, universe))
        );
        assert_eq!(matched_returner(&mut arena, returner), Maybe::Present(atom));
        assert_eq!(matched_list(&mut arena, list), Maybe::Present(atom));
        assert_eq!(
            matched_stack(&mut arena, stack),
            Maybe::Present((returner, arrow))
        );
        assert_eq!(
            matched_with(&mut arena, with),
            Maybe::Present((returner, arrow))
        );
        let Maybe::Present(ambient) = matched_function(&mut arena, arrow)
        else {
            panic!("an arrow matches a function");
        };
        assert_eq!(
            (ambient.domain(), ambient.codomain(), ambient.scope()),
            (atom, returner, CodomainScope::Ambient)
        );
        let Maybe::Present(dependent) = matched_function(&mut arena, pi)
        else {
            panic!("a dependent arrow matches a function");
        };
        assert_eq!(
            (dependent.domain(), dependent.codomain(), dependent.scope()),
            (text, returner, CodomainScope::UnderBinder)
        );
        let mismatched = matching::Absent::Mismatched;
        assert_eq!(matched_thunk(&mut arena, atom), Maybe::Absent(mismatched));
        assert_eq!(matched_product(&mut arena, sum), Maybe::Absent(mismatched));
        assert_eq!(matched_sum(&mut arena, product), Maybe::Absent(mismatched));
        assert_eq!(
            matched_static_pi(&mut arena, product),
            Maybe::Absent(mismatched)
        );
        assert_eq!(
            matched_returner(&mut arena, arrow),
            Maybe::Absent(mismatched)
        );
        assert_eq!(
            matched_function(&mut arena, returner),
            Maybe::Absent(mismatched)
        );
        assert_eq!(matched_list(&mut arena, product), Maybe::Absent(mismatched));
        assert_eq!(matched_stack(&mut arena, list), Maybe::Absent(mismatched));
        assert_eq!(matched_with(&mut arena, arrow), Maybe::Absent(mismatched));
        assert_eq!(
            matched_thunk(&mut CoreArena::new(), thunk),
            Maybe::Absent(matching::Absent::Dangling)
        );
    }
}
