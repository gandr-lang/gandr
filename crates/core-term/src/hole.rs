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
//!
//! # Typed holes, marks and the unknown type
//!
//! `Value::Hole` and `Computation::Hole` are holes the author left in a body,
//! named by a `HoleId`; `Value::Mark` and `Computation::Mark` wrap a term an
//! elaboration found ill-typed, naming the entry of its mark table by a
//! `MarkIndex`. `ValueType::Unknown` and `CompType::Unknown` are the types a
//! hole and a mark have when nothing hands them one (Hazelnut, POPL 2017). All
//! six are elaboration-only: the kernel's closed vocabulary has none of them,
//! so the bridge that erases a core term refuses a hole and the unknown type
//! and erases a mark to its body.
//!
//! A rule that demands a former of a type reads it through the matched-type
//! operations in `hole`: a known type answers its former's components or that
//! it has another former, and the unknown type answers its former with unknown
//! components, so an introduction checks against the unknown type and an
//! elimination of a term of the unknown type goes on. A decode of a hole or a
//! mark is the unknown type too, read through `value_type_knowledge` and
//! `comp_type_knowledge`, without minting a node. A matched dependent arrow
//! reports whether its codomain stands under the argument's binder, so the
//! checker shifts only what the scoping requires.
//!
//! `fill_hole` replaces every hole of a name by its fill, written in the
//! context the hole stands in, so a fill is a substitution of syntax rather
//! than of a value under binders (Live Functional Programming with Typed Holes,
//! POPL 2019); `wrap_marks` wraps each named node once, which is how a total
//! elaboration returns its marked term (Zhao et al., POPL 2024). Both run on
//! the binder machines' heap task stack and reuse every subterm they do not
//! change. The alternative was a hole carrying its expected type, which ties
//! the term to one elaboration; the type is the judgement's answer, and the
//! hole is only its name.
//!
//! A hole a call nominates for an implicit it omits ([`HoleId::nominated`]),
//! or the elaborator for a wildcard `_` ([`HoleId::wildcard`]), stands for a
//! metavariable, whose solution is written under the binders the call or the
//! wildcard stands under. `fill_value_hole`, `fill_value_type_hole` and
//! `fill_comp_type_hole` place the solution wherever the hole stands, raised
//! past the binders between: inside a type the call's head was instantiated
//! at, or inside another solution, the hole stands deeper than its scope.

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
/// The elaborator issues hole names; this crate compares them and splits
/// them in two halves, so two holes with one name are one hole filled at
/// once. A hole the text writes is named in the lower half, by its place; a
/// hole the elaborator nominates as a metavariable is named in the upper
/// half: one standing for an implicit the text omits in its upper quarter,
/// counted down from the last name ([`HoleId::nominated`]), and one standing
/// for a wildcard `_` the text writes in its lower quarter, counted up from
/// the half's first name ([`HoleId::wildcard`]). No two of the three share a
/// name, and a hole's name says which it is.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct HoleId(u32);

/// Where a hole comes from, read off the part of the names its own is in.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum HoleOrigin
{
    /// A hole the text writes, which its author fills.
    Written,
    /// A hole the elaborator nominates for an implicit the text omits, which
    /// the checker solves as a metavariable.
    Nominated,
    /// A hole the elaborator nominates for a wildcard `_` the text writes,
    /// which the checker solves as a metavariable.
    Wildcard,
}

/// The place of a hole among those an elaborator nominates, counted from
/// zero.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct NominationIndex(u32);

impl From<u32> for NominationIndex
{
    /// Read a `u32` as a nomination's place.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(place: u32) -> Self
    {
        Self(place)
    }
}

impl HoleId
{
    /// The first name of the upper half, the nominated holes'.
    const NOMINATED: u32 = 1 << 31_u32;

    /// The first name of the upper half's upper quarter, the holes nominated
    /// for omitted implicits; the quarter below it is the wildcards'.
    const OMITTED: u32 = 3 << 30_u32;

    /// How many names each quarter of the upper half holds.
    const QUARTER: u32 = 1 << 30_u32;

    /// The name of the `index`th hole an elaborator nominates for an implicit
    /// the text omits: the last name less `index`, which is `index`'s
    /// complement.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a nominated name for each `index` below a quarter's size,
    ///   distinct indices naming distinct holes; `None` past it.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the first and the last index of the quarter, and the
    ///   index past it, separate the names from the refusal; a written name
    ///   below the half and a wildcard's name are never nominated.
    /// - witness: `hole::tests::a_nominated_hole_shares_no_name_with_a_written_one`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| match ret {
        Some(hole) => matches!(hole.origin(), HoleOrigin::Nominated) && hole.0 == !index.0,
        None => index.0 >= Self::QUARTER,
    })]
    pub const fn nominated(index: NominationIndex) -> Option<Self>
    {
        if index.0 >= Self::QUARTER {
            return None;
        }
        Some(Self(!index.0))
    }

    /// The name of the `index`th hole an elaborator nominates for a wildcard
    /// `_` the text writes: the upper half's first name plus `index`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a wildcard's name for each `index` below a quarter's size,
    ///   distinct indices naming distinct holes; `None` past it.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::nominated`], over the quarter below.
    /// - witness: `hole::tests::a_nominated_hole_shares_no_name_with_a_written_one`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| match ret {
        Some(hole) => matches!(hole.origin(), HoleOrigin::Wildcard) && hole.0 == (Self::NOMINATED | index.0),
        None => index.0 >= Self::QUARTER,
    })]
    pub const fn wildcard(index: NominationIndex) -> Option<Self>
    {
        if index.0 >= Self::QUARTER {
            return None;
        }
        Some(Self(Self::NOMINATED | index.0))
    }

    /// The name of the `index`th hole a checker nominates for a carrier a
    /// crossing solves: the omitted implicits' quarter's first name plus
    /// `index`. [`Self::nominated`] counts down from the quarter's last name,
    /// so the two meet only past a quarter's worth of names between them; a
    /// crossing's hole is declared to a solver of its own and never stands in
    /// a body.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a nominated name for each `index` below a quarter's size,
    ///   distinct indices naming distinct holes and `index` naming the hole
    ///   [`Self::nominated`] names for the quarter's last index less `index`;
    ///   `None` past it.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the first index names the quarter's first name, and
    ///   the index past the quarter is refused.
    /// - witness: `hole::tests::a_crossing_hole_counts_up_from_the_quarter_nominated_counts_down`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| match ret {
        Some(hole) => matches!(hole.origin(), HoleOrigin::Nominated) && hole.0 == (Self::OMITTED | index.0),
        None => index.0 >= Self::QUARTER,
    })]
    pub const fn crossing(index: NominationIndex) -> Option<Self>
    {
        if index.0 >= Self::QUARTER {
            return None;
        }
        Some(Self(Self::OMITTED | index.0))
    }

    /// Where this hole comes from: nominated for an omitted implicit in the
    /// upper half's upper quarter, for a wildcard in its lower quarter, and
    /// written below the half.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn origin(self) -> HoleOrigin
    {
        if self.0 >= Self::OMITTED {
            HoleOrigin::Nominated
        }
        else if self.0 >= Self::NOMINATED {
            HoleOrigin::Wildcard
        }
        else {
            HoleOrigin::Written
        }
    }
}

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
        Some(&(Value::Hole(_) | Value::Mark { .. })) => Knowledge::Unknown,
        Some(_) | None => Knowledge::Known,
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
        Some(&ValueType::Unknown) => Knowledge::Unknown,
        Some(&ValueType::Element { code, .. }) => unknown_code(arena, code),
        Some(_) | None => Knowledge::Known,
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
        Some(&CompType::Unknown) => Knowledge::Unknown,
        Some(&CompType::Element { code, .. }) => unknown_code(arena, code),
        Some(_) | None => Knowledge::Known,
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
        Some(&ValueType::Thunk(body)) => Maybe::Present(body),
        Some(_) => mismatched(),
        None => dangling(),
    }
}

/// The components a product, a sum or a lazy product matched.
///
/// A known former gives its own, in order. The unknown type gives one unknown
/// type every component stands at, however many the introduction or the
/// elimination has.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Components<T = ValueTypeId>
{
    /// A known former's components, in order.
    Known(alloc::boxed::Box<[T]>),
    /// The unknown type: every component is this freshly minted unknown type.
    Unknown(T),
}

/// Match a value type against the eager product: `A ▸ A₁ × … × Aₙ`.
///
/// # Specification
/// - requires: `subject` is read at its weak head.
/// - ensures: the components of a product of any arity, the empty one the unit
///   type's; one freshly minted unknown value type when `subject` is unknown.
/// - provides: what a tuple checks its components against.
/// - fails: [`matching::Absent::Mismatched`] for another known former,
///   [`matching::Absent::Dangling`] for an id naming no node.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`matched_thunk`], over the product former; the unit
///   type separates a product of no components from a mismatch.
/// - witness: `hole::tests::the_unknown_type_matches_every_former_with_unknown_components`
/// - witness: `hole::tests::a_known_type_matches_only_its_own_former`
#[spec(ensures: |ret| match ret {
    | Maybe::Present(Components::Known(ref parts)) => matches!(arena.value_type(subject), Some(ValueType::Product(held)) if held == parts),
    | Maybe::Present(Components::Unknown(unknown)) => arena.value_type(unknown) == Some(&ValueType::Unknown),
    | Maybe::Absent(_) => true,
})]
#[inline]
pub fn matched_product(
    arena: &mut CoreArena,
    subject: ValueTypeId,
) -> Maybe<Components, matching::Absent>
{
    if value_type_knowledge(arena, subject) == Knowledge::Unknown {
        return Maybe::Present(Components::Unknown(arena.value_type_unknown()));
    }
    match arena.value_type(subject) {
        Some(&ValueType::Product(ref components)) => {
            Maybe::Present(Components::Known(components.clone()))
        },
        Some(_) => mismatched(),
        None => dangling(),
    }
}

/// Match a value type against the sum: `A ▸ A₁ + … + Aₙ`.
///
/// # Specification
/// - requires: `subject` is read at its weak head.
/// - ensures: the summands of a sum of any arity, the empty one the empty
///   type's; one freshly minted unknown value type when `subject` is unknown.
/// - provides: what an injection checks its payload against and what a case
///   binds in each branch.
/// - fails: [`matching::Absent::Mismatched`] for another known former,
///   [`matching::Absent::Dangling`] for an id naming no node.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`matched_thunk`], over the sum former.
/// - witness: `hole::tests::the_unknown_type_matches_every_former_with_unknown_components`
/// - witness: `hole::tests::a_known_type_matches_only_its_own_former`
#[spec(ensures: |ret| match ret {
    | Maybe::Present(Components::Known(ref parts)) => matches!(arena.value_type(subject), Some(ValueType::Sum(held)) if held == parts),
    | Maybe::Present(Components::Unknown(unknown)) => arena.value_type(unknown) == Some(&ValueType::Unknown),
    | Maybe::Absent(_) => true,
})]
#[inline]
pub fn matched_sum(
    arena: &mut CoreArena,
    subject: ValueTypeId,
) -> Maybe<Components, matching::Absent>
{
    if value_type_knowledge(arena, subject) == Knowledge::Unknown {
        return Maybe::Present(Components::Unknown(arena.value_type_unknown()));
    }
    match arena.value_type(subject) {
        Some(&ValueType::Sum(ref summands)) => Maybe::Present(Components::Known(summands.clone())),
        Some(_) => mismatched(),
        None => dangling(),
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
        Some(&ValueType::StaticPi { domain, codomain }) => Maybe::Present((domain, codomain)),
        Some(_) => mismatched(),
        None => dangling(),
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
        Some(&CompType::Returner { result, .. }) => Maybe::Present(result),
        Some(_) => mismatched(),
        None => dangling(),
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
        Some(&CompType::Arrow { domain, codomain }) => Maybe::Present(MatchedFunction {
            domain,
            codomain,
            scope: CodomainScope::Ambient,
        }),
        Some(&CompType::Pi { domain, codomain }) => Maybe::Present(MatchedFunction {
            domain,
            codomain,
            scope: CodomainScope::UnderBinder,
        }),
        Some(_) => mismatched(),
        None => dangling(),
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
        Some(&ValueType::List(element)) => Maybe::Present(element),
        Some(_) => mismatched(),
        None => dangling(),
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
        Some(&ValueType::Stack { input, output }) => Maybe::Present((input, output)),
        Some(_) => mismatched(),
        None => dangling(),
    }
}

/// Match a computation type against the lazy product: `C ▸ C₁ & … & Cₙ`.
///
/// # Specification
/// - requires: `subject` is read at its weak head.
/// - ensures: the components of a lazy product of any arity, in order, the
///   empty one the terminal type's; one freshly minted unknown computation type
///   when `subject` is unknown.
/// - provides: what a lazy tuple checks its components against and what a
///   projection selects.
/// - fails: [`matching::Absent::Mismatched`] for another known former,
///   [`matching::Absent::Dangling`] for an id naming no node.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`matched_product`], over the lazy product.
/// - witness: `hole::tests::the_unknown_type_matches_every_former_with_unknown_components`
/// - witness: `hole::tests::a_known_type_matches_only_its_own_former`
#[spec(ensures: |ret| match ret {
    | Maybe::Present(Components::Known(ref parts)) => matches!(arena.comp_type(subject), Some(&CompType::With(ref held)) if held == parts),
    | Maybe::Present(Components::Unknown(unknown)) => arena.comp_type(unknown) == Some(&CompType::Unknown),
    | Maybe::Absent(_) => true,
})]
#[inline]
pub fn matched_with(
    arena: &mut CoreArena,
    subject: CompTypeId,
) -> Maybe<Components<CompTypeId>, matching::Absent>
{
    if comp_type_knowledge(arena, subject) == Knowledge::Unknown {
        return Maybe::Present(Components::Unknown(arena.comp_type_unknown()));
    }
    match arena.comp_type(subject) {
        Some(&CompType::With(ref components)) => {
            Maybe::Present(Components::Known(components.clone()))
        },
        Some(_) => mismatched(),
        None => dangling(),
    }
}

#[cfg(test)]
mod tests;
