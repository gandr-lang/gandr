//! The entity-attribute layer: the closed [`AttributeRegistry`], the payload
//! [`PayloadVerdict`] each schema returns, and the [`AttributeTable`] a lowered
//! module carries beside its declarations.
//!
//! # The side table is keyed by content identity
//!
//! An entry is filed under the content digest of the declaration form the
//! attribute decorates, never under that declaration's position in a list. A
//! position is invalidated by an edit anywhere earlier in the file; a digest
//! is invalidated only by an edit inside the declaration it is about. The
//! molded tree makes a leading attribute block part of the declaration form it
//! precedes, so the digest folds the declaration's own attributes: editing an
//! attribute re-keys that declaration's entries, and an edit anywhere else
//! leaves the key alone.
//!
//! # Every schema here is inert
//!
//! The lowered term is neither read nor written by the attribute pass: a
//! payload lowers to its own core value, filed here, and nothing about the
//! decorated declaration's core term depends on it. The semantic tier — an
//! attribute reflected into the core term because it changes what the entity
//! *is* — has no representation in this crate.
//!
//! # An unknown name gets a bounded suggestion
//!
//! The registry is closed and small, so a misspelling is answered with the one
//! nearest registered name within a fixed edit distance. The bound is what
//! keeps the suggestion an aid rather than a guess: past it the nearest entry
//! carries no information about what the author meant.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use core::fmt;

use gandr_core_term::ValueId;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::NodeDigest;
use quenchant_shape::shape::Maybe;

use crate::form::Former;
use crate::resolve::SurfaceName;

quenchant_shape::reason_enum! {
    /// Why the registry answers nothing for a spelling.
    pub mod registry {
        /// The registry holds no entry for the spelling.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No registered attribute is spelled so.
            Unregistered,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why an unknown attribute carries no suggestion.
    pub mod suggestion {
        /// No registered name sits near the spelling.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// Every registered name sits past the suggestion bound.
            BeyondBound,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why an attribute entry carries no payload.
    pub mod payload {
        /// The attribute was filed with no payload value.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The attribute is a bare marker, whose schema takes no payload.
            Marker,
        }
    }
}

/// The furthest an unknown attribute name may sit from a registered one and
/// still be answered with it.
const SUGGESTION_BOUND: EditDistance = EditDistance(2_usize);

/// One name the attribute registry holds.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RegisteredAttribute(&'static str);

impl AsRef<str> for RegisteredAttribute
{
    /// The registry's own spelling of the name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        self.0
    }
}

impl fmt::Display for RegisteredAttribute
{
    /// Writes the registry's own spelling of the name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(self.0)
    }
}

/// The number of single-character edits between two spellings.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct EditDistance(usize);

impl From<usize> for EditDistance
{
    /// The distance of `edits` edits.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(edits: usize) -> Self
    {
        Self(edits)
    }
}

impl From<EditDistance> for usize
{
    /// The number of edits `distance` holds.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(distance: EditDistance) -> Self
    {
        distance.0
    }
}

/// What an attribute's payload must be, if it takes one at all.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum AttributeSchema
{
    /// A bare marker: the attribute takes no payload.
    Marker,
    /// One integer literal.
    Integer,
    /// One text literal.
    Text,
}

impl fmt::Display for AttributeSchema
{
    /// Writes what the schema takes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            | Self::Marker => f.write_str("no payload"),
            | Self::Integer => f.write_str("an integer payload"),
            | Self::Text => f.write_str("a text payload"),
        }
    }
}

/// What an attribute's payload was written as.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum PayloadForm
{
    /// No payload was written.
    Absent,
    /// An integer literal.
    Integer,
    /// A text literal.
    Text,
    /// A value of the fragment that is neither literal form.
    OtherValue,
}

impl fmt::Display for PayloadForm
{
    /// Writes what was written.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            | Self::Absent => f.write_str("no payload"),
            | Self::Integer => f.write_str("an integer payload"),
            | Self::Text => f.write_str("a text payload"),
            | Self::OtherValue => f.write_str("a non-literal payload"),
        }
    }
}

/// Whether a schema admits the payload it was written with.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum PayloadVerdict
{
    /// The payload matches the schema, absence included.
    Admitted,
    /// The schema takes a payload and none was written.
    Missing,
    /// A payload was written that the schema does not admit, a payload on a
    /// bare marker included.
    IllTyped,
}

/// The registry: the closed set of attribute names and the schema of each.
///
/// Closed because a schema decides how a payload is read: a name outside this
/// table has no reading at all, and answering it with a default would let a
/// misspelling behave like the attribute it was not.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct AttributeRegistry;

/// Every registered attribute, with its schema.
const REGISTRY: [(&str, AttributeSchema); 4_usize] = [
    ("checks", AttributeSchema::Marker),
    ("owes", AttributeSchema::Integer),
    ("refuses", AttributeSchema::Text),
    ("runs", AttributeSchema::Text),
];

impl AttributeRegistry
{
    /// Every registered name, in registry order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn names() -> Vec<RegisteredAttribute>
    {
        REGISTRY
            .into_iter()
            .map(|(spelling, _schema)| RegisteredAttribute(spelling))
            .collect()
    }

    /// The registry entry `name` spells, when the table holds it.
    ///
    /// # Specification
    /// - requires: nothing — every identifier is admissible input.
    /// - ensures: exactly the entry whose spelling equals `name`, paired with
    ///   its schema; the unregistered absence for every other identifier, so
    ///   the lookup has no fallthrough and a misspelling cannot acquire a
    ///   reading.
    /// - provides: the resolution step every attribute takes before its payload
    ///   is looked at.
    /// - fails: never; a name the registry does not hold is an absence, which
    ///   the caller reports as an unknown attribute with a bounded suggestion.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the registry is a finite class, enumerated
    ///   exhaustively with each row's exact schema asserted, and separated from
    ///   the miss arm by a near miss, a case shift and the empty spelling, each
    ///   asserted absent.
    /// - witness: `attribute::tests::every_registered_attribute_answers_its_schema`
    /// - witness: `attribute::tests::an_unregistered_name_answers_nothing`
    #[inline]
    pub fn lookup(
        name: SurfaceName<'_>
    ) -> Maybe<(RegisteredAttribute, AttributeSchema), registry::Absent>
    {
        let spelled: &str = name.as_ref();
        let found = REGISTRY.into_iter().find_map(|(entry, schema)| {
            (entry == spelled).then_some((RegisteredAttribute(entry), schema))
        });

        found.map_or(
            Maybe::Absent(registry::Absent::Unregistered),
            Maybe::Present,
        )
    }

    /// The registered name nearest `name`, when one sits within the bound.
    ///
    /// # Specification
    /// - requires: nothing — every identifier is admissible input, a registered
    ///   one included.
    /// - ensures: the registered name at the least edit distance from `name`,
    ///   when that distance is at most two edits; ties are broken by registry
    ///   order, so the answer does not depend on iteration accident.
    /// - provides: the repair an unknown-attribute refusal carries.
    /// - fails: never; when every registered name sits more than two edits away
    ///   the answer is the beyond-bound absence, because past that bound the
    ///   nearest entry says nothing about what the author meant.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two decision surfaces (the minimum selection and the
    ///   bound comparison) separated by one near miss per registry row, so an
    ///   answer fixed to any single row fails two of the three, and by a
    ///   spelling three edits from every row and the empty spelling, both
    ///   asserted absent.
    /// - witness: `attribute::tests::a_near_misspelling_suggests_its_attribute`
    /// - witness: `attribute::tests::a_distant_spelling_suggests_nothing`
    #[inline]
    pub fn suggestion(name: SurfaceName<'_>) -> Maybe<RegisteredAttribute, suggestion::Absent>
    {
        let mut best: Maybe<(EditDistance, RegisteredAttribute), suggestion::Absent> =
            Maybe::Absent(suggestion::Absent::BeyondBound);
        for (spelling, _schema) in REGISTRY {
            let candidate = RegisteredAttribute(spelling);
            let distance = edit_distance(name, candidate);
            if distance > SUGGESTION_BOUND {
                continue;
            }
            let improves = match best {
                | Maybe::Present((incumbent, _held)) => distance < incumbent,
                | Maybe::Absent(_) => true,
            };
            if improves {
                best = Maybe::Present((distance, candidate));
            }
        }

        best.map(|(_distance, candidate)| candidate)
    }
}

/// Whether `schema` admits a payload written as `form`.
///
/// # Specification
/// - requires: nothing; the function is total over both closed vocabularies.
/// - ensures: absence is admitted exactly by the bare marker, an integer
///   literal exactly by the integer schema, a text literal exactly by the text
///   schema; every other pair is refused, and the refusal is the missing one
///   exactly when nothing was written for a schema that takes something.
/// - provides: the one decision the payload half of the attribute pass makes,
///   separated from the diagnostics that report it.
/// - fails: never — a refusal is a verdict here, not an error.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the domain is the finite product of two closed
///   vocabularies, enumerated exhaustively against a pinned twelve-row table,
///   so a swapped or widened arm breaks one row.
/// - witness: `attribute::tests::the_payload_verdict_table_is_pinned`
#[inline]
#[must_use]
pub const fn payload_verdict(
    schema: AttributeSchema,
    form: PayloadForm,
) -> PayloadVerdict
{
    match (schema, form) {
        | (AttributeSchema::Marker, PayloadForm::Absent)
        | (AttributeSchema::Integer, PayloadForm::Integer)
        | (AttributeSchema::Text, PayloadForm::Text) => PayloadVerdict::Admitted,
        | (AttributeSchema::Integer | AttributeSchema::Text, PayloadForm::Absent) => {
            PayloadVerdict::Missing
        },
        | (
            AttributeSchema::Marker,
            PayloadForm::Integer | PayloadForm::Text | PayloadForm::OtherValue,
        )
        | (AttributeSchema::Integer, PayloadForm::Text | PayloadForm::OtherValue)
        | (AttributeSchema::Text, PayloadForm::Integer | PayloadForm::OtherValue) => {
            PayloadVerdict::IllTyped
        },
    }
}

/// The form a payload read as `former` was written in.
///
/// # Specification
/// - requires: `former` is the former of a payload that can stand as a value,
///   which the attribute pass establishes before asking.
/// - ensures: the two literal formers answer their own forms and every other
///   former answers the non-literal form; absence is not expressible here,
///   because a payload was written.
/// - provides: the syntactic half of the payload verdict.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the former vocabulary is a finite class, enumerated
///   exhaustively with each former's exact form asserted, so promoting any
///   former to a literal form breaks one row.
/// - witness: `attribute::tests::only_the_two_literal_kinds_are_literal_payloads`
#[inline]
#[must_use]
pub const fn payload_form(former: Former) -> PayloadForm
{
    match former {
        | Former::Number => PayloadForm::Integer,
        | Former::Text => PayloadForm::Text,
        | Former::Name
        | Former::Constructor
        | Former::Parenthesized
        | Former::Thunk
        | Former::Lambda
        | Former::Return
        | Former::Force
        | Former::Call
        | Former::Projection
        | Former::TypeHead
        | Former::Universe
        | Former::TypeApplication
        | Former::ThunkType
        | Former::ReturnerType
        | Former::ArrowType
        | Former::ProductType
        | Former::LazyProductType
        | Former::ValueFunctionType
        | Former::StaticAbstraction
        | Former::ParenthesizedType
        | Former::Declaration
        | Former::AttributeBlock
        | Former::Import
        | Former::Module
        | Former::Unadmitted => PayloadForm::OtherValue,
    }
}

/// The number of single-character edits between two spellings.
///
/// # Specification
/// - requires: nothing — either spelling may be empty.
/// - ensures: the Levenshtein distance over characters: the least number of
///   insertions, deletions and substitutions carrying one spelling to the
///   other, which is zero exactly when the two are equal.
/// - provides: the ordering the bounded suggestion selects its answer by.
/// - fails: never.
/// - panics: none. The row walk reads through checked lookups, and every
///   addition saturates.
///
/// # Adequacy
/// - hypothesis: L3 — four decision surfaces (the substitution cost and the
///   three-way minimum) separated by equal spellings, a single substitution, a
///   single insertion, a single deletion, a transposition costing two, and each
///   spelling against the empty one, every case asserted as an exact distance.
/// - witness: `attribute::tests::the_edit_distance_of_equal_spellings_is_zero`
/// - witness: `attribute::tests::each_single_edit_costs_one`
/// - witness: `attribute::tests::an_empty_spelling_costs_the_other_length`
#[must_use]
fn edit_distance(
    written: SurfaceName<'_>,
    candidate: RegisteredAttribute,
) -> EditDistance
{
    let left: &str = written.as_ref();
    let right: &str = candidate.as_ref();
    let width = right.chars().count();
    let mut previous: Vec<usize> = (0_usize ..= width).collect();
    let mut current: Vec<usize> = Vec::with_capacity(width.saturating_add(1_usize));
    for (row, from) in left.chars().enumerate() {
        current.clear();
        current.push(row.saturating_add(1_usize));
        for (column, into) in right.chars().enumerate() {
            let above = previous
                .get(column.saturating_add(1_usize))
                .copied()
                .unwrap_or(usize::MAX);
            let before = current.get(column).copied().unwrap_or(usize::MAX);
            let diagonal = previous.get(column).copied().unwrap_or(usize::MAX);
            let substitution = diagonal.saturating_add(usize::from(from != into));
            let best = above
                .saturating_add(1_usize)
                .min(before.saturating_add(1_usize))
                .min(substitution);
            current.push(best);
        }
        core::mem::swap(&mut previous, &mut current);
    }

    EditDistance(previous.last().copied().unwrap_or(width))
}

/// One attribute, resolved against the registry and filed under a declaration.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct AttributeEntry
{
    /// The registry name this attribute resolved to.
    name: RegisteredAttribute,
    /// The schema that name carries.
    schema: AttributeSchema,
    /// The payload's lowered core value, absent for a bare marker.
    payload: Maybe<ValueId, payload::Absent>,
    /// The bytes of the source the attribute covers.
    span: ByteSpan,
}

impl AttributeEntry
{
    /// The entry for `name` at `schema`, over `payload`, covering `span`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        name: RegisteredAttribute,
        schema: AttributeSchema,
        payload: Maybe<ValueId, payload::Absent>,
        span: ByteSpan,
    ) -> Self
    {
        Self {
            name,
            schema,
            payload,
            span,
        }
    }

    /// The registry name this attribute resolved to.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn name(&self) -> RegisteredAttribute
    {
        self.name
    }

    /// The schema that name carries.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn schema(&self) -> AttributeSchema
    {
        self.schema
    }

    /// The payload's lowered core value, absent for a bare marker.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn payload(&self) -> Maybe<ValueId, payload::Absent>
    {
        self.payload
    }

    /// The bytes of the source the attribute covers.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn span(&self) -> ByteSpan
    {
        self.span
    }
}

/// Every attributed declaration's entries, keyed by the declaration form's
/// content identity.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct AttributeTable
{
    /// Declaration content identity to that declaration's entries, in the
    /// order the source wrote them.
    entries: BTreeMap<NodeDigest, Vec<AttributeEntry>>,
}

impl AttributeTable
{
    /// A table holding no entries.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new() -> Self
    {
        Self {
            entries: BTreeMap::new(),
        }
    }

    /// File `entry` under the declaration whose content identity is `key`.
    ///
    /// # Specification
    /// - requires: `key` is the content digest of a declaration form of the
    ///   module being lowered.
    /// - ensures: the entry is appended to that declaration's list, after every
    ///   entry already filed under it, so one declaration's entries stay in the
    ///   order the source wrote them.
    /// - provides: the one way to grow the side table, so ordering is a
    ///   property of the table rather than of each caller.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two decision surfaces (the key lookup and the append)
    ///   separated by a first entry under a fresh key, a second entry under the
    ///   same key asserted to follow it, and an entry under a second key
    ///   asserted not to disturb the first.
    /// - witness: `attribute::tests::entries_keep_the_order_they_were_filed_in`
    /// - witness: `attribute::tests::two_declarations_keep_separate_entry_lists`
    #[inline]
    pub fn file(
        &mut self,
        key: NodeDigest,
        entry: AttributeEntry,
    )
    {
        self.entries.entry(key).or_default().push(entry);
    }

    /// The entries filed under `key`, in source order.
    ///
    /// # Specification
    /// - requires: nothing — a digest this table holds nothing for is
    ///   admissible input, which is the unattributed declaration's case.
    /// - ensures: exactly the entries filed under `key`, in the order they were
    ///   filed; the empty slice for a declaration carrying no attributes, so
    ///   absence and emptiness are one answer.
    /// - provides: the read face the corpus layer above reads expectations
    ///   through.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one lookup, separated by a filed key asserted as an
    ///   exact entry list and an unfiled key asserted empty.
    /// - witness: `attribute::tests::entries_keep_the_order_they_were_filed_in`
    /// - witness: `attribute::tests::an_unattributed_declaration_has_no_entries`
    #[inline]
    #[must_use]
    pub fn entries(
        &self,
        key: NodeDigest,
    ) -> &[AttributeEntry]
    {
        self.entries.get(&key).map_or(&[], Vec::as_slice)
    }

    /// How many declarations carry at least one entry.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn attributed_count(&self) -> AttributedCount
    {
        AttributedCount(self.entries.len())
    }
}

/// A number of declarations carrying attributes.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct AttributedCount(usize);

impl From<usize> for AttributedCount
{
    /// The count `count`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: usize) -> Self
    {
        Self(count)
    }
}

impl From<AttributedCount> for usize
{
    /// The number `count` holds.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: AttributedCount) -> Self
    {
        count.0
    }
}

#[cfg(test)]
mod tests
{
    use alloc::format;
    use alloc::string::String;
    use alloc::vec;

    use gandr_surface_syntax::ByteOffset;
    use gandr_surface_syntax::NodeDigest;
    use quenchant_shape::shape::Maybe;

    use super::AttributeEntry;
    use super::AttributeRegistry;
    use super::AttributeSchema;
    use super::AttributeTable;
    use super::AttributedCount;
    use super::EditDistance;
    use super::PayloadForm;
    use super::PayloadVerdict;
    use super::edit_distance;
    use super::payload;
    use super::payload_form;
    use super::payload_verdict;
    use super::registry;
    use super::suggestion;
    use crate::fixture::registered;
    use crate::fixture::span;
    use crate::form::Former;
    use crate::resolve::SurfaceName;

    #[test]
    fn every_registered_attribute_answers_its_schema()
    {
        let expected = [
            ("checks", AttributeSchema::Marker),
            ("owes", AttributeSchema::Integer),
            ("refuses", AttributeSchema::Text),
            ("runs", AttributeSchema::Text),
        ];

        for (spelling, schema) in expected {
            let found = AttributeRegistry::lookup(SurfaceName::from(spelling));
            assert_eq!(
                found.map(|(_name, held)| held),
                Maybe::Present(schema),
                "the registry is pinned row by row"
            );
            assert_eq!(
                found.map(|(held, _schema)| format!("{held}")),
                Maybe::Present(String::from(spelling)),
                "the entry names itself with the registry's own spelling"
            );
        }
        assert_eq!(
            AttributeRegistry::names().len(),
            expected.len(),
            "the pinned table covers the whole registry"
        );
    }

    #[test]
    fn an_unregistered_name_answers_nothing()
    {
        for spelling in ["check", "Checks", "owe", ""] {
            assert_eq!(
                AttributeRegistry::lookup(SurfaceName::from(spelling)),
                Maybe::Absent(registry::Absent::Unregistered),
                "the registry has no fallthrough"
            );
        }
    }

    #[test]
    fn a_near_misspelling_suggests_its_attribute()
    {
        // One row per registry entry: an answer fixed to any single entry
        // fails the others.
        let expected = [
            ("check", "checks"),
            ("owe", "owes"),
            ("refuse", "refuses"),
            ("run", "runs"),
        ];

        for (written, nearest) in expected {
            assert_eq!(
                AttributeRegistry::suggestion(SurfaceName::from(written)),
                Maybe::Present(registered(SurfaceName::from(nearest))),
                "a one-edit miss answers its own entry"
            );
        }
        assert_eq!(
            expected.len(),
            AttributeRegistry::names().len(),
            "every registry row is separated by a near miss of its own"
        );
    }

    #[test]
    fn a_distant_spelling_suggests_nothing()
    {
        assert_eq!(
            AttributeRegistry::suggestion(SurfaceName::from("expects")),
            Maybe::Absent(suggestion::Absent::BeyondBound),
            "three edits from every entry is past the bound"
        );
        assert_eq!(
            AttributeRegistry::suggestion(SurfaceName::from("")),
            Maybe::Absent(suggestion::Absent::BeyondBound),
            "the empty spelling sits at each entry's own length"
        );
    }

    #[test]
    fn the_edit_distance_of_equal_spellings_is_zero()
    {
        assert_eq!(
            edit_distance(
                SurfaceName::from("checks"),
                registered(SurfaceName::from("checks"))
            ),
            EditDistance::from(0_usize),
            "no edit carries a spelling to itself"
        );
    }

    #[test]
    fn each_single_edit_costs_one()
    {
        let checks = registered(SurfaceName::from("checks"));
        assert_eq!(
            edit_distance(SurfaceName::from("checkz"), checks),
            EditDistance::from(1_usize),
            "one substitution costs one"
        );
        assert_eq!(
            edit_distance(SurfaceName::from("check"), checks),
            EditDistance::from(1_usize),
            "one insertion costs one"
        );
        assert_eq!(
            edit_distance(SurfaceName::from("checkss"), checks),
            EditDistance::from(1_usize),
            "one deletion costs one"
        );
        assert_eq!(
            edit_distance(SurfaceName::from("cheskc"), checks),
            EditDistance::from(2_usize),
            "a transposition costs two substitutions"
        );
    }

    #[test]
    fn an_empty_spelling_costs_the_other_length()
    {
        assert_eq!(
            edit_distance(SurfaceName::from(""), registered(SurfaceName::from("owes"))),
            EditDistance::from(4_usize),
            "the empty spelling costs one insertion per character"
        );
    }

    #[test]
    fn the_payload_verdict_table_is_pinned()
    {
        let expected = [
            (
                AttributeSchema::Marker,
                PayloadForm::Absent,
                PayloadVerdict::Admitted,
            ),
            (
                AttributeSchema::Marker,
                PayloadForm::Integer,
                PayloadVerdict::IllTyped,
            ),
            (
                AttributeSchema::Marker,
                PayloadForm::Text,
                PayloadVerdict::IllTyped,
            ),
            (
                AttributeSchema::Marker,
                PayloadForm::OtherValue,
                PayloadVerdict::IllTyped,
            ),
            (
                AttributeSchema::Integer,
                PayloadForm::Absent,
                PayloadVerdict::Missing,
            ),
            (
                AttributeSchema::Integer,
                PayloadForm::Integer,
                PayloadVerdict::Admitted,
            ),
            (
                AttributeSchema::Integer,
                PayloadForm::Text,
                PayloadVerdict::IllTyped,
            ),
            (
                AttributeSchema::Integer,
                PayloadForm::OtherValue,
                PayloadVerdict::IllTyped,
            ),
            (
                AttributeSchema::Text,
                PayloadForm::Absent,
                PayloadVerdict::Missing,
            ),
            (
                AttributeSchema::Text,
                PayloadForm::Integer,
                PayloadVerdict::IllTyped,
            ),
            (
                AttributeSchema::Text,
                PayloadForm::Text,
                PayloadVerdict::Admitted,
            ),
            (
                AttributeSchema::Text,
                PayloadForm::OtherValue,
                PayloadVerdict::IllTyped,
            ),
        ];

        for (schema, form, verdict) in expected {
            assert_eq!(
                payload_verdict(schema, form),
                verdict,
                "the payload verdict table is pinned row by row"
            );
        }
        assert_eq!(
            expected.len(),
            12_usize,
            "the pinned table covers the whole product of the two vocabularies"
        );
    }

    #[test]
    fn only_the_two_literal_kinds_are_literal_payloads()
    {
        for former in Former::ALL {
            let expected = match former {
                | Former::Number => PayloadForm::Integer,
                | Former::Text => PayloadForm::Text,
                | Former::Name
                | Former::Constructor
                | Former::Parenthesized
                | Former::Thunk
                | Former::Lambda
                | Former::Return
                | Former::Force
                | Former::Call
                | Former::Projection
                | Former::TypeHead
                | Former::Universe
                | Former::TypeApplication
                | Former::ThunkType
                | Former::ReturnerType
                | Former::ArrowType
                | Former::ProductType
                | Former::LazyProductType
                | Former::ValueFunctionType
                | Former::StaticAbstraction
                | Former::ParenthesizedType
                | Former::Declaration
                | Former::AttributeBlock
                | Former::Import
                | Former::Module
                | Former::Unadmitted => PayloadForm::OtherValue,
            };
            assert_eq!(
                payload_form(former),
                expected,
                "exactly the two literal formers carry a literal payload form"
            );
        }
    }

    #[test]
    fn every_schema_and_payload_form_renders_its_own_name()
    {
        let schemas = [
            (AttributeSchema::Marker, "no payload"),
            (AttributeSchema::Integer, "an integer payload"),
            (AttributeSchema::Text, "a text payload"),
        ];
        for (schema, rendering) in schemas {
            assert_eq!(
                format!("{schema}"),
                String::from(rendering),
                "each schema names what it takes"
            );
        }
        let forms = [
            (PayloadForm::Absent, "no payload"),
            (PayloadForm::Integer, "an integer payload"),
            (PayloadForm::Text, "a text payload"),
            (PayloadForm::OtherValue, "a non-literal payload"),
        ];
        for (form, rendering) in forms {
            assert_eq!(
                format!("{form}"),
                String::from(rendering),
                "each payload form names what was written"
            );
        }
    }

    #[test]
    fn entries_keep_the_order_they_were_filed_in()
    {
        let mut table = AttributeTable::new();
        let key = NodeDigest::from([1_u8; 32_usize]);
        let first = AttributeEntry::new(
            registered(SurfaceName::from("checks")),
            AttributeSchema::Marker,
            Maybe::Absent(payload::Absent::Marker),
            span(ByteOffset::from(0_usize), ByteOffset::from(6_usize)),
        );
        let second = AttributeEntry::new(
            registered(SurfaceName::from("owes")),
            AttributeSchema::Integer,
            Maybe::Absent(payload::Absent::Marker),
            span(ByteOffset::from(8_usize), ByteOffset::from(15_usize)),
        );
        table.file(key, first);
        table.file(key, second);

        assert_eq!(
            table.entries(key),
            vec![first, second].as_slice(),
            "entries stay in the order the source wrote them"
        );
        assert_eq!(
            table.attributed_count(),
            AttributedCount::from(1_usize),
            "two entries under one key are one attributed declaration"
        );
    }

    #[test]
    fn two_declarations_keep_separate_entry_lists()
    {
        let mut table = AttributeTable::new();
        let first_key = NodeDigest::from([1_u8; 32_usize]);
        let second_key = NodeDigest::from([2_u8; 32_usize]);
        let first = AttributeEntry::new(
            registered(SurfaceName::from("checks")),
            AttributeSchema::Marker,
            Maybe::Absent(payload::Absent::Marker),
            span(ByteOffset::from(0_usize), ByteOffset::from(6_usize)),
        );
        let second = AttributeEntry::new(
            registered(SurfaceName::from("refuses")),
            AttributeSchema::Text,
            Maybe::Absent(payload::Absent::Marker),
            span(ByteOffset::from(8_usize), ByteOffset::from(20_usize)),
        );
        table.file(first_key, first);
        table.file(second_key, second);

        assert_eq!(
            table.entries(first_key),
            vec![first].as_slice(),
            "one declaration's list is untouched by another's"
        );
        assert_eq!(
            table.entries(second_key),
            vec![second].as_slice(),
            "the second declaration holds only its own entry"
        );
        assert_eq!(
            table.attributed_count(),
            AttributedCount::from(2_usize),
            "two keys are two attributed declarations"
        );
    }

    #[test]
    fn an_unattributed_declaration_has_no_entries()
    {
        let table = AttributeTable::new();

        assert!(
            table.entries(NodeDigest::from([9_u8; 32_usize])).is_empty(),
            "a digest the table holds nothing for reads as the empty list"
        );
    }
}
