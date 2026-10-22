//! The entity-attribute layer: the closed [`AttributeRegistry`], the payload
//! [`PayloadVerdict`] each schema returns, and the [`AttributeTable`] a lowered
//! module carries beside its declarations.
//!
//! # The side table is keyed by content identity
//!
//! An entry is filed under the [`UnitKey`] of the declaration form the
//! attribute decorates — the source holding the form, the digest of the
//! top-level form holding it and its rank there — never under that
//! declaration's position in a list. A position is invalidated by an edit
//! anywhere earlier in the file; a key is invalidated only by an edit inside
//! the top-level form holding the declaration. The molded tree makes a leading
//! attribute block part of the declaration form it precedes, so the key reads
//! the declaration's own attributes: editing an attribute re-keys that form's
//! entries, and an edit to another form leaves the key alone. Two
//! byte-identical forms in two sources of one unit are filed apart by their
//! sources (#596).
//!
//! # Every schema but `respects` and `entry` is inert
//!
//! The lowered term is neither read nor written by the attribute pass: a
//! payload lowers to its own core value, filed here, and nothing about the
//! decorated declaration's core term depends on it. `respects` and `entry`
//! are the semantic attributes: a `respects` payload names the laws a fold
//! rests on, and an `entry` payload the worlds a declaration is judged at and
//! migrates to, which the table keeps beside the entry as constants and the
//! checker's declaration carries. The term is still untouched; what changes
//! is the evidence the declaration is admitted on, or the world it is judged
//! at.
//!
//! # An unknown name gets a bounded suggestion
//!
//! The registry is closed and small, so a misspelling is answered with the one
//! nearest registered name within a fixed edit distance. The bound is what
//! keeps the suggestion an aid rather than a guess: past it the nearest entry
//! carries no information about what the author meant.
//!
//! # Attributes and documentation
//!
//! An attribute is resolved against a closed registry, with five diagnostics,
//! and filed in a side table under the content identity of the declaration it
//! decorates, whatever that declaration's outcome; at the top level an
//! attribute block is a form of its own, so that identity excludes the
//! attributes. A declaration's documentation, its `///` runs and `doc("…")`
//! entries, is read into one text under the same identity, its links resolved
//! as names.
//!
//! # Attributes: a closed registry and a side table
//!
//! The registry is closed: `checks` and `explicit_exits` take no payload,
//! `explicit_runs` none or a text naming its one option, `effects`, `owes` an
//! integer, `refuses`, `runs`, `normalizes` and `doc` a text, `respects` and
//! `entry` one declared name or a tuple of them, and `form` one bare word,
//! `explicit` or `sugared`. The attribute block
//! admits one payload per attribute and refuses an attribute written twice,
//! so several laws are one tuple, `respects((a, b))`, in the order of the
//! rules they answer, and an entry's worlds one tuple, `entry((home, w, …))`,
//! its home first and then the world of each capability. Five diagnostics
//! cover what an attribute can get wrong, checked in this order: an unknown
//! name, with the registered name within edit distance two when one exists;
//! the same attribute written twice for one declared name, naming the first;
//! a payload that is not a value at all, decided before the schema is
//! consulted because being no value is a different fact from being the wrong
//! one; a missing payload; and a payload of a form the schema does not admit,
//! a payload on a marker included. A payload is read as a value under no
//! binder, and the schema types it at the literal: an integer or a text. A
//! well-formed `doc` entry never reaches the registry, because the parser
//! reads it as documentation (the `doc` module); `doc` is registered so that a
//! malformed one meets the payload diagnostics. `explicit_exits` is read by
//! the lowering, which marks every exit it inferred under the declaration or
//! module the attribute decorates as asked for; `explicit_runs` likewise marks
//! every computation it held nested there, asked for every run or, under
//! `effects`, for the effectful ones; a module takes attributes as a
//! declaration does, and the lowering files them under the module's key.
//!
//! A word payload is read as written and never lowered: `form(explicit)`
//! names the spelling the source is written in (`gandr-surface-format`), not a
//! declaration, so `explicit` is not looked up in scope and the entry is filed
//! with no value. A word the schema does not name is refused as an ill-typed
//! payload naming the words it takes. The alternative was a text payload,
//! `form("explicit")`, which the text schema already reads; the bare word was
//! kept because the payload is a closed choice, not a string, and the
//! formatter reads it off the tree before anything lowers. Reversal: a second
//! closed-choice attribute whose words collide with declared names would read
//! better as a text.
//!
//! Executable predicates preserve the registry inventory, exact lookup, the
//! payload decision table, distance bounds and the borrowed identity of a filed
//! entry list. Suggestions count Unicode scalar edits, include distance two and
//! break equal-distance ties by registry order; boundary witnesses distinguish
//! these choices without re-running an allocating distance algorithm in the
//! suggestion predicate. Filing appends to one declaration key without
//! replacing its earlier entries. An attribute record retains producer-supplied
//! metadata; it does not itself authenticate a source span or validate a
//! payload in an unheld value arena.
//!
//! An admitted attribute is filed under the content identity of the declaration
//! form it decorates. At the top level every attribute block is a form of its
//! own standing before that declaration, a decision of `gandr-surface-grammar`,
//! and the collector carries the blocks it meets to the next declaration, a
//! definition or a data declaration alike, so the identity excludes the
//! attributes: adding, editing or removing one re-keys nothing. A block before
//! no declaration — at the end of the module, or before an import or a module —
//! refuses the module. A module member keeps its blocks inside its form, and
//! its identity covers them.
//!
//! The alternative was folding a definition's blocks into its form, which keys
//! the definition by its attributes and, with the standalone block a data
//! declaration takes, ties the two readings of every `@[` until the token after
//! `]`. Two top-level declarations written alike share an identity and so one
//! entry list; both declare one name, so the second is refused as a duplicate.
//! Reversal: when two declarations written alike must keep separate entries,
//! the key gains the declaration's position.
//!
//! An attribute is filed whatever its declaration's outcome: a refused
//! declaration still has its tree and its key, and an expectation about a
//! refusal — `refuses` — can only be read off the declaration that refused. Its
//! payload is minted for the same reason, the one part of a refused declaration
//! that lowers. A declaration form whose own tiles fault records no half, and
//! its attributes are not filed.
//!
//! The alternative was to file attributes for unrefused declarations only. It
//! was declined because it leaves every lowering refusal unexpectable: a
//! fixture stating the refusal it expects would be read as stating nothing.
//! Reversal: none while an attribute can state an expectation about its
//! declaration's refusal.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_kernel_term::ConstantIndex;
use gandr_surface_syntax::ByteSpan;
use quenchant_shape::shape::Maybe;

use crate::form::Former;
use crate::resolve::SurfaceName;
use crate::unit::UnitKey;

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
            /// The payload is a word its schema reads as written, never as a
            /// value: [`super::AttributeSchema::Word`].
            Word,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a `respects` or `entry` payload names no declarations.
    pub mod names {
        /// The payload is a value of another form.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// Neither a declared name nor a tuple of declared names.
            Unnamed,
        }
    }
}

/// The declarations a `respects` or `entry` payload names, in the order it
/// names them.
///
/// A declared name lowers to its constant and a tuple to its components, so a
/// payload names declarations exactly when it is one constant or a tuple of
/// them. The unit is the empty tuple, and a fold resting on no law is no
/// fold, as an entry at no world is no entry: it names none.
///
/// # Specification
/// - requires: `payload` is the lowered value of a payload the
///   [`AttributeSchema::Names`] schema admitted.
/// - ensures: the one constant `payload` is, or the constants of its components
///   in written order when it is a non-empty tuple of constants;
///   [`names::Absent::Unnamed`] for any other value, the unit included.
/// - fails: never — an unnamed payload is an absence, not an error.
/// - panics: none.
///
/// # Termination
/// - reason: one pass over the tuple's finite components, not recursion.
/// - measure: the components left.
///
/// # Adequacy
/// - hypothesis: L3 — a single name, a tuple of names, a tuple holding a unit,
///   and the unit separate the answers.
/// - witness: `attribute::tests::a_respects_payload_names_its_laws_in_written_order`
#[spec(ensures: |ref ret| match (ret, arena.value(payload)) {
    | (&Maybe::Present(ref named), Some(&Value::Constant(name))) => named.as_slice() == [name],
    | (&Maybe::Present(ref named), Some(&Value::Tuple(ref items))) => !items.is_empty() && named.len() == items.len(),
    | (&Maybe::Present(_), _) => false,
    | (&Maybe::Absent(_), _) => true,
})]
#[inline]
pub fn names(
    arena: &CoreArena,
    payload: ValueId,
) -> Maybe<Vec<ConstantIndex>, names::Absent>
{
    let unnamed = Maybe::Absent(names::Absent::Unnamed);
    match arena.value(payload) {
        Some(&Value::Constant(name)) => Maybe::Present(Vec::from([name])),
        Some(&Value::Tuple(ref items)) if !items.is_empty() => {
            let mut named = Vec::with_capacity(items.len());
            for &item in items {
                let Some(&Value::Constant(name)) = arena.value(item)
                else {
                    return unnamed;
                };
                named.push(name);
            }
            Maybe::Present(named)
        },
        _ => unnamed,
    }
}

/// The furthest an unknown attribute name may sit from a registered one and
/// still be answered with it.
///
/// # Specification
/// - requires: nothing.
/// - ensures: candidate distances at most two are eligible; larger distances
///   are not.
/// - provides: the inclusive suggestion threshold.
/// - executable: none — the specification attribute does not support constant
///   items; selection and boundary witnesses exercise this policy.
///
/// # Adequacy
/// - hypothesis: L3 — distances two and three separate eligibility, and an
///   equal-distance pair exercises the registry-order tie.
/// - witness: `attribute::tests::suggestions_include_the_bound_and_break_ties_by_registry_order`
const SUGGESTION_BOUND: EditDistance = EditDistance(2_usize);

/// One name the attribute registry holds.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RegisteredAttribute(&'static str);

impl RegisteredAttribute
{
    /// `doc`: its text documents the declaration it decorates, joined after
    /// any `///` lines; it is filed as the declaration's documentation, never
    /// in the attribute table.
    pub const DOC: Self = Self("doc");
    /// `explicit_exits`: the declaration, or every member of the module, it
    /// decorates asks for every exit to be written, so the `explicit-exits`
    /// lint reports each exit the lowering inferred there.
    pub const EXPLICIT_EXITS: Self = Self("explicit_exits");
    /// `explicit_runs`: the declaration, or every member of the module, it
    /// decorates asks for every run the checker infers there to be written,
    /// or, with the text `"effects"`, every run that performs an effect, so
    /// the `explicit-runs` lint reports each.
    pub const EXPLICIT_RUNS: Self = Self("explicit_runs");
    /// The one option `explicit_runs` takes: only the runs that perform an
    /// effect are asked for.
    pub const EFFECTS: &'static str = "effects";
    /// `respects`: the recursive definition it decorates is a fold, and the
    /// laws it names, one per rule of the presented type the fold's `case`
    /// is over and in the rules' written order, are the evidence for each
    /// rule the fold does not respect by conversion alone.
    pub const RESPECTS: Self = Self("respects");
    /// `entry`: the declaration it decorates is judged at the world its first
    /// name declares, holding one capability to migrate to the world each
    /// later name declares.
    pub const ENTRY: Self = Self("entry");
    /// `form`: the spelling the source it heads is written in, `explicit` —
    /// the core's own, every thunk, force, run and exit written out — or
    /// `sugared`; the formatter lays the source out in it.
    pub const FORM: Self = Self("form");
    /// The words `form` takes.
    pub const FORMS: &'static [&'static str] = &["explicit", "sugared"];
}

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
    /// A bare marker, or the one text literal spelling the option named.
    MarkerOr(&'static str),
    /// One declared name, or a tuple of declared names.
    Names,
    /// One bare word among those named, read as written and never lowered as
    /// a value.
    Word(&'static [&'static str]),
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
            Self::Marker => f.write_str("no payload"),
            Self::Integer => f.write_str("an integer payload"),
            Self::Text => f.write_str("a text payload"),
            Self::MarkerOr(option) => write!(f, "no payload or the text \"{option}\""),
            Self::Names => f.write_str("a declared name or a tuple of declared names"),
            Self::Word(words) => {
                f.write_str("one of the words")?;
                for (index, word) in words.iter().enumerate() {
                    let joint = if index == 0 { " " } else { ", " };
                    write!(f, "{joint}`{word}`")?;
                }
                Ok(())
            },
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
    /// A text literal spelling no option its schema names: what a text is
    /// read as where a [`AttributeSchema::MarkerOr`] schema stands.
    OtherText,
    /// A bare word: one name, standing alone.
    Word,
    /// A bare word spelling none its schema names: what a word is read as
    /// where a [`AttributeSchema::Word`] schema stands.
    OtherWord,
    /// A value of the fragment that is none of the forms above.
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
            Self::Absent => f.write_str("no payload"),
            Self::Integer => f.write_str("an integer payload"),
            Self::Text => f.write_str("a text payload"),
            Self::OtherText => f.write_str("another text"),
            Self::Word => f.write_str("a bare word"),
            Self::OtherWord => f.write_str("another word"),
            Self::OtherValue => f.write_str("a non-literal payload"),
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
///
/// # Specification
/// - requires: nothing.
/// - ensures: lookup has no fallback for an unregistered name; suggestion is
///   bounded and names retain registry order.
/// - provides: the closed attribute vocabulary and its schema mapping.
/// - executable: none — the unit facade holds no instance state; the associated
///   function predicates check each observable boundary.
///
/// # Adequacy
/// - hypothesis: L3 — every named schema, case-sensitive misses, near misses,
///   the inclusive bound and a tied minimum are observed.
/// - witness: `attribute::tests::every_registered_attribute_answers_its_schema`
/// - witness: `attribute::tests::an_unregistered_name_answers_nothing`
/// - witness: `attribute::tests::suggestions_include_the_bound_and_break_ties_by_registry_order`
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct AttributeRegistry;

/// Every registered attribute, with its schema.
///
/// # Specification
/// - requires: nothing.
/// - ensures: names are distinct and each row supplies its declared schema; row
///   order decides tied suggestions.
/// - provides: the finite schema inventory used by resolution.
/// - executable: none — the specification attribute does not support constant
///   items; lookup and names predicates preserve the rows at runtime.
///
/// # Adequacy
/// - hypothesis: L3 — the finite inventory is checked row by row, and tied
///   suggestions select the earlier eligible row.
/// - witness: `attribute::tests::every_registered_attribute_answers_its_schema`
/// - witness: `attribute::tests::suggestions_include_the_bound_and_break_ties_by_registry_order`
const REGISTRY: [(&str, AttributeSchema); 11_usize] = [
    ("checks", AttributeSchema::Marker),
    ("owes", AttributeSchema::Integer),
    ("refuses", AttributeSchema::Text),
    ("runs", AttributeSchema::Text),
    ("normalizes", AttributeSchema::Text),
    (RegisteredAttribute::DOC.0, AttributeSchema::Text),
    (
        RegisteredAttribute::EXPLICIT_EXITS.0,
        AttributeSchema::Marker,
    ),
    (
        RegisteredAttribute::EXPLICIT_RUNS.0,
        AttributeSchema::MarkerOr(RegisteredAttribute::EFFECTS),
    ),
    (RegisteredAttribute::RESPECTS.0, AttributeSchema::Names),
    (RegisteredAttribute::ENTRY.0, AttributeSchema::Names),
    (
        RegisteredAttribute::FORM.0,
        AttributeSchema::Word(RegisteredAttribute::FORMS),
    ),
];

impl AttributeRegistry
{
    /// Every registered name, in registry order.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: every registry spelling appears once in registry order.
    /// - provides: the closed name inventory, without schema payloads.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the finite inventory has a lookup result and distinct
    ///   near miss for every named schema.
    /// - witness: `attribute::tests::every_registered_attribute_answers_its_schema`
    /// - witness: `attribute::tests::a_near_misspelling_suggests_its_attribute`
    #[spec(
        ensures: |ret| {
            ret.len() == REGISTRY.len()
                && ret
                    .iter()
                    .zip(REGISTRY)
                    .all(|(name, (spelling, _))| name.0 == spelling)
        },
    )]
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
    #[spec(
        ensures: |ret| match ret {
            | Maybe::Present((registered, schema)) => {
                registered.0 == name.as_ref()
                    && REGISTRY
                        .iter()
                        .any(|&(spelled, expected)| spelled == registered.0 && expected == schema)
            },
            | Maybe::Absent(registry::Absent::Unregistered) => REGISTRY
                .iter()
                .all(|&(spelled, _)| spelled != name.as_ref()),
        },
    )]
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
    /// - hypothesis: L3 — one near miss per registry row, exact registered
    ///   spellings, distances two and three, a two-way tie, and a later entry
    ///   one edit away after an earlier one two away separate minimum
    ///   selection, inclusion of the bound and registry-order ties. The
    ///   predicate checks membership, the length lower bound and exact matches
    ///   without re-running the allocating distance calculation.
    /// - witness: `attribute::tests::a_near_misspelling_suggests_its_attribute`
    /// - witness: `attribute::tests::a_distant_spelling_suggests_nothing`
    /// - witness: `attribute::tests::suggestions_include_the_bound_and_break_ties_by_registry_order`
    #[spec(
        ensures: |ret| {
            let spelled: &str = name.as_ref();
            match ret {
                | Maybe::Present(registered) => {
                    REGISTRY.iter().any(|&(entry, _)| entry == registered.0)
                        && spelled
                            .chars()
                            .count()
                            .abs_diff(registered.0.chars().count())
                            <= SUGGESTION_BOUND.0
                        && REGISTRY
                            .iter()
                            .all(|&(entry, _)| entry != spelled || registered.0 == spelled)
                },
                | Maybe::Absent(suggestion::Absent::BeyondBound) => {
                    REGISTRY.iter().all(|&(entry, _)| entry != spelled)
                },
            }
        },
    )]
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
                Maybe::Present((incumbent, _held)) => distance < incumbent,
                Maybe::Absent(_) => true,
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
/// - ensures: absence is admitted exactly by the bare marker and the
///   marker-or-option schema; an integer literal exactly by the integer schema;
///   a text literal by the text schema and, read as the option it spells, by
///   the marker-or-option schema; a text spelling no option by the text schema
///   alone; a bare word by the names schema, as the one name it declares, and
///   by the word schema, read as one of its words; a word spelling none by no
///   schema; any other value exactly by the names schema; every other pair is
///   refused, and the refusal is the missing one exactly when nothing was
///   written for a schema that takes something.
/// - provides: the one decision the payload half of the attribute pass makes,
///   separated from the diagnostics that report it.
/// - fails: never — a refusal is a verdict here, not an error.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the domain is the finite product of two closed
///   vocabularies, enumerated exhaustively against a pinned table, so a swapped
///   or widened arm breaks one row.
/// - witness: `attribute::tests::the_payload_verdict_table_is_pinned`
#[spec(
    ensures: |ret| {
        let admitted = matches!(
            (schema, form),
            (AttributeSchema::Marker | AttributeSchema::MarkerOr(_), PayloadForm::Absent)
                | (AttributeSchema::Integer, PayloadForm::Integer)
                | (AttributeSchema::Text, PayloadForm::Text | PayloadForm::OtherText)
                | (AttributeSchema::MarkerOr(_), PayloadForm::Text)
                | (AttributeSchema::Names, PayloadForm::Word | PayloadForm::OtherValue)
                | (AttributeSchema::Word(_), PayloadForm::Word)
        );
        let missing = matches!(form, PayloadForm::Absent)
            && matches!(
                schema,
                AttributeSchema::Integer
                    | AttributeSchema::Text
                    | AttributeSchema::Names
                    | AttributeSchema::Word(_)
            );
        matches!(ret, PayloadVerdict::Admitted) == admitted
            && matches!(ret, PayloadVerdict::Missing) == missing
            && matches!(ret, PayloadVerdict::IllTyped) == (!admitted && !missing)
    },
)]
#[inline]
#[must_use]
pub const fn payload_verdict(
    schema: AttributeSchema,
    form: PayloadForm,
) -> PayloadVerdict
{
    match (schema, form) {
        (AttributeSchema::Marker | AttributeSchema::MarkerOr(_), PayloadForm::Absent)
        | (AttributeSchema::Integer, PayloadForm::Integer)
        | (AttributeSchema::Text, PayloadForm::Text | PayloadForm::OtherText)
        | (AttributeSchema::MarkerOr(_), PayloadForm::Text)
        | (AttributeSchema::Names, PayloadForm::Word | PayloadForm::OtherValue)
        | (AttributeSchema::Word(_), PayloadForm::Word) => PayloadVerdict::Admitted,
        (
            AttributeSchema::Integer
            | AttributeSchema::Text
            | AttributeSchema::Names
            | AttributeSchema::Word(_),
            PayloadForm::Absent,
        ) => PayloadVerdict::Missing,
        (
            AttributeSchema::Marker,
            PayloadForm::Integer
            | PayloadForm::Text
            | PayloadForm::OtherText
            | PayloadForm::Word
            | PayloadForm::OtherWord
            | PayloadForm::OtherValue,
        )
        | (
            AttributeSchema::Integer,
            PayloadForm::Text
            | PayloadForm::OtherText
            | PayloadForm::Word
            | PayloadForm::OtherWord
            | PayloadForm::OtherValue,
        )
        | (
            AttributeSchema::Text,
            PayloadForm::Integer
            | PayloadForm::Word
            | PayloadForm::OtherWord
            | PayloadForm::OtherValue,
        )
        | (
            AttributeSchema::MarkerOr(_),
            PayloadForm::Integer
            | PayloadForm::OtherText
            | PayloadForm::Word
            | PayloadForm::OtherWord
            | PayloadForm::OtherValue,
        )
        | (
            AttributeSchema::Names,
            PayloadForm::Integer
            | PayloadForm::Text
            | PayloadForm::OtherText
            | PayloadForm::OtherWord,
        )
        | (
            AttributeSchema::Word(_),
            PayloadForm::Integer
            | PayloadForm::Text
            | PayloadForm::OtherText
            | PayloadForm::OtherWord
            | PayloadForm::OtherValue,
        ) => PayloadVerdict::IllTyped,
    }
}

/// The form a payload read as `former` was written in.
///
/// # Specification
/// - requires: nothing — classification is total over `Former`; the caller
///   separately decides whether the form can stand as a value.
/// - ensures: the two literal formers answer their own forms, a bare name the
///   word form, and every other former the non-literal form; absence is not
///   expressible here, because a payload was written.
/// - provides: the syntactic half of the payload verdict.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — source attributes reject a payload of the wrong literal
///   form, and a word schema admits a bare word and refuses a text.
/// - witness: `lower::tests::a_payload_of_the_wrong_form_is_refused`
/// - witness: `lower::tests::a_form_payload_is_read_as_one_of_its_words`
#[spec(
    ensures: |ret| {
        matches!(ret, PayloadForm::Integer) == matches!(former, Former::Number)
            && matches!(ret, PayloadForm::Text) == matches!(former, Former::Text)
            && matches!(ret, PayloadForm::Word) == matches!(former, Former::Name)
            && matches!(ret, PayloadForm::OtherValue)
                != matches!(former, Former::Number | Former::Text | Former::Name)
            && !matches!(ret, PayloadForm::Absent | PayloadForm::OtherText | PayloadForm::OtherWord)
    },
)]
#[inline]
#[must_use]
pub const fn payload_form(former: Former) -> PayloadForm
{
    match former {
        Former::Number => PayloadForm::Integer,
        Former::Text => PayloadForm::Text,
        Former::Name => PayloadForm::Word,
        Former::Hole
        | Former::Binary
        | Former::Unary
        | Former::Constructor
        | Former::Parenthesized
        | Former::TypeQuote
        | Former::Unit
        | Former::Thunk
        | Former::Lambda
        | Former::Return
        | Former::Exit
        | Former::Become
        | Former::Loop
        | Former::While
        | Former::For
        | Former::Break
        | Former::Continue
        | Former::Block
        | Former::Force
        | Former::Run
        | Former::Call
        | Former::Case
        | Former::Telescope
        | Former::List
        | Former::PackModel
        | Former::Injection
        | Former::LazyRecord
        | Former::Instantiation
        | Former::Projection
        | Former::TypeHead
        | Former::TypePath
        | Former::Universe
        | Former::TypeApplication
        | Former::ThunkType
        | Former::ReturnerType
        | Former::ArrowType
        | Former::ProductType
        | Former::SumType
        | Former::LazyProductType
        | Former::TelescopeType
        | Former::LabelledSumType
        | Former::LazyRecordType
        | Former::ValueFunctionType
        | Former::StaticAbstraction
        | Former::ParenthesizedType
        | Former::PathType
        | Former::RelationType
        | Former::ManifestType
        | Former::CapabilityType
        | Former::AtType
        | Former::StagedType
        | Former::ModedType
        | Former::Scope
        | Former::Declaration
        | Former::AttributeBlock
        | Former::Import
        | Former::Module
        | Former::Data
        | Former::Mutual
        | Former::SessionType
        | Former::Action
        | Former::Offer
        | Former::Access
        | Former::World
        | Former::WorldDeclaration
        | Former::Reserved
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
/// - witness: `attribute::tests::edit_distance_counts_unicode_scalars_not_bytes`
#[spec(
    ensures: |ret| {
        let left: &str = written.as_ref();
        let right = candidate.0;
        let left_len = left.chars().count();
        let right_len = right.chars().count();
        ret.0 >= left_len.abs_diff(right_len)
            && ret.0 <= left_len.max(right_len)
            && (ret.0 == 0) == (left == right)
            && (!left.is_empty() || ret.0 == right_len)
            && (!right.is_empty() || ret.0 == left_len)
    },
)]
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
///
/// # Specification
/// - requires: the producer establishes registry, payload and source-span
///   correspondence before filing.
/// - ensures: construction retains the supplied record unchanged; the record
///   itself does not validate schema admission or authenticate an arena value.
/// - provides: a resolved attribute record beside its declaration.
/// - executable: none — the record holds neither its source form nor the value
///   arena needed to check producer correspondence; construction is a field
///   initializer.
///
/// # Adequacy
/// - hypothesis: L3 — exact distinct records retain their filing order and stay
///   separated by declaration keys; these are storage witnesses, not proof of
///   arbitrary payload admission.
/// - witness: `attribute::tests::entries_keep_the_order_they_were_filed_in`
/// - witness: `attribute::tests::two_declarations_keep_separate_entry_lists`
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
/// cross-tree key, and the laws a `respects` entry and the worlds an `entry`
/// entry names under the same key.
///
/// # Specification
/// - requires: producers file entries under the intended declaration's key.
/// - ensures: every stored key has a nonempty ordered entry list; no lookup
///   synthesizes an attribute and a repeated key appends rather than replaces.
/// - provides: attribute metadata separated from core terms.
/// - executable: none — this build's specification facade does not expose the
///   type-item runtime; filing and lookup predicates check the observable
///   boundaries.
///
/// # Adequacy
/// - hypothesis: L3 — fresh and repeated keys, a second independent key and an
///   absent key separate append, key isolation and absence.
/// - witness: `attribute::tests::entries_keep_the_order_they_were_filed_in`
/// - witness: `attribute::tests::two_declarations_keep_separate_entry_lists`
/// - witness: `attribute::tests::an_unattributed_declaration_has_no_entries`
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct AttributeTable
{
    /// Declaration key to that declaration's entries, in the order the source
    /// wrote them.
    entries: BTreeMap<UnitKey, Vec<AttributeEntry>>,
    /// Declaration key to the laws its `respects` entry names, in the order
    /// the payload names them.
    laws: BTreeMap<UnitKey, Vec<ConstantIndex>>,
    /// Declaration key to the worlds its `entry` entry names, its home first,
    /// in the order the payload names them.
    worlds: BTreeMap<UnitKey, Vec<ConstantIndex>>,
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
            laws: BTreeMap::new(),
            worlds: BTreeMap::new(),
        }
    }

    /// File `entry` under the declaration whose key is `key`.
    ///
    /// # Specification
    /// - requires: `key` is the key of a declaration form of the module being
    ///   lowered.
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
    #[spec(
        captures: before = (
            self.entries.len(),
            self.entries.get(&key).map_or(0, Vec::len),
            self.entries.contains_key(&key),
            entry,
        ),
        ensures: self.entries.len() == before.0.saturating_add(usize::from(!before.2))
            && self.entries.get(&key).is_some_and(|items| {
                items.len() == before.1.saturating_add(1) && items.last() == Some(&before.3)
            }),
    )]
    #[inline]
    pub fn file(
        &mut self,
        key: UnitKey,
        entry: AttributeEntry,
    )
    {
        self.entries.entry(key).or_default().push(entry);
    }

    /// The entries filed under `key`, in source order.
    ///
    /// # Specification
    /// - requires: nothing — a key this table holds nothing for is admissible
    ///   input, which is the unattributed declaration's case.
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
    #[spec(
        ensures: |ret| match self.entries.get(&key) {
            | Some(entries) => core::ptr::eq(&raw const *ret, &raw const *entries.as_slice()),
            | None => ret.is_empty(),
        },
    )]
    #[inline]
    #[must_use]
    pub fn entries(
        &self,
        key: UnitKey,
    ) -> &[AttributeEntry]
    {
        self.entries.get(&key).map_or(&[], Vec::as_slice)
    }

    /// File `laws`, what the `respects` entry filed under `key` names.
    ///
    /// # Specification
    /// - requires: an entry naming `laws` is filed under `key`; the attribute
    ///   pass refuses a second `respects` for one declaration, so `key` holds
    ///   no laws yet.
    /// - ensures: [`Self::laws`] at `key` answers `laws`.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — laws filed under one key are read back from it and
    ///   from no other.
    /// - witness: `attribute::tests::a_respects_payload_names_its_laws_in_written_order`
    #[spec(
        captures: count = laws.len(),
        ensures: self.laws.get(&key).is_some_and(|held| held.len() == count),
    )]
    #[inline]
    pub fn file_laws(
        &mut self,
        key: UnitKey,
        laws: Vec<ConstantIndex>,
    )
    {
        let _replaced = self.laws.insert(key, laws);
    }

    /// The laws the `respects` entry filed under `key` names, in the order
    /// it names them.
    ///
    /// # Specification
    /// - requires: nothing — a key holding no laws is admissible input, a
    ///   declaration that is no lawful fold.
    /// - ensures: exactly the laws filed under `key`; the empty slice when none
    ///   were.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a filed key and an unfiled one separate the two
    ///   answers.
    /// - witness: `attribute::tests::a_respects_payload_names_its_laws_in_written_order`
    #[spec(
        ensures: |ret| match self.laws.get(&key) {
            | Some(laws) => core::ptr::eq(&raw const *ret, &raw const *laws.as_slice()),
            | None => ret.is_empty(),
        },
    )]
    #[inline]
    #[must_use]
    pub fn laws(
        &self,
        key: UnitKey,
    ) -> &[ConstantIndex]
    {
        self.laws.get(&key).map_or(&[], Vec::as_slice)
    }

    /// File `worlds`, what the `entry` entry filed under `key` names: the
    /// declaration's home, then the world of each capability it holds.
    ///
    /// # Specification
    /// - requires: an entry naming `worlds` is filed under `key`; the attribute
    ///   pass refuses a second `entry` for one declaration, so `key` holds no
    ///   worlds yet.
    /// - ensures: [`Self::worlds`] at `key` answers `worlds`.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — worlds filed under one key are read back from it and
    ///   from no other.
    /// - witness: `lower::world::tests::an_entry_names_its_home_then_its_capabilities`
    #[spec(
        captures: count = worlds.len(),
        ensures: self.worlds.get(&key).is_some_and(|held| held.len() == count),
    )]
    #[inline]
    pub fn file_worlds(
        &mut self,
        key: UnitKey,
        worlds: Vec<ConstantIndex>,
    )
    {
        let _replaced = self.worlds.insert(key, worlds);
    }

    /// File `named`, what the `attribute` entry filed under `key` names: as
    /// worlds for `entry`, as laws for `respects`, and nothing when it names
    /// none, which is every other attribute's case.
    ///
    /// # Specification
    /// - requires: `named` is what the `attribute` entry filed under `key`
    ///   names.
    /// - ensures: [`Self::worlds`] at `key` answers a non-empty `named` of an
    ///   `entry`, [`Self::laws`] a non-empty `named` of any other attribute,
    ///   and an empty one changes nothing.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an `entry`, a `respects` and an unnamed attribute
    ///   separate the three routes.
    /// - witness: `lower::world::tests::an_entry_names_its_home_then_its_capabilities`
    /// - witness: `lower::tests::a_respects_attribute_names_its_laws_through_either_form`
    #[spec(
        captures: count = named.len(),
        ensures: count == 0
            || if attribute == RegisteredAttribute::ENTRY { self.worlds(key).len() == count } else { self.laws(key).len() == count },
    )]
    #[inline]
    pub fn file_named(
        &mut self,
        key: UnitKey,
        attribute: RegisteredAttribute,
        named: Vec<ConstantIndex>,
    )
    {
        if named.is_empty() {
            return;
        }
        if attribute == RegisteredAttribute::ENTRY {
            self.file_worlds(key, named);
        }
        else {
            self.file_laws(key, named);
        }
    }

    /// The worlds the `entry` entry filed under `key` names, its home first,
    /// in the order it names them.
    ///
    /// # Specification
    /// - requires: nothing — a key holding no worlds is admissible input, a
    ///   declaration judged where its context places it.
    /// - ensures: exactly the worlds filed under `key`; the empty slice when
    ///   none were.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a filed key and an unfiled one separate the two
    ///   answers.
    /// - witness: `lower::world::tests::an_entry_names_its_home_then_its_capabilities`
    #[spec(
        ensures: |ret| match self.worlds.get(&key) {
            | Some(worlds) => core::ptr::eq(&raw const *ret, &raw const *worlds.as_slice()),
            | None => ret.is_empty(),
        },
    )]
    #[inline]
    #[must_use]
    pub fn worlds(
        &self,
        key: UnitKey,
    ) -> &[ConstantIndex]
    {
        self.worlds.get(&key).map_or(&[], Vec::as_slice)
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
    use alloc::vec;

    use gandr_core_term::CoreArena;
    use gandr_kernel_term::ConstantIndex;
    use gandr_surface_syntax::ByteOffset;
    use gandr_surface_syntax::FormRank;
    use gandr_surface_syntax::NodeDigest;
    use gandr_surface_syntax::NodeKey;
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
    use super::names;
    use super::payload;
    use super::payload_verdict;
    use super::registry;
    use super::suggestion;
    use crate::fixture::registered;
    use crate::fixture::span;
    use crate::resolve::SurfaceName;
    use crate::unit::SourceIndex;
    use crate::unit::UnitKey;

    /// The key of the form whose digest is `form`, in the source at `source`.
    ///
    /// # Specification
    /// trivial.
    fn keyed(
        source: SourceIndex,
        form: NodeDigest,
    ) -> UnitKey
    {
        UnitKey::new(source, NodeKey::new(form, FormRank::default()))
    }

    #[test]
    fn suggestions_include_the_bound_and_break_ties_by_registry_order()
    {
        for spelling in AttributeRegistry::names() {
            assert_eq!(
                AttributeRegistry::suggestion(SurfaceName::from(spelling.as_ref())),
                Maybe::Present(spelling)
            );
        }
        let owes = registered(SurfaceName::from("owes"));
        assert_eq!(
            AttributeRegistry::suggestion(SurfaceName::from("ow")),
            Maybe::Present(owes)
        );
        assert_eq!(
            AttributeRegistry::suggestion(SurfaceName::from("e")),
            Maybe::Absent(suggestion::Absent::BeyondBound)
        );
        assert_eq!(
            edit_distance(SurfaceName::from("rows"), owes),
            EditDistance::from(2_usize)
        );
        assert_eq!(
            edit_distance(
                SurfaceName::from("rows"),
                registered(SurfaceName::from("runs"))
            ),
            EditDistance::from(2_usize)
        );
        assert_eq!(
            AttributeRegistry::suggestion(SurfaceName::from("rows")),
            Maybe::Present(owes)
        );
        assert_eq!(
            AttributeRegistry::suggestion(SurfaceName::from("ouns")),
            Maybe::Present(registered(SurfaceName::from("runs"))),
            "a later spelling one edit away displaces an earlier one two away"
        );
    }

    #[test]
    fn edit_distance_counts_unicode_scalars_not_bytes()
    {
        let runs = registered(SurfaceName::from("runs"));
        assert_eq!(
            edit_distance(SurfaceName::from("rüns"), runs),
            EditDistance::from(1_usize)
        );
        assert_eq!(
            edit_distance(SurfaceName::from("ru水ns"), runs),
            EditDistance::from(1_usize)
        );
        assert_eq!(
            edit_distance(SurfaceName::from("水"), runs),
            EditDistance::from(4_usize)
        );
        assert_eq!(
            AttributeRegistry::suggestion(SurfaceName::from("rüns")),
            Maybe::Present(runs)
        );
    }
    #[test]
    fn every_registered_attribute_answers_its_schema()
    {
        let expected = [
            ("checks", AttributeSchema::Marker),
            ("owes", AttributeSchema::Integer),
            ("refuses", AttributeSchema::Text),
            ("runs", AttributeSchema::Text),
            ("normalizes", AttributeSchema::Text),
            ("doc", AttributeSchema::Text),
            ("explicit_exits", AttributeSchema::Marker),
            ("explicit_runs", AttributeSchema::MarkerOr("effects")),
            ("respects", AttributeSchema::Names),
            ("entry", AttributeSchema::Names),
            ("form", AttributeSchema::Word(&["explicit", "sugared"])),
        ];

        for (spelling, schema) in expected {
            let found = AttributeRegistry::lookup(SurfaceName::from(spelling));
            assert_eq!(
                found.map(|(_name, held)| held),
                Maybe::Present(schema),
                "the registry is pinned row by row"
            );
            if let Maybe::Present((held, _schema)) = found {
                let actual: &str = held.as_ref();
                assert_eq!(
                    actual, spelling,
                    "the resolved name keeps its exact identifier"
                );
            }
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
            ("normalize", "normalizes"),
            ("docs", "doc"),
            ("explicit_exit", "explicit_exits"),
            ("explicit_run", "explicit_runs"),
            ("respect", "respects"),
            ("entri", "entry"),
            ("forms", "form"),
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
            AttributeRegistry::suggestion(SurfaceName::from("expect")),
            Maybe::Absent(suggestion::Absent::BeyondBound),
            "three edits from the nearest entry is past the bound"
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
        use PayloadVerdict::Admitted as A;
        use PayloadVerdict::IllTyped as I;
        use PayloadVerdict::Missing as M;
        let forms = [
            PayloadForm::Absent,
            PayloadForm::Integer,
            PayloadForm::Text,
            PayloadForm::OtherText,
            PayloadForm::Word,
            PayloadForm::OtherWord,
            PayloadForm::OtherValue,
        ];
        // One row per schema, one column per form in the order above.
        let expected = [
            (AttributeSchema::Marker, [A, I, I, I, I, I, I]),
            (AttributeSchema::Integer, [M, A, I, I, I, I, I]),
            (AttributeSchema::Text, [M, I, A, A, I, I, I]),
            (AttributeSchema::MarkerOr("effects"), [A, I, A, I, I, I, I]),
            (AttributeSchema::Names, [M, I, I, I, A, I, A]),
            (AttributeSchema::Word(&["explicit", "sugared"]), [
                M, I, I, I, A, I, I,
            ]),
        ];

        for (schema, verdicts) in expected {
            for (form, verdict) in forms.into_iter().zip(verdicts) {
                assert_eq!(
                    payload_verdict(schema, form),
                    verdict,
                    "{schema} against {form}: the payload verdict table is pinned cell by cell"
                );
            }
        }
    }

    #[test]
    fn a_respects_payload_names_its_laws_in_written_order()
    {
        let mut arena = CoreArena::new();
        let (first, second) = (ConstantIndex::from(7_usize), ConstantIndex::from(3_usize));
        let named = arena.value_constant(first);
        let other = arena.value_constant(second);
        let pair = arena.value_tuple(&[named, other]);
        let unit = arena.value_unit();
        let mixed = arena.value_tuple(&[named, unit]);
        assert_eq!(
            names(&arena, named),
            Maybe::Present(vec![first]),
            "a declared name names one law"
        );
        assert_eq!(
            names(&arena, pair),
            Maybe::Present(vec![first, second]),
            "a tuple names its laws in the order written, not by position"
        );
        for unnamed in [mixed, unit] {
            assert_eq!(
                names(&arena, unnamed),
                Maybe::Absent(names::Absent::Unnamed),
                "a payload holding anything but names names no law"
            );
        }
        let mut table = AttributeTable::new();
        let filed = keyed(SourceIndex::default(), NodeDigest::from([1_u8; 32_usize]));
        let unfiled = keyed(SourceIndex::default(), NodeDigest::from([2_u8; 32_usize]));
        table.file_laws(filed, vec![first, second]);
        assert_eq!(
            table.laws(filed),
            [first, second].as_slice(),
            "the laws filed under a key are read back from it"
        );
        assert!(table.laws(unfiled).is_empty(), "and from no other");
    }

    #[test]
    fn entries_keep_the_order_they_were_filed_in()
    {
        let mut table = AttributeTable::new();
        let key = keyed(SourceIndex::default(), NodeDigest::from([1_u8; 32_usize]));
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

    /// Two declarations keep their own lists, whether their forms differ or
    /// one form is written byte for byte in two sources of a unit (#596).
    #[test]
    fn two_declarations_keep_separate_entry_lists()
    {
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
        let form = NodeDigest::from([1_u8; 32_usize]);
        let first_key = keyed(SourceIndex::default(), form);
        for second_key in [
            keyed(SourceIndex::default(), NodeDigest::from([2_u8; 32_usize])),
            keyed(SourceIndex::from(1_usize), form),
        ] {
            let mut table = AttributeTable::new();
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
    }

    #[test]
    fn an_unattributed_declaration_has_no_entries()
    {
        let table = AttributeTable::new();

        assert!(
            table
                .entries(keyed(
                    SourceIndex::default(),
                    NodeDigest::from([9_u8; 32_usize])
                ))
                .is_empty(),
            "a key the table holds nothing for reads as the empty list"
        );
    }

    /// Every schema and every payload form renders a message of its own, and
    /// a word schema lists each word it admits.
    #[test]
    fn every_schema_and_payload_form_renders_its_own_message()
    {
        use alloc::string::String;
        use alloc::string::ToString;
        use alloc::vec::Vec;

        let apart = |messages: &[String]| {
            for (position, message) in messages.iter().enumerate() {
                for other in messages.iter().skip(position.saturating_add(1)) {
                    assert_ne!(message, other, "two renderings alike read as one");
                }
            }
        };
        let schemas: Vec<String> = [
            AttributeSchema::Marker,
            AttributeSchema::Integer,
            AttributeSchema::Text,
            AttributeSchema::MarkerOr("all"),
            AttributeSchema::Names,
            AttributeSchema::Word(&["explicit", "implicit"]),
        ]
        .iter()
        .map(ToString::to_string)
        .collect();
        apart(&schemas);
        assert!(
            schemas
                .last()
                .is_some_and(|words| words.contains("`explicit`, `implicit`")),
            "a word schema lists its words: {schemas:?}"
        );
        let forms: Vec<String> = [
            PayloadForm::Absent,
            PayloadForm::Integer,
            PayloadForm::Text,
            PayloadForm::OtherText,
            PayloadForm::Word,
            PayloadForm::OtherWord,
            PayloadForm::OtherValue,
        ]
        .iter()
        .map(ToString::to_string)
        .collect();
        apart(&forms);
        assert_eq!(usize::from(EditDistance::from(3_usize)), 3_usize);
    }
}
