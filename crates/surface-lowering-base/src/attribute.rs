//! The entity-attribute layer: the closed [`AttributeRegistry`], the payload
//! [`PayloadVerdict`] each schema returns, and the [`AttributeTable`] a lowered
//! module carries beside its declarations.
//!
//! Its public types: `AttributeRegistry`, `AttributeSchema`,
//! `RegisteredAttribute`, `PayloadForm`, `PayloadVerdict`,
//! `payload_form`, `payload_verdict`, `texts`, `AttributeEntry`,
//! `AttributeTable` and `AttributedCount`.
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
//! # Every schema but `respects`, `entry` and `identity` is inert
//!
//! The lowered term is neither read nor written by the attribute pass: a
//! payload lowers to its own core value, filed here, and nothing about the
//! decorated declaration's core term depends on it. `respects`, `entry` and
//! `identity` are the semantic attributes: a `respects` payload names the
//! laws a fold rests on, an `entry` payload the worlds a declaration is
//! judged at and migrates to, which the table keeps beside the entry as
//! constants and the checker's declaration carries, and an `identity`
//! payload on a sealed module's type member the relation, reflexivity and
//! optional transport law its atom is admitted with. The term is still
//! untouched; what changes is the evidence the declaration is admitted on,
//! the world it is judged at, or what a path at the atom is.
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
//! The registry is closed: `checks`, `explicit_exits` and `inert` take no
//! payload, `explicit_runs` none or a text naming its one option, `effects`,
//! `owes` an integer, `refuses`, `runs`, `normalizes` and `doc` a text,
//! `distributes` a text or a tuple of texts, read in written order, `respects`
//! and `entry` one declared name or a tuple of them, `identity` a tuple of two
//! or three declared names, `form` one bare word, `explicit` or `sugared`, and
//! `deprecated` none or a record of the texts `since` and `note`, either
//! left out. The attribute block
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
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::Literal;
use gandr_kernel_term::StringLiteral;
use gandr_surface_grammar::EditDistance;
use gandr_surface_grammar::LabelText;
use gandr_surface_grammar::edit_distance;
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
            /// The payload is a form its schema reads as its spelling, never
            /// as a value: [`super::AttributeSchema::Spelled`]. The spelling
            /// is filed beside the entry.
            Spelled,
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

quenchant_shape::reason_enum! {
    /// Why a `distributes` payload holds no texts.
    pub mod texts {
        /// The payload is a value of another form.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// Neither a text nor a non-empty tuple of texts.
            Untexted,
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

/// The texts a `distributes` payload holds, in the order it writes them.
///
/// One text literal lowers to itself and a tuple to its components, so a
/// payload holds texts exactly when it is one text literal or a non-empty
/// tuple of them.
///
/// # Specification
/// - requires: `payload` is the lowered value of a payload the
///   [`AttributeSchema::Texts`] schema admitted.
/// - ensures: the one text `payload` is, or the texts of its components in
///   written order when it is a non-empty tuple of text literals;
///   [`texts::Absent::Untexted`] for any other value, the unit included.
/// - fails: never — such a payload is an absence, not an error.
/// - panics: none.
///
/// # Termination
/// - reason: one pass over the tuple's finite components, not recursion.
/// - measure: the components left.
///
/// # Adequacy
/// - hypothesis: L3 — one text, a tuple of texts, a tuple holding an integer,
///   and the unit separate the answers.
/// - witness: `attribute::tests::a_distributes_payload_holds_its_texts_in_written_order`
#[spec(ensures: |ref ret| match (ret, arena.value(payload)) {
    | (&Maybe::Present(ref texts), Some(&Value::Literal(Literal::Text(_)))) => texts.len() == 1,
    | (&Maybe::Present(ref texts), Some(&Value::Tuple(ref items))) => !items.is_empty() && texts.len() == items.len(),
    | (&Maybe::Present(_), _) => false,
    | (&Maybe::Absent(_), _) => true,
})]
#[inline]
pub fn texts(
    arena: &CoreArena,
    payload: ValueId,
) -> Maybe<Vec<&StringLiteral>, texts::Absent>
{
    let untexted = Maybe::Absent(texts::Absent::Untexted);
    match arena.value(payload) {
        Some(&Value::Literal(Literal::Text(ref text))) => Maybe::Present(Vec::from([text])),
        Some(&Value::Tuple(ref items)) if !items.is_empty() => {
            let mut texts = Vec::with_capacity(items.len());
            for &item in items {
                let Some(&Value::Literal(Literal::Text(ref text))) = arena.value(item)
                else {
                    return untexted;
                };
                texts.push(text);
            }
            Maybe::Present(texts)
        },
        _ => untexted,
    }
}

/// The relation, reflexivity and, when stated, transport law an `identity`
/// payload names, as the components the payload lowered them to.
///
/// # Specification
/// - requires: `payload` is the lowered value of a payload the
///   [`AttributeSchema::Interface`] schema admitted.
/// - ensures: the components of `payload`, in written order, when it is a tuple
///   of two or three declared names; [`names::Absent::Unnamed`] for any other
///   value, a lone name included.
/// - fails: never — an unnamed payload is an absence, not an error.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a pair, a triple, a lone name, four names and a pair
///   holding a non-name separate the answers.
/// - witness: `attribute::tests::an_identity_payload_names_two_or_three_declarations`
#[spec(ensures: |ref ret| match *ret {
    | Maybe::Present(ref members) => (2_usize ..= 3_usize).contains(&members.len())
        && members.iter().all(|&member| matches!(arena.value(member), Some(&Value::Constant(_)))),
    | Maybe::Absent(_) => true,
})]
#[inline]
pub fn members(
    arena: &CoreArena,
    payload: ValueId,
) -> Maybe<Vec<ValueId>, names::Absent>
{
    match arena.value(payload) {
        Some(&Value::Tuple(ref items))
            if (2_usize ..= 3_usize).contains(&items.len())
                && items
                    .iter()
                    .all(|&item| matches!(arena.value(item), Some(&Value::Constant(_)))) =>
        {
            Maybe::Present(items.to_vec())
        },
        _ => Maybe::Absent(names::Absent::Unnamed),
    }
}

/// What a `deprecated` attribute states: the version that deprecated the
/// declaration and a note on what to use instead, each when written.
///
/// # Specification
/// - requires: nothing.
/// - ensures: each text is the one its record field spells.
/// - panics: none.
/// - executable: none — a carrier; [`deprecation`] states what it holds.
///
/// # Adequacy
/// - hypothesis: L3 — as [`deprecation`].
/// - witness: `attribute::tests::a_deprecated_payload_reads_its_texts`
#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Deprecation
{
    /// The version that deprecated the declaration, when stated.
    pub since: Option<String>,
    /// What to use instead, when stated.
    pub note: Option<String>,
}

/// What a `deprecated` record payload states, read off its lowered value.
///
/// # Specification
/// - requires: `payload` is the lowered value of a payload the
///   [`AttributeSchema::MarkerOrRecord`] schema admitted.
/// - ensures: the texts of `since` and `note` when `payload` is a record each
///   of whose labels is one of [`RegisteredAttribute::DEPRECATION_FIELDS`] and
///   each of whose values is a text literal; [`names::Absent::Unnamed`] for any
///   other value, a record with another label or a field that is no text
///   included.
/// - fails: never — a payload of another shape is an absence, not an error.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a record of both texts, of one, the empty record, a
///   foreign label, a field that is an integer and a tuple separate the
///   answers.
/// - witness: `attribute::tests::a_deprecated_payload_reads_its_texts`
#[spec(ensures: |ref ret| match (ret, arena.value(payload)) {
    | (&Maybe::Present(_), Some(&Value::Record(ref written))) => written.keys().all(|label| matches!(label.as_ref(), "since" | "note")),
    | (&Maybe::Present(_), _) => false,
    | (&Maybe::Absent(_), _) => true,
})]
#[inline]
pub fn deprecation(
    arena: &CoreArena,
    payload: ValueId,
) -> Maybe<Deprecation, names::Absent>
{
    let Some(&Value::Record(ref written)) = arena.value(payload)
    else {
        return Maybe::Absent(names::Absent::Unnamed);
    };
    let mut stated = Deprecation::default();
    for (label, &value) in written {
        let Some(&Value::Literal(Literal::Text(ref text))) = arena.value(value)
        else {
            return Maybe::Absent(names::Absent::Unnamed);
        };
        let text = String::from(text.as_ref());
        match label.as_ref() {
            "since" => stated.since = Some(text),
            "note" => stated.note = Some(text),
            _ => return Maybe::Absent(names::Absent::Unnamed),
        }
    }
    Maybe::Present(stated)
}

/// A use of a deprecated declaration: the use's bytes, the declaration's
/// name, and what its `deprecated` attribute states.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `span` is a written name the lowering resolved to the declaration
///   `name` names, whose attribute states `deprecation`.
/// - panics: none.
/// - executable: none — a carrier; `LoweredModule::deprecated_uses` states what
///   it holds.
///
/// # Adequacy
/// - hypothesis: L3 — the one use of a marked declaration carries its bytes,
///   its name and the text its attribute states.
/// - witness: `tests::attribute::a_deprecated_use_carries_its_bytes_its_name_and_its_texts`
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct DeprecatedUse<'source>
{
    /// The bytes of the use.
    pub span: ByteSpan,
    /// The deprecated declaration's name.
    pub name: SurfaceName<'source>,
    /// What its `deprecated` attribute states.
    pub deprecation: Deprecation,
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
    /// laws it names, one per rule of the presented type the fold's `match`
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
    /// `identity`: the abstract type sealing the type member it decorates
    /// relates its elements by the relation its payload names first, with
    /// the reflexivity it names second and, when it names a third, the
    /// transport law that makes the relation the atom's identity.
    pub const IDENTITY: Self = Self("identity");
    /// `deprecated`: the declaration it decorates is kept for the code that
    /// still uses it, and each use is reported, with the version that
    /// deprecated it and a note on what to use instead when the record
    /// payload states them.
    pub const DEPRECATED: Self = Self("deprecated");
    /// The fields a `deprecated` record may state, each a text.
    pub const DEPRECATION_FIELDS: &'static [&'static str] = &["since", "note"];
    /// `boundary`: the `extern "rust"` block it decorates is checked against
    /// the rows its payload names, one per member in written order. Each
    /// member's declared types, printed by Rust's default layout, realise its
    /// row, or the block is refused by the first clause a member breaks.
    pub const BOUNDARY: Self = Self("boundary");
    /// `builtin`: the declaration it decorates takes the built-in role its
    /// word names, which a core former reads by role
    /// ([`gandr_kernel_term::Builtin`]).
    pub const BUILTIN: Self = Self("builtin");
    /// `traces`: the run of the declaration it decorates is recorded, and the
    /// payload states the web one channel's play decomposes to. It is the one
    /// attribute written more than once on a name, once per channel.
    pub const TRACES: Self = Self("traces");
    /// `reads`: the declaration it decorates checks, owing nothing, and
    /// mentions exactly the items its payload names, `()` when it mentions
    /// none: the footprint read off its content table's roots.
    pub const READS: Self = Self("reads");
    /// `distributes`: the declaration it decorates checks, owing nothing, and
    /// the runs of its draws, one for each sequence of answers, give the
    /// outcomes its payload states with their exact weights.
    pub const DISTRIBUTES: Self = Self("distributes");
    /// `inert`: the top-level definition it decorates is inert, as a theory's
    /// operation marked `@[ inert ]` is. Only another inert declaration and the
    /// manifest step read it, and a package's address leaves it out. A
    /// module's member takes no mark.
    pub const INERT: Self = Self("inert");
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
    /// One text literal, or a tuple of text literals.
    Texts,
    /// A bare marker, or the one text literal spelling the option named.
    MarkerOr(&'static str),
    /// One declared name, or a tuple of declared names.
    Names,
    /// A tuple of two or three declared names: a relation, its reflexivity
    /// and, when stated, its transport law.
    Interface,
    /// One bare word among those named, read as written and never lowered as
    /// a value.
    Word(&'static [&'static str]),
    /// A bare marker, or a record whose fields are among those named, each a
    /// text literal, any of them left out.
    MarkerOrRecord(&'static [&'static str]),
    /// One form written unquoted, read as its spelling and never lowered as a
    /// value.
    Spelled,
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
            Self::Texts => f.write_str("a text or a tuple of texts"),
            Self::MarkerOr(option) => write!(f, "no payload or the text \"{option}\""),
            Self::Names => f.write_str("a declared name or a tuple of declared names"),
            Self::Interface => f.write_str(
                "a tuple of two or three declared names: a relation, its reflexivity and \
                 optionally its transport law",
            ),
            Self::Word(words) => {
                f.write_str("one of the words")?;
                for (index, word) in words.iter().enumerate() {
                    let joint = if index == 0 { " " } else { ", " };
                    write!(f, "{joint}`{word}`")?;
                }
                Ok(())
            },
            Self::MarkerOrRecord(fields) => {
                f.write_str("no payload or a record of the texts")?;
                for (index, field) in fields.iter().enumerate() {
                    let joint = if index == 0 { " " } else { ", " };
                    write!(f, "{joint}`{field}`")?;
                }
                Ok(())
            },
            Self::Spelled => f.write_str("an unquoted form"),
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
    /// A payload written with a name, `primes = 2`.
    Named,
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
            Self::Named => f.write_str("a named payload"),
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
const REGISTRY: [(&str, AttributeSchema); 20_usize] = [
    ("checks", AttributeSchema::Marker),
    ("owes", AttributeSchema::Integer),
    ("refuses", AttributeSchema::Text),
    ("runs", AttributeSchema::Text),
    ("normalizes", AttributeSchema::Text),
    ("decomposes", AttributeSchema::Spelled),
    (RegisteredAttribute::TRACES.0, AttributeSchema::Spelled),
    (RegisteredAttribute::READS.0, AttributeSchema::Spelled),
    (RegisteredAttribute::DISTRIBUTES.0, AttributeSchema::Texts),
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
    (RegisteredAttribute::IDENTITY.0, AttributeSchema::Interface),
    (
        RegisteredAttribute::DEPRECATED.0,
        AttributeSchema::MarkerOrRecord(RegisteredAttribute::DEPRECATION_FIELDS),
    ),
    (RegisteredAttribute::BOUNDARY.0, AttributeSchema::Names),
    (
        RegisteredAttribute::BUILTIN.0,
        AttributeSchema::Word(gandr_kernel_term::Builtin::WORDS),
    ),
    (RegisteredAttribute::INERT.0, AttributeSchema::Marker),
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
            let distance = edit_distance(LabelText(name.as_ref()), LabelText(candidate.as_ref()));
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
/// - ensures: absence is admitted exactly by the bare marker, the
///   marker-or-option and the marker-or-record schemas; an integer literal
///   exactly by the integer schema; a text literal by the text schema and, read
///   as the option it spells, by the marker-or-option schema; a text spelling
///   no option by the text schema alone; a bare word by the names schema, as
///   the one name it declares, and by the word schema, read as one of its
///   words; a word spelling none by no schema; any other value exactly by the
///   names, interface and marker-or-record schemas, each reading its shape off
///   the lowered value; a word or any other value, unquoted, and a named
///   payload, by the spelled schema alone; every other pair is refused, and the
///   refusal is the missing one exactly when nothing was written for a schema
///   that takes something.
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
            (
                AttributeSchema::Marker
                    | AttributeSchema::MarkerOr(_)
                    | AttributeSchema::MarkerOrRecord(_),
                PayloadForm::Absent
            ) | (AttributeSchema::Integer, PayloadForm::Integer)
                | (AttributeSchema::Text, PayloadForm::Text | PayloadForm::OtherText)
                | (
                    AttributeSchema::Texts,
                    PayloadForm::Text | PayloadForm::OtherText | PayloadForm::OtherValue
                )
                | (AttributeSchema::MarkerOr(_), PayloadForm::Text)
                | (
                    AttributeSchema::Names | AttributeSchema::Spelled,
                    PayloadForm::Word | PayloadForm::OtherValue
                )
                | (
                    AttributeSchema::Interface | AttributeSchema::MarkerOrRecord(_),
                    PayloadForm::OtherValue
                )
                | (AttributeSchema::Word(_), PayloadForm::Word)
                | (AttributeSchema::Spelled, PayloadForm::Named)
        );
        let missing = matches!(form, PayloadForm::Absent)
            && matches!(
                schema,
                AttributeSchema::Integer
                    | AttributeSchema::Text
                    | AttributeSchema::Texts
                    | AttributeSchema::Names
                    | AttributeSchema::Interface
                    | AttributeSchema::Word(_)
                    | AttributeSchema::Spelled
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
        (
            AttributeSchema::Marker
            | AttributeSchema::MarkerOr(_)
            | AttributeSchema::MarkerOrRecord(_),
            PayloadForm::Absent,
        )
        | (AttributeSchema::Integer, PayloadForm::Integer)
        | (AttributeSchema::Text, PayloadForm::Text | PayloadForm::OtherText)
        | (
            AttributeSchema::Texts,
            PayloadForm::Text | PayloadForm::OtherText | PayloadForm::OtherValue,
        )
        | (AttributeSchema::MarkerOr(_), PayloadForm::Text)
        | (
            AttributeSchema::Names | AttributeSchema::Spelled,
            PayloadForm::Word | PayloadForm::OtherValue,
        )
        | (
            AttributeSchema::Interface | AttributeSchema::MarkerOrRecord(_),
            PayloadForm::OtherValue,
        )
        | (AttributeSchema::Word(_), PayloadForm::Word)
        | (AttributeSchema::Spelled, PayloadForm::Named) => PayloadVerdict::Admitted,
        (
            AttributeSchema::Integer
            | AttributeSchema::Text
            | AttributeSchema::Texts
            | AttributeSchema::Names
            | AttributeSchema::Interface
            | AttributeSchema::Word(_)
            | AttributeSchema::Spelled,
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
            AttributeSchema::Texts,
            PayloadForm::Integer | PayloadForm::Word | PayloadForm::OtherWord,
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
            AttributeSchema::Names | AttributeSchema::Spelled,
            PayloadForm::Integer
            | PayloadForm::Text
            | PayloadForm::OtherText
            | PayloadForm::OtherWord,
        )
        | (
            AttributeSchema::Interface | AttributeSchema::MarkerOrRecord(_),
            PayloadForm::Integer
            | PayloadForm::Text
            | PayloadForm::OtherText
            | PayloadForm::Word
            | PayloadForm::OtherWord,
        )
        | (
            AttributeSchema::Word(_),
            PayloadForm::Integer
            | PayloadForm::Text
            | PayloadForm::OtherText
            | PayloadForm::OtherWord
            | PayloadForm::OtherValue,
        )
        | (
            AttributeSchema::Marker
            | AttributeSchema::Integer
            | AttributeSchema::Text
            | AttributeSchema::Texts
            | AttributeSchema::MarkerOr(_)
            | AttributeSchema::Names
            | AttributeSchema::Interface
            | AttributeSchema::MarkerOrRecord(_)
            | AttributeSchema::Word(_),
            PayloadForm::Named,
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
/// - hypothesis: L3 — the literal formers, a bare name and three other formers
///   each read as their own form.
/// - witness: `attribute::tests::each_former_reads_as_its_own_payload_form`
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
        Former::Character
        | Former::Hole
        | Former::Binary
        | Former::Unary
        | Former::Constructor
        | Former::Parenthesized
        | Former::TypeQuote
        | Former::Boolean
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
        | Former::ForgetModel
        | Former::Case
        | Former::If
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
        | Former::LinearArrowType
        | Former::ProductType
        | Former::SumType
        | Former::LazyProductType
        | Former::TelescopeType
        | Former::LabelledSumType
        | Former::LazyRecordType
        | Former::ParenthesizedType
        | Former::PathType
        | Former::BridgeType
        | Former::FlowType
        | Former::RelationType
        | Former::ManifestType
        | Former::CapabilityType
        | Former::AtType
        | Former::StagedType
        | Former::ModedType
        | Former::Scope
        | Former::Declaration
        | Former::AttributeBlock
        | Former::Visibility
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
        | Former::Reserved(_)
        | Former::Unadmitted(_)
        | Former::Misplaced => PayloadForm::OtherValue,
    }
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
/// cross-tree key.
///
/// The laws a `respects` entry, the worlds an `entry` entry and the interface
/// an `identity` entry names are kept under the same key.
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
    /// Type member key to the relation, reflexivity and transport law its
    /// `identity` entry names, in that order, as the payload's components.
    interfaces: BTreeMap<UnitKey, Vec<ValueId>>,
    /// Declaration key and entry span to the spelling of a payload its schema
    /// reads unquoted: [`AttributeSchema::Spelled`]. The span tells apart the
    /// entries of an attribute written more than once.
    spellings: BTreeMap<(UnitKey, ByteSpan), String>,
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
            interfaces: BTreeMap::new(),
            spellings: BTreeMap::new(),
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
    /// - witness: `attribute::tests::the_table_reads_back_what_it_files_under_its_key_alone`
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
    /// worlds for `entry`, as laws for `respects`, and nothing for any other
    /// attribute, whose names its own pass reads off the payload.
    ///
    /// # Specification
    /// - requires: `named` is what the `attribute` entry filed under `key`
    ///   names.
    /// - ensures: [`Self::worlds`] at `key` answers a non-empty `named` of an
    ///   `entry`, [`Self::laws`] one of a `respects`, and anything else changes
    ///   nothing.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an `entry`, a `respects` and a `boundary` separate
    ///   the three routes.
    /// - witness: `attribute::tests::the_table_reads_back_what_it_files_under_its_key_alone`
    #[spec(
        captures: count = named.len(),
        ensures: count == 0
            || if attribute == RegisteredAttribute::ENTRY { self.worlds(key).len() == count } else if attribute == RegisteredAttribute::RESPECTS { self.laws(key).len() == count } else { true },
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
        else if attribute == RegisteredAttribute::RESPECTS {
            self.file_laws(key, named);
        }
    }

    /// File `members`, the relation, reflexivity and, when stated, transport
    /// law the `identity` entry filed under the type member `key` names.
    ///
    /// # Specification
    /// - requires: an `identity` entry naming `members` is filed under `key`;
    ///   the attribute pass refuses a second `identity` for one member, so
    ///   `key` holds no interface yet.
    /// - ensures: [`Self::interface`] at `key` answers `members`.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an interface filed under one key is read back from it
    ///   and from no other.
    /// - witness: `attribute::tests::an_identity_payload_names_two_or_three_declarations`
    #[spec(
        captures: count = members.len(),
        ensures: self.interfaces.get(&key).is_some_and(|held| held.len() == count),
    )]
    #[inline]
    pub fn file_interface(
        &mut self,
        key: UnitKey,
        members: Vec<ValueId>,
    )
    {
        let _replaced = self.interfaces.insert(key, members);
    }

    /// The relation, reflexivity and, when stated, transport law the
    /// `identity` entry filed under the type member `key` names, in that
    /// order, as the values its payload lowered them to.
    ///
    /// # Specification
    /// - requires: nothing — a key holding no interface is admissible input, a
    ///   type member sealed with no identity of its own.
    /// - ensures: exactly the members filed under `key`; the empty slice when
    ///   none were.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a filed key and an unfiled one separate the two
    ///   answers.
    /// - witness: `attribute::tests::an_identity_payload_names_two_or_three_declarations`
    #[spec(
        ensures: |ret| match self.interfaces.get(&key) {
            | Some(members) => core::ptr::eq(&raw const *ret, &raw const *members.as_slice()),
            | None => ret.is_empty(),
        },
    )]
    #[inline]
    #[must_use]
    pub fn interface(
        &self,
        key: UnitKey,
    ) -> &[ValueId]
    {
        self.interfaces.get(&key).map_or(&[], Vec::as_slice)
    }

    /// File `spelled`, the spelling of the payload the entry spanning `at`
    /// filed under `key` was written with, its schema reading it unquoted.
    ///
    /// # Specification
    /// - requires: an entry spanning `at` whose schema is
    ///   [`AttributeSchema::Spelled`] is filed under `key`.
    /// - ensures: [`Self::spelled`] at `key` and `at` answers `spelled`.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a spelling filed under one key is read back from it,
    ///   and from no other key or entry.
    /// - witness: `attribute::tests::the_table_reads_back_what_it_files_under_its_key_alone`
    #[spec(ensures: self.spellings.contains_key(&(key, at)))]
    #[inline]
    pub fn file_spelled(
        &mut self,
        key: UnitKey,
        at: ByteSpan,
        spelled: String,
    )
    {
        let _replaced = self.spellings.insert((key, at), spelled);
    }

    /// The spelling of the payload the entry spanning `at` filed under `key`
    /// was written with, when its schema reads it unquoted.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the spelling filed under `key` and `at`; absent when none
    ///   was.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::file_spelled`].
    /// - witness: `attribute::tests::the_table_reads_back_what_it_files_under_its_key_alone`
    #[spec(ensures: |ret| ret.is_some() == self.spellings.contains_key(&(key, at)))]
    #[inline]
    #[must_use]
    pub fn spelled(
        &self,
        key: UnitKey,
        at: ByteSpan,
    ) -> Option<&String>
    {
        self.spellings.get(&(key, at))
    }

    /// What the `deprecated` entry filed under `key` states, read off its
    /// payload in `arena`.
    ///
    /// # Specification
    /// - requires: `arena` holds the payloads this table's entries were minted
    ///   into.
    /// - ensures: for a `deprecated` entry under `key`, nothing stated for a
    ///   bare marker and the payload's texts for a record, as [`deprecation`]
    ///   reads them; none when `key` holds no such entry.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a marker, a record and an undecorated declaration
    ///   separate the answers.
    /// - witness: `attribute::tests::the_table_reads_back_what_it_files_under_its_key_alone`
    #[spec(ensures: |ret| ret.is_none() || !self.entries(key).is_empty())]
    #[must_use]
    #[inline]
    pub fn deprecation(
        &self,
        key: UnitKey,
        arena: &CoreArena,
    ) -> Option<Deprecation>
    {
        let entry = self
            .entries(key)
            .iter()
            .find(|entry| entry.name() == RegisteredAttribute::DEPRECATED)?;
        Some(match entry.payload() {
            Maybe::Present(value) => match deprecation(arena, value) {
                Maybe::Present(stated) => stated,
                Maybe::Absent(_) => Deprecation::default(),
            },
            Maybe::Absent(_) => Deprecation::default(),
        })
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
    /// - witness: `attribute::tests::the_table_reads_back_what_it_files_under_its_key_alone`
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
    use alloc::collections::BTreeMap;
    use alloc::string::String;
    use alloc::vec;

    use gandr_core_term::CoreArena;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::Literal;
    use gandr_surface_grammar::EditDistance;
    use gandr_surface_grammar::LabelText;
    use gandr_surface_grammar::edit_distance;
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
    use super::Deprecation;
    use super::PayloadForm;
    use super::PayloadVerdict;
    use super::deprecation;
    use super::members;
    use super::names;
    use super::payload;
    use super::payload_verdict;
    use super::registry;
    use super::suggestion;
    use super::texts;
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
            edit_distance(LabelText("rows"), LabelText("owes")),
            EditDistance(2_usize)
        );
        assert_eq!(
            edit_distance(LabelText("rows"), LabelText("runs")),
            EditDistance(2_usize)
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
    fn a_suggestion_counts_unicode_scalars_not_bytes()
    {
        assert_eq!(
            AttributeRegistry::suggestion(SurfaceName::from("rüns")),
            Maybe::Present(registered(SurfaceName::from("runs")))
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
            ("decomposes", AttributeSchema::Spelled),
            ("traces", AttributeSchema::Spelled),
            ("reads", AttributeSchema::Spelled),
            ("distributes", AttributeSchema::Texts),
            ("doc", AttributeSchema::Text),
            ("explicit_exits", AttributeSchema::Marker),
            ("explicit_runs", AttributeSchema::MarkerOr("effects")),
            ("respects", AttributeSchema::Names),
            ("entry", AttributeSchema::Names),
            ("form", AttributeSchema::Word(&["explicit", "sugared"])),
            ("identity", AttributeSchema::Interface),
            (
                "deprecated",
                AttributeSchema::MarkerOrRecord(&["since", "note"]),
            ),
            ("boundary", AttributeSchema::Names),
            (
                "builtin",
                AttributeSchema::Word(&["irSignature", "irPair", "irArgs", "irDecode"]),
            ),
            ("inert", AttributeSchema::Marker),
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
            ("identiy", "identity"),
            ("deprecate", "deprecated"),
            ("decompose", "decomposes"),
            ("trace", "traces"),
            ("read", "reads"),
            ("distribute", "distributes"),
            ("boundary", "boundary"),
            ("builtins", "builtin"),
            ("inrt", "inert"),
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
            PayloadForm::Named,
        ];
        // One row per schema, one column per form in the order above.
        let expected = [
            (AttributeSchema::Marker, [A, I, I, I, I, I, I, I]),
            (AttributeSchema::Integer, [M, A, I, I, I, I, I, I]),
            (AttributeSchema::Text, [M, I, A, A, I, I, I, I]),
            (AttributeSchema::Texts, [M, I, A, A, I, I, A, I]),
            (AttributeSchema::MarkerOr("effects"), [
                A, I, A, I, I, I, I, I,
            ]),
            (AttributeSchema::Names, [M, I, I, I, A, I, A, I]),
            (AttributeSchema::Interface, [M, I, I, I, I, I, A, I]),
            (AttributeSchema::Word(&["explicit", "sugared"]), [
                M, I, I, I, A, I, I, I,
            ]),
            (AttributeSchema::MarkerOrRecord(&["since", "note"]), [
                A, I, I, I, I, I, A, I,
            ]),
            (AttributeSchema::Spelled, [M, I, I, I, A, I, A, A]),
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
    fn a_distributes_payload_holds_its_texts_in_written_order()
    {
        let mut arena = CoreArena::new();
        let mut text = |written: &str| {
            arena.value_literal(Literal::Text(gandr_kernel_term::StringLiteral::new(
                String::from(written),
            )))
        };
        let (half, quarter) = (text("1/2 1"), text("1/4 0"));
        let pair = arena.value_tuple(&[half, quarter]);
        let unit = arena.value_unit();
        let named = arena.value_constant(ConstantIndex::from(3_usize));
        let mixed = arena.value_tuple(&[half, named]);
        let (half_text, quarter_text) = (
            gandr_kernel_term::StringLiteral::new(String::from("1/2 1")),
            gandr_kernel_term::StringLiteral::new(String::from("1/4 0")),
        );
        assert_eq!(
            texts(&arena, half),
            Maybe::Present(vec![&half_text]),
            "one text holds itself"
        );
        assert_eq!(
            texts(&arena, pair),
            Maybe::Present(vec![&half_text, &quarter_text]),
            "a tuple holds its texts in the order written"
        );
        for other in [mixed, unit, named] {
            assert_eq!(
                texts(&arena, other),
                Maybe::Absent(super::texts::Absent::Untexted),
                "a payload holding anything but texts holds none"
            );
        }
    }

    #[test]
    fn a_deprecated_payload_reads_its_texts()
    {
        let mut arena = CoreArena::new();
        let mut text = |written: &str| {
            arena.value_literal(Literal::Text(gandr_kernel_term::StringLiteral::new(
                String::from(written),
            )))
        };
        let (since, note) = (text("0.2"), text("use `cube`"));
        let label = |written: &str| gandr_kernel_term::FieldLabel::from(String::from(written));
        let both = arena.value_record(BTreeMap::from([
            (label("since"), since),
            (label("note"), note),
        ]));
        let alone = arena.value_record(BTreeMap::from([(label("note"), note)]));
        let empty = arena.value_record(BTreeMap::new());
        assert_eq!(
            deprecation(&arena, both),
            Maybe::Present(Deprecation {
                since: Some(String::from("0.2")),
                note: Some(String::from("use `cube`")),
            }),
            "a record states both texts"
        );
        assert_eq!(
            deprecation(&arena, alone),
            Maybe::Present(Deprecation {
                since: None,
                note: Some(String::from("use `cube`")),
            }),
            "a field left out is unstated"
        );
        assert_eq!(
            deprecation(&arena, empty),
            Maybe::Present(Deprecation::default()),
            "the empty record states nothing"
        );
        let unit = arena.value_unit();
        let foreign = arena.value_record(BTreeMap::from([(label("reason"), note)]));
        let untexted = arena.value_record(BTreeMap::from([(label("since"), unit)]));
        let tuple = arena.value_tuple(&[since, note]);
        for refused in [foreign, untexted, tuple, unit] {
            assert_eq!(
                deprecation(&arena, refused),
                Maybe::Absent(names::Absent::Unnamed),
                "a foreign label, a field that is no text, or a value that is no record is \
                 refused"
            );
        }
    }

    #[test]
    fn an_identity_payload_names_two_or_three_declarations()
    {
        let mut arena = CoreArena::new();
        let [relation, reflexivity, law, extra] =
            [3_usize, 5, 8, 13].map(|at| arena.value_constant(ConstantIndex::from(at)));
        let pair = arena.value_tuple(&[relation, reflexivity]);
        let triple = arena.value_tuple(&[relation, reflexivity, law]);
        assert_eq!(
            members(&arena, pair),
            Maybe::Present(vec![relation, reflexivity]),
            "a relation and its reflexivity are an interface stating no law"
        );
        assert_eq!(
            members(&arena, triple),
            Maybe::Present(vec![relation, reflexivity, law]),
            "a third name is its law, the members kept in written order"
        );
        let unit = arena.value_unit();
        let single = arena.value_tuple(&[relation]);
        let quadruple = arena.value_tuple(&[relation, reflexivity, law, extra]);
        let mixed = arena.value_tuple(&[relation, unit]);
        for unnamed in [relation, single, quadruple, mixed, unit] {
            assert_eq!(
                members(&arena, unnamed),
                Maybe::Absent(names::Absent::Unnamed),
                "a lone name, one name too few or too many, or a non-name is no interface"
            );
        }
        let mut table = AttributeTable::new();
        let filed = keyed(SourceIndex::default(), NodeDigest::from([1_u8; 32_usize]));
        let unfiled = keyed(SourceIndex::default(), NodeDigest::from([2_u8; 32_usize]));
        table.file_interface(filed, vec![relation, reflexivity, law]);
        assert_eq!(
            table.interface(filed),
            [relation, reflexivity, law].as_slice(),
            "the interface filed under a type member is read back from it"
        );
        assert!(table.interface(unfiled).is_empty(), "and from no other");
        assert!(table.laws(filed).is_empty(), "and is no law of the member");
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

    /// The literal formers read as their own payload forms, a bare name as a
    /// word, and every other former as a value of another form.
    #[test]
    fn each_former_reads_as_its_own_payload_form()
    {
        use crate::form::Former;

        for (former, form) in [
            (Former::Number, PayloadForm::Integer),
            (Former::Text, PayloadForm::Text),
            (Former::Name, PayloadForm::Word),
            (Former::Character, PayloadForm::OtherValue),
            (Former::Constructor, PayloadForm::OtherValue),
            (Former::Lambda, PayloadForm::OtherValue),
        ] {
            assert_eq!(super::payload_form(former), form, "{former:?}");
        }
    }

    /// What the table files under one key it reads back from that key alone:
    /// the worlds of an `entry`, the laws of a `respects`, nothing of a
    /// `boundary`, a spelling by its entry's span, and a deprecation by its
    /// payload.
    #[test]
    fn the_table_reads_back_what_it_files_under_its_key_alone()
    {
        let mut table = AttributeTable::new();
        let [first, second, third] = [1_u8, 2, 3]
            .map(|form| keyed(SourceIndex::default(), NodeDigest::from([form; 32_usize])));
        let names = vec![ConstantIndex::from(4_usize), ConstantIndex::from(7_usize)];
        table.file_named(first, registered(SurfaceName::from("entry")), names.clone());
        table.file_named(
            second,
            registered(SurfaceName::from("respects")),
            names.clone(),
        );
        table.file_named(
            third,
            registered(SurfaceName::from("boundary")),
            names.clone(),
        );
        assert_eq!(
            (table.worlds(first), table.laws(first)),
            (names.as_slice(), [].as_slice()),
            "an `entry` names worlds"
        );
        assert_eq!(
            (table.worlds(second), table.laws(second)),
            ([].as_slice(), names.as_slice()),
            "a `respects` names laws"
        );
        assert_eq!(
            (table.worlds(third), table.laws(third)),
            ([].as_slice(), [].as_slice()),
            "a `boundary` files nothing here"
        );
        table.file_worlds(third, vec![ConstantIndex::from(9_usize)]);
        assert_eq!(table.worlds(third), [ConstantIndex::from(9_usize)]);

        let at = span(ByteOffset::from(0_usize), ByteOffset::from(9_usize));
        let elsewhere = span(ByteOffset::from(10_usize), ByteOffset::from(19_usize));
        table.file_spelled(first, at, String::from("explicit"));
        assert_eq!(table.spelled(first, at), Some(&String::from("explicit")));
        assert_eq!(
            table.spelled(first, elsewhere),
            None,
            "another entry's span"
        );
        assert_eq!(table.spelled(second, at), None, "another key");

        let mut arena = CoreArena::new();
        let note = arena.value_literal(Literal::Text(gandr_kernel_term::StringLiteral::new(
            String::from("use `cube`"),
        )));
        let record = arena.value_record(BTreeMap::from([(
            gandr_kernel_term::FieldLabel::from(String::from("note")),
            note,
        )]));
        let deprecated = |payload| {
            AttributeEntry::new(
                registered(SurfaceName::from("deprecated")),
                AttributeSchema::MarkerOrRecord(&["since", "note"]),
                payload,
                at,
            )
        };
        table.file(first, deprecated(Maybe::Absent(payload::Absent::Marker)));
        table.file(second, deprecated(Maybe::Present(record)));
        assert_eq!(
            table.deprecation(first, &arena),
            Some(Deprecation::default()),
            "a bare marker states nothing"
        );
        assert_eq!(
            table.deprecation(second, &arena),
            Some(Deprecation {
                since: None,
                note: Some(String::from("use `cube`")),
            }),
            "a record states its texts"
        );
        assert_eq!(
            table.deprecation(third, &arena),
            None,
            "an undecorated declaration"
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
            AttributeSchema::Texts,
            AttributeSchema::MarkerOr("all"),
            AttributeSchema::Names,
            AttributeSchema::Interface,
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
    }
}
